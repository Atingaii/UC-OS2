(* Actual 13-entry pointer-array reads, connected to abstract task membership.
   No expression result or chosen-task oracle occurs in the input relation. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.certiucos.v293.code.V293OSSchedDispatch.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import Coq.Lists.List Lia.
Local Open Scope nat_scope.

Fixpoint V293_read_pointers (tp : type) (b : block) (offset : Z) (entries : list val) : asrt :=
  match entries with
  | nil => Aemp
  | cons v tail => Amapsto (b, offset) (Tptr tp) false v **
      V293_read_pointers tp b (offset + 4)%Z tail
  end.

Lemma V293_read_pointers_load : forall entries tp b offset n,
  n < length entries -> rule_type_val_match (Tptr tp) (nth n entries Vnull) = true ->
  forall s, s |= V293_read_pointers tp b offset entries ->
  load (Tptr tp) (getmem s) (b, (offset + 4 * Z.of_nat n)%Z) = Some (nth n entries Vnull).
Proof.
  induction entries as [ | v tail IH]; intros tp b offset n Hn Htype s Hs; [simpl in Hn; lia | ].
  destruct n as [ | n].
  - replace (offset + 4 * Z.of_nat 0)%Z with offset by lia.
    eapply V293_star_load_l; [ | exact Hs].
    intros s0 [Hm _]. eapply mapstoval_load; eassumption.
  - replace (offset + 4 * Z.of_nat (S n))%Z with (offset + 4 + 4 * Z.of_nat n)%Z by lia.
    eapply V293_star_load_r; [ | exact Hs]. apply IH; [simpl in Hn; lia | exact Htype].
Qed.

Lemma V293_eval_pointer_array : forall ge le M table high tp bp bh n v,
  get le table = None -> get le high = None ->
  get ge table = Some (bp, Tarray (Tptr tp) 13) -> get ge high = Some (bh, Tint8) ->
  load Tint8 M (bh, 0%Z) = Some (V293_byteval n) -> n < 13 ->
  load (Tptr tp) M (bp, (4 * Z.of_nat n)%Z) = Some v ->
  evalval (V293_OSSched_target_expr table high) (ge, le, M) = Some v /\
  evaltype (V293_OSSched_target_expr table high) (ge, le, M) = Some (Tptr tp).
Proof.
  intros ge le M table high tp bp bh n v Nt Nh Gt Gh Mh Hn Mt.
  unfold V293_OSSched_target_expr. cbn [evalval evaltype get_lenv get_genv get_mem].
  rewrite Nt, Nh, Gt, Gh. cbn [evaltype evalval get_lenv get_genv get_mem].
  rewrite Mh. unfold V293_byteval. simpl typelen.
  replace (load (Tarray (Tptr tp) 13) M (bp, 0%Z))
    with (Some (Vptr (bp, Int.zero))) by reflexivity.
  cbn beta iota.
  rewrite Int.add_zero_l. unfold Int.mul.
  rewrite (Int.unsigned_repr (Z.of_nat 4)), (Int.unsigned_repr (Z.of_nat n)) by
    (unfold Int.max_unsigned, Int.modulus, Int.wordsize; simpl; lia).
  change (Z.of_nat 4) with 4%Z.
  rewrite Int.unsigned_repr by (change (0 <= 4 * Z.of_nat n <= 4294967295)%Z; lia).
  change (load (Tptr tp) M (bp, (4 * Z.of_nat n)%Z) = Some v /\ Some (Tptr tp) = Some (Tptr tp)).
  rewrite Mt. auto.
Qed.

Lemma V293_star_abst_get_l : forall p q key value,
  (forall s, s |= p -> get (getabst s) key = Some value) ->
  forall s, s |= p ** q -> get (getabst s) key = Some value.
Proof.
  intros p q key value H s [m1 [m2 [m [o1 [o2 [o [Em [Jm [Eo [Jo [Hp Hq]]]]]]]]]]].
  pose proof (H _ Hp) as Hget.
  destruct s as [[[[[[ge le] M] ir] aux] O] aop]. cbn in *. subst o.
  eapply OSAbstMod.join_get_l; eauto.
Qed.

Lemma V293_star_abst_get_r : forall p q key value,
  (forall s, s |= q -> get (getabst s) key = Some value) ->
  forall s, s |= p ** q -> get (getabst s) key = Some value.
Proof.
  intros p q key value H s Hs. eapply V293_star_abst_get_l; [exact H | ].
  apply astar_comm; exact Hs.
Qed.

Theorem V293_OSSched_target_task : forall s table high tp bp bh lo hi entries tasks frame,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks ->
  get (getlenv s) table = None -> get (getlenv s) high = None ->
  get (getgenv s) table = Some (bp, Tarray (Tptr tp) 13) ->
  get (getgenv s) high = Some (bh, Tint8) ->
  load Tint8 (getmem s) (bh, 0%Z) =
    Some (V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi))) ->
  s |= (V293_read_pointers tp bp 0 entries ** Aabsdata abstcblsid (abstcblist tasks)) ** frame ->
  exists t m,
    get tasks t = Some (Int.repr (Z.of_nat (V293_ready_select lo hi (V293_ready_group lo hi))), rdy, m) /\
    evalval (V293_OSSched_target_expr table high) (getgenv s, getlenv s, getmem s) = Some (Vptr t) /\
    evaltype (V293_OSSched_target_expr table high) (getgenv s, getlenv s, getmem s) = Some (Tptr tp) /\
    V293_scheduler (getabst s) t.
Proof.
  intros s table high tp bp bh lo hi entries tasks frame Hlo Hhi Hnonempty Hb Ht Nt Nh Gt Gh Mh Hs.
  destruct (V293_ready_selection_task lo hi entries tasks Hlo Hhi Hnonempty Hb Ht)
    as [t [m [Htask [Hentry Hhighest]]]].
  pose proof (V293_ready_selection_range lo hi (V293_ready_group lo hi) Hlo Hhi eq_refl Hnonempty) as Hrange.
  assert (Hload : load (Tptr tp) (getmem s)
    (bp, (4 * Z.of_nat (V293_ready_select lo hi (V293_ready_group lo hi)))%Z) = Some (Vptr t)).
  { rewrite <- Hentry. replace (4 * Z.of_nat (V293_ready_select lo hi (V293_ready_group lo hi)))%Z
      with (0 + 4 * Z.of_nat (V293_ready_select lo hi (V293_ready_group lo hi)))%Z by lia.
    eapply V293_star_load_l; [ | exact Hs].
    apply V293_star_load_l. eapply V293_read_pointers_load;
      [rewrite (proj1 Ht); exact Hrange | ]. rewrite Hentry. reflexivity. }
  assert (HO : get (getabst s) abstcblsid = Some (abstcblist tasks)).
  { eapply V293_star_abst_get_l; [ | exact Hs]. apply V293_star_abst_get_r.
    intros s0 [E _]. rewrite <- E. apply map_get_sig. }
  destruct (V293_eval_pointer_array (getgenv s) (getlenv s) (getmem s)
    table high tp bp bh _ _ Nt Nh Gt Gh Mh Hrange Hload) as [Ev Et].
  exists t. exists m. split; [exact Htask | ]. split; [exact Ev | ].
  split; [exact Et | ]. exists tasks. auto.
Qed.
