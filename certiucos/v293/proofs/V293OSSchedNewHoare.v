Require Import Coq.Arith.Arith Coq.Lists.List Lia.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Local Open Scope nat_scope.

(* Exact read-only bytes; no final expression value is built into this resource. *)
Fixpoint V293_read_bytes (b : block) (offset : Z) (values : list nat) : asrt :=
  match values with
  | nil => Aemp
  | cons v tail => Amapsto (b, offset) Tint8 false (V293_byteval v) **
                 V293_read_bytes b (offset + 1)%Z tail
  end.

Definition V293_sched_inputs (bt bg br : block) (lo hi g : nat) : asrt :=
  V293_read_bytes bt 0 V293_ready_table **
  V293_read_bytes br 0 (cons lo (cons hi nil)) **
  Amapsto (bg, 0%Z) Tint8 false (V293_byteval g).

(* Environment-only assertion. All conjuncts have empty resource footprints. *)
Definition V293_sched_bindings unmap group rows high y bt bg br bh byblock : asrt :=
  Agvarenv unmap (Tarray Tint8 256) (bt, 0%Z) //\\
  Agvarenv group Tint8 (bg, 0%Z) //\\
  Agvarenv rows (Tarray Tint8 2) (br, 0%Z) //\\
  Agvarenv high Tint8 (bh, 0%Z) //\\
  Alvarenv y Tint8 (byblock, 0%Z) //\\
  A_notin_lenv unmap //\\ A_notin_lenv group //\\
  A_notin_lenv rows //\\ A_notin_lenv high.

Lemma V293_byte_type : forall n, n < 256 ->
  rule_type_val_match Tint8 (V293_byteval n) = true.
Proof.
  intros n Hn. unfold V293_byteval, rule_type_val_match.
  rewrite Int.unsigned_repr by
    (unfold Int.max_unsigned, Int.modulus, Int.wordsize; simpl; lia).
  assert (B : (Z.of_nat n <=? Byte.max_unsigned)%Z = true).
  { apply Z.leb_le. unfold Byte.max_unsigned, Byte.modulus, Byte.wordsize. simpl. lia. }
  rewrite B. reflexivity.
Qed.

Lemma V293_mapsto_load : forall s b i perm n,
  n < 256 -> s |= Amapsto (b, i) Tint8 perm (V293_byteval n) ->
  load Tint8 (getmem s) (b, i) = Some (V293_byteval n).
Proof. intros s b i perm n Hn [Hm _]. eapply mapstoval_load; [apply V293_byte_type; exact Hn | exact Hm]. Qed.

Lemma V293_star_load_l : forall p q t a v,
  (forall s, s |= p -> load t (getmem s) a = Some v) ->
  forall s, s |= p ** q -> load t (getmem s) a = Some v.
Proof.
  intros p q t a v H s [m1 [m2 [m [o1 [o2 [o [Em [Jm [Eo [Jo [Hp Hq]]]]]]]]]]].
  pose proof (H _ Hp) as Hload.
  destruct s as [[[[[[ge le] M] ir] aux] O] aop]. cbn in *. subst m.
  eapply load_local; eauto.
Qed.

Lemma V293_star_load_r : forall p q t a v,
  (forall s, s |= q -> load t (getmem s) a = Some v) ->
  forall s, s |= p ** q -> load t (getmem s) a = Some v.
Proof. intros p q t a v H s Hs. eapply V293_star_load_l; [exact H | apply astar_comm; exact Hs]. Qed.

Lemma V293_star_env_l : forall p q (E : env -> env -> Prop),
  (forall s, s |= p -> E (getgenv s) (getlenv s)) ->
  forall s, s |= p ** q -> E (getgenv s) (getlenv s).
Proof.
  intros p q E H s [m1 [m2 [m [o1 [o2 [o [Em [Jm [Eo [Jo [Hp Hq]]]]]]]]]]].
  pose proof (H _ Hp) as He.
  destruct s as [[[[[[ge le] M] ir] aux] O] aop]. exact He.
Qed.

Lemma V293_star_env_r : forall p q (E : env -> env -> Prop),
  (forall s, s |= q -> E (getgenv s) (getlenv s)) ->
  forall s, s |= p ** q -> E (getgenv s) (getlenv s).
Proof. intros p q E H s Hs. eapply V293_star_env_l; [exact H | apply astar_comm; exact Hs]. Qed.

Lemma V293_read_bytes_load : forall values b offset n,
  n < length values -> nth n values 0 < 256 ->
  forall s, s |= V293_read_bytes b offset values ->
  load Tint8 (getmem s) (b, (offset + Z.of_nat n)%Z) =
    Some (V293_byteval (nth n values 0)).
Proof.
  induction values as [ | v tail IH]; intros b offset n Hn Hv s Hs; [simpl in Hn; lia | ].
  destruct n as [ | n].
  - replace (offset + Z.of_nat 0)%Z with offset by lia.
    eapply V293_star_load_l; [ | exact Hs]. intros. eapply V293_mapsto_load; eassumption.
  - replace (offset + Z.of_nat (S n))%Z with (offset + 1 + Z.of_nat n)%Z by lia.
    eapply V293_star_load_r; [ | exact Hs]. apply IH; [simpl in Hn; lia | exact Hv].
Qed.

Lemma V293_sched_inputs_load : forall bt bg br lo hi g,
  lo < 256 -> hi < 256 -> g < 256 ->
  forall s, s |= V293_sched_inputs bt bg br lo hi g ->
  V293_sched_read_memory (getmem s) bt bg br lo hi g.
Proof.
  intros bt bg br lo hi g Hlo Hhi Hg s Hs. unfold V293_sched_read_memory.
  unfold V293_sched_inputs in Hs. repeat split.
  - eapply V293_star_load_r; [ | exact Hs]. intros s1 Hs1.
    eapply V293_star_load_r; [ | exact Hs1]. intros. eapply V293_mapsto_load; eassumption.
  - intros n Hn. eapply V293_star_load_l; [ | exact Hs].
    replace (Z.of_nat n) with (0 + Z.of_nat n)%Z by lia.
    apply V293_read_bytes_load.
    + change (n < 256). exact Hn.
    + pose proof (proj1 (V293_ready_row_spec n Hn)). unfold V293_ready_lookup in *. lia.
  - eapply V293_star_load_r; [ | exact Hs]. intros s1 Hs1.
    eapply V293_star_load_l; [ | exact Hs1].
    change (forall s2, s2 |= V293_read_bytes br 0 (cons lo (cons hi nil)) ->
      load Tint8 (getmem s2) (br, (0 + Z.of_nat 0)%Z) = Some (V293_byteval (nth 0 (cons lo (cons hi nil)) 0))).
    apply V293_read_bytes_load; simpl; lia.
  - eapply V293_star_load_r; [ | exact Hs]. intros s1 Hs1.
    eapply V293_star_load_l; [ | exact Hs1].
    change (forall s2, s2 |= V293_read_bytes br 0 (cons lo (cons hi nil)) ->
      load Tint8 (getmem s2) (br, (0 + Z.of_nat 1)%Z) = Some (V293_byteval (nth 1 (cons lo (cons hi nil)) 0))).
    apply V293_read_bytes_load; simpl; lia.
Qed.

Lemma V293_sched_bindings_view : forall s unmap group rows high y bt bg br bh byblock,
  s |= V293_sched_bindings unmap group rows high y bt bg br bh byblock ->
  V293_sched_read_env (getgenv s) (getlenv s) unmap group rows bt bg br /\
  get (getlenv s) y = Some (byblock, Tint8) /\
  get (getlenv s) high = None /\ get (getgenv s) high = Some (bh, Tint8).
Proof.
  intros s unmap group rows high y bt bg br bh byblock H.
  destruct H as [[b1 [G1 [B1 _]]] [[b2 [G2 [B2 _]]] [[b3 [G3 [B3 _]]]
    [[b4 [G4 [B4 _]]] [[b5 [L5 [B5 _]]] [[N1 _] [[N2 _] [[N3 _] [N4 _]]]]]]]]].
  inversion B1; inversion B2; inversion B3; inversion B4; inversion B5; subst.
  assert (Z1 : get (getlenv s) unmap = None) by (destruct (get (getlenv s) unmap) eqn:E; [exfalso; apply N1; exists p; exact E | reflexivity]).
  assert (Z2 : get (getlenv s) group = None) by (destruct (get (getlenv s) group) eqn:E; [exfalso; apply N2; exists p; exact E | reflexivity]).
  assert (Z3 : get (getlenv s) rows = None) by (destruct (get (getlenv s) rows) eqn:E; [exfalso; apply N3; exists p; exact E | reflexivity]).
  assert (Z4 : get (getlenv s) high = None) by (destruct (get (getlenv s) high) eqn:E; [exfalso; apply N4; exists p; exact E | reflexivity]).
  unfold V293_sched_read_env. repeat split; assumption.
Qed.

(* CurLINV ends in Atrue, hence remains available under disjoint extensions. *)
Lemma V293_CurLINV_extend : forall li tid extra,
  CurLINV li tid ** extra ==> CurLINV li tid.
Proof.
  intros li tid extra s Hs. unfold CurLINV in *.
  apply astar_l_aexists_elim in Hs. destruct Hs as [lg Hs]. exists lg.
  apply astar_assoc_elim in Hs.
  eapply astar_mono; [intros s0 H; exact H | | exact Hs].
  intros s0 H. apply astar_assoc_elim in H.
  eapply astar_mono; [intros s1 H1; exact H1 | | exact H]. intros; exact I.
Qed.

Lemma V293_star_reads_l : forall p q bt bg br lo hi g,
  (forall s, s |= p -> V293_sched_read_memory (getmem s) bt bg br lo hi g) ->
  forall s, s |= p ** q -> V293_sched_read_memory (getmem s) bt bg br lo hi g.
Proof.
  intros p q bt bg br lo hi g H s Hs. repeat split.
  - eapply V293_star_load_l; [intros s0 H0; exact (proj1 (H s0 H0)) | exact Hs].
  - intros n Hn. eapply V293_star_load_l; [intros s0 H0; exact (proj1 (proj2 (H s0 H0)) n Hn) | exact Hs].
  - eapply V293_star_load_l; [intros s0 H0; exact (proj1 (proj2 (proj2 (H s0 H0)))) | exact Hs].
  - eapply V293_star_load_l; [intros s0 H0; exact (proj2 (proj2 (proj2 (H s0 H0)))) | exact Hs].
Qed.

Lemma V293_star_reads_r : forall p q bt bg br lo hi g,
  (forall s, s |= q -> V293_sched_read_memory (getmem s) bt bg br lo hi g) ->
  forall s, s |= p ** q -> V293_sched_read_memory (getmem s) bt bg br lo hi g.
Proof. intros p q bt bg br lo hi g H s Hs. eapply V293_star_reads_l; [exact H | apply astar_comm; exact Hs]. Qed.

Lemma V293_star_CurLINV_l : forall p q li tid,
  (p ==> CurLINV li tid) -> p ** q ==> CurLINV li tid.
Proof.
  intros p q li tid H s Hs. apply V293_CurLINV_extend with (extra := q).
  eapply astar_mono; [exact H | intros s0 H0; exact H0 | exact Hs].
Qed.

Lemma V293_star_CurLINV_r : forall p q li tid,
  (q ==> CurLINV li tid) -> p ** q ==> CurLINV li tid.
Proof. intros p q li tid H s Hs. eapply V293_star_CurLINV_l; [exact H | apply astar_comm; exact Hs]. Qed.

Definition V293_sched_common unmap group rows high y bt bg br bh byblock lo hi g li tid frame :=
  (V293_sched_bindings unmap group rows high y bt bg br bh byblock **
   V293_sched_inputs bt bg br lo hi g) ** (CurLINV li tid ** frame).

Definition V293_sched_state common byblock bh yv hv :=
  (common ** PV (byblock, Int.zero) @ Tint8 |-> yv) **
  PV (bh, Int.zero) @ Tint8 |-> hv.

Lemma V293_sched_common_env : forall unmap group rows high y bt bg br bh byblock lo hi g li tid frame,
  forall s, s |= V293_sched_common unmap group rows high y bt bg br bh byblock lo hi g li tid frame ->
  V293_sched_read_env (getgenv s) (getlenv s) unmap group rows bt bg br /\
  get (getlenv s) y = Some (byblock, Tint8) /\
  get (getlenv s) high = None /\ get (getgenv s) high = Some (bh, Tint8).
Proof.
  intros. eapply V293_star_env_l; [ | exact H]. intros s0 H0.
  eapply V293_star_env_l; [ | exact H0]. intros s1 H1. eapply V293_sched_bindings_view; exact H1.
Qed.

Lemma V293_sched_common_reads : forall unmap group rows high y bt bg br bh byblock lo hi g li tid frame,
  lo < 256 -> hi < 256 -> g < 256 -> forall s,
  s |= V293_sched_common unmap group rows high y bt bg br bh byblock lo hi g li tid frame ->
  V293_sched_read_memory (getmem s) bt bg br lo hi g.
Proof.
  intros unmap group rows high y bt bg br bh byblock lo hi g li tid frame Hlo Hhi Hg s Hs.
  eapply V293_star_reads_l; [ | exact Hs]. intros s0 H0.
  eapply V293_star_reads_r; [ | exact H0]. apply V293_sched_inputs_load; assumption.
Qed.

Lemma V293_sched_common_CurLINV : forall unmap group rows high y bt bg br bh byblock lo hi g li tid frame,
  V293_sched_common unmap group rows high y bt bg br bh byblock lo hi g li tid frame ==> CurLINV li tid.
Proof.
  intros unmap group rows high y bt bg br bh byblock lo hi g li tid frame s Hs.
  unfold V293_sched_common in Hs.
  eapply V293_star_CurLINV_r; [ | exact Hs]. intros s0 H0.
  eapply V293_star_CurLINV_l; [ | exact H0]. intros s1 H1; exact H1.
Qed.

Lemma V293_three_swap : forall p q r, (p ** q) ** r ==> (p ** r) ** q.
Proof.
  intros p q r s H. apply astar_assoc_intro.
  apply astar_assoc_elim in H.
  eapply astar_mono; [intros s0 H0; exact H0 | apply astar_comm | exact H].
Qed.

(* The first assignment consumes a writable local byte, preserving the actual
   input bytes, the global output byte, and the supplied local invariant. *)
Theorem V293_OSSchedNew_row_hoare : forall Spec sd li I r ri tid aop frame
    unmap group rows high y bt bg br bh byblock lo hi g yold hold,
  lo < 256 -> hi < 256 -> g < 256 ->
  let common := V293_sched_common unmap group rows high y bt bg br bh byblock lo hi g li tid frame in
  InfRules Spec sd li I r ri
    (<||aop||> ** V293_sched_state common byblock bh yold hold)
    (sassign (evar y) (V293_OSSchedNew_row_expr unmap group))
    (<||aop||> ** V293_sched_state common byblock bh (V293_byteval (V293_ready_lookup g)) hold) tid.
Proof.
  intros Spec sd li I r ri tid aop frame unmap group rows high y bt bg br bh byblock lo hi g yold hold Hlo Hhi Hg common.
  unfold V293_sched_state. eapply conseq_rule.
  - apply astar_mono; [intros s H; exact H | apply V293_three_swap].
  - apply astar_mono; [intros s H; exact H | apply V293_three_swap].
  - eapply assign_rule with (tp2 := Tint8).
    + apply eq_int. auto.
    + intros s Hs.
      assert (He : V293_sched_read_env (getgenv s) (getlenv s) unmap group rows bt bg br /\
        get (getlenv s) y = Some (byblock, Tint8) /\
        get (getlenv s) high = None /\ get (getgenv s) high = Some (bh, Tint8)).
      { eapply V293_star_env_l; [ | exact Hs]. intros s0 H0.
        eapply V293_star_env_l; [ | exact H0]. apply V293_sched_common_env. }
      assert (Hm : V293_sched_read_memory (getmem s) bt bg br lo hi g).
      { eapply V293_star_reads_l; [ | exact Hs]. intros s0 H0.
        eapply V293_star_reads_l; [ | exact H0]. apply V293_sched_common_reads; assumption. }
      destruct He as [He [Ey _]].
      destruct s as [[[[[[ge le] M] irs] aux] O] op].
      cbn [getgenv getlenv getmem get_smem get_genv get_lenv get_mem] in He, Ey, Hm.
      destruct (V293_OSSchedNew_row_eval ge le M unmap group rows bt bg br lo hi g He Hm Hg) as [Ev Et].
      split.
      * cbn [sat evaladdr evaltype getsmem get_smem get_lenv]. rewrite Ey. auto.
      * cbn [sat getsmem]. split; [exact Ev | ]. split; [exact Et | unfold V293_byteval; discriminate].
    + intros s Hs. eapply V293_star_CurLINV_l; [ | exact Hs]. intros s0 H0.
      eapply V293_star_CurLINV_l; [ | exact H0]. apply V293_sched_common_CurLINV.
Qed.

Theorem V293_OSSchedNew_priority_hoare : forall Spec sd li I r ri tid aop frame
    unmap group rows high y bt bg br bh byblock lo hi g hold,
  lo < 256 -> hi < 256 -> g < 256 -> g = V293_ready_group lo hi ->
  (exists p, V293_bitmap_ready lo hi p) ->
  let common := V293_sched_common unmap group rows high y bt bg br bh byblock lo hi g li tid frame in
  InfRules Spec sd li I r ri
    (<||aop||> ** V293_sched_state common byblock bh (V293_byteval (V293_ready_lookup g)) hold)
    (sassign (evar high) (V293_OSSchedNew_priority_expr unmap rows y))
    (<||aop||> ** V293_sched_state common byblock bh (V293_byteval (V293_ready_lookup g))
      (V293_byteval (V293_ready_select lo hi g))) tid.
Proof.
  intros Spec sd li I r ri tid aop frame unmap group rows high y bt bg br bh byblock lo hi g hold Hlo Hhi Hg Hgroup Hready common.
  unfold V293_sched_state. eapply assign_rule with (tp2 := Tint8).
  - apply eq_int. auto.
  - intros s Hs.
    assert (He : V293_sched_read_env (getgenv s) (getlenv s) unmap group rows bt bg br /\
      get (getlenv s) y = Some (byblock, Tint8) /\
      get (getlenv s) high = None /\ get (getgenv s) high = Some (bh, Tint8)).
    { eapply V293_star_env_l; [ | exact Hs]. intros s0 H0.
      eapply V293_star_env_l; [ | exact H0]. apply V293_sched_common_env. }
    assert (Hm : V293_sched_read_memory (getmem s) bt bg br lo hi g).
    { eapply V293_star_reads_l; [ | exact Hs]. intros s0 H0.
      eapply V293_star_reads_l; [ | exact H0]. apply V293_sched_common_reads; assumption. }
    assert (Yload : load Tint8 (getmem s) (byblock, 0%Z) = Some (V293_byteval (V293_ready_lookup g))).
    { eapply V293_star_load_l; [ | exact Hs]. intros s0 H0.
      eapply V293_star_load_r; [ | exact H0]. intros s1 H1.
      change (s1 |= Amapsto (byblock, 0%Z) Tint8 true (V293_byteval (V293_ready_lookup g))) in H1.
      eapply V293_mapsto_load; [ | exact H1].
      pose proof (proj1 (V293_ready_row_spec g Hg)). lia. }
    destruct He as [He [Ey [Eh Gh]]].
    destruct s as [[[[[[ge le] M] irs] aux] O] op].
    cbn [getgenv getlenv getmem get_smem get_genv get_lenv get_mem] in He, Ey, Eh, Gh, Hm, Yload.
    destruct (V293_OSSchedNew_priority_eval ge le M unmap group rows y bt bg br byblock lo hi g
      He Hm Ey Yload Hlo Hhi Hgroup Hready) as [Ev Et].
    split.
    + cbn [sat evaladdr evaltype getsmem get_smem get_lenv get_genv]. rewrite Eh, Gh. auto.
    + cbn [sat getsmem get_smem]. split; [exact Ev | ]. split; [exact Et | unfold V293_byteval; discriminate].
  - intros s Hs. eapply V293_star_CurLINV_l; [ | exact Hs]. intros s0 H0.
    eapply V293_star_CurLINV_l; [ | exact H0]. apply V293_sched_common_CurLINV.
Qed.

Definition V293_OSSchedNew_post common byblock bh lo hi g : retasrt :=
  fun result => [|result = None /\
      V293_bitmap_ready lo hi (V293_ready_select lo hi g) /\
      (forall p, V293_bitmap_ready lo hi p -> V293_ready_select lo hi g <= p)|] **
    V293_sched_state common byblock bh (V293_byteval (V293_ready_lookup g))
      (V293_byteval (V293_ready_select lo hi g)).

(* Function body only: entry allocation, local-byte disposal and the internal
   function specification table remain separate component-linking obligations.
   The caller supplies its genuine CurLINV; no invariant is replaced by True. *)
Theorem V293_OSSchedNew_body_hoare : forall Spec sd li I tid aop frame
    unmap group rows high y bt bg br bh byblock lo hi g yold hold,
  lo < 256 -> hi < 256 -> g = V293_ready_group lo hi ->
  (exists p, V293_bitmap_ready lo hi p) ->
  let common := V293_sched_common unmap group rows high y bt bg br bh byblock lo hi g li tid frame in
  InfRules Spec sd li I
    (fun result => <||aop||> ** V293_OSSchedNew_post common byblock bh lo hi g result) Afalse
    (<||aop||> ** V293_sched_state common byblock bh yold hold)
    (V293_OSSchedNew_body unmap group rows high y) Afalse tid.
Proof.
  intros Spec sd li I tid aop frame unmap group rows high y bt bg br bh byblock lo hi g yold hold Hlo Hhi Hgroup Hready common.
  assert (Hg : g < 256).
  { rewrite Hgroup. unfold V293_ready_group. destruct (lo =? 0); destruct (hi =? 0); simpl; lia. }
  unfold V293_OSSchedNew_body, V293_OSSchedNew_updates. eapply seq_rule.
  - eapply seq_rule.
    + apply V293_OSSchedNew_row_hoare; assumption.
    + apply V293_OSSchedNew_priority_hoare; assumption.
  - apply ret_rule. apply astar_mono; [intros s H; exact H | ]. intros s Hs.
    unfold V293_OSSchedNew_post. apply astar_l_apure_intro; [exact Hs | ].
    split; [reflexivity | ]. exact (proj2 (V293_ready_selection lo hi g Hlo Hhi Hgroup Hready)).
Qed.
