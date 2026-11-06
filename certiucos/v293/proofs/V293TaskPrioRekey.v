(* Actual array-address evaluation, constructive stores and execution of the
   frozen table-write fragment. Not a full OSTaskChangePrio/API proof. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import Coq.Lists.List Lia.
Local Open Scope nat_scope.

Definition V293_bytes_writable (M : mem) b i n : Prop :=
  forall k, k < n -> exists v, get M (b, (i + Z.of_nat k)%Z) = Some (true, v).

Lemma V293_storebytes_exists : forall bytes M b i,
  V293_bytes_writable M b i (length bytes) ->
  exists M', storebytes M (b, i) bytes = Some M'.
Proof.
  induction bytes as [ | v bytes IH]; intros M b i W.
  - exists M. reflexivity.
  - destruct (W 0 ltac:(simpl; lia)) as [old H].
    replace (i + Z.of_nat 0)%Z with i in H by lia.
    destruct (IH M b (i+1)%Z) as [M' S].
    { intros k Hk. specialize (W (Datatypes.S k) ltac:(simpl; lia)).
      replace (i + Z.of_nat (Datatypes.S k))%Z with (i+1+Z.of_nat k)%Z in W by lia. exact W. }
    exists (set M' (b,i) (true,v)). cbn [storebytes]. unfold addr, offset in *.
    rewrite H, S. reflexivity.
Qed.

Lemma V293_storebytes_outside : forall bytes M M' b i other j,
  storebytes M (b,i) bytes = Some M' ->
  other <> b \/ (j < i)%Z \/ (i + Z.of_nat (length bytes) <= j)%Z ->
  get M' (other,j) = get M (other,j).
Proof.
  induction bytes as [ | v bytes IH]; intros M M' b i other j S R.
  - cbn [storebytes] in S. inversion S. reflexivity.
  - cbn [storebytes] in S. unfold addr, offset in *.
    destruct (get M (b,i)) as [[permission old] | ]; try discriminate.
    destruct permission; try discriminate.
    destruct (storebytes M (b,(i+1)%Z) bytes) as [tail | ] eqn:T; try discriminate.
    inversion S; subst M'. rewrite map_get_set'.
    + eapply IH; [exact T | ]. simpl length in R. rewrite Nat2Z.inj_succ in R. intuition lia.
    + intro E; inversion E; subst. simpl length in R. rewrite Nat2Z.inj_succ in R. intuition lia.
Qed.

Lemma V293_storebytes_nth : forall bytes M M' b i k,
  storebytes M (b,i) bytes = Some M' -> k < length bytes ->
  get M' (b,(i+Z.of_nat k)%Z) = Some (true,nth k bytes Undef).
Proof.
  induction bytes as [ | v bytes IH]; intros M M' b i k S R; [simpl in R; lia | ].
  cbn [storebytes] in S. unfold addr, offset in *.
  destruct (get M (b,i)) as [[permission old] | ]; try discriminate.
  destruct permission; try discriminate.
  destruct (storebytes M (b,(i+1)%Z) bytes) as [tail | ] eqn:T; try discriminate.
  inversion S; subst M'. destruct k as [ | k].
  - replace (i+Z.of_nat 0)%Z with i by lia. apply map_get_set.
  - rewrite map_get_set' by (intro E; inversion E; lia).
    replace (i+Z.of_nat (Datatypes.S k))%Z with (i+1+Z.of_nat k)%Z by lia.
    apply IH with (M := M); [exact T|simpl in R; lia].
Qed.

Lemma V293_loadbytes_get : forall bytes M b i,
  (forall k, k < length bytes -> exists permission,
    get M (b,(i+Z.of_nat k)%Z) = Some (permission,nth k bytes Undef)) ->
  loadbytes M (b,i) (length bytes) = Some bytes.
Proof.
  induction bytes as [ | v bytes IH]; intros M b i H; [reflexivity | ].
  destruct (H 0 ltac:(simpl; lia)) as [permission E].
  replace (i+Z.of_nat 0)%Z with i in E by lia.
  cbn [length loadbytes]. unfold addr, offset in *. rewrite E.
  rewrite (IH M b (i+1)%Z); [reflexivity | ]. intros k R.
  specialize (H (Datatypes.S k) ltac:(simpl; lia)). simpl nth in H.
  replace (i+Z.of_nat (Datatypes.S k))%Z with (i+1+Z.of_nat k)%Z in H by lia. exact H.
Qed.

Lemma V293_store_readback : forall tp M M' b i v,
  rule_type_val_match (Tptr tp) v = true -> store (Tptr tp) M (b,i) v = Some M' ->
  load (Tptr tp) M' (b,i) = Some v.
Proof.
  intros tp M M' b i v Ht S. unfold load, loadm.
  rewrite <- (encode_val_length (Tptr tp) v). rewrite V293_loadbytes_get.
  - rewrite type_val_mach_encode_val_decode_val by exact Ht. reflexivity.
  - intros k R. exists true. eapply V293_storebytes_nth; eassumption.
Qed.

Lemma V293_loadbytes_ext : forall n M M' b i,
  (forall k, k < n -> get M' (b,(i+Z.of_nat k)%Z) = get M (b,(i+Z.of_nat k)%Z)) ->
  loadbytes M' (b,i) n = loadbytes M (b,i) n.
Proof.
  induction n as [ | n IH]; intros M M' b i H; [reflexivity | ].
  cbn [loadbytes]. unfold addr, offset in *.
  pose proof (H 0 ltac:(lia)) as E. replace (i+Z.of_nat 0)%Z with i in E by lia. rewrite E.
  rewrite (IH M M' b (i+1)%Z); [reflexivity | ]. intros k R.
  specialize (H (Datatypes.S k) ltac:(lia)).
  replace (i+Z.of_nat (Datatypes.S k))%Z with (i+1+Z.of_nat k)%Z in H by lia. exact H.
Qed.

Lemma V293_pointer_store_other_slot : forall tp M M' b p q v,
  p <> q -> store (Tptr tp) M (b,(4*Z.of_nat p)%Z) v = Some M' ->
  load (Tptr tp) M' (b,(4*Z.of_nat q)%Z) = load (Tptr tp) M (b,(4*Z.of_nat q)%Z).
Proof.
  intros tp M M' b p q v N S. unfold load, loadm.
  rewrite V293_loadbytes_ext with (M := M); [reflexivity | ].
  intros k R. eapply V293_storebytes_outside; [exact S | ].
  rewrite encode_val_length. simpl typelen in *. right. destruct (Nat.lt_ge_cases q p); [left|right]; lia.
Qed.

Theorem V293_task_prio_rekey_stores : forall tp M b old new next,
  old <> new ->
  V293_bytes_writable M b (4*Z.of_nat old)%Z 4 ->
  V293_bytes_writable M b (4*Z.of_nat new)%Z 4 ->
  exists M1 M2,
    store (Tptr tp) M (b,(4*Z.of_nat old)%Z) Vnull = Some M1 /\
    store (Tptr tp) M1 (b,(4*Z.of_nat new)%Z) (Vptr next) = Some M2 /\
    load (Tptr tp) M2 (b,(4*Z.of_nat old)%Z) = Some Vnull /\
    load (Tptr tp) M2 (b,(4*Z.of_nat new)%Z) = Some (Vptr next) /\
    (forall other j,
      (other <> b \/ (j < 4*Z.of_nat old)%Z \/ (4*Z.of_nat old+4 <= j)%Z) ->
      (other <> b \/ (j < 4*Z.of_nat new)%Z \/ (4*Z.of_nat new+4 <= j)%Z) ->
      get M2 (other,j) = get M (other,j)).
Proof.
  intros tp M b old new next N Wo Wn.
  destruct (V293_storebytes_exists (encode_val (Tptr tp) Vnull) M b (4*Z.of_nat old)%Z)
    as [M1 S1]; [rewrite encode_val_length; exact Wo | ].
  assert (Wn1 : V293_bytes_writable M1 b (4*Z.of_nat new)%Z 4).
  { intros k R. unfold V293_bytes_writable in Wn. destruct (Wn k R) as [v E]. exists v.
    rewrite V293_storebytes_outside with (M := M) (bytes := encode_val (Tptr tp) Vnull) (b := b) (i := (4*Z.of_nat old)%Z); [exact E|exact S1 | ].
    rewrite encode_val_length. simpl typelen. right. destruct (Nat.lt_ge_cases new old); [left|right]; lia. }
  destruct (V293_storebytes_exists (encode_val (Tptr tp) (Vptr next)) M1 b (4*Z.of_nat new)%Z)
    as [M2 S2]; [rewrite encode_val_length; exact Wn1 | ].
  exists M1. exists M2. split; [exact S1 | ]. split; [exact S2 | ]. split.
  - rewrite V293_pointer_store_other_slot with (M := M1) (p := new) (v := Vptr next); [ | congruence|exact S2].
    eapply V293_store_readback; [reflexivity|exact S1].
  - split; [eapply V293_store_readback; [reflexivity|exact S2] | ]. intros other j Ro Rn.
    rewrite V293_storebytes_outside with (M := M1) (bytes := encode_val (Tptr tp) (Vptr next))
      (b := b) (i := (4*Z.of_nat new)%Z); [ | exact S2|rewrite encode_val_length; exact Rn].
    eapply V293_storebytes_outside; [exact S1|rewrite encode_val_length; exact Ro].
Qed.

Lemma V293_rekey_array_address : forall ge le M table index tp b bi n,
  get le table = None -> get ge table = Some (b,Tarray (Tptr tp) 13) ->
  get le index = Some (bi,Tint8) -> load Tint8 M (bi,0%Z) = Some (V293_byteval n) ->
  n < 13 ->
  evaltype (earrayelem (evar table) (evar index)) (ge,le,M) = Some (Tptr tp) /\
  evaladdr (earrayelem (evar table) (evar index)) (ge,le,M) =
    Some (Vptr (b,Int.repr (4*Z.of_nat n))).
Proof.
  intros ge le M table index tp b bi n Nt Gt Gi Li R.
  cbn [evaltype evaladdr get_lenv get_genv get_mem]. rewrite Nt, Gt, Gi.
  cbn [evaltype evalval get_lenv get_genv get_mem].
  rewrite Nt, Gt, Gi. cbn beta iota. rewrite Li.
  unfold V293_byteval. simpl typelen.
  replace (load (Tarray (Tptr tp) 13) M (b,0%Z))
    with (Some (Vptr (b,Int.zero))) by reflexivity.
  cbn beta iota. rewrite Int.add_zero_l. unfold Int.mul.
  rewrite (Int.unsigned_repr (Z.of_nat 4)), (Int.unsigned_repr (Z.of_nat n)) by
    (unfold Int.max_unsigned, Int.modulus, Int.wordsize; simpl; lia).
  split; reflexivity.
Qed.

Lemma V293_assign_pointer_execution : forall P ge le M M' lhs rhs tp tr b off value ks,
  evaltype lhs (ge,le,M) = Some (Tptr tp) -> evaltype rhs (ge,le,M) = Some tr ->
  assign_type_match (Tptr tp) tr ->
  evaladdr lhs (ge,le,M) = Some (Vptr (b,Int.repr off)) ->
  evalval rhs (ge,le,M) = Some value -> (0 <= off <= Int.max_unsigned)%Z ->
  store (Tptr tp) M (b,off) value = Some M' ->
  cstepstar P (curs (sassign lhs rhs),(kenil,ks)) (ge,le,M)
    (curs (sskip None),(kenil,ks)) (ge,le,M').
Proof.
  intros P ge le M M' lhs rhs tp tr b off value ks Tl Tr Tm A V R S.
  eapply c_stepstarn. { eapply stmt_step; [reflexivity | ]. eapply sassign_step; eassumption. }
  eapply V293_cstepstar_trans.
  { apply V293_expr_steps. apply evalval_imply_estepstar. exact V. }
  eapply c_stepstarn. { eapply stmt_step; [reflexivity | ]. constructor. }
  eapply V293_cstepstar_trans.
  { apply V293_expr_steps. apply evalval_imply_estepstar. eapply evaladdr_val_eq; eassumption. }
  eapply c_stepstarn.
  { eapply stmt_step; [reflexivity | ]. eapply sassignend_step; try reflexivity.
    cbn [addrval_to_addr]. rewrite Int.unsigned_repr by exact R. exact S. }
  apply c_stepstar0.
Qed.

(* A single stable execution interface: successful stores are CONSTRUCTED
   from byte permissions; the second assignment rereads real local operands.
   Local operand blocks cannot alias the array block. No API call is run. *)
Theorem V293_OSTaskChangePrio_table_execution :
  forall P ks ge le M table oldprio newprio ptcb tp b bo bn bc old new next,
  old < 13 -> new < 13 -> old <> new ->
  get le table = None -> get ge table = Some (b,Tarray (Tptr tp) 13) ->
  get le oldprio = Some (bo,Tint8) -> get le newprio = Some (bn,Tint8) ->
  get le ptcb = Some (bc,Tptr tp) -> b <> bo -> b <> bn -> b <> bc ->
  load Tint8 M (bo,0%Z) = Some (V293_byteval old) ->
  load Tint8 M (bn,0%Z) = Some (V293_byteval new) ->
  load (Tptr tp) M (bc,0%Z) = Some (Vptr next) ->
  V293_bytes_writable M b (4*Z.of_nat old)%Z 4 ->
  V293_bytes_writable M b (4*Z.of_nat new)%Z 4 ->
  exists M1 M2,
    store (Tptr tp) M (b,(4*Z.of_nat old)%Z) Vnull = Some M1 /\
    store (Tptr tp) M1 (b,(4*Z.of_nat new)%Z) (Vptr next) = Some M2 /\
    cstepstar P (curs (V293_task_prio_rekey table oldprio newprio ptcb),(kenil,ks)) (ge,le,M)
      (curs (sskip None),(kenil,ks)) (ge,le,M2) /\
    load (Tptr tp) M2 (b,(4*Z.of_nat old)%Z) = Some Vnull /\
    load (Tptr tp) M2 (b,(4*Z.of_nat new)%Z) = Some (Vptr next) /\
    (forall other j,
      (other <> b \/ (j < 4*Z.of_nat old)%Z \/ (4*Z.of_nat old+4 <= j)%Z) ->
      (other <> b \/ (j < 4*Z.of_nat new)%Z \/ (4*Z.of_nat new+4 <= j)%Z) ->
      get M2 (other,j) = get M (other,j)).
Proof.
  intros P ks ge le M table oldprio newprio ptcb tp b bo bn bc old new next
    Ro Rn N Nt Gt Go Gn Gc No Nn Nc Lo Ln Lc Wo Wn.
  destruct (V293_task_prio_rekey_stores tp M b old new next N Wo Wn)
    as (M1 & M2 & S1 & S2 & Lold & Lnew & Frame).
  assert (Ln1 : load Tint8 M1 (bn,0%Z) = Some (V293_byteval new)).
  { unfold load,loadm. erewrite V293_loadbytes_ext with (M := M); [exact Ln | ].
    intros k R. eapply V293_storebytes_outside; [exact S1|left; congruence]. }
  assert (Lc1 : load (Tptr tp) M1 (bc,0%Z) = Some (Vptr next)).
  { unfold load,loadm. erewrite V293_loadbytes_ext with (M := M); [exact Lc | ].
    intros k R. eapply V293_storebytes_outside; [exact S1|left; congruence]. }
  destruct (V293_rekey_array_address ge le M table oldprio tp b bo old Nt Gt Go Lo Ro) as [To Ao].
  destruct (V293_rekey_array_address ge le M1 table newprio tp b bn new Nt Gt Gn Ln1 Rn) as [Tn An].
  exists M1. exists M2. split; [exact S1 | ]. split; [exact S2 | ]. split.
  - unfold V293_task_prio_rekey.
    eapply c_stepstarn. { eapply stmt_step; [reflexivity | ]. constructor. }
    eapply V293_cstepstar_trans.
    { eapply V293_assign_pointer_execution with (tr := Tnull) (tp := tp) (b := b) (off := (4*Z.of_nat old)%Z) (M' := M1); try eassumption; try reflexivity.
      - apply eq_tnull. left. eauto.
      - change (0 <= 4 * Z.of_nat old <= 4294967295)%Z. lia. }
    eapply c_stepstarn. { eapply stmt_step; [reflexivity | ]. constructor. }
    eapply V293_assign_pointer_execution with (tr := Tptr tp) (tp := tp) (b := b) (off := (4*Z.of_nat new)%Z) (M' := M2); try eassumption.
    + cbn [evaltype get_lenv]. rewrite Gc. reflexivity.
    + apply eq_vptr. eauto.
    + cbn [evalval evaltype get_lenv get_genv get_mem]. rewrite Gc. exact Lc1.
    + change (0 <= 4 * Z.of_nat new <= 4294967295)%Z. lia.
  - auto.
Qed.

(* The post-table is not an unrelated mathematical oracle: every one of its
   13 pointer reads is transported through the two actual physical stores. *)
Definition V293_table_loads tp M b (entries : list val) : Prop :=
  forall p, p < 13 ->
    load (Tptr tp) M (b,(4*Z.of_nat p)%Z) = Some (nth p entries Vnull).

Local Lemma V293_rekey_nth_same : forall entries p v,
  p < length entries -> nth p (update_nth_val p entries v) Vnull = v.
Proof.
  induction entries as [ | x xs IH]; intros [ | p] v R; simpl in *; try lia;
    [reflexivity | apply IH; lia].
Qed.
Local Lemma V293_rekey_nth_other : forall entries p q v,
  p <> q -> nth p (update_nth_val q entries v) Vnull = nth p entries Vnull.
Proof.
  induction entries as [ | x xs IH]; intros [ | p] [ | q] v N;
    simpl in *; try reflexivity; try congruence. apply IH. congruence.
Qed.
Local Lemma V293_rekey_update_length : forall entries p v,
  length (update_nth_val p entries v) = length entries.
Proof.
  induction entries as [ | x xs IH]; intros [ | p] v; simpl; auto.
Qed.

Theorem V293_task_prio_rekey_table_model : forall tp M M1 M2 b entries old new next,
  length entries = 13 -> old < 13 -> new < 13 ->
  V293_table_loads tp M b entries ->
  store (Tptr tp) M (b,(4*Z.of_nat old)%Z) Vnull = Some M1 ->
  store (Tptr tp) M1 (b,(4*Z.of_nat new)%Z) (Vptr next) = Some M2 ->
  V293_table_loads tp M2 b
    (update_nth_val new (update_nth_val old entries Vnull) (Vptr next)).
Proof.
  intros tp M M1 M2 b entries old new next Len Ro Rn View S1 S2 p Rp.
  destruct (Nat.eq_dec p new) as [E | Nn].
  - subst p. rewrite V293_rekey_nth_same by (rewrite V293_rekey_update_length; lia).
    eapply V293_store_readback; [reflexivity | exact S2].
  - rewrite V293_rekey_nth_other by exact Nn.
    rewrite V293_pointer_store_other_slot with (M := M1) (p := new) (v := Vptr next)
      by (try congruence; exact S2).
    destruct (Nat.eq_dec p old) as [E | No].
    + subst p. rewrite V293_rekey_nth_same by lia.
      eapply V293_store_readback; [reflexivity | exact S1].
    + rewrite V293_rekey_nth_other by exact No.
      rewrite V293_pointer_store_other_slot with (M := M) (p := old) (v := Vnull)
        by (try congruence; exact S1). apply View; exact Rp.
Qed.

(* Post-update bitmap/task correspondence remains explicit: this theorem
   does NOT invent a proof of the intervening bitmap/TCB/event operations.
   Unlike the earlier pure-list result, the old slot is observed in M2. *)
Theorem V293_task_prio_rekey_ready_choice :
  forall tp M M1 M2 b entries old new next lo hi tasks,
  length entries = 13 -> old < 13 -> new < 13 -> old <> new ->
  V293_table_loads tp M b entries ->
  store (Tptr tp) M (b,(4*Z.of_nat old)%Z) Vnull = Some M1 ->
  store (Tptr tp) M1 (b,(4*Z.of_nat new)%Z) (Vptr next) = Some M2 ->
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  V293_bitmap_tasks lo hi tasks ->
  V293_priority_table
    (update_nth_val new (update_nth_val old entries Vnull) (Vptr next)) tasks ->
  load (Tptr tp) M2 (b,(4*Z.of_nat old)%Z) = Some Vnull /\
  V293_ready_select lo hi (V293_ready_group lo hi) <> old.
Proof.
  intros tp M M1 M2 b entries old new next lo hi tasks Len Ro Rn N View S1 S2
    Hlo Hhi Hr Hb Htable.
  assert (Empty : load (Tptr tp) M2 (b,(4*Z.of_nat old)%Z) = Some Vnull).
  { rewrite V293_pointer_store_other_slot with (M := M1) (p := new) (v := Vptr next)
      by (try congruence; exact S2).
    eapply V293_store_readback; [reflexivity | exact S1]. }
  split; [exact Empty | ]. intro E.
  destruct (V293_ready_selection_task lo hi _ tasks Hlo Hhi Hr Hb Htable)
    as (chosen & message & Htask & Hentry & Hhighest).
  pose proof (V293_task_prio_rekey_table_model tp M M1 M2 b entries old new next
    Len Ro Rn View S1 S2 old Ro) as Physical.
  rewrite E in Hentry. rewrite Hentry, Empty in Physical. discriminate.
Qed.

(* A semantic single-factor control: with the two indices equal, the second
   real store wins. This is NOT a legal full-API execution (its earlier guard
   rejects equal priorities), and is not evidence about that unmodeled guard. *)
Theorem V293_task_prio_rekey_alias_control : forall tp M b p next,
  V293_bytes_writable M b (4*Z.of_nat p)%Z 4 ->
  exists M1 M2,
    store (Tptr tp) M (b,(4*Z.of_nat p)%Z) Vnull = Some M1 /\
    store (Tptr tp) M1 (b,(4*Z.of_nat p)%Z) (Vptr next) = Some M2 /\
    load (Tptr tp) M2 (b,(4*Z.of_nat p)%Z) = Some (Vptr next) /\
    load (Tptr tp) M2 (b,(4*Z.of_nat p)%Z) <> Some Vnull.
Proof.
  intros tp M b p next W.
  destruct (V293_storebytes_exists (encode_val (Tptr tp) Vnull) M b (4*Z.of_nat p)%Z)
    as [M1 S1]; [rewrite encode_val_length; exact W | ].
  assert (W1 : V293_bytes_writable M1 b (4*Z.of_nat p)%Z 4).
  { intros k R. exists (nth k (encode_val (Tptr tp) Vnull) Undef).
    eapply V293_storebytes_nth; [exact S1 | rewrite encode_val_length; exact R]. }
  destruct (V293_storebytes_exists (encode_val (Tptr tp) (Vptr next)) M1 b (4*Z.of_nat p)%Z)
    as [M2 S2]; [rewrite encode_val_length; exact W1 | ].
  assert (Read : load (Tptr tp) M2 (b,(4*Z.of_nat p)%Z) = Some (Vptr next))
    by (eapply V293_store_readback; [reflexivity | exact S2]).
  exists M1. exists M2. repeat split; try assumption. rewrite Read. discriminate.
Qed.

(* A sparse, concrete memory witness for precisely the two touched slots and
   three operands. It is not a full array/TCB/ready invariant or an initialized
   OS state. In particular it does not assign meaning to the other 11 slots. *)
Definition V293_rekey_fixture_ge : env :=
  set (emp : env) 200%Z (20%positive,Tarray (Tptr Tvoid) 13).
Definition V293_rekey_fixture_le : env :=
  set (set (set (emp : env) 201%Z (21%positive,Tint8))
    202%Z (22%positive,Tint8)) 203%Z (23%positive,Tptr Tvoid).
Definition V293_rekey_fixture_memory : mem :=
  (set (set (set (set (set (set (set (set (set (set (set (set (set (set (emp : mem)
    (20%positive,32%Z) (true,Pointer 15%positive Int.zero 3))
    (20%positive,33%Z) (true,Pointer 15%positive Int.zero 2))
    (20%positive,34%Z) (true,Pointer 15%positive Int.zero 1))
    (20%positive,35%Z) (true,Pointer 15%positive Int.zero 0))
    (20%positive,24%Z) (true,Byte Byte.zero))
    (20%positive,25%Z) (true,Byte Byte.zero))
    (20%positive,26%Z) (true,Byte Byte.zero))
    (20%positive,27%Z) (true,Byte Byte.zero))
    (21%positive,0%Z) (true,Byte (Byte.repr 8)))
    (22%positive,0%Z) (true,Byte (Byte.repr 6)))
    (23%positive,0%Z) (true,Pointer 15%positive Int.zero 3))
    (23%positive,1%Z) (true,Pointer 15%positive Int.zero 2))
    (23%positive,2%Z) (true,Pointer 15%positive Int.zero 1))
    (23%positive,3%Z) (true,Pointer 15%positive Int.zero 0)).

Local Ltac rekey_fixture_compute :=
  unfold addr,offset,block in *;
  cbv beta iota zeta delta [V293_rekey_fixture_memory
    load loadm typelen loadbytes encode_val inj_pointer inj_bytes List.map
    encode_int V293_byteval];
  repeat first [rewrite map_get_set | rewrite map_get_set' by (intro E; inversion E; lia) |
    rewrite map_emp_get]; reflexivity.

Local Ltac rekey_fixture_load :=
  lazymatch goal with
  | |- load (Tptr ?tp) ?M (?b,?i) = Some ?v =>
    let Bytes := fresh "Bytes" in
    assert (Bytes : loadbytes M (b,i) 4 = Some (encode_val (Tptr tp) v));
    [ change (loadbytes M (b,i) (length (encode_val (Tptr tp) v)) = Some (encode_val (Tptr tp) v));
      apply V293_loadbytes_get;
      intros [ | [ | [ | [ | k]]]] R; try (cbn [encode_val inj_pointer list_repeat length] in R; lia);
      exists true; rekey_fixture_compute
    | change (match loadbytes M (b,i) 4 with Some bs => Some (decode_val (Tptr tp) bs) | None => None end = Some v);
      rewrite Bytes; reflexivity ]
  | _ => rekey_fixture_compute
  end.

Theorem V293_task_prio_rekey_fixture_execution : forall P ks,
  load (Tptr Tvoid) V293_rekey_fixture_memory (20%positive,32%Z) =
    Some (Vptr (15%positive,Int.zero)) /\
  load (Tptr Tvoid) V293_rekey_fixture_memory (20%positive,24%Z) = Some Vnull /\
  exists M2,
    cstepstar P
      (curs (V293_task_prio_rekey 200%Z 201%Z 202%Z 203%Z),(kenil,ks))
      (V293_rekey_fixture_ge,V293_rekey_fixture_le,V293_rekey_fixture_memory)
      (curs (sskip None),(kenil,ks)) (V293_rekey_fixture_ge,V293_rekey_fixture_le,M2) /\
    load (Tptr Tvoid) M2 (20%positive,32%Z) = Some Vnull /\
    load (Tptr Tvoid) M2 (20%positive,24%Z) = Some (Vptr (15%positive,Int.zero)).
Proof.
  intros P ks. split; [rekey_fixture_load | ]. split; [rekey_fixture_load | ].
  assert (Wo : V293_bytes_writable V293_rekey_fixture_memory 20%positive 32%Z 4).
  { intros [ | [ | [ | [ | k]]]] R; try (simpl in R; lia);
      eexists; rekey_fixture_compute. }
  assert (Wn : V293_bytes_writable V293_rekey_fixture_memory 20%positive 24%Z 4).
  { intros [ | [ | [ | [ | k]]]] R; try (simpl in R; lia);
      eexists; rekey_fixture_compute. }
  destruct (V293_OSTaskChangePrio_table_execution P ks
    V293_rekey_fixture_ge V293_rekey_fixture_le V293_rekey_fixture_memory
    200%Z 201%Z 202%Z 203%Z Tvoid 20%positive 21%positive 22%positive 23%positive
    8 6 (15%positive,Int.zero)) as (M1 & M2 & S1 & S2 & Exec & Lold & Lnew & Frame).
  all: try (unfold V293_rekey_fixture_ge,V293_rekey_fixture_le;
    repeat first [rewrite map_get_set | rewrite map_get_set' by discriminate | rewrite map_emp_get];
    reflexivity).
  all: try lia; try discriminate; try exact Wo; try exact Wn; try rekey_fixture_load.
  exists M2. auto.
Qed.

(* Byte arithmetic used by os_task.c:125,127,129,130.  The complement
   is explicitly narrowed BEFORE the AND, as in the frozen C cast. *)
Definition V293_rekey_clear_int (row bit : nat) : int32 :=
  Int.and (Int.repr (Z.of_nat row))
    (Int.modu (Int.not (Int.shl Int.one (Int.repr (Z.of_nat bit)))) (Int.repr 256)).
Definition V293_rekey_set_int (row bit : nat) : int32 :=
  Int.or (Int.repr (Z.of_nat row))
    (Int.shl Int.one (Int.repr (Z.of_nat bit))).

Definition V293_rekey_byte_check (row bit : nat) : bool :=
  (Nat.clearbit row bit <? 256) && (Nat.setbit row bit <? 256) &&
  Int.eq (V293_rekey_clear_int row bit) (Int.repr (Z.of_nat (Nat.clearbit row bit))) &&
  Int.eq (V293_rekey_set_int row bit) (Int.repr (Z.of_nat (Nat.setbit row bit))).

Lemma V293_rekey_bytes_checked :
  forallb (fun row => forallb (V293_rekey_byte_check row) (seq 0 8)) (seq 0 256) = true.
Proof. vm_compute. reflexivity. Qed.

Theorem V293_rekey_byte_arithmetic : forall row bit,
  row < 256 -> bit < 8 ->
  Nat.clearbit row bit < 256 /\ Nat.setbit row bit < 256 /\
  V293_rekey_clear_int row bit = Int.repr (Z.of_nat (Nat.clearbit row bit)) /\
  V293_rekey_set_int row bit = Int.repr (Z.of_nat (Nat.setbit row bit)).
Proof.
  intros row bit R B. pose proof V293_rekey_bytes_checked as H.
  rewrite forallb_forall in H.
  specialize (H row (proj2 (in_seq 256 0 row) ltac:(lia))).
  rewrite forallb_forall in H.
  specialize (H bit (proj2 (in_seq 8 0 bit) ltac:(lia))).
  unfold V293_rekey_byte_check in H.
  repeat rewrite andb_true_iff in H. destruct H as [[[C S] E] F].
  apply Nat.ltb_lt in C. apply Nat.ltb_lt in S.
  pose proof (Int.eq_spec (V293_rekey_clear_int row bit)
    (Int.repr (Z.of_nat (Nat.clearbit row bit)))) as EC. rewrite E in EC.
  pose proof (Int.eq_spec (V293_rekey_set_int row bit)
    (Int.repr (Z.of_nat (Nat.setbit row bit)))) as ES. rewrite F in ES. auto.
Qed.

(* These are values of the ready THEN branch, not memory writes.  Updating
   the pair sequentially is essential when old and new are in the same row. *)
Definition V293_ready_clear_rows (lo hi old : nat) : nat * nat :=
  if old <? 8 then (Nat.clearbit lo old, hi)
  else (lo, Nat.clearbit hi (old-8)).
Definition V293_ready_set_rows (lo hi new : nat) : nat * nat :=
  if new <? 8 then (Nat.setbit lo new, hi)
  else (lo, Nat.setbit hi (new-8)).
Definition V293_ready_rekey_rows (lo hi old new : nat) : nat * nat :=
  let cleared := V293_ready_clear_rows lo hi old in
  V293_ready_set_rows (fst cleared) (snd cleared) new.

Lemma V293_ready_clear_membership : forall lo hi old p,
  old < 13 -> p < 13 ->
  (V293_bitmap_ready (fst (V293_ready_clear_rows lo hi old))
    (snd (V293_ready_clear_rows lo hi old)) p <->
   V293_bitmap_ready lo hi p /\ p <> old).
Proof.
  intros lo hi old p O P. unfold V293_ready_clear_rows.
  destruct (old <? 8) eqn:E; [apply Nat.ltb_lt in E | apply Nat.ltb_ge in E];
    cbn [fst snd]; unfold V293_bitmap_ready;
    rewrite ?Nat.clearbit_iff; intuition lia.
Qed.

Lemma V293_ready_set_membership : forall lo hi new p,
  new < 13 -> p < 13 ->
  (V293_bitmap_ready (fst (V293_ready_set_rows lo hi new))
    (snd (V293_ready_set_rows lo hi new)) p <->
   p = new \/ V293_bitmap_ready lo hi p).
Proof.
  intros lo hi new p N P. unfold V293_ready_set_rows.
  destruct (new <? 8) eqn:E; [apply Nat.ltb_lt in E | apply Nat.ltb_ge in E];
    cbn [fst snd]; unfold V293_bitmap_ready;
    rewrite ?Nat.setbit_iff; intuition lia.
Qed.

Theorem V293_ready_rekey_membership : forall lo hi old new p,
  old < 13 -> new < 13 -> p < 13 ->
  (V293_bitmap_ready (fst (V293_ready_rekey_rows lo hi old new))
    (snd (V293_ready_rekey_rows lo hi old new)) p <->
   p = new \/ (V293_bitmap_ready lo hi p /\ p <> old)).
Proof.
  intros. unfold V293_ready_rekey_rows.
  rewrite V293_ready_set_membership by assumption.
  rewrite V293_ready_clear_membership by assumption. reflexivity.
Qed.

Lemma V293_ready_rekey_bounds : forall lo hi old new,
  lo < 256 -> hi < 256 -> old < 13 -> new < 13 ->
  fst (V293_ready_rekey_rows lo hi old new) < 256 /\
  snd (V293_ready_rekey_rows lo hi old new) < 256.
Proof.
  intros lo hi old new L H O N.
  unfold V293_ready_rekey_rows, V293_ready_clear_rows, V293_ready_set_rows.
  destruct (old <? 8) eqn:E; destruct (new <? 8) eqn:F;
    [apply Nat.ltb_lt in E; apply Nat.ltb_lt in F |
     apply Nat.ltb_lt in E; apply Nat.ltb_ge in F |
     apply Nat.ltb_ge in E; apply Nat.ltb_lt in F |
     apply Nat.ltb_ge in E; apply Nat.ltb_ge in F]; cbn [fst snd].
  - pose proof (V293_rekey_byte_arithmetic lo old L E) as [C _].
    pose proof (V293_rekey_byte_arithmetic _ new C F) as [_ [S _]]. auto.
  - pose proof (V293_rekey_byte_arithmetic lo old L E) as [C _].
    pose proof (V293_rekey_byte_arithmetic hi (new-8) H ltac:(lia)) as [_ [S _]]. auto.
  - pose proof (V293_rekey_byte_arithmetic hi (old-8) H ltac:(lia)) as [C _].
    pose proof (V293_rekey_byte_arithmetic lo new L F) as [_ [S _]]. auto.
  - pose proof (V293_rekey_byte_arithmetic hi (old-8) H ltac:(lia)) as [C _].
    pose proof (V293_rekey_byte_arithmetic _ (new-8) C ltac:(lia)) as [_ [S _]]. auto.
Qed.

(* Invalid high-row positions 5..7 remain unconstrained and are preserved,
   rather than forbidden to simplify the scheduler proof. *)
Theorem V293_ready_rekey_high_bits : forall lo hi old new bit,
  old < 13 -> new < 13 -> 5 <= bit ->
  Nat.testbit (snd (V293_ready_rekey_rows lo hi old new)) bit = Nat.testbit hi bit.
Proof.
  intros lo hi old new bit O N B.
  unfold V293_ready_rekey_rows, V293_ready_clear_rows, V293_ready_set_rows.
  destruct (old <? 8) eqn:E; destruct (new <? 8) eqn:F;
    try apply Nat.ltb_ge in E; try apply Nat.ltb_ge in F;
    cbn [fst snd]; rewrite ?Nat.setbit_neq, ?Nat.clearbit_neq by lia; reflexivity.
Qed.

Lemma V293_rekey_task_entry : forall entries tasks t p status message,
  V293_priority_table entries tasks -> p < 13 ->
  get tasks t = Some (Int.repr (Z.of_nat p),status,message) ->
  nth p entries Vnull = Vptr t.
Proof.
  intros entries tasks t p status message [_ Table] P T.
  destruct (Table _ _ _ _ T) as [q [Q [Eq Entry]]].
  assert (p=q) by (eapply V293_priority_repr_injective; eassumption).
  subst q. exact Entry.
Qed.

Lemma V293_rekey_priority_unique : forall entries tasks t u p status message status' message',
  V293_priority_table entries tasks -> p < 13 ->
  get tasks t = Some (Int.repr (Z.of_nat p),status,message) ->
  get tasks u = Some (Int.repr (Z.of_nat p),status',message') -> t=u.
Proof.
  intros. pose proof (V293_rekey_task_entry _ _ _ _ _ _ H H0 H1) as T.
  pose proof (V293_rekey_task_entry _ _ _ _ _ _ H H0 H2) as U.
  rewrite T in U. inversion U. reflexivity.
Qed.

Theorem V293_rekey_task_table_preserved : forall entries tasks next old new status message,
  old < 13 -> new < 13 ->
  V293_priority_table entries tasks ->
  get tasks next = Some (Int.repr (Z.of_nat old),status,message) ->
  nth new entries Vnull = Vnull ->
  V293_priority_table
    (update_nth_val new (update_nth_val old entries Vnull) (Vptr next))
    (set tasks next (Int.repr (Z.of_nat new),status,message)).
Proof.
  intros entries tasks next old new status message O N Table Task Empty.
  destruct Table as [Len Entries]. split.
  - rewrite !V293_rekey_update_length. exact Len.
  - intros t priority state msg T.
    destruct (TcbMod.eq_dec t next) as [Eq | Ne].
    + subst t. rewrite map_get_set in T. inversion T; subst priority state msg.
      exists new. split; [exact N | ]. split; [reflexivity | ].
      rewrite V293_rekey_nth_same by (rewrite V293_rekey_update_length; lia). reflexivity.
    + rewrite map_get_set' in T by congruence.
      destruct (Entries _ _ _ _ T) as [p [P [Eq Entry]]].
      assert (Po : p <> old).
      { intro E; subst p. subst priority.
        pose proof (V293_rekey_priority_unique entries tasks t next old state msg status message
          (conj Len Entries) O T Task). contradiction. }
      assert (Pn : p <> new).
      { intro E; subst p. rewrite Empty in Entry. discriminate. }
      exists p. split; [exact P | ]. split; [exact Eq | ].
      rewrite !V293_rekey_nth_other by assumption. exact Entry.
Qed.

(* Ready-task case: the relation after the update is DERIVED from the entry
   relation and one task-map write.  No post-state bitmap oracle is assumed. *)
Theorem V293_rekey_ready_tasks_preserved : forall lo hi entries tasks next old new message,
  old < 13 -> new < 13 ->
  V293_priority_table entries tasks -> V293_bitmap_tasks lo hi tasks ->
  get tasks next = Some (Int.repr (Z.of_nat old),rdy,message) ->
  V293_bitmap_tasks (fst (V293_ready_rekey_rows lo hi old new))
    (snd (V293_ready_rekey_rows lo hi old new))
    (set tasks next (Int.repr (Z.of_nat new),rdy,message)).
Proof.
  intros lo hi entries tasks next old new message O N Table Bitmap Task p P.
  rewrite V293_ready_rekey_membership by assumption. split.
  - intros [E | [Ready Ne]].
    + subst p. exists next. exists message. apply map_get_set.
    + destruct (proj1 (Bitmap p P) Ready) as [t [msg T]].
      assert (Nt : t <> next).
      { intro E; subst t. rewrite Task in T.
        assert (Eq : Int.repr (Z.of_nat old) = Int.repr (Z.of_nat p)) by congruence.
        pose proof (V293_priority_repr_injective old p O P Eq). congruence. }
      exists t. exists msg. rewrite map_get_set' by congruence. exact T.
  - intros [t [msg T]]. destruct (TcbMod.eq_dec t next) as [E | Ne].
    + subst t. rewrite map_get_set in T. left.
      assert (Eq : Int.repr (Z.of_nat p) = Int.repr (Z.of_nat new)) by congruence.
      eapply V293_priority_repr_injective; eassumption.
    + rewrite map_get_set' in T by congruence. right. split.
      * apply (proj2 (Bitmap p P)). exists t. exists msg. exact T.
      * intro E; subst p.
        pose proof (V293_rekey_priority_unique entries tasks t next old rdy msg rdy message
          Table O T Task). contradiction.
Qed.

Lemma V293_rekey_byte_narrow : forall n,
  n < 256 -> Int.modu (Int.repr (Z.of_nat n)) (Int.repr 256) = Int.repr (Z.of_nat n).
Proof.
  intros n N. unfold Int.modu.
  rewrite !Int.unsigned_repr by
    (unfold Int.max_unsigned, Int.modulus, Int.wordsize; simpl; lia).
  rewrite Z.mod_small by lia. reflexivity.
Qed.

Theorem V293_task_prio_byte_expr_eval : forall ge le M row mask r bit,
  r < 256 -> bit < 8 ->
  evaltype row (ge,le,M) = Some Tint8 ->
  evaltype mask (ge,le,M) = Some Tint8 ->
  evalval row (ge,le,M) = Some (V293_byteval r) ->
  evalval mask (ge,le,M) = Some (Vint32 (Int.shl Int.one (Int.repr (Z.of_nat bit)))) ->
  evaltype (V293_task_prio_clear_expr row mask) (ge,le,M) = Some Tint8 /\
  evaltype (V293_task_prio_set_expr row mask) (ge,le,M) = Some Tint8 /\
  evalval (V293_task_prio_clear_expr row mask) (ge,le,M) =
    Some (V293_byteval (Nat.clearbit r bit)) /\
  evalval (V293_task_prio_set_expr row mask) (ge,le,M) =
    Some (V293_byteval (Nat.setbit r bit)).
Proof.
  intros ge le M row mask r bit R B Hrowtype Hmasktype Hrowvalue Hmaskvalue.
  destruct (V293_rekey_byte_arithmetic r bit R B) as [C [S [EC ES]]].
  unfold V293_task_prio_clear_expr, V293_task_prio_set_expr.
  cbn [evaltype evalval]. rewrite Hrowtype, Hmasktype, Hrowvalue, Hmaskvalue.
  cbn [cast_eval uop_type uop_eval negint bop_type bop_int_type bop_eval and or].
  change (Some Tint8 = Some Tint8 /\ Some Tint8 = Some Tint8 /\
    Some (Vint32 (Int.modu (V293_rekey_clear_int r bit) (Int.repr 256))) =
      Some (V293_byteval (Nat.clearbit r bit)) /\
    Some (Vint32 (Int.modu (V293_rekey_set_int r bit) (Int.repr 256))) =
      Some (V293_byteval (Nat.setbit r bit))).
  rewrite EC, ES, !V293_rekey_byte_narrow by assumption. repeat split; reflexivity.
Qed.

(* Actual ordering of the GROUP operations for the ready THEN branch.
   This is a value-level result, not an assertion of physical stores. *)
Definition V293_ready_clear_group (lo hi old : nat) : nat :=
  let rows := V293_ready_clear_rows lo hi old in
  if (if old <? 8 then fst rows else snd rows) =? 0
  then Nat.clearbit (V293_ready_group lo hi) (if old <? 8 then 0 else 1)
  else V293_ready_group lo hi.
Definition V293_ready_rekey_group (lo hi old new : nat) : nat :=
  Nat.setbit (V293_ready_clear_group lo hi old) (if new <? 8 then 0 else 1).

Lemma V293_ready_clear_group_correct : forall lo hi old,
  V293_ready_clear_group lo hi old =
  V293_ready_group (fst (V293_ready_clear_rows lo hi old))
    (snd (V293_ready_clear_rows lo hi old)).
Proof.
  intros lo hi old.
  unfold V293_ready_clear_group, V293_ready_clear_rows.
  destruct (old <? 8) eqn:E; cbn [fst snd]; unfold V293_ready_group.
  - destruct (lo =? 0) eqn:L; destruct (hi =? 0) eqn:H;
      destruct (Nat.clearbit lo old =? 0) eqn:C; try reflexivity.
    all: apply Nat.eqb_eq in L; subst lo;
      unfold Nat.clearbit in C; rewrite Nat.ldiff_0_l in C; discriminate.
  - destruct (lo =? 0) eqn:L; destruct (hi =? 0) eqn:H;
      destruct (Nat.clearbit hi (old-8) =? 0) eqn:C; try reflexivity.
    all: apply Nat.eqb_eq in H; subst hi;
      unfold Nat.clearbit in C; rewrite Nat.ldiff_0_l in C; discriminate.
Qed.

Lemma V293_ready_set_group_correct : forall lo hi new,
  Nat.setbit (V293_ready_group lo hi) (if new <? 8 then 0 else 1) =
  V293_ready_group (fst (V293_ready_set_rows lo hi new))
    (snd (V293_ready_set_rows lo hi new)).
Proof.
  intros lo hi new. unfold V293_ready_set_rows.
  assert (Nonzero : forall a b, (Nat.setbit a b =? 0) = false).
  { intros a b. apply Nat.eqb_neq. intro E.
    pose proof (Nat.setbit_eq a b) as H. rewrite E, Nat.testbit_0_l in H. discriminate. }
  destruct (new <? 8) eqn:E; cbn [fst snd]; unfold V293_ready_group; rewrite Nonzero;
    destruct (lo =? 0); destruct (hi =? 0); reflexivity.
Qed.

Theorem V293_ready_rekey_group_correct : forall lo hi old new,
  V293_ready_rekey_group lo hi old new =
  V293_ready_group (fst (V293_ready_rekey_rows lo hi old new))
    (snd (V293_ready_rekey_rows lo hi old new)).
Proof.
  intros. unfold V293_ready_rekey_group, V293_ready_rekey_rows.
  rewrite V293_ready_clear_group_correct. apply V293_ready_set_group_correct.
Qed.

(* Stable forward correspondence for the READY-task path.  Physical table
   stores are explicit; bitmap/TCB writes are NOT claimed to execute.  Unlike
   V293_task_prio_rekey_ready_choice, all post-state task/table/bitmap
   relations and group consistency are proved from entry relations. *)
Theorem V293_task_prio_rekey_ready_correspondence :
  forall tp M M1 M2 b entries tasks next old new lo hi message,
  old < 13 -> new < 13 -> old <> new -> lo < 256 -> hi < 256 ->
  V293_priority_table entries tasks -> V293_bitmap_tasks lo hi tasks ->
  get tasks next = Some (Int.repr (Z.of_nat old),rdy,message) ->
  nth new entries Vnull = Vnull -> V293_table_loads tp M b entries ->
  store (Tptr tp) M (b,(4*Z.of_nat old)%Z) Vnull = Some M1 ->
  store (Tptr tp) M1 (b,(4*Z.of_nat new)%Z) (Vptr next) = Some M2 ->
  let rows := V293_ready_rekey_rows lo hi old new in
  let tasks' := set tasks next (Int.repr (Z.of_nat new),rdy,message) in
  let entries' := update_nth_val new (update_nth_val old entries Vnull) (Vptr next) in
  V293_bitmap_ready lo hi old /\ fst rows < 256 /\ snd rows < 256 /\
  V293_ready_rekey_group lo hi old new = V293_ready_group (fst rows) (snd rows) /\
  V293_bitmap_tasks (fst rows) (snd rows) tasks' /\
  V293_priority_table entries' tasks' /\ V293_table_loads tp M2 b entries' /\
  load (Tptr tp) M2 (b,(4*Z.of_nat old)%Z) = Some Vnull /\
  exists chosen msg,
    get tasks' chosen = Some
      (Int.repr (Z.of_nat (V293_ready_select (fst rows) (snd rows)
        (V293_ready_rekey_group lo hi old new))),rdy,msg) /\
    load (Tptr tp) M2 (b,(4*Z.of_nat (V293_ready_select (fst rows) (snd rows)
      (V293_ready_rekey_group lo hi old new)))%Z) = Some (Vptr chosen) /\
    V293_highest_ready tasks' chosen /\
    V293_ready_select (fst rows) (snd rows) (V293_ready_rekey_group lo hi old new) <> old.
Proof.
  intros tp M M1 M2 b entries tasks next old new lo hi message
    O N D L H Table Bitmap Task Empty View S1 S2.
  cbn zeta.
  pose proof (V293_rekey_ready_tasks_preserved lo hi entries tasks next old new message
    O N Table Bitmap Task) as Bpost.
  pose proof (V293_rekey_task_table_preserved entries tasks next old new rdy message
    O N Table Task Empty) as Tpost.
  pose proof (V293_task_prio_rekey_table_model tp M M1 M2 b entries old new next
    (proj1 Table) O N View S1 S2) as Vpost.
  destruct (V293_ready_rekey_bounds lo hi old new L H O N) as [Lpost Hpost].
  pose proof (V293_ready_rekey_group_correct lo hi old new) as Group.
  assert (Nonempty : exists p, V293_bitmap_ready
    (fst (V293_ready_rekey_rows lo hi old new))
    (snd (V293_ready_rekey_rows lo hi old new)) p).
  { exists new. apply V293_ready_rekey_membership; auto. }
  destruct (V293_task_prio_rekey_ready_choice tp M M1 M2 b entries old new next
    _ _ _ (proj1 Table) O N D View S1 S2 Lpost Hpost Nonempty Bpost Tpost)
    as [Oldnull Different].
  split.
  { apply (proj2 (Bitmap old O)). exists next. exists message. exact Task. }
  split; [exact Lpost | ]. split; [exact Hpost | ]. split; [exact Group | ].
  split; [exact Bpost | ]. split; [exact Tpost | ]. split; [exact Vpost | ].
  split; [exact Oldnull | ]. rewrite Group.
  destruct (V293_ready_selection_task _ _ _ _ Lpost Hpost Nonempty Bpost Tpost)
    as (chosen & msg & T & Entry & Highest).
  exists chosen. exists msg. split; [exact T | ]. split.
  - rewrite Vpost.
    + rewrite Entry. reflexivity.
    + eapply V293_ready_selection_range; eauto.
  - split; assumption.
Qed.

(* Concrete value checks, not initialization/reachability witnesses. *)
Theorem V293_ready_rekey_row_controls :
  V293_ready_rekey_rows 0 1 8 6 = (64,0) /\ V293_ready_rekey_group 0 1 8 6 = 1 /\
  V293_ready_rekey_rows 0 1 8 10 = (0,4) /\ V293_ready_rekey_group 0 1 8 10 = 2 /\
  V293_ready_rekey_rows 20 0 2 6 = (80,0) /\ V293_ready_rekey_group 20 0 2 6 = 1 /\
  V293_ready_rekey_rows 0 129 8 6 = (64,128) /\ V293_ready_rekey_group 0 129 8 6 = 3.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* Physical byte writes at arbitrary offsets.  These are memory operations,
   not specifications of a preselected post-state. *)
Definition V293_put_byte (M : mem) (a : addr) (n : nat) : mem :=
  set M a (true, Byte (Byte.repr (Int.unsigned (Int.repr (Z.of_nat n))))).

Lemma V293_put_byte_store : forall M a n old,
  get M a = Some (true,old) ->
  store Tint8 M a (V293_byteval n) = Some (V293_put_byte M a n).
Proof.
  intros M [b i] n old W. unfold store, V293_byteval, V293_put_byte.
  cbn [encode_val inj_bytes encode_int]. unfold inj_bytes.
  cbn [List.map storebytes]. unfold addr, offset in *. rewrite W. reflexivity.
Qed.

Lemma V293_put_byte_load : forall M a n,
  n < 256 -> load Tint8 (V293_put_byte M a n) a = Some (V293_byteval n).
Proof.
  intros M [b i] n R. eapply V293_encoded_byte_load with (permission := true).
  - exact R.
  - unfold V293_put_byte. apply map_get_set.
Qed.

Lemma V293_put_byte_other : forall M a n other,
  other <> a -> get (V293_put_byte M a n) other = get M other.
Proof. intros. unfold V293_put_byte. apply map_get_set'. congruence. Qed.

Lemma V293_put_byte_other_load : forall M a n other,
  other <> a -> load Tint8 (V293_put_byte M a n) other = load Tint8 M other.
Proof.
  intros M a n [b i] N. unfold load,loadm. cbn [typelen loadbytes].
  rewrite V293_put_byte_other by exact N. reflexivity.
Qed.

Lemma V293_assign_byte_offset_execution : forall P ge le M M' lhs rhs b off value ks,
  evaltype lhs (ge,le,M) = Some Tint8 -> evaltype rhs (ge,le,M) = Some Tint8 ->
  evaladdr lhs (ge,le,M) = Some (Vptr (b,Int.repr off)) ->
  evalval rhs (ge,le,M) = Some value -> (0 <= off <= Int.max_unsigned)%Z ->
  store Tint8 M (b,off) value = Some M' ->
  cstepstar P (curs (sassign lhs rhs),(kenil,ks)) (ge,le,M)
    (curs (sskip None),(kenil,ks)) (ge,le,M').
Proof.
  intros P ge le M M' lhs rhs b off value ks Tl Tr A V R S.
  eapply c_stepstarn.
  { eapply stmt_step; [reflexivity | ]. eapply sassign_step; try eassumption.
    apply eq_int. auto. }
  eapply V293_cstepstar_trans.
  { apply V293_expr_steps. apply evalval_imply_estepstar. exact V. }
  eapply c_stepstarn. { eapply stmt_step; [reflexivity | ]. constructor. }
  eapply V293_cstepstar_trans.
  { apply V293_expr_steps. apply evalval_imply_estepstar. eapply evaladdr_val_eq; eassumption. }
  eapply c_stepstarn.
  { eapply stmt_step; [reflexivity | ]. eapply sassignend_step; try reflexivity.
    cbn [addrval_to_addr]. rewrite Int.unsigned_repr by exact R. exact S. }
  apply c_stepstar0.
Qed.

Definition V293_prio_row (p : nat) : nat := if p <? 8 then 0 else 1.
Definition V293_prio_bit (p : nat) : nat := if p <? 8 then p else p-8.
Definition V293_mask_value (bit : nat) : val :=
  Vint32 (Int.shl Int.one (Int.repr (Z.of_nat bit))).

(* Only byte operands live here, never the shared rows/group bytes.
   The list is standard variable/value binding data, not a second memory model. *)
Definition V293_rekey_locals (ge le : env) (M : mem) (br bg : block)
    (bindings : list (var * val)) : Prop :=
  forall x value, In (x,value) bindings -> exists b,
    get le x = Some (b,Tint8) /\ b <> br /\ b <> bg /\
    load Tint8 M (b,0%Z) = Some value.

Lemma V293_rekey_locals_write : forall ge le M br bg bindings a n,
  V293_rekey_locals ge le M br bg bindings ->
  fst a = br \/ fst a = bg ->
  V293_rekey_locals ge le (V293_put_byte M a n) br bg bindings.
Proof.
  intros ge le M br bg bindings [b i] n H A x value I.
  destruct (H x value I) as (bx & E & Nr & Ng & L).
  exists bx. repeat split; try assumption.
  rewrite V293_put_byte_other_load; [exact L | ]. simpl in A. intro C.
  inversion C; subst. intuition.
Qed.

Lemma V293_rekey_local_eval : forall ge le M br bg bindings x value,
  V293_rekey_locals ge le M br bg bindings -> In (x,value) bindings ->
  evaltype (evar x) (ge,le,M) = Some Tint8 /\
  evalval (evar x) (ge,le,M) = Some value.
Proof.
  intros ge le M br bg bindings x value H I.
  destruct (H x value I) as (b & E & _ & _ & L).
  cbn [evaltype evalval get_lenv get_genv get_mem]. rewrite E. auto.
Qed.

Definition V293_rekey_bitmap_loads M br bg lo hi group : Prop :=
  load Tint8 M (br,0%Z) = Some (V293_byteval lo) /\
  load Tint8 M (br,1%Z) = Some (V293_byteval hi) /\
  load Tint8 M (bg,0%Z) = Some (V293_byteval group).
Definition V293_rekey_bitmap_writable M br bg : Prop :=
  (exists v, get M (br,0%Z) = Some (true,v)) /\
  (exists v, get M (br,1%Z) = Some (true,v)) /\
  (exists v, get M (bg,0%Z) = Some (true,v)).

Lemma V293_rekey_writable_write : forall M br bg a n,
  V293_rekey_bitmap_writable M br bg ->
  V293_rekey_bitmap_writable (V293_put_byte M a n) br bg.
Proof.
  intros M br bg a n (L & H & G). unfold V293_rekey_bitmap_writable.
  assert (W : forall other, (exists v, get M other = Some (true,v)) ->
    exists v, get (V293_put_byte M a n) other = Some (true,v)).
  { intros other [v V]. destruct (addr_eq_dec other a) as [E|N].
    - subst other. eexists. unfold V293_put_byte. apply map_get_set.
    - exists v. rewrite V293_put_byte_other by exact N. exact V. }
  repeat split; apply W; assumption.
Qed.

Definition V293_rekey_rmw_expr (clear : bool) (lhs mask : expr) : expr :=
  if clear then V293_task_prio_clear_expr lhs mask else V293_task_prio_set_expr lhs mask.
Definition V293_rekey_rmw_value (clear : bool) (row bit : nat) : nat :=
  if clear then Nat.clearbit row bit else Nat.setbit row bit.

(* One real read/modify/write: no successful-store or composite RHS premise. *)
Theorem V293_rekey_byte_rmw_execution :
  forall P ks ge le M lhs mask b off row bit clear,
  row < 256 -> bit < 8 -> (0 <= off <= Int.max_unsigned)%Z ->
  evaltype lhs (ge,le,M) = Some Tint8 ->
  evaladdr lhs (ge,le,M) = Some (Vptr (b,Int.repr off)) ->
  evalval lhs (ge,le,M) = Some (V293_byteval row) ->
  evaltype mask (ge,le,M) = Some Tint8 ->
  evalval mask (ge,le,M) = Some (V293_mask_value bit) ->
  (exists v, get M (b,off) = Some (true,v)) ->
  let value := V293_rekey_rmw_value clear row bit in
  let M' := V293_put_byte M (b,off) value in
  value < 256 /\ store Tint8 M (b,off) (V293_byteval value) = Some M' /\
  cstepstar P (curs (sassign lhs (V293_rekey_rmw_expr clear lhs mask)),(kenil,ks)) (ge,le,M)
    (curs (sskip None),(kenil,ks)) (ge,le,M') /\
  load Tint8 M' (b,off) = Some (V293_byteval value) /\
  (forall other, other <> (b,off) -> get M' other = get M other).
Proof.
  intros P ks ge le M lhs mask b off row bit clear R B Off Tl A Vl Tm Vm [v W].
  cbn zeta.
  destruct (V293_rekey_byte_arithmetic row bit R B) as [C [S _]].
  destruct (V293_task_prio_byte_expr_eval ge le M lhs mask row bit R B Tl Tm Vl Vm)
    as [Tc [Ts [Vc Vs]]].
  assert (Bound : V293_rekey_rmw_value clear row bit < 256)
    by (destruct clear; assumption).
  assert (Store : store Tint8 M (b,off)
    (V293_byteval (V293_rekey_rmw_value clear row bit)) =
    Some (V293_put_byte M (b,off) (V293_rekey_rmw_value clear row bit)))
    by (eapply V293_put_byte_store; exact W).
  split; [exact Bound | ]. split; [exact Store | ]. split.
  - eapply V293_assign_byte_offset_execution; try eassumption;
      unfold V293_rekey_rmw_expr; destruct clear; assumption.
  - split; [apply V293_put_byte_load; exact Bound | ].
    intros. apply V293_put_byte_other. exact H.
Qed.

Definition V293_ready_replace_row (lo hi y value : nat) : nat * nat :=
  if y =? 0 then (value,hi) else (lo,value).

Lemma V293_rekey_row_loads_write : forall M br bg lo hi g y value,
  br <> bg -> y < 2 -> value < 256 ->
  V293_rekey_bitmap_loads M br bg lo hi g ->
  V293_rekey_bitmap_loads (V293_put_byte M (br,Z.of_nat y) value) br bg
    (fst (V293_ready_replace_row lo hi y value))
    (snd (V293_ready_replace_row lo hi y value)) g.
Proof.
  intros M br bg lo hi g y value N Y V (L & H & G).
  destruct y as [ | [ | y]]; try lia; cbn [V293_ready_replace_row fst snd Z.of_nat].
  - split; [apply V293_put_byte_load; exact V | ]. split;
      rewrite V293_put_byte_other_load; try assumption; congruence.
  - split; [rewrite V293_put_byte_other_load; [exact L|congruence] | ].
    split; [apply V293_put_byte_load; exact V | ].
    rewrite V293_put_byte_other_load; [exact G|congruence].
Qed.

Lemma V293_rekey_group_loads_write : forall M br bg lo hi g value,
  br <> bg -> value < 256 -> V293_rekey_bitmap_loads M br bg lo hi g ->
  V293_rekey_bitmap_loads (V293_put_byte M (bg,0%Z) value) br bg lo hi value.
Proof.
  intros M br bg lo hi g value N V (L & H & G). split.
  - rewrite V293_put_byte_other_load; [exact L|congruence].
  - split; [rewrite V293_put_byte_other_load; [exact H|congruence] | ].
    apply V293_put_byte_load. exact V.
Qed.

Lemma V293_rekey_row_eval : forall ge le M rows index br lo hi g bg y,
  get le rows = None -> get ge rows = Some (br,Tarray Tint8 2) ->
  evaltype index (ge,le,M) = Some Tint8 ->
  evalval index (ge,le,M) = Some (V293_byteval y) -> y < 2 ->
  V293_rekey_bitmap_loads M br bg lo hi g ->
  evaltype (earrayelem (evar rows) index) (ge,le,M) = Some Tint8 /\
  evaladdr (earrayelem (evar rows) index) (ge,le,M) =
    Some (Vptr (br,Int.repr (Z.of_nat y))) /\
  evalval (earrayelem (evar rows) index) (ge,le,M) =
    Some (V293_byteval (V293_ready_row lo hi y)).
Proof.
  intros ge le M rows index br lo hi g bg y Nr Gr Ti Vi Y (L & H & G).
  assert (BaseT : evaltype (evar rows) (ge,le,M) = Some (Tarray Tint8 2)).
  { cbn [evaltype get_lenv get_genv]. rewrite Nr,Gr. reflexivity. }
  assert (BaseV : evalval (evar rows) (ge,le,M) = Some (Vptr (br,Int.zero))).
  { cbn [evalval evaltype get_lenv get_genv get_mem]. rewrite Nr,Gr. reflexivity. }
  assert (Load : load Tint8 M (br,Z.of_nat y) = Some (V293_byteval (V293_ready_row lo hi y))).
  { destruct y as [ | [ | y]]; try lia; assumption. }
  destruct (V293_eval_byte_array ge le M (evar rows) index br 2 y _
    BaseT BaseV Ti Vi Y ltac:(lia) Load) as [V T].
  split; [exact T | ]. split; [ | exact V].
  cbn [evaladdr]. rewrite BaseT,BaseV,Vi. unfold V293_byteval.
  simpl typelen. rewrite (Int.mul_commut Int.one), Int.mul_one, Int.add_zero_l. reflexivity.
Qed.

Lemma V293_rekey_row_execution :
  forall P ks ge le M rows index mask br bg lo hi g y bit clear bindings,
  br <> bg -> lo < 256 -> hi < 256 -> y < 2 -> bit < 8 ->
  get le rows = None -> get ge rows = Some (br,Tarray Tint8 2) ->
  V293_rekey_bitmap_loads M br bg lo hi g -> V293_rekey_bitmap_writable M br bg ->
  V293_rekey_locals ge le M br bg bindings ->
  In (index,V293_byteval y) bindings -> In (mask,V293_mask_value bit) bindings ->
  let value := V293_rekey_rmw_value clear (V293_ready_row lo hi y) bit in
  let M' := V293_put_byte M (br,Z.of_nat y) value in
  cstepstar P (curs (sassign (earrayelem (evar rows) (evar index))
    (V293_rekey_rmw_expr clear (earrayelem (evar rows) (evar index)) (evar mask))),
    (kenil,ks)) (ge,le,M) (curs (sskip None),(kenil,ks)) (ge,le,M') /\
  V293_rekey_bitmap_loads M' br bg
    (fst (V293_ready_replace_row lo hi y value))
    (snd (V293_ready_replace_row lo hi y value)) g /\
  V293_rekey_bitmap_writable M' br bg /\ V293_rekey_locals ge le M' br bg bindings /\
  value < 256.
Proof.
  intros P ks ge le M rows index mask br bg lo hi g y bit clear bindings
    N L H Y B Nr Gr Loads W Loc Ii Im. cbn zeta.
  destruct (V293_rekey_local_eval ge le M br bg bindings index _ Loc Ii) as [Ti Vi].
  destruct (V293_rekey_local_eval ge le M br bg bindings mask _ Loc Im) as [Tm Vm].
  destruct (V293_rekey_row_eval ge le M rows (evar index) br lo hi g bg y
    Nr Gr Ti Vi Y Loads) as [Tr [Ar Vr]].
  assert (Row : V293_ready_row lo hi y < 256)
    by (unfold V293_ready_row; destruct (y =? 0); assumption).
  assert (Writable : exists v, get M (br,Z.of_nat y) = Some (true,v)).
  { destruct W as [W0 [W1 Wg]]. destruct y as [ | [ | y]]; try lia; assumption. }
  destruct (V293_rekey_byte_rmw_execution P ks ge le M
    (earrayelem (evar rows) (evar index)) (evar mask) br (Z.of_nat y)
    (V293_ready_row lo hi y) bit clear Row B ltac:(change (0 <= Z.of_nat y <= 4294967295)%Z; lia)
    Tr Ar Vr Tm Vm Writable) as [Bound [Store [Exec [Read Frame]]]].
  split; [exact Exec | ]. split.
  - apply V293_rekey_row_loads_write; assumption.
  - split; [apply V293_rekey_writable_write; exact W | ]. split.
    + apply V293_rekey_locals_write; [exact Loc | left; reflexivity].
    + exact Bound.
Qed.

Lemma V293_rekey_group_execution :
  forall P ks ge le M group mask br bg lo hi g bit clear bindings,
  br <> bg -> g < 256 -> bit < 8 ->
  get le group = None -> get ge group = Some (bg,Tint8) ->
  V293_rekey_bitmap_loads M br bg lo hi g -> V293_rekey_bitmap_writable M br bg ->
  V293_rekey_locals ge le M br bg bindings -> In (mask,V293_mask_value bit) bindings ->
  let value := V293_rekey_rmw_value clear g bit in
  let M' := V293_put_byte M (bg,0%Z) value in
  cstepstar P (curs (sassign (evar group)
    (V293_rekey_rmw_expr clear (evar group) (evar mask))),(kenil,ks)) (ge,le,M)
    (curs (sskip None),(kenil,ks)) (ge,le,M') /\
  V293_rekey_bitmap_loads M' br bg lo hi value /\ V293_rekey_bitmap_writable M' br bg /\
  V293_rekey_locals ge le M' br bg bindings /\ value < 256.
Proof.
  intros P ks ge le M group mask br bg lo hi g bit clear bindings
    N G B Ng Gg Loads W Loc Im. cbn zeta.
  destruct (V293_rekey_local_eval ge le M br bg bindings mask _ Loc Im) as [Tm Vm].
  assert (Tg : evaltype (evar group) (ge,le,M) = Some Tint8).
  { cbn [evaltype get_lenv get_genv]. rewrite Ng,Gg. reflexivity. }
  assert (Ag : evaladdr (evar group) (ge,le,M) = Some (Vptr (bg,Int.repr 0))).
  { cbn [evaladdr get_lenv get_genv]. rewrite Ng,Gg. reflexivity. }
  assert (Vg : evalval (evar group) (ge,le,M) = Some (V293_byteval g)).
  { cbn [evalval evaltype get_lenv get_genv get_mem]. rewrite Ng,Gg. exact (proj2 (proj2 Loads)). }
  destruct (V293_rekey_byte_rmw_execution P ks ge le M (evar group) (evar mask) bg 0%Z
    g bit clear G B ltac:(change (0 <= 0 <= 4294967295)%Z; lia)
    Tg Ag Vg Tm Vm (proj2 (proj2 W))) as [Bound [Store [Exec [Read Frame]]]].
  split; [exact Exec | ]. split.
  - eapply V293_rekey_group_loads_write; eassumption.
  - split; [apply V293_rekey_writable_write; exact W | ]. split.
    + apply V293_rekey_locals_write; [exact Loc | right; reflexivity].
    + exact Bound.
Qed.

Lemma V293_rekey_byte_zero_eval : forall ge le M row n,
  n < 256 -> evaltype row (ge,le,M) = Some Tint8 ->
  evalval row (ge,le,M) = Some (V293_byteval n) ->
  evalval (ebinop oeq (ecast row Tint32) (econst32 Int.zero)) (ge,le,M) =
    Some (Vint32 (if n =? 0 then Int.one else Int.zero)).
Proof.
  intros ge le M row n N T V. cbn [evalval evaltype]. rewrite T,V.
  cbn [cast_eval bop_type bop_int_type bop_eval val_eq]. unfold V293_byteval. cbn [cmp_int_type is_int_type val_eq].
  pose proof (Int.eq_spec (Int.repr (Z.of_nat n)) Int.zero) as E.
  destruct (Int.eq (Int.repr (Z.of_nat n)) Int.zero) eqn:Ei;
    destruct (n =? 0) eqn:En; try reflexivity.
  - apply Nat.eqb_neq in En. apply (f_equal Int.unsigned) in E.
    rewrite Int.unsigned_repr in E by (change (0 <= Z.of_nat n <= 4294967295)%Z; lia).
    change (Z.of_nat n = 0)%Z in E. lia.
  - apply Nat.eqb_eq in En. subst n. contradiction.
Qed.

Lemma V293_rekey_sequence_execution : forall P ks ge le M M1 M2 a b,
  (forall tail, cstepstar P (curs a,(kenil,tail)) (ge,le,M)
    (curs (sskip None),(kenil,tail)) (ge,le,M1)) ->
  cstepstar P (curs b,(kenil,ks)) (ge,le,M1)
    (curs (sskip None),(kenil,ks)) (ge,le,M2) ->
  cstepstar P (curs (sseq a b),(kenil,ks)) (ge,le,M)
    (curs (sskip None),(kenil,ks)) (ge,le,M2).
Proof.
  intros P ks ge le M M1 M2 a b A B.
  eapply c_stepstarn. { eapply stmt_step; [reflexivity|constructor]. }
  eapply V293_cstepstar_trans; [apply A | ].
  eapply c_stepstarn. { eapply stmt_step; [reflexivity|constructor]. } exact B.
Qed.

Lemma V293_rekey_if_execution : forall P ks ge le M M' cond body (flag : bool),
  evalval cond (ge,le,M) = Some (Vint32 (if flag then Int.one else Int.zero)) ->
  (flag = true -> cstepstar P (curs body,(kenil,ks)) (ge,le,M)
    (curs (sskip None),(kenil,ks)) (ge,le,M')) ->
  (flag = false -> M' = M) ->
  cstepstar P (curs (sifthen cond body),(kenil,ks)) (ge,le,M)
    (curs (sskip None),(kenil,ks)) (ge,le,M').
Proof.
  intros P ks ge le M M' cond body flag V Yes No.
  eapply c_stepstarn. { eapply stmt_step; [reflexivity|constructor]. }
  eapply V293_cstepstar_trans.
  { apply V293_expr_steps. apply evalval_imply_estepstar. exact V. }
  destruct flag.
  - eapply c_stepstarn. { eapply stmt_step; [reflexivity|apply svift_step; reflexivity]. }
    apply Yes. reflexivity.
  - specialize (No eq_refl). subst M'.
    eapply c_stepstarn. { eapply stmt_step; [reflexivity|apply sviff_step; reflexivity]. }
    apply c_stepstar0.
Qed.

Definition V293_rekey_ready_bindings (yold ynew xold xnew byold bynew : var) (old new : nat) :=
  (yold,V293_byteval (V293_prio_row old)) ::
  (ynew,V293_byteval (V293_prio_row new)) ::
  (xold,V293_mask_value (V293_prio_bit old)) ::
  (xnew,V293_mask_value (V293_prio_bit new)) ::
  (byold,V293_mask_value (V293_prio_row old)) ::
  (bynew,V293_mask_value (V293_prio_row new)) :: nil.

(* Exactly four possible writes, in source order; the conditional clear of
   the group is skipped when the just-written old row is nonzero. *)
Definition V293_rekey_ready_memory M br bg lo hi old new :=
  let cleared := V293_ready_clear_rows lo hi old in
  let oldvalue := V293_ready_row (fst cleared) (snd cleared) (V293_prio_row old) in
  let M1 := V293_put_byte M (br,Z.of_nat (V293_prio_row old)) oldvalue in
  let M2 := if oldvalue =? 0
    then V293_put_byte M1 (bg,0%Z) (V293_ready_clear_group lo hi old) else M1 in
  let M3 := V293_put_byte M2 (bg,0%Z) (V293_ready_rekey_group lo hi old new) in
  let rows := V293_ready_rekey_rows lo hi old new in
  V293_put_byte M3 (br,Z.of_nat (V293_prio_row new))
    (V293_ready_row (fst rows) (snd rows) (V293_prio_row new)).

Lemma V293_prio_coordinates : forall p,
  p < 13 -> V293_prio_row p < 2 /\ V293_prio_bit p < 8.
Proof.
  intros p P. unfold V293_prio_row,V293_prio_bit.
  destruct (p <? 8) eqn:E; apply Nat.ltb_lt in E || apply Nat.ltb_ge in E; lia.
Qed.

Lemma V293_rekey_clear_row_value : forall lo hi old,
  V293_ready_row (fst (V293_ready_clear_rows lo hi old))
    (snd (V293_ready_clear_rows lo hi old)) (V293_prio_row old) =
  Nat.clearbit (V293_ready_row lo hi (V293_prio_row old)) (V293_prio_bit old) /\
  V293_ready_replace_row lo hi (V293_prio_row old)
    (Nat.clearbit (V293_ready_row lo hi (V293_prio_row old)) (V293_prio_bit old)) =
    V293_ready_clear_rows lo hi old.
Proof.
  intros. unfold V293_ready_row,V293_ready_clear_rows,V293_prio_row,V293_prio_bit,
    V293_ready_replace_row. destruct (old <? 8); split; reflexivity.
Qed.

Lemma V293_rekey_set_row_value : forall lo hi new,
  V293_ready_row (fst (V293_ready_set_rows lo hi new))
    (snd (V293_ready_set_rows lo hi new)) (V293_prio_row new) =
  Nat.setbit (V293_ready_row lo hi (V293_prio_row new)) (V293_prio_bit new) /\
  V293_ready_replace_row lo hi (V293_prio_row new)
    (Nat.setbit (V293_ready_row lo hi (V293_prio_row new)) (V293_prio_bit new)) =
    V293_ready_set_rows lo hi new.
Proof.
  intros. unfold V293_ready_row,V293_ready_set_rows,V293_prio_row,V293_prio_bit,
    V293_ready_replace_row. destruct (new <? 8); split; reflexivity.
Qed.

(* Stable physical execution interface for the INSIDE of the ready branch.
   Actual entry row/group reads, byte write permissions and six local reads
   suffice. No intermediate or exit expression/load/store is assumed. *)
Theorem V293_task_prio_ready_then_execution :
  forall P ks ge le M rows group yold ynew xold xnew byold bynew br bg lo hi old new,
  old < 13 -> new < 13 -> lo < 256 -> hi < 256 -> br <> bg ->
  get le rows = None -> get ge rows = Some (br,Tarray Tint8 2) ->
  get le group = None -> get ge group = Some (bg,Tint8) ->
  V293_rekey_bitmap_loads M br bg lo hi (V293_ready_group lo hi) ->
  V293_rekey_bitmap_writable M br bg ->
  V293_rekey_locals ge le M br bg (V293_rekey_ready_bindings
    yold ynew xold xnew byold bynew old new) ->
  let M' := V293_rekey_ready_memory M br bg lo hi old new in
  let finalrows := V293_ready_rekey_rows lo hi old new in
  cstepstar P (curs (V293_task_prio_ready_then rows group yold ynew xold xnew byold bynew),
    (kenil,ks)) (ge,le,M) (curs (sskip None),(kenil,ks)) (ge,le,M') /\
  V293_rekey_bitmap_loads M' br bg (fst finalrows) (snd finalrows)
    (V293_ready_group (fst finalrows) (snd finalrows)) /\
  V293_rekey_bitmap_writable M' br bg /\
  V293_rekey_locals ge le M' br bg (V293_rekey_ready_bindings
    yold ynew xold xnew byold bynew old new) /\
  (forall b i, b <> br -> b <> bg -> get M' (b,i) = get M (b,i)).
Proof.
  intros P ks ge le M rows group yold ynew xold xnew byold bynew br bg lo hi old new
    O N L H Apart Nr Gr Ng Gg Loads W Loc.
  cbn zeta.
  pose (bindings := V293_rekey_ready_bindings yold ynew xold xnew byold bynew old new).
  change (V293_rekey_locals ge le M br bg bindings) in Loc.
  assert (Iyold : In (yold,V293_byteval (V293_prio_row old)) bindings)
    by (unfold bindings,V293_rekey_ready_bindings; simpl; auto 8).
  assert (Iynew : In (ynew,V293_byteval (V293_prio_row new)) bindings)
    by (unfold bindings,V293_rekey_ready_bindings; simpl; auto 8).
  assert (Ixold : In (xold,V293_mask_value (V293_prio_bit old)) bindings)
    by (unfold bindings,V293_rekey_ready_bindings; simpl; auto 8).
  assert (Ixnew : In (xnew,V293_mask_value (V293_prio_bit new)) bindings)
    by (unfold bindings,V293_rekey_ready_bindings; simpl; auto 8).
  assert (Ibyold : In (byold,V293_mask_value (V293_prio_row old)) bindings)
    by (unfold bindings,V293_rekey_ready_bindings; simpl; auto 8).
  assert (Ibynew : In (bynew,V293_mask_value (V293_prio_row new)) bindings)
    by (unfold bindings,V293_rekey_ready_bindings; simpl; auto 8).
  destruct (V293_prio_coordinates old O) as [Yo Xo].
  destruct (V293_prio_coordinates new N) as [Yn Xn].
  pose (cleared := V293_ready_clear_rows lo hi old).
  pose (cv := Nat.clearbit (V293_ready_row lo hi (V293_prio_row old)) (V293_prio_bit old)).
  pose (M1 := V293_put_byte M (br,Z.of_nat (V293_prio_row old)) cv).
  assert (EC : V293_ready_replace_row lo hi (V293_prio_row old) cv = cleared)
    by (apply V293_rekey_clear_row_value).
  assert (CV : V293_ready_row (fst cleared) (snd cleared) (V293_prio_row old) = cv)
    by (apply V293_rekey_clear_row_value).
  assert (Clear : forall tail,
    cstepstar P (curs (sassign (earrayelem (evar rows) (evar yold))
      (V293_task_prio_clear_expr (earrayelem (evar rows) (evar yold)) (evar xold))),
      (kenil,tail)) (ge,le,M) (curs (sskip None),(kenil,tail)) (ge,le,M1)).
  { intro tail. exact (proj1 (V293_rekey_row_execution P tail ge le M rows yold xold
      br bg lo hi (V293_ready_group lo hi) (V293_prio_row old) (V293_prio_bit old) true
      bindings Apart L H Yo Xo Nr Gr Loads W Loc Iyold Ixold)). }
  destruct (V293_rekey_row_execution P ks ge le M rows yold xold br bg lo hi
    (V293_ready_group lo hi) (V293_prio_row old) (V293_prio_bit old) true bindings
    Apart L H Yo Xo Nr Gr Loads W Loc Iyold Ixold) as [_ [Loads1 [W1 [Loc1 CBound]]]].
  change (V293_rekey_bitmap_loads M1 br bg
    (fst (V293_ready_replace_row lo hi (V293_prio_row old) cv))
    (snd (V293_ready_replace_row lo hi (V293_prio_row old) cv)) (V293_ready_group lo hi)) in Loads1.
  rewrite EC in Loads1.
  change (V293_rekey_bitmap_writable M1 br bg) in W1.
  change (V293_rekey_locals ge le M1 br bg bindings) in Loc1.
  change (cv < 256) in CBound.
  assert (CL : fst cleared < 256 /\ snd cleared < 256).
  { unfold cleared,V293_ready_clear_rows. destruct (old <? 8) eqn:E;
      cbn [fst snd]; unfold cv,V293_ready_row,V293_prio_row,V293_prio_bit in CBound;
      rewrite E in CBound; cbn in CBound; split; assumption. }
  assert (GroupBound : V293_ready_group lo hi < 256).
  { unfold V293_ready_group. destruct (lo =? 0); destruct (hi =? 0); lia. }
  pose (gc := V293_ready_clear_group lo hi old).
  pose (M2 := if cv =? 0 then V293_put_byte M1 (bg,0%Z) gc else M1).
  assert (GC : gc = if cv =? 0 then
    Nat.clearbit (V293_ready_group lo hi) (V293_prio_row old) else V293_ready_group lo hi).
  { unfold gc,V293_ready_clear_group,cleared,cv,V293_prio_row,V293_prio_bit,V293_ready_row,
      V293_ready_clear_rows. destruct (old <? 8); reflexivity. }
  assert (Cond : evalval (ebinop oeq
    (ecast (earrayelem (evar rows) (evar yold)) Tint32) (econst32 Int.zero)) (ge,le,M1) =
    Some (Vint32 (if cv =? 0 then Int.one else Int.zero))).
  { destruct (V293_rekey_local_eval ge le M1 br bg bindings yold _ Loc1 Iyold) as [Ty Vy].
    destruct (V293_rekey_row_eval ge le M1 rows (evar yold) br (fst cleared) (snd cleared)
      (V293_ready_group lo hi) bg (V293_prio_row old) Nr Gr Ty Vy Yo Loads1) as [T [_ V]].
    rewrite CV in V. eapply V293_rekey_byte_zero_eval; eassumption. }
  assert (GroupClear : forall tail,
    cstepstar P (curs (sifthen (ebinop oeq
      (ecast (earrayelem (evar rows) (evar yold)) Tint32) (econst32 Int.zero))
      (sassign (evar group) (V293_task_prio_clear_expr (evar group) (evar byold)))),
      (kenil,tail)) (ge,le,M1) (curs (sskip None),(kenil,tail)) (ge,le,M2)).
  { intro tail. eapply V293_rekey_if_execution with (flag := cv =? 0); [exact Cond| | ].
    - intro Zero. unfold M2. rewrite GC; try rewrite Zero.
      exact (proj1 (V293_rekey_group_execution P tail ge le M1 group byold br bg
        (fst cleared) (snd cleared) (V293_ready_group lo hi) (V293_prio_row old) true
        bindings Apart GroupBound ltac:(lia) Ng Gg Loads1 W1 Loc1 Ibyold)).
    - intro Nonzero. unfold M2. rewrite Nonzero. reflexivity. }
  assert (AfterClear : V293_rekey_bitmap_loads M2 br bg (fst cleared) (snd cleared) gc /\
    V293_rekey_bitmap_writable M2 br bg /\ V293_rekey_locals ge le M2 br bg bindings /\ gc < 256).
  { unfold M2. destruct (cv =? 0) eqn:Zero.
    - rewrite GC; try rewrite Zero.
      exact (proj2 (V293_rekey_group_execution P ks ge le M1 group byold br bg
        (fst cleared) (snd cleared) (V293_ready_group lo hi) (V293_prio_row old) true
        bindings Apart GroupBound ltac:(lia) Ng Gg Loads1 W1 Loc1 Ibyold)).
    - rewrite GC; try rewrite Zero. auto. }
  destruct AfterClear as [Loads2 [W2 [Loc2 GCBound]]].
  pose (gn := V293_ready_rekey_group lo hi old new).
  pose (M3 := V293_put_byte M2 (bg,0%Z) gn).
  assert (GroupSet : forall tail,
    cstepstar P (curs (sassign (evar group)
      (V293_task_prio_set_expr (evar group) (evar bynew))),(kenil,tail)) (ge,le,M2)
      (curs (sskip None),(kenil,tail)) (ge,le,M3)).
  { intro tail. exact (proj1 (V293_rekey_group_execution P tail ge le M2 group bynew br bg
      (fst cleared) (snd cleared) gc (V293_prio_row new) false bindings
      Apart GCBound ltac:(lia) Ng Gg Loads2 W2 Loc2 Ibynew)). }
  destruct (V293_rekey_group_execution P ks ge le M2 group bynew br bg
    (fst cleared) (snd cleared) gc (V293_prio_row new) false bindings Apart GCBound
    ltac:(lia) Ng Gg Loads2 W2 Loc2 Ibynew) as [_ [Loads3 [W3 [Loc3 GNBound]]]].
  change (V293_rekey_bitmap_loads M3 br bg (fst cleared) (snd cleared) gn) in Loads3.
  change (V293_rekey_bitmap_writable M3 br bg) in W3.
  change (V293_rekey_locals ge le M3 br bg bindings) in Loc3.
  pose (nv := Nat.setbit (V293_ready_row (fst cleared) (snd cleared) (V293_prio_row new))
    (V293_prio_bit new)).
  pose (M4 := V293_put_byte M3 (br,Z.of_nat (V293_prio_row new)) nv).
  destruct (V293_rekey_row_execution P ks ge le M3 rows ynew xnew br bg
    (fst cleared) (snd cleared) gn (V293_prio_row new) (V293_prio_bit new) false bindings
    Apart (proj1 CL) (proj2 CL) Yn Xn Nr Gr Loads3 W3 Loc3 Iynew Ixnew)
    as [RowSet [Loads4 [W4 [Loc4 NVBound]]]].
  assert (ES : V293_ready_replace_row (fst cleared) (snd cleared) (V293_prio_row new) nv =
    V293_ready_rekey_rows lo hi old new)
    by (apply V293_rekey_set_row_value).
  change (V293_rekey_bitmap_loads M4 br bg
    (fst (V293_ready_replace_row (fst cleared) (snd cleared) (V293_prio_row new) nv))
    (snd (V293_ready_replace_row (fst cleared) (snd cleared) (V293_prio_row new) nv)) gn) in Loads4.
  rewrite ES in Loads4. unfold gn in Loads4. rewrite V293_ready_rekey_group_correct in Loads4.
  assert (Memory : V293_rekey_ready_memory M br bg lo hi old new = M4).
  { unfold V293_rekey_ready_memory. fold cleared. rewrite CV.
    fold M1 M2 M3. unfold M4,nv. f_equal.
    unfold V293_ready_rekey_rows. fold cleared. apply V293_rekey_set_row_value. }
  rewrite Memory. split.
  - unfold V293_task_prio_ready_then.
    eapply V293_rekey_sequence_execution; [exact Clear | ].
    eapply V293_rekey_sequence_execution; [exact GroupClear | ].
    eapply V293_rekey_sequence_execution; [exact GroupSet | exact RowSet].
  - split; [exact Loads4 | ]. split; [exact W4 | ]. split; [exact Loc4 | ].
    intros b i R G. unfold M4,M3,M2,M1.
    repeat rewrite V293_put_byte_other by congruence.
    destruct (cv =? 0); repeat rewrite V293_put_byte_other by congruence; reflexivity.
Qed.

(* Simultaneous concrete entry resources.  No reachability/initialization
   credit: these fixtures inhabit precisely the ready THEN interface. *)
Definition V293_ready_fragment_fixture_ge : env :=
  set (set emp 300%Z (30%positive,Tarray Tint8 2)) 301%Z (31%positive,Tint8).
Definition V293_ready_fragment_fixture_le : env :=
  set (set (set (set (set (set emp 302%Z (32%positive,Tint8))
    303%Z (33%positive,Tint8)) 304%Z (34%positive,Tint8))
    305%Z (35%positive,Tint8)) 306%Z (36%positive,Tint8)) 307%Z (37%positive,Tint8).
Definition V293_ready_fragment_fixture_mem lo hi old new : mem :=
  V293_put_byte (V293_put_byte (V293_put_byte (V293_put_byte
    (V293_put_byte (V293_put_byte (V293_put_byte (V293_put_byte
      (V293_put_byte emp (30%positive,0%Z) lo) (30%positive,1%Z) hi)
      (31%positive,0%Z) (V293_ready_group lo hi))
      (32%positive,0%Z) (V293_prio_row old))
      (33%positive,0%Z) (V293_prio_row new))
      (34%positive,0%Z) (2 ^ V293_prio_bit old))
      (35%positive,0%Z) (2 ^ V293_prio_bit new))
      (36%positive,0%Z) (2 ^ V293_prio_row old))
      (37%positive,0%Z) (2 ^ V293_prio_row new).

Lemma V293_mask_byte_value : forall bit,
  bit < 8 -> 2 ^ bit < 256 /\ V293_byteval (2 ^ bit) = V293_mask_value bit.
Proof.
  intros bit B. do 8 (destruct bit as [ | bit]; [split; [cbn; lia|reflexivity] | ]). lia.
Qed.

Lemma V293_put_byte_get_same : forall M a n,
  get (V293_put_byte M a n) a =
    Some (true,Byte (Byte.repr (Int.unsigned (Int.repr (Z.of_nat n))))).
Proof. intros. unfold V293_put_byte. apply map_get_set. Qed.

Local Ltac ready_fixture_get :=
  unfold V293_ready_fragment_fixture_ge,V293_ready_fragment_fixture_le,
    V293_ready_fragment_fixture_mem;
  repeat first [rewrite V293_put_byte_get_same |
    rewrite V293_put_byte_other by discriminate | rewrite map_get_set |
    rewrite map_get_set' by discriminate | rewrite map_emp_get].
Local Ltac ready_fixture_load :=
  unfold V293_ready_fragment_fixture_mem;
  repeat rewrite V293_put_byte_other_load by discriminate;
  apply V293_put_byte_load; eassumption.

Theorem V293_ready_fragment_entry_witness : forall lo hi old new,
  lo < 256 -> hi < 256 -> old < 13 -> new < 13 ->
  V293_rekey_bitmap_loads (V293_ready_fragment_fixture_mem lo hi old new)
    30%positive 31%positive lo hi (V293_ready_group lo hi) /\
  V293_rekey_bitmap_writable (V293_ready_fragment_fixture_mem lo hi old new) 30%positive 31%positive /\
  V293_rekey_locals V293_ready_fragment_fixture_ge V293_ready_fragment_fixture_le
    (V293_ready_fragment_fixture_mem lo hi old new) 30%positive 31%positive
    (V293_rekey_ready_bindings 302%Z 303%Z 304%Z 305%Z 306%Z 307%Z old new).
Proof.
  intros lo hi old new L H O N.
  destruct (V293_prio_coordinates old O) as [Yo Xo].
  destruct (V293_prio_coordinates new N) as [Yn Xn].
  assert (Yob : V293_prio_row old < 256) by lia.
  assert (Ynb : V293_prio_row new < 256) by lia.
  destruct (V293_mask_byte_value (V293_prio_bit old) Xo) as [Xob Xov].
  destruct (V293_mask_byte_value (V293_prio_bit new) Xn) as [Xnb Xnv].
  destruct (V293_mask_byte_value (V293_prio_row old) ltac:(lia)) as [Byob Byov].
  destruct (V293_mask_byte_value (V293_prio_row new) ltac:(lia)) as [Bynb Bynv].
  assert (G : V293_ready_group lo hi < 256).
  { unfold V293_ready_group. destruct (lo =? 0); destruct (hi =? 0); lia. }
  split.
  - unfold V293_rekey_bitmap_loads. repeat split; ready_fixture_load.
  - split.
    + unfold V293_rekey_bitmap_writable. repeat split; eexists; ready_fixture_get; reflexivity.
    + intros x value I. cbn [V293_rekey_ready_bindings In] in I.
      destruct I as [E|[E|[E|[E|[E|[E|F]]]]]]; try contradiction;
        inversion E; subst x value.
      all: eexists; split; [ready_fixture_get; reflexivity | ]; split; [discriminate| ];
        split; [discriminate| ].
      all: try ready_fixture_load.
      all: rewrite <- Xov || rewrite <- Xnv || rewrite <- Byov || rewrite <- Bynv;
        ready_fixture_load.
Qed.

(* Concrete executions cover both outcomes of the inner if, same-row reuse,
   and preservation of the unused high bit.  Preconditions are discharged by
   the simultaneous entry witness, not postulated for the examples. *)
Theorem V293_ready_fragment_execution_witness : forall P ks lo hi old new,
  lo < 256 -> hi < 256 -> old < 13 -> new < 13 ->
  let M := V293_ready_fragment_fixture_mem lo hi old new in
  let M' := V293_rekey_ready_memory M 30%positive 31%positive lo hi old new in
  cstepstar P (curs (V293_task_prio_ready_then
    300%Z 301%Z 302%Z 303%Z 304%Z 305%Z 306%Z 307%Z),(kenil,ks))
    (V293_ready_fragment_fixture_ge,V293_ready_fragment_fixture_le,M)
    (curs (sskip None),(kenil,ks))
    (V293_ready_fragment_fixture_ge,V293_ready_fragment_fixture_le,M') /\
  V293_rekey_bitmap_loads M' 30%positive 31%positive
    (fst (V293_ready_rekey_rows lo hi old new)) (snd (V293_ready_rekey_rows lo hi old new))
    (V293_ready_group (fst (V293_ready_rekey_rows lo hi old new))
      (snd (V293_ready_rekey_rows lo hi old new))).
Proof.
  intros P ks lo hi old new L H O N. cbn zeta.
  destruct (V293_ready_fragment_entry_witness lo hi old new L H O N) as [Loads [W Loc]].
  destruct (V293_task_prio_ready_then_execution P ks
    V293_ready_fragment_fixture_ge V293_ready_fragment_fixture_le
    (V293_ready_fragment_fixture_mem lo hi old new)
    300%Z 301%Z 302%Z 303%Z 304%Z 305%Z 306%Z 307%Z 30%positive 31%positive lo hi old new)
    as [Exec [Read _]].
  all: try assumption; try discriminate; try (ready_fixture_get; reflexivity).
  auto.
Qed.

Definition V293_ready_fragment_observes lo hi old new expectedlo expectedhi expectedgroup : Prop :=
  V293_rekey_bitmap_loads
    (V293_rekey_ready_memory (V293_ready_fragment_fixture_mem lo hi old new)
      30%positive 31%positive lo hi old new) 30%positive 31%positive
    expectedlo expectedhi expectedgroup.

Theorem V293_ready_fragment_physical_controls :
  V293_ready_fragment_observes 0 1 8 6 64 0 1 /\
  V293_ready_fragment_observes 0 1 8 10 0 4 2 /\
  V293_ready_fragment_observes 20 0 2 6 80 0 1 /\
  V293_ready_fragment_observes 0 129 8 6 64 128 3.
Proof.
  split.
  - exact (proj2 (V293_ready_fragment_execution_witness (fun _ => None) kstop 0 1 8 6
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))).
  - split.
    + exact (proj2 (V293_ready_fragment_execution_witness (fun _ => None) kstop 0 1 8 10
        ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))).
    + split.
      * exact (proj2 (V293_ready_fragment_execution_witness (fun _ => None) kstop 20 0 2 6
          ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))).
      * exact (proj2 (V293_ready_fragment_execution_witness (fun _ => None) kstop 0 129 8 6
          ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))).
Qed.

(* Removing only the no-alias restriction destroys stability of a local
   operand. This raw memory example is not a valid API entry counterexample. *)
Theorem V293_ready_fragment_alias_control :
  let M := V293_put_byte emp (30%positive,0%Z) 2 in
  let M' := V293_put_byte M (30%positive,0%Z) (Nat.clearbit 2 1) in
  load Tint8 M (30%positive,0%Z) = Some (V293_mask_value 1) /\
  store Tint8 M (30%positive,0%Z) (V293_byteval (Nat.clearbit 2 1)) = Some M' /\
  load Tint8 M' (30%positive,0%Z) = Some (V293_byteval 0) /\
  load Tint8 M' (30%positive,0%Z) <> Some (V293_mask_value 1).
Proof.
  cbn zeta. split.
  - change (load Tint8 (V293_put_byte emp (30%positive,0%Z) 2) (30%positive,0%Z) =
      Some (V293_byteval 2)). apply V293_put_byte_load. lia.
  - split.
    + eapply V293_put_byte_store. apply V293_put_byte_get_same.
    + split.
      * apply V293_put_byte_load. cbn. lia.
      * rewrite V293_put_byte_load by (cbn; lia). discriminate.
Qed.

(* Component connection at the ready THEN entry. The physical priority table
   has ALREADY been rekeyed; it is transported through the bitmap writes by
   their byte frame. This does not silently execute the three intervening
   TCB reads or claim that physical TCB fields have been changed. *)
Theorem V293_task_prio_ready_then_correspondence :
  forall P ks ge le M rows group yold ynew xold xnew byold bynew
    br bg bt tp lo hi old new entries tasks next message,
  old < 13 -> new < 13 -> lo < 256 -> hi < 256 -> br <> bg -> bt <> br -> bt <> bg ->
  get le rows = None -> get ge rows = Some (br,Tarray Tint8 2) ->
  get le group = None -> get ge group = Some (bg,Tint8) ->
  V293_rekey_bitmap_loads M br bg lo hi (V293_ready_group lo hi) ->
  V293_rekey_bitmap_writable M br bg ->
  V293_rekey_locals ge le M br bg (V293_rekey_ready_bindings
    yold ynew xold xnew byold bynew old new) ->
  V293_priority_table entries tasks -> V293_bitmap_tasks lo hi tasks ->
  get tasks next = Some (Int.repr (Z.of_nat old),rdy,message) ->
  nth new entries Vnull = Vnull ->
  V293_table_loads tp M bt (update_nth_val new (update_nth_val old entries Vnull) (Vptr next)) ->
  let M' := V293_rekey_ready_memory M br bg lo hi old new in
  let finalrows := V293_ready_rekey_rows lo hi old new in
  let tasks' := set tasks next (Int.repr (Z.of_nat new),rdy,message) in
  let entries' := update_nth_val new (update_nth_val old entries Vnull) (Vptr next) in
  cstepstar P (curs (V293_task_prio_ready_then rows group yold ynew xold xnew byold bynew),
    (kenil,ks)) (ge,le,M) (curs (sskip None),(kenil,ks)) (ge,le,M') /\
  V293_rekey_bitmap_loads M' br bg (fst finalrows) (snd finalrows)
    (V293_ready_group (fst finalrows) (snd finalrows)) /\
  V293_bitmap_tasks (fst finalrows) (snd finalrows) tasks' /\
  V293_priority_table entries' tasks' /\ V293_table_loads tp M' bt entries' /\
  exists chosen msg,
    get tasks' chosen = Some (Int.repr (Z.of_nat
      (V293_ready_select (fst finalrows) (snd finalrows)
        (V293_ready_group (fst finalrows) (snd finalrows)))),rdy,msg) /\
    V293_highest_ready tasks' chosen /\
    load (Tptr tp) M' (bt,(4*Z.of_nat
      (V293_ready_select (fst finalrows) (snd finalrows)
        (V293_ready_group (fst finalrows) (snd finalrows))))%Z) = Some (Vptr chosen).
Proof.
  intros P ks ge le M rows group yold ynew xold xnew byold bynew
    br bg bt tp lo hi old new entries tasks next message
    O N L H Apart Tr Tg Nr Gr Ng Gg Loads W Loc Table Bitmap Task Empty View.
  cbn zeta.
  destruct (V293_task_prio_ready_then_execution P ks ge le M rows group
    yold ynew xold xnew byold bynew br bg lo hi old new O N L H Apart Nr Gr Ng Gg Loads W Loc)
    as [Exec [Read [_ [_ Frame]]]].
  pose proof (V293_rekey_ready_tasks_preserved lo hi entries tasks next old new message
    O N Table Bitmap Task) as Bpost.
  pose proof (V293_rekey_task_table_preserved entries tasks next old new rdy message
    O N Table Task Empty) as Tpost.
  assert (Vpost : V293_table_loads tp (V293_rekey_ready_memory M br bg lo hi old new) bt
    (update_nth_val new (update_nth_val old entries Vnull) (Vptr next))).
  { intros p R. unfold load,loadm. rewrite V293_loadbytes_ext with (M := M).
    - exact (View p R).
    - intros k K. apply Frame; assumption. }
  split; [exact Exec | ]. split; [exact Read | ]. split; [exact Bpost | ].
  split; [exact Tpost | ]. split; [exact Vpost | ].
  destruct (V293_ready_rekey_bounds lo hi old new L H O N) as [Lpost Hpost].
  assert (Nonempty : exists p, V293_bitmap_ready
    (fst (V293_ready_rekey_rows lo hi old new)) (snd (V293_ready_rekey_rows lo hi old new)) p).
  { exists new. apply V293_ready_rekey_membership; auto. }
  destruct (V293_ready_selection_task _ _ _ _ Lpost Hpost Nonempty Bpost Tpost)
    as (chosen & msg & Selected & Entry & Highest).
  exists chosen. exists msg. split; [exact Selected | ]. split; [exact Highest | ].
  rewrite Vpost.
  - rewrite Entry. reflexivity.
  - eapply V293_ready_selection_range; eauto.
Qed.

(* Exact field order/types and explicit padding of the configured TCB. *)
Theorem V293_tcb_old_field_layout :
  typelen V293_tcb_type = 56 /\
  ftype 18%Z V293_tcb_fields = Some Tint8 /\
  ftype 20%Z V293_tcb_fields = Some Tint8 /\
  ftype 19%Z V293_tcb_fields = Some Tint8 /\
  field_offset 18%Z V293_tcb_fields = Some (Int.repr 52) /\
  field_offset 20%Z V293_tcb_fields = Some (Int.repr 54) /\
  field_offset 19%Z V293_tcb_fields = Some (Int.repr 53).
Proof. repeat split; reflexivity. Qed.

Lemma V293_put_byte_pointer_frame : forall M a n tp b i,
  fst a <> b ->
  load (Tptr tp) (V293_put_byte M a n) (b,i) = load (Tptr tp) M (b,i).
Proof.
  intros M [ba ia] n tp b i N. simpl in N. unfold load,loadm.
  rewrite V293_loadbytes_ext with (M := M); [reflexivity | ]. intros k K.
  apply V293_put_byte_other. intro E. inversion E. congruence.
Qed.

Lemma V293_tcb_byte_field_eval : forall ge le M ptcb bc bt base field delta value,
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  load (Tptr V293_tcb_type) M (bc,0%Z) = Some (Vptr (bt,Int.repr base)) ->
  ftype field V293_tcb_fields = Some Tint8 ->
  field_offset field V293_tcb_fields = Some (Int.repr delta) ->
  (0 <= base)%Z -> (0 <= delta)%Z -> (base+delta <= Int.max_unsigned)%Z ->
  load Tint8 M (bt,(base+delta)%Z) = Some value ->
  evaltype (efield (ederef (evar ptcb)) field) (ge,le,M) = Some Tint8 /\
  evalval (efield (ederef (evar ptcb)) field) (ge,le,M) = Some value.
Proof.
  intros ge le M ptcb bc bt base field delta value Bptr Hptr Ft Fo B D R Read.
  assert (Tp : evaltype (ederef (evar ptcb)) (ge,le,M) = Some V293_tcb_type).
  { cbn [evaltype get_lenv get_genv get_mem]. rewrite Bptr. reflexivity. }
  assert (T : evaltype (efield (ederef (evar ptcb)) field) (ge,le,M) = Some Tint8).
  { cbn [evaltype]. rewrite Bptr. exact Ft. }
  split; [exact T | ]. cbn [evalval]. rewrite T.
  cbn [evaladdr evalval evaltype get_lenv get_genv get_mem]. rewrite Bptr.
  cbn beta iota. rewrite Hptr. unfold getoff. rewrite Tp.
  cbn [V293_tcb_type]. rewrite Fo. cbn [addrval_to_addr].
  rewrite Int.repr_unsigned. unfold Int.add.
  rewrite (Int.unsigned_repr base) by lia.
  rewrite (Int.unsigned_repr delta) by lia.
  rewrite Int.unsigned_repr by lia. exact Read.
Qed.

(* A real field read and byte assignment. Store success follows from its
   destination permission; it is not a caller-supplied execution premise. *)
Theorem V293_tcb_field_assignment :
  forall P ks ge le M ptcb dest bc bt bd base field delta n,
  n < 256 ->
  get le ptcb = Some (bc,Tptr V293_tcb_type) -> get le dest = Some (bd,Tint8) ->
  load (Tptr V293_tcb_type) M (bc,0%Z) = Some (Vptr (bt,Int.repr base)) ->
  ftype field V293_tcb_fields = Some Tint8 ->
  field_offset field V293_tcb_fields = Some (Int.repr delta) ->
  (0 <= base)%Z -> (0 <= delta)%Z -> (base+delta <= Int.max_unsigned)%Z ->
  load Tint8 M (bt,(base+delta)%Z) = Some (V293_byteval n) ->
  (exists v, get M (bd,0%Z) = Some (true,v)) ->
  let M' := V293_put_byte M (bd,0%Z) n in
  cstepstar P (curs (sassign (evar dest) (efield (ederef (evar ptcb)) field)),(kenil,ks))
    (ge,le,M) (curs (sskip None),(kenil,ks)) (ge,le,M') /\
  load Tint8 M' (bd,0%Z) = Some (V293_byteval n) /\
  (forall other, other <> (bd,0%Z) -> get M' other = get M other).
Proof.
  intros P ks ge le M ptcb dest bc bt bd base field delta n N Bp Bd Hptr Ft Fo B D R L [v W].
  cbn zeta.
  destruct (V293_tcb_byte_field_eval ge le M ptcb bc bt base field delta _ Bp Hptr Ft Fo B D R L)
    as [FieldType FieldValue].
  assert (Store : store Tint8 M (bd,0%Z) (V293_byteval n) =
    Some (V293_put_byte M (bd,0%Z) n)) by (apply V293_put_byte_store with (old := v); exact W).
  split.
  - eapply V293_assign_byte_offset_execution with (off := 0%Z); try eassumption.
    + cbn [evaltype]. rewrite Bd. reflexivity.
    + cbn [evaladdr get_lenv get_genv]. rewrite Bd. reflexivity.
    + change (0 <= 0 <= 4294967295)%Z. lia.
  - split; [apply V293_put_byte_load; exact N | ].
    intros. apply V293_put_byte_other. assumption.
Qed.

Definition V293_tcb_old_loads (M : mem) bt base vy vby vx : Prop :=
  load Tint8 M (bt,(base+52)%Z) = Some (V293_byteval vy) /\
  load Tint8 M (bt,(base+54)%Z) = Some (V293_byteval vby) /\
  load Tint8 M (bt,(base+53)%Z) = Some (V293_byteval vx).
Definition V293_tcb_read_memory (M : mem) dy bby bx vy vby vx : mem :=
  V293_put_byte (V293_put_byte (V293_put_byte M (dy,0%Z) vy)
    (bby,0%Z) vby) (bx,0%Z) vx.

(* Three actual field reads, including reloading ptcb after each local write.
   Values are entry memory data, not an assumed abstract TCB invariant. *)
Theorem V293_task_prio_read_old_execution :
  forall P ks ge le M ptcb yo byo xo bc bt dy bby bx base vy vby vx,
  vy < 256 -> vby < 256 -> vx < 256 ->
  (0 <= base)%Z -> (base+55 <= Int.max_unsigned)%Z ->
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  get le yo = Some (dy,Tint8) -> get le byo = Some (bby,Tint8) ->
  get le xo = Some (bx,Tint8) ->
  dy <> bby -> dy <> bx -> bby <> bx ->
  (forall b, b = dy \/ b = bby \/ b = bx -> b <> bc /\ b <> bt) ->
  load (Tptr V293_tcb_type) M (bc,0%Z) = Some (Vptr (bt,Int.repr base)) ->
  V293_tcb_old_loads M bt base vy vby vx ->
  (exists v, get M (dy,0%Z) = Some (true,v)) ->
  (exists v, get M (bby,0%Z) = Some (true,v)) ->
  (exists v, get M (bx,0%Z) = Some (true,v)) ->
  let M' := V293_tcb_read_memory M dy bby bx vy vby vx in
  cstepstar P (curs (V293_task_prio_read_old ptcb yo byo xo),(kenil,ks))
    (ge,le,M) (curs (sskip None),(kenil,ks)) (ge,le,M') /\
  load Tint8 M' (dy,0%Z) = Some (V293_byteval vy) /\
  load Tint8 M' (bby,0%Z) = Some (V293_byteval vby) /\
  load Tint8 M' (bx,0%Z) = Some (V293_byteval vx) /\
  load (Tptr V293_tcb_type) M' (bc,0%Z) = Some (Vptr (bt,Int.repr base)) /\
  V293_tcb_old_loads M' bt base vy vby vx /\
  (forall b i, b <> dy -> b <> bby -> b <> bx -> get M' (b,i) = get M (b,i)).
Proof.
  intros P ks ge le M ptcb yo byo xo bc bt dy bby bx base vy vby vx
    Y BY X B R Bp By Bby Bx NYB NYX NBX Apart Hptr [Ly [Lby Lx]] Wy Wby Wx.
  destruct (Apart dy ltac:(auto)) as [Yc Yt].
  destruct (Apart bby ltac:(auto)) as [BYc BYt].
  destruct (Apart bx ltac:(auto)) as [Xc Xt].
  set (M1 := V293_put_byte M (dy,0%Z) vy).
  set (M2 := V293_put_byte M1 (bby,0%Z) vby).
  assert (P1 : load (Tptr V293_tcb_type) M1 (bc,0%Z) = Some (Vptr (bt,Int.repr base))).
  { unfold M1. rewrite V293_put_byte_pointer_frame; [exact Hptr | exact Yc]. }
  assert (P2 : load (Tptr V293_tcb_type) M2 (bc,0%Z) = Some (Vptr (bt,Int.repr base))).
  { unfold M2. rewrite V293_put_byte_pointer_frame; [exact P1 | exact BYc]. }
  assert (Lby1 : load Tint8 M1 (bt,(base+54)%Z) = Some (V293_byteval vby)).
  { unfold M1. rewrite V293_put_byte_other_load; [exact Lby | congruence]. }
  assert (Lx2 : load Tint8 M2 (bt,(base+53)%Z) = Some (V293_byteval vx)).
  { unfold M2,M1. repeat rewrite V293_put_byte_other_load by congruence. exact Lx. }
  assert (Wby1 : exists v, get M1 (bby,0%Z) = Some (true,v)).
  { unfold M1. rewrite V293_put_byte_other by congruence. exact Wby. }
  assert (Wx2 : exists v, get M2 (bx,0%Z) = Some (true,v)).
  { unfold M2,M1. repeat rewrite V293_put_byte_other by congruence. exact Wx. }
  assert (E1 : forall tail, cstepstar P
    (curs (sassign (evar yo) (efield (ederef (evar ptcb)) 18%Z)),(kenil,tail))
    (ge,le,M) (curs (sskip None),(kenil,tail)) (ge,le,M1)).
  { intro tail. destruct (V293_tcb_field_assignment P tail ge le M ptcb yo bc bt dy
      base 18%Z 52%Z vy Y Bp By Hptr eq_refl eq_refl B ltac:(lia) ltac:(lia) Ly Wy)
      as [E _]. exact E. }
  assert (E2 : forall tail, cstepstar P
    (curs (sassign (evar byo) (efield (ederef (evar ptcb)) 20%Z)),(kenil,tail))
    (ge,le,M1) (curs (sskip None),(kenil,tail)) (ge,le,M2)).
  { intro tail. destruct (V293_tcb_field_assignment P tail ge le M1 ptcb byo bc bt bby
      base 20%Z 54%Z vby BY Bp Bby P1 eq_refl eq_refl B ltac:(lia) ltac:(lia) Lby1 Wby1)
      as [E _]. exact E. }
  cbn zeta. split.
  - unfold V293_task_prio_read_old,V293_tcb_read_memory.
    eapply V293_rekey_sequence_execution; [exact E1 | ].
    eapply V293_rekey_sequence_execution; [exact E2 | ].
    destruct (V293_tcb_field_assignment P ks ge le M2 ptcb xo bc bt bx
      base 19%Z 53%Z vx X Bp Bx P2 eq_refl eq_refl B ltac:(lia) ltac:(lia) Lx2 Wx2)
      as [E _]. exact E.
  - unfold V293_tcb_read_memory. fold M1. fold M2.
    split.
    + unfold M2. repeat rewrite V293_put_byte_other_load by congruence.
      unfold M1. apply V293_put_byte_load. exact Y.
    + split.
      * rewrite V293_put_byte_other_load by congruence.
        unfold M2. apply V293_put_byte_load. exact BY.
      * split; [apply V293_put_byte_load; exact X | ].
        split.
        -- rewrite V293_put_byte_pointer_frame; [exact P2 | exact Xc].
        -- split.
           ++ unfold V293_tcb_old_loads,M2,M1.
              repeat rewrite V293_put_byte_other_load by congruence. auto.
           ++ intros. unfold M2,M1.
              repeat rewrite V293_put_byte_other by congruence. reflexivity.
Qed.

Definition V293_tcb_fixture_ge : env := emp.
Definition V293_tcb_fixture_le : env :=
  set (set (set (set (emp : env) 400%Z (40%positive,Tptr V293_tcb_type))
    401%Z (42%positive,Tint8)) 402%Z (43%positive,Tint8)) 403%Z (44%positive,Tint8).
Definition V293_tcb_fixture_pointer : mem :=
  set (set (set (set (emp : mem)
    (40%positive,0%Z) (true,Pointer 41%positive (Int.repr 8) 3))
    (40%positive,1%Z) (true,Pointer 41%positive (Int.repr 8) 2))
    (40%positive,2%Z) (true,Pointer 41%positive (Int.repr 8) 1))
    (40%positive,3%Z) (true,Pointer 41%positive (Int.repr 8) 0).
Definition V293_tcb_fixture_memory vy vby vx : mem :=
  V293_put_byte (V293_put_byte (V293_put_byte
    (V293_put_byte (V293_put_byte (V293_put_byte V293_tcb_fixture_pointer
      (41%positive,60%Z) vy) (41%positive,62%Z) vby) (41%positive,61%Z) vx)
    (42%positive,0%Z) 255) (43%positive,0%Z) 255) (44%positive,0%Z) 255.

Local Ltac tcb_fixture_get :=
  unfold V293_tcb_fixture_pointer,addr,offset,block in *;
  repeat first [rewrite map_get_set |
    rewrite map_get_set' by (intro E; inversion E; lia) | rewrite map_emp_get]; reflexivity.

Lemma V293_tcb_fixture_pointer_load :
  load (Tptr V293_tcb_type) V293_tcb_fixture_pointer (40%positive,0%Z) =
    Some (Vptr (41%positive,Int.repr 8)).
Proof.
  assert (Bytes : loadbytes V293_tcb_fixture_pointer (40%positive,0%Z) 4 =
    Some (encode_val (Tptr V293_tcb_type) (Vptr (41%positive,Int.repr 8)))).
  { change (loadbytes V293_tcb_fixture_pointer (40%positive,0%Z)
      (length (encode_val (Tptr V293_tcb_type) (Vptr (41%positive,Int.repr 8)))) =
      Some (encode_val (Tptr V293_tcb_type) (Vptr (41%positive,Int.repr 8)))).
    apply V293_loadbytes_get.
    intros [ | [ | [ | [ | k]]]] R;
      try (cbn [encode_val inj_pointer list_repeat length] in R; lia);
      exists true; cbn [encode_val inj_pointer list_repeat nth]; tcb_fixture_get. }
  change (match loadbytes V293_tcb_fixture_pointer (40%positive,0%Z) 4 with
    | Some bs => Some (decode_val (Tptr V293_tcb_type) bs) | None => None end =
    Some (Vptr (41%positive,Int.repr 8))).
  rewrite Bytes. reflexivity.
Qed.

(* All physical entry requirements inhabit this SAME memory. Its TCB base
   offset is 8, not zero; unused TCB fields and full initialization stay open. *)
Theorem V293_tcb_read_entry_witness : forall vy vby vx,
  vy < 256 -> vby < 256 -> vx < 256 ->
  let M := V293_tcb_fixture_memory vy vby vx in
  get V293_tcb_fixture_le 400%Z = Some (40%positive,Tptr V293_tcb_type) /\
  get V293_tcb_fixture_le 401%Z = Some (42%positive,Tint8) /\
  get V293_tcb_fixture_le 402%Z = Some (43%positive,Tint8) /\
  get V293_tcb_fixture_le 403%Z = Some (44%positive,Tint8) /\
  load (Tptr V293_tcb_type) M (40%positive,0%Z) = Some (Vptr (41%positive,Int.repr 8)) /\
  V293_tcb_old_loads M 41%positive 8%Z vy vby vx /\
  (exists v, get M (42%positive,0%Z) = Some (true,v)) /\
  (exists v, get M (43%positive,0%Z) = Some (true,v)) /\
  (exists v, get M (44%positive,0%Z) = Some (true,v)).
Proof.
  intros vy vby vx Y BY X. cbn zeta.
  assert (B400 : get V293_tcb_fixture_le 400%Z = Some (40%positive,Tptr V293_tcb_type)).
  { unfold V293_tcb_fixture_le. repeat rewrite map_get_set' by discriminate. apply map_get_set. }
  assert (B401 : get V293_tcb_fixture_le 401%Z = Some (42%positive,Tint8)).
  { unfold V293_tcb_fixture_le. repeat rewrite map_get_set' by discriminate. apply map_get_set. }
  assert (B402 : get V293_tcb_fixture_le 402%Z = Some (43%positive,Tint8)).
  { unfold V293_tcb_fixture_le. rewrite map_get_set' by discriminate. apply map_get_set. }
  assert (B403 : get V293_tcb_fixture_le 403%Z = Some (44%positive,Tint8)).
  { unfold V293_tcb_fixture_le. apply map_get_set. }
  split; [exact B400 | ]. split; [exact B401 | ]. split; [exact B402 | ].
  split; [exact B403 | ]. split.
  - unfold V293_tcb_fixture_memory.
    repeat rewrite V293_put_byte_pointer_frame by discriminate.
    exact V293_tcb_fixture_pointer_load.
  - split.
    + unfold V293_tcb_old_loads,V293_tcb_fixture_memory.
      repeat split; repeat rewrite V293_put_byte_other_load by discriminate;
        apply V293_put_byte_load; assumption.
    + unfold V293_tcb_fixture_memory,V293_put_byte.
      repeat split; eexists; repeat rewrite map_get_set' by discriminate; apply map_get_set.
Qed.

Theorem V293_tcb_read_execution_witness : forall P ks vy vby vx,
  vy < 256 -> vby < 256 -> vx < 256 ->
  let M := V293_tcb_fixture_memory vy vby vx in
  let M' := V293_tcb_read_memory M 42%positive 43%positive 44%positive vy vby vx in
  cstepstar P (curs (V293_task_prio_read_old 400%Z 401%Z 402%Z 403%Z),(kenil,ks))
    (V293_tcb_fixture_ge,V293_tcb_fixture_le,M)
    (curs (sskip None),(kenil,ks)) (V293_tcb_fixture_ge,V293_tcb_fixture_le,M') /\
  load Tint8 M' (42%positive,0%Z) = Some (V293_byteval vy) /\
  load Tint8 M' (43%positive,0%Z) = Some (V293_byteval vby) /\
  load Tint8 M' (44%positive,0%Z) = Some (V293_byteval vx).
Proof.
  intros P ks vy vby vx Y BY X. cbn zeta.
  destruct (V293_tcb_read_entry_witness vy vby vx Y BY X)
    as [Bp [By [Bby [Bx [Hptr [Fields [Wy [Wby Wx]]]]]]]].
  destruct (V293_task_prio_read_old_execution P ks V293_tcb_fixture_ge V293_tcb_fixture_le
    (V293_tcb_fixture_memory vy vby vx) 400%Z 401%Z 402%Z 403%Z
    40%positive 41%positive 42%positive 43%positive 44%positive 8%Z vy vby vx
    Y BY X ltac:(lia) ltac:(change (8+55 <= 4294967295)%Z; lia) Bp By Bby Bx
    ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
    ltac:(intros b [E | [E | E]]; subst; split; discriminate) Hptr Fields Wy Wby Wx)
    as [E [Ly [Lby [Lx _]]]]. auto.
Qed.

Theorem V293_tcb_read_physical_control : forall P ks,
  let M := V293_tcb_fixture_memory 1 2 4 in
  let M' := V293_tcb_read_memory M 42%positive 43%positive 44%positive 1 2 4 in
  cstepstar P (curs (V293_task_prio_read_old 400%Z 401%Z 402%Z 403%Z),(kenil,ks))
    (V293_tcb_fixture_ge,V293_tcb_fixture_le,M)
    (curs (sskip None),(kenil,ks)) (V293_tcb_fixture_ge,V293_tcb_fixture_le,M') /\
  load Tint8 M' (42%positive,0%Z) = Some (V293_byteval 1) /\
  load Tint8 M' (43%positive,0%Z) = Some (V293_byteval 2) /\
  load Tint8 M' (44%positive,0%Z) = Some (V293_byteval 4).
Proof.
  intros P ks. exact (V293_tcb_read_execution_witness P ks 1 2 4
    ltac:(lia) ltac:(lia) ltac:(lia)).
Qed.

(* Neutralizing only pointer/local separation: an actual byte store to
   ptcb's first storage byte destroys pointer decoding. Not a legal API run. *)
Theorem V293_tcb_pointer_alias_control :
  let M := V293_tcb_fixture_memory 1 2 4 in
  exists M', store Tint8 M (40%positive,0%Z) (V293_byteval 1) = Some M' /\
    load (Tptr V293_tcb_type) M' (40%positive,0%Z) = Some Vundef.
Proof.
  cbn zeta. exists (V293_put_byte (V293_tcb_fixture_memory 1 2 4) (40%positive,0%Z) 1).
  split.
  - apply V293_put_byte_store with (old := Pointer 41%positive (Int.repr 8) 3).
    unfold V293_tcb_fixture_memory.
    repeat rewrite V293_put_byte_other by discriminate. tcb_fixture_get.
  - assert (Bytes : loadbytes
        (V293_put_byte (V293_tcb_fixture_memory 1 2 4) (40%positive,0%Z) 1)
        (40%positive,0%Z) 4 =
        Some (Byte (Byte.repr 1) :: Pointer 41%positive (Int.repr 8) 2 ::
          Pointer 41%positive (Int.repr 8) 1 :: Pointer 41%positive (Int.repr 8) 0 :: nil)).
    { change (loadbytes
        (V293_put_byte (V293_tcb_fixture_memory 1 2 4) (40%positive,0%Z) 1)
        (40%positive,0%Z) (length
        (Byte (Byte.repr 1) :: Pointer 41%positive (Int.repr 8) 2 ::
          Pointer 41%positive (Int.repr 8) 1 :: Pointer 41%positive (Int.repr 8) 0 :: nil)) =
        Some (Byte (Byte.repr 1) :: Pointer 41%positive (Int.repr 8) 2 ::
          Pointer 41%positive (Int.repr 8) 1 :: Pointer 41%positive (Int.repr 8) 0 :: nil)).
      apply V293_loadbytes_get. intros [ | [ | [ | [ | k]]]] R;
        try (simpl in R; lia); exists true;
        cbn [nth]; unfold V293_tcb_fixture_memory,V293_put_byte;
        tcb_fixture_get. }
    change (match loadbytes
        (V293_put_byte (V293_tcb_fixture_memory 1 2 4) (40%positive,0%Z) 1)
        (40%positive,0%Z) 4 with
      | Some bs => Some (decode_val (Tptr V293_tcb_type) bs) | None => None end = Some Vundef).
    rewrite Bytes. reflexivity.
Qed.

(* Actual promoted bit test, independently checked over its full byte domain. *)
Definition V293_ready_test_int row bit :=
  Int.and (Int.repr (Z.of_nat row)) (Int.shl Int.one (Int.repr (Z.of_nat bit))).
Lemma V293_ready_test_checked :
  forallb (fun row => forallb (fun bit => Bool.eqb
    (negb (Int.eq (V293_ready_test_int row bit) Int.zero)) (Nat.testbit row bit))
    (seq 0 8)) (seq 0 256) = true.
Proof. vm_compute. reflexivity. Qed.

Theorem V293_ready_test_arithmetic : forall row bit,
  row < 256 -> bit < 8 ->
  negb (Int.eq (V293_ready_test_int row bit) Int.zero) = Nat.testbit row bit.
Proof.
  intros row bit R B. pose proof V293_ready_test_checked as H.
  rewrite forallb_forall in H. specialize (H row (proj2 (in_seq 256 0 row) ltac:(lia))).
  rewrite forallb_forall in H. specialize (H bit (proj2 (in_seq 8 0 bit) ltac:(lia))).
  apply Bool.eqb_prop in H. exact H.
Qed.

Lemma V293_ready_test_expr_eval : forall ge le M row mask r bit,
  r < 256 -> bit < 8 ->
  evaltype row (ge,le,M) = Some Tint8 -> evalval row (ge,le,M) = Some (V293_byteval r) ->
  evaltype mask (ge,le,M) = Some Tint8 -> evalval mask (ge,le,M) = Some (V293_mask_value bit) ->
  evalval (eunop oppsite (ebinop oeq
    (ebinop obitand (ecast row Tint32) (ecast mask Tint32)) (econst32 Int.zero)))
    (ge,le,M) = Some (Vint32 (if Nat.testbit r bit then Int.one else Int.zero)).
Proof.
  intros ge le M row mask r bit R B Tr Vr Tm Vm.
  cbn [evalval evaltype]. rewrite Tr,Vr,Tm,Vm.
  cbn [cast_eval bop_type bop_int_type bop_eval val_eq cmp_int_type is_int_type
    uop_type uop_eval notint].
  unfold V293_byteval,V293_mask_value.
  cbn [and val_eq uop_eval notint].
  pose proof (V293_ready_test_arithmetic r bit R B) as A.
  unfold V293_ready_test_int in A.
  destruct (Int.eq (Int.and (Int.repr (Z.of_nat r))
    (Int.shl Int.one (Int.repr (Z.of_nat bit)))) Int.zero) eqn:E;
    simpl in A; rewrite <- A; reflexivity.
Qed.

Definition V293_ready_test_flag lo hi old : bool :=
  Nat.testbit (V293_ready_row lo hi (V293_prio_row old)) (V293_prio_bit old).
Definition V293_ready_branch_memory M br bg lo hi old new : mem :=
  if V293_ready_test_flag lo hi old
  then V293_rekey_ready_memory M br bg lo hi old new else M.
Definition V293_ready_branch_rows lo hi old new : nat * nat :=
  if V293_ready_test_flag lo hi old then V293_ready_rekey_rows lo hi old new else (lo,hi).

(* Branch selection is derived from actual entry reads, not a caller oracle. *)
Theorem V293_task_prio_ready_branch_execution :
  forall P ks ge le M rows group yo yn xo xn byo byn br bg lo hi old new,
  old < 13 -> new < 13 -> lo < 256 -> hi < 256 -> br <> bg ->
  get le rows = None -> get ge rows = Some (br,Tarray Tint8 2) ->
  get le group = None -> get ge group = Some (bg,Tint8) ->
  V293_rekey_bitmap_loads M br bg lo hi (V293_ready_group lo hi) ->
  V293_rekey_bitmap_writable M br bg ->
  V293_rekey_locals ge le M br bg (V293_rekey_ready_bindings yo yn xo xn byo byn old new) ->
  let M' := V293_ready_branch_memory M br bg lo hi old new in
  let finalrows := V293_ready_branch_rows lo hi old new in
  evalval (V293_task_prio_ready_test rows yo xo) (ge,le,M) =
    Some (Vint32 (if V293_ready_test_flag lo hi old then Int.one else Int.zero)) /\
  cstepstar P (curs (V293_task_prio_ready_branch rows group yo yn xo xn byo byn),(kenil,ks))
    (ge,le,M) (curs (sskip None),(kenil,ks)) (ge,le,M') /\
  V293_rekey_bitmap_loads M' br bg (fst finalrows) (snd finalrows)
    (V293_ready_group (fst finalrows) (snd finalrows)) /\
  V293_rekey_bitmap_writable M' br bg /\
  V293_rekey_locals ge le M' br bg (V293_rekey_ready_bindings yo yn xo xn byo byn old new) /\
  (forall b i, b <> br -> b <> bg -> get M' (b,i) = get M (b,i)).
Proof.
  intros P ks ge le M rows group yo yn xo xn byo byn br bg lo hi old new
    O N L H Apart Nr Gr Ng Gg Loads W Loc. cbn zeta.
  destruct (V293_prio_coordinates old O) as [Y B].
  destruct (V293_rekey_local_eval ge le M br bg _ yo _ Loc
    ltac:(unfold V293_rekey_ready_bindings; simpl; auto)) as [Ty Vy].
  destruct (V293_rekey_local_eval ge le M br bg _ xo _ Loc
    ltac:(unfold V293_rekey_ready_bindings; simpl; auto)) as [Tx Vx].
  destruct (V293_rekey_row_eval ge le M rows (evar yo) br lo hi _ bg _
    Nr Gr Ty Vy Y Loads) as [Tr [_ Vr]].
  assert (R : V293_ready_row lo hi (V293_prio_row old) < 256)
    by (unfold V293_ready_row; destruct (V293_prio_row old =? 0); assumption).
  assert (Test : evalval (V293_task_prio_ready_test rows yo xo) (ge,le,M) =
    Some (Vint32 (if V293_ready_test_flag lo hi old then Int.one else Int.zero))).
  { unfold V293_task_prio_ready_test,V293_ready_test_flag.
    eapply V293_ready_test_expr_eval; eassumption. }
  split; [exact Test | ].
  unfold V293_ready_branch_memory,V293_ready_branch_rows.
  destruct (V293_ready_test_flag lo hi old) eqn:F.
  - destruct (V293_task_prio_ready_then_execution P ks ge le M rows group yo yn xo xn byo byn
      br bg lo hi old new O N L H Apart Nr Gr Ng Gg Loads W Loc) as [E Rest].
    split; [ | exact Rest]. unfold V293_task_prio_ready_branch.
    eapply V293_rekey_if_execution with (flag := true); [exact Test | | ].
    + intros _. exact E.
    + discriminate.
  - split.
    + unfold V293_task_prio_ready_branch.
      eapply V293_rekey_if_execution with (flag := false); [exact Test | discriminate | auto].
    + simpl. split; [exact Loads | ]. split; [exact W | ].
      split; [exact Loc | ]. intros. reflexivity.
Qed.

Definition V293_rekey_new_bindings (yn xn byn : var) (new : nat) :=
  (yn,V293_byteval (V293_prio_row new)) ::
  (xn,V293_mask_value (V293_prio_bit new)) ::
  (byn,V293_mask_value (V293_prio_row new)) :: nil.

Lemma V293_tcb_read_byte_frame : forall M dy dby dx y byv x b i,
  b <> dy -> b <> dby -> b <> dx ->
  load Tint8 (V293_tcb_read_memory M dy dby dx y byv x) (b,i) = load Tint8 M (b,i).
Proof.
  intros. unfold V293_tcb_read_memory.
  repeat rewrite V293_put_byte_other_load by congruence. reflexivity.
Qed.

(* Three old values are obtained by the actual TCB assignments. Only the
   three already-computed NEW values are required at entry. Their blocks
   must survive the three old-value writes; no post-read bindings oracle. *)
Theorem V293_task_prio_read_ready_execution :
  forall P ks ge le M ptcb rows group yo yn xo xn byo byn
    bc bt dy dby dx base br bg lo hi old new,
  old < 13 -> new < 13 -> lo < 256 -> hi < 256 -> br <> bg ->
  (0 <= base)%Z -> (base+55 <= Int.max_unsigned)%Z ->
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  get le yo = Some (dy,Tint8) -> get le byo = Some (dby,Tint8) -> get le xo = Some (dx,Tint8) ->
  get le rows = None -> get ge rows = Some (br,Tarray Tint8 2) ->
  get le group = None -> get ge group = Some (bg,Tint8) ->
  dy <> dby -> dy <> dx -> dby <> dx ->
  (forall b, b = dy \/ b = dby \/ b = dx -> b <> bc /\ b <> bt /\ b <> br /\ b <> bg) ->
  load (Tptr V293_tcb_type) M (bc,0%Z) = Some (Vptr (bt,Int.repr base)) ->
  V293_tcb_old_loads M bt base (V293_prio_row old)
    (2 ^ V293_prio_row old) (2 ^ V293_prio_bit old) ->
  (exists v, get M (dy,0%Z) = Some (true,v)) ->
  (exists v, get M (dby,0%Z) = Some (true,v)) ->
  (exists v, get M (dx,0%Z) = Some (true,v)) ->
  V293_rekey_bitmap_loads M br bg lo hi (V293_ready_group lo hi) ->
  V293_rekey_bitmap_writable M br bg ->
  V293_rekey_locals ge le M br bg (V293_rekey_new_bindings yn xn byn new) ->
  (forall x v b, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (b,Tint8) -> b <> dy /\ b <> dby /\ b <> dx) ->
  let Mr := V293_tcb_read_memory M dy dby dx (V293_prio_row old)
    (2 ^ V293_prio_row old) (2 ^ V293_prio_bit old) in
  let Mf := V293_ready_branch_memory Mr br bg lo hi old new in
  let finalrows := V293_ready_branch_rows lo hi old new in
  cstepstar P (curs (V293_task_prio_read_ready ptcb rows group yo yn xo xn byo byn),(kenil,ks))
    (ge,le,M) (curs (sskip None),(kenil,ks)) (ge,le,Mf) /\
  evalval (V293_task_prio_ready_test rows yo xo) (ge,le,Mr) =
    Some (Vint32 (if V293_ready_test_flag lo hi old then Int.one else Int.zero)) /\
  V293_rekey_bitmap_loads Mf br bg (fst finalrows) (snd finalrows)
    (V293_ready_group (fst finalrows) (snd finalrows)) /\
  V293_rekey_bitmap_writable Mf br bg /\
  V293_rekey_locals ge le Mf br bg (V293_rekey_ready_bindings yo yn xo xn byo byn old new) /\
  (forall b i, b <> dy -> b <> dby -> b <> dx -> b <> br -> b <> bg ->
    get Mf (b,i) = get M (b,i)).
Proof.
  intros P ks ge le M ptcb rows group yo yn xo xn byo byn bc bt dy dby dx base br bg lo hi old new
    O N L H BR Base Limit Bp By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Hptr Fields
    Wy Wby Wx Loads W NewLoc NewApart. cbn zeta.
  destruct (V293_prio_coordinates old O) as [Y X].
  destruct (V293_mask_byte_value (V293_prio_row old) ltac:(lia)) as [BYBound BYValue].
  destruct (V293_mask_byte_value (V293_prio_bit old) X) as [XBound XValue].
  assert (A : forall b, b = dy \/ b = dby \/ b = dx -> b <> bc /\ b <> bt).
  { intros b I. destruct (Apart b I) as [C [T _]]. auto. }
  pose proof (V293_task_prio_read_old_execution P ks ge le M ptcb yo byo xo
    bc bt dy dby dx base (V293_prio_row old) (2 ^ V293_prio_row old) (2 ^ V293_prio_bit old)
    ltac:(lia) BYBound XBound Base Limit Bp By Bby Bx YBY YX BYX A Hptr Fields Wy Wby Wx)
    as [Read [Ly [Lby [Lx [_ [_ Frame]]]]]].
  set (Mr := V293_tcb_read_memory M dy dby dx (V293_prio_row old)
    (2 ^ V293_prio_row old) (2 ^ V293_prio_bit old)) in *.
  pose proof (Apart dy ltac:(auto)) as Ady.
  pose proof (Apart dby ltac:(auto)) as Adby.
  pose proof (Apart dx ltac:(auto)) as Adx.
  assert (BrA : br <> dy /\ br <> dby /\ br <> dx) by (intuition congruence).
  assert (BgA : bg <> dy /\ bg <> dby /\ bg <> dx) by (intuition congruence).
  assert (LoadsR : V293_rekey_bitmap_loads Mr br bg lo hi (V293_ready_group lo hi)).
  { unfold V293_rekey_bitmap_loads,Mr. repeat rewrite V293_tcb_read_byte_frame by tauto. exact Loads. }
  assert (WR : V293_rekey_bitmap_writable Mr br bg).
  { unfold V293_rekey_bitmap_writable. repeat rewrite Frame by tauto. exact W. }
  assert (NewR : V293_rekey_locals ge le Mr br bg (V293_rekey_new_bindings yn xn byn new)).
  { intros x v I. destruct (NewLoc x v I) as (b & Bind & Ar & Ag & Lval).
    destruct (NewApart x v b I Bind) as [Ay [Aby Ax]].
    exists b. repeat split; try assumption. unfold Mr.
    rewrite V293_tcb_read_byte_frame by assumption. exact Lval. }
  assert (LocR : V293_rekey_locals ge le Mr br bg
    (V293_rekey_ready_bindings yo yn xo xn byo byn old new)).
  { intros x v I. cbn [V293_rekey_ready_bindings In] in I.
    destruct I as [E|[E|[E|[E|[E|[E|F]]]]]]; try contradiction.
    - inversion E; subst x v. exists dy. destruct (Apart dy ltac:(auto)) as [_ [_ [Ar Ag]]]. auto.
    - apply NewR. unfold V293_rekey_new_bindings. simpl. auto.
    - inversion E; subst x v. exists dx. destruct (Apart dx ltac:(auto)) as [_ [_ [Ar Ag]]].
      rewrite <- XValue. auto.
    - apply NewR. unfold V293_rekey_new_bindings. simpl. auto.
    - inversion E; subst x v. exists dby. destruct (Apart dby ltac:(auto)) as [_ [_ [Ar Ag]]].
      rewrite <- BYValue. auto.
    - apply NewR. unfold V293_rekey_new_bindings. simpl. auto. }
  destruct (V293_task_prio_ready_branch_execution P ks ge le Mr rows group yo yn xo xn byo byn
    br bg lo hi old new O N L H BR Nr Gr Ng Gg LoadsR WR LocR)
    as [Test [Branch [FinalLoads [FinalW [FinalLoc FinalFrame]]]]].
  split.
  - unfold V293_task_prio_read_ready. eapply V293_rekey_sequence_execution; [ | exact Branch].
    intro tail. exact (proj1 (V293_task_prio_read_old_execution P tail ge le M ptcb yo byo xo
      bc bt dy dby dx base (V293_prio_row old) (2 ^ V293_prio_row old) (2 ^ V293_prio_bit old)
      ltac:(lia) BYBound XBound Base Limit Bp By Bby Bx YBY YX BYX A Hptr Fields Wy Wby Wx)).
  - split; [exact Test | ]. split; [exact FinalLoads | ]. split; [exact FinalW | ].
    split; [exact FinalLoc | ]. intros b i Ay Aby Ax Ar Ag.
    rewrite FinalFrame by assumption. apply Frame; assumption.
Qed.

(* One actual memory: source pointer/TCB, bitmap, three NEW local values,
   and deliberately stale (255) destinations of the three OLD assignments. *)
Definition V293_read_ready_fixture_le : env :=
  set V293_ready_fragment_fixture_le 400%Z (40%positive,Tptr V293_tcb_type).
Definition V293_read_ready_fixture_mem lo hi old new : mem :=
  V293_put_byte (V293_put_byte (V293_put_byte
    (V293_put_byte (V293_put_byte (V293_put_byte
      (V293_put_byte (V293_put_byte (V293_put_byte
        (V293_put_byte (V293_put_byte (V293_put_byte V293_tcb_fixture_pointer
          (41%positive,60%Z) (V293_prio_row old))
          (41%positive,62%Z) (2 ^ V293_prio_row old))
          (41%positive,61%Z) (2 ^ V293_prio_bit old))
        (30%positive,0%Z) lo) (30%positive,1%Z) hi)
        (31%positive,0%Z) (V293_ready_group lo hi))
      (32%positive,0%Z) 255) (36%positive,0%Z) 255) (34%positive,0%Z) 255)
    (33%positive,0%Z) (V293_prio_row new))
    (35%positive,0%Z) (2 ^ V293_prio_bit new))
    (37%positive,0%Z) (2 ^ V293_prio_row new).

Local Ltac read_ready_fixture_get :=
  unfold V293_ready_fragment_fixture_ge,V293_read_ready_fixture_le,
    V293_ready_fragment_fixture_le,V293_read_ready_fixture_mem;
  repeat first [rewrite V293_put_byte_get_same |
    rewrite V293_put_byte_other by discriminate | rewrite map_get_set |
    rewrite map_get_set' by discriminate | rewrite map_emp_get].
Local Ltac read_ready_fixture_load :=
  unfold V293_read_ready_fixture_mem;
  repeat rewrite V293_put_byte_other_load by discriminate;
  apply V293_put_byte_load; eassumption.

Theorem V293_read_ready_entry_witness : forall lo hi old new,
  lo < 256 -> hi < 256 -> old < 13 -> new < 13 ->
  let M := V293_read_ready_fixture_mem lo hi old new in
  load (Tptr V293_tcb_type) M (40%positive,0%Z) = Some (Vptr (41%positive,Int.repr 8)) /\
  V293_tcb_old_loads M 41%positive 8%Z (V293_prio_row old)
    (2 ^ V293_prio_row old) (2 ^ V293_prio_bit old) /\
  (exists v, get M (32%positive,0%Z) = Some (true,v)) /\
  (exists v, get M (36%positive,0%Z) = Some (true,v)) /\
  (exists v, get M (34%positive,0%Z) = Some (true,v)) /\
  V293_rekey_bitmap_loads M 30%positive 31%positive lo hi (V293_ready_group lo hi) /\
  V293_rekey_bitmap_writable M 30%positive 31%positive /\
  V293_rekey_locals V293_ready_fragment_fixture_ge V293_read_ready_fixture_le M
    30%positive 31%positive (V293_rekey_new_bindings 303%Z 305%Z 307%Z new).
Proof.
  intros lo hi old new L H O N. cbn zeta.
  destruct (V293_prio_coordinates old O) as [Yo Xo].
  destruct (V293_prio_coordinates new N) as [Yn Xn].
  destruct (V293_mask_byte_value (V293_prio_row old) ltac:(lia)) as [BYo EBYo].
  destruct (V293_mask_byte_value (V293_prio_bit old) Xo) as [BXo EBXo].
  destruct (V293_mask_byte_value (V293_prio_row new) ltac:(lia)) as [BYn EBYn].
  destruct (V293_mask_byte_value (V293_prio_bit new) Xn) as [BXn EBXn].
  assert (Yob : V293_prio_row old < 256) by lia.
  assert (Ynb : V293_prio_row new < 256) by lia.
  assert (G : V293_ready_group lo hi < 256).
  { unfold V293_ready_group. destruct (lo =? 0); destruct (hi =? 0); lia. }
  split.
  - unfold V293_read_ready_fixture_mem.
    repeat rewrite V293_put_byte_pointer_frame by discriminate. exact V293_tcb_fixture_pointer_load.
  - split.
    + unfold V293_tcb_old_loads. repeat split; read_ready_fixture_load.
    + split; [eexists; read_ready_fixture_get; reflexivity | ].
      split; [eexists; read_ready_fixture_get; reflexivity | ].
      split; [eexists; read_ready_fixture_get; reflexivity | ].
      split.
      * unfold V293_rekey_bitmap_loads. repeat split; read_ready_fixture_load.
      * split.
        -- unfold V293_rekey_bitmap_writable. repeat split; eexists; read_ready_fixture_get; reflexivity.
        -- intros x v I. cbn [V293_rekey_new_bindings In] in I.
           destruct I as [E|[E|[E|F]]]; try contradiction; inversion E; subst x v.
           all: eexists; split; [read_ready_fixture_get; reflexivity | ];
             split; [discriminate | ]; split; [discriminate | ].
           all: try read_ready_fixture_load.
           all: rewrite <- EBXn || rewrite <- EBYn; read_ready_fixture_load.
Qed.

Theorem V293_read_ready_execution_witness : forall P ks lo hi old new,
  lo < 256 -> hi < 256 -> old < 13 -> new < 13 ->
  let M := V293_read_ready_fixture_mem lo hi old new in
  let Mr := V293_tcb_read_memory M 32%positive 36%positive 34%positive
    (V293_prio_row old) (2 ^ V293_prio_row old) (2 ^ V293_prio_bit old) in
  let Mf := V293_ready_branch_memory Mr 30%positive 31%positive lo hi old new in
  let fr := V293_ready_branch_rows lo hi old new in
  cstepstar P (curs (V293_task_prio_read_ready 400%Z
    300%Z 301%Z 302%Z 303%Z 304%Z 305%Z 306%Z 307%Z),(kenil,ks))
    (V293_ready_fragment_fixture_ge,V293_read_ready_fixture_le,M)
    (curs (sskip None),(kenil,ks)) (V293_ready_fragment_fixture_ge,V293_read_ready_fixture_le,Mf) /\
  evalval (V293_task_prio_ready_test 300%Z 302%Z 304%Z)
    (V293_ready_fragment_fixture_ge,V293_read_ready_fixture_le,Mr) =
    Some (Vint32 (if V293_ready_test_flag lo hi old then Int.one else Int.zero)) /\
  V293_rekey_bitmap_loads Mf 30%positive 31%positive (fst fr) (snd fr)
    (V293_ready_group (fst fr) (snd fr)).
Proof.
  intros P ks lo hi old new L H O N. cbn zeta.
  destruct (V293_read_ready_entry_witness lo hi old new L H O N)
    as [Hptr [Fields [Wy [Wby [Wx [Loads [W NewLoc]]]]]]].
  destruct (V293_task_prio_read_ready_execution P ks V293_ready_fragment_fixture_ge
    V293_read_ready_fixture_le (V293_read_ready_fixture_mem lo hi old new)
    400%Z 300%Z 301%Z 302%Z 303%Z 304%Z 305%Z 306%Z 307%Z
    40%positive 41%positive 32%positive 36%positive 34%positive 8%Z
    30%positive 31%positive lo hi old new)
    as [Exec [Test [Read _]]].
  all: try assumption; try discriminate; try (read_ready_fixture_get; reflexivity);
    try (change (0 <= 8)%Z; lia); try (change (8+55 <= 4294967295)%Z; lia).
  - intros b [E|[E|E]]; subst b; repeat split; discriminate.
  - intros x v b I Bind. cbn [V293_rekey_new_bindings In] in I.
    destruct I as [E|[E|[E|F]]]; try contradiction; inversion E; subst x v;
      unfold V293_read_ready_fixture_le,V293_ready_fragment_fixture_le in Bind;
      repeat rewrite map_get_set' in Bind by discriminate;
      rewrite map_get_set in Bind; inversion Bind; subst b; repeat split; discriminate.
  - auto.
Qed.

Definition V293_read_ready_observes lo hi old new (flag : bool) expectedlo expectedhi expectedgroup : Prop :=
  forall P ks,
  let M := V293_read_ready_fixture_mem lo hi old new in
  let Mr := V293_tcb_read_memory M 32%positive 36%positive 34%positive
    (V293_prio_row old) (2 ^ V293_prio_row old) (2 ^ V293_prio_bit old) in
  let Mf := V293_ready_branch_memory Mr 30%positive 31%positive lo hi old new in
  cstepstar P (curs (V293_task_prio_read_ready 400%Z
    300%Z 301%Z 302%Z 303%Z 304%Z 305%Z 306%Z 307%Z),(kenil,ks))
    (V293_ready_fragment_fixture_ge,V293_read_ready_fixture_le,M)
    (curs (sskip None),(kenil,ks)) (V293_ready_fragment_fixture_ge,V293_read_ready_fixture_le,Mf) /\
  evalval (V293_task_prio_ready_test 300%Z 302%Z 304%Z)
    (V293_ready_fragment_fixture_ge,V293_read_ready_fixture_le,Mr) =
    Some (Vint32 (if flag then Int.one else Int.zero)) /\
  V293_rekey_bitmap_loads Mf 30%positive 31%positive expectedlo expectedhi expectedgroup.

(* Single-factor semantic control: only old ready bit 2 is cleared from the
   input row (20 -> 16). Both runs execute the three reads from stale 255. *)
Theorem V293_read_ready_physical_controls :
  V293_read_ready_observes 20 0 2 6 true 80 0 1 /\
  V293_read_ready_observes 16 0 2 6 false 16 0 1.
Proof.
  split; intros P ks.
  - exact (V293_read_ready_execution_witness P ks 20 0 2 6
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
  - exact (V293_read_ready_execution_witness P ks 16 0 2 6
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
Qed.

(* A bytewise frame transports actual loads, including multi-byte pointers. *)
Lemma V293_load_block_frame : forall tp M M' b i,
  (forall j, get M' (b,j) = get M (b,j)) ->
  load tp M' (b,i) = load tp M (b,i).
Proof.
  intros tp M M' b i Frame. destruct tp; unfold load,loadm; try reflexivity;
    rewrite V293_loadbytes_ext with (M := M); try reflexivity;
    intros; apply Frame.
Qed.

(* One physical entry, no suffix-execution or intermediate-read oracle.
   The entire table view is required at ENTRY and derived at the FINAL
   memory after the local writes and ready bitmap branch, not merely M2. *)
Theorem V293_task_prio_prefix_execution :
  forall P ks ge le M table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi old new entries,
  old < 13 -> new < 13 -> old <> new -> lo < 256 -> hi < 256 -> br <> bg ->
  (0 <= base)%Z -> (base+55 <= Int.max_unsigned)%Z ->
  get le table = None -> get ge table = Some (b,Tarray (Tptr V293_tcb_type) 13) ->
  get le oldprio = Some (bo,Tint8) -> get le newprio = Some (bn,Tint8) ->
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  b <> bo -> b <> bn -> b <> bc -> b <> bt ->
  b <> dy -> b <> dby -> b <> dx -> b <> br -> b <> bg ->
  load Tint8 M (bo,0%Z) = Some (V293_byteval old) ->
  load Tint8 M (bn,0%Z) = Some (V293_byteval new) ->
  load (Tptr V293_tcb_type) M (bc,0%Z) = Some (Vptr (bt,Int.repr base)) ->
  V293_bytes_writable M b (4*Z.of_nat old)%Z 4 ->
  V293_bytes_writable M b (4*Z.of_nat new)%Z 4 ->
  length entries = 13 -> V293_table_loads V293_tcb_type M b entries ->
  get le yo = Some (dy,Tint8) -> get le byo = Some (dby,Tint8) -> get le xo = Some (dx,Tint8) ->
  get le rows = None -> get ge rows = Some (br,Tarray Tint8 2) ->
  get le group = None -> get ge group = Some (bg,Tint8) ->
  dy <> dby -> dy <> dx -> dby <> dx ->
  (forall c, c = dy \/ c = dby \/ c = dx -> c <> bc /\ c <> bt /\ c <> br /\ c <> bg) ->
  V293_tcb_old_loads M bt base (V293_prio_row old)
    (2 ^ V293_prio_row old) (2 ^ V293_prio_bit old) ->
  (exists v, get M (dy,0%Z) = Some (true,v)) ->
  (exists v, get M (dby,0%Z) = Some (true,v)) ->
  (exists v, get M (dx,0%Z) = Some (true,v)) ->
  V293_rekey_bitmap_loads M br bg lo hi (V293_ready_group lo hi) ->
  V293_rekey_bitmap_writable M br bg ->
  V293_rekey_locals ge le M br bg (V293_rekey_new_bindings yn xn byn new) ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> b /\ c <> dy /\ c <> dby /\ c <> dx) ->
  exists M1 M2,
  let Mr := V293_tcb_read_memory M2 dy dby dx (V293_prio_row old)
    (2 ^ V293_prio_row old) (2 ^ V293_prio_bit old) in
  let Mf := V293_ready_branch_memory Mr br bg lo hi old new in
  let fr := V293_ready_branch_rows lo hi old new in
  store (Tptr V293_tcb_type) M (b,(4*Z.of_nat old)%Z) Vnull = Some M1 /\
  store (Tptr V293_tcb_type) M1 (b,(4*Z.of_nat new)%Z) (Vptr (bt,Int.repr base)) = Some M2 /\
  cstepstar P (curs (V293_task_prio_prefix table oldprio newprio ptcb rows group yo yn xo xn byo byn),
    (kenil,ks)) (ge,le,M) (curs (sskip None),(kenil,ks)) (ge,le,Mf) /\
  evalval (V293_task_prio_ready_test rows yo xo) (ge,le,Mr) =
    Some (Vint32 (if V293_ready_test_flag lo hi old then Int.one else Int.zero)) /\
  V293_rekey_bitmap_loads Mf br bg (fst fr) (snd fr) (V293_ready_group (fst fr) (snd fr)) /\
  V293_table_loads V293_tcb_type Mf b
    (update_nth_val new (update_nth_val old entries Vnull) (Vptr (bt,Int.repr base))) /\
  load (Tptr V293_tcb_type) Mf (b,(4*Z.of_nat old)%Z) = Some Vnull /\
  load (Tptr V293_tcb_type) Mf (b,(4*Z.of_nat new)%Z) = Some (Vptr (bt,Int.repr base)) /\
  V293_rekey_bitmap_writable Mf br bg /\
  V293_rekey_locals ge le Mf br bg (V293_rekey_ready_bindings yo yn xo xn byo byn old new) /\
  (forall c i, c <> b -> c <> dy -> c <> dby -> c <> dx -> c <> br -> c <> bg ->
    get Mf (c,i) = get M (c,i)).
Proof.
  intros P ks ge le M table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi old new entries
    O N ON L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg
    Lo Ln Lp Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields
    Wy Wby Wx Loads W NewLoc NewApart.
  destruct (V293_OSTaskChangePrio_table_execution P ks ge le M table oldprio newprio ptcb
    V293_tcb_type b bo bn bc old new (bt,Int.repr base)
    O N ON Nt Gt Bo Bn Bc Tbo Tbn Tbc Lo Ln Lp Wo Wn)
    as (M1 & M2 & S1 & S2 & TableExec & OldSlot & NewSlot & TableFrame).
  assert (Frame : forall c i, c <> b -> get M2 (c,i) = get M (c,i)).
  { intros c i A. apply TableFrame; left; exact A. }
  assert (ReadFrame : forall tp c i, c <> b -> load tp M2 (c,i) = load tp M (c,i)).
  { intros tp c i A. apply V293_load_block_frame. intro j. apply Frame. exact A. }
  assert (Fields2 : V293_tcb_old_loads M2 bt base (V293_prio_row old)
    (2 ^ V293_prio_row old) (2 ^ V293_prio_bit old)).
  { unfold V293_tcb_old_loads in *. repeat rewrite ReadFrame by congruence. exact Fields. }
  assert (Loads2 : V293_rekey_bitmap_loads M2 br bg lo hi (V293_ready_group lo hi)).
  { unfold V293_rekey_bitmap_loads in *. repeat rewrite ReadFrame by congruence. exact Loads. }
  assert (W2 : V293_rekey_bitmap_writable M2 br bg).
  { unfold V293_rekey_bitmap_writable in *. repeat rewrite Frame by congruence. exact W. }
  assert (NewLoc2 : V293_rekey_locals ge le M2 br bg (V293_rekey_new_bindings yn xn byn new)).
  { intros x v I. destruct (NewLoc x v I) as (c & Bind & Cr & Cg & Lval).
    destruct (NewApart x v c I Bind) as [Cb _]. exists c. repeat split; try assumption.
    rewrite ReadFrame by assumption. exact Lval. }
  destruct (V293_task_prio_read_ready_execution P ks ge le M2 ptcb rows group yo yn xo xn byo byn
    bc bt dy dby dx base br bg lo hi old new O N L H RG Base Limit Bc By Bby Bx Nr Gr Ng Gg
    YBY YX BYX Apart ltac:(rewrite ReadFrame by congruence; exact Lp) Fields2
    ltac:(rewrite Frame by congruence; exact Wy)
    ltac:(rewrite Frame by congruence; exact Wby)
    ltac:(rewrite Frame by congruence; exact Wx) Loads2 W2 NewLoc2
    ltac:(intros x v c I Bind; exact (proj2 (NewApart x v c I Bind))))
    as [Suffix [Test [FinalLoads [FinalW [FinalLoc FinalFrame]]]]].
  set (Mr := V293_tcb_read_memory M2 dy dby dx (V293_prio_row old)
    (2 ^ V293_prio_row old) (2 ^ V293_prio_bit old)) in *.
  set (Mf := V293_ready_branch_memory Mr br bg lo hi old new) in *.
  assert (TableFinalFrame : forall i, get Mf (b,i) = get M2 (b,i)).
  { intro i. apply FinalFrame; assumption. }
  assert (TableFinalLoad : forall tp i, load tp Mf (b,i) = load tp M2 (b,i)).
  { intros tp i. apply V293_load_block_frame. exact TableFinalFrame. }
  assert (FinalView : V293_table_loads V293_tcb_type Mf b
    (update_nth_val new (update_nth_val old entries Vnull) (Vptr (bt,Int.repr base)))).
  { intros p R. rewrite TableFinalLoad. eapply V293_task_prio_rekey_table_model; eassumption. }
  exists M1. exists M2. cbn zeta. fold Mr Mf. split; [exact S1 | ]. split; [exact S2 | ]. split.
  - unfold V293_task_prio_prefix. eapply V293_rekey_sequence_execution; [ | exact Suffix].
    intro tail. destruct (V293_OSTaskChangePrio_table_execution P tail ge le M table oldprio newprio ptcb
      V293_tcb_type b bo bn bc old new (bt,Int.repr base)
      O N ON Nt Gt Bo Bn Bc Tbo Tbn Tbc Lo Ln Lp Wo Wn)
      as (A & B & SA & SB & Exec & _).
    rewrite S1 in SA. inversion SA; subst A. rewrite S2 in SB. inversion SB; subst B. exact Exec.
  - split; [exact Test | ]. split; [exact FinalLoads | ]. split; [exact FinalView | ].
    split; [rewrite TableFinalLoad; exact OldSlot | ].
    split; [rewrite TableFinalLoad; exact NewSlot | ].
    split; [exact FinalW | ]. split; [exact FinalLoc | ].
    intros c i Cb Cy Cby Cx Cr Cg. rewrite FinalFrame by assumption. apply Frame. exact Cb.
Qed.

(* Finite fixture construction, NOT a runtime allocator or reachability claim. *)
Fixpoint V293_fixture_put_bytes (M : mem) (b : block) (i : Z) (bytes : list memval) : mem :=
  match bytes with
  | nil => M
  | v :: rest => set (V293_fixture_put_bytes M b (i+1)%Z rest) (b,i) (true,v)
  end.

Lemma V293_fixture_bytes_outside : forall bytes M b i c j,
  c <> b \/ (j < i)%Z \/ (i+Z.of_nat (length bytes) <= j)%Z ->
  get (V293_fixture_put_bytes M b i bytes) (c,j) = get M (c,j).
Proof.
  induction bytes as [ | v rest IH]; intros M b i c j R; [reflexivity| ].
  cbn [V293_fixture_put_bytes]. rewrite map_get_set'.
  - apply IH. simpl length in R. rewrite Nat2Z.inj_succ in R. intuition lia.
  - intro E. inversion E; subst. simpl length in R. rewrite Nat2Z.inj_succ in R. intuition lia.
Qed.

Lemma V293_fixture_bytes_nth : forall bytes M b i k,
  k < length bytes ->
  get (V293_fixture_put_bytes M b i bytes) (b,(i+Z.of_nat k)%Z) =
    Some (true,nth k bytes Undef).
Proof.
  induction bytes as [ | v rest IH]; intros M b i [ | k] R; simpl length in R; try lia.
  - replace (i+Z.of_nat 0)%Z with i by lia. apply map_get_set.
  - cbn [V293_fixture_put_bytes]. rewrite map_get_set' by (intro E; inversion E; lia).
    replace (i+Z.of_nat (S k))%Z with (i+1+Z.of_nat k)%Z by lia. apply IH. lia.
Qed.

Lemma V293_fixture_pointer_load : forall M b i v,
  rule_type_val_match (Tptr V293_tcb_type) v = true ->
  load (Tptr V293_tcb_type)
    (V293_fixture_put_bytes M b i (encode_val (Tptr V293_tcb_type) v)) (b,i) = Some v.
Proof.
  intros M b i v Match. unfold load,loadm.
  rewrite <- (encode_val_length (Tptr V293_tcb_type) v).
  rewrite V293_loadbytes_get.
  - rewrite type_val_mach_encode_val_decode_val by exact Match. reflexivity.
  - intros k K. exists true. apply V293_fixture_bytes_nth. exact K.
Qed.

Fixpoint V293_fixture_put_table (M : mem) (b : block) (i : Z) (entries : list val) : mem :=
  match entries with
  | nil => M
  | v :: rest => V293_fixture_put_bytes (V293_fixture_put_table M b (i+4)%Z rest)
      b i (encode_val (Tptr V293_tcb_type) v)
  end.

Lemma V293_fixture_table_outside : forall entries M b i c j,
  c <> b -> get (V293_fixture_put_table M b i entries) (c,j) = get M (c,j).
Proof.
  induction entries as [ | v rest IH]; intros M b i c j Apart; [reflexivity| ].
  cbn [V293_fixture_put_table]. rewrite V293_fixture_bytes_outside by (left; exact Apart).
  apply IH. exact Apart.
Qed.

Lemma V293_fixture_table_slot : forall entries M b i p,
  Forall (fun v => rule_type_val_match (Tptr V293_tcb_type) v = true) entries ->
  p < length entries ->
  load (Tptr V293_tcb_type) (V293_fixture_put_table M b i entries)
    (b,(i+4*Z.of_nat p)%Z) = Some (nth p entries Vnull).
Proof.
  induction entries as [ | v rest IH]; intros M b i [ | p] All R; simpl length in R; try lia.
  all: inversion All; subst.
  - replace (i+4*Z.of_nat 0)%Z with i by lia. cbn [V293_fixture_put_table nth].
    apply V293_fixture_pointer_load. assumption.
  - cbn [V293_fixture_put_table nth]. unfold load,loadm.
    rewrite V293_loadbytes_ext with (M := V293_fixture_put_table M b (i+4)%Z rest).
    + replace (i+4*Z.of_nat (S p))%Z with (i+4+4*Z.of_nat p)%Z by lia.
      apply IH; [assumption|lia].
    + intros k K. apply V293_fixture_bytes_outside. right; right.
      rewrite encode_val_length. simpl typelen in *. lia.
Qed.

Lemma V293_fixture_table_writable : forall entries M b i p,
  p < length entries -> V293_bytes_writable (V293_fixture_put_table M b i entries)
    b (i+4*Z.of_nat p)%Z 4.
Proof.
  induction entries as [ | v rest IH]; intros M b i [ | p] R; simpl length in R; try lia.
  - intros k K. replace (i+4*Z.of_nat 0+Z.of_nat k)%Z with (i+Z.of_nat k)%Z by lia.
    cbn [V293_fixture_put_table]. exists (nth k (encode_val (Tptr V293_tcb_type) v) Undef).
    apply V293_fixture_bytes_nth. rewrite encode_val_length. exact K.
  - intros k K. cbn [V293_fixture_put_table]. rewrite V293_fixture_bytes_outside.
    + replace (i+4*Z.of_nat (S p)+Z.of_nat k)%Z with (i+4+4*Z.of_nat p+Z.of_nat k)%Z by lia.
      apply (IH M b (i+4)%Z p ltac:(lia) k K).
    + right; right. rewrite encode_val_length. simpl typelen. lia.
Qed.

Definition V293_prefix_fixture_entries : list val :=
  Vnull :: Vnull :: Vnull :: Vnull :: Vptr (60%positive,Int.zero) :: Vnull :: Vnull ::
  Vnull :: Vptr (41%positive,Int.repr 8) :: Vnull :: Vnull :: Vnull :: Vnull :: nil.
Definition V293_prefix_fixture_ge : env :=
  set V293_ready_fragment_fixture_ge 500%Z (50%positive,Tarray (Tptr V293_tcb_type) 13).
Definition V293_prefix_fixture_le : env :=
  set (set V293_read_ready_fixture_le 501%Z (51%positive,Tint8)) 502%Z (52%positive,Tint8).
Definition V293_prefix_fixture_mem (live : bool) : mem :=
  V293_put_byte (V293_put_byte
    (V293_fixture_put_table (V293_read_ready_fixture_mem 16 (if live then 1 else 0) 8 6)
      50%positive 0%Z V293_prefix_fixture_entries) (51%positive,0%Z) 8) (52%positive,0%Z) 6.

Lemma V293_prefix_fixture_outside : forall live c i,
  c <> 50%positive -> c <> 51%positive -> c <> 52%positive ->
  get (V293_prefix_fixture_mem live) (c,i) =
    get (V293_read_ready_fixture_mem 16 (if live then 1 else 0) 8 6) (c,i).
Proof.
  intros live c i T O N. unfold V293_prefix_fixture_mem.
  repeat rewrite V293_put_byte_other by (intro E; inversion E; congruence).
  apply V293_fixture_table_outside. exact T.
Qed.

Theorem V293_prefix_fixture_table_entry : forall live,
  V293_table_loads V293_tcb_type (V293_prefix_fixture_mem live) 50%positive V293_prefix_fixture_entries /\
  V293_bytes_writable (V293_prefix_fixture_mem live) 50%positive 32%Z 4 /\
  V293_bytes_writable (V293_prefix_fixture_mem live) 50%positive 24%Z 4.
Proof.
  intro live. split.
  - intros p R. unfold V293_prefix_fixture_mem.
    repeat rewrite V293_put_byte_pointer_frame by discriminate.
    replace (4*Z.of_nat p)%Z with (0+4*Z.of_nat p)%Z by lia.
    apply V293_fixture_table_slot.
    + unfold V293_prefix_fixture_entries. repeat constructor.
    + exact R.
  - split; intros k K; unfold V293_prefix_fixture_mem;
      repeat rewrite V293_put_byte_other by discriminate.
    + change (exists v, get (V293_fixture_put_table
        (V293_read_ready_fixture_mem 16 (if live then 1 else 0) 8 6)
        50%positive 0%Z V293_prefix_fixture_entries) (50%positive,(0+4*Z.of_nat 8+Z.of_nat k)%Z)
        = Some (true,v)).
      apply V293_fixture_table_writable; [cbn; lia|exact K].
    + change (exists v, get (V293_fixture_put_table
        (V293_read_ready_fixture_mem 16 (if live then 1 else 0) 8 6)
        50%positive 0%Z V293_prefix_fixture_entries) (50%positive,(0+4*Z.of_nat 6+Z.of_nat k)%Z)
        = Some (true,v)).
      apply V293_fixture_table_writable; [cbn; lia|exact K].
Qed.

Theorem V293_prefix_fixture_body_entry : forall live,
  let M := V293_prefix_fixture_mem live in
  load (Tptr V293_tcb_type) M (40%positive,0%Z) = Some (Vptr (41%positive,Int.repr 8)) /\
  V293_tcb_old_loads M 41%positive 8%Z 1 2 1 /\
  (exists v, get M (32%positive,0%Z) = Some (true,v)) /\
  (exists v, get M (36%positive,0%Z) = Some (true,v)) /\
  (exists v, get M (34%positive,0%Z) = Some (true,v)) /\
  V293_rekey_bitmap_loads M 30%positive 31%positive 16 (if live then 1 else 0)
    (V293_ready_group 16 (if live then 1 else 0)) /\
  V293_rekey_bitmap_writable M 30%positive 31%positive /\
  V293_rekey_locals V293_prefix_fixture_ge V293_prefix_fixture_le M
    30%positive 31%positive (V293_rekey_new_bindings 303%Z 305%Z 307%Z 6).
Proof.
  intro live. cbn zeta.
  destruct (V293_read_ready_entry_witness 16 (if live then 1 else 0) 8 6
    ltac:(lia) ltac:(destruct live; lia) ltac:(lia) ltac:(lia))
    as [Hptr [Fields [Wy [Wby [Wx [Loads [W NewLoc]]]]]]].
  assert (RF : forall tp c i, c <> 50%positive -> c <> 51%positive -> c <> 52%positive ->
    load tp (V293_prefix_fixture_mem live) (c,i) =
      load tp (V293_read_ready_fixture_mem 16 (if live then 1 else 0) 8 6) (c,i)).
  { intros tp c i T O N. apply V293_load_block_frame. intro j.
    apply V293_prefix_fixture_outside; assumption. }
  split; [rewrite RF by discriminate; exact Hptr | ]. split.
  - unfold V293_tcb_old_loads in *. repeat rewrite RF by discriminate. exact Fields.
  - split; [rewrite V293_prefix_fixture_outside by discriminate; exact Wy | ].
    split; [rewrite V293_prefix_fixture_outside by discriminate; exact Wby | ].
    split; [rewrite V293_prefix_fixture_outside by discriminate; exact Wx | ]. split.
    + unfold V293_rekey_bitmap_loads in *. repeat rewrite RF by discriminate.
      exact Loads.
    + split.
      * unfold V293_rekey_bitmap_writable in *. repeat rewrite V293_prefix_fixture_outside by discriminate. exact W.
      * intros x v I. destruct (NewLoc x v I) as (c & Bind & Cr & Cg & Lval).
        cbn [V293_rekey_new_bindings In] in I.
        destruct I as [E|[E|[E|F]]]; try contradiction; inversion E; subst x v.
        all: unfold V293_read_ready_fixture_le,V293_ready_fragment_fixture_le in Bind;
          repeat rewrite map_get_set' in Bind by discriminate; rewrite map_get_set in Bind;
          inversion Bind; subst c.
        all: eexists; split.
        all: try (unfold V293_prefix_fixture_le,V293_read_ready_fixture_le,V293_ready_fragment_fixture_le;
          repeat rewrite map_get_set' by discriminate; rewrite map_get_set; reflexivity).
        all: split; [exact Cr | ]; split; [exact Cg | ]; rewrite RF by discriminate; exact Lval.
Qed.

Definition V293_prefix_observes (live flag : bool) final_lo final_hi final_group old_slot : Prop :=
  forall P ks, exists M1 M2,
  let M := V293_prefix_fixture_mem live in
  let Mr := V293_tcb_read_memory M2 32%positive 36%positive 34%positive 1 2 1 in
  let Mf := V293_ready_branch_memory Mr 30%positive 31%positive 16 (if live then 1 else 0) 8 6 in
  store (Tptr V293_tcb_type) M (50%positive,32%Z) Vnull = Some M1 /\
  store (Tptr V293_tcb_type) M1 (50%positive,24%Z) (Vptr (41%positive,Int.repr 8)) = Some M2 /\
  cstepstar P (curs (V293_task_prio_prefix 500%Z 501%Z 502%Z 400%Z
    300%Z 301%Z 302%Z 303%Z 304%Z 305%Z 306%Z 307%Z),(kenil,ks))
    (V293_prefix_fixture_ge,V293_prefix_fixture_le,M)
    (curs (sskip None),(kenil,ks)) (V293_prefix_fixture_ge,V293_prefix_fixture_le,Mf) /\
  evalval (V293_task_prio_ready_test 300%Z 302%Z 304%Z)
    (V293_prefix_fixture_ge,V293_prefix_fixture_le,Mr) =
    Some (Vint32 (if flag then Int.one else Int.zero)) /\
  V293_rekey_bitmap_loads Mf 30%positive 31%positive final_lo final_hi final_group /\
  V293_table_loads V293_tcb_type Mf 50%positive
    (update_nth_val 6 (update_nth_val 8 V293_prefix_fixture_entries Vnull) (Vptr (41%positive,Int.repr 8))) /\
  load (Tptr V293_tcb_type) Mf (50%positive,32%Z) = Some old_slot /\
  load (Tptr V293_tcb_type) Mf (50%positive,24%Z) = Some (Vptr (41%positive,Int.repr 8)).

Local Ltac prefix_fixture_bind :=
  unfold V293_prefix_fixture_ge,V293_prefix_fixture_le,V293_ready_fragment_fixture_ge,
    V293_read_ready_fixture_le,V293_ready_fragment_fixture_le;
  repeat first [rewrite map_get_set | rewrite map_get_set' by discriminate | rewrite map_emp_get].

Theorem V293_prefix_execution_witness : forall live,
  V293_prefix_observes live live (if live then 80 else 16) 0 1 Vnull.
Proof.
  intros live P ks.
  destruct (V293_prefix_fixture_table_entry live) as [View [Wo Wn]].
  destruct (V293_prefix_fixture_body_entry live)
    as [Hptr [Fields [Wy [Wby [Wx [Loads [W NewLoc]]]]]]].
  destruct (V293_task_prio_prefix_execution P ks V293_prefix_fixture_ge V293_prefix_fixture_le
    (V293_prefix_fixture_mem live) 500%Z 501%Z 502%Z 400%Z
    300%Z 301%Z 302%Z 303%Z 304%Z 305%Z 306%Z 307%Z
    50%positive 51%positive 52%positive 40%positive 41%positive
    32%positive 36%positive 34%positive 8%Z 30%positive 31%positive 16
    (if live then 1 else 0) 8 6 V293_prefix_fixture_entries)
    as (M1 & M2 & S1 & S2 & Exec & Test & FinalLoads & FinalView & OldSlot & NewSlot & _).
  all: try assumption; try discriminate; try (prefix_fixture_bind; reflexivity);
    try (change (0 <= 8)%Z; lia); try (change (8+55 <= 4294967295)%Z; lia);
    try (change (8<13); lia); try (change (6<13); lia); try (change (16<256); lia);
    try (destruct live; lia); try (change (length V293_prefix_fixture_entries = 13); reflexivity).
  - unfold V293_prefix_fixture_mem. rewrite V293_put_byte_other_load by discriminate.
    apply V293_put_byte_load. lia.
  - unfold V293_prefix_fixture_mem. apply V293_put_byte_load. lia.
  - intros x v c I Bind. cbn [V293_rekey_new_bindings In] in I.
    destruct I as [E|[E|[E|F]]]; try contradiction; inversion E; subst x v;
      unfold V293_prefix_fixture_le,V293_read_ready_fixture_le,V293_ready_fragment_fixture_le in Bind;
      repeat rewrite map_get_set' in Bind by discriminate; rewrite map_get_set in Bind;
      inversion Bind; subst c; repeat split; discriminate.
  - exists M1. exists M2. split; [exact S1 | ]. split; [exact S2 | ]. split; [exact Exec | ].
    split; [destruct live; exact Test | ]. split; [destruct live; exact FinalLoads | ].
    split; [exact FinalView | ]. auto.
Qed.

Theorem V293_prefix_physical_controls :
  V293_prefix_observes true true 80 0 1 Vnull /\
  V293_prefix_observes false false 16 0 1 Vnull.
Proof.
  split; [exact (V293_prefix_execution_witness true) | exact (V293_prefix_execution_witness false)].
Qed.

Require Import CertiOS.framework.proof.auxdef.

Definition V293_prefix_fixture_tasks (live : bool) : TcbMod.map :=
  set (sig (60%positive,Int.zero) (Int.repr 4,rdy,Vnull))
    (41%positive,Int.repr 8)
    (Int.repr 8,(if live then rdy else wait os_stat_time Int.one),Vnull).

Theorem V293_prefix_fixture_relations : forall live,
  V293_priority_table V293_prefix_fixture_entries (V293_prefix_fixture_tasks live) /\
  V293_bitmap_tasks 16 (if live then 1 else 0) (V293_prefix_fixture_tasks live) /\
  get (V293_prefix_fixture_tasks live) (41%positive,Int.repr 8) =
    Some (Int.repr 8,(if live then rdy else wait os_stat_time Int.one),Vnull) /\
  nth 6 V293_prefix_fixture_entries Vnull = Vnull.
Proof.
  intro live.
  assert (Moving : get (V293_prefix_fixture_tasks live) (41%positive,Int.repr 8) =
    Some (Int.repr 8,(if live then rdy else wait os_stat_time Int.one),Vnull)).
  { unfold V293_prefix_fixture_tasks. apply map_get_set. }
  assert (Other : get (V293_prefix_fixture_tasks live) (60%positive,Int.zero) =
    Some (Int.repr 4,rdy,Vnull)).
  { unfold V293_prefix_fixture_tasks. rewrite map_get_set' by discriminate. apply map_get_sig. }
  assert (Only : forall t p st m, get (V293_prefix_fixture_tasks live) t = Some (p,st,m) ->
    (t = (41%positive,Int.repr 8) /\ p = Int.repr 8 /\
      st = (if live then rdy else wait os_stat_time Int.one) /\ m = Vnull) \/
    (t = (60%positive,Int.zero) /\ p = Int.repr 4 /\ st = rdy /\ m = Vnull)).
  { intros t p st m T. unfold V293_prefix_fixture_tasks in T.
    destruct (tid_eq_dec (41%positive,Int.repr 8) t) as [E|E].
    - subst t. rewrite map_get_set in T. inversion T. left. auto.
    - rewrite map_get_set' in T by exact E.
      destruct (tid_eq_dec (60%positive,Int.zero) t) as [F|F].
      + subst t. rewrite map_get_sig in T. inversion T. right. auto.
      + rewrite map_get_sig' in T by exact F. discriminate. }
  split.
  - split; [reflexivity | ]. intros t p st m T.
    destruct (Only t p st m T) as [[Et [Ep _]]|[Et [Ep _]]]; subst t p.
    + exists 8. split; [lia | ]. split; reflexivity.
    + exists 4. split; [lia | ]. split; reflexivity.
  - split.
    + intros p R. split.
      * intro Bit. assert (Where : p = 4 \/ (p = 8 /\ live = true)).
        { destruct live; do 13 (destruct p as [ | p]; [vm_compute in Bit; intuition lia | ]); lia. }
        destruct Where as [E|[E Mode]]; subst p.
        -- exists (60%positive,Int.zero). exists Vnull. exact Other.
        -- subst live. exists (41%positive,Int.repr 8). exists Vnull. exact Moving.
      * intros (t & m & T). destruct (Only t (Int.repr (Z.of_nat p)) rdy m T)
          as [[_ [Ep [St _]]]|[_ [Ep _]]].
        -- assert (E : p = 8) by (apply V293_priority_repr_injective; [exact R | lia | exact Ep]).
           subst p. destruct live; [vm_compute; intuition lia | discriminate St].
        -- assert (E : p = 4) by (apply V293_priority_repr_injective; [exact R | lia | exact Ep]).
           subst p. destruct live; vm_compute; intuition lia.
    + auto.
Qed.

(* The SAME concrete entry has all 13 physical slots, task/table/bitmap
   relations and a real full-prefix execution, including the false path.
   This still does not allocate the rest of the TCB or prove reachability. *)
Theorem V293_prefix_combined_witness : forall live,
  let M := V293_prefix_fixture_mem live in
  let tasks := V293_prefix_fixture_tasks live in
  V293_table_loads V293_tcb_type M 50%positive V293_prefix_fixture_entries /\
  V293_priority_table V293_prefix_fixture_entries tasks /\
  V293_bitmap_tasks 16 (if live then 1 else 0) tasks /\
  get tasks (41%positive,Int.repr 8) =
    Some (Int.repr 8,(if live then rdy else wait os_stat_time Int.one),Vnull) /\
  nth 6 V293_prefix_fixture_entries Vnull = Vnull /\
  V293_prefix_observes live live (if live then 80 else 16) 0 1 Vnull.
Proof.
  intro live. cbn zeta.
  destruct (V293_prefix_fixture_relations live) as [Table [Bitmap [Moving Empty]]].
  split; [exact (proj1 (V293_prefix_fixture_table_entry live)) | ].
  split; [exact Table | ]. split; [exact Bitmap | ]. split; [exact Moving | ].
  split; [exact Empty | ]. exact (V293_prefix_execution_witness live).
Qed.

Theorem V293_event_source_layout :
  typelen V293_event_type = 16 /\
  field_offset 4%Z V293_event_fields = Some (Int.repr 10) /\
  field_offset 5%Z V293_event_fields = Some (Int.repr 11) /\
  ftype 9%Z V293_tcb_fields = Some (Tcom_ptr 411%Z) /\
  field_offset 9%Z V293_tcb_fields = Some (Int.repr 28).
Proof. repeat split; reflexivity. Qed.

Lemma V293_tcb_event_field_eval : forall ge le M ptcb bc bt base value,
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  load (Tptr V293_tcb_type) M (bc,0%Z) = Some (Vptr (bt,Int.repr base)) ->
  (0 <= base)%Z -> (base+28 <= Int.max_unsigned)%Z ->
  load (Tcom_ptr 411%Z) M (bt,(base+28)%Z) = Some value ->
  evaltype (efield (ederef (evar ptcb)) 9%Z) (ge,le,M) = Some (Tcom_ptr 411%Z) /\
  evalval (efield (ederef (evar ptcb)) 9%Z) (ge,le,M) = Some value.
Proof.
  intros ge le M ptcb bc bt base value Bptr Hptr B R Read.
  assert (Tp : evaltype (ederef (evar ptcb)) (ge,le,M) = Some V293_tcb_type).
  { cbn [evaltype get_lenv get_genv get_mem]. rewrite Bptr. reflexivity. }
  assert (T : evaltype (efield (ederef (evar ptcb)) 9%Z) (ge,le,M) = Some (Tcom_ptr 411%Z)).
  { cbn [evaltype]. rewrite Bptr. reflexivity. }
  split; [exact T | ]. cbn [evalval]. rewrite T.
  cbn [evaladdr evalval evaltype get_lenv get_genv get_mem]. rewrite Bptr.
  cbn beta iota. rewrite Hptr. unfold getoff. rewrite Tp.
  cbn [V293_tcb_type field_offset typelen]. cbn [addrval_to_addr].
  rewrite Int.repr_unsigned. unfold Int.add.
  rewrite (Int.unsigned_repr base) by lia.
  change (load (Tcom_ptr 411%Z) M (bt,Int.unsigned (Int.repr (base+28))) = Some value).
  rewrite Int.unsigned_repr by lia. exact Read.
Qed.

(* Both null and non-null cases of the actual condition, without executing
   or postulating the non-null body. A pointer value need not be dereferenced. *)
Theorem V293_event_test_eval : forall ge le M pevent be value,
  get le pevent = Some (be,Tptr V293_event_type) ->
  load (Tptr V293_event_type) M (be,0%Z) = Some value ->
  (value = Vnull \/ exists a, value = Vptr a) ->
  evalval (V293_task_prio_event_test pevent) (ge,le,M) =
    Some (Vint32 (if match value with Vnull => false | _ => true end
      then Int.one else Int.zero)).
Proof.
  intros ge le M pevent be value Bind Read [Null | [a PointerValue]]; subst value;
    cbn [V293_task_prio_event_test evalval evaltype get_lenv get_genv get_mem];
    rewrite Bind; cbn beta iota; rewrite Read;
    cbn [cast_eval bop_type bop_eval val_eq uop_eval notint uop_type is_int_type]; try reflexivity.
  destruct a; reflexivity.
Qed.

(* Stable interface for the real pointer assignment. Store success and the
   subsequent condition are outputs, never premises. *)
Theorem V293_task_prio_event_read_execution :
  forall P ks ge le M ptcb pevent bc bt be base value,
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  get le pevent = Some (be,Tptr V293_event_type) ->
  load (Tptr V293_tcb_type) M (bc,0%Z) = Some (Vptr (bt,Int.repr base)) ->
  (0 <= base)%Z -> (base+28 <= Int.max_unsigned)%Z ->
  load (Tcom_ptr 411%Z) M (bt,(base+28)%Z) = Some value ->
  (value = Vnull \/ exists a, value = Vptr a) ->
  V293_bytes_writable M be 0%Z 4 ->
  exists Me,
  store (Tptr V293_event_type) M (be,0%Z) value = Some Me /\
  cstepstar P (curs (V293_task_prio_event_read ptcb pevent),(kenil,ks))
    (ge,le,M) (curs (sskip None),(kenil,ks)) (ge,le,Me) /\
  load (Tptr V293_event_type) Me (be,0%Z) = Some value /\
  evalval (V293_task_prio_event_test pevent) (ge,le,Me) =
    Some (Vint32 (if match value with Vnull => false | _ => true end
      then Int.one else Int.zero)) /\
  (forall c i, c <> be -> get Me (c,i) = get M (c,i)).
Proof.
  intros P ks ge le M ptcb pevent bc bt be base value Bp Be Lp B R L E W.
  destruct (V293_tcb_event_field_eval ge le M ptcb bc bt base value Bp Lp B R L)
    as [Ft Fv].
  destruct (V293_storebytes_exists (encode_val (Tptr V293_event_type) value) M be 0%Z)
    as [Me Store]; [rewrite encode_val_length; exact W | ].
  assert (Valid : rule_type_val_match (Tptr V293_event_type) value = true).
  { destruct E as [-> | [a ->]]; reflexivity. }
  assert (Read : load (Tptr V293_event_type) Me (be,0%Z) = Some value).
  { eapply V293_store_readback; eassumption. }
  exists Me. split; [exact Store | ]. split.
  - unfold V293_task_prio_event_read.
    eapply V293_assign_pointer_execution with (tr := Tcom_ptr 411%Z)
      (tp := V293_event_type) (b := be) (off := 0%Z); try eassumption.
    + cbn [evaltype]. rewrite Be. reflexivity.
    + apply eq_vcomptr. split; [left; eauto | left; eauto].
    + cbn [evaladdr get_lenv get_genv]. rewrite Be. reflexivity.
    + change (0 <= 0 <= 4294967295)%Z. lia.
  - split; [exact Read | ]. split.
    + eapply V293_event_test_eval; eassumption.
    + intros c i N. eapply V293_storebytes_outside; [exact Store | left; exact N].
Qed.

Theorem V293_task_prio_event_null_execution :
  forall P ks ge le M ptcb pevent yo yn xo xn byo byn bc bt be base,
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  get le pevent = Some (be,Tptr V293_event_type) ->
  load (Tptr V293_tcb_type) M (bc,0%Z) = Some (Vptr (bt,Int.repr base)) ->
  (0 <= base)%Z -> (base+28 <= Int.max_unsigned)%Z ->
  load (Tcom_ptr 411%Z) M (bt,(base+28)%Z) = Some Vnull ->
  V293_bytes_writable M be 0%Z 4 ->
  exists Me,
  store (Tptr V293_event_type) M (be,0%Z) Vnull = Some Me /\
  cstepstar P (curs (V293_task_prio_event ptcb pevent yo yn xo xn byo byn),(kenil,ks))
    (ge,le,M) (curs (sskip None),(kenil,ks)) (ge,le,Me) /\
  load (Tptr V293_event_type) Me (be,0%Z) = Some Vnull /\
  (forall c i, c <> be -> get Me (c,i) = get M (c,i)).
Proof.
  intros P ks ge le M ptcb pevent yo yn xo xn byo byn bc bt be base Bp Be Lp B R L W.
  destruct (V293_task_prio_event_read_execution P ks ge le M ptcb pevent bc bt be base Vnull
    Bp Be Lp B R L ltac:(left; reflexivity) W) as (Me & Store & Exec & Read & Test & Frame).
  exists Me. split; [exact Store | ]. split.
  - unfold V293_task_prio_event. eapply V293_rekey_sequence_execution.
    + intro tail. destruct (V293_task_prio_event_read_execution P tail ge le M ptcb pevent bc bt be base Vnull
        Bp Be Lp B R L ltac:(left; reflexivity) W) as (Mt & St & Et & _).
      rewrite Store in St. inversion St; subst Mt. exact Et.
    + eapply V293_rekey_if_execution with (flag := false); try exact Test; try reflexivity.
      intros Impossible. discriminate.
  - split; assumption.
Qed.

(* Continuous source 119-143, null event path only. *)
Theorem V293_task_prio_prefix_event_null_execution :
  forall P ks ge le M table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi old new entries pevent be,
  old < 13 -> new < 13 -> old <> new -> lo < 256 -> hi < 256 -> br <> bg ->
  (0 <= base)%Z -> (base+55 <= Int.max_unsigned)%Z ->
  get le table = None -> get ge table = Some (b,Tarray (Tptr V293_tcb_type) 13) ->
  get le oldprio = Some (bo,Tint8) -> get le newprio = Some (bn,Tint8) ->
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  b <> bo -> b <> bn -> b <> bc -> b <> bt ->
  b <> dy -> b <> dby -> b <> dx -> b <> br -> b <> bg ->
  load Tint8 M (bo,0%Z) = Some (V293_byteval old) ->
  load Tint8 M (bn,0%Z) = Some (V293_byteval new) ->
  load (Tptr V293_tcb_type) M (bc,0%Z) = Some (Vptr (bt,Int.repr base)) ->
  V293_bytes_writable M b (4*Z.of_nat old)%Z 4 ->
  V293_bytes_writable M b (4*Z.of_nat new)%Z 4 ->
  length entries = 13 -> V293_table_loads V293_tcb_type M b entries ->
  get le yo = Some (dy,Tint8) -> get le byo = Some (dby,Tint8) -> get le xo = Some (dx,Tint8) ->
  get le rows = None -> get ge rows = Some (br,Tarray Tint8 2) ->
  get le group = None -> get ge group = Some (bg,Tint8) ->
  dy <> dby -> dy <> dx -> dby <> dx ->
  (forall c, c = dy \/ c = dby \/ c = dx -> c <> bc /\ c <> bt /\ c <> br /\ c <> bg) ->
  V293_tcb_old_loads M bt base (V293_prio_row old)
    (2 ^ V293_prio_row old) (2 ^ V293_prio_bit old) ->
  (exists v, get M (dy,0%Z) = Some (true,v)) ->
  (exists v, get M (dby,0%Z) = Some (true,v)) ->
  (exists v, get M (dx,0%Z) = Some (true,v)) ->
  V293_rekey_bitmap_loads M br bg lo hi (V293_ready_group lo hi) ->
  V293_rekey_bitmap_writable M br bg ->
  V293_rekey_locals ge le M br bg (V293_rekey_new_bindings yn xn byn new) ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> b /\ c <> dy /\ c <> dby /\ c <> dx) ->
  get le pevent = Some (be,Tptr V293_event_type) ->
  V293_bytes_writable M be 0%Z 4 ->
  load (Tcom_ptr 411%Z) M (bt,(base+28)%Z) = Some Vnull ->
  bc <> br -> bc <> bg -> bt <> br -> bt <> bg ->
  be <> b -> be <> dy -> be <> dby -> be <> dx -> be <> br -> be <> bg ->
  exists M1 M2 Me,

  let Mr := V293_tcb_read_memory M2 dy dby dx (V293_prio_row old)
    (2 ^ V293_prio_row old) (2 ^ V293_prio_bit old) in
  let Mf := V293_ready_branch_memory Mr br bg lo hi old new in
  let fr := V293_ready_branch_rows lo hi old new in
  store (Tptr V293_tcb_type) M (b,(4*Z.of_nat old)%Z) Vnull = Some M1 /\
  store (Tptr V293_tcb_type) M1 (b,(4*Z.of_nat new)%Z) (Vptr (bt,Int.repr base)) = Some M2 /\
  store (Tptr V293_event_type) Mf (be,0%Z) Vnull = Some Me /\
  load (Tptr V293_event_type) Me (be,0%Z) = Some Vnull /\
  cstepstar P (curs (V293_task_prio_prefix_event table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent),
    (kenil,ks)) (ge,le,M) (curs (sskip None),(kenil,ks)) (ge,le,Me) /\
  evalval (V293_task_prio_ready_test rows yo xo) (ge,le,Mr) =
    Some (Vint32 (if V293_ready_test_flag lo hi old then Int.one else Int.zero)) /\
  V293_rekey_bitmap_loads Me br bg (fst fr) (snd fr) (V293_ready_group (fst fr) (snd fr)) /\
  V293_table_loads V293_tcb_type Me b
    (update_nth_val new (update_nth_val old entries Vnull) (Vptr (bt,Int.repr base))) /\
  load (Tptr V293_tcb_type) Me (b,(4*Z.of_nat old)%Z) = Some Vnull /\
  load (Tptr V293_tcb_type) Me (b,(4*Z.of_nat new)%Z) = Some (Vptr (bt,Int.repr base)) /\
  V293_rekey_bitmap_writable Me br bg /\
  V293_rekey_locals ge le Mf br bg (V293_rekey_ready_bindings yo yn xo xn byo byn old new) /\
  (forall c i, c <> b -> c <> dy -> c <> dby -> c <> dx -> c <> br -> c <> bg -> c <> be ->
    get Me (c,i) = get M (c,i)).
Proof.
  intros P ks ge le M table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi old new entries pevent be
    O N ON L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg
    Lo Ln Lp Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields
    Wy Wby Wx Loads W NewLoc NewApart Be We Event Cr Cg Br Bg Eb Ey Eby Ex Er Eg.
  assert (Prefix : forall tail, exists M1 M2,
    store (Tptr V293_tcb_type) M (b,(4*Z.of_nat old)%Z) Vnull = Some M1 /\
    store (Tptr V293_tcb_type) M1 (b,(4*Z.of_nat new)%Z) (Vptr (bt,Int.repr base)) = Some M2 /\
    cstepstar P (curs (V293_task_prio_prefix table oldprio newprio ptcb rows group yo yn xo xn byo byn),
      (kenil,tail)) (ge,le,M) (curs (sskip None),(kenil,tail))
      (ge,le,V293_ready_branch_memory
        (V293_tcb_read_memory M2 dy dby dx (V293_prio_row old)
          (2 ^ V293_prio_row old) (2 ^ V293_prio_bit old)) br bg lo hi old new)).
  { intro tail.
    destruct (V293_task_prio_prefix_execution P tail ge le M table oldprio newprio ptcb rows group
      yo yn xo xn byo byn b bo bn bc bt dy dby dx base br bg lo hi old new entries
      O N ON L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg
      Lo Ln Lp Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields
      Wy Wby Wx Loads W NewLoc NewApart) as (M1 & M2 & S1 & S2 & E & _).
    exists M1. exists M2. auto. }
  destruct (V293_task_prio_prefix_execution P ks ge le M table oldprio newprio ptcb rows group
    yo yn xo xn byo byn b bo bn bc bt dy dby dx base br bg lo hi old new entries
    O N ON L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg
    Lo Ln Lp Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields
    Wy Wby Wx Loads W NewLoc NewApart)
    as (M1 & M2 & S1 & S2 & Exec & Test & FinalLoads & FinalView & OldSlot & NewSlot & FinalW & FinalLoc & Frame).
  set (Mr := V293_tcb_read_memory M2 dy dby dx (V293_prio_row old)
    (2 ^ V293_prio_row old) (2 ^ V293_prio_bit old)) in *.
  set (Mf := V293_ready_branch_memory Mr br bg lo hi old new) in *.
  assert (PC : forall i, get Mf (bc,i) = get M (bc,i)).
  { intro i. apply Frame; try congruence;
      destruct (Apart dy ltac:(auto)) as [A _];
      destruct (Apart dby ltac:(auto)) as [A' _];
      destruct (Apart dx ltac:(auto)) as [A'' _]; congruence. }
  assert (TC : forall i, get Mf (bt,i) = get M (bt,i)).
  { intro i. apply Frame; try congruence;
      destruct (Apart dy ltac:(auto)) as [_ [A _]];
      destruct (Apart dby ltac:(auto)) as [_ [A' _]];
      destruct (Apart dx ltac:(auto)) as [_ [A'' _]]; congruence. }
  assert (EC : forall i, get Mf (be,i) = get M (be,i)) by (intro i; apply Frame; assumption).
  destruct (V293_task_prio_event_null_execution P ks ge le Mf ptcb pevent yo yn xo xn byo byn bc bt be base
    Bc Be ltac:(rewrite (V293_load_block_frame _ M Mf bc 0%Z PC); exact Lp)
    Base ltac:(lia) ltac:(rewrite (V293_load_block_frame _ M Mf bt (base+28)%Z TC); exact Event)
    ltac:(intros k K; rewrite EC; exact (We k K)))
    as (Me & Store & Suffix & Read & EF).
  assert (RF : forall tp c i, c <> be -> load tp Me (c,i) = load tp Mf (c,i)).
  { intros tp c i A. apply V293_load_block_frame. intro j. apply EF. exact A. }
  exists M1. exists M2. exists Me. cbn zeta. fold Mr Mf.
  split; [exact S1 | ]. split; [exact S2 | ]. split; [exact Store | ]. split; [exact Read | ]. split.
  - unfold V293_task_prio_prefix_event. eapply V293_rekey_sequence_execution; [ | exact Suffix].
    intro tail. destruct (Prefix tail) as (A & B & SA & SB & E).
    rewrite S1 in SA. inversion SA; subst A. rewrite S2 in SB. inversion SB; subst B. exact E.
  - split; [exact Test | ]. split.
    + unfold V293_rekey_bitmap_loads in *. repeat rewrite RF by congruence. exact FinalLoads.
    + split.
      * intros p R. rewrite RF by congruence. exact (FinalView p R).
      * split; [rewrite RF by congruence; exact OldSlot | ].
        split; [rewrite RF by congruence; exact NewSlot | ]. split.
        -- unfold V293_rekey_bitmap_writable in *. repeat rewrite EF by congruence. exact FinalW.
        -- split.
           ++ exact FinalLoc.
           ++ intros c i Cb Cy Cby Cx Cr' Cg' Ce. rewrite EF by exact Ce.
              apply Frame; assumption.
Qed.

Lemma V293_fixture_encoded_load : forall tp M b i v,
  rule_type_val_match tp v = true ->
  load tp (V293_fixture_put_bytes M b i (encode_val tp v)) (b,i) = Some v.
Proof.
  intros tp M b i v Match. destruct tp; try (destruct v; discriminate);
    unfold load,loadm;
    rewrite <- (encode_val_length _ v); rewrite V293_loadbytes_get;
    try (rewrite type_val_mach_encode_val_decode_val by exact Match; reflexivity);
    intros k K; exists true; apply V293_fixture_bytes_nth; exact K.
Qed.

Definition V293_event_fixture_le : env :=
  set V293_prefix_fixture_le 600%Z (70%positive,Tptr V293_event_type).
Definition V293_event_fixture_mem live value : mem :=
  V293_fixture_put_bytes
    (V293_fixture_put_bytes (V293_prefix_fixture_mem live) 41%positive 36%Z
      (encode_val (Tcom_ptr 411%Z) value))
    70%positive 0%Z (encode_val (Tptr V293_event_type) (Vptr (71%positive,Int.repr 3))).

Lemma V293_event_fixture_outside : forall live value c i,
  c <> 70%positive -> (c <> 41%positive \/ (i < 36)%Z \/ (40 <= i)%Z) ->
  get (V293_event_fixture_mem live value) (c,i) = get (V293_prefix_fixture_mem live) (c,i).
Proof.
  intros live value c i C R. unfold V293_event_fixture_mem.
  rewrite V293_fixture_bytes_outside by (left; exact C).
  rewrite V293_fixture_bytes_outside; [reflexivity | ].
  rewrite encode_val_length. exact R.
Qed.

Theorem V293_event_fixture_entry : forall live value,
  (value = Vnull \/ exists a, value = Vptr a) ->
  let M := V293_event_fixture_mem live value in
  load (Tptr V293_tcb_type) M (40%positive,0%Z) = Some (Vptr (41%positive,Int.repr 8)) /\
  load (Tcom_ptr 411%Z) M (41%positive,36%Z) = Some value /\
  V293_bytes_writable M 70%positive 0%Z 4 /\
  V293_tcb_old_loads M 41%positive 8%Z 1 2 1 /\
  V293_table_loads V293_tcb_type M 50%positive V293_prefix_fixture_entries /\
  V293_bytes_writable M 50%positive 32%Z 4 /\
  V293_bytes_writable M 50%positive 24%Z 4 /\
  (exists v, get M (32%positive,0%Z) = Some (true,v)) /\
  (exists v, get M (36%positive,0%Z) = Some (true,v)) /\
  (exists v, get M (34%positive,0%Z) = Some (true,v)) /\
  V293_rekey_bitmap_loads M 30%positive 31%positive 16 (if live then 1 else 0)
    (V293_ready_group 16 (if live then 1 else 0)) /\
  V293_rekey_bitmap_writable M 30%positive 31%positive /\
  V293_rekey_locals V293_prefix_fixture_ge V293_event_fixture_le M
    30%positive 31%positive (V293_rekey_new_bindings 303%Z 305%Z 307%Z 6).
Proof.
  intros live value Valid. cbn zeta.
  destruct (V293_prefix_fixture_table_entry live) as [View [Wo Wn]].
  destruct (V293_prefix_fixture_body_entry live)
    as [Lp [Fields [Wy [Wby [Wx [Loads [W NewLoc]]]]]]].
  assert (RF : forall tp c i, c <> 70%positive -> c <> 41%positive ->
    load tp (V293_event_fixture_mem live value) (c,i) = load tp (V293_prefix_fixture_mem live) (c,i)).
  { intros tp c i A B. apply V293_load_block_frame. intro j.
    apply V293_event_fixture_outside; [exact A | left; exact B]. }
  split; [rewrite RF by discriminate; exact Lp | ]. split.
  - unfold V293_event_fixture_mem.
    rewrite (V293_load_block_frame (Tcom_ptr 411%Z)
      (V293_fixture_put_bytes (V293_prefix_fixture_mem live) 41%positive 36%Z
        (encode_val (Tcom_ptr 411%Z) value)) _ 41%positive 36%Z).
    + apply V293_fixture_encoded_load. destruct Valid as [-> | [a ->]]; reflexivity.
    + intro j. apply V293_fixture_bytes_outside. left. discriminate.
  - split.
    + intros k K. unfold V293_event_fixture_mem.
      change (exists v, get (V293_fixture_put_bytes
        (V293_fixture_put_bytes (V293_prefix_fixture_mem live) 41%positive 36%Z (encode_val (Tcom_ptr 411%Z) value)) 70%positive 0%Z
        (encode_val (Tptr V293_event_type) (Vptr (71%positive,Int.repr 3))))
        (70%positive,(0+Z.of_nat k)%Z) = Some (true,v)).
      exists (nth k (encode_val (Tptr V293_event_type) (Vptr (71%positive,Int.repr 3))) Undef).
      apply V293_fixture_bytes_nth. rewrite encode_val_length. exact K.
    + split.
      * unfold V293_tcb_old_loads in *. destruct Fields as [Fy [Fby Fx]].
        cbn [load loadm typelen loadbytes] in Fy,Fby,Fx |- *.
        repeat rewrite V293_event_fixture_outside by (try discriminate; right; right; lia).
        auto.
      * split.
        -- intros p R. rewrite RF by discriminate. exact (View p R).
        -- split.
           ++ intros k K. rewrite V293_event_fixture_outside by (try discriminate; left; discriminate).
              exact (Wo k K).
           ++ split.
              ** intros k K. rewrite V293_event_fixture_outside by (try discriminate; left; discriminate).
                 exact (Wn k K).
              ** split; [rewrite V293_event_fixture_outside by (try discriminate; left; discriminate); exact Wy | ].
                 split; [rewrite V293_event_fixture_outside by (try discriminate; left; discriminate); exact Wby | ].
                 split; [rewrite V293_event_fixture_outside by (try discriminate; left; discriminate); exact Wx | ]. split.
                 --- unfold V293_rekey_bitmap_loads in *. repeat rewrite RF by discriminate. exact Loads.
                 --- split.
                     +++ unfold V293_rekey_bitmap_writable in *.
                         repeat rewrite V293_event_fixture_outside by (try discriminate; left; discriminate). exact W.
                     +++ intros x v I. destruct (NewLoc x v I) as (c & Bind & A & B & Load).
                         cbn [V293_rekey_new_bindings In] in I.
                         destruct I as [E|[E|[E|F]]]; try contradiction; inversion E; subst x v;
                           unfold V293_prefix_fixture_le,V293_read_ready_fixture_le,V293_ready_fragment_fixture_le in Bind;
                           repeat rewrite map_get_set' in Bind by discriminate; rewrite map_get_set in Bind;
                           inversion Bind; subst c.
                         all: eexists; split.
                         all: try (unfold V293_event_fixture_le,V293_prefix_fixture_le,V293_read_ready_fixture_le,V293_ready_fragment_fixture_le;
                           repeat rewrite map_get_set' by discriminate; rewrite map_get_set; reflexivity).
                         all: split; [exact A | ]; split; [exact B | ]; rewrite RF by discriminate; exact Load.
Qed.

Local Ltac event_fixture_bind := unfold V293_event_fixture_le; prefix_fixture_bind.

Definition V293_event_read_observes live value (flag : bool) : Prop :=
  forall P ks, exists Me,
  cstepstar P (curs (V293_task_prio_event_read 400%Z 600%Z),(kenil,ks))
    (V293_prefix_fixture_ge,V293_event_fixture_le,V293_event_fixture_mem live value)
    (curs (sskip None),(kenil,ks)) (V293_prefix_fixture_ge,V293_event_fixture_le,Me) /\
  load (Tptr V293_event_type) Me (70%positive,0%Z) = Some value /\
  evalval (V293_task_prio_event_test 600%Z) (V293_prefix_fixture_ge,V293_event_fixture_le,Me) =
    Some (Vint32 (if flag then Int.one else Int.zero)).

Theorem V293_event_read_controls : forall live,
  V293_event_read_observes live Vnull false /\
  V293_event_read_observes live (Vptr (72%positive,Int.repr 5)) true.
Proof.
  intro live. split; intros P ks.
  - destruct (V293_event_fixture_entry live Vnull ltac:(left; reflexivity)) as (Lp & Event & W & _).
    destruct (V293_task_prio_event_read_execution P ks V293_prefix_fixture_ge V293_event_fixture_le
      (V293_event_fixture_mem live Vnull) 400%Z 600%Z 40%positive 41%positive 70%positive 8%Z Vnull
      ltac:(event_fixture_bind; reflexivity) ltac:(event_fixture_bind; reflexivity)
      Lp ltac:(lia) ltac:(change (8+28<=4294967295)%Z; lia) Event ltac:(left; reflexivity) W)
      as (Me & _ & Exec & Read & Test & _).
    exists Me. auto.
  - destruct (V293_event_fixture_entry live (Vptr (72%positive,Int.repr 5)) ltac:(right; eauto))
      as (Lp & Event & W & _).
    destruct (V293_task_prio_event_read_execution P ks V293_prefix_fixture_ge V293_event_fixture_le
      (V293_event_fixture_mem live (Vptr (72%positive,Int.repr 5))) 400%Z 600%Z
      40%positive 41%positive 70%positive 8%Z (Vptr (72%positive,Int.repr 5))
      ltac:(event_fixture_bind; reflexivity) ltac:(event_fixture_bind; reflexivity)
      Lp ltac:(lia) ltac:(change (8+28<=4294967295)%Z; lia) Event ltac:(right; eauto) W)
      as (Me & _ & Exec & Read & Test & _).
    exists Me. auto.
Qed.

Definition V293_prefix_event_observes live final_lo event_value : Prop :=
  forall P ks, exists Me,
  cstepstar P (curs (V293_task_prio_prefix_event 500%Z 501%Z 502%Z 400%Z
    300%Z 301%Z 302%Z 303%Z 304%Z 305%Z 306%Z 307%Z 600%Z),(kenil,ks))
    (V293_prefix_fixture_ge,V293_event_fixture_le,V293_event_fixture_mem live Vnull)
    (curs (sskip None),(kenil,ks)) (V293_prefix_fixture_ge,V293_event_fixture_le,Me) /\
  load (Tptr V293_event_type) Me (70%positive,0%Z) = Some event_value /\
  V293_rekey_bitmap_loads Me 30%positive 31%positive final_lo 0 1 /\
  V293_table_loads V293_tcb_type Me 50%positive
    (update_nth_val 6 (update_nth_val 8 V293_prefix_fixture_entries Vnull) (Vptr (41%positive,Int.repr 8))).

Theorem V293_prefix_event_execution_witness : forall live,
  V293_prefix_event_observes live (if live then 80 else 16) Vnull.
Proof.
  intros live P ks.
  destruct (V293_event_fixture_entry live Vnull ltac:(left; reflexivity))
    as (Lp & Event & We & Fields & View & Wo & Wn & Wy & Wby & Wx & Loads & W & NewLoc).
  destruct (V293_task_prio_prefix_event_null_execution P ks V293_prefix_fixture_ge V293_event_fixture_le
    (V293_event_fixture_mem live Vnull) 500%Z 501%Z 502%Z 400%Z
    300%Z 301%Z 302%Z 303%Z 304%Z 305%Z 306%Z 307%Z
    50%positive 51%positive 52%positive 40%positive 41%positive
    32%positive 36%positive 34%positive 8%Z 30%positive 31%positive 16
    (if live then 1 else 0) 8 6 V293_prefix_fixture_entries 600%Z 70%positive)
    as (M1 & M2 & Me & S1 & S2 & Store & Read & Exec & Test & FinalLoads & FinalView & Rest).
  all: try assumption; try discriminate; try (event_fixture_bind; reflexivity);
    try (change (0 <= 8)%Z; lia); try (change (8+55 <= 4294967295)%Z; lia);
    try (change (8<13); lia); try (change (6<13); lia); try (change (16<256); lia);
    try (destruct live; lia); try (change (length V293_prefix_fixture_entries = 13); reflexivity).
  - rewrite (V293_load_block_frame _ (V293_prefix_fixture_mem live)) by
      (intro j; apply V293_event_fixture_outside; [discriminate | left; discriminate]).
    unfold V293_prefix_fixture_mem. rewrite V293_put_byte_other_load by discriminate.
    apply V293_put_byte_load. lia.
  - rewrite (V293_load_block_frame _ (V293_prefix_fixture_mem live)) by
      (intro j; apply V293_event_fixture_outside; [discriminate | left; discriminate]).
    unfold V293_prefix_fixture_mem. apply V293_put_byte_load. lia.
  - intros x v c I Bind. cbn [V293_rekey_new_bindings In] in I.
    destruct I as [E|[E|[E|F]]]; try contradiction; inversion E; subst x v;
      unfold V293_event_fixture_le,V293_prefix_fixture_le,V293_read_ready_fixture_le,V293_ready_fragment_fixture_le in Bind;
      repeat rewrite map_get_set' in Bind by discriminate; rewrite map_get_set in Bind;
      inversion Bind; subst c; repeat split; discriminate.
  - exists Me. split; [exact Exec | ]. split; [exact Read | ].
    split; [destruct live; exact FinalLoads | exact FinalView].
Qed.

Theorem V293_prefix_event_controls :
  V293_prefix_event_observes true 80 Vnull /\
  V293_prefix_event_observes false 16 Vnull.
Proof.
  split; [exact (V293_prefix_event_execution_witness true) | exact (V293_prefix_event_execution_witness false)].
Qed.

(* Event bytes are fields of ONE object, not two global bitmap blocks. *)
Definition V293_event_bitmap_loads M be base lo hi group : Prop :=
  load Tint8 M (be,(base+11)%Z) = Some (V293_byteval lo) /\
  load Tint8 M (be,(base+12)%Z) = Some (V293_byteval hi) /\
  load Tint8 M (be,(base+10)%Z) = Some (V293_byteval group).
Definition V293_event_bitmap_writable M be base : Prop :=
  (exists v, get M (be,(base+11)%Z) = Some (true,v)) /\
  (exists v, get M (be,(base+12)%Z) = Some (true,v)) /\
  (exists v, get M (be,(base+10)%Z) = Some (true,v)).

Lemma V293_event_field_address : forall ge le M pevent bc be base id tp off,
  get le pevent = Some (bc,Tptr V293_event_type) ->
  load (Tptr V293_event_type) M (bc,0%Z) = Some (Vptr (be,Int.repr base)) ->
  ftype id V293_event_fields = Some tp ->
  field_offset id V293_event_fields = Some (Int.repr off) ->
  (0 <= base)%Z -> (0 <= off)%Z -> (base+off <= Int.max_unsigned)%Z ->
  evaltype (efield (ederef (evar pevent)) id) (ge,le,M) = Some tp /\
  evaladdr (efield (ederef (evar pevent)) id) (ge,le,M) =
    Some (Vptr (be,Int.repr (base+off))).
Proof.
  intros ge le M pevent bc be base id tp off Bind Hptr Ft Fo B O R.
  assert (Td : evaltype (ederef (evar pevent)) (ge,le,M) = Some V293_event_type).
  { cbn [evaltype get_lenv get_genv]. rewrite Bind. reflexivity. }
  split.
  - cbn [evaltype get_lenv get_genv]. rewrite Bind. exact Ft.
  - cbn [evaladdr evalval evaltype get_lenv get_genv get_mem]. rewrite Bind.
    cbn beta iota. rewrite Hptr. unfold getoff. rewrite Td. cbn [V293_event_type]. rewrite Fo.
    rewrite Int.repr_unsigned. unfold Int.add.
    rewrite !Int.unsigned_repr by lia. reflexivity.
Qed.

Lemma V293_event_field_value : forall ge le M pevent bc be base id tp off value,
  get le pevent = Some (bc,Tptr V293_event_type) ->
  load (Tptr V293_event_type) M (bc,0%Z) = Some (Vptr (be,Int.repr base)) ->
  ftype id V293_event_fields = Some tp ->
  field_offset id V293_event_fields = Some (Int.repr off) ->
  (0 <= base)%Z -> (0 <= off)%Z -> (base+off <= Int.max_unsigned)%Z ->
  load tp M (be,(base+off)%Z) = Some value ->
  evalval (efield (ederef (evar pevent)) id) (ge,le,M) = Some value.
Proof.
  intros ge le M pevent bc be base id tp off value Bind Hptr Ft Fo B O R Read.
  destruct (V293_event_field_address ge le M pevent bc be base id tp off Bind Hptr Ft Fo B O R)
    as [T A].
  assert (Td : evaltype (ederef (evar pevent)) (ge,le,M) = Some V293_event_type).
  { cbn [evaltype get_lenv get_genv]. rewrite Bind. reflexivity. }
  cbn [evalval]. rewrite T.
  cbn [evaladdr evalval evaltype get_lenv get_genv get_mem]. rewrite Bind.
  cbn beta iota. rewrite Hptr. unfold getoff. rewrite Td.
  cbn [V293_event_type]. rewrite Fo. cbn [addrval_to_addr].
  rewrite Int.repr_unsigned. unfold Int.add.
  rewrite (Int.unsigned_repr base) by lia.
  rewrite (Int.unsigned_repr off) by lia.
  rewrite Int.unsigned_repr by lia. exact Read.
Qed.

(* Array indexing at a nonzero field address; array remains the real expr. *)
Lemma V293_byte_array_offset_eval : forall ge le M array index be base y value,
  evaltype array (ge,le,M) = Some (Tarray Tint8 2) ->
  evalval array (ge,le,M) = Some (Vptr (be,Int.repr base)) ->
  evaltype index (ge,le,M) = Some Tint8 ->
  evalval index (ge,le,M) = Some (V293_byteval y) ->
  (0 <= base)%Z -> (base+Z.of_nat y <= Int.max_unsigned)%Z -> y < 2 ->
  load Tint8 M (be,(base+Z.of_nat y)%Z) = Some value ->
  evaltype (earrayelem array index) (ge,le,M) = Some Tint8 /\
  evaladdr (earrayelem array index) (ge,le,M) = Some (Vptr (be,Int.repr (base+Z.of_nat y))) /\
  evalval (earrayelem array index) (ge,le,M) = Some value.
Proof.
  intros ge le M array index be base y value Ta Va Ti Vi B R Y Read.
  assert (T : evaltype (earrayelem array index) (ge,le,M) = Some Tint8).
  { cbn [evaltype]. rewrite Ta,Ti. reflexivity. }
  assert (Sum : Int.add (Int.repr base) (Int.mul Int.one (Int.repr (Z.of_nat y))) =
    Int.repr (base+Z.of_nat y)).
  { rewrite (Int.mul_commut Int.one),Int.mul_one. unfold Int.add.
    rewrite !Int.unsigned_repr by lia. reflexivity. }
  split; [exact T | ]. split.
  - cbn [evaladdr]. rewrite Ta,Va,Vi. unfold V293_byteval.
    exact (f_equal (fun i => Some (Vptr (be,i))) Sum).
  - cbn [evalval]. rewrite T,Va,Vi. unfold V293_byteval. cbn [get_mem typelen].
    change (load Tint8 M (be,Int.unsigned (Int.add (Int.repr base)
      (Int.mul Int.one (Int.repr (Z.of_nat y))))) = Some value).
    rewrite Sum,Int.unsigned_repr by lia. exact Read.
Qed.

Lemma V293_event_row_eval : forall ge le M pevent index bc be base lo hi g y,
  get le pevent = Some (bc,Tptr V293_event_type) ->
  load (Tptr V293_event_type) M (bc,0%Z) = Some (Vptr (be,Int.repr base)) ->
  (0 <= base)%Z -> (base+12 <= Int.max_unsigned)%Z ->
  evaltype index (ge,le,M) = Some Tint8 ->
  evalval index (ge,le,M) = Some (V293_byteval y) -> y < 2 ->
  V293_event_bitmap_loads M be base lo hi g ->
  evaltype (earrayelem (efield (ederef (evar pevent)) 5%Z) index) (ge,le,M) = Some Tint8 /\
  evaladdr (earrayelem (efield (ederef (evar pevent)) 5%Z) index) (ge,le,M) =
    Some (Vptr (be,Int.repr (base+11+Z.of_nat y))) /\
  evalval (earrayelem (efield (ederef (evar pevent)) 5%Z) index) (ge,le,M) =
    Some (V293_byteval (V293_ready_row lo hi y)).
Proof.
  intros ge le M pevent index bc be base lo hi g y Bind Hptr B R Ti Vi Y Loads.
  destruct (V293_event_field_address ge le M pevent bc be base 5%Z (Tarray Tint8 2) 11%Z
    Bind Hptr eq_refl eq_refl B ltac:(lia) ltac:(lia)) as [Ta Aa].
  assert (Va : evalval (efield (ederef (evar pevent)) 5%Z) (ge,le,M) =
    Some (Vptr (be,Int.repr (base+11)))).
  { eapply V293_event_field_value with (tp := Tarray Tint8 2) (off := 11%Z);
      try eassumption; try reflexivity; try lia. }
  eapply V293_byte_array_offset_eval; try eassumption; try lia.
  destruct Loads as [L [H G]]. destruct y as [ | [ | y]]; try lia;
    cbn [V293_ready_row Nat.eqb Z.of_nat Pos.of_succ_nat];
    replace (base+11+0)%Z with (base+11)%Z by lia;
    replace (base+11+1)%Z with (base+12)%Z by lia; try assumption.
Qed.

Lemma V293_event_group_eval : forall ge le M pevent bc be base lo hi g,
  get le pevent = Some (bc,Tptr V293_event_type) ->
  load (Tptr V293_event_type) M (bc,0%Z) = Some (Vptr (be,Int.repr base)) ->
  (0 <= base)%Z -> (base+12 <= Int.max_unsigned)%Z ->
  V293_event_bitmap_loads M be base lo hi g ->
  evaltype (efield (ederef (evar pevent)) 4%Z) (ge,le,M) = Some Tint8 /\
  evaladdr (efield (ederef (evar pevent)) 4%Z) (ge,le,M) =
    Some (Vptr (be,Int.repr (base+10))) /\
  evalval (efield (ederef (evar pevent)) 4%Z) (ge,le,M) = Some (V293_byteval g).
Proof.
  intros ge le M pevent bc be base lo hi g Bind Hptr B R Loads.
  destruct (V293_event_field_address ge le M pevent bc be base 4%Z Tint8 10%Z
    Bind Hptr eq_refl eq_refl B ltac:(lia) ltac:(lia)) as [T A].
  split; [exact T | ]. split; [exact A | ].
  eapply V293_event_field_value with (tp := Tint8) (off := 10%Z);
    try eassumption; try reflexivity; try lia.
  exact (proj2 (proj2 Loads)).
Qed.

Lemma V293_event_row_loads_write : forall M be base lo hi g y value,
  y < 2 -> value < 256 -> V293_event_bitmap_loads M be base lo hi g ->
  V293_event_bitmap_loads (V293_put_byte M (be,(base+11+Z.of_nat y)%Z) value) be base
    (fst (V293_ready_replace_row lo hi y value))
    (snd (V293_ready_replace_row lo hi y value)) g.
Proof.
  intros M be base lo hi g y value Y V (L & H & G).
  destruct y as [ | [ | y]]; try lia; cbn [V293_ready_replace_row fst snd Z.of_nat Pos.of_succ_nat];
    replace (base+11+0)%Z with (base+11)%Z by lia;
    replace (base+11+1)%Z with (base+12)%Z by lia.
  - split; [apply V293_put_byte_load; exact V | ]. split;
      rewrite V293_put_byte_other_load; try assumption; intro E; inversion E; lia.
  - split; [rewrite V293_put_byte_other_load; [exact L | intro E; inversion E; lia] | ].
    split; [apply V293_put_byte_load; exact V | ].
    rewrite V293_put_byte_other_load; [exact G | intro E; inversion E; lia].
Qed.

Lemma V293_event_group_loads_write : forall M be base lo hi g value,
  value < 256 -> V293_event_bitmap_loads M be base lo hi g ->
  V293_event_bitmap_loads (V293_put_byte M (be,(base+10)%Z) value) be base lo hi value.
Proof.
  intros M be base lo hi g value V (L & H & G). split.
  - rewrite V293_put_byte_other_load; [exact L | intro E; inversion E; lia].
  - split.
    + rewrite V293_put_byte_other_load; [exact H | intro E; inversion E; lia].
    + apply V293_put_byte_load. exact V.
Qed.

Lemma V293_event_writable_write : forall M be base a n,
  V293_event_bitmap_writable M be base ->
  V293_event_bitmap_writable (V293_put_byte M a n) be base.
Proof.
  intros M be base a n (L & H & G). unfold V293_event_bitmap_writable.
  assert (W : forall other, (exists v, get M other = Some (true,v)) ->
    exists v, get (V293_put_byte M a n) other = Some (true,v)).
  { intros other [v V]. destruct (addr_eq_dec other a) as [E|N].
    - subst other. eexists. apply V293_put_byte_get_same.
    - exists v. rewrite V293_put_byte_other by exact N. exact V. }
  repeat split; apply W; assumption.
Qed.

Lemma V293_event_pointer_write : forall M pevent_block be a n,
  pevent_block <> be -> fst a = be ->
  load (Tptr V293_event_type) (V293_put_byte M a n) (pevent_block,0%Z) =
    load (Tptr V293_event_type) M (pevent_block,0%Z).
Proof.
  intros M bc be a n Apart A. apply V293_load_block_frame.
  intro i. apply V293_put_byte_other. intro E. apply (f_equal fst) in E. cbn in E. congruence.
Qed.

Lemma V293_event_row_execution :
  forall P ks ge le M pevent index mask be bc base lo hi g y bit clear bindings,
  lo < 256 -> hi < 256 -> y < 2 -> bit < 8 ->
  get le pevent = Some (bc,Tptr V293_event_type) ->
  load (Tptr V293_event_type) M (bc,0%Z) = Some (Vptr (be,Int.repr base)) ->
  (0 <= base)%Z -> (base+12 <= Int.max_unsigned)%Z ->
  V293_event_bitmap_loads M be base lo hi g -> V293_event_bitmap_writable M be base ->
  V293_rekey_locals ge le M be be bindings ->
  In (index,V293_byteval y) bindings -> In (mask,V293_mask_value bit) bindings ->
  let value := V293_rekey_rmw_value clear (V293_ready_row lo hi y) bit in
  let M' := V293_put_byte M (be,(base+11+Z.of_nat y)%Z) value in
  cstepstar P (curs (sassign (earrayelem (efield (ederef (evar pevent)) 5%Z) (evar index))
    (V293_rekey_rmw_expr clear (earrayelem (efield (ederef (evar pevent)) 5%Z) (evar index)) (evar mask))),
    (kenil,ks)) (ge,le,M) (curs (sskip None),(kenil,ks)) (ge,le,M') /\
  V293_event_bitmap_loads M' be base
    (fst (V293_ready_replace_row lo hi y value))
    (snd (V293_ready_replace_row lo hi y value)) g /\
  V293_event_bitmap_writable M' be base /\ V293_rekey_locals ge le M' be be bindings /\
  value < 256.
Proof.
  intros P ks ge le M pevent index mask be bc base lo hi g y bit clear bindings
    L H Y Bit Bind Hptr B R Loads W Loc Ii Im. cbn zeta.
  destruct (V293_rekey_local_eval ge le M be be bindings index _ Loc Ii) as [Ti Vi].
  destruct (V293_rekey_local_eval ge le M be be bindings mask _ Loc Im) as [Tm Vm].
  destruct (V293_event_row_eval ge le M pevent (evar index) bc be base lo hi g y
    Bind Hptr B R Ti Vi Y Loads) as [Tr [Ar Vr]].
  assert (Row : V293_ready_row lo hi y < 256)
    by (unfold V293_ready_row; destruct (y =? 0); assumption).
  assert (Writable : exists v, get M (be,(base+11+Z.of_nat y)%Z) = Some (true,v)).
  { destruct W as [W0 [W1 Wg]]. destruct y as [ | [ | y]]; try lia; cbn [Z.of_nat Pos.of_succ_nat];
      replace (base+11+0)%Z with (base+11)%Z by lia;
      replace (base+11+1)%Z with (base+12)%Z by lia; assumption. }
  destruct (V293_rekey_byte_rmw_execution P ks ge le M
    (earrayelem (efield (ederef (evar pevent)) 5%Z) (evar index)) (evar mask)
    be (base+11+Z.of_nat y)%Z (V293_ready_row lo hi y) bit clear Row Bit ltac:(lia)
    Tr Ar Vr Tm Vm Writable) as [Bound [Store [Exec [Read Frame]]]].
  split; [exact Exec | ]. split.
  - apply V293_event_row_loads_write; assumption.
  - split; [apply V293_event_writable_write; exact W | ]. split.
    + apply V293_rekey_locals_write; [exact Loc | left; reflexivity].
    + exact Bound.
Qed.

Lemma V293_event_group_execution :
  forall P ks ge le M pevent mask be bc base lo hi g bit clear bindings,
  g < 256 -> bit < 8 ->
  get le pevent = Some (bc,Tptr V293_event_type) ->
  load (Tptr V293_event_type) M (bc,0%Z) = Some (Vptr (be,Int.repr base)) ->
  (0 <= base)%Z -> (base+12 <= Int.max_unsigned)%Z ->
  V293_event_bitmap_loads M be base lo hi g -> V293_event_bitmap_writable M be base ->
  V293_rekey_locals ge le M be be bindings -> In (mask,V293_mask_value bit) bindings ->
  let value := V293_rekey_rmw_value clear g bit in
  let M' := V293_put_byte M (be,(base+10)%Z) value in
  cstepstar P (curs (sassign (efield (ederef (evar pevent)) 4%Z)
    (V293_rekey_rmw_expr clear (efield (ederef (evar pevent)) 4%Z) (evar mask))),
    (kenil,ks)) (ge,le,M) (curs (sskip None),(kenil,ks)) (ge,le,M') /\
  V293_event_bitmap_loads M' be base lo hi value /\ V293_event_bitmap_writable M' be base /\
  V293_rekey_locals ge le M' be be bindings /\ value < 256.
Proof.
  intros P ks ge le M pevent mask be bc base lo hi g bit clear bindings
    G Bit Bind Hptr B R Loads W Loc Im. cbn zeta.
  destruct (V293_rekey_local_eval ge le M be be bindings mask _ Loc Im) as [Tm Vm].
  destruct (V293_event_group_eval ge le M pevent bc be base lo hi g Bind Hptr B R Loads)
    as [Tg [Ag Vg]].
  destruct (V293_rekey_byte_rmw_execution P ks ge le M
    (efield (ederef (evar pevent)) 4%Z) (evar mask) be (base+10)%Z
    g bit clear G Bit ltac:(lia) Tg Ag Vg Tm Vm (proj2 (proj2 W)))
    as [Bound [Store [Exec [Read Frame]]]].
  split; [exact Exec | ]. split.
  - eapply V293_event_group_loads_write; eassumption.
  - split; [apply V293_event_writable_write; exact W | ]. split.
    + apply V293_rekey_locals_write; [exact Loc | left; reflexivity].
    + exact Bound.
Qed.

Definition V293_event_rekey_memory M be base lo hi old new :=
  let cleared := V293_ready_clear_rows lo hi old in
  let cv := V293_ready_row (fst cleared) (snd cleared) (V293_prio_row old) in
  let M1 := V293_put_byte M (be,(base+11+Z.of_nat (V293_prio_row old))%Z) cv in
  let M2 := if cv =? 0 then
    V293_put_byte M1 (be,(base+10)%Z) (V293_ready_clear_group lo hi old) else M1 in
  let M3 := V293_put_byte M2 (be,(base+10)%Z) (V293_ready_rekey_group lo hi old new) in
  let rows := V293_ready_rekey_rows lo hi old new in
  V293_put_byte M3 (be,(base+11+Z.of_nat (V293_prio_row new))%Z)
    (V293_ready_row (fst rows) (snd rows) (V293_prio_row new)).

(* Stable interface for the real field-based THEN; no global aliases,
   successful stores, intermediate evaluations or exit reads are premises. *)
Theorem V293_task_prio_event_then_execution :
  forall P ks ge le M pevent yo yn xo xn byo byn be bc base lo hi old new,
  old < 13 -> new < 13 -> lo < 256 -> hi < 256 -> bc <> be ->
  get le pevent = Some (bc,Tptr V293_event_type) ->
  load (Tptr V293_event_type) M (bc,0%Z) = Some (Vptr (be,Int.repr base)) ->
  (0 <= base)%Z -> (base+12 <= Int.max_unsigned)%Z ->
  V293_event_bitmap_loads M be base lo hi (V293_ready_group lo hi) ->
  V293_event_bitmap_writable M be base ->
  V293_rekey_locals ge le M be be (V293_rekey_ready_bindings yo yn xo xn byo byn old new) ->
  let M' := V293_event_rekey_memory M be base lo hi old new in
  let fr := V293_ready_rekey_rows lo hi old new in
  cstepstar P (curs (V293_task_prio_event_then pevent yo yn xo xn byo byn),(kenil,ks))
    (ge,le,M) (curs (sskip None),(kenil,ks)) (ge,le,M') /\
  V293_event_bitmap_loads M' be base (fst fr) (snd fr) (V293_ready_group (fst fr) (snd fr)) /\
  V293_event_bitmap_writable M' be base /\
  V293_rekey_locals ge le M' be be (V293_rekey_ready_bindings yo yn xo xn byo byn old new) /\
  load (Tptr V293_event_type) M' (bc,0%Z) = Some (Vptr (be,Int.repr base)) /\
  (forall c i, c <> be \/ (i < base+10)%Z \/ (base+12 < i)%Z -> get M' (c,i) = get M (c,i)).
Proof.
  intros P ks ge le M pevent yo yn xo xn byo byn be bc base lo hi old new
    O N L H Apart Bind Hptr Base Limit Loads W Loc. cbn zeta.
  pose (bindings := V293_rekey_ready_bindings yo yn xo xn byo byn old new).
  change (V293_rekey_locals ge le M be be bindings) in Loc.
  assert (Iyo : In (yo,V293_byteval (V293_prio_row old)) bindings)
    by (unfold bindings,V293_rekey_ready_bindings; simpl; auto 8).
  assert (Iyn : In (yn,V293_byteval (V293_prio_row new)) bindings)
    by (unfold bindings,V293_rekey_ready_bindings; simpl; auto 8).
  assert (Ixo : In (xo,V293_mask_value (V293_prio_bit old)) bindings)
    by (unfold bindings,V293_rekey_ready_bindings; simpl; auto 8).
  assert (Ixn : In (xn,V293_mask_value (V293_prio_bit new)) bindings)
    by (unfold bindings,V293_rekey_ready_bindings; simpl; auto 8).
  assert (Ibyo : In (byo,V293_mask_value (V293_prio_row old)) bindings)
    by (unfold bindings,V293_rekey_ready_bindings; simpl; auto 8).
  assert (Ibyn : In (byn,V293_mask_value (V293_prio_row new)) bindings)
    by (unfold bindings,V293_rekey_ready_bindings; simpl; auto 8).
  destruct (V293_prio_coordinates old O) as [Yo Xo].
  destruct (V293_prio_coordinates new N) as [Yn Xn].
  pose (cleared := V293_ready_clear_rows lo hi old).
  pose (cv := Nat.clearbit (V293_ready_row lo hi (V293_prio_row old)) (V293_prio_bit old)).
  pose (M1 := V293_put_byte M (be,(base+11+Z.of_nat (V293_prio_row old))%Z) cv).
  assert (EC : V293_ready_replace_row lo hi (V293_prio_row old) cv = cleared)
    by (apply V293_rekey_clear_row_value).
  assert (CV : V293_ready_row (fst cleared) (snd cleared) (V293_prio_row old) = cv)
    by (apply V293_rekey_clear_row_value).
  assert (Clear : forall tail,
    cstepstar P (curs (sassign (earrayelem (efield (ederef (evar pevent)) 5%Z) (evar yo))
      (V293_task_prio_clear_expr (earrayelem (efield (ederef (evar pevent)) 5%Z) (evar yo)) (evar xo))),
      (kenil,tail)) (ge,le,M) (curs (sskip None),(kenil,tail)) (ge,le,M1)).
  { intro tail. exact (proj1 (V293_event_row_execution P tail ge le M pevent yo xo
      be bc base lo hi (V293_ready_group lo hi) (V293_prio_row old) (V293_prio_bit old) true
      bindings L H Yo Xo Bind Hptr Base Limit Loads W Loc Iyo Ixo)). }
  destruct (V293_event_row_execution P ks ge le M pevent yo xo be bc base lo hi
    (V293_ready_group lo hi) (V293_prio_row old) (V293_prio_bit old) true bindings
    L H Yo Xo Bind Hptr Base Limit Loads W Loc Iyo Ixo) as [_ [Loads1 [W1 [Loc1 CBound]]]].
  change (V293_event_bitmap_loads M1 be base
    (fst (V293_ready_replace_row lo hi (V293_prio_row old) cv))
    (snd (V293_ready_replace_row lo hi (V293_prio_row old) cv)) (V293_ready_group lo hi)) in Loads1.
  rewrite EC in Loads1.
  change (V293_event_bitmap_writable M1 be base) in W1.
  change (V293_rekey_locals ge le M1 be be bindings) in Loc1.
  change (cv < 256) in CBound.
  assert (Ptr1 : load (Tptr V293_event_type) M1 (bc,0%Z) = Some (Vptr (be,Int.repr base))).
  { unfold M1. rewrite (V293_event_pointer_write M bc be (be,(base+11+Z.of_nat (V293_prio_row old))%Z) cv Apart eq_refl). exact Hptr. }
  assert (CL : fst cleared < 256 /\ snd cleared < 256).
  { unfold cleared,V293_ready_clear_rows. destruct (old <? 8) eqn:E;
      cbn [fst snd]; unfold cv,V293_ready_row,V293_prio_row,V293_prio_bit in CBound;
      rewrite E in CBound; cbn in CBound; split; assumption. }
  assert (GroupBound : V293_ready_group lo hi < 256).
  { unfold V293_ready_group. destruct (lo =? 0); destruct (hi =? 0); lia. }
  pose (gc := V293_ready_clear_group lo hi old).
  pose (M2 := if cv =? 0 then V293_put_byte M1 (be,(base+10)%Z) gc else M1).
  assert (GC : gc = if cv =? 0 then
    Nat.clearbit (V293_ready_group lo hi) (V293_prio_row old) else V293_ready_group lo hi).
  { unfold gc,V293_ready_clear_group,cleared,cv,V293_prio_row,V293_prio_bit,V293_ready_row,
      V293_ready_clear_rows. destruct (old <? 8); reflexivity. }
  assert (Cond : evalval (ebinop oeq
    (ecast (earrayelem (efield (ederef (evar pevent)) 5%Z) (evar yo)) Tint32)
    (econst32 Int.zero)) (ge,le,M1) = Some (Vint32 (if cv =? 0 then Int.one else Int.zero))).
  { destruct (V293_rekey_local_eval ge le M1 be be bindings yo _ Loc1 Iyo) as [Ty Vy].
    destruct (V293_event_row_eval ge le M1 pevent (evar yo) bc be base
      (fst cleared) (snd cleared) (V293_ready_group lo hi) (V293_prio_row old)
      Bind Ptr1 Base Limit Ty Vy Yo Loads1) as [T [_ V]].
    rewrite CV in V. eapply V293_rekey_byte_zero_eval; eassumption. }
  assert (GroupClear : forall tail,
    cstepstar P (curs (sifthen (ebinop oeq
      (ecast (earrayelem (efield (ederef (evar pevent)) 5%Z) (evar yo)) Tint32) (econst32 Int.zero))
      (sassign (efield (ederef (evar pevent)) 4%Z)
        (V293_task_prio_clear_expr (efield (ederef (evar pevent)) 4%Z) (evar byo)))),
      (kenil,tail)) (ge,le,M1) (curs (sskip None),(kenil,tail)) (ge,le,M2)).
  { intro tail. eapply V293_rekey_if_execution with (flag := cv =? 0); [exact Cond| | ].
    - intro Zero. unfold M2. rewrite GC; try rewrite Zero.
      exact (proj1 (V293_event_group_execution P tail ge le M1 pevent byo be bc base
        (fst cleared) (snd cleared) (V293_ready_group lo hi) (V293_prio_row old) true
        bindings GroupBound ltac:(lia) Bind Ptr1 Base Limit Loads1 W1 Loc1 Ibyo)).
    - intro Nonzero. unfold M2. rewrite Nonzero. reflexivity. }
  assert (AfterClear : V293_event_bitmap_loads M2 be base (fst cleared) (snd cleared) gc /\
    V293_event_bitmap_writable M2 be base /\ V293_rekey_locals ge le M2 be be bindings /\ gc < 256).
  { unfold M2. destruct (cv =? 0) eqn:Zero.
    - rewrite GC; try rewrite Zero.
      exact (proj2 (V293_event_group_execution P ks ge le M1 pevent byo be bc base
        (fst cleared) (snd cleared) (V293_ready_group lo hi) (V293_prio_row old) true
        bindings GroupBound ltac:(lia) Bind Ptr1 Base Limit Loads1 W1 Loc1 Ibyo)).
    - rewrite GC; try rewrite Zero. auto. }
  destruct AfterClear as [Loads2 [W2 [Loc2 GCBound]]].
  assert (Ptr2 : load (Tptr V293_event_type) M2 (bc,0%Z) = Some (Vptr (be,Int.repr base))).
  { unfold M2. destruct (cv =? 0); [rewrite (V293_event_pointer_write M1 bc be (be,(base+10)%Z) gc Apart eq_refl) | ]; exact Ptr1. }
  pose (gn := V293_ready_rekey_group lo hi old new).
  pose (M3 := V293_put_byte M2 (be,(base+10)%Z) gn).
  assert (GroupSet : forall tail,
    cstepstar P (curs (sassign (efield (ederef (evar pevent)) 4%Z)
      (V293_task_prio_set_expr (efield (ederef (evar pevent)) 4%Z) (evar byn))),
      (kenil,tail)) (ge,le,M2) (curs (sskip None),(kenil,tail)) (ge,le,M3)).
  { intro tail. exact (proj1 (V293_event_group_execution P tail ge le M2 pevent byn be bc base
      (fst cleared) (snd cleared) gc (V293_prio_row new) false bindings
      GCBound ltac:(lia) Bind Ptr2 Base Limit Loads2 W2 Loc2 Ibyn)). }
  destruct (V293_event_group_execution P ks ge le M2 pevent byn be bc base
    (fst cleared) (snd cleared) gc (V293_prio_row new) false bindings GCBound
    ltac:(lia) Bind Ptr2 Base Limit Loads2 W2 Loc2 Ibyn) as [_ [Loads3 [W3 [Loc3 GNBound]]]].
  change (V293_event_bitmap_loads M3 be base (fst cleared) (snd cleared) gn) in Loads3.
  change (V293_event_bitmap_writable M3 be base) in W3.
  change (V293_rekey_locals ge le M3 be be bindings) in Loc3.
  assert (Ptr3 : load (Tptr V293_event_type) M3 (bc,0%Z) = Some (Vptr (be,Int.repr base))).
  { unfold M3. rewrite (V293_event_pointer_write M2 bc be (be,(base+10)%Z) gn Apart eq_refl). exact Ptr2. }
  pose (nv := Nat.setbit (V293_ready_row (fst cleared) (snd cleared) (V293_prio_row new))
    (V293_prio_bit new)).
  pose (M4 := V293_put_byte M3 (be,(base+11+Z.of_nat (V293_prio_row new))%Z) nv).
  destruct (V293_event_row_execution P ks ge le M3 pevent yn xn be bc base
    (fst cleared) (snd cleared) gn (V293_prio_row new) (V293_prio_bit new) false bindings
    (proj1 CL) (proj2 CL) Yn Xn Bind Ptr3 Base Limit Loads3 W3 Loc3 Iyn Ixn)
    as [RowSet [Loads4 [W4 [Loc4 NVBound]]]].
  assert (ES : V293_ready_replace_row (fst cleared) (snd cleared) (V293_prio_row new) nv =
    V293_ready_rekey_rows lo hi old new) by (apply V293_rekey_set_row_value).
  change (V293_event_bitmap_loads M4 be base
    (fst (V293_ready_replace_row (fst cleared) (snd cleared) (V293_prio_row new) nv))
    (snd (V293_ready_replace_row (fst cleared) (snd cleared) (V293_prio_row new) nv)) gn) in Loads4.
  rewrite ES in Loads4. unfold gn in Loads4. rewrite V293_ready_rekey_group_correct in Loads4.
  assert (Memory : V293_event_rekey_memory M be base lo hi old new = M4).
  { unfold V293_event_rekey_memory. fold cleared. rewrite CV.
    fold M1 M2 M3. unfold M4,nv. f_equal.
    unfold V293_ready_rekey_rows. fold cleared. apply V293_rekey_set_row_value. }
  rewrite Memory. split.
  - unfold V293_task_prio_event_then.
    eapply V293_rekey_sequence_execution; [exact Clear | ].
    eapply V293_rekey_sequence_execution; [exact GroupClear | ].
    eapply V293_rekey_sequence_execution; [exact GroupSet | exact RowSet].
  - split; [exact Loads4 | ]. split; [exact W4 | ]. split; [exact Loc4 | ]. split.
    + unfold M4. rewrite (V293_event_pointer_write M3 bc be (be,(base+11+Z.of_nat (V293_prio_row new))%Z) nv Apart eq_refl). exact Ptr3.
    + intros c i Outside. unfold M4,M3,M2,M1.
      assert (No : forall y, y < 2 -> (c,i) <> (be,(base+11+Z.of_nat y)%Z)).
      { intros y Y E. inversion E; subst c i. destruct Outside as [A|[A|A]]; try contradiction; lia. }
      assert (Ng : (c,i) <> (be,(base+10)%Z)).
      { intro E. inversion E; subst c i. destruct Outside as [A|[A|A]]; try contradiction; lia. }
      destruct (cv =? 0); repeat first
        [ rewrite V293_put_byte_other by (apply No; assumption)
        | rewrite V293_put_byte_other by exact Ng ]; reflexivity.
Qed.

(* The real event-field read, actual non-null condition, and field updates
   run in one memory chain.  Entry resources, not a suffix oracle. *)
Theorem V293_task_prio_event_nonnull_execution :
  forall P ks ge le M ptcb pevent yo yn xo xn byo byn bc bt bp tcbbase be base lo hi old new,
  old < 13 -> new < 13 -> lo < 256 -> hi < 256 -> bp <> be ->
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  get le pevent = Some (bp,Tptr V293_event_type) ->
  load (Tptr V293_tcb_type) M (bc,0%Z) = Some (Vptr (bt,Int.repr tcbbase)) ->
  (0 <= tcbbase)%Z -> (tcbbase+28 <= Int.max_unsigned)%Z ->
  load (Tcom_ptr 411%Z) M (bt,(tcbbase+28)%Z) = Some (Vptr (be,Int.repr base)) ->
  V293_bytes_writable M bp 0%Z 4 ->
  (0 <= base)%Z -> (base+12 <= Int.max_unsigned)%Z ->
  V293_event_bitmap_loads M be base lo hi (V293_ready_group lo hi) ->
  V293_event_bitmap_writable M be base ->
  V293_rekey_locals ge le M be be (V293_rekey_ready_bindings yo yn xo xn byo byn old new) ->
  (forall x v c, In (x,v) (V293_rekey_ready_bindings yo yn xo xn byo byn old new) ->
    get le x = Some (c,Tint8) -> c <> bp) ->
  exists Me,
  let Mf := V293_event_rekey_memory Me be base lo hi old new in
  let fr := V293_ready_rekey_rows lo hi old new in
  store (Tptr V293_event_type) M (bp,0%Z) (Vptr (be,Int.repr base)) = Some Me /\
  cstepstar P (curs (V293_task_prio_event ptcb pevent yo yn xo xn byo byn),(kenil,ks))
    (ge,le,M) (curs (sskip None),(kenil,ks)) (ge,le,Mf) /\
  V293_event_bitmap_loads Mf be base (fst fr) (snd fr) (V293_ready_group (fst fr) (snd fr)) /\
  V293_event_bitmap_writable Mf be base /\
  V293_rekey_locals ge le Mf be be (V293_rekey_ready_bindings yo yn xo xn byo byn old new) /\
  load (Tptr V293_event_type) Mf (bp,0%Z) = Some (Vptr (be,Int.repr base)) /\
  (forall c i, c <> bp -> c <> be -> get Mf (c,i) = get M (c,i)).
Proof.
  intros P ks ge le M ptcb pevent yo yn xo xn byo byn bc bt bp tcbbase be base lo hi old new
    O N L H Apart Bp Be Lp TB TR Event Dest Base Limit Loads W Loc LocalApart.
  destruct (V293_task_prio_event_read_execution P ks ge le M ptcb pevent bc bt bp tcbbase
    (Vptr (be,Int.repr base)) Bp Be Lp TB TR Event ltac:(right; eauto) Dest)
    as (Me & Store & ReadExec & Read & Test & Frame).
  assert (ELoads : V293_event_bitmap_loads Me be base lo hi (V293_ready_group lo hi)).
  { destruct Loads as (LL & LH & LG). unfold V293_event_bitmap_loads.
    repeat split; erewrite V293_load_block_frame; try eassumption;
      intros; apply Frame; congruence. }
  assert (EW : V293_event_bitmap_writable Me be base).
  { destruct W as ([vl WL] & [vh WH] & [vg WG]). unfold V293_event_bitmap_writable.
    repeat split; eexists; rewrite Frame by congruence; eassumption. }
  assert (ELoc : V293_rekey_locals ge le Me be be
    (V293_rekey_ready_bindings yo yn xo xn byo byn old new)).
  { intros x v I. destruct (Loc x v I) as (c & Bind & A & B & Load).
    exists c. repeat split; try assumption. erewrite V293_load_block_frame; [exact Load | ].
    intro i. apply Frame. eapply LocalApart; eassumption. }
  destruct (V293_task_prio_event_then_execution P ks ge le Me pevent yo yn xo xn byo byn
    be bp base lo hi old new O N L H Apart Be Read Base Limit ELoads EW ELoc)
    as (Body & FinalLoads & FinalW & FinalLoc & FinalPtr & FinalFrame).
  exists Me. cbn zeta. split; [exact Store | ]. split.
  - unfold V293_task_prio_event. eapply V293_rekey_sequence_execution.
    + intro tail. destruct (V293_task_prio_event_read_execution P tail ge le M ptcb pevent bc bt bp tcbbase
        (Vptr (be,Int.repr base)) Bp Be Lp TB TR Event ltac:(right; eauto) Dest)
        as (Mt & St & Et & _).
      rewrite Store in St. inversion St; subst Mt. exact Et.
    + eapply V293_rekey_if_execution with (flag := true); [exact Test | | ].
      * intros _. exact Body.
      * intros Impossible. discriminate.
  - split; [exact FinalLoads | ]. split; [exact FinalW | ]. split; [exact FinalLoc | ].
    split; [exact FinalPtr | ]. intros c i Cp Ce.
    rewrite FinalFrame by (left; exact Ce). apply Frame. exact Cp.
Qed.

(* One satisfiable physical entry. Ready bytes stay 16/0/1 independently of
   the event wait bitmap. Neither an allocator nor a reachable API invariant. *)
Definition V293_event_body_fixture_le : env :=
  set (set V293_ready_fragment_fixture_le 600%Z (70%positive,Tptr V293_event_type))
    601%Z (40%positive,Tptr V293_tcb_type).
Definition V293_event_body_fixture_mem lo hi old new : mem :=
  V293_fixture_put_bytes
    (V293_fixture_put_bytes
      (V293_fixture_put_bytes
        (V293_put_byte (V293_put_byte (V293_put_byte
          (V293_ready_fragment_fixture_mem 16 0 old new)
          (72%positive,16%Z) lo) (72%positive,17%Z) hi)
          (72%positive,15%Z) (V293_ready_group lo hi))
        40%positive 0%Z (encode_val (Tptr V293_tcb_type) (Vptr (41%positive,Int.repr 8))))
      41%positive 36%Z (encode_val (Tcom_ptr 411%Z) (Vptr (72%positive,Int.repr 5))))
    70%positive 0%Z (encode_val (Tptr V293_event_type) (Vptr (71%positive,Int.repr 3))).

Lemma V293_event_body_fixture_outside : forall lo hi old new c i,
  c <> 70%positive -> c <> 41%positive -> c <> 40%positive -> c <> 72%positive ->
  get (V293_event_body_fixture_mem lo hi old new) (c,i) =
    get (V293_ready_fragment_fixture_mem 16 0 old new) (c,i).
Proof.
  intros lo hi old new c i A B C D. unfold V293_event_body_fixture_mem.
  repeat rewrite V293_fixture_bytes_outside by (left; assumption).
  repeat rewrite V293_put_byte_other by congruence. reflexivity.
Qed.

Theorem V293_event_body_fixture_entry : forall lo hi old new,
  lo < 256 -> hi < 256 -> old < 13 -> new < 13 ->
  let M := V293_event_body_fixture_mem lo hi old new in
  let le := V293_event_body_fixture_le in
  load (Tptr V293_tcb_type) M (40%positive,0%Z) = Some (Vptr (41%positive,Int.repr 8)) /\
  load (Tcom_ptr 411%Z) M (41%positive,36%Z) = Some (Vptr (72%positive,Int.repr 5)) /\
  load (Tptr V293_event_type) M (70%positive,0%Z) = Some (Vptr (71%positive,Int.repr 3)) /\
  V293_bytes_writable M 70%positive 0%Z 4 /\
  V293_event_bitmap_loads M 72%positive 5%Z lo hi (V293_ready_group lo hi) /\
  V293_event_bitmap_writable M 72%positive 5%Z /\
  V293_rekey_locals V293_ready_fragment_fixture_ge le M 72%positive 72%positive
    (V293_rekey_ready_bindings 302%Z 303%Z 304%Z 305%Z 306%Z 307%Z old new) /\
  (forall x v c, In (x,v) (V293_rekey_ready_bindings 302%Z 303%Z 304%Z 305%Z 306%Z 307%Z old new) ->
    get le x = Some (c,Tint8) -> c <> 70%positive) /\
  V293_rekey_bitmap_loads M 30%positive 31%positive 16 0 1.
Proof.
  intros lo hi old new L H O N. cbn zeta.
  destruct (V293_ready_fragment_entry_witness 16 0 old new ltac:(lia) ltac:(lia) O N)
    as (Ready & _ & Loc).
  assert (RF : forall tp c i, c <> 70%positive -> c <> 41%positive -> c <> 40%positive -> c <> 72%positive ->
    load tp (V293_event_body_fixture_mem lo hi old new) (c,i) =
    load tp (V293_ready_fragment_fixture_mem 16 0 old new) (c,i)).
  { intros. apply V293_load_block_frame. intro j. apply V293_event_body_fixture_outside; assumption. }
  assert (EF : forall c i, c <> 70%positive -> c <> 41%positive -> c <> 40%positive ->
    get (V293_event_body_fixture_mem lo hi old new) (c,i) =
    get (V293_put_byte (V293_put_byte (V293_put_byte
      (V293_ready_fragment_fixture_mem 16 0 old new) (72%positive,16%Z) lo)
      (72%positive,17%Z) hi) (72%positive,15%Z) (V293_ready_group lo hi)) (c,i)).
  { intros. unfold V293_event_body_fixture_mem.
    repeat rewrite V293_fixture_bytes_outside by (left; assumption). reflexivity. }
  split.
  - unfold V293_event_body_fixture_mem.
    erewrite V293_load_block_frame; [apply V293_fixture_encoded_load; reflexivity | ].
    intro j. repeat rewrite V293_fixture_bytes_outside by (left; discriminate). reflexivity.
  - split.
    + unfold V293_event_body_fixture_mem.
      erewrite V293_load_block_frame; [apply V293_fixture_encoded_load; reflexivity | ].
      intro j. rewrite V293_fixture_bytes_outside by (left; discriminate). reflexivity.
    + split; [unfold V293_event_body_fixture_mem; apply V293_fixture_encoded_load; reflexivity | ]. split.
      * intros k K. unfold V293_event_body_fixture_mem.
        exists (nth k (encode_val (Tptr V293_event_type) (Vptr (71%positive,Int.repr 3))) Undef).
        apply V293_fixture_bytes_nth. rewrite encode_val_length. exact K.
      * split.
        -- unfold V293_event_bitmap_loads. repeat split;
             (erewrite V293_load_block_frame; [ | intro j; apply EF; discriminate]);
             repeat rewrite V293_put_byte_other_load by discriminate; apply V293_put_byte_load; try assumption.
           unfold V293_ready_group. destruct (lo =? 0); destruct (hi =? 0); lia.
        -- split.
           ++ unfold V293_event_bitmap_writable. repeat split;
                eexists; rewrite EF by discriminate;
                repeat rewrite V293_put_byte_other by discriminate;
                apply V293_put_byte_get_same.
           ++ split.
              ** intros x v I. destruct (Loc x v I) as (c & Bind & A & B & Load).
                 cbn [V293_rekey_ready_bindings In] in I.
                 destruct I as [E|[E|[E|[E|[E|[E|F]]]]]]; try contradiction;
                   inversion E; subst x v;
                   unfold V293_ready_fragment_fixture_le in Bind;
                   repeat first [rewrite map_get_set in Bind | rewrite map_get_set' in Bind by discriminate];
                   inversion Bind; subst c.
                 all: eexists; split; [unfold V293_event_body_fixture_le,V293_ready_fragment_fixture_le;
                   repeat first [rewrite map_get_set | rewrite map_get_set' by discriminate]; reflexivity | ];
                   split; [discriminate| ]; split; [discriminate| ]; rewrite RF by discriminate; exact Load.
              ** split.
                 --- intros x v c I Bind. cbn [V293_rekey_ready_bindings In] in I.
                     destruct I as [E|[E|[E|[E|[E|[E|F]]]]]]; try contradiction;
                       inversion E; subst x v; unfold V293_event_body_fixture_le,V293_ready_fragment_fixture_le in Bind;
                       repeat first [rewrite map_get_set in Bind | rewrite map_get_set' in Bind by discriminate];
                       inversion Bind; discriminate.
                 --- unfold V293_rekey_bitmap_loads in *. repeat rewrite RF by discriminate. exact Ready.
Qed.

Theorem V293_event_nonnull_execution_witness : forall P ks lo hi old new,
  lo < 256 -> hi < 256 -> old < 13 -> new < 13 ->
  exists Mf,
  cstepstar P (curs (V293_task_prio_event 601%Z 600%Z 302%Z 303%Z 304%Z 305%Z 306%Z 307%Z),
    (kenil,ks))
    (V293_ready_fragment_fixture_ge,V293_event_body_fixture_le,V293_event_body_fixture_mem lo hi old new)
    (curs (sskip None),(kenil,ks)) (V293_ready_fragment_fixture_ge,V293_event_body_fixture_le,Mf) /\
  V293_event_bitmap_loads Mf 72%positive 5%Z
    (fst (V293_ready_rekey_rows lo hi old new)) (snd (V293_ready_rekey_rows lo hi old new))
    (V293_ready_group (fst (V293_ready_rekey_rows lo hi old new)) (snd (V293_ready_rekey_rows lo hi old new))) /\
  load (Tptr V293_event_type) Mf (70%positive,0%Z) = Some (Vptr (72%positive,Int.repr 5)) /\
  V293_rekey_bitmap_loads Mf 30%positive 31%positive 16 0 1.
Proof.
  intros P ks lo hi old new L H O N.
  destruct (V293_event_body_fixture_entry lo hi old new L H O N)
    as (Lp & Event & Initial & Dest & Loads & W & Loc & Apart & Ready).
  assert (Bp : get V293_event_body_fixture_le 601%Z = Some (40%positive,Tptr V293_tcb_type)).
  { unfold V293_event_body_fixture_le. apply map_get_set. }
  assert (Be : get V293_event_body_fixture_le 600%Z = Some (70%positive,Tptr V293_event_type)).
  { unfold V293_event_body_fixture_le. rewrite map_get_set' by discriminate. apply map_get_set. }
  destruct (V293_task_prio_event_nonnull_execution P ks V293_ready_fragment_fixture_ge
    V293_event_body_fixture_le (V293_event_body_fixture_mem lo hi old new)
    601%Z 600%Z 302%Z 303%Z 304%Z 305%Z 306%Z 307%Z
    40%positive 41%positive 70%positive 8%Z 72%positive 5%Z lo hi old new
    O N L H ltac:(discriminate) Bp Be Lp ltac:(lia) ltac:(change (8+28 <= 4294967295)%Z; lia) Event Dest
    ltac:(lia) ltac:(change (5+12 <= 4294967295)%Z; lia) Loads W Loc Apart)
    as (Me & Store & Exec & Final & _ & _ & PointerRead & Frame).
  exists (V293_event_rekey_memory Me 72%positive 5%Z lo hi old new).
  split; [exact Exec | ]. split; [exact Final | ]. split; [exact PointerRead | ].
  unfold V293_rekey_bitmap_loads in *. destruct Ready as (R0 & R1 & RG).
  repeat split; erewrite V293_load_block_frame; try eassumption;
    intro i; apply Frame; discriminate.
Qed.

Definition V293_event_nonnull_observes lo hi old new expectedlo expectedhi expectedgroup : Prop :=
  forall P ks, exists Mf,
  cstepstar P (curs (V293_task_prio_event 601%Z 600%Z 302%Z 303%Z 304%Z 305%Z 306%Z 307%Z),
    (kenil,ks))
    (V293_ready_fragment_fixture_ge,V293_event_body_fixture_le,V293_event_body_fixture_mem lo hi old new)
    (curs (sskip None),(kenil,ks)) (V293_ready_fragment_fixture_ge,V293_event_body_fixture_le,Mf) /\
  V293_event_bitmap_loads Mf 72%positive 5%Z expectedlo expectedhi expectedgroup /\
  load (Tptr V293_event_type) Mf (70%positive,0%Z) = Some (Vptr (72%positive,Int.repr 5)) /\
  V293_rekey_bitmap_loads Mf 30%positive 31%positive 16 0 1.

Theorem V293_event_nonnull_physical_controls :
  V293_event_nonnull_observes 0 1 8 6 64 0 1 /\
  V293_event_nonnull_observes 0 1 8 10 0 4 2 /\
  V293_event_nonnull_observes 20 0 2 6 80 0 1 /\
  V293_event_nonnull_observes 0 129 8 6 64 128 3.
Proof.
  split.
  - intros P ks. exact (V293_event_nonnull_execution_witness P ks 0 1 8 6 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
  - split.
    + intros P ks. exact (V293_event_nonnull_execution_witness P ks 0 1 8 10 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    + split.
      * intros P ks. exact (V293_event_nonnull_execution_witness P ks 20 0 2 6 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
      * intros P ks. exact (V293_event_nonnull_execution_witness P ks 0 129 8 6 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
Qed.

(* Only the generic arbitrary-address pointer frame needs this raw control.
   This overwrite is NOT an OSEventGrp/Tbl address with nonnegative base.
   Thus it does NOT establish necessity of whole-block separation for the
   actual event program (whose offset >= 10 is disjoint from bytes 0..3). *)
Theorem V293_event_pointer_raw_alias_control :
  let M := V293_fixture_put_bytes emp 72%positive 0%Z
    (encode_val (Tptr V293_event_type) (Vptr (72%positive,Int.repr 5))) in
  load (Tptr V293_event_type) M (72%positive,0%Z) = Some (Vptr (72%positive,Int.repr 5)) /\
  load (Tptr V293_event_type) (V293_put_byte M (72%positive,0%Z) 0)
    (72%positive,0%Z) = Some Vundef.
Proof.
  cbn zeta. split; [apply V293_fixture_encoded_load; reflexivity | ].
  cbn [load loadm typelen loadbytes encode_val inj_pointer V293_fixture_put_bytes].
  unfold V293_put_byte.
  repeat first [rewrite map_get_set | rewrite map_get_set' by discriminate].
  reflexivity.
Qed.

(* Continuous source 119-143, non-null event path. All resources start in M. *)
Theorem V293_task_prio_prefix_event_nonnull_execution :
  forall P ks ge le M table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi old new entries pevent bp be ebase elo ehi,
  old < 13 -> new < 13 -> old <> new -> lo < 256 -> hi < 256 -> br <> bg ->
  (0 <= base)%Z -> (base+55 <= Int.max_unsigned)%Z ->
  get le table = None -> get ge table = Some (b,Tarray (Tptr V293_tcb_type) 13) ->
  get le oldprio = Some (bo,Tint8) -> get le newprio = Some (bn,Tint8) ->
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  b <> bo -> b <> bn -> b <> bc -> b <> bt ->
  b <> dy -> b <> dby -> b <> dx -> b <> br -> b <> bg ->
  load Tint8 M (bo,0%Z) = Some (V293_byteval old) ->
  load Tint8 M (bn,0%Z) = Some (V293_byteval new) ->
  load (Tptr V293_tcb_type) M (bc,0%Z) = Some (Vptr (bt,Int.repr base)) ->
  V293_bytes_writable M b (4*Z.of_nat old)%Z 4 ->
  V293_bytes_writable M b (4*Z.of_nat new)%Z 4 ->
  length entries = 13 -> V293_table_loads V293_tcb_type M b entries ->
  get le yo = Some (dy,Tint8) -> get le byo = Some (dby,Tint8) -> get le xo = Some (dx,Tint8) ->
  get le rows = None -> get ge rows = Some (br,Tarray Tint8 2) ->
  get le group = None -> get ge group = Some (bg,Tint8) ->
  dy <> dby -> dy <> dx -> dby <> dx ->
  (forall c, c = dy \/ c = dby \/ c = dx -> c <> bc /\ c <> bt /\ c <> br /\ c <> bg) ->
  V293_tcb_old_loads M bt base (V293_prio_row old)
    (2 ^ V293_prio_row old) (2 ^ V293_prio_bit old) ->
  (exists v, get M (dy,0%Z) = Some (true,v)) ->
  (exists v, get M (dby,0%Z) = Some (true,v)) ->
  (exists v, get M (dx,0%Z) = Some (true,v)) ->
  V293_rekey_bitmap_loads M br bg lo hi (V293_ready_group lo hi) ->
  V293_rekey_bitmap_writable M br bg ->
  V293_rekey_locals ge le M br bg (V293_rekey_new_bindings yn xn byn new) ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> b /\ c <> dy /\ c <> dby /\ c <> dx) ->
  get le pevent = Some (bp,Tptr V293_event_type) ->
  V293_bytes_writable M bp 0%Z 4 ->
  load (Tcom_ptr 411%Z) M (bt,(base+28)%Z) = Some (Vptr (be,Int.repr ebase)) ->
  bc <> br -> bc <> bg -> bt <> br -> bt <> bg ->
  bp <> b -> bp <> dy -> bp <> dby -> bp <> dx -> bp <> br -> bp <> bg ->
  bp <> be ->
  be <> b -> be <> dy -> be <> dby -> be <> dx -> be <> br -> be <> bg ->
  elo < 256 -> ehi < 256 -> (0 <= ebase)%Z -> (ebase+12 <= Int.max_unsigned)%Z ->
  V293_event_bitmap_loads M be ebase elo ehi (V293_ready_group elo ehi) ->
  V293_event_bitmap_writable M be ebase ->
  (forall x v c, In (x,v) (V293_rekey_ready_bindings yo yn xo xn byo byn old new) ->
    get le x = Some (c,Tint8) -> c <> bp /\ c <> be) ->
  exists M1 M2 Me,
  let Mr := V293_tcb_read_memory M2 dy dby dx (V293_prio_row old)
    (2 ^ V293_prio_row old) (2 ^ V293_prio_bit old) in
  let Mf := V293_ready_branch_memory Mr br bg lo hi old new in
  let Mg := V293_event_rekey_memory Me be ebase elo ehi old new in
  let fr := V293_ready_branch_rows lo hi old new in
  let er := V293_ready_rekey_rows elo ehi old new in
  store (Tptr V293_tcb_type) M (b,(4*Z.of_nat old)%Z) Vnull = Some M1 /\
  store (Tptr V293_tcb_type) M1 (b,(4*Z.of_nat new)%Z) (Vptr (bt,Int.repr base)) = Some M2 /\
  store (Tptr V293_event_type) Mf (bp,0%Z) (Vptr (be,Int.repr ebase)) = Some Me /\
  cstepstar P (curs (V293_task_prio_prefix_event table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent),
    (kenil,ks)) (ge,le,M) (curs (sskip None),(kenil,ks)) (ge,le,Mg) /\
  evalval (V293_task_prio_ready_test rows yo xo) (ge,le,Mr) =
    Some (Vint32 (if V293_ready_test_flag lo hi old then Int.one else Int.zero)) /\
  V293_rekey_bitmap_loads Mg br bg (fst fr) (snd fr) (V293_ready_group (fst fr) (snd fr)) /\
  V293_table_loads V293_tcb_type Mg b
    (update_nth_val new (update_nth_val old entries Vnull) (Vptr (bt,Int.repr base))) /\
  load (Tptr V293_tcb_type) Mg (b,(4*Z.of_nat old)%Z) = Some Vnull /\
  load (Tptr V293_tcb_type) Mg (b,(4*Z.of_nat new)%Z) = Some (Vptr (bt,Int.repr base)) /\
  V293_rekey_bitmap_writable Mg br bg /\
  V293_rekey_locals ge le Mg br bg (V293_rekey_ready_bindings yo yn xo xn byo byn old new) /\
  V293_event_bitmap_loads Mg be ebase (fst er) (snd er) (V293_ready_group (fst er) (snd er)) /\
  V293_event_bitmap_writable Mg be ebase /\
  load (Tptr V293_event_type) Mg (bp,0%Z) = Some (Vptr (be,Int.repr ebase)) /\
  (forall c i, c <> b -> c <> dy -> c <> dby -> c <> dx -> c <> br -> c <> bg -> c <> bp -> c <> be ->
    get Mg (c,i) = get M (c,i)).
Proof.
  intros P ks ge le M table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi old new entries pevent bp be ebase elo ehi
    O N ON L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg
    Lo Ln Lp Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields
    Wy Wby Wx Loads W NewLoc NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg PE Eb Ey Eby Ex Er Eg EL EH EB ELimit ELoads EW LocalApart.
  assert (Prefix : forall tail, exists M1 M2,
    store (Tptr V293_tcb_type) M (b,(4*Z.of_nat old)%Z) Vnull = Some M1 /\
    store (Tptr V293_tcb_type) M1 (b,(4*Z.of_nat new)%Z) (Vptr (bt,Int.repr base)) = Some M2 /\
    cstepstar P (curs (V293_task_prio_prefix table oldprio newprio ptcb rows group yo yn xo xn byo byn),
      (kenil,tail)) (ge,le,M) (curs (sskip None),(kenil,tail))
      (ge,le,V293_ready_branch_memory
        (V293_tcb_read_memory M2 dy dby dx (V293_prio_row old)
          (2 ^ V293_prio_row old) (2 ^ V293_prio_bit old)) br bg lo hi old new)).
  { intro tail.
    destruct (V293_task_prio_prefix_execution P tail ge le M table oldprio newprio ptcb rows group
      yo yn xo xn byo byn b bo bn bc bt dy dby dx base br bg lo hi old new entries
      O N ON L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg
      Lo Ln Lp Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields
      Wy Wby Wx Loads W NewLoc NewApart) as (M1 & M2 & S1 & S2 & E & _).
    exists M1. exists M2. auto. }
  destruct (V293_task_prio_prefix_execution P ks ge le M table oldprio newprio ptcb rows group
    yo yn xo xn byo byn b bo bn bc bt dy dby dx base br bg lo hi old new entries
    O N ON L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg
    Lo Ln Lp Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields
    Wy Wby Wx Loads W NewLoc NewApart)
    as (M1 & M2 & S1 & S2 & Exec & Test & FinalLoads & FinalView & OldSlot & NewSlot & FinalW & FinalLoc & Frame).
  set (Mr := V293_tcb_read_memory M2 dy dby dx (V293_prio_row old)
    (2 ^ V293_prio_row old) (2 ^ V293_prio_bit old)) in *.
  set (Mf := V293_ready_branch_memory Mr br bg lo hi old new) in *.
  assert (PC : forall i, get Mf (bc,i) = get M (bc,i)).
  { intro i. apply Frame; try congruence;
      destruct (Apart dy ltac:(auto)) as [A _];
      destruct (Apart dby ltac:(auto)) as [A' _];
      destruct (Apart dx ltac:(auto)) as [A'' _]; congruence. }
  assert (TC : forall i, get Mf (bt,i) = get M (bt,i)).
  { intro i. apply Frame; try congruence;
      destruct (Apart dy ltac:(auto)) as [_ [A _]];
      destruct (Apart dby ltac:(auto)) as [_ [A' _]];
      destruct (Apart dx ltac:(auto)) as [_ [A'' _]]; congruence. }
  assert (PF : forall i, get Mf (bp,i) = get M (bp,i)) by (intro i; apply Frame; assumption).
  assert (EC : forall i, get Mf (be,i) = get M (be,i)) by (intro i; apply Frame; assumption).
  assert (ELoadsF : V293_event_bitmap_loads Mf be ebase elo ehi (V293_ready_group elo ehi)).
  { unfold V293_event_bitmap_loads in *.
    repeat rewrite (V293_load_block_frame _ M Mf be _ EC). exact ELoads. }
  assert (EWF : V293_event_bitmap_writable Mf be ebase).
  { unfold V293_event_bitmap_writable in *. repeat rewrite EC. exact EW. }
  assert (ELoc : V293_rekey_locals ge le Mf be be
    (V293_rekey_ready_bindings yo yn xo xn byo byn old new)).
  { intros x v I. destruct (FinalLoc x v I) as (c & Bind & A & B & Load).
    destruct (LocalApart x v c I Bind) as [Cp Ce]. exists c. auto. }
  destruct (V293_task_prio_event_nonnull_execution P ks ge le Mf ptcb pevent yo yn xo xn byo byn
    bc bt bp base be ebase elo ehi old new O N EL EH PE Bc Be
    ltac:(rewrite (V293_load_block_frame _ M Mf bc 0%Z PC); exact Lp)
    Base ltac:(lia) ltac:(rewrite (V293_load_block_frame _ M Mf bt (base+28)%Z TC); exact Event)
    ltac:(intros k K; rewrite PF; exact (We k K)) EB ELimit ELoadsF EWF ELoc
    ltac:(intros x v c I Bind; exact (proj1 (LocalApart x v c I Bind))))
    as (Me & Store & Suffix & EventLoads & EventW & EventLoc & Read & EF).
  set (Mg := V293_event_rekey_memory Me be ebase elo ehi old new) in *.
  assert (RF : forall tp c i, c <> bp -> c <> be -> load tp Mg (c,i) = load tp Mf (c,i)).
  { intros tp c i A B. apply V293_load_block_frame. intro j. apply EF; assumption. }
  exists M1. exists M2. exists Me. cbn zeta. fold Mr Mf Mg.
  split; [exact S1 | ]. split; [exact S2 | ]. split; [exact Store | ]. split.
  - unfold V293_task_prio_prefix_event. eapply V293_rekey_sequence_execution; [ | exact Suffix].
    intro tail. destruct (Prefix tail) as (A & B & SA & SB & E).
    rewrite S1 in SA. inversion SA; subst A. rewrite S2 in SB. inversion SB; subst B. exact E.
  - split; [exact Test | ]. split.
    + unfold V293_rekey_bitmap_loads in *. repeat rewrite RF by congruence. exact FinalLoads.
    + split.
      * intros p R. rewrite RF by congruence. exact (FinalView p R).
      * split; [rewrite RF by congruence; exact OldSlot | ].
        split; [rewrite RF by congruence; exact NewSlot | ]. split.
        -- unfold V293_rekey_bitmap_writable in *. repeat rewrite EF by congruence. exact FinalW.
        -- split.
           ++ intros x v I. destruct (FinalLoc x v I) as (c & Bind & A & B & Load).
              destruct (LocalApart x v c I Bind) as [Cp Ce].
              exists c. repeat split; try assumption. rewrite RF by assumption. exact Load.
           ++ split; [exact EventLoads | ]. split; [exact EventW | ]. split; [exact Read | ].
              intros c i Cb Cy Cby Cx Cr' Cg' Cp Ce. rewrite EF by assumption.
              apply Frame; assumption.
Qed.

(* Extend the existing simultaneous table/TCB/ready entry by real event
   bytes. Old locals are still overwritten from the TCB, not entry oracles. *)
Definition V293_prefix_event_nonnull_mem live elo ehi : mem :=
  V293_put_byte (V293_put_byte (V293_put_byte
    (V293_event_fixture_mem live (Vptr (72%positive,Int.repr 5)))
    (72%positive,16%Z) elo) (72%positive,17%Z) ehi)
    (72%positive,15%Z) (V293_ready_group elo ehi).

Lemma V293_prefix_event_nonnull_outside : forall live elo ehi c i,
  c <> 72%positive ->
  get (V293_prefix_event_nonnull_mem live elo ehi) (c,i) =
    get (V293_event_fixture_mem live (Vptr (72%positive,Int.repr 5))) (c,i).
Proof.
  intros. unfold V293_prefix_event_nonnull_mem.
  repeat rewrite V293_put_byte_other by congruence. reflexivity.
Qed.

Theorem V293_prefix_event_nonnull_entry : forall live elo ehi,
  elo < 256 -> ehi < 256 ->
  let M := V293_prefix_event_nonnull_mem live elo ehi in
  load (Tptr V293_tcb_type) M (40%positive,0%Z) = Some (Vptr (41%positive,Int.repr 8)) /\
  load (Tcom_ptr 411%Z) M (41%positive,36%Z) = Some (Vptr (72%positive,Int.repr 5)) /\
  V293_bytes_writable M 70%positive 0%Z 4 /\
  V293_tcb_old_loads M 41%positive 8%Z 1 2 1 /\
  V293_table_loads V293_tcb_type M 50%positive V293_prefix_fixture_entries /\
  V293_bytes_writable M 50%positive 32%Z 4 /\
  V293_bytes_writable M 50%positive 24%Z 4 /\
  (exists v, get M (32%positive,0%Z) = Some (true,v)) /\
  (exists v, get M (36%positive,0%Z) = Some (true,v)) /\
  (exists v, get M (34%positive,0%Z) = Some (true,v)) /\
  V293_rekey_bitmap_loads M 30%positive 31%positive 16 (if live then 1 else 0)
    (V293_ready_group 16 (if live then 1 else 0)) /\
  V293_rekey_bitmap_writable M 30%positive 31%positive /\
  V293_rekey_locals V293_prefix_fixture_ge V293_event_fixture_le M
    30%positive 31%positive (V293_rekey_new_bindings 303%Z 305%Z 307%Z 6) /\
  load Tint8 M (51%positive,0%Z) = Some (V293_byteval 8) /\
  load Tint8 M (52%positive,0%Z) = Some (V293_byteval 6) /\
  load (Tptr V293_event_type) M (70%positive,0%Z) = Some (Vptr (71%positive,Int.repr 3)) /\
  V293_event_bitmap_loads M 72%positive 5%Z elo ehi (V293_ready_group elo ehi) /\
  V293_event_bitmap_writable M 72%positive 5%Z.
Proof.
  intros live elo ehi EL EH. cbn zeta.
  destruct (V293_event_fixture_entry live (Vptr (72%positive,Int.repr 5)) ltac:(right; eauto))
    as (Lp & Event & We & Fields & View & Wo & Wn & Wy & Wby & Wx & Loads & W & NewLoc).
  assert (RF : forall tp c i, c <> 72%positive ->
    load tp (V293_prefix_event_nonnull_mem live elo ehi) (c,i) =
      load tp (V293_event_fixture_mem live (Vptr (72%positive,Int.repr 5))) (c,i)).
  { intros. apply V293_load_block_frame. intro j. apply V293_prefix_event_nonnull_outside. assumption. }
  split; [rewrite RF by discriminate; exact Lp | ].
  split; [rewrite RF by discriminate; exact Event | ]. split.
  - intros k K. rewrite V293_prefix_event_nonnull_outside by discriminate. exact (We k K).
  - split.
    + unfold V293_tcb_old_loads in *. repeat rewrite RF by discriminate. exact Fields.
    + split; [intros p R; rewrite RF by discriminate; exact (View p R) | ].
      split; [intros k K; rewrite V293_prefix_event_nonnull_outside by discriminate; exact (Wo k K) | ].
      split; [intros k K; rewrite V293_prefix_event_nonnull_outside by discriminate; exact (Wn k K) | ].
      split; [rewrite V293_prefix_event_nonnull_outside by discriminate; exact Wy | ].
      split; [rewrite V293_prefix_event_nonnull_outside by discriminate; exact Wby | ].
      split; [rewrite V293_prefix_event_nonnull_outside by discriminate; exact Wx | ]. split.
      * unfold V293_rekey_bitmap_loads in *. repeat rewrite RF by discriminate. exact Loads.
      * split.
        -- unfold V293_rekey_bitmap_writable in *.
           repeat rewrite V293_prefix_event_nonnull_outside by discriminate. exact W.
        -- split.
           ++ intros x v I. destruct (NewLoc x v I) as (c & Bind & A & B & Load).
              cbn [V293_rekey_new_bindings In] in I.
              destruct I as [E|[E|[E|F]]]; try contradiction; inversion E; subst x v;
                unfold V293_event_fixture_le,V293_prefix_fixture_le,V293_read_ready_fixture_le,V293_ready_fragment_fixture_le in Bind;
                repeat first [rewrite map_get_set in Bind | rewrite map_get_set' in Bind by discriminate];
                inversion Bind; subst c.
              all: eexists; split; [exact Bind | ]; split; [exact A | ]; split; [exact B | ];
                rewrite RF by discriminate; exact Load.
           ++ split.
              ** rewrite RF by discriminate.
                 rewrite (V293_load_block_frame _ (V293_prefix_fixture_mem live)) by
                   (intro j; apply V293_event_fixture_outside; [discriminate | left; discriminate]).
                 unfold V293_prefix_fixture_mem. rewrite V293_put_byte_other_load by discriminate.
                 apply V293_put_byte_load. lia.
              ** split.
                 --- rewrite RF by discriminate.
                     rewrite (V293_load_block_frame _ (V293_prefix_fixture_mem live)) by
                       (intro j; apply V293_event_fixture_outside; [discriminate | left; discriminate]).
                     unfold V293_prefix_fixture_mem. apply V293_put_byte_load. lia.
                 --- split.
                     +++ rewrite RF by discriminate. unfold V293_event_fixture_mem.
                         apply V293_fixture_encoded_load. reflexivity.
                     +++ split.
                         *** unfold V293_event_bitmap_loads,V293_prefix_event_nonnull_mem.
                             repeat split; repeat rewrite V293_put_byte_other_load by discriminate;
                               apply V293_put_byte_load; try assumption.
                             unfold V293_ready_group. destruct (elo =? 0); destruct (ehi =? 0); lia.
                         *** unfold V293_event_bitmap_writable,V293_prefix_event_nonnull_mem.
                             repeat split; eexists;
                               repeat rewrite V293_put_byte_other by discriminate;
                               apply V293_put_byte_get_same.
Qed.

Definition V293_prefix_event_nonnull_observes live elo ehi final_lo final_elo final_ehi final_eg : Prop :=
  forall P ks, exists Mg,
  cstepstar P (curs (V293_task_prio_prefix_event 500%Z 501%Z 502%Z 400%Z
    300%Z 301%Z 302%Z 303%Z 304%Z 305%Z 306%Z 307%Z 600%Z),(kenil,ks))
    (V293_prefix_fixture_ge,V293_event_fixture_le,V293_prefix_event_nonnull_mem live elo ehi)
    (curs (sskip None),(kenil,ks)) (V293_prefix_fixture_ge,V293_event_fixture_le,Mg) /\
  load (Tptr V293_event_type) Mg (70%positive,0%Z) = Some (Vptr (72%positive,Int.repr 5)) /\
  V293_rekey_bitmap_loads Mg 30%positive 31%positive final_lo 0 1 /\
  V293_event_bitmap_loads Mg 72%positive 5%Z final_elo final_ehi final_eg /\
  V293_table_loads V293_tcb_type Mg 50%positive
    (update_nth_val 6 (update_nth_val 8 V293_prefix_fixture_entries Vnull) (Vptr (41%positive,Int.repr 8))) /\
  load (Tptr V293_tcb_type) Mg (50%positive,32%Z) = Some Vnull /\
  load (Tptr V293_tcb_type) Mg (50%positive,24%Z) = Some (Vptr (41%positive,Int.repr 8)).

Theorem V293_prefix_event_nonnull_execution_witness : forall live elo ehi,
  elo < 256 -> ehi < 256 ->
  V293_prefix_event_nonnull_observes live elo ehi (if live then 80 else 16)
    (fst (V293_ready_rekey_rows elo ehi 8 6)) (snd (V293_ready_rekey_rows elo ehi 8 6))
    (V293_ready_group (fst (V293_ready_rekey_rows elo ehi 8 6)) (snd (V293_ready_rekey_rows elo ehi 8 6))).
Proof.
  intros live elo ehi EL EH P ks.
  destruct (V293_prefix_event_nonnull_entry live elo ehi EL EH)
    as (Lp & Event & We & Fields & View & Wo & Wn & Wy & Wby & Wx & Loads & W & NewLoc & Lo & Ln & Initial & ELoads & EW).
  destruct (V293_task_prio_prefix_event_nonnull_execution P ks V293_prefix_fixture_ge V293_event_fixture_le
    (V293_prefix_event_nonnull_mem live elo ehi) 500%Z 501%Z 502%Z 400%Z
    300%Z 301%Z 302%Z 303%Z 304%Z 305%Z 306%Z 307%Z
    50%positive 51%positive 52%positive 40%positive 41%positive
    32%positive 36%positive 34%positive 8%Z 30%positive 31%positive 16
    (if live then 1 else 0) 8 6 V293_prefix_fixture_entries 600%Z 70%positive 72%positive 5%Z elo ehi)
    as (M1 & M2 & Me & S1 & S2 & Store & Exec & Test & FinalLoads & FinalView & OldSlot & NewSlot & FinalW & FinalLoc & FinalEvent & FinalEW & Read & Frame).
  all: try assumption; try discriminate; try (event_fixture_bind; reflexivity);
    try (change (0 <= 8)%Z; lia); try (change (8+55 <= 4294967295)%Z; lia);
    try (change (0 <= 5)%Z; lia); try (change (5+12 <= 4294967295)%Z; lia);
    try (change (8<13); lia); try (change (6<13); lia); try (change (16<256); lia);
    try (destruct live; lia); try (change (length V293_prefix_fixture_entries = 13); reflexivity).
  - intros x v c I Bind. cbn [V293_rekey_new_bindings In] in I.
    destruct I as [E|[E|[E|F]]]; try contradiction; inversion E; subst x v;
      unfold V293_event_fixture_le,V293_prefix_fixture_le,V293_read_ready_fixture_le,V293_ready_fragment_fixture_le in Bind;
      repeat first [rewrite map_get_set in Bind | rewrite map_get_set' in Bind by discriminate];
      inversion Bind; subst c; repeat split; discriminate.
  - intros x v c I Bind. cbn [V293_rekey_ready_bindings In] in I.
    destruct I as [E|[E|[E|[E|[E|[E|F]]]]]]; try contradiction; inversion E; subst x v;
      unfold V293_event_fixture_le,V293_prefix_fixture_le,V293_read_ready_fixture_le,V293_ready_fragment_fixture_le in Bind;
      repeat first [rewrite map_get_set in Bind | rewrite map_get_set' in Bind by discriminate];
      inversion Bind; subst c; split; discriminate.
  - eexists. split; [exact Exec | ]. split; [exact Read | ].
    split; [destruct live; exact FinalLoads | ]. split; [exact FinalEvent | ].
    split; [exact FinalView | ]. split; assumption.
Qed.

Theorem V293_prefix_event_nonnull_controls :
  V293_prefix_event_nonnull_observes false 0 1 16 64 0 1 /\
  V293_prefix_event_nonnull_observes true 0 1 80 64 0 1 /\
  V293_prefix_event_nonnull_observes false 16 3 16 80 2 3 /\
  V293_prefix_event_nonnull_observes false 0 129 16 64 128 3.
Proof.
  split; [exact (V293_prefix_event_nonnull_execution_witness false 0 1 ltac:(lia) ltac:(lia)) | ].
  split; [exact (V293_prefix_event_nonnull_execution_witness true 0 1 ltac:(lia) ltac:(lia)) | ].
  split; [exact (V293_prefix_event_nonnull_execution_witness false 16 3 ltac:(lia) ltac:(lia)) | ].
  exact (V293_prefix_event_nonnull_execution_witness false 0 129 ltac:(lia) ltac:(lia)).
Qed.

(* os_task.c:162-166: five physical fields, not an abstract TCB replacement. *)
Import ListNotations.
Definition V293_tcb_update_bindings newprio yn xi byn xn new : list (var * val) :=
  [(newprio,V293_byteval new); (yn,V293_byteval (V293_prio_row new));
   (xi,V293_byteval (V293_prio_bit new)); (byn,V293_byteval (2 ^ V293_prio_row new));
   (xn,V293_byteval (2 ^ V293_prio_bit new))].
Definition V293_tcb_update_writable (M : mem) bt base : Prop :=
  forall delta, (50 <= delta <= 54)%Z ->
    exists v, get M (bt,(base+delta)%Z) = Some (true,v).
Definition V293_tcb_update_memory M bt base new : mem :=
  V293_put_byte (V293_put_byte (V293_put_byte (V293_put_byte
    (V293_put_byte M (bt,(base+50)%Z) new)
      (bt,(base+52)%Z) (V293_prio_row new))
      (bt,(base+51)%Z) (V293_prio_bit new))
      (bt,(base+54)%Z) (2 ^ V293_prio_row new))
      (bt,(base+53)%Z) (2 ^ V293_prio_bit new).
Definition V293_tcb_updated_loads M bt base new : Prop :=
  load Tint8 M (bt,(base+50)%Z) = Some (V293_byteval new) /\
  load Tint8 M (bt,(base+52)%Z) = Some (V293_byteval (V293_prio_row new)) /\
  load Tint8 M (bt,(base+51)%Z) = Some (V293_byteval (V293_prio_bit new)) /\
  load Tint8 M (bt,(base+54)%Z) = Some (V293_byteval (2 ^ V293_prio_row new)) /\
  load Tint8 M (bt,(base+53)%Z) = Some (V293_byteval (2 ^ V293_prio_bit new)).

Lemma V293_tcb_byte_field_address : forall ge le M ptcb bc bt base id delta,
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  load (Tptr V293_tcb_type) M (bc,0%Z) = Some (Vptr (bt,Int.repr base)) ->
  ftype id V293_tcb_fields = Some Tint8 ->
  field_offset id V293_tcb_fields = Some (Int.repr delta) ->
  (0 <= base)%Z -> (0 <= delta)%Z -> (base+delta <= Int.max_unsigned)%Z ->
  evaltype (efield (ederef (evar ptcb)) id) (ge,le,M) = Some Tint8 /\
  evaladdr (efield (ederef (evar ptcb)) id) (ge,le,M) =
    Some (Vptr (bt,Int.repr (base+delta))).
Proof.
  intros ge le M ptcb bc bt base id delta Bind Hptr Ft Fo B D R.
  assert (Td : evaltype (ederef (evar ptcb)) (ge,le,M) = Some V293_tcb_type).
  { cbn [evaltype get_lenv get_genv]. rewrite Bind. reflexivity. }
  split.
  - cbn [evaltype get_lenv get_genv]. rewrite Bind. exact Ft.
  - cbn [evaladdr evalval evaltype get_lenv get_genv get_mem]. rewrite Bind.
    cbn beta iota. rewrite Hptr. unfold getoff. rewrite Td. cbn [V293_tcb_type]. rewrite Fo.
    rewrite Int.repr_unsigned. unfold Int.add.
    rewrite !Int.unsigned_repr by lia. reflexivity.
Qed.

(* Store construction needs permission, NOT an assumed old field value.
   Re-read the pointer and operand after every preceding physical write. *)
Lemma V293_tcb_update_one_execution :
  forall P ks ge le M ptcb bc bt base bindings id delta operand n,
  get le ptcb = Some (bc,Tptr V293_tcb_type) -> bc <> bt ->
  load (Tptr V293_tcb_type) M (bc,0%Z) = Some (Vptr (bt,Int.repr base)) ->
  V293_rekey_locals ge le M bt bt bindings ->
  V293_tcb_update_writable M bt base ->
  ftype id V293_tcb_fields = Some Tint8 ->
  field_offset id V293_tcb_fields = Some (Int.repr delta) ->
  (0 <= base)%Z -> (base+55 <= Int.max_unsigned)%Z -> (50 <= delta <= 54)%Z ->
  In (operand,V293_byteval n) bindings ->
  let M' := V293_put_byte M (bt,(base+delta)%Z) n in
  cstepstar P (curs (sassign (efield (ederef (evar ptcb)) id) (evar operand)),(kenil,ks))
    (ge,le,M) (curs (sskip None),(kenil,ks)) (ge,le,M') /\
  load (Tptr V293_tcb_type) M' (bc,0%Z) = Some (Vptr (bt,Int.repr base)) /\
  V293_rekey_locals ge le M' bt bt bindings /\ V293_tcb_update_writable M' bt base.
Proof.
  intros P ks ge le M ptcb bc bt base bindings id delta operand n
    Bind Apart Hptr Loc W Ft Fo B R D I. cbn zeta.
  destruct (V293_tcb_byte_field_address ge le M ptcb bc bt base id delta
    Bind Hptr Ft Fo B ltac:(lia) ltac:(lia)) as [T A].
  destruct (V293_rekey_local_eval ge le M bt bt bindings operand _ Loc I) as [Tr Vr].
  destruct (W delta D) as [v Permission].
  split.
  - eapply V293_assign_byte_offset_execution; try eassumption; [lia | ].
    apply V293_put_byte_store with (old := v). exact Permission.
  - split.
    + rewrite V293_put_byte_pointer_frame by (simpl; congruence). exact Hptr.
    + split.
      * apply V293_rekey_locals_write; [exact Loc | left; reflexivity].
      * intros d Bound. destruct (Z.eq_dec d delta) as [-> | Ne].
        -- eexists. apply V293_put_byte_get_same.
        -- rewrite V293_put_byte_other by (intro E; inversion E; lia). exact (W d Bound).
Qed.

Theorem V293_task_prio_tcb_update_execution :
  forall P ks ge le M ptcb newprio yn xi byn xn bc bt base new,
  new < 13 -> (0 <= base)%Z -> (base+55 <= Int.max_unsigned)%Z ->
  get le ptcb = Some (bc,Tptr V293_tcb_type) -> bc <> bt ->
  load (Tptr V293_tcb_type) M (bc,0%Z) = Some (Vptr (bt,Int.repr base)) ->
  V293_rekey_locals ge le M bt bt (V293_tcb_update_bindings newprio yn xi byn xn new) ->
  V293_tcb_update_writable M bt base ->
  let M' := V293_tcb_update_memory M bt base new in
  cstepstar P (curs (V293_task_prio_tcb_update ptcb newprio yn xi byn xn),(kenil,ks))
    (ge,le,M) (curs (sskip None),(kenil,ks)) (ge,le,M') /\
  V293_tcb_updated_loads M' bt base new /\
  load (Tptr V293_tcb_type) M' (bc,0%Z) = Some (Vptr (bt,Int.repr base)) /\
  V293_rekey_locals ge le M' bt bt (V293_tcb_update_bindings newprio yn xi byn xn new) /\
  V293_tcb_update_writable M' bt base /\
  (forall c i, c <> bt \/ (i < base+50)%Z \/ (base+54 < i)%Z -> get M' (c,i) = get M (c,i)).
Proof.
  intros P ks ge le M ptcb newprio yn xi byn xn bc bt base new N B R Bind Apart Hptr Loc W.
  set (bindings := V293_tcb_update_bindings newprio yn xi byn xn new) in *.
  set (M1 := V293_put_byte M (bt,(base+50)%Z) new).
  set (M2 := V293_put_byte M1 (bt,(base+52)%Z) (V293_prio_row new)).
  set (M3 := V293_put_byte M2 (bt,(base+51)%Z) (V293_prio_bit new)).
  set (M4 := V293_put_byte M3 (bt,(base+54)%Z) (2 ^ V293_prio_row new)).
  assert (Step1 : forall tail, cstepstar P
    (curs (sassign (efield (ederef (evar ptcb)) 16%Z) (evar newprio)),(kenil,tail))
    (ge,le,M) (curs (sskip None),(kenil,tail)) (ge,le,M1)).
  { intro tail. eapply (proj1 (V293_tcb_update_one_execution P tail ge le M ptcb bc bt base
      bindings 16%Z 50%Z newprio new Bind Apart Hptr Loc W eq_refl eq_refl B R
      ltac:(lia) ltac:(unfold bindings,V293_tcb_update_bindings; simpl; tauto))). }
  destruct (V293_tcb_update_one_execution P ks ge le M ptcb bc bt base
    bindings 16%Z 50%Z newprio new Bind Apart Hptr Loc W eq_refl eq_refl B R
    ltac:(lia) ltac:(unfold bindings,V293_tcb_update_bindings; simpl; tauto))
    as [_ [P1 [Loc1 W1]]]. fold M1 in P1,Loc1,W1.
  assert (Step2 : forall tail, cstepstar P
    (curs (sassign (efield (ederef (evar ptcb)) 18%Z) (evar yn)),(kenil,tail))
    (ge,le,M1) (curs (sskip None),(kenil,tail)) (ge,le,M2)).
  { intro tail. eapply (proj1 (V293_tcb_update_one_execution P tail ge le M1 ptcb bc bt base
      bindings 18%Z 52%Z yn (V293_prio_row new) Bind Apart P1 Loc1 W1 eq_refl eq_refl B R
      ltac:(lia) ltac:(unfold bindings,V293_tcb_update_bindings; simpl; tauto))). }
  destruct (V293_tcb_update_one_execution P ks ge le M1 ptcb bc bt base
    bindings 18%Z 52%Z yn (V293_prio_row new) Bind Apart P1 Loc1 W1 eq_refl eq_refl B R
    ltac:(lia) ltac:(unfold bindings,V293_tcb_update_bindings; simpl; tauto))
    as [_ [P2 [Loc2 W2]]]. fold M2 in P2,Loc2,W2.
  assert (Step3 : forall tail, cstepstar P
    (curs (sassign (efield (ederef (evar ptcb)) 17%Z) (evar xi)),(kenil,tail))
    (ge,le,M2) (curs (sskip None),(kenil,tail)) (ge,le,M3)).
  { intro tail. eapply (proj1 (V293_tcb_update_one_execution P tail ge le M2 ptcb bc bt base
      bindings 17%Z 51%Z xi (V293_prio_bit new) Bind Apart P2 Loc2 W2 eq_refl eq_refl B R
      ltac:(lia) ltac:(unfold bindings,V293_tcb_update_bindings; simpl; tauto))). }
  destruct (V293_tcb_update_one_execution P ks ge le M2 ptcb bc bt base
    bindings 17%Z 51%Z xi (V293_prio_bit new) Bind Apart P2 Loc2 W2 eq_refl eq_refl B R
    ltac:(lia) ltac:(unfold bindings,V293_tcb_update_bindings; simpl; tauto))
    as [_ [P3 [Loc3 W3]]]. fold M3 in P3,Loc3,W3.
  assert (Step4 : forall tail, cstepstar P
    (curs (sassign (efield (ederef (evar ptcb)) 20%Z) (evar byn)),(kenil,tail))
    (ge,le,M3) (curs (sskip None),(kenil,tail)) (ge,le,M4)).
  { intro tail. eapply (proj1 (V293_tcb_update_one_execution P tail ge le M3 ptcb bc bt base
      bindings 20%Z 54%Z byn (2 ^ V293_prio_row new) Bind Apart P3 Loc3 W3 eq_refl eq_refl B R
      ltac:(lia) ltac:(unfold bindings,V293_tcb_update_bindings; simpl; tauto))). }
  destruct (V293_tcb_update_one_execution P ks ge le M3 ptcb bc bt base
    bindings 20%Z 54%Z byn (2 ^ V293_prio_row new) Bind Apart P3 Loc3 W3 eq_refl eq_refl B R
    ltac:(lia) ltac:(unfold bindings,V293_tcb_update_bindings; simpl; tauto))
    as [_ [P4 [Loc4 W4]]]. fold M4 in P4,Loc4,W4.
  destruct (V293_tcb_update_one_execution P ks ge le M4 ptcb bc bt base
    bindings 19%Z 53%Z xn (2 ^ V293_prio_bit new) Bind Apart P4 Loc4 W4 eq_refl eq_refl B R
    ltac:(lia) ltac:(unfold bindings,V293_tcb_update_bindings; simpl; tauto))
    as [Step5 [P5 [Loc5 W5]]].
  cbn zeta. unfold V293_tcb_update_memory. fold M1 M2 M3 M4. split.
  - unfold V293_task_prio_tcb_update.
    eapply V293_rekey_sequence_execution; [exact Step1 | ].
    eapply V293_rekey_sequence_execution; [exact Step2 | ].
    eapply V293_rekey_sequence_execution; [exact Step3 | ].
    eapply V293_rekey_sequence_execution; [exact Step4 | exact Step5].
  - split.
    + unfold V293_tcb_updated_loads,M4,M3,M2,M1.
      destruct (V293_prio_coordinates new N) as [Y X].
      destruct (V293_mask_byte_value (V293_prio_row new) ltac:(lia)) as [BY _].
      destruct (V293_mask_byte_value (V293_prio_bit new) X) as [BX _].
      repeat split; repeat rewrite V293_put_byte_other_load by (intro E; inversion E; lia);
        apply V293_put_byte_load; lia.
    + split; [exact P5 | ]. split; [exact Loc5 | ]. split; [exact W5 | ].
      intros c i Outside. unfold M4,M3,M2,M1.
      repeat rewrite V293_put_byte_other by (intro E; inversion E; subst; clear -Outside; intuition lia).
      reflexivity.
Qed.

Theorem V293_task_prio_prefix_event_update_execution :
  forall P ks ge le M table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi old new entries pevent bp be ebase elo ehi xi bi,
  old < 13 -> new < 13 -> old <> new -> lo < 256 -> hi < 256 -> br <> bg ->
  (0 <= base)%Z -> (base+55 <= Int.max_unsigned)%Z ->
  get le table = None -> get ge table = Some (b,Tarray (Tptr V293_tcb_type) 13) ->
  get le oldprio = Some (bo,Tint8) -> get le newprio = Some (bn,Tint8) ->
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  b <> bo -> b <> bn -> b <> bc -> b <> bt ->
  b <> dy -> b <> dby -> b <> dx -> b <> br -> b <> bg ->
  load Tint8 M (bo,0%Z) = Some (V293_byteval old) ->
  load Tint8 M (bn,0%Z) = Some (V293_byteval new) ->
  load (Tptr V293_tcb_type) M (bc,0%Z) = Some (Vptr (bt,Int.repr base)) ->
  V293_bytes_writable M b (4*Z.of_nat old)%Z 4 ->
  V293_bytes_writable M b (4*Z.of_nat new)%Z 4 ->
  length entries = 13 -> V293_table_loads V293_tcb_type M b entries ->
  get le yo = Some (dy,Tint8) -> get le byo = Some (dby,Tint8) -> get le xo = Some (dx,Tint8) ->
  get le rows = None -> get ge rows = Some (br,Tarray Tint8 2) ->
  get le group = None -> get ge group = Some (bg,Tint8) ->
  dy <> dby -> dy <> dx -> dby <> dx ->
  (forall c, c = dy \/ c = dby \/ c = dx -> c <> bc /\ c <> bt /\ c <> br /\ c <> bg) ->
  V293_tcb_old_loads M bt base (V293_prio_row old)
    (2 ^ V293_prio_row old) (2 ^ V293_prio_bit old) ->
  (exists v, get M (dy,0%Z) = Some (true,v)) ->
  (exists v, get M (dby,0%Z) = Some (true,v)) ->
  (exists v, get M (dx,0%Z) = Some (true,v)) ->
  V293_rekey_bitmap_loads M br bg lo hi (V293_ready_group lo hi) ->
  V293_rekey_bitmap_writable M br bg ->
  V293_rekey_locals ge le M br bg (V293_rekey_new_bindings yn xn byn new) ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> b /\ c <> dy /\ c <> dby /\ c <> dx) ->
  get le pevent = Some (bp,Tptr V293_event_type) ->
  V293_bytes_writable M bp 0%Z 4 ->
  load (Tcom_ptr 411%Z) M (bt,(base+28)%Z) = Some (Vptr (be,Int.repr ebase)) ->
  bc <> br -> bc <> bg -> bt <> br -> bt <> bg ->
  bp <> b -> bp <> dy -> bp <> dby -> bp <> dx -> bp <> br -> bp <> bg ->
  bp <> be ->
  be <> b -> be <> dy -> be <> dby -> be <> dx -> be <> br -> be <> bg ->
  elo < 256 -> ehi < 256 -> (0 <= ebase)%Z -> (ebase+12 <= Int.max_unsigned)%Z ->
  V293_event_bitmap_loads M be ebase elo ehi (V293_ready_group elo ehi) ->
  V293_event_bitmap_writable M be ebase ->
  (forall x v c, In (x,v) (V293_rekey_ready_bindings yo yn xo xn byo byn old new) ->
    get le x = Some (c,Tint8) -> c <> bp /\ c <> be) ->
  bc <> bt -> bc <> bp -> bc <> be -> bt <> bp -> bt <> be ->
  get le xi = Some (bi,Tint8) ->
  load Tint8 M (bi,0%Z) = Some (V293_byteval (V293_prio_bit new)) ->
  (forall c, c = bn \/ c = bi ->
    c <> b /\ c <> dy /\ c <> dby /\ c <> dx /\ c <> br /\ c <> bg /\ c <> bp /\ c <> be /\ c <> bt) ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> bt) ->
  V293_tcb_update_writable M bt base ->
  exists Mg,
  let Mh := V293_tcb_update_memory Mg bt base new in
  let fr := V293_ready_branch_rows lo hi old new in
  let er := V293_ready_rekey_rows elo ehi old new in
  cstepstar P (curs (V293_task_prio_prefix_event_update table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent xi),
    (kenil,ks)) (ge,le,M) (curs (sskip None),(kenil,ks)) (ge,le,Mh) /\
  V293_tcb_updated_loads Mh bt base new /\
  V293_rekey_bitmap_loads Mh br bg (fst fr) (snd fr) (V293_ready_group (fst fr) (snd fr)) /\
  V293_table_loads V293_tcb_type Mh b
    (update_nth_val new (update_nth_val old entries Vnull) (Vptr (bt,Int.repr base))) /\
  load (Tptr V293_tcb_type) Mh (b,(4*Z.of_nat old)%Z) = Some Vnull /\
  load (Tptr V293_tcb_type) Mh (b,(4*Z.of_nat new)%Z) = Some (Vptr (bt,Int.repr base)) /\
  V293_event_bitmap_loads Mh be ebase (fst er) (snd er) (V293_ready_group (fst er) (snd er)) /\
  load (Tptr V293_event_type) Mh (bp,0%Z) = Some (Vptr (be,Int.repr ebase)) /\
  load (Tptr V293_tcb_type) Mh (bc,0%Z) = Some (Vptr (bt,Int.repr base)) /\
  V293_tcb_update_writable Mh bt base /\
  (forall c i, c <> b -> c <> dy -> c <> dby -> c <> dx -> c <> br -> c <> bg -> c <> bp -> c <> be -> c <> bt ->
    get Mh (c,i) = get M (c,i)).
Proof.
  intros P ks ge le M table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi old new entries pevent bp be ebase elo ehi xi bi
    O N ON L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg
    Lo Ln Lp Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields
    Wy Wby Wx Loads W NewLoc NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg PE Eb Ey Eby Ex Er Eg
    EL EH EB ELimit ELoads EW LocalApart CT CP CE TP TE Bi Li ExtraApart NewTcbApart TW.
  destruct (V293_task_prio_prefix_event_nonnull_execution P ks ge le M table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi old new entries pevent bp be ebase elo ehi
    O N ON L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg
    Lo Ln Lp Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields
    Wy Wby Wx Loads W NewLoc NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg PE Eb Ey Eby Ex Er Eg
    EL EH EB ELimit ELoads EW LocalApart)
    as (M1 & M2 & Me & S1 & S2 & Store & Exec & Test & FinalLoads & FinalView & OldSlot & NewSlot & FinalW & FinalLoc & FinalEvent & FinalEW & Read & Frame).
  set (Mr := V293_tcb_read_memory M2 dy dby dx (V293_prio_row old)
    (2 ^ V293_prio_row old) (2 ^ V293_prio_bit old)) in *.
  set (Mf := V293_ready_branch_memory Mr br bg lo hi old new) in *.
  set (Mg := V293_event_rekey_memory Me be ebase elo ehi old new) in *.
  assert (Prefix : forall tail, cstepstar P
    (curs (V293_task_prio_prefix_event table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent),(kenil,tail))
    (ge,le,M) (curs (sskip None),(kenil,tail)) (ge,le,Mg)).
  { intro tail. destruct (V293_task_prio_prefix_event_nonnull_execution P tail ge le M table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi old new entries pevent bp be ebase elo ehi
    O N ON L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg
    Lo Ln Lp Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields
    Wy Wby Wx Loads W NewLoc NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg PE Eb Ey Eby Ex Er Eg
    EL EH EB ELimit ELoads EW LocalApart)
      as (A & B & C & SA & SB & SC & E & _).
    rewrite S1 in SA. inversion SA; subst A. rewrite S2 in SB. inversion SB; subst B.
    change (store (Tptr V293_event_type) Mf (bp,0%Z) (Vptr (be,Int.repr ebase)) = Some C) in SC.
    rewrite Store in SC. inversion SC; subst C. exact E. }
  assert (TC : forall i, get Mg (bt,i) = get M (bt,i)).
  { intro i. apply Frame; try congruence;
      destruct (Apart dy ltac:(auto)) as [_ [A _]];
      destruct (Apart dby ltac:(auto)) as [_ [A' _]];
      destruct (Apart dx ltac:(auto)) as [_ [A'' _]]; congruence. }
  assert (PC : forall i, get Mg (bc,i) = get M (bc,i)).
  { intro i. apply Frame; try congruence;
      destruct (Apart dy ltac:(auto)) as [A _];
      destruct (Apart dby ltac:(auto)) as [A' _];
      destruct (Apart dx ltac:(auto)) as [A'' _]; congruence. }
  assert (ExtraFrame : forall c, c = bn \/ c = bi ->
    forall tp i, load tp Mg (c,i) = load tp M (c,i)).
  { intros c I tp i. destruct (ExtraApart c I) as (A & B & C & D & E & F & G & H' & J).
    apply V293_load_block_frame. intro j. apply Frame; assumption. }
  assert (Hptr : load (Tptr V293_tcb_type) Mg (bc,0%Z) = Some (Vptr (bt,Int.repr base))).
  { rewrite (V293_load_block_frame _ M Mg bc 0%Z PC). exact Lp. }
  assert (WG : V293_tcb_update_writable Mg bt base).
  { intros d D. rewrite TC. exact (TW d D). }
  assert (NewValues : forall x v, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    exists c, get le x = Some (c,Tint8) /\ c <> bt /\ c <> bt /\ load Tint8 Mg (c,0%Z) = Some v).
  { intros x v I. destruct (FinalLoc x v ltac:(clear -I; unfold V293_rekey_new_bindings in I;
      unfold V293_rekey_ready_bindings; simpl in *; tauto)) as (c & Bind & A & B & Load).
    exists c. repeat split; try assumption; eapply NewTcbApart; eassumption. }
  destruct (V293_prio_coordinates new N) as [Yn Xn].
  destruct (V293_mask_byte_value (V293_prio_row new) ltac:(lia)) as [_ BY].
  destruct (V293_mask_byte_value (V293_prio_bit new) Xn) as [_ BX].
  assert (Operands : V293_rekey_locals ge le Mg bt bt (V293_tcb_update_bindings newprio yn xi byn xn new)).
  { intros x v I. cbn [V293_tcb_update_bindings In] in I.
    destruct I as [E|[E|[E|[E|[E|F]]]]]; try contradiction; inversion E; subst x v.
    - exists bn. destruct (ExtraApart bn ltac:(auto)) as (_ & _ & _ & _ & _ & _ & _ & _ & A).
      repeat split; try assumption.
      rewrite ExtraFrame by auto. exact Ln.
    - apply NewValues. unfold V293_rekey_new_bindings; simpl; tauto.
    - exists bi. destruct (ExtraApart bi ltac:(auto)) as (_ & _ & _ & _ & _ & _ & _ & _ & A).
      repeat split; try assumption. rewrite ExtraFrame by auto. exact Li.
    - rewrite BY. apply NewValues. unfold V293_rekey_new_bindings; simpl; tauto.
    - rewrite BX. apply NewValues. unfold V293_rekey_new_bindings; simpl; tauto. }
  destruct (V293_task_prio_tcb_update_execution P ks ge le Mg ptcb newprio yn xi byn xn bc bt base new
    N Base Limit Bc CT Hptr Operands WG)
    as (Suffix & Updated & Pointer & FinalOperands & Writable & TF).
  set (Mh := V293_tcb_update_memory Mg bt base new) in *.
  assert (RF : forall tp c i, c <> bt -> load tp Mh (c,i) = load tp Mg (c,i)).
  { intros tp c i A. apply V293_load_block_frame. intro j. apply TF. left. exact A. }
  exists Mg. cbn zeta. fold Mh. split.
  - unfold V293_task_prio_prefix_event_update. eapply V293_rekey_sequence_execution; eassumption.
  - split; [exact Updated | ]. split.
    + unfold V293_rekey_bitmap_loads in *. repeat rewrite RF by congruence. exact FinalLoads.
    + split; [intros p R; rewrite RF by congruence; exact (FinalView p R) | ].
      split; [rewrite RF by congruence; exact OldSlot | ].
      split; [rewrite RF by congruence; exact NewSlot | ]. split.
      * unfold V293_event_bitmap_loads in *. repeat rewrite RF by congruence. exact FinalEvent.
      * split; [rewrite RF by congruence; exact Read | ].
        split; [exact Pointer | ]. split; [exact Writable | ].
        intros c i A B C D E F G H' J. rewrite TF by auto. apply Frame; assumption.
Qed.

(* All five OLD fields are present at entry; the extra x_new local is 6,
   while bitx_new is 64. No post-state is supplied by this fixture. *)
Definition V293_tcb_update_fixture_le : env :=
  set V293_event_fixture_le 601%Z (73%positive,Tint8).
Definition V293_tcb_update_fixture_mem live elo ehi : mem :=
  V293_put_byte (V293_put_byte (V293_put_byte (V293_put_byte
    (V293_put_byte (V293_put_byte (V293_prefix_event_nonnull_mem live elo ehi)
      (41%positive,58%Z) 8) (41%positive,60%Z) 1)
      (41%positive,59%Z) 0) (41%positive,62%Z) 2)
      (41%positive,61%Z) 1) (73%positive,0%Z) 6.

Lemma V293_tcb_update_fixture_outside : forall live elo ehi c i,
  c <> 73%positive -> c <> 41%positive \/ (i < 58)%Z \/ (62 < i)%Z ->
  get (V293_tcb_update_fixture_mem live elo ehi) (c,i) =
    get (V293_prefix_event_nonnull_mem live elo ehi) (c,i).
Proof.
  intros live elo ehi c i A Outside. unfold V293_tcb_update_fixture_mem.
  repeat rewrite V293_put_byte_other by
    (intro E; inversion E; subst; clear -A Outside; intuition lia). reflexivity.
Qed.
Local Ltac update_fixture_get :=
  unfold V293_tcb_update_fixture_mem;
  repeat first [rewrite V293_put_byte_other by discriminate | rewrite V293_put_byte_get_same].
Local Ltac update_fixture_load :=
  unfold V293_tcb_update_fixture_mem;
  repeat rewrite V293_put_byte_other_load by discriminate;
  apply V293_put_byte_load; lia.
Local Ltac update_fixture_bind :=
  unfold V293_tcb_update_fixture_le;
  repeat first [rewrite map_get_set | rewrite map_get_set' by discriminate];
  try (event_fixture_bind; reflexivity).

Definition V293_tcb_update_observes live elo ehi final_lo final_elo final_ehi final_eg : Prop :=
  forall P ks, exists Mh,
  cstepstar P (curs (V293_task_prio_prefix_event_update 500%Z 501%Z 502%Z 400%Z
    300%Z 301%Z 302%Z 303%Z 304%Z 305%Z 306%Z 307%Z 600%Z 601%Z),(kenil,ks))
    (V293_prefix_fixture_ge,V293_tcb_update_fixture_le,V293_tcb_update_fixture_mem live elo ehi)
    (curs (sskip None),(kenil,ks)) (V293_prefix_fixture_ge,V293_tcb_update_fixture_le,Mh) /\
  load Tint8 Mh (41%positive,58%Z) = Some (V293_byteval 6) /\
  load Tint8 Mh (41%positive,60%Z) = Some (V293_byteval 0) /\
  load Tint8 Mh (41%positive,59%Z) = Some (V293_byteval 6) /\
  load Tint8 Mh (41%positive,62%Z) = Some (V293_byteval 1) /\
  load Tint8 Mh (41%positive,61%Z) = Some (V293_byteval 64) /\
  V293_rekey_bitmap_loads Mh 30%positive 31%positive final_lo 0 1 /\
  V293_event_bitmap_loads Mh 72%positive 5%Z final_elo final_ehi final_eg /\
  V293_table_loads V293_tcb_type Mh 50%positive
    (update_nth_val 6 (update_nth_val 8 V293_prefix_fixture_entries Vnull) (Vptr (41%positive,Int.repr 8))) /\
  load (Tptr V293_tcb_type) Mh (50%positive,32%Z) = Some Vnull /\
  load (Tptr V293_tcb_type) Mh (50%positive,24%Z) = Some (Vptr (41%positive,Int.repr 8)) /\
  load (Tptr V293_event_type) Mh (70%positive,0%Z) = Some (Vptr (72%positive,Int.repr 5)) /\
  load (Tptr V293_tcb_type) Mh (40%positive,0%Z) = Some (Vptr (41%positive,Int.repr 8)).

Theorem V293_tcb_update_continuous_witness : forall live elo ehi,
  elo < 256 -> ehi < 256 ->
  V293_tcb_update_observes live elo ehi (if live then 80 else 16)
    (fst (V293_ready_rekey_rows elo ehi 8 6)) (snd (V293_ready_rekey_rows elo ehi 8 6))
    (V293_ready_group (fst (V293_ready_rekey_rows elo ehi 8 6)) (snd (V293_ready_rekey_rows elo ehi 8 6))).
Proof.
  intros live elo ehi EL EH P ks.
  destruct (V293_prefix_event_nonnull_entry live elo ehi EL EH)
    as (Lp & Event & We & Fields & View & Wo & Wn & Wy & Wby & Wx & Loads & W & NewLoc & Lo & Ln & Initial & ELoads & EW).
  set (M := V293_tcb_update_fixture_mem live elo ehi).
  assert (RF : forall tp c i, c <> 41%positive -> c <> 73%positive ->
    load tp M (c,i) = load tp (V293_prefix_event_nonnull_mem live elo ehi) (c,i)).
  { intros tp c i A B. apply V293_load_block_frame. intro j.
    apply V293_tcb_update_fixture_outside; [exact B | left; exact A]. }
  assert (Hptr : load (Tptr V293_tcb_type) M (40%positive,0%Z) = Some (Vptr (41%positive,Int.repr 8))).
  { rewrite RF by discriminate. exact Lp. }
  assert (HEvent : load (Tcom_ptr 411%Z) M (41%positive,36%Z) = Some (Vptr (72%positive,Int.repr 5))).
  { unfold load,loadm. rewrite (V293_loadbytes_ext _ (V293_prefix_event_nonnull_mem live elo ehi) M).
    - exact Event.
    - intros k K. cbn [typelen] in K.
      apply V293_tcb_update_fixture_outside; [discriminate | right; left; lia]. }
  assert (HFields : V293_tcb_old_loads M 41%positive 8%Z 1 2 1).
  { unfold V293_tcb_old_loads,M. repeat split; update_fixture_load. }
  assert (HView : V293_table_loads V293_tcb_type M 50%positive V293_prefix_fixture_entries).
  { intros p R. rewrite RF by discriminate. exact (View p R). }
  assert (HWo : V293_bytes_writable M 50%positive 32%Z 4).
  { intros k K. unfold M; rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact (Wo k K). }
  assert (HWn : V293_bytes_writable M 50%positive 24%Z 4).
  { intros k K. unfold M; rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact (Wn k K). }
  assert (HWe : V293_bytes_writable M 70%positive 0%Z 4).
  { intros k K. unfold M; rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact (We k K). }
  assert (HWy : exists v, get M (32%positive,0%Z) = Some (true,v)).
  { unfold M; rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact Wy. }
  assert (HWby : exists v, get M (36%positive,0%Z) = Some (true,v)).
  { unfold M; rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact Wby. }
  assert (HWx : exists v, get M (34%positive,0%Z) = Some (true,v)).
  { unfold M; rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact Wx. }
  assert (HLoads : V293_rekey_bitmap_loads M 30%positive 31%positive 16 (if live then 1 else 0)
    (V293_ready_group 16 (if live then 1 else 0))).
  { unfold V293_rekey_bitmap_loads in *. repeat rewrite RF by discriminate. exact Loads. }
  assert (HW : V293_rekey_bitmap_writable M 30%positive 31%positive).
  { unfold V293_rekey_bitmap_writable in *.
    unfold M; repeat rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact W. }
  assert (HELoads : V293_event_bitmap_loads M 72%positive 5%Z elo ehi (V293_ready_group elo ehi)).
  { unfold V293_event_bitmap_loads in *. repeat rewrite RF by discriminate. exact ELoads. }
  assert (HEW : V293_event_bitmap_writable M 72%positive 5%Z).
  { unfold V293_event_bitmap_writable in *.
    unfold M; repeat rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact EW. }
  assert (HNewLoc : V293_rekey_locals V293_prefix_fixture_ge V293_tcb_update_fixture_le M
    30%positive 31%positive (V293_rekey_new_bindings 303%Z 305%Z 307%Z 6)).
  { intros x v I. destruct (NewLoc x v I) as (c & Bind & A & B & Read).
    cbn [V293_rekey_new_bindings In] in I.
    destruct I as [E|[E|[E|F]]]; try contradiction; inversion E; subst x v;
      unfold V293_event_fixture_le,V293_prefix_fixture_le,V293_read_ready_fixture_le,V293_ready_fragment_fixture_le in Bind;
      repeat first [rewrite map_get_set in Bind | rewrite map_get_set' in Bind by discriminate];
      inversion Bind; subst c.
    all: eexists; split; [update_fixture_bind; reflexivity | ];
      split; [discriminate | ]; split; [discriminate | ]; rewrite RF by discriminate; exact Read. }
  assert (HLo : load Tint8 M (51%positive,0%Z) = Some (V293_byteval 8)).
  { rewrite RF by discriminate. exact Lo. }
  assert (HLn : load Tint8 M (52%positive,0%Z) = Some (V293_byteval 6)).
  { rewrite RF by discriminate. exact Ln. }
  assert (HLi : load Tint8 M (73%positive,0%Z) = Some (V293_byteval 6)).
  { unfold M. update_fixture_load. }
  assert (HTW : V293_tcb_update_writable M 41%positive 8%Z).
  { intros d D. assert (d=50 \/ d=51 \/ d=52 \/ d=53 \/ d=54)%Z by lia.
    destruct H as [-> | [-> | [-> | [-> | ->]]]]; unfold M;
      eexists; update_fixture_get; reflexivity. }
  destruct (V293_task_prio_prefix_event_update_execution P ks V293_prefix_fixture_ge V293_tcb_update_fixture_le
    M 500%Z 501%Z 502%Z 400%Z 300%Z 301%Z 302%Z 303%Z 304%Z 305%Z 306%Z 307%Z
    50%positive 51%positive 52%positive 40%positive 41%positive 32%positive 36%positive 34%positive
    8%Z 30%positive 31%positive 16 (if live then 1 else 0) 8 6 V293_prefix_fixture_entries
    600%Z 70%positive 72%positive 5%Z elo ehi 601%Z 73%positive)
    as (Mg & Exec & Updated & FinalLoads & FinalView & OldSlot & NewSlot & FinalEvent & Read & Pointer & TW & Frame).
  all: try assumption; try discriminate; try (update_fixture_bind; reflexivity);
    try (change (0 <= 8)%Z; lia); try (change (8+55 <= 4294967295)%Z; lia);
    try (change (0 <= 5)%Z; lia); try (change (5+12 <= 4294967295)%Z; lia);
    try (change (8<13); lia); try (change (6<13); lia); try (change (16<256); lia);
    try (destruct live; lia); try (change (length V293_prefix_fixture_entries = 13); reflexivity).
  - intros x v c I Bind. cbn [V293_rekey_new_bindings In] in I.
    destruct I as [E|[E|[E|F]]]; try contradiction; inversion E; subst x v;
      unfold V293_tcb_update_fixture_le,V293_event_fixture_le,V293_prefix_fixture_le,V293_read_ready_fixture_le,V293_ready_fragment_fixture_le in Bind;
      repeat first [rewrite map_get_set in Bind | rewrite map_get_set' in Bind by discriminate];
      inversion Bind; subst c; repeat split; discriminate.
  - intros x v c I Bind. cbn [V293_rekey_ready_bindings In] in I.
    destruct I as [E|[E|[E|[E|[E|[E|F]]]]]]; try contradiction; inversion E; subst x v;
      unfold V293_tcb_update_fixture_le,V293_event_fixture_le,V293_prefix_fixture_le,V293_read_ready_fixture_le,V293_ready_fragment_fixture_le in Bind;
      repeat first [rewrite map_get_set in Bind | rewrite map_get_set' in Bind by discriminate];
      inversion Bind; subst c; split; discriminate.
  - intros x v c I Bind. cbn [V293_rekey_new_bindings In] in I.
    destruct I as [E|[E|[E|F]]]; try contradiction; inversion E; subst x v;
      unfold V293_tcb_update_fixture_le,V293_event_fixture_le,V293_prefix_fixture_le,V293_read_ready_fixture_le,V293_ready_fragment_fixture_le in Bind;
      repeat first [rewrite map_get_set in Bind | rewrite map_get_set' in Bind by discriminate];
      inversion Bind; subst c; discriminate.
  - eexists. split; [exact Exec | ]. unfold V293_tcb_updated_loads in Updated.
    destruct Updated as (Prio & Y & X & BY & BX).
    split; [exact Prio | ]. split; [exact Y | ]. split; [exact X | ].
    split; [exact BY | ]. split; [exact BX | ].
    split; [destruct live; exact FinalLoads | ]. split; [exact FinalEvent | ].
    split; [exact FinalView | ]. split; [exact OldSlot | ]. split; [exact NewSlot | ]. split; assumption.
Qed.

Theorem V293_tcb_update_continuous_controls :
  V293_tcb_update_observes false 0 1 16 64 0 1 /\
  V293_tcb_update_observes true 0 1 80 64 0 1 /\
  V293_tcb_update_observes false 16 3 16 80 2 3 /\
  V293_tcb_update_observes false 0 129 16 64 128 3.
Proof.
  split; [exact (V293_tcb_update_continuous_witness false 0 1 ltac:(lia) ltac:(lia)) | ].
  split; [exact (V293_tcb_update_continuous_witness true 0 1 ltac:(lia) ltac:(lia)) | ].
  split; [exact (V293_tcb_update_continuous_witness false 16 3 ltac:(lia) ltac:(lia)) | ].
  exact (V293_tcb_update_continuous_witness false 0 129 ltac:(lia) ltac:(lia)).
Qed.

(* The same program's NULL branch still performs the five TCB assignments.
   All suffix resources are derived from the original entry, not assumed. *)
Theorem V293_task_prio_prefix_null_update_execution :
  forall P ks ge le M table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi old new entries pevent bp xi bi,
  old < 13 -> new < 13 -> old <> new -> lo < 256 -> hi < 256 -> br <> bg ->
  (0 <= base)%Z -> (base+55 <= Int.max_unsigned)%Z ->
  get le table = None -> get ge table = Some (b,Tarray (Tptr V293_tcb_type) 13) ->
  get le oldprio = Some (bo,Tint8) -> get le newprio = Some (bn,Tint8) ->
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  b <> bo -> b <> bn -> b <> bc -> b <> bt ->
  b <> dy -> b <> dby -> b <> dx -> b <> br -> b <> bg ->
  load Tint8 M (bo,0%Z) = Some (V293_byteval old) ->
  load Tint8 M (bn,0%Z) = Some (V293_byteval new) ->
  load (Tptr V293_tcb_type) M (bc,0%Z) = Some (Vptr (bt,Int.repr base)) ->
  V293_bytes_writable M b (4*Z.of_nat old)%Z 4 ->
  V293_bytes_writable M b (4*Z.of_nat new)%Z 4 ->
  length entries = 13 -> V293_table_loads V293_tcb_type M b entries ->
  get le yo = Some (dy,Tint8) -> get le byo = Some (dby,Tint8) -> get le xo = Some (dx,Tint8) ->
  get le rows = None -> get ge rows = Some (br,Tarray Tint8 2) ->
  get le group = None -> get ge group = Some (bg,Tint8) ->
  dy <> dby -> dy <> dx -> dby <> dx ->
  (forall c, c = dy \/ c = dby \/ c = dx -> c <> bc /\ c <> bt /\ c <> br /\ c <> bg) ->
  V293_tcb_old_loads M bt base (V293_prio_row old)
    (2 ^ V293_prio_row old) (2 ^ V293_prio_bit old) ->
  (exists v, get M (dy,0%Z) = Some (true,v)) ->
  (exists v, get M (dby,0%Z) = Some (true,v)) ->
  (exists v, get M (dx,0%Z) = Some (true,v)) ->
  V293_rekey_bitmap_loads M br bg lo hi (V293_ready_group lo hi) ->
  V293_rekey_bitmap_writable M br bg ->
  V293_rekey_locals ge le M br bg (V293_rekey_new_bindings yn xn byn new) ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> b /\ c <> dy /\ c <> dby /\ c <> dx) ->
  get le pevent = Some (bp,Tptr V293_event_type) ->
  V293_bytes_writable M bp 0%Z 4 ->
  load (Tcom_ptr 411%Z) M (bt,(base+28)%Z) = Some Vnull ->
  bc <> br -> bc <> bg -> bt <> br -> bt <> bg ->
  bp <> b -> bp <> dy -> bp <> dby -> bp <> dx -> bp <> br -> bp <> bg ->
  bc <> bt -> bc <> bp -> bt <> bp ->
  get le xi = Some (bi,Tint8) ->
  load Tint8 M (bi,0%Z) = Some (V293_byteval (V293_prio_bit new)) ->
  (forall c, c = bn \/ c = bi ->
    c <> b /\ c <> dy /\ c <> dby /\ c <> dx /\ c <> br /\ c <> bg /\ c <> bp /\ c <> bt) ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> bp /\ c <> bt) ->
  V293_tcb_update_writable M bt base ->
  exists Me,
  let Mh := V293_tcb_update_memory Me bt base new in
  let fr := V293_ready_branch_rows lo hi old new in
  cstepstar P (curs (V293_task_prio_prefix_event_update table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent xi),
    (kenil,ks)) (ge,le,M) (curs (sskip None),(kenil,ks)) (ge,le,Mh) /\
  V293_tcb_updated_loads Mh bt base new /\
  V293_rekey_bitmap_loads Mh br bg (fst fr) (snd fr) (V293_ready_group (fst fr) (snd fr)) /\
  V293_table_loads V293_tcb_type Mh b
    (update_nth_val new (update_nth_val old entries Vnull) (Vptr (bt,Int.repr base))) /\
  load (Tptr V293_tcb_type) Mh (b,(4*Z.of_nat old)%Z) = Some Vnull /\
  load (Tptr V293_tcb_type) Mh (b,(4*Z.of_nat new)%Z) = Some (Vptr (bt,Int.repr base)) /\
  load (Tptr V293_event_type) Mh (bp,0%Z) = Some Vnull /\
  load (Tptr V293_tcb_type) Mh (bc,0%Z) = Some (Vptr (bt,Int.repr base)) /\
  load (Tcom_ptr 411%Z) Mh (bt,(base+28)%Z) = Some Vnull /\
  (forall i, (i < base+50)%Z \/ (base+54 < i)%Z -> get Mh (bt,i) = get M (bt,i)) /\
  (forall c i, c <> b -> c <> dy -> c <> dby -> c <> dx -> c <> br -> c <> bg -> c <> bp -> c <> bt ->
    get Mh (c,i) = get M (c,i)).
Proof.
  intros P ks ge le M table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi old new entries pevent bp xi bi
    O N ON L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg
    Lo Ln Lp Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields
    Wy Wby Wx Loads W NewLoc NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg
    CT CP TP Bi Li ExtraApart NewTcbApart TW.
  destruct (V293_task_prio_prefix_event_null_execution P ks ge le M table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi old new entries pevent bp
    O N ON L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg
    Lo Ln Lp Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields
    Wy Wby Wx Loads W NewLoc NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg)
    as (M1 & M2 & Me & S1 & S2 & Store & Read & Exec & Test & FinalLoads & FinalView & OldSlot & NewSlot & FinalW & FinalLoc & Frame).
  set (Mr := V293_tcb_read_memory M2 dy dby dx (V293_prio_row old)
    (2 ^ V293_prio_row old) (2 ^ V293_prio_bit old)) in *.
  set (Mf := V293_ready_branch_memory Mr br bg lo hi old new) in *.
  assert (Prefix : forall tail, cstepstar P
    (curs (V293_task_prio_prefix_event table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent),(kenil,tail))
    (ge,le,M) (curs (sskip None),(kenil,tail)) (ge,le,Me)).
  { intro tail. destruct (V293_task_prio_prefix_event_null_execution P tail ge le M table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi old new entries pevent bp
    O N ON L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg
    Lo Ln Lp Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields
    Wy Wby Wx Loads W NewLoc NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg)
      as (A & B & C & SA & SB & SC & _ & E & _).
    rewrite S1 in SA. inversion SA; subst A. rewrite S2 in SB. inversion SB; subst B.
    change (store (Tptr V293_event_type) Mf (bp,0%Z) Vnull = Some C) in SC.
    rewrite Store in SC. inversion SC; subst C. exact E. }
  assert (TC : forall i, get Me (bt,i) = get M (bt,i)).
  { intro i. apply Frame; try congruence;
      destruct (Apart dy ltac:(auto)) as [_ [A _]];
      destruct (Apart dby ltac:(auto)) as [_ [A' _]];
      destruct (Apart dx ltac:(auto)) as [_ [A'' _]]; congruence. }
  assert (PC : forall i, get Me (bc,i) = get M (bc,i)).
  { intro i. apply Frame; try congruence;
      destruct (Apart dy ltac:(auto)) as [A _];
      destruct (Apart dby ltac:(auto)) as [A' _];
      destruct (Apart dx ltac:(auto)) as [A'' _]; congruence. }
  assert (ExtraFrame : forall c, c = bn \/ c = bi ->
    forall tp i, load tp Me (c,i) = load tp M (c,i)).
  { intros c I tp i. destruct (ExtraApart c I) as (A & B & C & D & E & F & G & J).
    apply V293_load_block_frame. intro j. apply Frame; assumption. }
  assert (EF : forall tp c i, c <> bp -> load tp Me (c,i) = load tp Mf (c,i)).
  { intros tp c i A. apply V293_load_block_frame. intro j.
    eapply V293_storebytes_outside; [exact Store | left; exact A]. }
  assert (Hptr : load (Tptr V293_tcb_type) Me (bc,0%Z) = Some (Vptr (bt,Int.repr base))).
  { rewrite (V293_load_block_frame _ M Me bc 0%Z PC). exact Lp. }
  assert (WG : V293_tcb_update_writable Me bt base).
  { intros d D. rewrite TC. exact (TW d D). }
  assert (NewValues : forall x v, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    exists c, get le x = Some (c,Tint8) /\ c <> bt /\ c <> bt /\ load Tint8 Me (c,0%Z) = Some v).
  { intros x v I. destruct (FinalLoc x v ltac:(clear -I; unfold V293_rekey_new_bindings in I;
      unfold V293_rekey_ready_bindings; simpl in *; tauto)) as (c & Bind & A & B & Load).
    destruct (NewTcbApart x v c I Bind) as [C D].
    exists c. repeat split; try assumption. rewrite EF by exact C. exact Load. }
  destruct (V293_prio_coordinates new N) as [Yn Xn].
  destruct (V293_mask_byte_value (V293_prio_row new) ltac:(lia)) as [_ BY].
  destruct (V293_mask_byte_value (V293_prio_bit new) Xn) as [_ BX].
  assert (Operands : V293_rekey_locals ge le Me bt bt (V293_tcb_update_bindings newprio yn xi byn xn new)).
  { intros x v I. cbn [V293_tcb_update_bindings In] in I.
    destruct I as [E|[E|[E|[E|[E|F]]]]]; try contradiction; inversion E; subst x v.
    - exists bn. destruct (ExtraApart bn ltac:(auto)) as (_ & _ & _ & _ & _ & _ & _ & A).
      repeat split; try assumption. rewrite ExtraFrame by auto. exact Ln.
    - apply NewValues. unfold V293_rekey_new_bindings; simpl; tauto.
    - exists bi. destruct (ExtraApart bi ltac:(auto)) as (_ & _ & _ & _ & _ & _ & _ & A).
      repeat split; try assumption. rewrite ExtraFrame by auto. exact Li.
    - rewrite BY. apply NewValues. unfold V293_rekey_new_bindings; simpl; tauto.
    - rewrite BX. apply NewValues. unfold V293_rekey_new_bindings; simpl; tauto. }
  destruct (V293_task_prio_tcb_update_execution P ks ge le Me ptcb newprio yn xi byn xn bc bt base new
    N Base Limit Bc CT Hptr Operands WG)
    as (Suffix & Updated & Pointer & FinalOperands & Writable & TF).
  set (Mh := V293_tcb_update_memory Me bt base new) in *.
  assert (RF : forall tp c i, c <> bt -> load tp Mh (c,i) = load tp Me (c,i)).
  { intros tp c i A. apply V293_load_block_frame. intro j. apply TF. left. exact A. }
  assert (Untouched : forall i, (i < base+50)%Z \/ (base+54 < i)%Z -> get Mh (bt,i) = get M (bt,i)).
  { intros i I. rewrite TF by (right; exact I). apply TC. }
  assert (FinalEvent : load (Tcom_ptr 411%Z) Mh (bt,(base+28)%Z) = Some Vnull).
  { unfold load,loadm. rewrite (V293_loadbytes_ext _ M Mh).
    - exact Event.
    - intros k K. cbn [typelen] in K. apply Untouched. left. lia. }
  exists Me. cbn zeta. fold Mh. split.
  - unfold V293_task_prio_prefix_event_update. eapply V293_rekey_sequence_execution; eassumption.
  - split; [exact Updated | ]. split.
    + unfold V293_rekey_bitmap_loads in *. repeat rewrite RF by congruence. exact FinalLoads.
    + split; [intros p R; rewrite RF by congruence; exact (FinalView p R) | ].
      split; [rewrite RF by congruence; exact OldSlot | ].
      split; [rewrite RF by congruence; exact NewSlot | ].
      split; [rewrite RF by congruence; exact Read | ].
      split; [exact Pointer | ]. split; [exact FinalEvent | ].
      split; [exact Untouched | ].
      intros c i A B C D E F G J. rewrite TF by auto. apply Frame; assumption.
Qed.

(* One field changes relative to the preceding non-null physical entry. *)
Definition V293_null_update_fixture_mem live elo ehi : mem :=
  V293_fixture_put_bytes (V293_tcb_update_fixture_mem live elo ehi)
    41%positive 36%Z (encode_val (Tcom_ptr 411%Z) Vnull).
Lemma V293_null_update_fixture_outside : forall live elo ehi c i,
  c <> 41%positive \/ (i < 36)%Z \/ (40 <= i)%Z ->
  get (V293_null_update_fixture_mem live elo ehi) (c,i) =
    get (V293_tcb_update_fixture_mem live elo ehi) (c,i).
Proof.
  intros live elo ehi c i R. unfold V293_null_update_fixture_mem.
  apply V293_fixture_bytes_outside. rewrite encode_val_length. exact R.
Qed.
Definition V293_null_update_observes live elo ehi final_lo : Prop :=
  forall P ks, exists Mh,
  cstepstar P (curs (V293_task_prio_prefix_event_update 500%Z 501%Z 502%Z 400%Z
    300%Z 301%Z 302%Z 303%Z 304%Z 305%Z 306%Z 307%Z 600%Z 601%Z),(kenil,ks))
    (V293_prefix_fixture_ge,V293_tcb_update_fixture_le,V293_null_update_fixture_mem live elo ehi)
    (curs (sskip None),(kenil,ks)) (V293_prefix_fixture_ge,V293_tcb_update_fixture_le,Mh) /\
  V293_tcb_updated_loads Mh 41%positive 8%Z 6 /\
  V293_rekey_bitmap_loads Mh 30%positive 31%positive final_lo 0 1 /\
  V293_table_loads V293_tcb_type Mh 50%positive
    (update_nth_val 6 (update_nth_val 8 V293_prefix_fixture_entries Vnull) (Vptr (41%positive,Int.repr 8))) /\
  load (Tptr V293_tcb_type) Mh (50%positive,32%Z) = Some Vnull /\
  load (Tptr V293_tcb_type) Mh (50%positive,24%Z) = Some (Vptr (41%positive,Int.repr 8)) /\
  load (Tptr V293_event_type) Mh (70%positive,0%Z) = Some Vnull /\
  load (Tptr V293_tcb_type) Mh (40%positive,0%Z) = Some (Vptr (41%positive,Int.repr 8)) /\
  load (Tcom_ptr 411%Z) Mh (41%positive,36%Z) = Some Vnull /\
  (forall i, (i < 58)%Z \/ (62 < i)%Z ->
    get Mh (41%positive,i) = get (V293_null_update_fixture_mem live elo ehi) (41%positive,i)) /\
  (forall i, get Mh (72%positive,i) = get (V293_tcb_update_fixture_mem live elo ehi) (72%positive,i)).

Theorem V293_null_update_continuous_witness : forall live elo ehi,
  elo < 256 -> ehi < 256 ->
  V293_null_update_observes live elo ehi (if live then 80 else 16).
Proof.

  intros live elo ehi EL EH P ks.
  destruct (V293_prefix_event_nonnull_entry live elo ehi EL EH)
    as (Lp & Event & We & Fields & View & Wo & Wn & Wy & Wby & Wx & Loads & W & NewLoc & Lo & Ln & Initial & ELoads & EW).
  set (M := V293_null_update_fixture_mem live elo ehi).
  assert (RF : forall tp c i, c <> 41%positive -> c <> 73%positive ->
    load tp M (c,i) = load tp (V293_prefix_event_nonnull_mem live elo ehi) (c,i)).
  { intros tp c i A B. apply V293_load_block_frame. intro j.
    unfold M. rewrite V293_null_update_fixture_outside by (left; exact A).
    apply V293_tcb_update_fixture_outside; [exact B | left; exact A]. }
  assert (Hptr : load (Tptr V293_tcb_type) M (40%positive,0%Z) = Some (Vptr (41%positive,Int.repr 8))).
  { rewrite RF by discriminate. exact Lp. }
  assert (HEvent : load (Tcom_ptr 411%Z) M (41%positive,36%Z) = Some Vnull).
  { unfold M,V293_null_update_fixture_mem. apply V293_fixture_encoded_load. reflexivity. }
  assert (HighByte : forall i, (40 <= i)%Z ->
    load Tint8 M (41%positive,i) = load Tint8 (V293_tcb_update_fixture_mem live elo ehi) (41%positive,i)).
  { intros i I. unfold load,loadm.
    rewrite (V293_loadbytes_ext _ (V293_tcb_update_fixture_mem live elo ehi) M).
    - reflexivity.
    - intros k K. unfold M. apply V293_null_update_fixture_outside. right; right. lia. }
  assert (HFields : V293_tcb_old_loads M 41%positive 8%Z 1 2 1).
  { unfold V293_tcb_old_loads. repeat split; rewrite HighByte by lia; update_fixture_load. }
  assert (HView : V293_table_loads V293_tcb_type M 50%positive V293_prefix_fixture_entries).
  { intros p R. rewrite RF by discriminate. exact (View p R). }
  assert (HWo : V293_bytes_writable M 50%positive 32%Z 4).
  { intros k K. unfold M; rewrite V293_null_update_fixture_outside by (left; discriminate); rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact (Wo k K). }
  assert (HWn : V293_bytes_writable M 50%positive 24%Z 4).
  { intros k K. unfold M; rewrite V293_null_update_fixture_outside by (left; discriminate); rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact (Wn k K). }
  assert (HWe : V293_bytes_writable M 70%positive 0%Z 4).
  { intros k K. unfold M; rewrite V293_null_update_fixture_outside by (left; discriminate); rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact (We k K). }
  assert (HWy : exists v, get M (32%positive,0%Z) = Some (true,v)).
  { unfold M; rewrite V293_null_update_fixture_outside by (left; discriminate); rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact Wy. }
  assert (HWby : exists v, get M (36%positive,0%Z) = Some (true,v)).
  { unfold M; rewrite V293_null_update_fixture_outside by (left; discriminate); rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact Wby. }
  assert (HWx : exists v, get M (34%positive,0%Z) = Some (true,v)).
  { unfold M; rewrite V293_null_update_fixture_outside by (left; discriminate); rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact Wx. }
  assert (HLoads : V293_rekey_bitmap_loads M 30%positive 31%positive 16 (if live then 1 else 0)
    (V293_ready_group 16 (if live then 1 else 0))).
  { unfold V293_rekey_bitmap_loads in *. repeat rewrite RF by discriminate. exact Loads. }
  assert (HW : V293_rekey_bitmap_writable M 30%positive 31%positive).
  { unfold V293_rekey_bitmap_writable in *.
    unfold M; repeat rewrite V293_null_update_fixture_outside by (left; discriminate); repeat rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact W. }
  assert (HNewLoc : V293_rekey_locals V293_prefix_fixture_ge V293_tcb_update_fixture_le M
    30%positive 31%positive (V293_rekey_new_bindings 303%Z 305%Z 307%Z 6)).
  { intros x v I. destruct (NewLoc x v I) as (c & Bind & A & B & Read).
    cbn [V293_rekey_new_bindings In] in I.
    destruct I as [E|[E|[E|F]]]; try contradiction; inversion E; subst x v;
      unfold V293_event_fixture_le,V293_prefix_fixture_le,V293_read_ready_fixture_le,V293_ready_fragment_fixture_le in Bind;
      repeat first [rewrite map_get_set in Bind | rewrite map_get_set' in Bind by discriminate];
      inversion Bind; subst c.
    all: eexists; split; [update_fixture_bind; reflexivity | ];
      split; [discriminate | ]; split; [discriminate | ]; rewrite RF by discriminate; exact Read. }
  assert (HLo : load Tint8 M (51%positive,0%Z) = Some (V293_byteval 8)).
  { rewrite RF by discriminate. exact Lo. }
  assert (HLn : load Tint8 M (52%positive,0%Z) = Some (V293_byteval 6)).
  { rewrite RF by discriminate. exact Ln. }
  assert (HLi : load Tint8 M (73%positive,0%Z) = Some (V293_byteval 6)).
  { unfold M. rewrite (V293_load_block_frame Tint8 (V293_tcb_update_fixture_mem live elo ehi) _ 73%positive 0%Z).
    - update_fixture_load.
    - intro i. apply V293_null_update_fixture_outside. left. discriminate. }
  assert (HTW : V293_tcb_update_writable M 41%positive 8%Z).
  { intros d D. assert (d=50 \/ d=51 \/ d=52 \/ d=53 \/ d=54)%Z by lia.
    destruct H as [-> | [-> | [-> | [-> | ->]]]]; unfold M;
      eexists; rewrite V293_null_update_fixture_outside by (right; right; lia); update_fixture_get; reflexivity. }
  destruct (V293_task_prio_prefix_null_update_execution P ks V293_prefix_fixture_ge V293_tcb_update_fixture_le
    M 500%Z 501%Z 502%Z 400%Z 300%Z 301%Z 302%Z 303%Z 304%Z 305%Z 306%Z 307%Z
    50%positive 51%positive 52%positive 40%positive 41%positive 32%positive 36%positive 34%positive
    8%Z 30%positive 31%positive 16 (if live then 1 else 0) 8 6 V293_prefix_fixture_entries
    600%Z 70%positive 601%Z 73%positive)
    as (Me & Exec & Updated & FinalLoads & FinalView & OldSlot & NewSlot & Read & Pointer & FinalEvent & Untouched & Frame).
  all: try assumption; try discriminate; try (update_fixture_bind; reflexivity);
    try (change (0 <= 8)%Z; lia); try (change (8+55 <= 4294967295)%Z; lia);
    try (change (8<13); lia); try (change (6<13); lia); try (change (16<256); lia);
    try (destruct live; lia); try (change (length V293_prefix_fixture_entries = 13); reflexivity).
  - intros x v c I Bind. cbn [V293_rekey_new_bindings In] in I.
    destruct I as [E|[E|[E|F]]]; try contradiction; inversion E; subst x v;
      unfold V293_tcb_update_fixture_le,V293_event_fixture_le,V293_prefix_fixture_le,V293_read_ready_fixture_le,V293_ready_fragment_fixture_le in Bind;
      repeat first [rewrite map_get_set in Bind | rewrite map_get_set' in Bind by discriminate];
      inversion Bind; subst c; repeat split; discriminate.
  - intros x v c I Bind. cbn [V293_rekey_new_bindings In] in I.
    destruct I as [E|[E|[E|F]]]; try contradiction; inversion E; subst x v;
      unfold V293_tcb_update_fixture_le,V293_event_fixture_le,V293_prefix_fixture_le,V293_read_ready_fixture_le,V293_ready_fragment_fixture_le in Bind;
      repeat first [rewrite map_get_set in Bind | rewrite map_get_set' in Bind by discriminate];
      inversion Bind; subst c; split; discriminate.
  - eexists. split; [exact Exec | ]. split; [exact Updated | ].
    split; [destruct live; exact FinalLoads | ]. split; [exact FinalView | ].
    split; [exact OldSlot | ]. split; [exact NewSlot | ]. split; [exact Read | ].
    split; [exact Pointer | ]. split; [exact FinalEvent | ]. split; [exact Untouched | ].
    intro i. rewrite Frame by discriminate. unfold M. apply V293_null_update_fixture_outside. left. discriminate.
Qed.

Theorem V293_null_update_entry_delta : forall live elo ehi,
  load (Tcom_ptr 411%Z) (V293_null_update_fixture_mem live elo ehi)
    (41%positive,36%Z) = Some Vnull /\
  (forall c i, c <> 41%positive \/ (i < 36)%Z \/ (40 <= i)%Z ->
    get (V293_null_update_fixture_mem live elo ehi) (c,i) =
    get (V293_tcb_update_fixture_mem live elo ehi) (c,i)).
Proof.
  intros live elo ehi. split.
  - unfold V293_null_update_fixture_mem. apply V293_fixture_encoded_load. reflexivity.
  - intros. apply V293_null_update_fixture_outside. assumption.
Qed.

Theorem V293_null_update_branch_controls :
  V293_null_update_observes false 0 1 16 /\
  V293_null_update_observes true 0 1 80 /\
  V293_tcb_update_observes false 0 1 16 64 0 1.
Proof.
  split; [exact (V293_null_update_continuous_witness false 0 1 ltac:(lia) ltac:(lia)) | ].
  split; [exact (V293_null_update_continuous_witness true 0 1 ltac:(lia) ltac:(lia)) | ].
  exact (V293_tcb_update_continuous_witness false 0 1 ltac:(lia) ltac:(lia)).
Qed.

(* Stronger non-null interface: internal TCB fields are not local pevent. *)
Theorem V293_task_prio_prefix_event_update_preserves :
  forall P ks ge le M table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi old new entries pevent bp be ebase elo ehi xi bi,
  old < 13 -> new < 13 -> old <> new -> lo < 256 -> hi < 256 -> br <> bg ->
  (0 <= base)%Z -> (base+55 <= Int.max_unsigned)%Z ->
  get le table = None -> get ge table = Some (b,Tarray (Tptr V293_tcb_type) 13) ->
  get le oldprio = Some (bo,Tint8) -> get le newprio = Some (bn,Tint8) ->
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  b <> bo -> b <> bn -> b <> bc -> b <> bt ->
  b <> dy -> b <> dby -> b <> dx -> b <> br -> b <> bg ->
  load Tint8 M (bo,0%Z) = Some (V293_byteval old) ->
  load Tint8 M (bn,0%Z) = Some (V293_byteval new) ->
  load (Tptr V293_tcb_type) M (bc,0%Z) = Some (Vptr (bt,Int.repr base)) ->
  V293_bytes_writable M b (4*Z.of_nat old)%Z 4 ->
  V293_bytes_writable M b (4*Z.of_nat new)%Z 4 ->
  length entries = 13 -> V293_table_loads V293_tcb_type M b entries ->
  get le yo = Some (dy,Tint8) -> get le byo = Some (dby,Tint8) -> get le xo = Some (dx,Tint8) ->
  get le rows = None -> get ge rows = Some (br,Tarray Tint8 2) ->
  get le group = None -> get ge group = Some (bg,Tint8) ->
  dy <> dby -> dy <> dx -> dby <> dx ->
  (forall c, c = dy \/ c = dby \/ c = dx -> c <> bc /\ c <> bt /\ c <> br /\ c <> bg) ->
  V293_tcb_old_loads M bt base (V293_prio_row old)
    (2 ^ V293_prio_row old) (2 ^ V293_prio_bit old) ->
  (exists v, get M (dy,0%Z) = Some (true,v)) ->
  (exists v, get M (dby,0%Z) = Some (true,v)) ->
  (exists v, get M (dx,0%Z) = Some (true,v)) ->
  V293_rekey_bitmap_loads M br bg lo hi (V293_ready_group lo hi) ->
  V293_rekey_bitmap_writable M br bg ->
  V293_rekey_locals ge le M br bg (V293_rekey_new_bindings yn xn byn new) ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> b /\ c <> dy /\ c <> dby /\ c <> dx) ->
  get le pevent = Some (bp,Tptr V293_event_type) ->
  V293_bytes_writable M bp 0%Z 4 ->
  load (Tcom_ptr 411%Z) M (bt,(base+28)%Z) = Some (Vptr (be,Int.repr ebase)) ->
  bc <> br -> bc <> bg -> bt <> br -> bt <> bg ->
  bp <> b -> bp <> dy -> bp <> dby -> bp <> dx -> bp <> br -> bp <> bg ->
  bp <> be ->
  be <> b -> be <> dy -> be <> dby -> be <> dx -> be <> br -> be <> bg ->
  elo < 256 -> ehi < 256 -> (0 <= ebase)%Z -> (ebase+12 <= Int.max_unsigned)%Z ->
  V293_event_bitmap_loads M be ebase elo ehi (V293_ready_group elo ehi) ->
  V293_event_bitmap_writable M be ebase ->
  (forall x v c, In (x,v) (V293_rekey_ready_bindings yo yn xo xn byo byn old new) ->
    get le x = Some (c,Tint8) -> c <> bp /\ c <> be) ->
  bc <> bt -> bc <> bp -> bc <> be -> bt <> bp -> bt <> be ->
  get le xi = Some (bi,Tint8) ->
  load Tint8 M (bi,0%Z) = Some (V293_byteval (V293_prio_bit new)) ->
  (forall c, c = bn \/ c = bi ->
    c <> b /\ c <> dy /\ c <> dby /\ c <> dx /\ c <> br /\ c <> bg /\ c <> bp /\ c <> be /\ c <> bt) ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> bt) ->
  V293_tcb_update_writable M bt base ->
  exists Mg,
  let Mh := V293_tcb_update_memory Mg bt base new in
  let fr := V293_ready_branch_rows lo hi old new in
  let er := V293_ready_rekey_rows elo ehi old new in
  cstepstar P (curs (V293_task_prio_prefix_event_update table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent xi),
    (kenil,ks)) (ge,le,M) (curs (sskip None),(kenil,ks)) (ge,le,Mh) /\
  V293_tcb_updated_loads Mh bt base new /\
  V293_rekey_bitmap_loads Mh br bg (fst fr) (snd fr) (V293_ready_group (fst fr) (snd fr)) /\
  V293_table_loads V293_tcb_type Mh b
    (update_nth_val new (update_nth_val old entries Vnull) (Vptr (bt,Int.repr base))) /\
  load (Tptr V293_tcb_type) Mh (b,(4*Z.of_nat old)%Z) = Some Vnull /\
  load (Tptr V293_tcb_type) Mh (b,(4*Z.of_nat new)%Z) = Some (Vptr (bt,Int.repr base)) /\
  V293_event_bitmap_loads Mh be ebase (fst er) (snd er) (V293_ready_group (fst er) (snd er)) /\
  load (Tptr V293_event_type) Mh (bp,0%Z) = Some (Vptr (be,Int.repr ebase)) /\
  load (Tptr V293_tcb_type) Mh (bc,0%Z) = Some (Vptr (bt,Int.repr base)) /\
  V293_tcb_update_writable Mh bt base /\
  load (Tcom_ptr 411%Z) Mh (bt,(base+28)%Z) = Some (Vptr (be,Int.repr ebase)) /\
  (forall i, (i < base+50)%Z \/ (base+54 < i)%Z -> get Mh (bt,i) = get M (bt,i)) /\
  (forall c i, c <> b -> c <> dy -> c <> dby -> c <> dx -> c <> br -> c <> bg -> c <> bp -> c <> be -> c <> bt ->
    get Mh (c,i) = get M (c,i)).
Proof.
  intros P ks ge le M table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi old new entries pevent bp be ebase elo ehi xi bi
    O N ON L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg
    Lo Ln Lp Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields
    Wy Wby Wx Loads W NewLoc NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg PE Eb Ey Eby Ex Er Eg
    EL EH EB ELimit ELoads EW LocalApart CT CP CE TP TE Bi Li ExtraApart NewTcbApart TW.
  destruct (V293_task_prio_prefix_event_nonnull_execution P ks ge le M table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi old new entries pevent bp be ebase elo ehi
    O N ON L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg
    Lo Ln Lp Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields
    Wy Wby Wx Loads W NewLoc NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg PE Eb Ey Eby Ex Er Eg
    EL EH EB ELimit ELoads EW LocalApart)
    as (M1 & M2 & Me & S1 & S2 & Store & Exec & Test & FinalLoads & FinalView & OldSlot & NewSlot & FinalW & FinalLoc & FinalEvent & FinalEW & Read & Frame).
  set (Mr := V293_tcb_read_memory M2 dy dby dx (V293_prio_row old)
    (2 ^ V293_prio_row old) (2 ^ V293_prio_bit old)) in *.
  set (Mf := V293_ready_branch_memory Mr br bg lo hi old new) in *.
  set (Mg := V293_event_rekey_memory Me be ebase elo ehi old new) in *.
  assert (Prefix : forall tail, cstepstar P
    (curs (V293_task_prio_prefix_event table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent),(kenil,tail))
    (ge,le,M) (curs (sskip None),(kenil,tail)) (ge,le,Mg)).
  { intro tail. destruct (V293_task_prio_prefix_event_nonnull_execution P tail ge le M table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi old new entries pevent bp be ebase elo ehi
    O N ON L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg
    Lo Ln Lp Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields
    Wy Wby Wx Loads W NewLoc NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg PE Eb Ey Eby Ex Er Eg
    EL EH EB ELimit ELoads EW LocalApart)
      as (A & B & C & SA & SB & SC & E & _).
    rewrite S1 in SA. inversion SA; subst A. rewrite S2 in SB. inversion SB; subst B.
    change (store (Tptr V293_event_type) Mf (bp,0%Z) (Vptr (be,Int.repr ebase)) = Some C) in SC.
    rewrite Store in SC. inversion SC; subst C. exact E. }
  assert (TC : forall i, get Mg (bt,i) = get M (bt,i)).
  { intro i. apply Frame; try congruence;
      destruct (Apart dy ltac:(auto)) as [_ [A _]];
      destruct (Apart dby ltac:(auto)) as [_ [A' _]];
      destruct (Apart dx ltac:(auto)) as [_ [A'' _]]; congruence. }
  assert (PC : forall i, get Mg (bc,i) = get M (bc,i)).
  { intro i. apply Frame; try congruence;
      destruct (Apart dy ltac:(auto)) as [A _];
      destruct (Apart dby ltac:(auto)) as [A' _];
      destruct (Apart dx ltac:(auto)) as [A'' _]; congruence. }
  assert (ExtraFrame : forall c, c = bn \/ c = bi ->
    forall tp i, load tp Mg (c,i) = load tp M (c,i)).
  { intros c I tp i. destruct (ExtraApart c I) as (A & B & C & D & E & F & G & H' & J).
    apply V293_load_block_frame. intro j. apply Frame; assumption. }
  assert (Hptr : load (Tptr V293_tcb_type) Mg (bc,0%Z) = Some (Vptr (bt,Int.repr base))).
  { rewrite (V293_load_block_frame _ M Mg bc 0%Z PC). exact Lp. }
  assert (WG : V293_tcb_update_writable Mg bt base).
  { intros d D. rewrite TC. exact (TW d D). }
  assert (NewValues : forall x v, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    exists c, get le x = Some (c,Tint8) /\ c <> bt /\ c <> bt /\ load Tint8 Mg (c,0%Z) = Some v).
  { intros x v I. destruct (FinalLoc x v ltac:(clear -I; unfold V293_rekey_new_bindings in I;
      unfold V293_rekey_ready_bindings; simpl in *; tauto)) as (c & Bind & A & B & Load).
    exists c. repeat split; try assumption; eapply NewTcbApart; eassumption. }
  destruct (V293_prio_coordinates new N) as [Yn Xn].
  destruct (V293_mask_byte_value (V293_prio_row new) ltac:(lia)) as [_ BY].
  destruct (V293_mask_byte_value (V293_prio_bit new) Xn) as [_ BX].
  assert (Operands : V293_rekey_locals ge le Mg bt bt (V293_tcb_update_bindings newprio yn xi byn xn new)).
  { intros x v I. cbn [V293_tcb_update_bindings In] in I.
    destruct I as [E|[E|[E|[E|[E|F]]]]]; try contradiction; inversion E; subst x v.
    - exists bn. destruct (ExtraApart bn ltac:(auto)) as (_ & _ & _ & _ & _ & _ & _ & _ & A).
      repeat split; try assumption.
      rewrite ExtraFrame by auto. exact Ln.
    - apply NewValues. unfold V293_rekey_new_bindings; simpl; tauto.
    - exists bi. destruct (ExtraApart bi ltac:(auto)) as (_ & _ & _ & _ & _ & _ & _ & _ & A).
      repeat split; try assumption. rewrite ExtraFrame by auto. exact Li.
    - rewrite BY. apply NewValues. unfold V293_rekey_new_bindings; simpl; tauto.
    - rewrite BX. apply NewValues. unfold V293_rekey_new_bindings; simpl; tauto. }
  destruct (V293_task_prio_tcb_update_execution P ks ge le Mg ptcb newprio yn xi byn xn bc bt base new
    N Base Limit Bc CT Hptr Operands WG)
    as (Suffix & Updated & Pointer & FinalOperands & Writable & TF).
  set (Mh := V293_tcb_update_memory Mg bt base new) in *.
  assert (RF : forall tp c i, c <> bt -> load tp Mh (c,i) = load tp Mg (c,i)).
  { intros tp c i A. apply V293_load_block_frame. intro j. apply TF. left. exact A. }
  assert (Untouched : forall i, (i < base+50)%Z \/ (base+54 < i)%Z -> get Mh (bt,i) = get M (bt,i)).
  { intros i I. rewrite TF by (right; exact I). apply TC. }
  assert (FinalInternalEvent : load (Tcom_ptr 411%Z) Mh (bt,(base+28)%Z) = Some (Vptr (be,Int.repr ebase))).
  { unfold load,loadm. rewrite (V293_loadbytes_ext _ M Mh).
    - exact Event.
    - intros k K. cbn [typelen] in K. apply Untouched. left. lia. }
  exists Mg. cbn zeta. fold Mh. split.
  - unfold V293_task_prio_prefix_event_update. eapply V293_rekey_sequence_execution; eassumption.
  - split; [exact Updated | ]. split.
    + unfold V293_rekey_bitmap_loads in *. repeat rewrite RF by congruence. exact FinalLoads.
    + split; [intros p R; rewrite RF by congruence; exact (FinalView p R) | ].
      split; [rewrite RF by congruence; exact OldSlot | ].
      split; [rewrite RF by congruence; exact NewSlot | ]. split.
      * unfold V293_event_bitmap_loads in *. repeat rewrite RF by congruence. exact FinalEvent.
      * split; [rewrite RF by congruence; exact Read | ].
        split; [exact Pointer | ]. split; [exact Writable | ].
        split; [exact FinalInternalEvent | ]. split; [exact Untouched | ].
        intros c i A B C D E F G H' J. rewrite TF by auto. apply Frame; assumption.
Qed.

Definition V293_tcb_update_frame_observes live elo ehi final_lo final_elo final_ehi final_eg : Prop :=
  forall P ks, exists Mh,
  cstepstar P (curs (V293_task_prio_prefix_event_update 500%Z 501%Z 502%Z 400%Z
    300%Z 301%Z 302%Z 303%Z 304%Z 305%Z 306%Z 307%Z 600%Z 601%Z),(kenil,ks))
    (V293_prefix_fixture_ge,V293_tcb_update_fixture_le,V293_tcb_update_fixture_mem live elo ehi)
    (curs (sskip None),(kenil,ks)) (V293_prefix_fixture_ge,V293_tcb_update_fixture_le,Mh) /\
  load Tint8 Mh (41%positive,58%Z) = Some (V293_byteval 6) /\
  load Tint8 Mh (41%positive,60%Z) = Some (V293_byteval 0) /\
  load Tint8 Mh (41%positive,59%Z) = Some (V293_byteval 6) /\
  load Tint8 Mh (41%positive,62%Z) = Some (V293_byteval 1) /\
  load Tint8 Mh (41%positive,61%Z) = Some (V293_byteval 64) /\
  V293_rekey_bitmap_loads Mh 30%positive 31%positive final_lo 0 1 /\
  V293_event_bitmap_loads Mh 72%positive 5%Z final_elo final_ehi final_eg /\
  V293_table_loads V293_tcb_type Mh 50%positive
    (update_nth_val 6 (update_nth_val 8 V293_prefix_fixture_entries Vnull) (Vptr (41%positive,Int.repr 8))) /\
  load (Tptr V293_tcb_type) Mh (50%positive,32%Z) = Some Vnull /\
  load (Tptr V293_tcb_type) Mh (50%positive,24%Z) = Some (Vptr (41%positive,Int.repr 8)) /\
  load (Tptr V293_event_type) Mh (70%positive,0%Z) = Some (Vptr (72%positive,Int.repr 5)) /\
  load (Tptr V293_tcb_type) Mh (40%positive,0%Z) = Some (Vptr (41%positive,Int.repr 8)) /\
  load (Tcom_ptr 411%Z) Mh (41%positive,36%Z) = Some (Vptr (72%positive,Int.repr 5)) /\
  (forall i, (i < 58)%Z \/ (62 < i)%Z ->
    get Mh (41%positive,i) = get (V293_tcb_update_fixture_mem live elo ehi) (41%positive,i)).

Theorem V293_tcb_update_frame_witness : forall live elo ehi,
  elo < 256 -> ehi < 256 ->
  V293_tcb_update_frame_observes live elo ehi (if live then 80 else 16)
    (fst (V293_ready_rekey_rows elo ehi 8 6)) (snd (V293_ready_rekey_rows elo ehi 8 6))
    (V293_ready_group (fst (V293_ready_rekey_rows elo ehi 8 6)) (snd (V293_ready_rekey_rows elo ehi 8 6))).
Proof.
  intros live elo ehi EL EH P ks.
  destruct (V293_prefix_event_nonnull_entry live elo ehi EL EH)
    as (Lp & Event & We & Fields & View & Wo & Wn & Wy & Wby & Wx & Loads & W & NewLoc & Lo & Ln & Initial & ELoads & EW).
  set (M := V293_tcb_update_fixture_mem live elo ehi).
  assert (RF : forall tp c i, c <> 41%positive -> c <> 73%positive ->
    load tp M (c,i) = load tp (V293_prefix_event_nonnull_mem live elo ehi) (c,i)).
  { intros tp c i A B. apply V293_load_block_frame. intro j.
    apply V293_tcb_update_fixture_outside; [exact B | left; exact A]. }
  assert (Hptr : load (Tptr V293_tcb_type) M (40%positive,0%Z) = Some (Vptr (41%positive,Int.repr 8))).
  { rewrite RF by discriminate. exact Lp. }
  assert (HEvent : load (Tcom_ptr 411%Z) M (41%positive,36%Z) = Some (Vptr (72%positive,Int.repr 5))).
  { unfold load,loadm. rewrite (V293_loadbytes_ext _ (V293_prefix_event_nonnull_mem live elo ehi) M).
    - exact Event.
    - intros k K. cbn [typelen] in K.
      apply V293_tcb_update_fixture_outside; [discriminate | right; left; lia]. }
  assert (HFields : V293_tcb_old_loads M 41%positive 8%Z 1 2 1).
  { unfold V293_tcb_old_loads,M. repeat split; update_fixture_load. }
  assert (HView : V293_table_loads V293_tcb_type M 50%positive V293_prefix_fixture_entries).
  { intros p R. rewrite RF by discriminate. exact (View p R). }
  assert (HWo : V293_bytes_writable M 50%positive 32%Z 4).
  { intros k K. unfold M; rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact (Wo k K). }
  assert (HWn : V293_bytes_writable M 50%positive 24%Z 4).
  { intros k K. unfold M; rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact (Wn k K). }
  assert (HWe : V293_bytes_writable M 70%positive 0%Z 4).
  { intros k K. unfold M; rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact (We k K). }
  assert (HWy : exists v, get M (32%positive,0%Z) = Some (true,v)).
  { unfold M; rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact Wy. }
  assert (HWby : exists v, get M (36%positive,0%Z) = Some (true,v)).
  { unfold M; rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact Wby. }
  assert (HWx : exists v, get M (34%positive,0%Z) = Some (true,v)).
  { unfold M; rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact Wx. }
  assert (HLoads : V293_rekey_bitmap_loads M 30%positive 31%positive 16 (if live then 1 else 0)
    (V293_ready_group 16 (if live then 1 else 0))).
  { unfold V293_rekey_bitmap_loads in *. repeat rewrite RF by discriminate. exact Loads. }
  assert (HW : V293_rekey_bitmap_writable M 30%positive 31%positive).
  { unfold V293_rekey_bitmap_writable in *.
    unfold M; repeat rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact W. }
  assert (HELoads : V293_event_bitmap_loads M 72%positive 5%Z elo ehi (V293_ready_group elo ehi)).
  { unfold V293_event_bitmap_loads in *. repeat rewrite RF by discriminate. exact ELoads. }
  assert (HEW : V293_event_bitmap_writable M 72%positive 5%Z).
  { unfold V293_event_bitmap_writable in *.
    unfold M; repeat rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact EW. }
  assert (HNewLoc : V293_rekey_locals V293_prefix_fixture_ge V293_tcb_update_fixture_le M
    30%positive 31%positive (V293_rekey_new_bindings 303%Z 305%Z 307%Z 6)).
  { intros x v I. destruct (NewLoc x v I) as (c & Bind & A & B & Read).
    cbn [V293_rekey_new_bindings In] in I.
    destruct I as [E|[E|[E|F]]]; try contradiction; inversion E; subst x v;
      unfold V293_event_fixture_le,V293_prefix_fixture_le,V293_read_ready_fixture_le,V293_ready_fragment_fixture_le in Bind;
      repeat first [rewrite map_get_set in Bind | rewrite map_get_set' in Bind by discriminate];
      inversion Bind; subst c.
    all: eexists; split; [update_fixture_bind; reflexivity | ];
      split; [discriminate | ]; split; [discriminate | ]; rewrite RF by discriminate; exact Read. }
  assert (HLo : load Tint8 M (51%positive,0%Z) = Some (V293_byteval 8)).
  { rewrite RF by discriminate. exact Lo. }
  assert (HLn : load Tint8 M (52%positive,0%Z) = Some (V293_byteval 6)).
  { rewrite RF by discriminate. exact Ln. }
  assert (HLi : load Tint8 M (73%positive,0%Z) = Some (V293_byteval 6)).
  { unfold M. update_fixture_load. }
  assert (HTW : V293_tcb_update_writable M 41%positive 8%Z).
  { intros d D. assert (d=50 \/ d=51 \/ d=52 \/ d=53 \/ d=54)%Z by lia.
    destruct H as [-> | [-> | [-> | [-> | ->]]]]; unfold M;
      eexists; update_fixture_get; reflexivity. }
  destruct (V293_task_prio_prefix_event_update_preserves P ks V293_prefix_fixture_ge V293_tcb_update_fixture_le
    M 500%Z 501%Z 502%Z 400%Z 300%Z 301%Z 302%Z 303%Z 304%Z 305%Z 306%Z 307%Z
    50%positive 51%positive 52%positive 40%positive 41%positive 32%positive 36%positive 34%positive
    8%Z 30%positive 31%positive 16 (if live then 1 else 0) 8 6 V293_prefix_fixture_entries
    600%Z 70%positive 72%positive 5%Z elo ehi 601%Z 73%positive)
    as (Mg & Exec & Updated & FinalLoads & FinalView & OldSlot & NewSlot & FinalEvent & Read & Pointer & TW & InternalEvent & Untouched & Frame).
  all: try assumption; try discriminate; try (update_fixture_bind; reflexivity);
    try (change (0 <= 8)%Z; lia); try (change (8+55 <= 4294967295)%Z; lia);
    try (change (0 <= 5)%Z; lia); try (change (5+12 <= 4294967295)%Z; lia);
    try (change (8<13); lia); try (change (6<13); lia); try (change (16<256); lia);
    try (destruct live; lia); try (change (length V293_prefix_fixture_entries = 13); reflexivity).
  - intros x v c I Bind. cbn [V293_rekey_new_bindings In] in I.
    destruct I as [E|[E|[E|F]]]; try contradiction; inversion E; subst x v;
      unfold V293_tcb_update_fixture_le,V293_event_fixture_le,V293_prefix_fixture_le,V293_read_ready_fixture_le,V293_ready_fragment_fixture_le in Bind;
      repeat first [rewrite map_get_set in Bind | rewrite map_get_set' in Bind by discriminate];
      inversion Bind; subst c; repeat split; discriminate.
  - intros x v c I Bind. cbn [V293_rekey_ready_bindings In] in I.
    destruct I as [E|[E|[E|[E|[E|[E|F]]]]]]; try contradiction; inversion E; subst x v;
      unfold V293_tcb_update_fixture_le,V293_event_fixture_le,V293_prefix_fixture_le,V293_read_ready_fixture_le,V293_ready_fragment_fixture_le in Bind;
      repeat first [rewrite map_get_set in Bind | rewrite map_get_set' in Bind by discriminate];
      inversion Bind; subst c; split; discriminate.
  - intros x v c I Bind. cbn [V293_rekey_new_bindings In] in I.
    destruct I as [E|[E|[E|F]]]; try contradiction; inversion E; subst x v;
      unfold V293_tcb_update_fixture_le,V293_event_fixture_le,V293_prefix_fixture_le,V293_read_ready_fixture_le,V293_ready_fragment_fixture_le in Bind;
      repeat first [rewrite map_get_set in Bind | rewrite map_get_set' in Bind by discriminate];
      inversion Bind; subst c; discriminate.
  - eexists. split; [exact Exec | ]. unfold V293_tcb_updated_loads in Updated.
    destruct Updated as (Prio & Y & X & BY & BX).
    split; [exact Prio | ]. split; [exact Y | ]. split; [exact X | ].
    split; [exact BY | ]. split; [exact BX | ].
    split; [destruct live; exact FinalLoads | ]. split; [exact FinalEvent | ].
    split; [exact FinalView | ]. split; [exact OldSlot | ]. split; [exact NewSlot | ]. split; [exact Read | ]. split; [exact Pointer | ].
    split; [exact InternalEvent | ]. exact Untouched.
Qed.

Theorem V293_tcb_update_frame_controls :
  V293_tcb_update_frame_observes false 0 1 16 64 0 1 /\
  V293_tcb_update_frame_observes true 0 1 80 64 0 1 /\
  V293_tcb_update_frame_observes false 16 3 16 80 2 3 /\
  V293_tcb_update_frame_observes false 0 129 16 64 128 3.
Proof.
  split; [exact (V293_tcb_update_frame_witness false 0 1 ltac:(lia) ltac:(lia)) | ].
  split; [exact (V293_tcb_update_frame_witness true 0 1 ltac:(lia) ltac:(lia)) | ].
  split; [exact (V293_tcb_update_frame_witness false 16 3 ltac:(lia) ltac:(lia)) | ].
  exact (V293_tcb_update_frame_witness false 0 129 ltac:(lia) ltac:(lia)).
Qed.

(* Fixed-profile finite arithmetic; includes idle index 12 only as capacity,
   not as a legal full-API new-priority guard. Signed C shift is nonnegative. *)
Theorem V293_coordinate_arithmetic : forall p,
  p < 13 ->
  Int.shr (Int.repr (Z.of_nat p)) (Int.repr 3) =
    Int.shru (Int.repr (Z.of_nat p)) (Int.repr 3) /\
  Int.modu (Int.shru (Int.repr (Z.of_nat p)) (Int.repr 3)) (Int.repr 256) =
    Int.repr (Z.of_nat (V293_prio_row p)) /\
  Int.modu (Int.and (Int.repr (Z.of_nat p)) (Int.repr 7)) (Int.repr 256) =
    Int.repr (Z.of_nat (V293_prio_bit p)).
Proof.
  intros p P. do 13 (destruct p as [ | p]; [vm_compute; repeat split; reflexivity | ]). lia.
Qed.

Theorem V293_coordinate_rhs_eval : forall ge le M newprio bn p,
  p < 13 -> get le newprio = Some (bn,Tint8) ->
  load Tint8 M (bn,0%Z) = Some (V293_byteval p) ->
  evaltype (V293_task_prio_y_expr newprio) (ge,le,M) = Some Tint8 /\
  evaltype (V293_task_prio_x_expr newprio) (ge,le,M) = Some Tint8 /\
  evalval (V293_task_prio_y_expr newprio) (ge,le,M) = Some (V293_byteval (V293_prio_row p)) /\
  evalval (V293_task_prio_x_expr newprio) (ge,le,M) = Some (V293_byteval (V293_prio_bit p)).
Proof.
  intros ge le M newprio bn p P B L.
  destruct (V293_coordinate_arithmetic p P) as [Signed [Y X]].
  unfold V293_task_prio_y_expr,V293_task_prio_x_expr.
  cbn [evaltype evalval get_lenv get_genv get_mem]. rewrite B.
  cbn beta iota. rewrite L.
  cbn [cast_eval bop_type bop_int_type bop_eval shr and].
  unfold V293_byteval.
  change (Some Tint8 = Some Tint8 /\ Some Tint8 = Some Tint8 /\
    Some (Vint32 (Int.modu (Int.shru (Int.repr (Z.of_nat p)) (Int.repr 3)) (Int.repr 256))) = Some (Vint32 (Int.repr (Z.of_nat (V293_prio_row p)))) /\
    Some (Vint32 (Int.modu (Int.and (Int.repr (Z.of_nat p)) (Int.repr 7)) (Int.repr 256))) = Some (Vint32 (Int.repr (Z.of_nat (V293_prio_bit p))))).
  rewrite Y,X. repeat split; reflexivity.
Qed.

Lemma V293_coordinate_mask_eval : forall ge le M coord b bit,
  bit < 8 -> get le coord = Some (b,Tint8) ->
  load Tint8 M (b,0%Z) = Some (V293_byteval bit) ->
  evaltype (V293_task_prio_mask_expr coord) (ge,le,M) = Some Tint8 /\
  evalval (V293_task_prio_mask_expr coord) (ge,le,M) = Some (V293_byteval (2 ^ bit)).
Proof.
  intros ge le M coord b bit B Bind Read.
  unfold V293_task_prio_mask_expr.
  cbn [evaltype evalval get_lenv get_genv get_mem]. rewrite Bind.
  cbn beta iota. rewrite Read.
  cbn [cast_eval bop_type bop_int_type bop_eval shl].
  do 8 (destruct bit as [ | bit]; [vm_compute; split; reflexivity | ]). lia.
Qed.

Lemma V293_coordinate_local_assignment : forall P ks ge le M dest b rhs n,
  n < 256 -> get le dest = Some (b,Tint8) ->
  evaltype rhs (ge,le,M) = Some Tint8 -> evalval rhs (ge,le,M) = Some (V293_byteval n) ->
  (exists v, get M (b,0%Z) = Some (true,v)) ->
  cstepstar P (curs (sassign (evar dest) rhs),(kenil,ks)) (ge,le,M)
    (curs (sskip None),(kenil,ks)) (ge,le,V293_put_byte M (b,0%Z) n).
Proof.
  intros P ks ge le M dest b rhs n N Bind T V [v W].
  eapply V293_assign_byte_offset_execution with (off:=0%Z); try eassumption.
  - cbn [evaltype]. rewrite Bind. reflexivity.
  - cbn [evaladdr get_lenv get_genv]. rewrite Bind. reflexivity.
  - change (0<=0<=4294967295)%Z. lia.
  - apply V293_put_byte_store with (old:=v). exact W.
Qed.

Definition V293_coordinate_memory M dy di dby dbx p :=
  V293_put_byte (V293_put_byte (V293_put_byte (V293_put_byte M
    (dy,0%Z) (V293_prio_row p)) (di,0%Z) (V293_prio_bit p))
    (dby,0%Z) (2 ^ V293_prio_row p)) (dbx,0%Z) (2 ^ V293_prio_bit p).

Theorem V293_task_prio_coordinates_execution :
  forall P ks ge le M newprio yn xi byn xn bn dy di dby dbx p,
  p < 13 ->
  get le newprio = Some (bn,Tint8) -> get le yn = Some (dy,Tint8) ->
  get le xi = Some (di,Tint8) -> get le byn = Some (dby,Tint8) -> get le xn = Some (dbx,Tint8) ->
  load Tint8 M (bn,0%Z) = Some (V293_byteval p) ->
  (forall b, b=dy \/ b=di \/ b=dby \/ b=dbx -> b <> bn) ->
  dy <> di -> dy <> dby -> dy <> dbx -> di <> dby -> di <> dbx -> dby <> dbx ->
  (forall b, b=dy \/ b=di \/ b=dby \/ b=dbx -> exists v, get M (b,0%Z) = Some (true,v)) ->
  let M' := V293_coordinate_memory M dy di dby dbx p in
  cstepstar P (curs (V293_task_prio_coordinates newprio yn xi byn xn),(kenil,ks))
    (ge,le,M) (curs (sskip None),(kenil,ks)) (ge,le,M') /\
  load Tint8 M' (dy,0%Z) = Some (V293_byteval (V293_prio_row p)) /\
  load Tint8 M' (di,0%Z) = Some (V293_byteval (V293_prio_bit p)) /\
  load Tint8 M' (dby,0%Z) = Some (V293_byteval (2 ^ V293_prio_row p)) /\
  load Tint8 M' (dbx,0%Z) = Some (V293_byteval (2 ^ V293_prio_bit p)) /\
  load Tint8 M' (bn,0%Z) = Some (V293_byteval p) /\
  (forall a, a <> (dy,0%Z) -> a <> (di,0%Z) -> a <> (dby,0%Z) -> a <> (dbx,0%Z) ->
    get M' a = get M a).
Proof.
  intros P ks ge le M newprio yn xi byn xn bn dy di dby dbx p N Bn By Bi Bby Bbx L Apart
    YI YBY YBX IBY IBX BYBX W. cbn zeta.
  destruct (V293_prio_coordinates p N) as [Y I].
  destruct (V293_mask_byte_value (V293_prio_row p) ltac:(lia)) as [BY _].
  destruct (V293_mask_byte_value (V293_prio_bit p) I) as [BX _].
  set (M1 := V293_put_byte M (dy,0%Z) (V293_prio_row p)).
  set (M2 := V293_put_byte M1 (di,0%Z) (V293_prio_bit p)).
  set (M3 := V293_put_byte M2 (dby,0%Z) (2 ^ V293_prio_row p)).
  assert (F1 : forall tp b i, b <> dy -> load tp M1 (b,i) = load tp M (b,i)).
  { intros. apply V293_load_block_frame. intro j. apply V293_put_byte_other. congruence. }
  assert (F2 : forall tp b i, b <> di -> b <> dy -> load tp M2 (b,i) = load tp M (b,i)).
  { intros. apply V293_load_block_frame. intro j. unfold M2,M1.
    repeat rewrite V293_put_byte_other by congruence. reflexivity. }
  assert (L1 : load Tint8 M1 (dy,0%Z) = Some (V293_byteval (V293_prio_row p))).
  { apply V293_put_byte_load. lia. }
  assert (L2 : load Tint8 M2 (di,0%Z) = Some (V293_byteval (V293_prio_bit p))).
  { apply V293_put_byte_load. lia. }
  assert (W1 : exists v, get M1 (di,0%Z) = Some (true,v)).
  { unfold M1. rewrite V293_put_byte_other by congruence. apply W; auto. }
  assert (W2 : exists v, get M2 (dby,0%Z) = Some (true,v)).
  { unfold M2,M1. repeat rewrite V293_put_byte_other by congruence. apply W; auto. }
  assert (W3 : exists v, get M3 (dbx,0%Z) = Some (true,v)).
  { unfold M3,M2,M1. repeat rewrite V293_put_byte_other by congruence. apply W; auto. }
  assert (Step1 : forall tail, cstepstar P
    (curs (sassign (evar yn) (V293_task_prio_y_expr newprio)),(kenil,tail))
    (ge,le,M) (curs (sskip None),(kenil,tail)) (ge,le,M1)).
  { intro tail. destruct (V293_coordinate_rhs_eval ge le M newprio bn p N Bn L) as [T [_ [V _]]].
    apply V293_coordinate_local_assignment; try assumption; try lia. apply W; auto. }
  assert (Ln1 : load Tint8 M1 (bn,0%Z) = Some (V293_byteval p)).
  { rewrite F1; [exact L | specialize (Apart dy ltac:(auto)); congruence]. }
  assert (Step2 : forall tail, cstepstar P
    (curs (sassign (evar xi) (V293_task_prio_x_expr newprio)),(kenil,tail))
    (ge,le,M1) (curs (sskip None),(kenil,tail)) (ge,le,M2)).
  { intro tail. destruct (V293_coordinate_rhs_eval ge le M1 newprio bn p N Bn Ln1) as [_ [T [_ V]]].
    apply V293_coordinate_local_assignment; try assumption; lia. }
  assert (Ly2 : load Tint8 M2 (dy,0%Z) = Some (V293_byteval (V293_prio_row p))).
  { unfold M2. rewrite V293_put_byte_other_load by congruence. exact L1. }
  assert (Step3 : forall tail, cstepstar P
    (curs (sassign (evar byn) (V293_task_prio_mask_expr yn)),(kenil,tail))
    (ge,le,M2) (curs (sskip None),(kenil,tail)) (ge,le,M3)).
  { intro tail. destruct (V293_coordinate_mask_eval ge le M2 yn dy (V293_prio_row p) ltac:(lia) By Ly2) as [T V].
    apply V293_coordinate_local_assignment; assumption. }
  assert (Li3 : load Tint8 M3 (di,0%Z) = Some (V293_byteval (V293_prio_bit p))).
  { unfold M3. rewrite V293_put_byte_other_load by congruence. exact L2. }
  assert (Step4 : cstepstar P
    (curs (sassign (evar xn) (V293_task_prio_mask_expr xi)),(kenil,ks))
    (ge,le,M3) (curs (sskip None),(kenil,ks))
    (ge,le,V293_put_byte M3 (dbx,0%Z) (2 ^ V293_prio_bit p))).
  { destruct (V293_coordinate_mask_eval ge le M3 xi di (V293_prio_bit p) I Bi Li3) as [T V].
    apply V293_coordinate_local_assignment; assumption. }
  split.
  - unfold V293_task_prio_coordinates,V293_coordinate_memory. fold M1 M2 M3.
    eapply V293_rekey_sequence_execution; [exact Step1 | ].
    eapply V293_rekey_sequence_execution; [exact Step2 | ].
    eapply V293_rekey_sequence_execution; [exact Step3 | exact Step4].
  - assert (Frame : forall a, a <> (dy,0%Z) -> a <> (di,0%Z) -> a <> (dby,0%Z) -> a <> (dbx,0%Z) ->
        get (V293_coordinate_memory M dy di dby dbx p) a = get M a).
    { intros. unfold V293_coordinate_memory. repeat rewrite V293_put_byte_other by assumption. reflexivity. }
    assert (FinalSource : load Tint8 (V293_coordinate_memory M dy di dby dbx p) (bn,0%Z) = Some (V293_byteval p)).
    { assert (Ny : bn <> dy) by (specialize (Apart dy ltac:(auto)); congruence).
      assert (Ni : bn <> di) by (specialize (Apart di ltac:(auto)); congruence).
      assert (Nby : bn <> dby) by (specialize (Apart dby ltac:(auto)); congruence).
      assert (Nbx : bn <> dbx) by (specialize (Apart dbx ltac:(auto)); congruence).
      unfold V293_coordinate_memory.
      repeat rewrite V293_put_byte_other_load by congruence. exact L. }
    split; [unfold V293_coordinate_memory; repeat rewrite V293_put_byte_other_load by congruence;
      apply V293_put_byte_load; lia | ].
    split; [unfold V293_coordinate_memory; repeat rewrite V293_put_byte_other_load by congruence;
      apply V293_put_byte_load; lia | ].
    split; [unfold V293_coordinate_memory; rewrite V293_put_byte_other_load by congruence;
      apply V293_put_byte_load; exact BY | ].
    split; [apply V293_put_byte_load; exact BX | ]. split; assumption.
Qed.

(* Four deliberately stale destinations, not four supplied correct results. *)
Definition V293_coordinate_fixture_mem live elo ehi :=
  V293_put_byte (V293_put_byte (V293_put_byte (V293_put_byte
    (V293_tcb_update_fixture_mem live elo ehi) (33%positive,0%Z) 255)
    (73%positive,0%Z) 255) (37%positive,0%Z) 255) (35%positive,0%Z) 255.

Lemma V293_coordinate_fixture_delta : forall live elo ehi a,
  a <> (33%positive,0%Z) -> a <> (73%positive,0%Z) ->
  a <> (37%positive,0%Z) -> a <> (35%positive,0%Z) ->
  get (V293_coordinate_fixture_mem live elo ehi) a =
    get (V293_tcb_update_fixture_mem live elo ehi) a.
Proof.
  intros. unfold V293_coordinate_fixture_mem.
  repeat rewrite V293_put_byte_other by assumption. reflexivity.
Qed.

Lemma V293_coordinate_fixture_stale : forall live elo ehi b,
  b=33%positive \/ b=73%positive \/ b=37%positive \/ b=35%positive ->
  load Tint8 (V293_coordinate_fixture_mem live elo ehi) (b,0%Z) = Some (V293_byteval 255).
Proof.
  intros live elo ehi b Cases. destruct Cases as [-> | [-> | [-> | ->]]];
    unfold V293_coordinate_fixture_mem;
    repeat rewrite V293_put_byte_other_load by discriminate;
    apply V293_put_byte_load; lia.
Qed.

Local Ltac coordinate_base_get :=
  update_fixture_get;
  repeat rewrite V293_prefix_event_nonnull_outside by discriminate;
  repeat rewrite V293_event_fixture_outside by (try discriminate; left; discriminate);
  repeat rewrite V293_prefix_fixture_outside by discriminate;
  unfold V293_read_ready_fixture_mem;
  repeat first [rewrite V293_put_byte_other by discriminate | rewrite V293_put_byte_get_same].

Lemma V293_coordinate_fixture_restore : forall live elo ehi,
  V293_coordinate_memory (V293_coordinate_fixture_mem live elo ehi)
    33%positive 73%positive 37%positive 35%positive 6 =
  V293_tcb_update_fixture_mem live elo ehi.
Proof.
  intros live elo ehi.
  assert (Y : get (V293_tcb_update_fixture_mem live elo ehi) (33%positive,0%Z) =
    Some (true,Byte (Byte.repr 0))) by (coordinate_base_get; reflexivity).
  assert (I : get (V293_tcb_update_fixture_mem live elo ehi) (73%positive,0%Z) =
    Some (true,Byte (Byte.repr 6))) by (coordinate_base_get; reflexivity).
  assert (BY : get (V293_tcb_update_fixture_mem live elo ehi) (37%positive,0%Z) =
    Some (true,Byte (Byte.repr 1))) by (coordinate_base_get; reflexivity).
  assert (BX : get (V293_tcb_update_fixture_mem live elo ehi) (35%positive,0%Z) =
    Some (true,Byte (Byte.repr 64))) by (coordinate_base_get; reflexivity).
  apply HalfPermMap.extensionality. intro a.
  change (get (V293_coordinate_memory (V293_coordinate_fixture_mem live elo ehi)
    33%positive 73%positive 37%positive 35%positive 6) a =
    get (V293_tcb_update_fixture_mem live elo ehi) a).
  destruct (addr_eq_dec a (33%positive,0%Z)) as [-> | Ny];
  [ | destruct (addr_eq_dec a (73%positive,0%Z)) as [-> | Ni]];
  [ | | destruct (addr_eq_dec a (37%positive,0%Z)) as [-> | Nby]];
  [ | | | destruct (addr_eq_dec a (35%positive,0%Z)) as [-> | Nbx]].
  - etransitivity; [ | symmetry; exact Y]. unfold V293_coordinate_memory.
    repeat rewrite V293_put_byte_other by discriminate. apply V293_put_byte_get_same.
  - etransitivity; [ | symmetry; exact I]. unfold V293_coordinate_memory.
    repeat rewrite V293_put_byte_other by discriminate. apply V293_put_byte_get_same.
  - etransitivity; [ | symmetry; exact BY]. unfold V293_coordinate_memory.
    rewrite V293_put_byte_other by discriminate. apply V293_put_byte_get_same.
  - etransitivity; [ | symmetry; exact BX]. unfold V293_coordinate_memory. apply V293_put_byte_get_same.
  - unfold V293_coordinate_memory. repeat rewrite V293_put_byte_other by assumption.
    apply V293_coordinate_fixture_delta; assumption.
Qed.

Lemma V293_coordinate_fixture_execution : forall P ks live elo ehi,
  cstepstar P (curs (V293_task_prio_coordinates 502%Z 303%Z 601%Z 307%Z 305%Z),(kenil,ks))
    (V293_prefix_fixture_ge,V293_tcb_update_fixture_le,V293_coordinate_fixture_mem live elo ehi)
    (curs (sskip None),(kenil,ks))
    (V293_prefix_fixture_ge,V293_tcb_update_fixture_le,V293_tcb_update_fixture_mem live elo ehi).
Proof.
  intros P ks live elo ehi.
  assert (Source : load Tint8 (V293_coordinate_fixture_mem live elo ehi) (52%positive,0%Z) =
    Some (V293_byteval 6)).
  { assert (F : load Tint8 (V293_coordinate_fixture_mem live elo ehi) (52%positive,0%Z) =
        load Tint8 (V293_prefix_fixture_mem live) (52%positive,0%Z)).
    { apply V293_load_block_frame. intro j.
      rewrite V293_coordinate_fixture_delta by (intro E; inversion E; discriminate).
      rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate).
      rewrite V293_prefix_event_nonnull_outside by discriminate.
      apply V293_event_fixture_outside; [discriminate | left; discriminate]. }
    rewrite F. unfold V293_prefix_fixture_mem. apply V293_put_byte_load; lia. }

  destruct (V293_task_prio_coordinates_execution P ks V293_prefix_fixture_ge V293_tcb_update_fixture_le
    (V293_coordinate_fixture_mem live elo ehi) 502%Z 303%Z 601%Z 307%Z 305%Z
    52%positive 33%positive 73%positive 37%positive 35%positive 6)
    as [Exec Rest]; try (change (6<13); lia); try (update_fixture_bind; reflexivity);
      try exact Source; try discriminate.
  - intros b Cases. destruct Cases as [-> | [-> | [-> | ->]]]; discriminate.
  - intros b Cases. destruct Cases as [-> | [-> | [-> | ->]]];
      unfold V293_coordinate_fixture_mem;
      repeat rewrite V293_put_byte_other by discriminate;
      eexists; apply V293_put_byte_get_same.
  - rewrite V293_coordinate_fixture_restore in Exec. exact Exec.
Qed.

Definition V293_coordinate_update_observes live elo ehi final_lo final_elo final_ehi final_eg : Prop :=
  forall P ks, exists Mh,
  cstepstar P (curs (V293_task_prio_coordinates_update 500%Z 501%Z 502%Z 400%Z
    300%Z 301%Z 302%Z 303%Z 304%Z 305%Z 306%Z 307%Z 600%Z 601%Z),(kenil,ks))
    (V293_prefix_fixture_ge,V293_tcb_update_fixture_le,V293_coordinate_fixture_mem live elo ehi)
    (curs (sskip None),(kenil,ks)) (V293_prefix_fixture_ge,V293_tcb_update_fixture_le,Mh) /\
  load Tint8 (V293_coordinate_fixture_mem live elo ehi) (33%positive,0%Z) = Some (V293_byteval 255) /\
  load Tint8 (V293_coordinate_fixture_mem live elo ehi) (73%positive,0%Z) = Some (V293_byteval 255) /\
  load Tint8 (V293_coordinate_fixture_mem live elo ehi) (37%positive,0%Z) = Some (V293_byteval 255) /\
  load Tint8 (V293_coordinate_fixture_mem live elo ehi) (35%positive,0%Z) = Some (V293_byteval 255) /\
  load Tint8 Mh (41%positive,58%Z) = Some (V293_byteval 6) /\
  load Tint8 Mh (41%positive,60%Z) = Some (V293_byteval 0) /\
  load Tint8 Mh (41%positive,59%Z) = Some (V293_byteval 6) /\
  load Tint8 Mh (41%positive,62%Z) = Some (V293_byteval 1) /\
  load Tint8 Mh (41%positive,61%Z) = Some (V293_byteval 64) /\
  V293_rekey_bitmap_loads Mh 30%positive 31%positive final_lo 0 1 /\
  V293_event_bitmap_loads Mh 72%positive 5%Z final_elo final_ehi final_eg /\
  V293_table_loads V293_tcb_type Mh 50%positive
    (update_nth_val 6 (update_nth_val 8 V293_prefix_fixture_entries Vnull) (Vptr (41%positive,Int.repr 8))) /\
  load (Tptr V293_tcb_type) Mh (50%positive,32%Z) = Some Vnull /\
  load (Tptr V293_tcb_type) Mh (50%positive,24%Z) = Some (Vptr (41%positive,Int.repr 8)) /\
  load (Tptr V293_event_type) Mh (70%positive,0%Z) = Some (Vptr (72%positive,Int.repr 5)) /\
  load (Tptr V293_tcb_type) Mh (40%positive,0%Z) = Some (Vptr (41%positive,Int.repr 8)) /\
  load (Tcom_ptr 411%Z) Mh (41%positive,36%Z) = Some (Vptr (72%positive,Int.repr 5)) /\
  (forall i, (i < 58)%Z \/ (62 < i)%Z ->
    get Mh (41%positive,i) = get (V293_coordinate_fixture_mem live elo ehi) (41%positive,i)).

Theorem V293_coordinate_update_witness : forall live elo ehi,
  elo < 256 -> ehi < 256 ->
  V293_coordinate_update_observes live elo ehi (if live then 80 else 16)
    (fst (V293_ready_rekey_rows elo ehi 8 6)) (snd (V293_ready_rekey_rows elo ehi 8 6))
    (V293_ready_group (fst (V293_ready_rekey_rows elo ehi 8 6)) (snd (V293_ready_rekey_rows elo ehi 8 6))).
Proof.
  intros live elo ehi EL EH P ks.
  destruct (V293_tcb_update_frame_witness live elo ehi EL EH P ks)
    as (Mh & Exec & Prio & Y & X & BY & BX & Ready & Event & View & Old & New & Ep & Tp & Internal & Frame).
  exists Mh. split.
  - unfold V293_task_prio_coordinates_update.
    eapply V293_rekey_sequence_execution; [intro tail; apply V293_coordinate_fixture_execution | exact Exec].
  - split; [apply V293_coordinate_fixture_stale; auto | ].
    split; [apply V293_coordinate_fixture_stale; auto | ].
    split; [apply V293_coordinate_fixture_stale; auto | ].
    split; [apply V293_coordinate_fixture_stale; auto | ].
    split; [exact Prio | ]. split; [exact Y | ]. split; [exact X | ].
    split; [exact BY | ]. split; [exact BX | ]. split; [exact Ready | ]. split; [exact Event | ].
    split; [exact View | ]. split; [exact Old | ]. split; [exact New | ]. split; [exact Ep | ].
    split; [exact Tp | ]. split; [exact Internal | ].
    intros i Outside. rewrite V293_coordinate_fixture_delta by discriminate. apply Frame; exact Outside.
Qed.

Theorem V293_coordinate_update_controls :
  V293_coordinate_update_observes false 0 1 16 64 0 1 /\
  V293_coordinate_update_observes true 0 1 80 64 0 1 /\
  V293_coordinate_update_observes false 16 3 16 80 2 3 /\
  V293_coordinate_update_observes false 0 129 16 64 128 3.
Proof.
  split; [exact (V293_coordinate_update_witness false 0 1 ltac:(lia) ltac:(lia)) | ].
  split; [exact (V293_coordinate_update_witness true 0 1 ltac:(lia) ltac:(lia)) | ].
  split; [exact (V293_coordinate_update_witness false 16 3 ltac:(lia) ltac:(lia)) | ].
  exact (V293_coordinate_update_witness false 0 129 ltac:(lia) ltac:(lia)).
Qed.

(* Generic 110--166 composition: coordinates are computed, never entry oracles. *)
Theorem V293_task_prio_coordinates_update_execution :
  forall P ks ge le M table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi old new entries pevent bp be ebase elo ehi xi bi ny nby nbx,
  old < 13 -> new < 13 -> old <> new -> lo < 256 -> hi < 256 -> br <> bg ->
  (0 <= base)%Z -> (base+55 <= Int.max_unsigned)%Z ->
  get le table = None -> get ge table = Some (b,Tarray (Tptr V293_tcb_type) 13) ->
  get le oldprio = Some (bo,Tint8) -> get le newprio = Some (bn,Tint8) ->
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  b <> bo -> b <> bn -> b <> bc -> b <> bt ->
  b <> dy -> b <> dby -> b <> dx -> b <> br -> b <> bg ->
  load Tint8 M (bo,0%Z) = Some (V293_byteval old) ->
  load Tint8 M (bn,0%Z) = Some (V293_byteval new) ->
  load (Tptr V293_tcb_type) M (bc,0%Z) = Some (Vptr (bt,Int.repr base)) ->
  V293_bytes_writable M b (4*Z.of_nat old)%Z 4 ->
  V293_bytes_writable M b (4*Z.of_nat new)%Z 4 ->
  length entries = 13 -> V293_table_loads V293_tcb_type M b entries ->
  get le yo = Some (dy,Tint8) -> get le byo = Some (dby,Tint8) -> get le xo = Some (dx,Tint8) ->
  get le rows = None -> get ge rows = Some (br,Tarray Tint8 2) ->
  get le group = None -> get ge group = Some (bg,Tint8) ->
  dy <> dby -> dy <> dx -> dby <> dx ->
  (forall c, c = dy \/ c = dby \/ c = dx -> c <> bc /\ c <> bt /\ c <> br /\ c <> bg) ->
  V293_tcb_old_loads M bt base (V293_prio_row old)
    (2 ^ V293_prio_row old) (2 ^ V293_prio_bit old) ->
  (exists v, get M (dy,0%Z) = Some (true,v)) ->
  (exists v, get M (dby,0%Z) = Some (true,v)) ->
  (exists v, get M (dx,0%Z) = Some (true,v)) ->
  V293_rekey_bitmap_loads M br bg lo hi (V293_ready_group lo hi) ->
  V293_rekey_bitmap_writable M br bg ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> b /\ c <> dy /\ c <> dby /\ c <> dx) ->
  get le pevent = Some (bp,Tptr V293_event_type) ->
  V293_bytes_writable M bp 0%Z 4 ->
  load (Tcom_ptr 411%Z) M (bt,(base+28)%Z) = Some (Vptr (be,Int.repr ebase)) ->
  bc <> br -> bc <> bg -> bt <> br -> bt <> bg ->
  bp <> b -> bp <> dy -> bp <> dby -> bp <> dx -> bp <> br -> bp <> bg ->
  bp <> be ->
  be <> b -> be <> dy -> be <> dby -> be <> dx -> be <> br -> be <> bg ->
  elo < 256 -> ehi < 256 -> (0 <= ebase)%Z -> (ebase+12 <= Int.max_unsigned)%Z ->
  V293_event_bitmap_loads M be ebase elo ehi (V293_ready_group elo ehi) ->
  V293_event_bitmap_writable M be ebase ->
  (forall x v c, In (x,v) (V293_rekey_ready_bindings yo yn xo xn byo byn old new) ->
    get le x = Some (c,Tint8) -> c <> bp /\ c <> be) ->
  bc <> bt -> bc <> bp -> bc <> be -> bt <> bp -> bt <> be ->
  get le xi = Some (bi,Tint8) ->
  (forall c, c = bn \/ c = bi ->
    c <> b /\ c <> dy /\ c <> dby /\ c <> dx /\ c <> br /\ c <> bg /\ c <> bp /\ c <> be /\ c <> bt) ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> bt) ->
  V293_tcb_update_writable M bt base ->
  get le yn = Some (ny,Tint8) -> get le byn = Some (nby,Tint8) ->
  get le xn = Some (nbx,Tint8) ->
  ny <> bi -> ny <> nby -> ny <> nbx -> bi <> nby -> bi <> nbx -> nby <> nbx ->
  (forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->
    c <> b /\ c <> bo /\ c <> bn /\ c <> bc /\ c <> bt /\
    c <> dy /\ c <> dby /\ c <> dx /\ c <> br /\ c <> bg /\ c <> bp /\ c <> be) ->
  (forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->
    exists v, get M (c,0%Z) = Some (true,v)) ->
  exists Mg,
  let Mh := V293_tcb_update_memory Mg bt base new in
  let fr := V293_ready_branch_rows lo hi old new in
  let er := V293_ready_rekey_rows elo ehi old new in
  cstepstar P (curs (V293_task_prio_coordinates_update table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent xi),
    (kenil,ks)) (ge,le,M) (curs (sskip None),(kenil,ks)) (ge,le,Mh) /\
  V293_tcb_updated_loads Mh bt base new /\
  V293_rekey_bitmap_loads Mh br bg (fst fr) (snd fr) (V293_ready_group (fst fr) (snd fr)) /\
  V293_table_loads V293_tcb_type Mh b
    (update_nth_val new (update_nth_val old entries Vnull) (Vptr (bt,Int.repr base))) /\
  load (Tptr V293_tcb_type) Mh (b,(4*Z.of_nat old)%Z) = Some Vnull /\
  load (Tptr V293_tcb_type) Mh (b,(4*Z.of_nat new)%Z) = Some (Vptr (bt,Int.repr base)) /\
  V293_event_bitmap_loads Mh be ebase (fst er) (snd er) (V293_ready_group (fst er) (snd er)) /\
  load (Tptr V293_event_type) Mh (bp,0%Z) = Some (Vptr (be,Int.repr ebase)) /\
  load (Tptr V293_tcb_type) Mh (bc,0%Z) = Some (Vptr (bt,Int.repr base)) /\
  V293_tcb_update_writable Mh bt base /\
  load (Tcom_ptr 411%Z) Mh (bt,(base+28)%Z) = Some (Vptr (be,Int.repr ebase)) /\
  (forall i, (i < base+50)%Z \/ (base+54 < i)%Z -> get Mh (bt,i) = get M (bt,i)) /\
  (forall c i, c <> b -> c <> dy -> c <> dby -> c <> dx -> c <> br -> c <> bg -> c <> bp -> c <> be -> c <> bt ->
    c <> ny -> c <> bi -> c <> nby -> c <> nbx ->
    get Mh (c,i) = get M (c,i)).
Proof.
  intros P ks ge le M table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi old new entries pevent bp be ebase elo ehi xi bi ny nby nbx
    O N ON L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg
    Lo Ln Lp Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields
    Wy Wby Wx Loads W NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg PE Eb Ey Eby Ex Er Eg
    EL EH EB ELimit ELoads EW LocalApart CT CP CE TP TE Bi ExtraApart NewTcbApart TW
    NBy NBby NBx NYI NYBY NYBX NIBY NIBX NBYBX CoordApart CoordW.
  assert (SourceApart : forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx -> c <> bn).
  { intros c I. destruct (CoordApart c I) as (_ & _ & A & _). exact A. }
  destruct (V293_task_prio_coordinates_execution P ks ge le M newprio yn xi byn xn bn ny bi nby nbx new
    N Bn NBy Bi NBby NBx Ln SourceApart NYI NYBY NYBX NIBY NIBX NBYBX CoordW)
    as (Coordinates & NewY & NewI & NewBY & NewBX & NewSource & CoordFrame).
  set (Mc := V293_coordinate_memory M ny bi nby nbx new) in *.
  assert (Safe : forall c, In c [b;bo;bn;bc;bt;dy;dby;dx;br;bg;bp;be] ->
    c <> ny /\ c <> bi /\ c <> nby /\ c <> nbx).
  { intros c I.
    pose proof (CoordApart ny ltac:(auto)) as A.
    pose proof (CoordApart bi ltac:(auto)) as B.
    pose proof (CoordApart nby ltac:(auto)) as C.
    pose proof (CoordApart nbx ltac:(auto)) as D.
    cbn in I. intuition congruence. }
  assert (CF : forall c i, In c [b;bo;bn;bc;bt;dy;dby;dx;br;bg;bp;be] ->
    get Mc (c,i) = get M (c,i)).
  { intros c i I. destruct (Safe c I) as (A & B & C & D).
    apply CoordFrame; congruence. }
  assert (LF : forall tp c i, In c [b;bo;bn;bc;bt;dy;dby;dx;br;bg;bp;be] ->
    load tp Mc (c,i) = load tp M (c,i)).
  { intros tp c i I. apply V293_load_block_frame. intro j. apply CF. exact I. }
  assert (NewLoc : V293_rekey_locals ge le Mc br bg (V293_rekey_new_bindings yn xn byn new)).
  { destruct (V293_prio_coordinates new N) as [Y X].
    destruct (V293_mask_byte_value (V293_prio_row new) ltac:(lia)) as [_ MY].
    destruct (V293_mask_byte_value (V293_prio_bit new) X) as [_ MX].
    intros x v I. cbn [V293_rekey_new_bindings In] in I.
    destruct I as [E|[E|[E|F]]]; try contradiction; inversion E; subst x v.
    - exists ny. destruct (CoordApart ny ltac:(auto)) as (_ & _ & _ & _ & _ & _ & _ & _ & A & B & _).
      repeat split; assumption.
    - exists nbx. destruct (CoordApart nbx ltac:(auto)) as (_ & _ & _ & _ & _ & _ & _ & _ & A & B & _).
      repeat split; try assumption. rewrite <- MX. exact NewBX.
    - exists nby. destruct (CoordApart nby ltac:(auto)) as (_ & _ & _ & _ & _ & _ & _ & _ & A & B & _).
      repeat split; try assumption. rewrite <- MY. exact NewBY. }
  assert (Resources :
    load Tint8 Mc (bo,0%Z) = Some (V293_byteval old) /\
    load (Tptr V293_tcb_type) Mc (bc,0%Z) = Some (Vptr (bt,Int.repr base)) /\
    V293_bytes_writable Mc b (4*Z.of_nat old)%Z 4 /\
    V293_bytes_writable Mc b (4*Z.of_nat new)%Z 4 /\
    V293_table_loads V293_tcb_type Mc b entries /\
    V293_tcb_old_loads Mc bt base (V293_prio_row old) (2 ^ V293_prio_row old) (2 ^ V293_prio_bit old) /\
    (exists v, get Mc (dy,0%Z) = Some (true,v)) /\
    (exists v, get Mc (dby,0%Z) = Some (true,v)) /\
    (exists v, get Mc (dx,0%Z) = Some (true,v)) /\
    V293_rekey_bitmap_loads Mc br bg lo hi (V293_ready_group lo hi) /\
    V293_rekey_bitmap_writable Mc br bg /\
    V293_bytes_writable Mc bp 0%Z 4 /\
    load (Tcom_ptr 411%Z) Mc (bt,(base+28)%Z) = Some (Vptr (be,Int.repr ebase)) /\
    V293_event_bitmap_loads Mc be ebase elo ehi (V293_ready_group elo ehi) /\
    V293_event_bitmap_writable Mc be ebase /\
    V293_tcb_update_writable Mc bt base).
  { unfold V293_bytes_writable,V293_table_loads,V293_tcb_old_loads,
      V293_rekey_bitmap_loads,V293_rekey_bitmap_writable,
      V293_event_bitmap_loads,V293_event_bitmap_writable,V293_tcb_update_writable in *.
    repeat rewrite LF by (simpl; tauto).
    repeat rewrite CF by (simpl; tauto).
    repeat split; try tauto.
    - intros k K. rewrite CF by (simpl; tauto). apply Wo. exact K.
    - intros k K. rewrite CF by (simpl; tauto). apply Wn. exact K.
    - intros p R. rewrite LF by (simpl; tauto). apply View. exact R.
    - intros k K. rewrite CF by (simpl; tauto). apply We. exact K.
    - intros d D. rewrite CF by (simpl; tauto). apply TW. exact D. }
  destruct Resources as (Clo & Clp & Cwo & Cwn & Cview & Cfields & Cwy & Cwby & Cwx & Cloads & Cw & Cwe & Cevent & Celoads & Cew & Ctw).
  destruct (V293_task_prio_prefix_event_update_preserves P ks ge le Mc table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi old new entries pevent bp be ebase elo ehi xi bi
    O N ON L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg
    Clo NewSource Clp Cwo Cwn Len Cview By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Cfields
    Cwy Cwby Cwx Cloads Cw NewLoc NewApart Be Cwe Cevent Cr Cg Br Bg Pb Py Pby Px Pr Pg PE Eb Ey Eby Ex Er Eg
    EL EH EB ELimit Celoads Cew LocalApart CT CP CE TP TE Bi NewI ExtraApart NewTcbApart Ctw)
    as (Mg & Exec & Updated & Ready & Table & OldSlot & NewSlot & EventOut & Read & Pointer & Writable & Internal & Untouched & Frame).
  exists Mg. cbn zeta in *. split.
  - unfold V293_task_prio_coordinates_update.
    eapply V293_rekey_sequence_execution; [ | exact Exec].
    intro tail. destruct (V293_task_prio_coordinates_execution P tail ge le M newprio yn xi byn xn bn ny bi nby nbx new
      N Bn NBy Bi NBby NBx Ln SourceApart NYI NYBY NYBX NIBY NIBX NBYBX CoordW) as [E _]. exact E.
  - split; [exact Updated | ]. split; [exact Ready | ]. split; [exact Table | ].
    split; [exact OldSlot | ]. split; [exact NewSlot | ]. split; [exact EventOut | ].
    split; [exact Read | ]. split; [exact Pointer | ]. split; [exact Writable | ].
    split; [exact Internal | ]. split.
    + intros i I. rewrite Untouched by exact I. apply CF. simpl; tauto.
    + intros c i A B C D E F G H' J NY NI NBY NBX.
      rewrite Frame by assumption. apply CoordFrame; congruence.
Qed.

(* The generic interface is inhabited by the same four-stale-byte entry. *)
Theorem V293_generic_coordinate_update_witness : forall live elo ehi,
  elo < 256 -> ehi < 256 ->
  V293_coordinate_update_observes live elo ehi (if live then 80 else 16)
    (fst (V293_ready_rekey_rows elo ehi 8 6)) (snd (V293_ready_rekey_rows elo ehi 8 6))
    (V293_ready_group (fst (V293_ready_rekey_rows elo ehi 8 6)) (snd (V293_ready_rekey_rows elo ehi 8 6))).
Proof.
  intros live elo ehi EL EH P ks.
  destruct (V293_prefix_event_nonnull_entry live elo ehi EL EH)
    as (Lp & Event & We & Fields & View & Wo & Wn & Wy & Wby & Wx & Loads & W & NewLoc & Lo & Ln & Initial & ELoads & EW).
  set (M := V293_coordinate_fixture_mem live elo ehi).
  assert (RF : forall tp c i, c <> 41%positive -> c <> 73%positive -> c <> 33%positive -> c <> 37%positive -> c <> 35%positive ->
    load tp M (c,i) = load tp (V293_prefix_event_nonnull_mem live elo ehi) (c,i)).
  { intros tp c i A B C D E. apply V293_load_block_frame. intro j.
    unfold M. rewrite V293_coordinate_fixture_delta by (intro Eq; inversion Eq; congruence).
    apply V293_tcb_update_fixture_outside; [exact B | left; exact A]. }
  assert (Hptr : load (Tptr V293_tcb_type) M (40%positive,0%Z) = Some (Vptr (41%positive,Int.repr 8))).
  { rewrite RF by discriminate. exact Lp. }
  assert (HEvent : load (Tcom_ptr 411%Z) M (41%positive,36%Z) = Some (Vptr (72%positive,Int.repr 5))).
  { unfold load,loadm. rewrite (V293_loadbytes_ext _ (V293_prefix_event_nonnull_mem live elo ehi) M).
    - exact Event.
    - intros k K. cbn [typelen] in K.
      unfold M. rewrite V293_coordinate_fixture_delta by (intro Eq; inversion Eq; discriminate).
      apply V293_tcb_update_fixture_outside; [discriminate | right; left; lia]. }
  assert (HFields : V293_tcb_old_loads M 41%positive 8%Z 1 2 1).
  { unfold V293_tcb_old_loads,M,V293_coordinate_fixture_mem; repeat rewrite V293_put_byte_other_load by discriminate; repeat split; update_fixture_load. }
  assert (HView : V293_table_loads V293_tcb_type M 50%positive V293_prefix_fixture_entries).
  { intros p R. rewrite RF by discriminate. exact (View p R). }
  assert (HWo : V293_bytes_writable M 50%positive 32%Z 4).
  { intros k K. unfold M; repeat rewrite V293_coordinate_fixture_delta by (intro Eq; inversion Eq; discriminate); rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact (Wo k K). }
  assert (HWn : V293_bytes_writable M 50%positive 24%Z 4).
  { intros k K. unfold M; repeat rewrite V293_coordinate_fixture_delta by (intro Eq; inversion Eq; discriminate); rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact (Wn k K). }
  assert (HWe : V293_bytes_writable M 70%positive 0%Z 4).
  { intros k K. unfold M; repeat rewrite V293_coordinate_fixture_delta by (intro Eq; inversion Eq; discriminate); rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact (We k K). }
  assert (HWy : exists v, get M (32%positive,0%Z) = Some (true,v)).
  { unfold M; repeat rewrite V293_coordinate_fixture_delta by (intro Eq; inversion Eq; discriminate); rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact Wy. }
  assert (HWby : exists v, get M (36%positive,0%Z) = Some (true,v)).
  { unfold M; repeat rewrite V293_coordinate_fixture_delta by (intro Eq; inversion Eq; discriminate); rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact Wby. }
  assert (HWx : exists v, get M (34%positive,0%Z) = Some (true,v)).
  { unfold M; repeat rewrite V293_coordinate_fixture_delta by (intro Eq; inversion Eq; discriminate); rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact Wx. }
  assert (HLoads : V293_rekey_bitmap_loads M 30%positive 31%positive 16 (if live then 1 else 0)
    (V293_ready_group 16 (if live then 1 else 0))).
  { unfold V293_rekey_bitmap_loads in *. repeat rewrite RF by discriminate. exact Loads. }
  assert (HW : V293_rekey_bitmap_writable M 30%positive 31%positive).
  { unfold V293_rekey_bitmap_writable in *.
    unfold M; repeat rewrite V293_coordinate_fixture_delta by (intro Eq; inversion Eq; discriminate); repeat rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact W. }
  assert (HELoads : V293_event_bitmap_loads M 72%positive 5%Z elo ehi (V293_ready_group elo ehi)).
  { unfold V293_event_bitmap_loads in *. repeat rewrite RF by discriminate. exact ELoads. }
  assert (HEW : V293_event_bitmap_writable M 72%positive 5%Z).
  { unfold V293_event_bitmap_writable in *.
    unfold M; repeat rewrite V293_coordinate_fixture_delta by (intro Eq; inversion Eq; discriminate); repeat rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact EW. }
  assert (HLo : load Tint8 M (51%positive,0%Z) = Some (V293_byteval 8)).
  { rewrite RF by discriminate. exact Lo. }
  assert (HLn : load Tint8 M (52%positive,0%Z) = Some (V293_byteval 6)).
  { rewrite RF by discriminate. exact Ln. }
  assert (HTW : V293_tcb_update_writable M 41%positive 8%Z).
  { intros d D. assert (d=50 \/ d=51 \/ d=52 \/ d=53 \/ d=54)%Z by lia.
    destruct H as [-> | [-> | [-> | [-> | ->]]]]; unfold M; repeat rewrite V293_coordinate_fixture_delta by (intro Eq; inversion Eq; discriminate);
      eexists; update_fixture_get; reflexivity. }
  destruct (V293_task_prio_coordinates_update_execution P ks V293_prefix_fixture_ge V293_tcb_update_fixture_le
    M 500%Z 501%Z 502%Z 400%Z 300%Z 301%Z 302%Z 303%Z 304%Z 305%Z 306%Z 307%Z
    50%positive 51%positive 52%positive 40%positive 41%positive 32%positive 36%positive 34%positive
    8%Z 30%positive 31%positive 16 (if live then 1 else 0) 8 6 V293_prefix_fixture_entries
    600%Z 70%positive 72%positive 5%Z elo ehi 601%Z 73%positive 33%positive 37%positive 35%positive)
    as (Mg & Exec & Updated & FinalLoads & FinalView & OldSlot & NewSlot & FinalEvent & Read & Pointer & TW & InternalEvent & Untouched & Frame).
  all: try assumption; try discriminate; try (update_fixture_bind; reflexivity);
    try (change (0 <= 8)%Z; lia); try (change (8+55 <= 4294967295)%Z; lia);
    try (change (0 <= 5)%Z; lia); try (change (5+12 <= 4294967295)%Z; lia);
    try (change (8<13); lia); try (change (6<13); lia); try (change (16<256); lia);
    try (destruct live; lia); try (change (length V293_prefix_fixture_entries = 13); reflexivity).
  - intros x v c I Bind. cbn [V293_rekey_new_bindings In] in I.
    destruct I as [E|[E|[E|F]]]; try contradiction; inversion E; subst x v;
      unfold V293_tcb_update_fixture_le,V293_event_fixture_le,V293_prefix_fixture_le,V293_read_ready_fixture_le,V293_ready_fragment_fixture_le in Bind;
      repeat first [rewrite map_get_set in Bind | rewrite map_get_set' in Bind by discriminate];
      inversion Bind; subst c; repeat split; discriminate.
  - intros x v c I Bind. cbn [V293_rekey_ready_bindings In] in I.
    destruct I as [E|[E|[E|[E|[E|[E|F]]]]]]; try contradiction; inversion E; subst x v;
      unfold V293_tcb_update_fixture_le,V293_event_fixture_le,V293_prefix_fixture_le,V293_read_ready_fixture_le,V293_ready_fragment_fixture_le in Bind;
      repeat first [rewrite map_get_set in Bind | rewrite map_get_set' in Bind by discriminate];
      inversion Bind; subst c; split; discriminate.
  - intros x v c I Bind. cbn [V293_rekey_new_bindings In] in I.
    destruct I as [E|[E|[E|F]]]; try contradiction; inversion E; subst x v;
      unfold V293_tcb_update_fixture_le,V293_event_fixture_le,V293_prefix_fixture_le,V293_read_ready_fixture_le,V293_ready_fragment_fixture_le in Bind;
      repeat first [rewrite map_get_set in Bind | rewrite map_get_set' in Bind by discriminate];
      inversion Bind; subst c; discriminate.
  - intros c Cases. destruct Cases as [-> | [-> | [-> | ->]]];
      unfold M,V293_coordinate_fixture_mem;
      repeat rewrite V293_put_byte_other by discriminate;
      eexists; apply V293_put_byte_get_same.
  - eexists. split; [exact Exec | ].
    do 4 (split; [apply V293_coordinate_fixture_stale; auto | ]).
    unfold V293_tcb_updated_loads in Updated.
    destruct Updated as (Prio & Y & X & BY & BX).
    split; [exact Prio | ]. split; [exact Y | ]. split; [exact X | ].
    split; [exact BY | ]. split; [exact BX | ].
    split; [destruct live; exact FinalLoads | ]. split; [exact FinalEvent | ].
    split; [exact FinalView | ]. split; [exact OldSlot | ]. split; [exact NewSlot | ]. split; [exact Read | ]. split; [exact Pointer | ].
    split; [exact InternalEvent | ]. exact Untouched.
Qed.

(* Actual 82--90 argument guards and successful 93--104 lookup.
   Critical calls, RESERVED and complete API linking are not proved here. *)
Lemma V293_entry_byte_arithmetic : forall p,
  p < 256 ->
  Int.ltu (Int.repr (Z.of_nat p)) (Int.repr 12) = (p <? 12) /\
  Int.eq (Int.repr (Z.of_nat p)) (Int.repr 255) = (p =? 255).
Proof.
  assert (C : forallb (fun p =>
    Bool.eqb (Int.ltu (Int.repr (Z.of_nat p)) (Int.repr 12)) (p <? 12) &&
    Bool.eqb (Int.eq (Int.repr (Z.of_nat p)) (Int.repr 255)) (p =? 255)) (seq 0 256) = true)
    by (vm_compute; reflexivity).
  intros p R. rewrite forallb_forall in C.
  specialize (C p (proj2 (in_seq 256 0 p) ltac:(lia))).
  apply andb_true_iff in C. destruct C as [A B].
  split; apply Bool.eqb_prop; assumption.
Qed.

Lemma V293_entry_byte_tests : forall ge le M prio b p,
  p < 256 -> get le prio = Some (b,Tint8) ->
  load Tint8 M (b,0%Z) = Some (V293_byteval p) ->
  evalval (V293_task_prio_ge_limit prio) (ge,le,M) =
    Some (Vint32 (if p <? 12 then Int.zero else Int.one)) /\
  evalval (V293_task_prio_is_self prio) (ge,le,M) =
    Some (Vint32 (if p =? 255 then Int.one else Int.zero)).
Proof.
  intros ge le M prio b p R B L.
  destruct (V293_entry_byte_arithmetic p R) as [Lt Eq].
  unfold V293_task_prio_ge_limit,V293_task_prio_is_self.
  cbn [evalval evaltype get_lenv get_genv get_mem]. rewrite B.
  cbn beta iota. rewrite L.
  cbn [V293_byteval cast_eval bop_type bop_int_type bop_eval cmp_int_type is_int_type
    cmp_val cmpu val_eq uop_eval notint].
  rewrite Lt,Eq. destruct (p <? 12), (p =? 255); split; reflexivity.
Qed.

Lemma V293_entry_if_select : forall P ks ge le M cond body (flag : bool),
  evalval cond (ge,le,M) = Some (Vint32 (if flag then Int.one else Int.zero)) ->
  cstepstar P (curs (sifthen cond body),(kenil,ks)) (ge,le,M)
    (curs (if flag then body else sskip None),(kenil,ks)) (ge,le,M).
Proof.
  intros P ks ge le M cond body flag E.
  eapply c_stepstarn. { eapply stmt_step; [reflexivity|constructor]. }
  eapply V293_cstepstar_trans.
  { apply V293_expr_steps. apply evalval_imply_estepstar. exact E. }
  destruct flag; eapply c_stepstarn;
    [eapply stmt_step; [reflexivity|apply svift_step; reflexivity]|apply c_stepstar0|
     eapply stmt_step; [reflexivity|apply sviff_step; reflexivity]|apply c_stepstar0].
Qed.

(* Stop at the return VALUE under kret, before local freeing/caller return. *)
Definition V293_argument_stop old new newprio ks : code :=
  let bad := curs (sskip (Some (V293_byteval 42))) in
  if old <? 12 then
    if new <? 12 then (curs (sskip None),(kenil,ks)) else (bad,(kenil,kret ks))
  else if old =? 255 then
    if new <? 12 then (curs (sskip None),(kenil,ks)) else (bad,(kenil,kret ks))
  else (bad,(kenil,kret (kseq (sifthen (V293_task_prio_ge_limit newprio)
    (srete (econst32 (Int.repr 42)))) ks))).

Theorem V293_task_prio_argument_execution : forall P ks ge le M oldprio newprio bo bn old new,
  old < 256 -> new < 256 ->
  get le oldprio = Some (bo,Tint8) -> get le newprio = Some (bn,Tint8) ->
  load Tint8 M (bo,0%Z) = Some (V293_byteval old) ->
  load Tint8 M (bn,0%Z) = Some (V293_byteval new) ->
  cstepstar P (curs (V293_task_prio_argument_guards oldprio newprio),(kenil,ks))
    (ge,le,M) (V293_argument_stop old new newprio ks) (ge,le,M).
Proof.
  intros P ks ge le M oldprio newprio bo bn old new O N Bo Bn Lo Ln.
  destruct (V293_entry_byte_tests ge le M oldprio bo old O Bo Lo) as [Old Self].
  destruct (V293_entry_byte_tests ge le M newprio bn new N Bn Ln) as [New _].
  assert (NotSelf : evalval (eunop oppsite (V293_task_prio_is_self oldprio)) (ge,le,M) =
    Some (Vint32 (if old =? 255 then Int.zero else Int.one))).
  { cbn [evalval evaltype]. unfold V293_task_prio_is_self in *.
    cbn [evaltype get_lenv get_genv] in *. rewrite Bo. cbn beta iota.
    rewrite Self. cbn [uop_eval notint]. destruct (old =? 255); reflexivity. }
  unfold V293_task_prio_argument_guards,V293_argument_stop.
  eapply c_stepstarn. { eapply stmt_step; [reflexivity|constructor]. }
  destruct (old <? 12) eqn:Eold.
  - eapply V293_cstepstar_trans.
    { eapply V293_entry_if_select with (flag:=false). exact Old. }
    eapply c_stepstarn. { eapply stmt_step; [reflexivity|constructor]. }
    destruct (new <? 12) eqn:Enew.
    + eapply V293_entry_if_select with (flag:=false). exact New.
    + eapply V293_cstepstar_trans.
      { eapply V293_entry_if_select with (flag:=true). exact New. }
      eapply c_stepstarn. { eapply stmt_step; [reflexivity|constructor]. }
      apply V293_expr_steps. apply evalval_imply_estepstar. reflexivity.
  - eapply V293_cstepstar_trans.
    { eapply V293_entry_if_select with (flag:=true). exact Old. }
    destruct (old =? 255) eqn:Eself.
    + eapply V293_cstepstar_trans.
      { eapply V293_entry_if_select with (flag:=false). exact NotSelf. }
      eapply c_stepstarn. { eapply stmt_step; [reflexivity|constructor]. }
      destruct (new <? 12) eqn:Enew.
      * eapply V293_entry_if_select with (flag:=false). exact New.
      * eapply V293_cstepstar_trans.
        { eapply V293_entry_if_select with (flag:=true). exact New. }
        eapply c_stepstarn. { eapply stmt_step; [reflexivity|constructor]. }
        apply V293_expr_steps. apply evalval_imply_estepstar. reflexivity.
    + eapply V293_cstepstar_trans.
      { eapply V293_entry_if_select with (flag:=true). exact NotSelf. }
      eapply c_stepstarn. { eapply stmt_step; [reflexivity|constructor]. }
      apply V293_expr_steps. apply evalval_imply_estepstar. reflexivity.
Qed.

Theorem V293_task_prio_argument_accepts : forall P ks ge le M oldprio newprio bo bn old new,
  old < 256 -> new < 256 ->
  get le oldprio = Some (bo,Tint8) -> get le newprio = Some (bn,Tint8) ->
  load Tint8 M (bo,0%Z) = Some (V293_byteval old) ->
  load Tint8 M (bn,0%Z) = Some (V293_byteval new) ->
  (old < 12 \/ old = 255) -> new < 12 ->
  cstepstar P (curs (V293_task_prio_argument_guards oldprio newprio),(kenil,ks))
    (ge,le,M) (curs (sskip None),(kenil,ks)) (ge,le,M).
Proof.
  intros P ks ge le M oldprio newprio bo bn old new O N Bo Bn Lo Ln Valid NV.
  pose proof (V293_task_prio_argument_execution P ks ge le M oldprio newprio bo bn old new O N Bo Bn Lo Ln) as E.
  unfold V293_argument_stop in E. assert (NL : (new <? 12)=true) by (apply Nat.ltb_lt; exact NV).
  rewrite NL in E. destruct Valid as [V| ->].
  - rewrite (proj2 (Nat.ltb_lt old 12) V) in E. exact E.
  - exact E.
Qed.

(* Global current pointer, read only by the SELF branch. *)
Lemma V293_entry_current_prio_eval : forall ge le M current bc bt base p,
  get le current = None -> get ge current = Some (bc,Tptr V293_tcb_type) ->
  load (Tptr V293_tcb_type) M (bc,0%Z) = Some (Vptr (bt,Int.repr base)) ->
  (0 <= base)%Z -> (base+50 <= Int.max_unsigned)%Z ->
  load Tint8 M (bt,(base+50)%Z) = Some (V293_byteval p) ->
  evaltype (efield (ederef (evar current)) 16%Z) (ge,le,M) = Some Tint8 /\
  evalval (efield (ederef (evar current)) 16%Z) (ge,le,M) = Some (V293_byteval p).
Proof.
  intros ge le M current bc bt base p N G L B R V.
  assert (T : evaltype (ederef (evar current)) (ge,le,M) = Some V293_tcb_type).
  { cbn [evaltype get_lenv get_genv]. rewrite N,G. reflexivity. }
  assert (F : evaltype (efield (ederef (evar current)) 16%Z) (ge,le,M) = Some Tint8).
  { cbn [evaltype get_lenv get_genv]. rewrite N,G. reflexivity. }
  split; [exact F | ]. cbn [evalval]. rewrite F.
  cbn [evaladdr evalval evaltype get_lenv get_genv get_mem]. rewrite N,G.
  cbn beta iota. rewrite L. unfold getoff. rewrite T.
  change (load Tint8 M (bt,Int.unsigned (Int.add (Int.repr (Int.unsigned (Int.repr base))) (Int.repr 50))) = Some (V293_byteval p)).
  rewrite Int.repr_unsigned. unfold Int.add.
  rewrite (Int.unsigned_repr base), (Int.unsigned_repr 50) by lia.
  rewrite Int.unsigned_repr by lia. exact V.
Qed.

Lemma V293_entry_array_eval : forall ge le M table index b bi p value,
  get le table = None -> get ge table = Some (b,Tarray (Tptr V293_tcb_type) 13) ->
  get le index = Some (bi,Tint8) -> load Tint8 M (bi,0%Z) = Some (V293_byteval p) -> p < 13 ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat p)%Z) = Some value ->
  evaltype (earrayelem (evar table) (evar index)) (ge,le,M) = Some (Tptr V293_tcb_type) /\
  evalval (earrayelem (evar table) (evar index)) (ge,le,M) = Some value.
Proof.
  intros ge le M table index b bi p value Nt Gt Bi L R V.
  destruct (V293_rekey_array_address ge le M table index V293_tcb_type b bi p Nt Gt Bi L R) as [T A].
  split; [exact T | ]. cbn [evalval]. rewrite T.
  cbn [evalval get_lenv get_genv get_mem]. rewrite Nt,Gt,Bi.
  cbn beta iota. rewrite L. unfold V293_byteval.
  cbn [evaltype get_lenv get_genv]. rewrite Nt,Gt,Bi. cbn beta iota.
  change (load (Tptr V293_tcb_type) M
    (b,Int.unsigned (Int.add Int.zero (Int.mul (Int.repr 4) (Int.repr (Z.of_nat p))))) = Some value).
  rewrite Int.add_zero_l. unfold Int.mul.
  rewrite (Int.unsigned_repr 4) by (change (0<=4<=4294967295)%Z; lia).
  rewrite (Int.unsigned_repr (Z.of_nat p)) by (change (0<=Z.of_nat p<=4294967295)%Z; lia).
  rewrite Int.unsigned_repr by (change (0<=4*Z.of_nat p<=4294967295)%Z; lia). exact V.
Qed.


Lemma V293_entry_null_eval : forall ge le M e value,
  evaltype e (ge,le,M) = Some (Tptr V293_tcb_type) ->
  evalval e (ge,le,M) = Some value ->
  (value = Vnull \/ exists a, value = Vptr a) ->
  evalval (V293_task_prio_null_test e) (ge,le,M) =
    Some (Vint32 (if match value with Vnull => true | _ => false end then Int.one else Int.zero)) /\
  evalval (eunop oppsite (V293_task_prio_null_test e)) (ge,le,M) =
    Some (Vint32 (if match value with Vnull => true | _ => false end then Int.zero else Int.one)).
Proof.
  intros ge le M e value T V Cases.
  unfold V293_task_prio_null_test.
  cbn [evaltype evalval]. rewrite T,V.
  destruct Cases as [-> | [a ->]]; [split; reflexivity| ].
  destruct a; split; reflexivity.
Qed.

(* Successful 93--104 path. No ptcb value is assumed in the entry memory. *)
Theorem V293_task_prio_entry_lookup_execution :
  forall P ks ge le M table oldprio newprio ptcb current (cpu_sr : var) (exit_id : fid)
    b bo bn bc bcur bct base old new curprio next,
  old < 256 -> new < 12 ->
  let resolved := if old =? 255 then curprio else old in
  resolved < 13 ->
  get le table = None -> get ge table = Some (b,Tarray (Tptr V293_tcb_type) 13) ->
  get le oldprio = Some (bo,Tint8) -> get le newprio = Some (bn,Tint8) ->
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  load Tint8 M (bo,0%Z) = Some (V293_byteval old) ->
  load Tint8 M (bn,0%Z) = Some (V293_byteval new) ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat new)%Z) = Some Vnull ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat resolved)%Z) = Some (Vptr next) ->
  b <> bo -> b <> bc -> bo <> bn -> bc <> bn -> bc <> bo ->
  (old = 255 ->
    get le current = None /\ get ge current = Some (bcur,Tptr V293_tcb_type) /\
    load (Tptr V293_tcb_type) M (bcur,0%Z) = Some (Vptr (bct,Int.repr base)) /\
    (0 <= base)%Z /\ (base+50 <= Int.max_unsigned)%Z /\
    load Tint8 M (bct,(base+50)%Z) = Some (V293_byteval curprio) /\
    (exists v, get M (bo,0%Z) = Some (true,v))) ->
  V293_bytes_writable M bc 0%Z 4 ->
  exists Mf,
  resolved <> new /\
  cstepstar P (curs (V293_task_prio_entry_lookup table oldprio newprio ptcb current cpu_sr exit_id),
    (kenil,ks)) (ge,le,M) (curs (sskip None),(kenil,ks)) (ge,le,Mf) /\
  load Tint8 Mf (bo,0%Z) = Some (V293_byteval resolved) /\
  load Tint8 Mf (bn,0%Z) = Some (V293_byteval new) /\
  load (Tptr V293_tcb_type) Mf (bc,0%Z) = Some (Vptr next) /\
  load (Tptr V293_tcb_type) Mf (b,(4*Z.of_nat resolved)%Z) = Some (Vptr next) /\
  load (Tptr V293_tcb_type) Mf (b,(4*Z.of_nat new)%Z) = Some Vnull /\
  V293_bytes_writable Mf bc 0%Z 4 /\
  (forall c i, c <> bo -> c <> bc -> get Mf (c,i) = get M (c,i)).
Proof.
  intros P ks ge le M table oldprio newprio ptcb current cpu_sr exit_id
    b bo bn bc bcur bct base old new curprio next O N resolved R Nt Gt Bo Bn Bc Lo Ln Empty Slot
    Tbo Tbc Onew Cnew CO Self CW.
  assert (Different : resolved <> new).
  { intro E. rewrite E in Slot. rewrite Empty in Slot. discriminate. }
  destruct (V293_entry_byte_tests ge le M oldprio bo old O Bo Lo) as [_ SelfTest].
  set (Ms := if old =? 255 then V293_put_byte M (bo,0%Z) curprio else M).
  assert (SelfStep : forall tail,
    cstepstar P (curs (V293_task_prio_self_read oldprio current),(kenil,tail)) (ge,le,M)
      (curs (sskip None),(kenil,tail)) (ge,le,Ms)).
  { intro tail. unfold V293_task_prio_self_read,Ms.
    destruct (old =? 255) eqn:S.
    - destruct (Self (proj1 (Nat.eqb_eq old 255) S)) as (Nc & Gc & Pc & Base & Limit & Prio & W).
      assert (CP : curprio < 256) by (unfold resolved in R; simpl in R; lia).
      destruct (V293_entry_current_prio_eval ge le M current bcur bct base curprio Nc Gc Pc Base Limit Prio) as [FieldType FieldValue].
      eapply V293_rekey_if_execution with (flag:=true); [exact SelfTest| |discriminate].
      intros _. eapply V293_coordinate_local_assignment; eassumption.
    - eapply V293_rekey_if_execution with (flag:=false); [exact SelfTest|discriminate|reflexivity]. }
  assert (SF : forall c i, c <> bo -> get Ms (c,i) = get M (c,i)).
  { intros c i D. unfold Ms. destruct (old =? 255); [apply V293_put_byte_other; congruence|reflexivity]. }
  assert (SL : forall tp c i, c <> bo -> load tp Ms (c,i) = load tp M (c,i)).
  { intros tp c i D. apply V293_load_block_frame. intros j. apply SF; exact D. }
  assert (ResolvedRead : load Tint8 Ms (bo,0%Z) = Some (V293_byteval resolved)).
  { unfold Ms,resolved. destruct (old =? 255) eqn:S.
    - apply V293_put_byte_load. unfold resolved in R. simpl in R. lia.
    - exact Lo. }
  assert (SlotS : load (Tptr V293_tcb_type) Ms (b,(4*Z.of_nat resolved)%Z) = Some (Vptr next)).
  { rewrite SL by congruence. exact Slot. }
  assert (W : V293_bytes_writable Ms bc 0%Z 4).
  { intros k K. unfold V293_bytes_writable in CW. rewrite SF by exact CO. apply CW; exact K. }
  destruct (V293_storebytes_exists (encode_val (Tptr V293_tcb_type) (Vptr next)) Ms bc 0%Z)
    as [Mf Store].
  { rewrite encode_val_length. exact W. }
  assert (PF : forall c i, c <> bc -> get Mf (c,i) = get Ms (c,i)).
  { intros c i D. eapply V293_storebytes_outside; [exact Store|left;exact D]. }
  assert (PL : forall tp c i, c <> bc -> load tp Mf (c,i) = load tp Ms (c,i)).
  { intros tp c i D. apply V293_load_block_frame. intro j. apply PF; exact D. }
  assert (Pointer : load (Tptr V293_tcb_type) Mf (bc,0%Z) = Some (Vptr next)).
  { eapply V293_store_readback; [reflexivity|exact Store]. }
  destruct (V293_entry_array_eval ge le M table newprio b bn new Vnull Nt Gt Bn Ln ltac:(lia) Empty)
    as [NewType NewValue].
  assert (TargetTest : evalval (eunop oppsite (V293_task_prio_null_test
    (earrayelem (evar table) (evar newprio)))) (ge,le,M) = Some (Vint32 Int.zero)).
  { apply (proj2 (V293_entry_null_eval ge le M _ Vnull NewType NewValue (or_introl eq_refl))). }
  destruct (V293_entry_array_eval ge le Ms table oldprio b bo resolved (Vptr next)
    Nt Gt Bo ResolvedRead ltac:(lia) SlotS) as [OldType OldValue].
  assert (LookupStep : forall tail,
    cstepstar P (curs (V293_task_prio_lookup table oldprio ptcb),(kenil,tail)) (ge,le,Ms)
      (curs (sskip None),(kenil,tail)) (ge,le,Mf)).
  { intro tail. unfold V293_task_prio_lookup.
    eapply V293_assign_pointer_execution with (tr:=Tptr V293_tcb_type) (b:=bc) (off:=0%Z);
      try eassumption.
    - cbn [evaltype get_lenv]. rewrite Bc. reflexivity.
    - apply eq_vptr. eauto.
    - cbn [evaladdr get_lenv]. rewrite Bc. reflexivity.
    - change (0<=0<=4294967295)%Z. lia. }
  assert (NullTest : evalval (V293_task_prio_null_test (evar ptcb)) (ge,le,Mf) = Some (Vint32 Int.zero)).
  { unfold V293_task_prio_null_test. cbn [evalval evaltype get_lenv get_genv get_mem].
    rewrite Bc. cbn beta iota. rewrite Pointer. destruct next; reflexivity. }
  exists Mf. split; [exact Different| ]. split.
  - unfold V293_task_prio_entry_lookup.
    eapply V293_rekey_sequence_execution with (M1:=M).
    + intro tail. eapply V293_rekey_if_execution with (flag:=false); [exact TargetTest|discriminate|reflexivity].
    + eapply V293_rekey_sequence_execution with (M1:=Ms); [exact SelfStep| ].
      eapply V293_rekey_sequence_execution with (M1:=Mf); [exact LookupStep| ].
      eapply V293_rekey_if_execution with (flag:=false); [exact NullTest|discriminate|reflexivity].
  - split; [rewrite PL by congruence; exact ResolvedRead| ].
    split; [rewrite PL,SL by congruence; exact Ln| ].
    split; [exact Pointer| ]. split; [rewrite PL by congruence; exact SlotS| ].
    split; [rewrite PL,SL by congruence; exact Empty| ]. split.
    + intros k K. exists (nth k (encode_val (Tptr V293_tcb_type) (Vptr next)) Undef).
      eapply V293_storebytes_nth; [exact Store|rewrite encode_val_length;exact K].
    + intros c i A B. rewrite PF by exact B. apply SF; exact A.
Qed.

(* Two physical entries differ only in the oldprio selector byte. The ptcb
   local starts NULL, not at the task pointer that lookup must produce. *)
Definition V293_entry_fixture_ge : env :=
  set (set emp 500%Z (50%positive,Tarray (Tptr V293_tcb_type) 13))
    750%Z (80%positive,Tptr V293_tcb_type).
Definition V293_entry_fixture_le : env :=
  set (set (set emp 501%Z (51%positive,Tint8)) 502%Z (52%positive,Tint8))
    400%Z (40%positive,Tptr V293_tcb_type).
Definition V293_entry_fixture_core : mem :=
  V293_fixture_put_bytes
    (V293_fixture_put_bytes emp 80%positive 0%Z
      (encode_val (Tptr V293_tcb_type) (Vptr (41%positive,Int.repr 8))))
    40%positive 0%Z (encode_val (Tptr V293_tcb_type) Vnull).
Definition V293_entry_fixture_mem (self : bool) : mem :=
  V293_put_byte (V293_put_byte (V293_put_byte
    (V293_fixture_put_table V293_entry_fixture_core 50%positive 0%Z V293_prefix_fixture_entries)
    (41%positive,58%Z) 8) (51%positive,0%Z) (if self then 255 else 8)) (52%positive,0%Z) 6.

Lemma V293_entry_fixture_delta : forall self c i,
  (c,i) <> (51%positive,0%Z) ->
  get (V293_entry_fixture_mem self) (c,i) = get (V293_entry_fixture_mem false) (c,i).
Proof.
  intros self c i Apart. unfold V293_entry_fixture_mem.
  destruct (addr_eq_dec (c,i) (52%positive,0%Z)) as [-> | D].
  - repeat rewrite V293_put_byte_get_same. reflexivity.
  - repeat rewrite (V293_put_byte_other _ (52%positive,0%Z) _ (c,i)) by congruence.
    repeat rewrite (V293_put_byte_other _ (51%positive,0%Z) _ (c,i)) by congruence. reflexivity.
Qed.

Local Ltac entry_fixture_bind :=
  unfold V293_entry_fixture_ge,V293_entry_fixture_le;
  repeat first [rewrite map_get_set | rewrite map_get_set' by discriminate];
  try reflexivity.

Lemma V293_entry_fixture_resources : forall self,
  let M := V293_entry_fixture_mem self in
  load Tint8 M (51%positive,0%Z) = Some (V293_byteval (if self then 255 else 8)) /\
  load Tint8 M (52%positive,0%Z) = Some (V293_byteval 6) /\
  load (Tptr V293_tcb_type) M (50%positive,24%Z) = Some Vnull /\
  load (Tptr V293_tcb_type) M (50%positive,32%Z) = Some (Vptr (41%positive,Int.repr 8)) /\
  load (Tptr V293_tcb_type) M (80%positive,0%Z) = Some (Vptr (41%positive,Int.repr 8)) /\
  load Tint8 M (41%positive,58%Z) = Some (V293_byteval 8) /\
  load (Tptr V293_tcb_type) M (40%positive,0%Z) = Some Vnull /\
  (exists v, get M (51%positive,0%Z) = Some (true,v)) /\
  V293_bytes_writable M 40%positive 0%Z 4.
Proof.
  intro self. cbn zeta.
  assert (Outer : forall c i, c <> 41%positive -> c <> 51%positive -> c <> 52%positive ->
    get (V293_entry_fixture_mem self) (c,i) =
      get (V293_fixture_put_table V293_entry_fixture_core 50%positive 0%Z V293_prefix_fixture_entries) (c,i)).
  { intros c i A B C. unfold V293_entry_fixture_mem.
    repeat rewrite V293_put_byte_other by (intro E; inversion E; congruence). reflexivity. }
  assert (LF : forall tp c i, c <> 41%positive -> c <> 51%positive -> c <> 52%positive ->
    load tp (V293_entry_fixture_mem self) (c,i) =
      load tp (V293_fixture_put_table V293_entry_fixture_core 50%positive 0%Z V293_prefix_fixture_entries) (c,i)).
  { intros tp c i A B C. apply V293_load_block_frame. intro j. apply Outer; assumption. }
  split.
  - unfold V293_entry_fixture_mem. rewrite V293_put_byte_other_load by discriminate.
    apply V293_put_byte_load. destruct self; lia.
  - split; [unfold V293_entry_fixture_mem; apply V293_put_byte_load; lia | ]. split.
    + rewrite LF by discriminate. change (load (Tptr V293_tcb_type)
        (V293_fixture_put_table V293_entry_fixture_core 50%positive 0%Z V293_prefix_fixture_entries)
        (50%positive,(0+4*Z.of_nat 6)%Z) = Some (nth 6 V293_prefix_fixture_entries Vnull)).
      apply V293_fixture_table_slot; [repeat constructor|cbn;lia].
    + split.
      * rewrite LF by discriminate. change (load (Tptr V293_tcb_type)
          (V293_fixture_put_table V293_entry_fixture_core 50%positive 0%Z V293_prefix_fixture_entries)
          (50%positive,(0+4*Z.of_nat 8)%Z) = Some (nth 8 V293_prefix_fixture_entries Vnull)).
        apply V293_fixture_table_slot; [repeat constructor|cbn;lia].
      * assert (CoreFrame : forall tp c i, c <> 41%positive -> c <> 51%positive -> c <> 52%positive -> c <> 50%positive ->
          load tp (V293_entry_fixture_mem self) (c,i) = load tp V293_entry_fixture_core (c,i)).
        { intros tp c i A B C D. apply V293_load_block_frame. intro j.
          rewrite Outer by assumption. apply V293_fixture_table_outside. exact D. }
        split.
        -- rewrite CoreFrame by discriminate. unfold V293_entry_fixture_core.
           unfold load,loadm. rewrite V293_loadbytes_ext with
             (M:=V293_fixture_put_bytes emp 80%positive 0%Z
               (encode_val (Tptr V293_tcb_type) (Vptr (41%positive,Int.repr 8)))).
           ++ apply V293_fixture_pointer_load. reflexivity.
           ++ intros k K. apply V293_fixture_bytes_outside. left; discriminate.
        -- split.
           ++ unfold V293_entry_fixture_mem. repeat rewrite V293_put_byte_other_load by discriminate.
              apply V293_put_byte_load. lia.
           ++ split.
              ** rewrite CoreFrame by discriminate. unfold V293_entry_fixture_core.
                 apply V293_fixture_pointer_load. reflexivity.
              ** split.
                 --- unfold V293_entry_fixture_mem. rewrite V293_put_byte_other by discriminate.
                     eexists. apply V293_put_byte_get_same.
                 --- intros k K. rewrite Outer by discriminate.
                     rewrite V293_fixture_table_outside by discriminate.
                     unfold V293_entry_fixture_core.
                     exists (nth k (encode_val (Tptr V293_tcb_type) Vnull) Undef).
                     apply V293_fixture_bytes_nth. rewrite encode_val_length. exact K.
Qed.

Theorem V293_task_prio_entry_witness : forall self P ks,
  exists Mf,
  load (Tptr V293_tcb_type) (V293_entry_fixture_mem self) (40%positive,0%Z) = Some Vnull /\
  cstepstar P (curs (V293_task_prio_argument_guards 501%Z 502%Z),(kenil,ks))
    (V293_entry_fixture_ge,V293_entry_fixture_le,V293_entry_fixture_mem self)
    (curs (sskip None),(kenil,ks)) (V293_entry_fixture_ge,V293_entry_fixture_le,V293_entry_fixture_mem self) /\
  cstepstar P (curs (V293_task_prio_entry_lookup 500%Z 501%Z 502%Z 400%Z 750%Z 751%Z 752%Z),(kenil,ks))
    (V293_entry_fixture_ge,V293_entry_fixture_le,V293_entry_fixture_mem self)
    (curs (sskip None),(kenil,ks)) (V293_entry_fixture_ge,V293_entry_fixture_le,Mf) /\
  load Tint8 Mf (51%positive,0%Z) = Some (V293_byteval 8) /\
  load Tint8 Mf (52%positive,0%Z) = Some (V293_byteval 6) /\
  load (Tptr V293_tcb_type) Mf (40%positive,0%Z) = Some (Vptr (41%positive,Int.repr 8)) /\
  load (Tptr V293_tcb_type) Mf (50%positive,32%Z) = Some (Vptr (41%positive,Int.repr 8)) /\
  load (Tptr V293_tcb_type) Mf (50%positive,24%Z) = Some Vnull.
Proof.
  intros self P ks.
  destruct (V293_entry_fixture_resources self) as (Lo & Ln & Empty & Slot & Current & Prio & Initial & Wo & CW).
  assert (Resolved : (if (if self then 255 else 8) =? 255 then 8 else (if self then 255 else 8)) = 8)
    by (destruct self; reflexivity).
  destruct (V293_task_prio_entry_lookup_execution P ks V293_entry_fixture_ge V293_entry_fixture_le
    (V293_entry_fixture_mem self) 500%Z 501%Z 502%Z 400%Z 750%Z 751%Z 752%Z
    50%positive 51%positive 52%positive 40%positive 80%positive 41%positive 8%Z
    (if self then 255 else 8) 6 8 (41%positive,Int.repr 8))
    as (Mf & Different & Exec & Old & New & Pointer & OldSlot & NewSlot & W & Frame).
  all: try assumption; try discriminate; try (entry_fixture_bind; reflexivity);
    try (destruct self; cbn; lia); try (rewrite Resolved; exact Slot).
  - intro IsSelf. repeat split; try (entry_fixture_bind; reflexivity); try assumption;
      try (change (0<=8)%Z; lia); try (change (8+50<=4294967295)%Z; lia).
  - exists Mf. split; [exact Initial | ]. split.
    + eapply V293_task_prio_argument_accepts with (old:=if self then 255 else 8) (new:=6) (bo:=51%positive) (bn:=52%positive); try eassumption;
        try (entry_fixture_bind; reflexivity); destruct self; cbn; intuition lia.
    + rewrite Resolved in *. split; [exact Exec | ].
      split; [exact Old | ]. split; [exact New | ]. split; [exact Pointer | ].
      split; assumption.
Qed.

(* The macro's symbol is static: evaluating its address never loads M. *)
Lemma V293_reserved_symbol_eval : forall ge le M reserved br,
  get le reserved = None -> get ge reserved = Some (br,Tint8) ->
  evaltype (V293_task_prio_reserved_expr reserved) (ge,le,M) = Some (Tptr V293_tcb_type) /\
  evalval (V293_task_prio_reserved_expr reserved) (ge,le,M) = Some (Vptr (br,Int.zero)).
Proof.
  intros ge le M reserved br N G. unfold V293_task_prio_reserved_expr.
  cbn [evaltype evalval evaladdr get_lenv get_genv get_mem]. rewrite N,G. split; reflexivity.
Qed.

Definition V293_reserved_matches (br : block) (value : val) : bool :=
  match value with
  | Vptr (b,i) => if peq b br then Int.eq i Int.zero else false
  | _ => false
  end.

Lemma V293_reserved_matches_pointer : forall br next,
  V293_reserved_matches br (Vptr next) = true <-> next = (br,Int.zero).
Proof.
  intros br [b i]. unfold V293_reserved_matches.
  destruct (peq b br) as [-> | D].
  - split.
    + intro E. pose proof (Int.eq_spec i Int.zero) as I. rewrite E in I. subst; reflexivity.
    + intro E. inversion E; subst. apply Int.eq_true.
  - split; [discriminate | intro E; inversion E; contradiction].
Qed.

Lemma V293_reserved_test_eval : forall ge le M ptcb reserved bc br value,
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  load (Tptr V293_tcb_type) M (bc,0%Z) = Some value ->
  (value = Vnull \/ exists next, value = Vptr next) ->
  get le reserved = None -> get ge reserved = Some (br,Tint8) ->
  evalval (V293_task_prio_reserved_test ptcb reserved) (ge,le,M) =
    Some (Vint32 (if V293_reserved_matches br value then Int.one else Int.zero)).
Proof.
  intros ge le M ptcb reserved bc br value B L Cases N G.
  unfold V293_task_prio_reserved_test,V293_task_prio_reserved_expr.
  cbn [evalval evaltype evaladdr get_lenv get_genv get_mem]. rewrite B,N,G.
  cbn beta iota. rewrite L.
  destruct Cases as [-> | [[b i] ->]]; [reflexivity | ].
  cbn [bop_type is_int_type bop_eval val_eq V293_reserved_matches].
  destruct (peq b br), (Int.eq i Int.zero); reflexivity.
Qed.

(* Both guard choices execute the real condition; the true choice stops
   before the actual exit call, not after a made-up successful call. *)
Theorem V293_task_prio_reserved_select :
  forall P ks ge le M ptcb reserved (cpu_sr : var) (exit_id : fid) bc br value,
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  load (Tptr V293_tcb_type) M (bc,0%Z) = Some value ->
  (value = Vnull \/ exists next, value = Vptr next) ->
  get le reserved = None -> get ge reserved = Some (br,Tint8) ->
  cstepstar P (curs (V293_task_prio_reserved_guard ptcb reserved cpu_sr exit_id),(kenil,ks))
    (ge,le,M)
    (curs (if V293_reserved_matches br value
      then V293_task_prio_reserved_error cpu_sr exit_id else sskip None),(kenil,ks)) (ge,le,M).
Proof.
  intros P ks ge le M ptcb reserved cpu_sr exit_id bc br value B L Cases N G.
  unfold V293_task_prio_reserved_guard. apply V293_entry_if_select.
  eapply V293_reserved_test_eval; eassumption.
Qed.

Lemma V293_task_prio_reserved_accepts :
  forall P ks ge le M ptcb reserved (cpu_sr : var) (exit_id : fid) bc br next,
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  load (Tptr V293_tcb_type) M (bc,0%Z) = Some (Vptr next) ->
  get le reserved = None -> get ge reserved = Some (br,Tint8) ->
  next <> (br,Int.zero) ->
  cstepstar P (curs (V293_task_prio_reserved_guard ptcb reserved cpu_sr exit_id),(kenil,ks))
    (ge,le,M) (curs (sskip None),(kenil,ks)) (ge,le,M).
Proof.
  intros P ks ge le M ptcb reserved cpu_sr exit_id bc br next B L N G Apart.
  pose proof (V293_task_prio_reserved_select P ks ge le M ptcb reserved cpu_sr exit_id bc br
    (Vptr next) B L (or_intror (ex_intro _ next eq_refl)) N G) as E.
  assert (V293_reserved_matches br (Vptr next) = false) as F.
  { destruct (V293_reserved_matches br (Vptr next)) eqn:Choice; [ |reflexivity].
    apply V293_reserved_matches_pointer in Choice. contradiction. }
  rewrite F in E. exact E.
Qed.

Theorem V293_task_prio_entry_reserved_execution :
  forall P ks ge le M table oldprio newprio ptcb current reserved (cpu_sr : var) (exit_id : fid)
    b bo bn bc bcur bct base old new curprio next br,
  old < 256 -> new < 12 ->
  let resolved := if old =? 255 then curprio else old in
  resolved < 13 ->
  get le table = None -> get ge table = Some (b,Tarray (Tptr V293_tcb_type) 13) ->
  get le oldprio = Some (bo,Tint8) -> get le newprio = Some (bn,Tint8) ->
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  load Tint8 M (bo,0%Z) = Some (V293_byteval old) ->
  load Tint8 M (bn,0%Z) = Some (V293_byteval new) ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat new)%Z) = Some Vnull ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat resolved)%Z) = Some (Vptr next) ->
  b <> bo -> b <> bc -> bo <> bn -> bc <> bn -> bc <> bo ->
  (old = 255 ->
    get le current = None /\ get ge current = Some (bcur,Tptr V293_tcb_type) /\
    load (Tptr V293_tcb_type) M (bcur,0%Z) = Some (Vptr (bct,Int.repr base)) /\
    (0 <= base)%Z /\ (base+50 <= Int.max_unsigned)%Z /\
    load Tint8 M (bct,(base+50)%Z) = Some (V293_byteval curprio) /\
    (exists v, get M (bo,0%Z) = Some (true,v))) ->
  get le reserved = None -> get ge reserved = Some (br,Tint8) ->
  next <> (br,Int.zero) ->
  V293_bytes_writable M bc 0%Z 4 ->
  exists Mf,
  resolved <> new /\
  cstepstar P (curs (V293_task_prio_entry_reserved table oldprio newprio ptcb current reserved cpu_sr exit_id),
    (kenil,ks)) (ge,le,M) (curs (sskip None),(kenil,ks)) (ge,le,Mf) /\
  load Tint8 Mf (bo,0%Z) = Some (V293_byteval resolved) /\
  load Tint8 Mf (bn,0%Z) = Some (V293_byteval new) /\
  load (Tptr V293_tcb_type) Mf (bc,0%Z) = Some (Vptr next) /\
  load (Tptr V293_tcb_type) Mf (b,(4*Z.of_nat resolved)%Z) = Some (Vptr next) /\
  load (Tptr V293_tcb_type) Mf (b,(4*Z.of_nat new)%Z) = Some Vnull /\
  V293_bytes_writable Mf bc 0%Z 4 /\
  (forall c i, c <> bo -> c <> bc -> get Mf (c,i) = get M (c,i)).
Proof.
  intros P ks ge le M table oldprio newprio ptcb current reserved cpu_sr exit_id
    b bo bn bc bcur bct base old new curprio next br O N resolved R Nt Gt Bo Bn Bc Lo Ln Empty Slot
    Tbo Tbc Onew Cnew CO Self Nr Gr Apart W.
  destruct (V293_task_prio_entry_lookup_execution P (kseq (V293_task_prio_reserved_guard ptcb reserved cpu_sr exit_id) ks)
    ge le M table oldprio newprio ptcb current cpu_sr exit_id
    b bo bn bc bcur bct base old new curprio next)
    as (Mf & Different & Lookup & Post); try eassumption.
  assert (Pointer : load (Tptr V293_tcb_type) Mf (bc,0%Z) = Some (Vptr next))
    by (destruct Post as (_ & _ & Pointer & _); exact Pointer).
  exists Mf. split; [exact Different| ]. split; [ | exact Post].
  unfold V293_task_prio_entry_reserved.
  eapply c_stepstarn. { eapply stmt_step; [reflexivity|constructor]. }
  eapply V293_cstepstar_trans; [exact Lookup | ].
  eapply c_stepstarn. { eapply stmt_step; [reflexivity|constructor]. }
  eapply V293_task_prio_reserved_accepts; eassumption.
Qed.

(* Equality preservation for exactly the three pointer roles used by the
   source: null, reserved token, and a real task distinct from that token. *)
Theorem V293_reserved_three_way_equality : forall br next,
  next <> (br,Int.zero) ->
  val_eq Vnull (Vptr (br,Int.zero)) = Some (Vint32 Int.zero) /\
  val_eq (Vptr (br,Int.zero)) (Vptr (br,Int.zero)) = Some (Vint32 Int.one) /\
  val_eq (Vptr next) (Vptr (br,Int.zero)) = Some (Vint32 Int.zero).
Proof.
  intros br [b i] Apart. split; [reflexivity | ]. split.
  - unfold val_eq. destruct (peq br br); [rewrite Int.eq_true; reflexivity | contradiction].
  - unfold val_eq. destruct (peq b br) as [-> | D]; [ | reflexivity].
    destruct (Int.eq i Int.zero) eqn:E; [ | reflexivity].
    pose proof (Int.eq_spec i Int.zero) as I. rewrite E in I. subst. contradiction.
Qed.

(* Neutralizing only non-collision admits this actual erroneous
   classification; no memory, ABI, or shared-invariant counterexample claimed. *)
Theorem V293_reserved_noncollision_needed : forall br,
  V293_reserved_matches br (Vptr (br,Int.zero)) = true /\
  V293_reserved_matches br Vnull = false.
Proof.
  intro br. split; [apply V293_reserved_matches_pointer; reflexivity | reflexivity].
Qed.

Definition V293_reserved_fixture_ge : env :=
  set V293_entry_fixture_ge 900%Z (99%positive,Tint8).

Local Ltac reserved_fixture_bind :=
  unfold V293_reserved_fixture_ge,V293_entry_fixture_ge,V293_entry_fixture_le;
  repeat first [rewrite map_get_set | rewrite map_get_set' by discriminate];
  try reflexivity.

Theorem V293_task_prio_reserved_witness : forall self P ks,
  exists Mf,
  load (Tptr V293_tcb_type) (V293_entry_fixture_mem self) (40%positive,0%Z) = Some Vnull /\
  cstepstar P (curs (V293_task_prio_entry_reserved
    500%Z 501%Z 502%Z 400%Z 750%Z 900%Z 751%Z 752%Z),(kenil,ks))
    (V293_reserved_fixture_ge,V293_entry_fixture_le,V293_entry_fixture_mem self)
    (curs (sskip None),(kenil,ks)) (V293_reserved_fixture_ge,V293_entry_fixture_le,Mf) /\
  load Tint8 Mf (51%positive,0%Z) = Some (V293_byteval 8) /\
  load Tint8 Mf (52%positive,0%Z) = Some (V293_byteval 6) /\
  load (Tptr V293_tcb_type) Mf (40%positive,0%Z) = Some (Vptr (41%positive,Int.repr 8)) /\
  load (Tptr V293_tcb_type) Mf (50%positive,32%Z) = Some (Vptr (41%positive,Int.repr 8)) /\
  load (Tptr V293_tcb_type) Mf (50%positive,24%Z) = Some Vnull.
Proof.
  intros self P ks.
  destruct (V293_entry_fixture_resources self) as (Lo & Ln & Empty & Slot & Current & Prio & Initial & Wo & CW).
  assert (Resolved : (if (if self then 255 else 8) =? 255 then 8 else (if self then 255 else 8)) = 8)
    by (destruct self; reflexivity).
  destruct (V293_task_prio_entry_reserved_execution P ks V293_reserved_fixture_ge V293_entry_fixture_le
    (V293_entry_fixture_mem self) 500%Z 501%Z 502%Z 400%Z 750%Z 900%Z 751%Z 752%Z
    50%positive 51%positive 52%positive 40%positive 80%positive 41%positive 8%Z
    (if self then 255 else 8) 6 8 (41%positive,Int.repr 8) 99%positive)
    as (Mf & Different & Exec & Old & New & Pointer & OldSlot & NewSlot & W & Frame).
  all: try assumption; try discriminate; try (reserved_fixture_bind; reflexivity);
    try (destruct self; cbn; lia); try (rewrite Resolved; exact Slot).
  - intro IsSelf. repeat split; try (reserved_fixture_bind; reflexivity); try assumption;
      try (change (0<=8)%Z; lia); try (change (8+50<=4294967295)%Z; lia).
  - exists Mf. split; [exact Initial | ]. rewrite Resolved in *.
    split; [exact Exec | ]. split; [exact Old | ]. split; [exact New | ].
    split; [exact Pointer | ]. split; assumption.
Qed.

(* The entry execution produces the pointer/old value needed by the real tail.
   Token identity and shared-state/init obligations remain explicit. *)
Local Opaque HalfPermMap.set.
Theorem V293_task_prio_entry_update_execution :
  forall P ks ge le M table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp be ebase elo ehi xi bi ny nby nbx
    current reserved (cpu_sr : var) (exit_id : fid) bcur bct curbase rb curprio,
  initial < 256 -> new < 12 ->
  let old := if initial =? 255 then curprio else initial in
  old < 13 -> lo < 256 -> hi < 256 -> br <> bg ->
  (0 <= base)%Z -> (base+55 <= Int.max_unsigned)%Z ->
  get le table = None -> get ge table = Some (b,Tarray (Tptr V293_tcb_type) 13) ->
  get le oldprio = Some (bo,Tint8) -> get le newprio = Some (bn,Tint8) ->
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  b <> bo -> b <> bn -> b <> bc -> b <> bt ->
  b <> dy -> b <> dby -> b <> dx -> b <> br -> b <> bg ->
  load Tint8 M (bo,0%Z) = Some (V293_byteval initial) ->
  load Tint8 M (bn,0%Z) = Some (V293_byteval new) ->
  V293_bytes_writable M b (4*Z.of_nat old)%Z 4 ->
  V293_bytes_writable M b (4*Z.of_nat new)%Z 4 ->
  length entries = 13 -> V293_table_loads V293_tcb_type M b entries ->
  get le yo = Some (dy,Tint8) -> get le byo = Some (dby,Tint8) -> get le xo = Some (dx,Tint8) ->
  get le rows = None -> get ge rows = Some (br,Tarray Tint8 2) ->
  get le group = None -> get ge group = Some (bg,Tint8) ->
  dy <> dby -> dy <> dx -> dby <> dx ->
  (forall c, c = dy \/ c = dby \/ c = dx -> c <> bc /\ c <> bt /\ c <> br /\ c <> bg) ->
  V293_tcb_old_loads M bt base (V293_prio_row old)
    (2 ^ V293_prio_row old) (2 ^ V293_prio_bit old) ->
  (exists v, get M (dy,0%Z) = Some (true,v)) ->
  (exists v, get M (dby,0%Z) = Some (true,v)) ->
  (exists v, get M (dx,0%Z) = Some (true,v)) ->
  V293_rekey_bitmap_loads M br bg lo hi (V293_ready_group lo hi) ->
  V293_rekey_bitmap_writable M br bg ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> b /\ c <> dy /\ c <> dby /\ c <> dx) ->
  get le pevent = Some (bp,Tptr V293_event_type) ->
  V293_bytes_writable M bp 0%Z 4 ->
  load (Tcom_ptr 411%Z) M (bt,(base+28)%Z) = Some (Vptr (be,Int.repr ebase)) ->
  bc <> br -> bc <> bg -> bt <> br -> bt <> bg ->
  bp <> b -> bp <> dy -> bp <> dby -> bp <> dx -> bp <> br -> bp <> bg ->
  bp <> be ->
  be <> b -> be <> dy -> be <> dby -> be <> dx -> be <> br -> be <> bg ->
  elo < 256 -> ehi < 256 -> (0 <= ebase)%Z -> (ebase+12 <= Int.max_unsigned)%Z ->
  V293_event_bitmap_loads M be ebase elo ehi (V293_ready_group elo ehi) ->
  V293_event_bitmap_writable M be ebase ->
  (forall x v c, In (x,v) (V293_rekey_ready_bindings yo yn xo xn byo byn old new) ->
    get le x = Some (c,Tint8) -> c <> bp /\ c <> be) ->
  bc <> bt -> bc <> bp -> bc <> be -> bt <> bp -> bt <> be ->
  get le xi = Some (bi,Tint8) ->
  (forall c, c = bn \/ c = bi ->
    c <> b /\ c <> dy /\ c <> dby /\ c <> dx /\ c <> br /\ c <> bg /\ c <> bp /\ c <> be /\ c <> bt) ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> bt) ->
  V293_tcb_update_writable M bt base ->
  get le yn = Some (ny,Tint8) -> get le byn = Some (nby,Tint8) ->
  get le xn = Some (nbx,Tint8) ->
  ny <> bi -> ny <> nby -> ny <> nbx -> bi <> nby -> bi <> nbx -> nby <> nbx ->
  (forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->
    c <> b /\ c <> bo /\ c <> bn /\ c <> bc /\ c <> bt /\
    c <> dy /\ c <> dby /\ c <> dx /\ c <> br /\ c <> bg /\ c <> bp /\ c <> be) ->
  (forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->
    exists v, get M (c,0%Z) = Some (true,v)) ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat new)%Z) = Some Vnull ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat old)%Z) = Some (Vptr (bt,Int.repr base)) ->
  bo <> bn -> bc <> bn -> bc <> bo ->
  (initial = 255 ->
    get le current = None /\ get ge current = Some (bcur,Tptr V293_tcb_type) /\
    load (Tptr V293_tcb_type) M (bcur,0%Z) = Some (Vptr (bct,Int.repr curbase)) /\
    (0 <= curbase)%Z /\ (curbase+50 <= Int.max_unsigned)%Z /\
    load Tint8 M (bct,(curbase+50)%Z) = Some (V293_byteval curprio) /\
    (exists v, get M (bo,0%Z) = Some (true,v))) ->
  get le reserved = None -> get ge reserved = Some (rb,Tint8) ->
  (bt,Int.repr base) <> (rb,Int.zero) ->
  V293_bytes_writable M bc 0%Z 4 ->
  (forall c, In c [b;bn;bt;dy;dby;dx;br;bg;bp;be;ny;bi;nby;nbx] ->
    c <> bo /\ c <> bc) ->
  exists Mg,
  let Mh := V293_tcb_update_memory Mg bt base new in
  let fr := V293_ready_branch_rows lo hi old new in
  let er := V293_ready_rekey_rows elo ehi old new in
  cstepstar P (curs (V293_task_prio_entry_update table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent xi
    current reserved cpu_sr exit_id),
    (kenil,ks)) (ge,le,M) (curs (sskip None),(kenil,ks)) (ge,le,Mh) /\
  V293_tcb_updated_loads Mh bt base new /\
  V293_rekey_bitmap_loads Mh br bg (fst fr) (snd fr) (V293_ready_group (fst fr) (snd fr)) /\
  V293_table_loads V293_tcb_type Mh b
    (update_nth_val new (update_nth_val old entries Vnull) (Vptr (bt,Int.repr base))) /\
  load (Tptr V293_tcb_type) Mh (b,(4*Z.of_nat old)%Z) = Some Vnull /\
  load (Tptr V293_tcb_type) Mh (b,(4*Z.of_nat new)%Z) = Some (Vptr (bt,Int.repr base)) /\
  V293_event_bitmap_loads Mh be ebase (fst er) (snd er) (V293_ready_group (fst er) (snd er)) /\
  load (Tptr V293_event_type) Mh (bp,0%Z) = Some (Vptr (be,Int.repr ebase)) /\
  load (Tptr V293_tcb_type) Mh (bc,0%Z) = Some (Vptr (bt,Int.repr base)) /\
  V293_tcb_update_writable Mh bt base /\
  load (Tcom_ptr 411%Z) Mh (bt,(base+28)%Z) = Some (Vptr (be,Int.repr ebase)) /\
  (forall i, (i < base+50)%Z \/ (base+54 < i)%Z -> get Mh (bt,i) = get M (bt,i)) /\
  (forall c i, c <> bo -> c <> bc -> c <> b -> c <> dy -> c <> dby -> c <> dx -> c <> br -> c <> bg -> c <> bp -> c <> be -> c <> bt ->
    c <> ny -> c <> bi -> c <> nby -> c <> nbx ->
    get Mh (c,i) = get M (c,i)).
Proof.
  intros P ks ge le M table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp be ebase elo ehi xi bi ny nby nbx
    current reserved cpu_sr exit_id bcur bct curbase rb curprio
    Input N old O L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg
    Lo Ln Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields
    Wy Wby Wx Loads W NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg PE Eb Ey Eby Ex Er Eg
    EL EH EB ELimit ELoads EW LocalApart CT CP CE TP TE Bi ExtraApart NewTcbApart TW
    NBy NBby NBx NYI NYBY NYBX NIBY NIBX NBYBX CoordApart CoordW
    Empty Slot Onew Cnew CO Self Nreserved Greserved Token CW EntryApart.
  destruct (V293_task_prio_entry_reserved_execution P
    (kseq (V293_task_prio_coordinates_update table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent xi) ks)
    ge le M table oldprio newprio ptcb current reserved cpu_sr exit_id
    b bo bn bc bcur bct curbase initial new curprio (bt,Int.repr base) rb
    Input N O Nt Gt Bo Bn Bc Lo Ln Empty Slot Tbo Tbc Onew Cnew CO Self Nreserved Greserved Token CW)
    as (Ma & Different & Entry & Aold & Anew & Pointer & ASlot & AEmpty & ACW & EntryFrame).
  assert (CF : forall c i, In c [b;bn;bt;dy;dby;dx;br;bg;bp;be;ny;bi;nby;nbx] ->
    get Ma (c,i) = get M (c,i)).
  { intros c i I. destruct (EntryApart c I) as [A B]. apply EntryFrame; assumption. }
  assert (LF : forall tp c i, In c [b;bn;bt;dy;dby;dx;br;bg;bp;be;ny;bi;nby;nbx] ->
    load tp Ma (c,i) = load tp M (c,i)).
  { intros tp c i I. apply V293_load_block_frame. intro j. apply CF; exact I. }
  assert (Resources :
    V293_bytes_writable Ma b (4*Z.of_nat old)%Z 4 /\
    V293_bytes_writable Ma b (4*Z.of_nat new)%Z 4 /\
    V293_table_loads V293_tcb_type Ma b entries /\
    V293_tcb_old_loads Ma bt base (V293_prio_row old) (2 ^ V293_prio_row old) (2 ^ V293_prio_bit old) /\
    (exists v, get Ma (dy,0%Z) = Some (true,v)) /\
    (exists v, get Ma (dby,0%Z) = Some (true,v)) /\
    (exists v, get Ma (dx,0%Z) = Some (true,v)) /\
    V293_rekey_bitmap_loads Ma br bg lo hi (V293_ready_group lo hi) /\
    V293_rekey_bitmap_writable Ma br bg /\
    V293_bytes_writable Ma bp 0%Z 4 /\
    load (Tcom_ptr 411%Z) Ma (bt,(base+28)%Z) = Some (Vptr (be,Int.repr ebase)) /\
    V293_event_bitmap_loads Ma be ebase elo ehi (V293_ready_group elo ehi) /\
    V293_event_bitmap_writable Ma be ebase /\
    V293_tcb_update_writable Ma bt base /\
    (forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->
      exists v, get Ma (c,0%Z) = Some (true,v))).
  { unfold V293_bytes_writable,V293_table_loads,V293_tcb_old_loads,
      V293_rekey_bitmap_loads,V293_rekey_bitmap_writable,
      V293_event_bitmap_loads,V293_event_bitmap_writable,V293_tcb_update_writable in *.
    repeat rewrite LF by (simpl; auto 20).
    repeat rewrite CF by (simpl; auto 20).
    repeat split; try tauto.
    - intros k K. rewrite CF by (simpl; auto 20). apply Wo; exact K.
    - intros k K. rewrite CF by (simpl; auto 20). apply Wn; exact K.
    - intros p R. rewrite LF by (simpl; auto 20). apply View; exact R.
    - intros k K. rewrite CF by (simpl; auto 20). apply We; exact K.
    - intros d D. rewrite CF by (simpl; auto 20). apply TW; exact D.
    - intros c I. destruct I as [-> | [-> | [-> | ->]]]; rewrite CF by (simpl; auto 20); apply CoordW; auto. }
  destruct Resources as (AWo & AWn & AView & AFields & AWy & AWby & AWx & ALoads & AW & AWe & AEvent & AELoads & AEW & ATW & ACoordW).
  destruct (V293_task_prio_coordinates_update_execution P ks ge le Ma table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi old new entries pevent bp be ebase elo ehi xi bi ny nby nbx
    O ltac:(clear -N; lia) Different L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg
    Aold Anew Pointer AWo AWn Len AView By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart AFields
    AWy AWby AWx ALoads AW NewApart Be AWe AEvent Cr Cg Br Bg Pb Py Pby Px Pr Pg PE Eb Ey Eby Ex Er Eg
    EL EH EB ELimit AELoads AEW LocalApart CT CP CE TP TE Bi ExtraApart NewTcbApart ATW
    NBy NBby NBx NYI NYBY NYBX NIBY NIBX NBYBX CoordApart ACoordW)
    as (Mg & Exec & Updated & Ready & Table & OldSlot & NewSlot & EventOut & Read & OutPointer & Writable & Internal & Untouched & Frame).
  exists Mg. cbn zeta in *. split.
  - unfold V293_task_prio_entry_update.
    eapply c_stepstarn. { eapply stmt_step; [reflexivity|constructor]. }
    eapply V293_cstepstar_trans; [exact Entry | ].
    eapply c_stepstarn. { eapply stmt_step; [reflexivity|constructor]. }
    exact Exec.
  - split; [exact Updated | ]. split; [exact Ready | ]. split; [exact Table | ].
    split; [exact OldSlot | ]. split; [exact NewSlot | ]. split; [exact EventOut | ].
    split; [exact Read | ]. split; [exact OutPointer | ]. split; [exact Writable | ].
    split; [exact Internal | ]. split.
    + intros i I. rewrite Untouched by exact I. apply CF; simpl; auto 20.
    + intros c i OB PC A B C D E F G H' J NY NI NBY NBX.
      rewrite Frame by assumption. apply EntryFrame; assumption.
Qed.

(* Original physical entry: NULL pointer, stale coordinates, one selector byte. *)
Definition V293_entry_update_fixture_ge : env :=
  set (set V293_prefix_fixture_ge 750%Z (80%positive,Tptr V293_tcb_type))
    900%Z (99%positive,Tint8).
Definition V293_entry_update_fixture_mem (self live : bool) elo ehi : mem :=
  V293_put_byte
    (V293_fixture_put_bytes
      (V293_fixture_put_bytes (V293_coordinate_fixture_mem live elo ehi)
        40%positive 0%Z (encode_val (Tptr V293_tcb_type) Vnull))
      80%positive 0%Z (encode_val (Tptr V293_tcb_type) (Vptr (41%positive,Int.repr 8))))
    (51%positive,0%Z) (if self then 255 else 8).

Lemma V293_entry_update_fixture_frame : forall self live elo ehi c i,
  c <> 51%positive -> c <> 40%positive -> c <> 80%positive ->
  get (V293_entry_update_fixture_mem self live elo ehi) (c,i) =
    get (V293_coordinate_fixture_mem live elo ehi) (c,i).
Proof.
  intros self live elo ehi c i A B C. unfold V293_entry_update_fixture_mem.
  rewrite V293_put_byte_other by (intro E; inversion E; congruence).
  repeat rewrite V293_fixture_bytes_outside by (left; assumption). reflexivity.
Qed.

Lemma V293_entry_update_fixture_selector_only : forall live elo ehi a,
  a <> (51%positive,0%Z) ->
  get (V293_entry_update_fixture_mem true live elo ehi) a =
    get (V293_entry_update_fixture_mem false live elo ehi) a.
Proof.
  intros. unfold V293_entry_update_fixture_mem.
  repeat rewrite V293_put_byte_other by assumption. reflexivity.
Qed.

Local Ltac entry_update_bind :=
  unfold V293_entry_update_fixture_ge,V293_tcb_update_fixture_le,
    V293_event_fixture_le,V293_prefix_fixture_ge,V293_prefix_fixture_le,
    V293_read_ready_fixture_le,V293_ready_fragment_fixture_le;
  repeat first [rewrite map_get_set | rewrite map_get_set' by discriminate]; reflexivity.
Local Ltac entry_update_get :=
  unfold V293_tcb_update_fixture_mem;
  repeat first [rewrite V293_put_byte_other by discriminate | rewrite V293_put_byte_get_same].
Local Ltac entry_update_load :=
  unfold V293_tcb_update_fixture_mem;
  repeat rewrite V293_put_byte_other_load by discriminate;
  apply V293_put_byte_load; lia.

Theorem V293_task_prio_entry_update_witness : forall self live elo ehi,
  elo < 256 -> ehi < 256 -> forall P ks,
  exists Mh,
  load (Tptr V293_tcb_type) (V293_entry_update_fixture_mem self live elo ehi)
    (40%positive,0%Z) = Some Vnull /\
  (forall c, In c [33%positive;73%positive;37%positive;35%positive] ->
    load Tint8 (V293_entry_update_fixture_mem self live elo ehi) (c,0%Z) = Some (V293_byteval 255)) /\
  cstepstar P (curs (V293_task_prio_entry_update
    500%Z 501%Z 502%Z 400%Z 300%Z 301%Z 302%Z 303%Z 304%Z 305%Z 306%Z 307%Z 600%Z 601%Z
    750%Z 900%Z 751%Z 752%Z),(kenil,ks))
    (V293_entry_update_fixture_ge,V293_tcb_update_fixture_le,V293_entry_update_fixture_mem self live elo ehi)
    (curs (sskip None),(kenil,ks)) (V293_entry_update_fixture_ge,V293_tcb_update_fixture_le,Mh) /\
  V293_tcb_updated_loads Mh 41%positive 8%Z 6 /\
  V293_rekey_bitmap_loads Mh 30%positive 31%positive (if live then 80 else 16) 0 1 /\
  V293_event_bitmap_loads Mh 72%positive 5%Z
    (fst (V293_ready_rekey_rows elo ehi 8 6)) (snd (V293_ready_rekey_rows elo ehi 8 6))
    (V293_ready_group (fst (V293_ready_rekey_rows elo ehi 8 6)) (snd (V293_ready_rekey_rows elo ehi 8 6))) /\
  V293_table_loads V293_tcb_type Mh 50%positive
    (update_nth_val 6 (update_nth_val 8 V293_prefix_fixture_entries Vnull) (Vptr (41%positive,Int.repr 8))) /\
  load (Tptr V293_tcb_type) Mh (50%positive,32%Z) = Some Vnull /\
  load (Tptr V293_tcb_type) Mh (50%positive,24%Z) = Some (Vptr (41%positive,Int.repr 8)) /\
  load (Tcom_ptr 411%Z) Mh (41%positive,36%Z) = Some (Vptr (72%positive,Int.repr 5)).
Proof.
  intros self live elo ehi EL EH P ks.
  destruct (V293_prefix_event_nonnull_entry live elo ehi EL EH)
    as (Lp & Event & We & Fields & View & Wo & Wn & Wy & Wby & Wx & Loads & W & NewLoc & Lo & Ln & Initial & ELoads & EW).
  set (M := V293_entry_update_fixture_mem self live elo ehi).
  assert (CF : forall c i, c<>51%positive -> c<>40%positive -> c<>80%positive ->
    get M (c,i) = get (V293_coordinate_fixture_mem live elo ehi) (c,i)).
  { intros. apply V293_entry_update_fixture_frame; assumption. }
  assert (LF : forall tp c i, c<>51%positive -> c<>40%positive -> c<>80%positive ->
    load tp M (c,i) = load tp (V293_coordinate_fixture_mem live elo ehi) (c,i)).
  { intros. apply V293_load_block_frame. intro j. apply CF; assumption. }
  assert (RF : forall tp c i, c <> 41%positive -> c <> 73%positive -> c <> 33%positive -> c <> 37%positive -> c <> 35%positive ->
    c<>51%positive -> c<>40%positive -> c<>80%positive ->
    load tp M (c,i) = load tp (V293_prefix_event_nonnull_mem live elo ehi) (c,i)).
  { intros. rewrite LF by assumption. apply V293_load_block_frame. intro j.
    rewrite V293_coordinate_fixture_delta by (intro E; inversion E; congruence).
    apply V293_tcb_update_fixture_outside; [assumption | left; assumption]. }
  assert (HEvent : load (Tcom_ptr 411%Z) M (41%positive,36%Z) = Some (Vptr (72%positive,Int.repr 5))).
  { unfold load,loadm. rewrite (V293_loadbytes_ext _ (V293_prefix_event_nonnull_mem live elo ehi) M).
    - exact Event.
    - intros k K. cbn [typelen] in K.
      unfold M. rewrite V293_entry_update_fixture_frame by discriminate. rewrite V293_coordinate_fixture_delta by (intro Eq; inversion Eq; discriminate).
      apply V293_tcb_update_fixture_outside; [discriminate | right; left; lia]. }
  assert (HFields : V293_tcb_old_loads M 41%positive 8%Z 1 2 1).
  { unfold V293_tcb_old_loads; repeat rewrite LF by discriminate; unfold V293_coordinate_fixture_mem; repeat rewrite V293_put_byte_other_load by discriminate; repeat split; entry_update_load. }
  assert (HView : V293_table_loads V293_tcb_type M 50%positive V293_prefix_fixture_entries).
  { intros p R. rewrite RF by discriminate. exact (View p R). }
  assert (HWo : V293_bytes_writable M 50%positive 32%Z 4).
  { intros k K. unfold M; repeat rewrite V293_entry_update_fixture_frame by discriminate; repeat rewrite V293_coordinate_fixture_delta by (intro Eq; inversion Eq; discriminate); rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact (Wo k K). }
  assert (HWn : V293_bytes_writable M 50%positive 24%Z 4).
  { intros k K. unfold M; repeat rewrite V293_entry_update_fixture_frame by discriminate; repeat rewrite V293_coordinate_fixture_delta by (intro Eq; inversion Eq; discriminate); rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact (Wn k K). }
  assert (HWe : V293_bytes_writable M 70%positive 0%Z 4).
  { intros k K. unfold M; repeat rewrite V293_entry_update_fixture_frame by discriminate; repeat rewrite V293_coordinate_fixture_delta by (intro Eq; inversion Eq; discriminate); rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact (We k K). }
  assert (HWy : exists v, get M (32%positive,0%Z) = Some (true,v)).
  { unfold M; repeat rewrite V293_entry_update_fixture_frame by discriminate; repeat rewrite V293_coordinate_fixture_delta by (intro Eq; inversion Eq; discriminate); rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact Wy. }
  assert (HWby : exists v, get M (36%positive,0%Z) = Some (true,v)).
  { unfold M; repeat rewrite V293_entry_update_fixture_frame by discriminate; repeat rewrite V293_coordinate_fixture_delta by (intro Eq; inversion Eq; discriminate); rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact Wby. }
  assert (HWx : exists v, get M (34%positive,0%Z) = Some (true,v)).
  { unfold M; repeat rewrite V293_entry_update_fixture_frame by discriminate; repeat rewrite V293_coordinate_fixture_delta by (intro Eq; inversion Eq; discriminate); rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact Wx. }
  assert (HLoads : V293_rekey_bitmap_loads M 30%positive 31%positive 16 (if live then 1 else 0)
    (V293_ready_group 16 (if live then 1 else 0))).
  { unfold V293_rekey_bitmap_loads in *. repeat rewrite RF by discriminate. exact Loads. }
  assert (HW : V293_rekey_bitmap_writable M 30%positive 31%positive).
  { unfold V293_rekey_bitmap_writable in *.
    unfold M; repeat rewrite V293_entry_update_fixture_frame by discriminate; repeat rewrite V293_coordinate_fixture_delta by (intro Eq; inversion Eq; discriminate); repeat rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact W. }
  assert (HELoads : V293_event_bitmap_loads M 72%positive 5%Z elo ehi (V293_ready_group elo ehi)).
  { unfold V293_event_bitmap_loads in *. repeat rewrite RF by discriminate. exact ELoads. }
  assert (HEW : V293_event_bitmap_writable M 72%positive 5%Z).
  { unfold V293_event_bitmap_writable in *.
    unfold M; repeat rewrite V293_entry_update_fixture_frame by discriminate; repeat rewrite V293_coordinate_fixture_delta by (intro Eq; inversion Eq; discriminate); repeat rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact EW. }
  assert (HLn : load Tint8 M (52%positive,0%Z) = Some (V293_byteval 6)).
  { rewrite RF by discriminate. exact Ln. }
  assert (HTW : V293_tcb_update_writable M 41%positive 8%Z).
  { intros d D. assert (d=50 \/ d=51 \/ d=52 \/ d=53 \/ d=54)%Z by lia.
    destruct H as [-> | [-> | [-> | [-> | ->]]]]; unfold M; repeat rewrite V293_entry_update_fixture_frame by discriminate; repeat rewrite V293_coordinate_fixture_delta by (intro Eq; inversion Eq; discriminate);
      eexists; entry_update_get; reflexivity. }
  assert (HLo : load Tint8 M (51%positive,0%Z) = Some (V293_byteval (if self then 255 else 8))).
  { unfold M,V293_entry_update_fixture_mem. apply V293_put_byte_load. destruct self; lia. }
  assert (SelectorW : exists v, get M (51%positive,0%Z) = Some (true,v)).
  { unfold M,V293_entry_update_fixture_mem. eexists. apply V293_put_byte_get_same. }
  assert (OuterLF : forall tp c i, c<>51%positive ->
    load tp M (c,i) = load tp
      (V293_fixture_put_bytes
        (V293_fixture_put_bytes (V293_coordinate_fixture_mem live elo ehi) 40%positive 0%Z
          (encode_val (Tptr V293_tcb_type) Vnull))
        80%positive 0%Z (encode_val (Tptr V293_tcb_type) (Vptr (41%positive,Int.repr 8)))) (c,i)).
  { intros tp c i A. apply V293_load_block_frame. intro j.
    unfold M,V293_entry_update_fixture_mem.
    apply V293_put_byte_other. intro E; inversion E; congruence. }
  assert (Current : load (Tptr V293_tcb_type) M (80%positive,0%Z) = Some (Vptr (41%positive,Int.repr 8))).
  { rewrite OuterLF by discriminate. apply V293_fixture_pointer_load. reflexivity. }
  assert (Null : load (Tptr V293_tcb_type) M (40%positive,0%Z) = Some Vnull).
  { rewrite OuterLF by discriminate. unfold load,loadm. rewrite V293_loadbytes_ext with
      (M:=V293_fixture_put_bytes (V293_coordinate_fixture_mem live elo ehi) 40%positive 0%Z
        (encode_val (Tptr V293_tcb_type) Vnull)).
    - apply V293_fixture_pointer_load. reflexivity.
    - intros k K. apply V293_fixture_bytes_outside. left; discriminate. }
  assert (CW : V293_bytes_writable M 40%positive 0%Z 4).
  { intros k K. unfold M,V293_entry_update_fixture_mem.
    rewrite V293_put_byte_other by discriminate.
    rewrite V293_fixture_bytes_outside by (left; discriminate).
    eexists. apply V293_fixture_bytes_nth. rewrite encode_val_length; exact K. }
  assert (Prio : load Tint8 M (41%positive,58%Z) = Some (V293_byteval 8)).
  { rewrite LF by discriminate. unfold V293_coordinate_fixture_mem.
    repeat rewrite V293_put_byte_other_load by discriminate. entry_update_load. }
  assert (Resolved : (if (if self then 255 else 8) =? 255 then 8 else (if self then 255 else 8)) = 8)
    by (destruct self; reflexivity).
  destruct (V293_task_prio_entry_update_execution P ks V293_entry_update_fixture_ge V293_tcb_update_fixture_le
    M 500%Z 501%Z 502%Z 400%Z 300%Z 301%Z 302%Z 303%Z 304%Z 305%Z 306%Z 307%Z
    50%positive 51%positive 52%positive 40%positive 41%positive 32%positive 36%positive 34%positive
    8%Z 30%positive 31%positive 16 (if live then 1 else 0) (if self then 255 else 8) 6 V293_prefix_fixture_entries
    600%Z 70%positive 72%positive 5%Z elo ehi 601%Z 73%positive 33%positive 37%positive 35%positive
    750%Z 900%Z 751%Z 752%Z 80%positive 41%positive 8%Z 99%positive 8)
    as (Mg & Exec & Updated & FinalLoads & FinalView & OldSlot & NewSlot & FinalEvent & Read & Pointer & TW & InternalEvent & Untouched & Frame).
  all: try rewrite Resolved; try assumption; try discriminate; try (entry_update_bind; reflexivity);
    try (change (0 <= 8)%Z; lia); try (change (8+55 <= 4294967295)%Z; lia);
    try (change (0 <= 5)%Z; lia); try (change (5+12 <= 4294967295)%Z; lia);
    try (change (8<13); lia); try (change (6<12); lia); try (change (16<256); lia);
    try (destruct live; lia); try (destruct self; cbn; lia);
    try (change (length V293_prefix_fixture_entries = 13); reflexivity).
  - intros x v c I Bind. cbn [V293_rekey_new_bindings In] in I.
    destruct I as [E|[E|[E|F]]]; try contradiction; inversion E; subst x v;
      unfold V293_tcb_update_fixture_le,V293_event_fixture_le,V293_prefix_fixture_le,V293_read_ready_fixture_le,V293_ready_fragment_fixture_le in Bind;
      repeat first [rewrite map_get_set in Bind | rewrite map_get_set' in Bind by discriminate];
      inversion Bind; subst c; repeat split; discriminate.
  - intros x v c I Bind. cbn [V293_rekey_ready_bindings In] in I.
    destruct I as [E|[E|[E|[E|[E|[E|F]]]]]]; try contradiction; inversion E; subst x v;
      unfold V293_tcb_update_fixture_le,V293_event_fixture_le,V293_prefix_fixture_le,V293_read_ready_fixture_le,V293_ready_fragment_fixture_le in Bind;
      repeat first [rewrite map_get_set in Bind | rewrite map_get_set' in Bind by discriminate];
      inversion Bind; subst c; split; discriminate.
  - intros x v c I Bind. cbn [V293_rekey_new_bindings In] in I.
    destruct I as [E|[E|[E|F]]]; try contradiction; inversion E; subst x v;
      unfold V293_tcb_update_fixture_le,V293_event_fixture_le,V293_prefix_fixture_le,V293_read_ready_fixture_le,V293_ready_fragment_fixture_le in Bind;
      repeat first [rewrite map_get_set in Bind | rewrite map_get_set' in Bind by discriminate];
      inversion Bind; subst c; discriminate.
  - intros c Cases. destruct Cases as [-> | [-> | [-> | ->]]];
      rewrite CF by discriminate; unfold V293_coordinate_fixture_mem;
      repeat rewrite V293_put_byte_other by discriminate;
      eexists; apply V293_put_byte_get_same.
  - change (load (Tptr V293_tcb_type) M (50%positive,24%Z) = Some (nth 6 V293_prefix_fixture_entries Vnull)).
    exact (HView 6 ltac:(clear; lia)).
  - change (load (Tptr V293_tcb_type) M (50%positive,32%Z) = Some (nth 8 V293_prefix_fixture_entries Vnull)).
    exact (HView 8 ltac:(clear; lia)).
  - intro IsSelf. repeat split; try (entry_update_bind; reflexivity); try assumption;
      try (change (0<=8)%Z; lia); try (change (8+50<=4294967295)%Z; lia).
  - exists (V293_tcb_update_memory Mg 41%positive 8%Z 6). rewrite Resolved in *.
    split; [exact Null | ]. split.
    + intros c I. rewrite LF by (clear - I; cbn in I; intuition congruence).
      apply V293_coordinate_fixture_stale. clear - I; cbn in I; intuition congruence.
    + split; [exact Exec | ]. split; [exact Updated | ].
      split; [destruct live; exact FinalLoads | ]. split; [exact FinalEvent | ].
      split; [exact FinalView | ]. split; [exact OldSlot | ]. split; [exact NewSlot | ]. exact InternalEvent.
Qed.

(* The same configured program, now taking its actual NULL-event branch. *)
Theorem V293_task_prio_coordinates_null_update_execution :
  forall P ks ge le M table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi old new entries pevent bp xi bi ny nby nbx,
  old < 13 -> new < 13 -> old <> new -> lo < 256 -> hi < 256 -> br <> bg ->
  (0 <= base)%Z -> (base+55 <= Int.max_unsigned)%Z ->
  get le table = None -> get ge table = Some (b,Tarray (Tptr V293_tcb_type) 13) ->
  get le oldprio = Some (bo,Tint8) -> get le newprio = Some (bn,Tint8) ->
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  b <> bo -> b <> bn -> b <> bc -> b <> bt ->
  b <> dy -> b <> dby -> b <> dx -> b <> br -> b <> bg ->
  load Tint8 M (bo,0%Z) = Some (V293_byteval old) ->
  load Tint8 M (bn,0%Z) = Some (V293_byteval new) ->
  load (Tptr V293_tcb_type) M (bc,0%Z) = Some (Vptr (bt,Int.repr base)) ->
  V293_bytes_writable M b (4*Z.of_nat old)%Z 4 ->
  V293_bytes_writable M b (4*Z.of_nat new)%Z 4 ->
  length entries = 13 -> V293_table_loads V293_tcb_type M b entries ->
  get le yo = Some (dy,Tint8) -> get le byo = Some (dby,Tint8) -> get le xo = Some (dx,Tint8) ->
  get le rows = None -> get ge rows = Some (br,Tarray Tint8 2) ->
  get le group = None -> get ge group = Some (bg,Tint8) ->
  dy <> dby -> dy <> dx -> dby <> dx ->
  (forall c, c = dy \/ c = dby \/ c = dx -> c <> bc /\ c <> bt /\ c <> br /\ c <> bg) ->
  V293_tcb_old_loads M bt base (V293_prio_row old)
    (2 ^ V293_prio_row old) (2 ^ V293_prio_bit old) ->
  (exists v, get M (dy,0%Z) = Some (true,v)) ->
  (exists v, get M (dby,0%Z) = Some (true,v)) ->
  (exists v, get M (dx,0%Z) = Some (true,v)) ->
  V293_rekey_bitmap_loads M br bg lo hi (V293_ready_group lo hi) ->
  V293_rekey_bitmap_writable M br bg ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> b /\ c <> dy /\ c <> dby /\ c <> dx) ->
  get le pevent = Some (bp,Tptr V293_event_type) ->
  V293_bytes_writable M bp 0%Z 4 ->
  load (Tcom_ptr 411%Z) M (bt,(base+28)%Z) = Some Vnull ->
  bc <> br -> bc <> bg -> bt <> br -> bt <> bg ->
  bp <> b -> bp <> dy -> bp <> dby -> bp <> dx -> bp <> br -> bp <> bg ->
  bc <> bt -> bc <> bp -> bt <> bp ->
  get le xi = Some (bi,Tint8) ->
  (forall c, c = bn \/ c = bi ->
    c <> b /\ c <> dy /\ c <> dby /\ c <> dx /\ c <> br /\ c <> bg /\ c <> bp /\ c <> bt) ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> bp /\ c <> bt) ->
  V293_tcb_update_writable M bt base ->
  get le yn = Some (ny,Tint8) -> get le byn = Some (nby,Tint8) ->
  get le xn = Some (nbx,Tint8) ->
  ny <> bi -> ny <> nby -> ny <> nbx -> bi <> nby -> bi <> nbx -> nby <> nbx ->
  (forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->
    c <> b /\ c <> bo /\ c <> bn /\ c <> bc /\ c <> bt /\
    c <> dy /\ c <> dby /\ c <> dx /\ c <> br /\ c <> bg /\ c <> bp) ->
  (forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->
    exists v, get M (c,0%Z) = Some (true,v)) ->
  exists Mg,
  let Mh := V293_tcb_update_memory Mg bt base new in
  let fr := V293_ready_branch_rows lo hi old new in
  cstepstar P (curs (V293_task_prio_coordinates_update table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent xi),
    (kenil,ks)) (ge,le,M) (curs (sskip None),(kenil,ks)) (ge,le,Mh) /\
  V293_tcb_updated_loads Mh bt base new /\
  V293_rekey_bitmap_loads Mh br bg (fst fr) (snd fr) (V293_ready_group (fst fr) (snd fr)) /\
  V293_table_loads V293_tcb_type Mh b
    (update_nth_val new (update_nth_val old entries Vnull) (Vptr (bt,Int.repr base))) /\
  load (Tptr V293_tcb_type) Mh (b,(4*Z.of_nat old)%Z) = Some Vnull /\
  load (Tptr V293_tcb_type) Mh (b,(4*Z.of_nat new)%Z) = Some (Vptr (bt,Int.repr base)) /\
  load (Tptr V293_event_type) Mh (bp,0%Z) = Some Vnull /\
  load (Tptr V293_tcb_type) Mh (bc,0%Z) = Some (Vptr (bt,Int.repr base)) /\
  load (Tcom_ptr 411%Z) Mh (bt,(base+28)%Z) = Some Vnull /\
  (forall i, (i < base+50)%Z \/ (base+54 < i)%Z -> get Mh (bt,i) = get M (bt,i)) /\
  (forall c i, c <> b -> c <> dy -> c <> dby -> c <> dx -> c <> br -> c <> bg -> c <> bp -> c <> bt ->
    c <> ny -> c <> bi -> c <> nby -> c <> nbx ->
    get Mh (c,i) = get M (c,i)).
Proof.
  intros P ks ge le M table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi old new entries pevent bp xi bi ny nby nbx
    O N ON L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg
    Lo Ln Lp Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields
    Wy Wby Wx Loads W NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg
    CT CP TP Bi ExtraApart NewTcbApart TW
    NBy NBby NBx NYI NYBY NYBX NIBY NIBX NBYBX CoordApart CoordW.
  assert (SourceApart : forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx -> c <> bn).
  { intros c I. destruct (CoordApart c I) as (_ & _ & A & _). exact A. }
  destruct (V293_task_prio_coordinates_execution P ks ge le M newprio yn xi byn xn bn ny bi nby nbx new
    N Bn NBy Bi NBby NBx Ln SourceApart NYI NYBY NYBX NIBY NIBX NBYBX CoordW)
    as (Coordinates & NewY & NewI & NewBY & NewBX & NewSource & CoordFrame).
  set (Mc := V293_coordinate_memory M ny bi nby nbx new) in *.
  assert (Safe : forall c, In c [b;bo;bn;bc;bt;dy;dby;dx;br;bg;bp] ->
    c <> ny /\ c <> bi /\ c <> nby /\ c <> nbx).
  { intros c I.
    pose proof (CoordApart ny ltac:(auto)) as A.
    pose proof (CoordApart bi ltac:(auto)) as B.
    pose proof (CoordApart nby ltac:(auto)) as C.
    pose proof (CoordApart nbx ltac:(auto)) as D.
    cbn in I. intuition congruence. }
  assert (CF : forall c i, In c [b;bo;bn;bc;bt;dy;dby;dx;br;bg;bp] ->
    get Mc (c,i) = get M (c,i)).
  { intros c i I. destruct (Safe c I) as (A & B & C & D).
    apply CoordFrame; congruence. }
  assert (LF : forall tp c i, In c [b;bo;bn;bc;bt;dy;dby;dx;br;bg;bp] ->
    load tp Mc (c,i) = load tp M (c,i)).
  { intros tp c i I. apply V293_load_block_frame. intro j. apply CF. exact I. }
  assert (NewLoc : V293_rekey_locals ge le Mc br bg (V293_rekey_new_bindings yn xn byn new)).
  { destruct (V293_prio_coordinates new N) as [Y X].
    destruct (V293_mask_byte_value (V293_prio_row new) ltac:(lia)) as [_ MY].
    destruct (V293_mask_byte_value (V293_prio_bit new) X) as [_ MX].
    intros x v I. cbn [V293_rekey_new_bindings In] in I.
    destruct I as [E|[E|[E|F]]]; try contradiction; inversion E; subst x v.
    - exists ny. destruct (CoordApart ny ltac:(auto)) as (_ & _ & _ & _ & _ & _ & _ & _ & A & B & _).
      repeat split; assumption.
    - exists nbx. destruct (CoordApart nbx ltac:(auto)) as (_ & _ & _ & _ & _ & _ & _ & _ & A & B & _).
      repeat split; try assumption. rewrite <- MX. exact NewBX.
    - exists nby. destruct (CoordApart nby ltac:(auto)) as (_ & _ & _ & _ & _ & _ & _ & _ & A & B & _).
      repeat split; try assumption. rewrite <- MY. exact NewBY. }
  assert (Resources :
    load Tint8 Mc (bo,0%Z) = Some (V293_byteval old) /\
    load (Tptr V293_tcb_type) Mc (bc,0%Z) = Some (Vptr (bt,Int.repr base)) /\
    V293_bytes_writable Mc b (4*Z.of_nat old)%Z 4 /\
    V293_bytes_writable Mc b (4*Z.of_nat new)%Z 4 /\
    V293_table_loads V293_tcb_type Mc b entries /\
    V293_tcb_old_loads Mc bt base (V293_prio_row old) (2 ^ V293_prio_row old) (2 ^ V293_prio_bit old) /\
    (exists v, get Mc (dy,0%Z) = Some (true,v)) /\
    (exists v, get Mc (dby,0%Z) = Some (true,v)) /\
    (exists v, get Mc (dx,0%Z) = Some (true,v)) /\
    V293_rekey_bitmap_loads Mc br bg lo hi (V293_ready_group lo hi) /\
    V293_rekey_bitmap_writable Mc br bg /\
    V293_bytes_writable Mc bp 0%Z 4 /\
    load (Tcom_ptr 411%Z) Mc (bt,(base+28)%Z) = Some Vnull /\
    V293_tcb_update_writable Mc bt base).
  { unfold V293_bytes_writable,V293_table_loads,V293_tcb_old_loads,
      V293_rekey_bitmap_loads,V293_rekey_bitmap_writable,
      V293_tcb_update_writable in *.
    repeat rewrite LF by (simpl; tauto).
    repeat rewrite CF by (simpl; tauto).
    repeat split; try tauto.
    - intros k K. rewrite CF by (simpl; tauto). apply Wo. exact K.
    - intros k K. rewrite CF by (simpl; tauto). apply Wn. exact K.
    - intros p R. rewrite LF by (simpl; tauto). apply View. exact R.
    - intros k K. rewrite CF by (simpl; tauto). apply We. exact K.
    - intros d D. rewrite CF by (simpl; tauto). apply TW. exact D. }
  destruct Resources as (Clo & Clp & Cwo & Cwn & Cview & Cfields & Cwy & Cwby & Cwx & Cloads & Cw & Cwe & Cevent & Ctw).
  destruct (V293_task_prio_prefix_null_update_execution P ks ge le Mc table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi old new entries pevent bp xi bi
    O N ON L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg
    Clo NewSource Clp Cwo Cwn Len Cview By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Cfields
    Cwy Cwby Cwx Cloads Cw NewLoc NewApart Be Cwe Cevent Cr Cg Br Bg Pb Py Pby Px Pr Pg
    CT CP TP Bi NewI ExtraApart NewTcbApart Ctw)
    as (Mg & Exec & Updated & Ready & Table & OldSlot & NewSlot & Read & Pointer & Internal & Untouched & Frame).
  exists Mg. cbn zeta in *. split.
  - unfold V293_task_prio_coordinates_update.
    eapply V293_rekey_sequence_execution; [ | exact Exec].
    intro tail. destruct (V293_task_prio_coordinates_execution P tail ge le M newprio yn xi byn xn bn ny bi nby nbx new
      N Bn NBy Bi NBby NBx Ln SourceApart NYI NYBY NYBX NIBY NIBX NBYBX CoordW) as [E _]. exact E.
  - split; [exact Updated | ]. split; [exact Ready | ]. split; [exact Table | ].
    split; [exact OldSlot | ]. split; [exact NewSlot | ].
    split; [exact Read | ]. split; [exact Pointer | ].
    split; [exact Internal | ]. split.
    + intros i I. rewrite Untouched by exact I. apply CF. simpl; tauto.
    + intros c i A B C D E F G J NY NI NBY NBX.
      rewrite Frame by assumption. apply CoordFrame; congruence.
Qed.

Theorem V293_task_prio_entry_null_update_execution :
  forall P ks ge le M table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp xi bi ny nby nbx
    current reserved (cpu_sr : var) (exit_id : fid) bcur bct curbase rb curprio,
  initial < 256 -> new < 12 ->
  let old := if initial =? 255 then curprio else initial in
  old < 13 -> lo < 256 -> hi < 256 -> br <> bg ->
  (0 <= base)%Z -> (base+55 <= Int.max_unsigned)%Z ->
  get le table = None -> get ge table = Some (b,Tarray (Tptr V293_tcb_type) 13) ->
  get le oldprio = Some (bo,Tint8) -> get le newprio = Some (bn,Tint8) ->
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  b <> bo -> b <> bn -> b <> bc -> b <> bt ->
  b <> dy -> b <> dby -> b <> dx -> b <> br -> b <> bg ->
  load Tint8 M (bo,0%Z) = Some (V293_byteval initial) ->
  load Tint8 M (bn,0%Z) = Some (V293_byteval new) ->
  V293_bytes_writable M b (4*Z.of_nat old)%Z 4 ->
  V293_bytes_writable M b (4*Z.of_nat new)%Z 4 ->
  length entries = 13 -> V293_table_loads V293_tcb_type M b entries ->
  get le yo = Some (dy,Tint8) -> get le byo = Some (dby,Tint8) -> get le xo = Some (dx,Tint8) ->
  get le rows = None -> get ge rows = Some (br,Tarray Tint8 2) ->
  get le group = None -> get ge group = Some (bg,Tint8) ->
  dy <> dby -> dy <> dx -> dby <> dx ->
  (forall c, c = dy \/ c = dby \/ c = dx -> c <> bc /\ c <> bt /\ c <> br /\ c <> bg) ->
  V293_tcb_old_loads M bt base (V293_prio_row old)
    (2 ^ V293_prio_row old) (2 ^ V293_prio_bit old) ->
  (exists v, get M (dy,0%Z) = Some (true,v)) ->
  (exists v, get M (dby,0%Z) = Some (true,v)) ->
  (exists v, get M (dx,0%Z) = Some (true,v)) ->
  V293_rekey_bitmap_loads M br bg lo hi (V293_ready_group lo hi) ->
  V293_rekey_bitmap_writable M br bg ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> b /\ c <> dy /\ c <> dby /\ c <> dx) ->
  get le pevent = Some (bp,Tptr V293_event_type) ->
  V293_bytes_writable M bp 0%Z 4 ->
  load (Tcom_ptr 411%Z) M (bt,(base+28)%Z) = Some Vnull ->
  bc <> br -> bc <> bg -> bt <> br -> bt <> bg ->
  bp <> b -> bp <> dy -> bp <> dby -> bp <> dx -> bp <> br -> bp <> bg ->
  bc <> bt -> bc <> bp -> bt <> bp ->
  get le xi = Some (bi,Tint8) ->
  (forall c, c = bn \/ c = bi ->
    c <> b /\ c <> dy /\ c <> dby /\ c <> dx /\ c <> br /\ c <> bg /\ c <> bp /\ c <> bt) ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> bp /\ c <> bt) ->
  V293_tcb_update_writable M bt base ->
  get le yn = Some (ny,Tint8) -> get le byn = Some (nby,Tint8) ->
  get le xn = Some (nbx,Tint8) ->
  ny <> bi -> ny <> nby -> ny <> nbx -> bi <> nby -> bi <> nbx -> nby <> nbx ->
  (forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->
    c <> b /\ c <> bo /\ c <> bn /\ c <> bc /\ c <> bt /\
    c <> dy /\ c <> dby /\ c <> dx /\ c <> br /\ c <> bg /\ c <> bp) ->
  (forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->
    exists v, get M (c,0%Z) = Some (true,v)) ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat new)%Z) = Some Vnull ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat old)%Z) = Some (Vptr (bt,Int.repr base)) ->
  bo <> bn -> bc <> bn -> bc <> bo ->
  (initial = 255 ->
    get le current = None /\ get ge current = Some (bcur,Tptr V293_tcb_type) /\
    load (Tptr V293_tcb_type) M (bcur,0%Z) = Some (Vptr (bct,Int.repr curbase)) /\
    (0 <= curbase)%Z /\ (curbase+50 <= Int.max_unsigned)%Z /\
    load Tint8 M (bct,(curbase+50)%Z) = Some (V293_byteval curprio) /\
    (exists v, get M (bo,0%Z) = Some (true,v))) ->
  get le reserved = None -> get ge reserved = Some (rb,Tint8) ->
  (bt,Int.repr base) <> (rb,Int.zero) ->
  V293_bytes_writable M bc 0%Z 4 ->
  (forall c, In c [b;bn;bt;dy;dby;dx;br;bg;bp;ny;bi;nby;nbx] ->
    c <> bo /\ c <> bc) ->
  exists Mg,
  let Mh := V293_tcb_update_memory Mg bt base new in
  let fr := V293_ready_branch_rows lo hi old new in
  cstepstar P (curs (V293_task_prio_entry_update table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent xi
    current reserved cpu_sr exit_id),
    (kenil,ks)) (ge,le,M) (curs (sskip None),(kenil,ks)) (ge,le,Mh) /\
  V293_tcb_updated_loads Mh bt base new /\
  V293_rekey_bitmap_loads Mh br bg (fst fr) (snd fr) (V293_ready_group (fst fr) (snd fr)) /\
  V293_table_loads V293_tcb_type Mh b
    (update_nth_val new (update_nth_val old entries Vnull) (Vptr (bt,Int.repr base))) /\
  load (Tptr V293_tcb_type) Mh (b,(4*Z.of_nat old)%Z) = Some Vnull /\
  load (Tptr V293_tcb_type) Mh (b,(4*Z.of_nat new)%Z) = Some (Vptr (bt,Int.repr base)) /\
  load (Tptr V293_event_type) Mh (bp,0%Z) = Some Vnull /\
  load (Tptr V293_tcb_type) Mh (bc,0%Z) = Some (Vptr (bt,Int.repr base)) /\
  load (Tcom_ptr 411%Z) Mh (bt,(base+28)%Z) = Some Vnull /\
  (forall i, (i < base+50)%Z \/ (base+54 < i)%Z -> get Mh (bt,i) = get M (bt,i)) /\
  (forall c i, c <> bo -> c <> bc -> c <> b -> c <> dy -> c <> dby -> c <> dx -> c <> br -> c <> bg -> c <> bp -> c <> bt ->
    c <> ny -> c <> bi -> c <> nby -> c <> nbx ->
    get Mh (c,i) = get M (c,i)).
Proof.
  intros P ks ge le M table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp xi bi ny nby nbx
    current reserved cpu_sr exit_id bcur bct curbase rb curprio
    Input N old O L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg
    Lo Ln Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields
    Wy Wby Wx Loads W NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg
    CT CP TP Bi ExtraApart NewTcbApart TW
    NBy NBby NBx NYI NYBY NYBX NIBY NIBX NBYBX CoordApart CoordW
    Empty Slot Onew Cnew CO Self Nreserved Greserved Token CW EntryApart.
  destruct (V293_task_prio_entry_reserved_execution P
    (kseq (V293_task_prio_coordinates_update table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent xi) ks)
    ge le M table oldprio newprio ptcb current reserved cpu_sr exit_id
    b bo bn bc bcur bct curbase initial new curprio (bt,Int.repr base) rb
    Input N O Nt Gt Bo Bn Bc Lo Ln Empty Slot Tbo Tbc Onew Cnew CO Self Nreserved Greserved Token CW)
    as (Ma & Different & Entry & Aold & Anew & Pointer & ASlot & AEmpty & ACW & EntryFrame).
  assert (CF : forall c i, In c [b;bn;bt;dy;dby;dx;br;bg;bp;ny;bi;nby;nbx] ->
    get Ma (c,i) = get M (c,i)).
  { intros c i I. destruct (EntryApart c I) as [A B]. apply EntryFrame; assumption. }
  assert (LF : forall tp c i, In c [b;bn;bt;dy;dby;dx;br;bg;bp;ny;bi;nby;nbx] ->
    load tp Ma (c,i) = load tp M (c,i)).
  { intros tp c i I. apply V293_load_block_frame. intro j. apply CF; exact I. }
  assert (Resources :
    V293_bytes_writable Ma b (4*Z.of_nat old)%Z 4 /\
    V293_bytes_writable Ma b (4*Z.of_nat new)%Z 4 /\
    V293_table_loads V293_tcb_type Ma b entries /\
    V293_tcb_old_loads Ma bt base (V293_prio_row old) (2 ^ V293_prio_row old) (2 ^ V293_prio_bit old) /\
    (exists v, get Ma (dy,0%Z) = Some (true,v)) /\
    (exists v, get Ma (dby,0%Z) = Some (true,v)) /\
    (exists v, get Ma (dx,0%Z) = Some (true,v)) /\
    V293_rekey_bitmap_loads Ma br bg lo hi (V293_ready_group lo hi) /\
    V293_rekey_bitmap_writable Ma br bg /\
    V293_bytes_writable Ma bp 0%Z 4 /\
    load (Tcom_ptr 411%Z) Ma (bt,(base+28)%Z) = Some Vnull /\
    V293_tcb_update_writable Ma bt base /\
    (forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->
      exists v, get Ma (c,0%Z) = Some (true,v))).
  { unfold V293_bytes_writable,V293_table_loads,V293_tcb_old_loads,
      V293_rekey_bitmap_loads,V293_rekey_bitmap_writable,
      V293_tcb_update_writable in *.
    repeat rewrite LF by (simpl; auto 20).
    repeat rewrite CF by (simpl; auto 20).
    repeat split; try tauto.
    - intros k K. rewrite CF by (simpl; auto 20). apply Wo; exact K.
    - intros k K. rewrite CF by (simpl; auto 20). apply Wn; exact K.
    - intros p R. rewrite LF by (simpl; auto 20). apply View; exact R.
    - intros k K. rewrite CF by (simpl; auto 20). apply We; exact K.
    - intros d D. rewrite CF by (simpl; auto 20). apply TW; exact D.
    - intros c I. destruct I as [-> | [-> | [-> | ->]]]; rewrite CF by (simpl; auto 20); apply CoordW; auto. }
  destruct Resources as (AWo & AWn & AView & AFields & AWy & AWby & AWx & ALoads & AW & AWe & AEvent & ATW & ACoordW).
  destruct (V293_task_prio_coordinates_null_update_execution P ks ge le Ma table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi old new entries pevent bp xi bi ny nby nbx
    O ltac:(clear -N; lia) Different L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg
    Aold Anew Pointer AWo AWn Len AView By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart AFields
    AWy AWby AWx ALoads AW NewApart Be AWe AEvent Cr Cg Br Bg Pb Py Pby Px Pr Pg
    CT CP TP Bi ExtraApart NewTcbApart ATW
    NBy NBby NBx NYI NYBY NYBX NIBY NIBX NBYBX CoordApart ACoordW)
    as (Mg & Exec & Updated & Ready & Table & OldSlot & NewSlot & Read & OutPointer & Internal & Untouched & Frame).
  exists Mg. cbn zeta in *. split.
  - unfold V293_task_prio_entry_update.
    eapply c_stepstarn. { eapply stmt_step; [reflexivity|constructor]. }
    eapply V293_cstepstar_trans; [exact Entry | ].
    eapply c_stepstarn. { eapply stmt_step; [reflexivity|constructor]. }
    exact Exec.
  - split; [exact Updated | ]. split; [exact Ready | ]. split; [exact Table | ].
    split; [exact OldSlot | ]. split; [exact NewSlot | ].
    split; [exact Read | ]. split; [exact OutPointer | ].
    split; [exact Internal | ]. split.
    + intros i I. rewrite Untouched by exact I. apply CF; simpl; auto 20.
    + intros c i OB PC A B C D E F G J NY NI NBY NBX.
      rewrite Frame by assumption. apply EntryFrame; assumption.
Qed.

Definition V293_entry_null_fixture_mem (self live : bool) elo ehi : mem :=
  V293_fixture_put_bytes (V293_entry_update_fixture_mem self live elo ehi)
    41%positive 36%Z (encode_val (Tcom_ptr 411%Z) Vnull).
Lemma V293_entry_null_fixture_outside : forall self live elo ehi c i,
  c <> 41%positive \/ (i < 36)%Z \/ (40 <= i)%Z ->
  get (V293_entry_null_fixture_mem self live elo ehi) (c,i) =
    get (V293_entry_update_fixture_mem self live elo ehi) (c,i).
Proof.
  intros self live elo ehi c i R. unfold V293_entry_null_fixture_mem.
  apply V293_fixture_bytes_outside. rewrite encode_val_length. exact R.
Qed.
Theorem V293_task_prio_entry_null_update_witness : forall self live elo ehi,
  elo < 256 -> ehi < 256 -> forall P ks,
  exists Mh,
  load (Tptr V293_tcb_type) (V293_entry_null_fixture_mem self live elo ehi)
    (40%positive,0%Z) = Some Vnull /\
  (forall c, In c [33%positive;73%positive;37%positive;35%positive] ->
    load Tint8 (V293_entry_null_fixture_mem self live elo ehi) (c,0%Z) = Some (V293_byteval 255)) /\
  cstepstar P (curs (V293_task_prio_entry_update
    500%Z 501%Z 502%Z 400%Z 300%Z 301%Z 302%Z 303%Z 304%Z 305%Z 306%Z 307%Z 600%Z 601%Z
    750%Z 900%Z 751%Z 752%Z),(kenil,ks))
    (V293_entry_update_fixture_ge,V293_tcb_update_fixture_le,V293_entry_null_fixture_mem self live elo ehi)
    (curs (sskip None),(kenil,ks)) (V293_entry_update_fixture_ge,V293_tcb_update_fixture_le,Mh) /\
  V293_tcb_updated_loads Mh 41%positive 8%Z 6 /\
  V293_rekey_bitmap_loads Mh 30%positive 31%positive (if live then 80 else 16) 0 1 /\
  V293_table_loads V293_tcb_type Mh 50%positive
    (update_nth_val 6 (update_nth_val 8 V293_prefix_fixture_entries Vnull) (Vptr (41%positive,Int.repr 8))) /\
  load (Tptr V293_tcb_type) Mh (50%positive,32%Z) = Some Vnull /\
  load (Tptr V293_tcb_type) Mh (50%positive,24%Z) = Some (Vptr (41%positive,Int.repr 8)) /\
  load (Tcom_ptr 411%Z) Mh (41%positive,36%Z) = Some Vnull /\
  load (Tptr V293_event_type) Mh (70%positive,0%Z) = Some Vnull /\
  (forall i, get Mh (72%positive,i) = get (V293_entry_null_fixture_mem self live elo ehi) (72%positive,i)).
Proof.
  intros self live elo ehi EL EH P ks.
  destruct (V293_prefix_event_nonnull_entry live elo ehi EL EH)
    as (Lp & Event & We & Fields & View & Wo & Wn & Wy & Wby & Wx & Loads & W & NewLoc & Lo & Ln & Initial & ELoads & EW).
  set (M := V293_entry_null_fixture_mem self live elo ehi).
  assert (CF : forall c i, c<>41%positive -> c<>51%positive -> c<>40%positive -> c<>80%positive ->
    get M (c,i) = get (V293_coordinate_fixture_mem live elo ehi) (c,i)).
  { intros. unfold M. repeat rewrite V293_entry_null_fixture_outside by (left; assumption). apply V293_entry_update_fixture_frame; assumption. }
  assert (LF : forall tp c i, c<>41%positive -> c<>51%positive -> c<>40%positive -> c<>80%positive ->
    load tp M (c,i) = load tp (V293_coordinate_fixture_mem live elo ehi) (c,i)).
  { intros. apply V293_load_block_frame. intro j. apply CF; assumption. }
  assert (RF : forall tp c i, c <> 41%positive -> c <> 73%positive -> c <> 33%positive -> c <> 37%positive -> c <> 35%positive ->
    c<>51%positive -> c<>40%positive -> c<>80%positive ->
    load tp M (c,i) = load tp (V293_prefix_event_nonnull_mem live elo ehi) (c,i)).
  { intros. rewrite LF by assumption. apply V293_load_block_frame. intro j.
    rewrite V293_coordinate_fixture_delta by (intro E; inversion E; congruence).
    apply V293_tcb_update_fixture_outside; [assumption | left; assumption]. }
  assert (HEvent : load (Tcom_ptr 411%Z) M (41%positive,36%Z) = Some Vnull).
  { unfold M,V293_entry_null_fixture_mem. apply V293_fixture_encoded_load. reflexivity. }
  assert (HighByte : forall i, (40 <= i)%Z ->
    load Tint8 M (41%positive,i) = load Tint8 (V293_entry_update_fixture_mem self live elo ehi) (41%positive,i)).
  { intros i I. unfold load,loadm. rewrite (V293_loadbytes_ext _ (V293_entry_update_fixture_mem self live elo ehi) M).
    - reflexivity.
    - intros k K. unfold M. apply V293_entry_null_fixture_outside. right; right; lia. }
  assert (HFields : V293_tcb_old_loads M 41%positive 8%Z 1 2 1).
  { unfold V293_tcb_old_loads. repeat split; rewrite HighByte by lia;
    apply (eq_trans (V293_load_block_frame _ _ _ _ _ (fun i => V293_entry_update_fixture_frame self live elo ehi 41%positive i ltac:(discriminate) ltac:(discriminate) ltac:(discriminate))));
    unfold V293_coordinate_fixture_mem; repeat rewrite V293_put_byte_other_load by discriminate; entry_update_load. }
  assert (HView : V293_table_loads V293_tcb_type M 50%positive V293_prefix_fixture_entries).
  { intros p R. rewrite RF by discriminate. exact (View p R). }
  assert (HWo : V293_bytes_writable M 50%positive 32%Z 4).
  { intros k K. unfold M; repeat rewrite V293_entry_null_fixture_outside by (left; discriminate); repeat rewrite V293_entry_update_fixture_frame by discriminate; repeat rewrite V293_coordinate_fixture_delta by (intro Eq; inversion Eq; discriminate); rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact (Wo k K). }
  assert (HWn : V293_bytes_writable M 50%positive 24%Z 4).
  { intros k K. unfold M; repeat rewrite V293_entry_null_fixture_outside by (left; discriminate); repeat rewrite V293_entry_update_fixture_frame by discriminate; repeat rewrite V293_coordinate_fixture_delta by (intro Eq; inversion Eq; discriminate); rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact (Wn k K). }
  assert (HWe : V293_bytes_writable M 70%positive 0%Z 4).
  { intros k K. unfold M; repeat rewrite V293_entry_null_fixture_outside by (left; discriminate); repeat rewrite V293_entry_update_fixture_frame by discriminate; repeat rewrite V293_coordinate_fixture_delta by (intro Eq; inversion Eq; discriminate); rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact (We k K). }
  assert (HWy : exists v, get M (32%positive,0%Z) = Some (true,v)).
  { unfold M; repeat rewrite V293_entry_null_fixture_outside by (left; discriminate); repeat rewrite V293_entry_update_fixture_frame by discriminate; repeat rewrite V293_coordinate_fixture_delta by (intro Eq; inversion Eq; discriminate); rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact Wy. }
  assert (HWby : exists v, get M (36%positive,0%Z) = Some (true,v)).
  { unfold M; repeat rewrite V293_entry_null_fixture_outside by (left; discriminate); repeat rewrite V293_entry_update_fixture_frame by discriminate; repeat rewrite V293_coordinate_fixture_delta by (intro Eq; inversion Eq; discriminate); rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact Wby. }
  assert (HWx : exists v, get M (34%positive,0%Z) = Some (true,v)).
  { unfold M; repeat rewrite V293_entry_null_fixture_outside by (left; discriminate); repeat rewrite V293_entry_update_fixture_frame by discriminate; repeat rewrite V293_coordinate_fixture_delta by (intro Eq; inversion Eq; discriminate); rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact Wx. }
  assert (HLoads : V293_rekey_bitmap_loads M 30%positive 31%positive 16 (if live then 1 else 0)
    (V293_ready_group 16 (if live then 1 else 0))).
  { unfold V293_rekey_bitmap_loads in *. repeat rewrite RF by discriminate. exact Loads. }
  assert (HW : V293_rekey_bitmap_writable M 30%positive 31%positive).
  { unfold V293_rekey_bitmap_writable in *.
    unfold M; repeat rewrite V293_entry_null_fixture_outside by (left; discriminate); repeat rewrite V293_entry_update_fixture_frame by discriminate; repeat rewrite V293_coordinate_fixture_delta by (intro Eq; inversion Eq; discriminate); repeat rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact W. }
  assert (HLn : load Tint8 M (52%positive,0%Z) = Some (V293_byteval 6)).
  { rewrite RF by discriminate. exact Ln. }
  assert (HTW : V293_tcb_update_writable M 41%positive 8%Z).
  { intros d D. assert (d=50 \/ d=51 \/ d=52 \/ d=53 \/ d=54)%Z by lia.
    destruct H as [-> | [-> | [-> | [-> | ->]]]]; unfold M; repeat rewrite V293_entry_null_fixture_outside by (right; right; lia); repeat rewrite V293_entry_update_fixture_frame by discriminate; repeat rewrite V293_coordinate_fixture_delta by (intro Eq; inversion Eq; discriminate);
      eexists; entry_update_get; reflexivity. }
  assert (HLo : load Tint8 M (51%positive,0%Z) = Some (V293_byteval (if self then 255 else 8))).
  { rewrite (V293_load_block_frame _ (V293_entry_update_fixture_mem self live elo ehi) M 51%positive 0%Z (fun i => V293_entry_null_fixture_outside self live elo ehi 51%positive i ltac:(left; discriminate))). unfold V293_entry_update_fixture_mem. apply V293_put_byte_load. destruct self; lia. }
  assert (SelectorW : exists v, get M (51%positive,0%Z) = Some (true,v)).
  { unfold M. repeat rewrite V293_entry_null_fixture_outside by (left; discriminate). unfold V293_entry_update_fixture_mem. eexists. apply V293_put_byte_get_same. }
  assert (OuterLF : forall tp c i, c<>41%positive -> c<>51%positive ->
    load tp M (c,i) = load tp
      (V293_fixture_put_bytes
        (V293_fixture_put_bytes (V293_coordinate_fixture_mem live elo ehi) 40%positive 0%Z
          (encode_val (Tptr V293_tcb_type) Vnull))
        80%positive 0%Z (encode_val (Tptr V293_tcb_type) (Vptr (41%positive,Int.repr 8)))) (c,i)).
  { intros tp c i A B. apply V293_load_block_frame. intro j.
    unfold M. repeat rewrite V293_entry_null_fixture_outside by (left; assumption). unfold V293_entry_update_fixture_mem.
    apply V293_put_byte_other. intro E; inversion E; congruence. }
  assert (Current : load (Tptr V293_tcb_type) M (80%positive,0%Z) = Some (Vptr (41%positive,Int.repr 8))).
  { rewrite OuterLF by discriminate. apply V293_fixture_pointer_load. reflexivity. }
  assert (Null : load (Tptr V293_tcb_type) M (40%positive,0%Z) = Some Vnull).
  { rewrite OuterLF by discriminate. unfold load,loadm. rewrite V293_loadbytes_ext with
      (M:=V293_fixture_put_bytes (V293_coordinate_fixture_mem live elo ehi) 40%positive 0%Z
        (encode_val (Tptr V293_tcb_type) Vnull)).
    - apply V293_fixture_pointer_load. reflexivity.
    - intros k K. apply V293_fixture_bytes_outside. left; discriminate. }
  assert (CW : V293_bytes_writable M 40%positive 0%Z 4).
  { intros k K. unfold M. repeat rewrite V293_entry_null_fixture_outside by (left; discriminate). unfold V293_entry_update_fixture_mem.
    rewrite V293_put_byte_other by discriminate.
    rewrite V293_fixture_bytes_outside by (left; discriminate).
    eexists. apply V293_fixture_bytes_nth. rewrite encode_val_length; exact K. }
  assert (Prio : load Tint8 M (41%positive,58%Z) = Some (V293_byteval 8)).
  { rewrite HighByte by lia. rewrite (V293_load_block_frame _ _ _ 41%positive 58%Z
      (fun i => V293_entry_update_fixture_frame self live elo ehi 41%positive i ltac:(discriminate) ltac:(discriminate) ltac:(discriminate))).
    unfold V293_coordinate_fixture_mem. repeat rewrite V293_put_byte_other_load by discriminate. entry_update_load. }
  assert (Resolved : (if (if self then 255 else 8) =? 255 then 8 else (if self then 255 else 8)) = 8)
    by (destruct self; reflexivity).
  destruct (V293_task_prio_entry_null_update_execution P ks V293_entry_update_fixture_ge V293_tcb_update_fixture_le
    M 500%Z 501%Z 502%Z 400%Z 300%Z 301%Z 302%Z 303%Z 304%Z 305%Z 306%Z 307%Z
    50%positive 51%positive 52%positive 40%positive 41%positive 32%positive 36%positive 34%positive
    8%Z 30%positive 31%positive 16 (if live then 1 else 0) (if self then 255 else 8) 6 V293_prefix_fixture_entries
    600%Z 70%positive 601%Z 73%positive 33%positive 37%positive 35%positive
    750%Z 900%Z 751%Z 752%Z 80%positive 41%positive 8%Z 99%positive 8)
    as (Mg & Exec & Updated & FinalLoads & FinalView & OldSlot & NewSlot & Read & Pointer & InternalEvent & Untouched & Frame).
  all: try rewrite Resolved; try assumption; try discriminate; try (entry_update_bind; reflexivity);
    try (change (0 <= 8)%Z; lia); try (change (8+55 <= 4294967295)%Z; lia);
    try (change (0 <= 5)%Z; lia); try (change (5+12 <= 4294967295)%Z; lia);
    try (change (8<13); lia); try (change (6<12); lia); try (change (16<256); lia);
    try (destruct live; lia); try (destruct self; cbn; lia);
    try (change (length V293_prefix_fixture_entries = 13); reflexivity).
  - intros x v c I Bind. cbn [V293_rekey_new_bindings In] in I.
    destruct I as [E|[E|[E|F]]]; try contradiction; inversion E; subst x v;
      unfold V293_tcb_update_fixture_le,V293_event_fixture_le,V293_prefix_fixture_le,V293_read_ready_fixture_le,V293_ready_fragment_fixture_le in Bind;
      repeat first [rewrite map_get_set in Bind | rewrite map_get_set' in Bind by discriminate];
      inversion Bind; subst c; repeat split; discriminate.
  - intros x v c I Bind. cbn [V293_rekey_new_bindings In] in I.
    destruct I as [E|[E|[E|F]]]; try contradiction; inversion E; subst x v;
      unfold V293_tcb_update_fixture_le,V293_event_fixture_le,V293_prefix_fixture_le,V293_read_ready_fixture_le,V293_ready_fragment_fixture_le in Bind;
      repeat first [rewrite map_get_set in Bind | rewrite map_get_set' in Bind by discriminate];
      inversion Bind; subst c; split; discriminate.
  - intros c Cases. destruct Cases as [-> | [-> | [-> | ->]]];
      rewrite CF by discriminate; unfold V293_coordinate_fixture_mem;
      repeat rewrite V293_put_byte_other by discriminate;
      eexists; apply V293_put_byte_get_same.
  - change (load (Tptr V293_tcb_type) M (50%positive,24%Z) = Some (nth 6 V293_prefix_fixture_entries Vnull)).
    exact (HView 6 ltac:(clear; lia)).
  - change (load (Tptr V293_tcb_type) M (50%positive,32%Z) = Some (nth 8 V293_prefix_fixture_entries Vnull)).
    exact (HView 8 ltac:(clear; lia)).
  - intro IsSelf. repeat split; try (entry_update_bind; reflexivity); try assumption;
      try (change (0<=8)%Z; lia); try (change (8+50<=4294967295)%Z; lia).
  - exists (V293_tcb_update_memory Mg 41%positive 8%Z 6). rewrite Resolved in *.
    split; [exact Null | ]. split.
    + intros c I. rewrite LF by (clear - I; cbn in I; intuition congruence).
      apply V293_coordinate_fixture_stale. clear - I; cbn in I; intuition congruence.
    + split; [exact Exec | ]. split; [exact Updated | ].
      split; [destruct live; exact FinalLoads | ].
      split; [exact FinalView | ]. split; [exact OldSlot | ]. split; [exact NewSlot | ]. split; [exact InternalEvent | ]. split; [exact Read | ]. intro i. apply Frame; discriminate.
Qed.

(* The analysis adapter passes &cpu_sr, not its saved integer value.
   These results stop BEFORE entering the port function: no interrupt-state
   restoration, port implementation, or caller return is assumed/proved. *)
Lemma V293_cpu_sr_address_eval : forall ge le M cpu_sr bs,
  get le cpu_sr = Some (bs,Tint32) ->
  evaltype (eaddrof (evar cpu_sr)) (ge,le,M) = Some (Tptr Tint32) /\
  evalval (eaddrof (evar cpu_sr)) (ge,le,M) = Some (Vptr (bs,Int.zero)).
Proof.
  intros ge le M cpu_sr bs B. split;
    cbn [evaltype evalval evaladdr get_lenv get_genv get_mem];
    rewrite B; reflexivity.
Qed.

Lemma V293_task_prio_error_call_execution :
  forall P ks ge le M cpu_sr exit_id bs error,
  get le cpu_sr = Some (bs,Tint32) ->
  cstepstar P
    (curs (sseq (scall exit_id (eaddrof (evar cpu_sr) :: nil))
      (srete (econst32 (Int.repr error)))),(kenil,ks)) (ge,le,M)
    (curs (sfexec exit_id (Vptr (bs,Int.zero) :: nil) (Tptr Tint32 :: nil)),
      (kenil,kseq (srete (econst32 (Int.repr error))) ks)) (ge,le,M).
Proof.
  intros P ks ge le M cpu_sr exit_id bs error B.
  destruct (V293_cpu_sr_address_eval ge le M cpu_sr bs B) as [T V].
  eapply c_stepstarn. { eapply stmt_step; [reflexivity | apply sseq_step]. }
  eapply c_stepstarn. { eapply stmt_step; [reflexivity | apply spcall_step; exact T]. }
  eapply c_stepstarn. { eapply expr_step; [reflexivity | apply eaddr_step; exact V]. }
  eapply c_stepstarn. { eapply stmt_step; [reflexivity | apply svfevalnil_step]. }
  apply c_stepstar0.
Qed.

(* The two witnesses are extracted from the REAL entry-lookup statement by
   the first equality; changing one call to pass a value invalidates it.
   Branch guards are not executed here. Each branch retains its own return. *)
Theorem V293_task_prio_error_exit_arguments :
  forall P ks ge le M table oldprio newprio ptcb current cpu_sr exit_id bs,
  get le cpu_sr = Some (bs,Tint32) ->
  exists occupied absent,
    V293_task_prio_entry_lookup table oldprio newprio ptcb current cpu_sr exit_id =
      sseq (sifthen (eunop oppsite (V293_task_prio_null_test
        (earrayelem (evar table) (evar newprio)))) occupied)
        (sseq (V293_task_prio_self_read oldprio current)
          (sseq (V293_task_prio_lookup table oldprio ptcb)
            (sifthen (V293_task_prio_null_test (evar ptcb)) absent))) /\
    cstepstar P (curs occupied,(kenil,ks)) (ge,le,M)
      (curs (sfexec exit_id (Vptr (bs,Int.zero) :: nil) (Tptr Tint32 :: nil)),
        (kenil,kseq (srete (econst32 (Int.repr 40))) ks)) (ge,le,M) /\
    cstepstar P (curs absent,(kenil,ks)) (ge,le,M)
      (curs (sfexec exit_id (Vptr (bs,Int.zero) :: nil) (Tptr Tint32 :: nil)),
        (kenil,kseq (srete (econst32 (Int.repr 41))) ks)) (ge,le,M) /\
    cstepstar P (curs (V293_task_prio_reserved_error cpu_sr exit_id),(kenil,ks)) (ge,le,M)
      (curs (sfexec exit_id (Vptr (bs,Int.zero) :: nil) (Tptr Tint32 :: nil)),
        (kenil,kseq (srete (econst32 (Int.repr 67))) ks)) (ge,le,M).
Proof.
  intros P ks ge le M table oldprio newprio ptcb current cpu_sr exit_id bs B.
  exists (sseq (scall exit_id (eaddrof (evar cpu_sr) :: nil)) (srete (econst32 (Int.repr 40)))).
  exists (sseq (scall exit_id (eaddrof (evar cpu_sr) :: nil)) (srete (econst32 (Int.repr 41)))).
  split; [reflexivity | ]. split; [apply V293_task_prio_error_call_execution; exact B | ].
  split; apply V293_task_prio_error_call_execution; exact B.
Qed.

(* A closed counterexample to confusing an address with the saved value:
   there is no readable cpu_sr storage at all, but the actual call argument
   still evaluates and its local type is a pointer rather than an integer. *)
Theorem V293_cpu_sr_unreadable_witness :
  let le : env := set emp 601%Z (61%positive,Tint32) in
  evalval (evar 601%Z) (emp,le,emp) = None /\
  evaltype (evar 601%Z) (emp,le,emp) = Some Tint32 /\
  evalval (eaddrof (evar 601%Z)) (emp,le,emp) = Some (Vptr (61%positive,Int.zero)) /\
  evaltype (eaddrof (evar 601%Z)) (emp,le,emp) = Some (Tptr Tint32) /\
  forall P ks,
    cstepstar P (curs (V293_task_prio_reserved_error 601%Z 602%Z),(kenil,ks)) (emp,le,emp)
      (curs (sfexec 602%Z (Vptr (61%positive,Int.zero) :: nil) (Tptr Tint32 :: nil)),
        (kenil,kseq (srete (econst32 (Int.repr 67))) ks)) (emp,le,emp).
Proof.
  cbn zeta. assert (B : get (set emp 601%Z (61%positive,Tint32)) 601%Z =
    Some (61%positive,Tint32)) by apply map_get_set.
  split.
  - reflexivity.
  - split.
    + reflexivity.
    + destruct (V293_cpu_sr_address_eval emp _ emp 601%Z 61%positive B) as [T V].
      split; [exact V | ]. split; [exact T | ].
      intros P ks. apply V293_task_prio_error_call_execution. exact B.
Qed.

(* Compose a skip-terminating prefix with an arbitrary real suffix, including
   a call boundary. The intermediate execution is proved, not a precondition. *)
Lemma V293_sequence_prefix_to : forall P ks ge le M M1 M2 a b final,
  (forall tail, cstepstar P (curs a,(kenil,tail)) (ge,le,M)
    (curs (sskip None),(kenil,tail)) (ge,le,M1)) ->
  cstepstar P (curs b,(kenil,ks)) (ge,le,M1) final (ge,le,M2) ->
  cstepstar P (curs (sseq a b),(kenil,ks)) (ge,le,M) final (ge,le,M2).
Proof.
  intros P ks ge le M M1 M2 a b final Prefix Suffix.
  eapply c_stepstarn. { eapply stmt_step; [reflexivity|apply sseq_step]. }
  eapply V293_cstepstar_trans; [apply Prefix| ].
  eapply c_stepstarn. { eapply stmt_step; [reflexivity|constructor]. }
  exact Suffix.
Qed.

(* Occupied new slot: the old selector, ptcb, and reserved symbol are never
   evaluated. Pending statements remain in the continuation, not executed. *)
Theorem V293_task_prio_occupied_entry_execution :
  forall P ks ge le M table oldprio newprio ptcb current reserved cpu_sr exit_id
    b bn bs new next,
  new < 12 ->
  get le table = None -> get ge table = Some (b,Tarray (Tptr V293_tcb_type) 13) ->
  get le newprio = Some (bn,Tint8) ->
  load Tint8 M (bn,0%Z) = Some (V293_byteval new) ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat new)%Z) = Some (Vptr next) ->
  get le cpu_sr = Some (bs,Tint32) ->
  cstepstar P
    (curs (V293_task_prio_entry_reserved table oldprio newprio ptcb current reserved cpu_sr exit_id),(kenil,ks)) (ge,le,M)
    (curs (sfexec exit_id (Vptr (bs,Int.zero)::nil) (Tptr Tint32::nil)),
      (kenil,kseq (srete (econst32 (Int.repr 40)))
        (kseq (sseq (V293_task_prio_self_read oldprio current)
          (sseq (V293_task_prio_lookup table oldprio ptcb)
            (sifthen (V293_task_prio_null_test (evar ptcb))
              (sseq (scall exit_id (eaddrof (evar cpu_sr)::nil)) (srete (econst32 (Int.repr 41)))))))
          (kseq (V293_task_prio_reserved_guard ptcb reserved cpu_sr exit_id) ks)))) (ge,le,M).
Proof.
  intros P ks ge le M table oldprio newprio ptcb current reserved cpu_sr exit_id b bn bs new next N Nt Gt Bn Ln Slot Bs.
  destruct (V293_entry_array_eval ge le M table newprio b bn new (Vptr next)
    Nt Gt Bn Ln ltac:(lia) Slot) as [T V].
  pose proof (proj2 (V293_entry_null_eval ge le M _ (Vptr next) T V
    (or_intror (ex_intro _ next eq_refl)))) as Test.
  unfold V293_task_prio_entry_reserved,V293_task_prio_entry_lookup.
  eapply c_stepstarn. { eapply stmt_step; [reflexivity|apply sseq_step]. }
  eapply c_stepstarn. { eapply stmt_step; [reflexivity|apply sseq_step]. }
  eapply V293_cstepstar_trans.
  { apply V293_entry_if_select with (flag:=true). exact Test. }
  apply V293_task_prio_error_call_execution. exact Bs.
Qed.

(* SELF resolution is independently usable by NULL lookup. No different-slot
   condition is introduced: an absent old slot may equal the empty new slot. *)
Lemma V293_task_prio_resolve_execution :
  forall P ge le M oldprio current bo bcur bct base old curprio,
  old < 256 ->
  let resolved := if old =? 255 then curprio else old in
  resolved < 13 ->
  get le oldprio = Some (bo,Tint8) ->
  load Tint8 M (bo,0%Z) = Some (V293_byteval old) ->
  (old = 255 ->
    get le current = None /\ get ge current = Some (bcur,Tptr V293_tcb_type) /\
    load (Tptr V293_tcb_type) M (bcur,0%Z) = Some (Vptr (bct,Int.repr base)) /\
    (0 <= base)%Z /\ (base+50 <= Int.max_unsigned)%Z /\
    load Tint8 M (bct,(base+50)%Z) = Some (V293_byteval curprio) /\
    (exists v, get M (bo,0%Z) = Some (true,v))) ->
  exists Ms,
    (forall tail, cstepstar P (curs (V293_task_prio_self_read oldprio current),(kenil,tail)) (ge,le,M)
      (curs (sskip None),(kenil,tail)) (ge,le,Ms)) /\
    load Tint8 Ms (bo,0%Z) = Some (V293_byteval resolved) /\
    (forall c i, c <> bo -> get Ms (c,i) = get M (c,i)).
Proof.
  intros P ge le M oldprio current bo bcur bct base old curprio O resolved R Bo Lo Self.
  destruct (V293_entry_byte_tests ge le M oldprio bo old O Bo Lo) as [_ Test].
  exists (if old =? 255 then V293_put_byte M (bo,0%Z) curprio else M).
  split.
  - intro tail. unfold V293_task_prio_self_read. destruct (old =? 255) eqn:S.
    + destruct (Self (proj1 (Nat.eqb_eq old 255) S)) as (Nc & Gc & Pc & Base & Limit & Prio & W).
      assert (CP : curprio < 256) by (unfold resolved in R; simpl in R; lia).
      destruct (V293_entry_current_prio_eval ge le M current bcur bct base curprio Nc Gc Pc Base Limit Prio) as [T V].
      eapply V293_rekey_if_execution with (flag:=true); [exact Test| |discriminate].
      intros _. eapply V293_coordinate_local_assignment; eassumption.
    + eapply V293_rekey_if_execution with (flag:=false); [exact Test|discriminate|reflexivity].
  - split.
    + unfold resolved. destruct (old =? 255) eqn:S; [apply V293_put_byte_load; unfold resolved in R; simpl in R; lia|exact Lo].
    + intros c i D. destruct (old =? 255); [apply V293_put_byte_other; congruence|reflexivity].
Qed.

Theorem V293_task_prio_absent_entry_execution :
  forall P ks ge le M table oldprio newprio ptcb current reserved cpu_sr exit_id
    b bo bn bc bs bcur bct base old new curprio,
  old < 256 -> new < 12 ->
  let resolved := if old =? 255 then curprio else old in
  resolved < 13 ->
  get le table = None -> get ge table = Some (b,Tarray (Tptr V293_tcb_type) 13) ->
  get le oldprio = Some (bo,Tint8) -> get le newprio = Some (bn,Tint8) ->
  get le ptcb = Some (bc,Tptr V293_tcb_type) -> get le cpu_sr = Some (bs,Tint32) ->
  load Tint8 M (bo,0%Z) = Some (V293_byteval old) ->
  load Tint8 M (bn,0%Z) = Some (V293_byteval new) ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat new)%Z) = Some Vnull ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat resolved)%Z) = Some Vnull ->
  b <> bo -> b <> bc -> bo <> bn -> bc <> bn -> bc <> bo ->
  (old = 255 ->
    get le current = None /\ get ge current = Some (bcur,Tptr V293_tcb_type) /\
    load (Tptr V293_tcb_type) M (bcur,0%Z) = Some (Vptr (bct,Int.repr base)) /\
    (0 <= base)%Z /\ (base+50 <= Int.max_unsigned)%Z /\
    load Tint8 M (bct,(base+50)%Z) = Some (V293_byteval curprio) /\
    (exists v, get M (bo,0%Z) = Some (true,v))) ->
  V293_bytes_writable M bc 0%Z 4 ->
  exists Mf,
    cstepstar P (curs (V293_task_prio_entry_reserved table oldprio newprio ptcb current reserved cpu_sr exit_id),(kenil,ks)) (ge,le,M)
      (curs (sfexec exit_id (Vptr (bs,Int.zero)::nil) (Tptr Tint32::nil)),
        (kenil,kseq (srete (econst32 (Int.repr 41)))
          (kseq (V293_task_prio_reserved_guard ptcb reserved cpu_sr exit_id) ks))) (ge,le,Mf) /\
    load Tint8 Mf (bo,0%Z) = Some (V293_byteval resolved) /\
    load Tint8 Mf (bn,0%Z) = Some (V293_byteval new) /\
    load (Tptr V293_tcb_type) Mf (bc,0%Z) = Some Vnull /\
    (forall i, i < 13 -> load (Tptr V293_tcb_type) Mf (b,(4*Z.of_nat i)%Z) = load (Tptr V293_tcb_type) M (b,(4*Z.of_nat i)%Z)) /\
    (forall c i, c <> bo -> c <> bc -> get Mf (c,i) = get M (c,i)).
Proof.
  intros P ks ge le M table oldprio newprio ptcb current reserved cpu_sr exit_id
    b bo bn bc bs bcur bct base old new curprio O N resolved R Nt Gt Bo Bn Bc Bs Lo Ln Empty Slot Tbo Tbc OB CB CO Self CW.
  destruct (V293_task_prio_resolve_execution P ge le M oldprio current bo bcur bct base old curprio O R Bo Lo Self)
    as (Ms & SelfStep & Read & SF).
  assert (SL : forall tp c i, c <> bo -> load tp Ms (c,i) = load tp M (c,i)).
  { intros tp c i D. apply V293_load_block_frame. intro j. apply SF; exact D. }
  assert (W : V293_bytes_writable Ms bc 0%Z 4).
  { intros k K. rewrite SF by exact CO. apply CW; exact K. }
  destruct (V293_storebytes_exists (encode_val (Tptr V293_tcb_type) Vnull) Ms bc 0%Z) as [Mf Store].
  { rewrite encode_val_length. exact W. }
  assert (PF : forall c i, c <> bc -> get Mf (c,i) = get Ms (c,i)).
  { intros c i D. eapply V293_storebytes_outside; [exact Store|left;exact D]. }
  assert (PL : forall tp c i, c <> bc -> load tp Mf (c,i) = load tp Ms (c,i)).
  { intros tp c i D. apply V293_load_block_frame. intro j. apply PF; exact D. }
  assert (Pointer : load (Tptr V293_tcb_type) Mf (bc,0%Z) = Some Vnull).
  { eapply V293_store_readback; [reflexivity|exact Store]. }
  destruct (V293_entry_array_eval ge le M table newprio b bn new Vnull Nt Gt Bn Ln ltac:(lia) Empty) as [NT NV].
  pose proof (proj2 (V293_entry_null_eval ge le M _ Vnull NT NV (or_introl eq_refl))) as TargetTest.
  assert (SlotS : load (Tptr V293_tcb_type) Ms (b,(4*Z.of_nat resolved)%Z) = Some Vnull).
  { rewrite SL by exact Tbo. exact Slot. }
  destruct (V293_entry_array_eval ge le Ms table oldprio b bo resolved Vnull Nt Gt Bo Read R SlotS) as [OT OV].
  assert (Lookup : forall tail, cstepstar P (curs (V293_task_prio_lookup table oldprio ptcb),(kenil,tail)) (ge,le,Ms)
      (curs (sskip None),(kenil,tail)) (ge,le,Mf)).
  { intro tail. unfold V293_task_prio_lookup.
    eapply V293_assign_pointer_execution with (tr:=Tptr V293_tcb_type) (b:=bc) (off:=0%Z); try eassumption.
    - cbn [evaltype get_lenv]. rewrite Bc. reflexivity.
    - apply eq_vptr. eauto.
    - cbn [evaladdr get_lenv]. rewrite Bc. reflexivity.
    - change (0<=0<=4294967295)%Z. lia. }
  assert (NullTest : evalval (V293_task_prio_null_test (evar ptcb)) (ge,le,Mf) = Some (Vint32 Int.one)).
  { unfold V293_task_prio_null_test. cbn [evalval evaltype get_lenv get_genv get_mem].
    rewrite Bc. cbn beta iota. rewrite Pointer. reflexivity. }
  exists Mf. split.
  - unfold V293_task_prio_entry_reserved.
    eapply c_stepstarn. { eapply stmt_step; [reflexivity|apply sseq_step]. }
    unfold V293_task_prio_entry_lookup.
    eapply V293_sequence_prefix_to with (M1:=M).
    + intro tail. eapply V293_rekey_if_execution with (flag:=false); [exact TargetTest|discriminate|reflexivity].
    + eapply V293_sequence_prefix_to with (M1:=Ms); [exact SelfStep| ].
      eapply V293_sequence_prefix_to with (M1:=Mf); [exact Lookup| ].
      eapply V293_cstepstar_trans.
      { apply V293_entry_if_select with (flag:=true). exact NullTest. }
      apply V293_task_prio_error_call_execution. exact Bs.
  - split; [rewrite PL by congruence; exact Read| ].
    split; [rewrite PL,SL by congruence; exact Ln| ].
    split; [exact Pointer| ]. split.
    + intros i I. rewrite PL,SL by congruence. reflexivity.
    + intros c i D E. rewrite PF by exact E. apply SF; exact D.
Qed.

(* A reserved token comes from the table lookup, not a preinitialized ptcb.
   The successful lookup lemma is valid for any non-NULL pointer, including
   the token; it does not assume non-collision with the reserved symbol. *)
Theorem V293_task_prio_reserved_entry_error_execution :
  forall P ks ge le M table oldprio newprio ptcb current reserved cpu_sr exit_id
    b bo bn bc bs bcur bct base old new curprio br,
  old < 256 -> new < 12 ->
  let resolved := if old =? 255 then curprio else old in
  resolved < 13 ->
  get le table = None -> get ge table = Some (b,Tarray (Tptr V293_tcb_type) 13) ->
  get le oldprio = Some (bo,Tint8) -> get le newprio = Some (bn,Tint8) ->
  get le ptcb = Some (bc,Tptr V293_tcb_type) -> get le cpu_sr = Some (bs,Tint32) ->
  get le reserved = None -> get ge reserved = Some (br,Tint8) ->
  load Tint8 M (bo,0%Z) = Some (V293_byteval old) ->
  load Tint8 M (bn,0%Z) = Some (V293_byteval new) ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat new)%Z) = Some Vnull ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat resolved)%Z) = Some (Vptr (br,Int.zero)) ->
  b <> bo -> b <> bc -> bo <> bn -> bc <> bn -> bc <> bo ->
  (old = 255 ->
    get le current = None /\ get ge current = Some (bcur,Tptr V293_tcb_type) /\
    load (Tptr V293_tcb_type) M (bcur,0%Z) = Some (Vptr (bct,Int.repr base)) /\
    (0 <= base)%Z /\ (base+50 <= Int.max_unsigned)%Z /\
    load Tint8 M (bct,(base+50)%Z) = Some (V293_byteval curprio) /\
    (exists v, get M (bo,0%Z) = Some (true,v))) ->
  V293_bytes_writable M bc 0%Z 4 ->
  exists Mf,
    resolved <> new /\
    cstepstar P (curs (V293_task_prio_entry_reserved table oldprio newprio ptcb current reserved cpu_sr exit_id),(kenil,ks)) (ge,le,M)
      (curs (sfexec exit_id (Vptr (bs,Int.zero)::nil) (Tptr Tint32::nil)),
        (kenil,kseq (srete (econst32 (Int.repr 67))) ks)) (ge,le,Mf) /\
    load Tint8 Mf (bo,0%Z) = Some (V293_byteval resolved) /\
    load Tint8 Mf (bn,0%Z) = Some (V293_byteval new) /\
    load (Tptr V293_tcb_type) Mf (bc,0%Z) = Some (Vptr (br,Int.zero)) /\
    load (Tptr V293_tcb_type) Mf (b,(4*Z.of_nat resolved)%Z) = Some (Vptr (br,Int.zero)) /\
    load (Tptr V293_tcb_type) Mf (b,(4*Z.of_nat new)%Z) = Some Vnull /\
    (forall c i, c <> bo -> c <> bc -> get Mf (c,i) = get M (c,i)).
Proof.
  intros P ks ge le M table oldprio newprio ptcb current reserved cpu_sr exit_id
    b bo bn bc bs bcur bct base old new curprio br O N resolved R Nt Gt Bo Bn Bc Bs Nr Gr Lo Ln Empty Slot Tbo Tbc OB CB CO Self CW.
  destruct (V293_task_prio_entry_lookup_execution P
    (kseq (V293_task_prio_reserved_guard ptcb reserved cpu_sr exit_id) ks) ge le M
    table oldprio newprio ptcb current cpu_sr exit_id b bo bn bc bcur bct base old new curprio
    (br,Int.zero) O N R Nt Gt Bo Bn Bc Lo Ln Empty Slot Tbo Tbc OB CB CO Self CW)
    as (Mf & Different & Exec & Old & New & Pointer & OldSlot & NewSlot & W & Frame).
  exists Mf. split; [exact Different| ]. split.
  - unfold V293_task_prio_entry_reserved.
    eapply c_stepstarn. { eapply stmt_step; [reflexivity|apply sseq_step]. }
    eapply V293_cstepstar_trans; [exact Exec| ].
    eapply c_stepstarn. { eapply stmt_step; [reflexivity|constructor]. }
    pose proof (V293_task_prio_reserved_select P ks ge le Mf ptcb reserved cpu_sr exit_id bc br
      (Vptr (br,Int.zero)) Bc Pointer (or_intror (ex_intro _ (br,Int.zero) eq_refl)) Nr Gr) as Select.
    assert (Match : V293_reserved_matches br (Vptr (br,Int.zero)) = true).
    { apply V293_reserved_matches_pointer. reflexivity. }
    rewrite Match in Select.
    eapply V293_cstepstar_trans; [exact Select| ].
    unfold V293_task_prio_reserved_error. apply V293_task_prio_error_call_execution. exact Bs.
  - repeat split; assumption.
Qed.

(* Closed physical witnesses, not initialization/shared-state reachability.
   kind 0: occupied new=6; kind 1: absent old=new=8; kind 2: reserved old=8.
   ptcb starts as a DIFFERENT pointer, so the lookup write is observable. *)
Definition V293_error_fixture_le : env :=
  set V293_entry_fixture_le 601%Z (61%positive,Tint32).
Definition V293_error_fixture_ge : env :=
  set V293_entry_fixture_ge 603%Z (90%positive,Tint8).
Definition V293_error_fixture_entries (kind : nat) : list val :=
  Vnull::Vnull::Vnull::Vnull::Vnull::Vnull::
    (if kind =? 0 then Vptr (90%positive,Int.zero) else Vnull)::Vnull::
    (if kind =? 2 then Vptr (90%positive,Int.zero) else Vnull)::
    Vnull::Vnull::Vnull::Vnull::nil.
Definition V293_error_fixture_core : mem :=
  V293_fixture_put_bytes
    (V293_fixture_put_bytes emp 80%positive 0%Z
      (encode_val (Tptr V293_tcb_type) (Vptr (41%positive,Int.repr 8))))
    40%positive 0%Z (encode_val (Tptr V293_tcb_type) (Vptr (70%positive,Int.zero))).
Definition V293_error_fixture_mem (self : bool) (kind : nat) : mem :=
  V293_put_byte (V293_put_byte (V293_put_byte
    (V293_fixture_put_table V293_error_fixture_core 50%positive 0%Z (V293_error_fixture_entries kind))
    (41%positive,58%Z) 8) (51%positive,0%Z) (if self then 255 else 8))
    (52%positive,0%Z) (if kind =? 1 then 8 else 6).

Local Ltac error_fixture_bind :=
  unfold V293_error_fixture_le,V293_error_fixture_ge,V293_entry_fixture_le,V293_entry_fixture_ge;
  repeat first [rewrite map_get_set | rewrite map_get_set' by discriminate]; reflexivity.

Lemma V293_error_fixture_resources : forall self kind,
  let M := V293_error_fixture_mem self kind in
  load Tint8 M (51%positive,0%Z) = Some (V293_byteval (if self then 255 else 8)) /\
  load Tint8 M (52%positive,0%Z) = Some (V293_byteval (if kind =? 1 then 8 else 6)) /\
  load (Tptr V293_tcb_type) M (50%positive,24%Z) = Some (if kind =? 0 then Vptr (90%positive,Int.zero) else Vnull) /\
  load (Tptr V293_tcb_type) M (50%positive,32%Z) = Some (if kind =? 2 then Vptr (90%positive,Int.zero) else Vnull) /\
  load (Tptr V293_tcb_type) M (80%positive,0%Z) = Some (Vptr (41%positive,Int.repr 8)) /\
  load Tint8 M (41%positive,58%Z) = Some (V293_byteval 8) /\
  load (Tptr V293_tcb_type) M (40%positive,0%Z) = Some (Vptr (70%positive,Int.zero)) /\
  (exists v, get M (51%positive,0%Z) = Some (true,v)) /\
  V293_bytes_writable M 40%positive 0%Z 4.
Proof.
  intros self kind. cbn zeta.
  assert (Outer : forall c i, c <> 41%positive -> c <> 51%positive -> c <> 52%positive ->
    get (V293_error_fixture_mem self kind) (c,i) =
      get (V293_fixture_put_table V293_error_fixture_core 50%positive 0%Z (V293_error_fixture_entries kind)) (c,i)).
  { intros c i A B C. unfold V293_error_fixture_mem.
    repeat rewrite V293_put_byte_other by (intro E; inversion E; congruence). reflexivity. }
  assert (LF : forall tp c i, c <> 41%positive -> c <> 51%positive -> c <> 52%positive ->
    load tp (V293_error_fixture_mem self kind) (c,i) =
      load tp (V293_fixture_put_table V293_error_fixture_core 50%positive 0%Z (V293_error_fixture_entries kind)) (c,i)).
  { intros tp c i A B C. apply V293_load_block_frame. intro j. apply Outer; assumption. }
  split.
  - unfold V293_error_fixture_mem. rewrite V293_put_byte_other_load by discriminate.
    apply V293_put_byte_load. destruct self; lia.
  - split; [unfold V293_error_fixture_mem; apply V293_put_byte_load; destruct (kind =? 1); lia | ]. split.
    + rewrite LF by discriminate. change (load (Tptr V293_tcb_type)
        (V293_fixture_put_table V293_error_fixture_core 50%positive 0%Z (V293_error_fixture_entries kind))
        (50%positive,(0+4*Z.of_nat 6)%Z) = Some (nth 6 (V293_error_fixture_entries kind) Vnull)).
      apply V293_fixture_table_slot; [unfold V293_error_fixture_entries; destruct (kind =? 0), (kind =? 2); repeat constructor|cbn;lia].
    + split.
      * rewrite LF by discriminate. change (load (Tptr V293_tcb_type)
          (V293_fixture_put_table V293_error_fixture_core 50%positive 0%Z (V293_error_fixture_entries kind))
          (50%positive,(0+4*Z.of_nat 8)%Z) = Some (nth 8 (V293_error_fixture_entries kind) Vnull)).
        apply V293_fixture_table_slot; [unfold V293_error_fixture_entries; destruct (kind =? 0), (kind =? 2); repeat constructor|cbn;lia].
      * assert (CoreFrame : forall tp c i, c <> 41%positive -> c <> 51%positive -> c <> 52%positive -> c <> 50%positive ->
          load tp (V293_error_fixture_mem self kind) (c,i) = load tp V293_error_fixture_core (c,i)).
        { intros tp c i A B C D. apply V293_load_block_frame. intro j.
          rewrite Outer by assumption. apply V293_fixture_table_outside. exact D. }
        split.
        -- rewrite CoreFrame by discriminate. unfold V293_error_fixture_core.
           unfold load,loadm. rewrite V293_loadbytes_ext with
             (M:=V293_fixture_put_bytes emp 80%positive 0%Z
               (encode_val (Tptr V293_tcb_type) (Vptr (41%positive,Int.repr 8)))).
           ++ apply V293_fixture_pointer_load. reflexivity.
           ++ intros k K. apply V293_fixture_bytes_outside. left; discriminate.
        -- split.
           ++ unfold V293_error_fixture_mem. repeat rewrite V293_put_byte_other_load by discriminate.
              apply V293_put_byte_load. lia.
           ++ split.
              ** rewrite CoreFrame by discriminate. unfold V293_error_fixture_core.
                 apply V293_fixture_pointer_load. reflexivity.
              ** split.
                 --- unfold V293_error_fixture_mem. rewrite V293_put_byte_other by discriminate.
                     eexists. apply V293_put_byte_get_same.
                 --- intros k K. rewrite Outer by discriminate.
                     rewrite V293_fixture_table_outside by discriminate.
                     unfold V293_error_fixture_core.
                     exists (nth k (encode_val (Tptr V293_tcb_type) (Vptr (70%positive,Int.zero))) Undef).
                     apply V293_fixture_bytes_nth. rewrite encode_val_length. exact K.
Qed.

Theorem V293_task_prio_absent_same_slot_witness : forall self P ks,
  exists Mf,
    load (Tptr V293_tcb_type) (V293_error_fixture_mem self 1) (40%positive,0%Z) =
      Some (Vptr (70%positive,Int.zero)) /\
    cstepstar P (curs (V293_task_prio_entry_reserved 500%Z 501%Z 502%Z 400%Z 750%Z 603%Z 601%Z 602%Z),(kenil,ks))
      (V293_error_fixture_ge,V293_error_fixture_le,V293_error_fixture_mem self 1)
      (curs (sfexec 602%Z (Vptr (61%positive,Int.zero)::nil) (Tptr Tint32::nil)),
        (kenil,kseq (srete (econst32 (Int.repr 41)))
          (kseq (V293_task_prio_reserved_guard 400%Z 603%Z 601%Z 602%Z) ks)))
      (V293_error_fixture_ge,V293_error_fixture_le,Mf) /\
    load Tint8 Mf (51%positive,0%Z) = Some (V293_byteval 8) /\
    load Tint8 Mf (52%positive,0%Z) = Some (V293_byteval 8) /\
    load (Tptr V293_tcb_type) Mf (40%positive,0%Z) = Some Vnull /\
    (forall i, i < 13 -> load (Tptr V293_tcb_type) Mf (50%positive,(4*Z.of_nat i)%Z) =
      load (Tptr V293_tcb_type) (V293_error_fixture_mem self 1) (50%positive,(4*Z.of_nat i)%Z)).
Proof.
  intros self P ks.
  destruct (V293_error_fixture_resources self 1) as (Lo & Ln & Empty & Slot & Current & Prio & Initial & Wo & CW).
  assert (Resolved : (if (if self then 255 else 8) =? 255 then 8 else (if self then 255 else 8)) = 8)
    by (destruct self; reflexivity).
  destruct (V293_task_prio_absent_entry_execution P ks V293_error_fixture_ge V293_error_fixture_le
    (V293_error_fixture_mem self 1) 500%Z 501%Z 502%Z 400%Z 750%Z 603%Z 601%Z 602%Z
    50%positive 51%positive 52%positive 40%positive 61%positive 80%positive 41%positive 8%Z
    (if self then 255 else 8) 8 8)
    as (Mf & Exec & Old & New & Pointer & Table & Frame).
  all: try error_fixture_bind; try discriminate; try assumption;
    try match goal with |- (_ < _)%nat => destruct self; cbn; lia end;
    try (rewrite Resolved; exact Slot).
  - intro IsSelf. repeat split; try error_fixture_bind;
      try assumption;
      try (change (0<=8)%Z; lia); try (change (8+50<=4294967295)%Z; lia).
  - exists Mf. split; [exact Initial| ].
    rewrite Resolved in *. split; [exact Exec| ]. split; [exact Old| ].
    split; [exact New| ]. split; assumption.
Qed.

Theorem V293_task_prio_reserved_error_witness : forall self P ks,
  exists Mf,
    load (Tptr V293_tcb_type) (V293_error_fixture_mem self 2) (40%positive,0%Z) =
      Some (Vptr (70%positive,Int.zero)) /\
    cstepstar P (curs (V293_task_prio_entry_reserved 500%Z 501%Z 502%Z 400%Z 750%Z 603%Z 601%Z 602%Z),(kenil,ks))
      (V293_error_fixture_ge,V293_error_fixture_le,V293_error_fixture_mem self 2)
      (curs (sfexec 602%Z (Vptr (61%positive,Int.zero)::nil) (Tptr Tint32::nil)),
        (kenil,kseq (srete (econst32 (Int.repr 67))) ks))
      (V293_error_fixture_ge,V293_error_fixture_le,Mf) /\
    load Tint8 Mf (51%positive,0%Z) = Some (V293_byteval 8) /\
    load Tint8 Mf (52%positive,0%Z) = Some (V293_byteval 6) /\
    load (Tptr V293_tcb_type) Mf (40%positive,0%Z) = Some (Vptr (90%positive,Int.zero)) /\
    load (Tptr V293_tcb_type) Mf (50%positive,32%Z) = Some (Vptr (90%positive,Int.zero)) /\
    load (Tptr V293_tcb_type) Mf (50%positive,24%Z) = Some Vnull.
Proof.
  intros self P ks.
  destruct (V293_error_fixture_resources self 2) as (Lo & Ln & Empty & Slot & Current & Prio & Initial & Wo & CW).
  assert (Resolved : (if (if self then 255 else 8) =? 255 then 8 else (if self then 255 else 8)) = 8)
    by (destruct self; reflexivity).
  destruct (V293_task_prio_reserved_entry_error_execution P ks V293_error_fixture_ge V293_error_fixture_le
    (V293_error_fixture_mem self 2) 500%Z 501%Z 502%Z 400%Z 750%Z 603%Z 601%Z 602%Z
    50%positive 51%positive 52%positive 40%positive 61%positive 80%positive 41%positive 8%Z
    (if self then 255 else 8) 6 8 90%positive)
    as (Mf & Different & Exec & Old & New & Pointer & OldSlot & NewSlot & Frame).
  all: try error_fixture_bind; try discriminate; try assumption;
    try match goal with |- (_ < _)%nat => destruct self; cbn; lia end;
    try (rewrite Resolved; exact Slot).
  - intro IsSelf. repeat split; try error_fixture_bind;
      try assumption;
      try (change (0<=8)%Z; lia); try (change (8+50<=4294967295)%Z; lia).
  - exists Mf. split; [exact Initial| ].
    rewrite Resolved in *. split; [exact Exec| ]. split; [exact Old| ].
    split; [exact New| ]. split; [exact Pointer| ]. split; assumption.
Qed.

Theorem V293_task_prio_occupied_error_witness : forall self P ks,
  cstepstar P (curs (V293_task_prio_entry_reserved 500%Z 501%Z 502%Z 400%Z 750%Z 603%Z 601%Z 602%Z),(kenil,ks))
    (V293_error_fixture_ge,V293_error_fixture_le,V293_error_fixture_mem self 0)
    (curs (sfexec 602%Z (Vptr (61%positive,Int.zero)::nil) (Tptr Tint32::nil)),
      (kenil,kseq (srete (econst32 (Int.repr 40)))
        (kseq (sseq (V293_task_prio_self_read 501%Z 750%Z)
          (sseq (V293_task_prio_lookup 500%Z 501%Z 400%Z)
            (sifthen (V293_task_prio_null_test (evar 400%Z))
              (sseq (scall 602%Z (eaddrof (evar 601%Z)::nil)) (srete (econst32 (Int.repr 41)))))))
          (kseq (V293_task_prio_reserved_guard 400%Z 603%Z 601%Z 602%Z) ks))))
    (V293_error_fixture_ge,V293_error_fixture_le,V293_error_fixture_mem self 0).
Proof.
  intros self P ks.
  destruct (V293_error_fixture_resources self 0) as (Lo & Ln & Slot & Rest).
  eapply V293_task_prio_occupied_entry_execution with
    (b:=50%positive) (bn:=52%positive) (new:=6) (next:=(90%positive,Int.zero));
    try error_fixture_bind; try exact Ln; try exact Slot; lia.
Qed.
