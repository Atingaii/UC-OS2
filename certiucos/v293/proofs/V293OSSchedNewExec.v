Require Import Coq.Arith.Arith Lia.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Local Open Scope nat_scope.

Definition V293_write_byte (M : mem) (b : block) (n : nat) : mem :=
  set M (b, 0%Z) (true, Byte (Byte.repr (Int.unsigned (Int.repr (Z.of_nat n))))).

Lemma V293_write_byte_store : forall M b n old,
  get M (b, 0%Z) = Some (true, old) ->
  store Tint8 M (b, 0%Z) (V293_byteval n) = Some (V293_write_byte M b n).
Proof.
  intros M b n old Hw. unfold store, V293_byteval, V293_write_byte.
  cbn [encode_val inj_bytes encode_int]. unfold inj_bytes. cbn [List.map storebytes]. unfold addr, offset in *. rewrite Hw. reflexivity.
Qed.

Lemma V293_encoded_byte_load : forall M b i permission n,
  n < 256 ->
  get M (b, i) = Some (permission, Byte (Byte.repr (Int.unsigned (Int.repr (Z.of_nat n))))) ->
  load Tint8 M (b, i) = Some (V293_byteval n).
Proof.
  intros M b i permission n Hn Hget.
  unfold load, loadm. cbn [typelen loadbytes]. unfold addr, offset in *.
  rewrite Hget.
  change (Some (decode_val Tint8 (encode_val Tint8 (V293_byteval n))) = Some (V293_byteval n)).
  rewrite type_val_mach_encode_val_decode_val; [reflexivity | ].
  unfold V293_byteval, rule_type_val_match.
  rewrite Int.unsigned_repr by
    (unfold Int.max_unsigned, Int.modulus, Int.wordsize; simpl; lia).
  assert (B : (Z.of_nat n <=? Byte.max_unsigned)%Z = true).
  { apply Z.leb_le. unfold Byte.max_unsigned, Byte.modulus, Byte.wordsize. simpl. lia. }
  rewrite B. reflexivity.
Qed.

Lemma V293_write_byte_load : forall M b n,
  n < 256 -> load Tint8 (V293_write_byte M b n) (b, 0%Z) = Some (V293_byteval n).
Proof.
  intros M b n Hn. eapply V293_encoded_byte_load with (permission := true).
  - exact Hn.
  - unfold V293_write_byte. apply map_get_set.
Qed.

Lemma V293_write_byte_other : forall M b n b' offset,
  b <> b' -> get (V293_write_byte M b n) (b', offset) = get M (b', offset).
Proof.
  intros. unfold V293_write_byte. apply map_get_set'. congruence.
Qed.

Lemma V293_write_byte_other_load : forall M b n b' offset,
  b <> b' -> load Tint8 (V293_write_byte M b n) (b', offset) = load Tint8 M (b', offset).
Proof.
  intros. unfold load, loadm. cbn [typelen loadbytes].
  rewrite V293_write_byte_other by assumption. reflexivity.
Qed.

Lemma V293_write_byte_reads : forall M bt bg br lo hi g byblock n,
  byblock <> bt -> byblock <> bg -> byblock <> br ->
  V293_sched_read_memory M bt bg br lo hi g ->
  V293_sched_read_memory (V293_write_byte M byblock n) bt bg br lo hi g.
Proof.
  intros M bt bg br lo hi g byblock n Ht Hg Hr [Mg [Mt [Mr0 Mr1]]].
  unfold V293_sched_read_memory. repeat split.
  - rewrite V293_write_byte_other_load by assumption. exact Mg.
  - intros. rewrite V293_write_byte_other_load by assumption. auto.
  - rewrite V293_write_byte_other_load by assumption. exact Mr0.
  - rewrite V293_write_byte_other_load by assumption. exact Mr1.
Qed.

Lemma V293_cstepstar_trans : forall P C1 m1 C2 m2 C3 m3,
  cstepstar P C1 m1 C2 m2 -> cstepstar P C2 m2 C3 m3 -> cstepstar P C1 m1 C3 m3.
Proof. intros P C1 m1 C2 m2 C3 m3 H12 H23. induction H12; [exact H23 | ]. eapply c_stepstarn; eauto. Qed.

Lemma V293_expr_steps : forall P c ke m c' ke' m' ks,
  estepstar c ke m c' ke' m' -> cstepstar P (c, (ke, ks)) m (c', (ke', ks)) m'.
Proof.
  intros P c ke m c' ke' m' ks H. induction H.
  - apply c_stepstar0.
  - eapply c_stepstarn; [eapply expr_step; [reflexivity | eassumption] | exact IHestepstar].
Qed.

Lemma V293_assign_byte_execution : forall P ge le M M' e1 e2 b v ks,
  evaltype e1 (ge, le, M) = Some Tint8 ->
  evaladdr e1 (ge, le, M) = Some (Vptr (b, Int.zero)) ->
  evaltype e2 (ge, le, M) = Some Tint8 ->
  evalval e2 (ge, le, M) = Some v ->
  store Tint8 M (b, 0%Z) v = Some M' ->
  cstepstar P (curs (sassign e1 e2), (kenil, ks)) (ge, le, M)
    (curs (sskip None), (kenil, ks)) (ge, le, M').
Proof.
  intros P ge le M M' e1 e2 b v ks E1 A1 E2 V2 Store.
  eapply c_stepstarn.
  { eapply stmt_step; [reflexivity | ]. eapply sassign_step; try eassumption.
    apply eq_int. auto. }
  eapply V293_cstepstar_trans.
  { apply V293_expr_steps. apply evalval_imply_estepstar. exact V2. }
  eapply c_stepstarn. { eapply stmt_step; [reflexivity | ]. constructor. }
  eapply V293_cstepstar_trans.
  { apply V293_expr_steps. apply evalval_imply_estepstar.
    eapply evaladdr_val_eq; eassumption. }
  eapply c_stepstarn.
  { eapply stmt_step; [reflexivity | ]. eapply sassignend_step; try reflexivity. exact Store. }
  apply c_stepstar0.
Qed.

(* Uninterleaved concrete execution of the two source assignments. Local
   allocation, void return/free and the interrupt/shared invariant are separate
   obligations: this is intentionally NOT the function's InfRules theorem. *)
Theorem V293_OSSchedNew_updates_execution : forall P ks ge le M unmap group rows high y
    bt bg br bh byblock lo hi g oldy oldhigh,
  V293_sched_read_env ge le unmap group rows bt bg br ->
  V293_sched_read_memory M bt bg br lo hi g ->
  get le y = Some (byblock, Tint8) ->
  get le high = None -> get ge high = Some (bh, Tint8) ->
  get M (byblock, 0%Z) = Some (true, oldy) ->
  get M (bh, 0%Z) = Some (true, oldhigh) ->
  byblock <> bt -> byblock <> bg -> byblock <> br -> byblock <> bh ->
  lo < 256 -> hi < 256 -> g = V293_ready_group lo hi ->
  (exists p, V293_bitmap_ready lo hi p) ->
  cstepstar P
    (curs (V293_OSSchedNew_updates unmap group rows high y), (kenil, ks)) (ge, le, M)
    (curs (sskip None), (kenil, ks))
    (ge, le, V293_write_byte (V293_write_byte M byblock (V293_ready_lookup g))
       bh (V293_ready_select lo hi g)).
Proof.
  intros P ks ge le M unmap group rows high y bt bg br bh byblock lo hi g oldy oldhigh
    He Hm Ey Eh Gh Wy Wh Byt Byg Byr Byh Hlo Hhi Hg Hnonempty.
  assert (Gbound : g < 256).
  { subst g. unfold V293_ready_group. destruct (lo =? 0); destruct (hi =? 0); lia. }
  destruct (V293_OSSchedNew_row_eval ge le M unmap group rows bt bg br lo hi g He Hm Gbound)
    as [Val1 Type1].
  pose proof (V293_write_byte_reads M bt bg br lo hi g byblock (V293_ready_lookup g)
    Byt Byg Byr Hm) as Reads1.
  pose proof (V293_write_byte_load M byblock (V293_ready_lookup g)
    ltac:(pose proof (proj1 (V293_ready_row_spec g Gbound)); lia)) as Yload.
  destruct (V293_OSSchedNew_priority_eval ge le _ unmap group rows y bt bg br byblock lo hi g
    He Reads1 Ey Yload Hlo Hhi Hg Hnonempty) as [Val2 Type2].
  unfold V293_OSSchedNew_updates.
  eapply c_stepstarn. { eapply stmt_step; [reflexivity | ]. constructor. }
  eapply V293_cstepstar_trans.
  { eapply V293_assign_byte_execution; try eassumption.
    - cbn [evaltype]. rewrite Ey. reflexivity.
    - cbn [evaladdr get_lenv]. rewrite Ey. reflexivity.
    - eapply V293_write_byte_store. exact Wy. }
  eapply c_stepstarn. { eapply stmt_step; [reflexivity | ]. constructor. }
  eapply V293_assign_byte_execution; try eassumption.
  - cbn [evaltype]. rewrite Eh, Gh. reflexivity.
  - cbn [evaladdr get_lenv get_genv]. rewrite Eh, Gh. reflexivity.
  - eapply V293_write_byte_store. rewrite V293_write_byte_other by exact Byh. exact Wh.
Qed.

Theorem V293_OSSchedNew_updates_frame : forall M byblock bh lo hi g a,
  a <> (byblock, 0%Z) -> a <> (bh, 0%Z) ->
  get (V293_write_byte (V293_write_byte M byblock (V293_ready_lookup g))
    bh (V293_ready_select lo hi g)) a = get M a.
Proof.
  intros. unfold V293_write_byte. repeat rewrite map_get_set' by congruence. reflexivity.
Qed.

Theorem V293_OSSchedNew_updates_result : forall M byblock bh lo hi g,
  lo < 256 -> hi < 256 -> g = V293_ready_group lo hi ->
  (exists p, V293_bitmap_ready lo hi p) ->
  load Tint8 (V293_write_byte (V293_write_byte M byblock (V293_ready_lookup g))
    bh (V293_ready_select lo hi g)) (bh, 0%Z) = Some (V293_byteval (V293_ready_select lo hi g)) /\
  V293_bitmap_ready lo hi (V293_ready_select lo hi g) /\
  (forall p, V293_bitmap_ready lo hi p -> V293_ready_select lo hi g <= p).
Proof.
  intros M byblock bh lo hi g Hlo Hhi Hg Hnonempty.
  split.
  - apply V293_write_byte_load.
    pose proof (V293_ready_selection_range lo hi g Hlo Hhi Hg Hnonempty). lia.
  - exact (proj2 (V293_ready_selection lo hi g Hlo Hhi Hg Hnonempty)).
Qed.

(* A concrete, bounded memory witness: read-only table/group/rows; writable
   output and local byte. This prevents an inconsistent load-view oracle. *)
Definition V293_idle_raw (a : addr) : option (bool * memval) :=
  let '(b, i) := a in
  if Pos.ltb b 6 then
    if Pos.eqb b 1 then
      if ((0 <=? i) && (i <? 256))%Z then
        Some (false, Byte (Byte.repr (Int.unsigned
          (Int.repr (Z.of_nat (V293_ready_lookup (Z.to_nat i))))))) else None
    else if Z.eqb i 0 then
      if Pos.eqb b 2 then Some (false, Byte (Byte.repr 2))
      else if Pos.eqb b 3 then Some (false, Byte (Byte.repr 0))
      else Some (true, Undef)
    else if (Pos.eqb b 3 && Z.eqb i 1)%bool then Some (false, Byte (Byte.repr 16))
    else None
  else None.

Lemma V293_idle_raw_bounded : HalfPermMap.raw_bounded V293_idle_raw.
Proof.
  exists 6%positive. intros b i v H.
  unfold V293_idle_raw in H. destruct (Pos.ltb b 6) eqn:E; [apply Pos.ltb_lt; exact E | discriminate].
Qed.

Definition V293_idle_memory : mem := @HalfPermMap.mkMap V293_idle_raw V293_idle_raw_bounded.

Theorem V293_OSSchedNew_precondition_witness :
  exists ge le M,
    V293_sched_read_env ge le 100%Z 101%Z 102%Z 1%positive 2%positive 3%positive /\
    V293_sched_read_memory M 1%positive 2%positive 3%positive 0 16 2 /\
    get le 104%Z = Some (5%positive, Tint8) /\
    get le 103%Z = None /\ get ge 103%Z = Some (4%positive, Tint8) /\
    get M (5%positive, 0%Z) = Some (true, Undef) /\
    get M (4%positive, 0%Z) = Some (true, Undef) /\
    2 = V293_ready_group 0 16 /\
    (exists p, V293_bitmap_ready 0 16 p).
Proof.
  exists (set (set (set (set (emp : env) 100%Z (1%positive, Tarray Tint8 256))
    101%Z (2%positive, Tint8)) 102%Z (3%positive, Tarray Tint8 2))
    103%Z (4%positive, Tint8)).
  exists (set (emp : env) 104%Z (5%positive, Tint8)).
  exists V293_idle_memory.
  split; [vm_compute; repeat split; reflexivity | ].
  split.
  - unfold V293_sched_read_memory. split; [vm_compute; reflexivity | ].
    split.
    + intros n Hn. eapply V293_encoded_byte_load with (permission := false).
      * pose proof (proj1 (V293_ready_row_spec n Hn)). lia.
      * change (V293_idle_raw (1%positive, Z.of_nat n) = Some (false, Byte (Byte.repr (Int.unsigned (Int.repr (Z.of_nat (V293_ready_lookup n))))))).
        unfold V293_idle_raw. cbn [Pos.ltb Pos.eqb].
        assert (A : (0 <=? Z.of_nat n)%Z = true) by (apply Z.leb_le; lia).
        assert (B : (Z.of_nat n <? 256)%Z = true) by (apply Z.ltb_lt; lia).
        rewrite A, B, Nat2Z.id. reflexivity.
    + vm_compute. split; reflexivity.
  - repeat split; try reflexivity; try (vm_compute; reflexivity).
    exists 12. right. split; [lia | ]. split; [lia | reflexivity].
Qed.
