Require Import Coq.Arith.Arith Coq.Lists.List Lia.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Local Open Scope nat_scope.

Definition V293_byteval (n : nat) : val := Vint32 (Int.repr (Z.of_nat n)).

(* These are concrete environment/load equations, not assumptions about the
   value of the composite expression that is being verified. No writable
   permission, interrupt invariant or Hoare conclusion is claimed here. *)
Definition V293_sched_read_env (ge le : env) (unmap group rows : var)
    (bt bg br : block) : Prop :=
  get le unmap = None /\ get le group = None /\ get le rows = None /\
  get ge unmap = Some (bt, Tarray Tint8 256) /\
  get ge group = Some (bg, Tint8) /\ get ge rows = Some (br, Tarray Tint8 2).

Definition V293_sched_read_memory (M : mem) (bt bg br : block)
    (lo hi group : nat) : Prop :=
  load Tint8 M (bg, 0%Z) = Some (V293_byteval group) /\
  (forall n, n < 256 -> load Tint8 M (bt, Z.of_nat n) =
    Some (V293_byteval (V293_ready_lookup n))) /\
  load Tint8 M (br, 0%Z) = Some (V293_byteval lo) /\
  load Tint8 M (br, 1%Z) = Some (V293_byteval hi).

Lemma V293_eval_byte_array : forall ge le M base index b count n v,
  evaltype base (ge, le, M) = Some (Tarray Tint8 count) ->
  evalval base (ge, le, M) = Some (Vptr (b, Int.zero)) ->
  evaltype index (ge, le, M) = Some Tint8 ->
  evalval index (ge, le, M) = Some (V293_byteval n) ->
  n < count -> count <= 256 ->
  load Tint8 M (b, Z.of_nat n) = Some v ->
  evalval (earrayelem base index) (ge, le, M) = Some v /\
  evaltype (earrayelem base index) (ge, le, M) = Some Tint8.
Proof.
  intros ge le M base index b count n v Hb Hbv Hi Hiv Hn Hcount Hv.
  cbn [evaltype evalval]. rewrite Hb, Hi, Hbv, Hiv.
  unfold V293_byteval. simpl typelen.
  rewrite (Int.mul_commut Int.one), Int.mul_one, Int.add_zero_l, Int.unsigned_repr.
  - auto.
  - unfold Int.max_unsigned, Int.modulus, Int.wordsize. simpl. lia.
Qed.

Theorem V293_OSSchedNew_row_eval : forall ge le M unmap group rows bt bg br lo hi g,
  V293_sched_read_env ge le unmap group rows bt bg br ->
  V293_sched_read_memory M bt bg br lo hi g -> g < 256 ->
  evalval (V293_OSSchedNew_row_expr unmap group) (ge, le, M) =
    Some (V293_byteval (V293_ready_lookup g)) /\
  evaltype (V293_OSSchedNew_row_expr unmap group) (ge, le, M) = Some Tint8.
Proof.
  intros ge le M unmap group rows bt bg br lo hi g He Hm Hg.
  destruct He as [Et [Eg [Er [Gt [Gg Gr]]]]].
  destruct Hm as [Mg [Mt [Mr0 Mr1]]].
  unfold V293_OSSchedNew_row_expr.
  eapply V293_eval_byte_array with (count := 256) (n := g) (b := bt);
    try assumption; try lia.
  - cbn [evaltype]. rewrite Et, Gt. reflexivity.
  - cbn [evaltype evalval get_lenv get_genv get_mem]. rewrite Et, Gt. reflexivity.
  - cbn [evaltype]. rewrite Eg, Gg. reflexivity.
  - cbn [evaltype evalval get_lenv get_genv get_mem]. rewrite Eg, Gg. exact Mg.
  - apply Mt. exact Hg.
Qed.

Lemma V293_shift_add_narrow : forall y bit,
  y < 2 -> bit < 8 ->
  Int.modu (Int.add (Int.shl (Int.repr (Z.of_nat y)) (Int.repr 3))
    (Int.repr (Z.of_nat bit))) (Int.repr Byte.modulus) =
  Int.repr (Z.of_nat (8 * y + bit)).
Proof.
  intros y bit Hy Hb.
  rewrite Int.shl_mul_two_p.
  change (Int.modu (Int.add (Int.mul (Int.repr (Z.of_nat y)) (Int.repr 8))
    (Int.repr (Z.of_nat bit))) (Int.repr 256) = Int.repr (Z.of_nat (8 * y + bit))).
  unfold Int.mul, Int.add, Int.modu.
  rewrite (Int.unsigned_repr (Z.of_nat y)), (Int.unsigned_repr 8),
    (Int.unsigned_repr (Z.of_nat bit)), (Int.unsigned_repr 256) by
    (unfold Int.max_unsigned, Int.modulus, Int.wordsize; simpl; lia).
  rewrite (Int.unsigned_repr (Z.of_nat y * 8)) by
    (unfold Int.max_unsigned, Int.modulus, Int.wordsize; simpl; lia).
  rewrite Int.unsigned_repr by
    (unfold Int.max_unsigned, Int.modulus, Int.wordsize; simpl; lia).
  rewrite Z.mod_small by lia.
  f_equal. rewrite Nat2Z.inj_add, Nat2Z.inj_mul. change 8%Z with (Z.of_nat 8). ring.
Qed.

Lemma V293_promoted_priority_eval : forall ge le M ye be yn bn,
  evaltype ye (ge, le, M) = Some Tint8 ->
  evalval ye (ge, le, M) = Some (V293_byteval yn) ->
  evaltype be (ge, le, M) = Some Tint8 ->
  evalval be (ge, le, M) = Some (V293_byteval bn) ->
  yn < 2 -> bn < 8 ->
  evalval (ecast (ebinop oplus
    (ebinop olshift (ecast ye Tint32) (econst32 (Int.repr 3)))
    (ecast be Tint32)) Tint8) (ge, le, M) = Some (V293_byteval (8 * yn + bn)) /\
  evaltype (ecast (ebinop oplus
    (ebinop olshift (ecast ye Tint32) (econst32 (Int.repr 3)))
    (ecast be Tint32)) Tint8) (ge, le, M) = Some Tint8.
Proof.
  intros ge le M ye be yn bn Yt Yv Bt Bv Hy Hb.
  cbn [evaltype evalval]. rewrite Yt, Bt, Yv, Bv.
  unfold V293_byteval.
  cbn [bop_type bop_int_type bop_eval shl add is_int_type cast_eval].
  split; [ | reflexivity].
  assert (ShiftOK : Int.ltu (Int.repr 3) Int.iwordsize = true) by reflexivity.
  rewrite ShiftOK. cbn [add].
  rewrite V293_shift_add_narrow; auto.
Qed.

Theorem V293_OSSchedNew_priority_eval : forall ge le M unmap group rows y bt bg br byblock lo hi g,
  V293_sched_read_env ge le unmap group rows bt bg br ->
  V293_sched_read_memory M bt bg br lo hi g ->
  get le y = Some (byblock, Tint8) ->
  load Tint8 M (byblock, 0%Z) = Some (V293_byteval (V293_ready_lookup g)) ->
  lo < 256 -> hi < 256 -> g = V293_ready_group lo hi ->
  (exists p, V293_bitmap_ready lo hi p) ->
  evalval (V293_OSSchedNew_priority_expr unmap rows y) (ge, le, M) =
    Some (V293_byteval (V293_ready_select lo hi g)) /\
  evaltype (V293_OSSchedNew_priority_expr unmap rows y) (ge, le, M) = Some Tint8.
Proof.
  intros ge le M unmap group rows y bt bg br byblock lo hi g He Hm Ey My Hlo Hhi Hg Hnonempty.
  pose proof (V293_ready_selection lo hi g Hlo Hhi Hg Hnonempty) as [Ybound _].
  destruct He as [Et [Eg [Er [Gt [Gg Gr]]]]].
  destruct Hm as [Mg [Mt [Mr0 Mr1]]].
  assert (Yt : evaltype (evar y) (ge, le, M) = Some Tint8).
  { cbn [evaltype]. rewrite Ey. reflexivity. }
  assert (Yv : evalval (evar y) (ge, le, M) = Some (V293_byteval (V293_ready_lookup g))).
  { cbn [evaltype evalval get_lenv get_genv get_mem]. rewrite Ey. exact My. }
  assert (Rt : evaltype (evar rows) (ge, le, M) = Some (Tarray Tint8 2)).
  { cbn [evaltype]. rewrite Er, Gr. reflexivity. }
  assert (RowsValue : evalval (evar rows) (ge, le, M) = Some (Vptr (br, Int.zero))).
  { cbn [evaltype evalval get_lenv get_genv get_mem]. rewrite Er, Gr. reflexivity. }
  assert (Rowv : load Tint8 M (br, Z.of_nat (V293_ready_lookup g)) =
    Some (V293_byteval (V293_ready_row lo hi (V293_ready_lookup g)))).
  { destruct (V293_ready_lookup g) as [ | k] eqn:E; [exact Mr0 | ].
    assert (k = 0) by lia. subst k. exact Mr1. }
  destruct (V293_eval_byte_array ge le M (evar rows) (evar y) br 2
    (V293_ready_lookup g) _ Rt RowsValue Yt Yv Ybound ltac:(lia) Rowv) as [Rowval Rowtype].
  assert (Rowbound : V293_ready_row lo hi (V293_ready_lookup g) < 256).
  { unfold V293_ready_row. destruct (V293_ready_lookup g =? 0); assumption. }
  assert (Tt : evaltype (evar unmap) (ge, le, M) = Some (Tarray Tint8 256)).
  { cbn [evaltype]. rewrite Et, Gt. reflexivity. }
  assert (Tv : evalval (evar unmap) (ge, le, M) = Some (Vptr (bt, Int.zero))).
  { cbn [evaltype evalval get_lenv get_genv get_mem]. rewrite Et, Gt. reflexivity. }
  destruct (V293_eval_byte_array ge le M (evar unmap) (earrayelem (evar rows) (evar y))
    bt 256 (V293_ready_row lo hi (V293_ready_lookup g)) _ Tt Tv Rowtype Rowval
    Rowbound ltac:(lia) (Mt _ Rowbound)) as [Bitval Bittype].
  unfold V293_OSSchedNew_priority_expr, V293_ready_select.
  eapply V293_promoted_priority_eval; try eassumption.
  apply (proj1 (V293_ready_row_spec _ Rowbound)).
Qed.
