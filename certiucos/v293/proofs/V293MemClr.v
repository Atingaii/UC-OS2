(* Actual byte writes and terminating native loop, from raw ownership. *)
Require Import CertiOS.certiucos.v293.code.V293OSMemClr.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope Z_scope.
Fixpoint V293_clr_bytes b off (values : list val) : list V293_record_cell :=
  match values with
  | [] => []
  | v::tail => ((b,off),Tint8,v)::V293_clr_bytes b (off+1) tail
  end.
Definition V293_clr_params bp bs b off n : list V293_record_cell :=
  [((bp,0),Tptr Tint8,Vptr (b,Int.repr off));
   ((bs,0),Tint16,Vint32 (Int.repr (Z.of_nat n)))].
Definition V293_clr_cells bp bs b off values :=
  V293_clr_params bp bs b off (length values) ++ V293_clr_bytes b off values.

Lemma V293_clr_frame_out : forall cells A R,
  V293_rdy_raw_cells cells (A ** R) ==> A ** V293_rdy_raw_cells cells R.
Proof.
  induction cells as [ | [[a tp] v] tail IH];intros A R s H;cbn [V293_rdy_raw_cells] in *.
  - exact H.
  - assert (K : s |= Amapsto a tp true v ** (A ** V293_rdy_raw_cells tail R)).
    { eapply astar_mono;[intros st HS;exact HS | apply IH | exact H]. }
    clear -K. sep auto.
Qed.

Lemma V293_clr_frame_in : forall cells A R,
  A ** V293_rdy_raw_cells cells R ==> V293_rdy_raw_cells cells (A ** R).
Proof.
  induction cells as [ | [[a tp] v] tail IH];intros A R s H;cbn [V293_rdy_raw_cells] in *.
  - exact H.
  - eapply astar_mono;[intros st HS;exact HS | apply IH | ]. clear -H. sep auto.
Qed.

Local Lemma V293_clr_max : Int.max_unsigned=4294967295.
Proof. reflexivity. Qed.
Lemma V293_clr_arithmetic : forall n off,
  0 <= n <= 65535 -> 0 <= off -> off+1 <= Int.max_unsigned ->
  rule_type_val_match Tint16 (Vint32 (Int.repr n))=true /\
  cast_eval (Int.repr n) Tint16 Tint32=Some (Int.repr n) /\
  Int.add (Int.repr off) (Int.mul Int.one (Int.repr (Z.of_nat 1)))=Int.repr (off+1).
Proof.
  intros n off N O Limit. split.
  - cbn [rule_type_val_match]. rewrite Int.unsigned_repr by (rewrite V293_clr_max;lia).
    assert (L : (n <=? Int16.max_unsigned)=true) by (apply Z.leb_le;change (n<=65535);lia).
    rewrite L;reflexivity.
  - split.
    + reflexivity.
    + rewrite Int.mul_one. unfold Int.add. rewrite Int.unsigned_repr by lia.
      rewrite Int.unsigned_one. reflexivity.
Qed.

Ltac V293_clr_eval :=
  cbn [evaltype evalval evaladdr get_lenv get_genv get_mem];
  cbv delta [env var memory.ident Modules.ident] in *;
  repeat first [match goal with H : ?lhs = ?rhs |- _ => progress rewrite H end |
    progress cbn [evaltype evalval evaladdr get_lenv get_genv get_mem bop_type bop_int_type bop_eval is_int_type cast_eval add sub cmp_val cmpu typelen]];
  reflexivity.
Ltac V293_clr_read H n name :=
  lazymatch type of H with
  | (?ge,?le,?M,?ir,?aux,?O,?op) |= V293_rdy_raw_cells ?cells ?R =>
    let cell := eval cbv beta iota zeta delta [nth] in (nth n cells ((1%positive,0%Z),Tint8,Vundef)) in
    lazymatch cell with (?a,?tp,?v) =>
    assert (name : load tp M a=Some v);
    [change (load tp (getmem (ge,le,M,ir,aux,O,op)) a=Some v);
     eapply (V293_rdy_raw_load cells R a tp v (ge,le,M,ir,aux,O,op));
     [cbn;auto 10 | first [reflexivity | lazymatch goal with |- rule_type_val_match Tint16 (Vint32 (Int.repr ?z))=true => exact (proj1 (V293_clr_arithmetic z 0 ltac:(lia) ltac:(lia) ltac:(rewrite V293_clr_max;lia))) end] | exact H] | ]
    end
  end.
Ltac V293_clr_write P H n lhs rhs value next step owned :=
  lazymatch type of H with
  | (?ge,?le,?M,?ir,?aux,?O,?op) |= V293_rdy_raw_cells ?cells ?R =>
    let before := eval cbv beta iota zeta delta [firstn] in (firstn n cells) in
    let cell := eval cbv beta iota zeta delta [nth] in (nth n cells ((1%positive,0%Z),Tint8,Vundef)) in
    let after := eval cbv beta iota zeta delta [skipn] in (skipn (S n) cells) in
    lazymatch cell with (?a,?tp,?old) =>
    let updated := eval cbn [app] in (before++(a,tp,value)::after) in
    let T := fresh "Write" in
    assert (T : exists Mf,
      (forall ks, cstepstar P (curs (sassign lhs rhs),(kenil,ks)) (ge,le,M)
        (curs (sskip None),(kenil,ks)) (ge,le,Mf)) /\
      (ge,le,Mf,ir,aux,O,op) |= V293_rdy_raw_cells updated R);
    [eapply (V293_rdy_assign before a tp old after value lhs rhs tp R P ge le M ir aux O op);
      [V293_clr_eval | V293_clr_eval |
       cbn [snd];apply Int.unsigned_repr;cbn [length] in *;lia | V293_clr_eval |
       first [solve [apply eq_int;auto] | apply eq_vptr;do 2 eexists;split;reflexivity] |
       V293_clr_eval | first [reflexivity | lazymatch goal with |- rule_type_val_match Tint16 (Vint32 (Int.repr ?z))=true => exact (proj1 (V293_clr_arithmetic z 0 ltac:(lia) ltac:(lia) ltac:(rewrite V293_clr_max;lia))) end] |
       exact H] |
     destruct T as (next & step & owned)]
    end
  end.

Theorem V293_OS_MemClr_loop_execution : forall values P ks ge le M ir aux O op R
  dest size bp bs b off,
  get le dest=Some (bp,Tptr Tint8) -> get le size=Some (bs,Tint16) ->
  Z.of_nat (length values)<=65535 -> 0<=off ->
  off+Z.of_nat (length values)<=Int.max_unsigned ->
  (ge,le,M,ir,aux,O,op) |= V293_rdy_raw_cells (V293_clr_cells bp bs b off values) R ->
  exists Mf,
    cstepstar P (curs (V293_clr_loop dest size),(kenil,ks)) (ge,le,M)
      (curs (sskip None),(kenil,ks)) (ge,le,Mf) /\
    (ge,le,Mf,ir,aux,O,op) |= V293_rdy_raw_cells
      (V293_clr_params bp bs b (off+Z.of_nat (length values)) 0 ++
       V293_clr_bytes b off (repeat (Vint32 Int.zero) (length values))) R.
Proof.
  induction values as [ | v tail IH];intros P ks ge le M ir aux O op R dest size bp bs b off
    Dest Size Bound Start Limit Owned.
  - unfold V293_clr_cells,V293_clr_params in Owned;cbn [length V293_clr_bytes app] in Owned.
    V293_clr_read Owned 1%nat ReadSize.
    assert (Guard : evalval (V293_clr_guard size) (ge,le,M)=Some (Vint32 Int.zero)).
    { unfold V293_clr_guard. V293_clr_eval. }
    exists M. split.
    + unfold V293_clr_loop. apply V293_rdy_while_false;exact Guard.
    + cbn [length repeat V293_clr_bytes app]. rewrite Z.add_0_r. exact Owned.
  - assert (N : 0<=Z.of_nat (length tail)<=65534) by (cbn [length] in Bound;lia).
    assert (Inc := proj2 (proj2 (V293_clr_arithmetic 0 off ltac:(lia) Start ltac:(cbn [length] in Limit;lia)))).
    assert (Dec : Int.modu (Int.sub (Int.repr (Z.of_nat (S (length tail)))) Int.one)
       (Int.repr Int16.modulus)=Int.repr (Z.of_nat (length tail))).
    { unfold Int.sub. rewrite Int.unsigned_repr by (rewrite V293_clr_max;lia).
      rewrite Int.unsigned_one. replace (Z.of_nat (S (length tail))-1) with (Z.of_nat (length tail)) by lia.
      unfold Int.modu. rewrite Int.unsigned_repr by (rewrite V293_clr_max;lia).
      change (Int.repr (Z.of_nat (length tail) mod 65536)=Int.repr (Z.of_nat (length tail))).
      rewrite Z.mod_small by lia. reflexivity. }
    assert (Positive : Int.ltu Int.zero (Int.repr (Z.of_nat (S (length tail))))=true).
    { unfold Int.ltu. rewrite Int.unsigned_zero,Int.unsigned_repr by (rewrite V293_clr_max;lia).
      destruct (zlt 0 (Z.of_nat (S (length tail))));[reflexivity | lia]. }
    unfold V293_clr_cells,V293_clr_params in Owned;cbn [length V293_clr_bytes app] in Owned.
    V293_clr_read Owned 0%nat ReadDest.
    V293_clr_read Owned 1%nat ReadSize.
    assert (Guard : evalval (V293_clr_guard size) (ge,le,M)=Some (Vint32 Int.one)).
    { unfold V293_clr_guard. V293_clr_eval. }
    V293_clr_write P Owned 2%nat (ederef (evar dest)) (ecast (econst32 Int.zero) Tint8)
      (Vint32 Int.zero) M1 StoreByte H1.
    V293_clr_read H1 0%nat ReadDest1.
    V293_clr_write P H1 0%nat (evar dest) (ebinop oplus (evar dest) (econst32 Int.one))
      (Vptr (b,Int.repr (off+1))) M2 Advance H2.
    V293_clr_read H2 1%nat ReadSize2.
    V293_clr_write P H2 1%nat (evar size)
      (ecast (ebinop ominus (ecast (evar size) Tint32) (econst32 Int.one)) Tint16)
      (Vint32 (Int.repr (Z.of_nat (length tail)))) M3 Decrement H3.
    assert (Next : (ge,le,M3,ir,aux,O,op) |= V293_rdy_raw_cells
      (V293_clr_cells bp bs b (off+1) tail) (Amapsto (b,off) Tint8 true (Vint32 Int.zero) ** R)).
    { apply V293_clr_frame_in. eapply (V293_rdy_cell_out
        (V293_clr_params bp bs b (off+1) (length tail)) (b,off) Tint8 (Vint32 Int.zero)
        (V293_clr_bytes b (off+1) tail) R). exact H3. }
    destruct (IH P ks ge le M3 ir aux O op
      (Amapsto (b,off) Tint8 true (Vint32 Int.zero) ** R) dest size bp bs b (off+1)
      Dest Size ltac:(lia) ltac:(lia) ltac:(cbn [length] in Limit;lia) Next) as (Mf & Rest & Final).
    exists Mf. split.
    + unfold V293_clr_loop. eapply V293_rdy_while_true;[exact Guard | | exact Rest].
      intro cont. unfold V293_clr_iteration,V293_clr_advance.
      eapply V293_rekey_sequence_execution;[exact StoreByte | ].
      eapply V293_rekey_sequence_execution;[exact Advance | apply Decrement].
    + cbn [length repeat V293_clr_bytes].
      replace (off+Z.of_nat (S (length tail))) with (off+1+Z.of_nat (length tail)) by lia.
      apply V293_rdy_cell_in. apply V293_clr_frame_out in Final. exact Final.
Qed.
Print Assumptions V293_OS_MemClr_loop_execution.

(* The empty range does not dereference, or even load, dest. *)
Theorem V293_OS_MemClr_zero_size : forall P ks ge le M ir aux O op R dest size bs,
  get le size=Some (bs,Tint16) ->
  (ge,le,M,ir,aux,O,op) |= Amapsto (bs,0) Tint16 true (Vint32 Int.zero) ** R ->
  cstepstar P (curs (V293_clr_loop dest size),(kenil,ks)) (ge,le,M)
    (curs (sskip None),(kenil,ks)) (ge,le,M).
Proof.
  intros P ks ge le M ir aux O op R dest size bs Size Owned.
  assert (ReadSize : load Tint16 M (bs,0)=Some (Vint32 Int.zero)).
  { change (load Tint16 (getmem (ge,le,M,ir,aux,O,op)) (bs,0)=Some (Vint32 Int.zero)).
    eapply (V293_rdy_raw_load (cons ((bs,0),Tint16,Vint32 Int.zero) nil) R);
      [left;reflexivity | reflexivity | exact Owned]. }
  unfold V293_clr_loop. apply V293_rdy_while_false.
  unfold V293_clr_guard. V293_clr_eval.
Qed.
Print Assumptions V293_OS_MemClr_zero_size.
