(* Actual writable stores to a configured TCB, not an assumed task creation.
   Existential sequential execution only. Entry has arbitrary old field values;
   pointer/parameter cells and an arbitrary separating frame survive all stores. *)
Require Import CertiOS.certiucos.v293.code.V293OSTCBInit.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.
Definition V293_tcb_init_input_cells bc bp bs bb bi bz be bo bt base p top bottom identity size ext options : list V293_record_cell :=
  [((bc,0%Z),(Tptr V293_tcb_type),(Vptr (bt,Int.repr base)));
   ((bp,0%Z),(Tint8),(V293_byteval p));
   ((bs,0%Z),(Tptr Tint32),(top));
   ((bb,0%Z),(Tptr Tint32),(bottom));
   ((bi,0%Z),(Tint16),(identity));
   ((bz,0%Z),(Tint32),(size));
   ((be,0%Z),(Tptr Tvoid),(ext));
   ((bo,0%Z),(Tint16),(options))].
Definition V293_tcb_init_old_fields bt base (old : Z -> val) : list V293_record_cell :=
  [((bt,(base+0)%Z),(Tptr Tint32),old 0%Z);
   ((bt,(base+50)%Z),(Tint8),old 50%Z);
   ((bt,(base+48)%Z),(Tint8),old 48%Z);
   ((bt,(base+49)%Z),(Tint8),old 49%Z);
   ((bt,(base+44)%Z),(Tint32),old 44%Z);
   ((bt,(base+4)%Z),(Tptr Tvoid),old 4%Z);
   ((bt,(base+12)%Z),(Tint32),old 12%Z);
   ((bt,(base+8)%Z),(Tptr Tint32),old 8%Z);
   ((bt,(base+16)%Z),(Tint16),old 16%Z);
   ((bt,(base+18)%Z),(Tint16),old 18%Z);
   ((bt,(base+55)%Z),(Tint8),old 55%Z);
   ((bt,(base+52)%Z),(Tint8),old 52%Z);
   ((bt,(base+51)%Z),(Tint8),old 51%Z);
   ((bt,(base+54)%Z),(Tint8),old 54%Z);
   ((bt,(base+53)%Z),(Tint8),old 53%Z);
   ((bt,(base+28)%Z),(Tcom_ptr 411%Z),old 28%Z);
   ((bt,(base+36)%Z),(Tcom_ptr 412%Z),old 36%Z);
   ((bt,(base+32)%Z),(Tptr Tvoid),old 32%Z)].
Definition V293_tcb_init_final_fields bt base p top bottom identity size ext options : list V293_record_cell :=
  [((bt,(base+0)%Z),(Tptr Tint32),(top));
   ((bt,(base+50)%Z),(Tint8),(V293_byteval p));
   ((bt,(base+48)%Z),(Tint8),(Vint32 Int.zero));
   ((bt,(base+49)%Z),(Tint8),(Vint32 Int.zero));
   ((bt,(base+44)%Z),(Tint32),(Vint32 Int.zero));
   ((bt,(base+4)%Z),(Tptr Tvoid),(ext));
   ((bt,(base+12)%Z),(Tint32),(size));
   ((bt,(base+8)%Z),(Tptr Tint32),(bottom));
   ((bt,(base+16)%Z),(Tint16),(options));
   ((bt,(base+18)%Z),(Tint16),(identity));
   ((bt,(base+55)%Z),(Tint8),(Vint32 Int.zero));
   ((bt,(base+52)%Z),(Tint8),(V293_byteval (V293_prio_row p)));
   ((bt,(base+51)%Z),(Tint8),(V293_byteval (V293_prio_bit p)));
   ((bt,(base+54)%Z),(Tint8),(V293_byteval (2 ^ V293_prio_row p)));
   ((bt,(base+53)%Z),(Tint8),(V293_byteval (2 ^ V293_prio_bit p)));
   ((bt,(base+28)%Z),(Tcom_ptr 411%Z),(Vnull));
   ((bt,(base+36)%Z),(Tcom_ptr 412%Z),(Vnull));
   ((bt,(base+32)%Z),(Tptr Tvoid),(Vnull))].
Definition V293_tcb_init_env le ptcb prio ptos pbos id stk_size pext opt bc bp bs bb bi bz be bo :=
  get le ptcb=Some (bc,(Tptr V293_tcb_type)) /\
  get le prio=Some (bp,(Tint8)) /\
  get le ptos=Some (bs,(Tptr Tint32)) /\
  get le pbos=Some (bb,(Tptr Tint32)) /\
  get le id=Some (bi,(Tint16)) /\
  get le stk_size=Some (bz,(Tint32)) /\
  get le pext=Some (be,(Tptr Tvoid)) /\
  get le opt=Some (bo,(Tint16)).
Definition V293_tcb_init_values_valid top bottom identity size ext options :=
  rule_type_val_match (Tptr Tint32) top=true /\
  rule_type_val_match (Tptr Tint32) bottom=true /\
  rule_type_val_match Tint16 identity=true /\
  rule_type_val_match Tint32 size=true /\
  rule_type_val_match (Tptr Tvoid) ext=true /\
  rule_type_val_match Tint16 options=true.

Lemma V293_tcb_init_field_address : forall ge le M ptcb bc bt base tag delta tp,
  get le ptcb=Some (bc,Tptr V293_tcb_type) ->
  load (Tptr V293_tcb_type) M (bc,0%Z)=Some (Vptr (bt,Int.repr base)) ->
  ftype tag V293_tcb_fields=Some tp ->
  field_offset tag V293_tcb_fields=Some (Int.repr delta) ->
  (0<=base)%Z -> (0<=delta)%Z -> (base+delta<=Int.max_unsigned)%Z ->
  evaltype (efield (ederef (evar ptcb)) tag) (ge,le,M)=Some tp /\
  evaladdr (efield (ederef (evar ptcb)) tag) (ge,le,M)=Some (Vptr (bt,Int.repr (base+delta))).
Proof.
  intros ge le M ptcb bc bt base tag delta tp Bind Pointer Ft Fo B D Bound.
  assert (Td : evaltype (ederef (evar ptcb)) (ge,le,M)=Some V293_tcb_type).
  { cbn [evaltype get_lenv get_genv]. rewrite Bind. reflexivity. }
  split.
  - cbn [evaltype get_lenv get_genv]. rewrite Bind. exact Ft.
  - cbn [evaladdr evalval evaltype get_lenv get_genv get_mem]. rewrite Bind.
    cbn beta iota. rewrite Pointer. unfold getoff. rewrite Td.
    cbn [V293_tcb_type]. rewrite Fo. rewrite Int.repr_unsigned. unfold Int.add.
    rewrite !Int.unsigned_repr by lia. reflexivity.
Qed.
Lemma V293_tcb_init_mask_eval : forall ge le M (coord : expr) n,
  n<8 -> evaltype coord (ge,le,M)=Some Tint8 ->
  evalval coord (ge,le,M)=Some (V293_byteval n) ->
  evaltype (ecast (ebinop olshift (econst32 Int.one) (ecast coord Tint32)) Tint8) (ge,le,M)=Some Tint8 /\
  evalval (ecast (ebinop olshift (econst32 Int.one) (ecast coord Tint32)) Tint8) (ge,le,M)=Some (V293_byteval (2^n)).
Proof.
  intros ge le M coord n Range Ty Read. cbn [evaltype evalval]. rewrite Ty,Read.
  cbn [cast_eval bop_type bop_int_type bop_eval shl].
  do 8 (destruct n as [ | n]; [vm_compute;split;reflexivity | ]). lia.
Qed.
Lemma V293_tcb_init_byte_valid : forall p,
  p<13 -> rule_type_val_match Tint8 (V293_byteval p)=true /\
  rule_type_val_match Tint8 (V293_byteval (V293_prio_row p))=true /\
  rule_type_val_match Tint8 (V293_byteval (V293_prio_bit p))=true /\
  rule_type_val_match Tint8 (V293_byteval (2^V293_prio_row p))=true /\
  rule_type_val_match Tint8 (V293_byteval (2^V293_prio_bit p))=true.
Proof. intros p Range. do 13 (destruct p as [ | p]; [vm_compute;repeat split;reflexivity | ]). lia. Qed.
Ltac V293_tcb_init_read H n name :=
  lazymatch type of H with
  | (?ge,?le,?M,?ir,?aux,?O,?op) |= V293_rdy_raw_cells ?cells ?R =>
    let cell := eval cbn in (nth n cells ((1%positive,0%Z),Tint8,Vundef)) in

    lazymatch cell with (?a,?tp,?v) =>
      assert (name : load tp M a=Some v);
      [change (load tp (getmem (ge,le,M,ir,aux,O,op)) a=Some v);
       eapply (V293_rdy_raw_load cells R a tp v (ge,le,M,ir,aux,O,op));
       [let rec member k := lazymatch k with Datatypes.O => left;reflexivity | Datatypes.S ?rest => right;member rest end in let nn := eval cbv in n in member nn | first [assumption | reflexivity] | exact H] | ]
    end
  end.


Ltac V293_tcb_init_write P H n lhs rhs rt value next step owned :=
  lazymatch type of H with
  | (?ge,?le,?M,?ir,?aux,?O,?op) |= V293_rdy_raw_cells ?cells ?R =>
    let before := eval cbn in (firstn n cells) in
    let cell := eval cbn in (nth n cells ((1%positive,0%Z),Tint8,Vundef)) in
    let after := eval cbn in (skipn (S n) cells) in
    lazymatch cell with (?a,?tp,?old) =>
      let updated := eval cbn [app] in (before++(a,tp,value)::after) in
      let T := fresh "Write" in
      assert (T : exists Mf,
        (forall tail, cstepstar P (curs (sassign lhs rhs),(kenil,tail)) (ge,le,M)
          (curs (sskip None),(kenil,tail)) (ge,le,Mf)) /\
        (ge,le,Mf,ir,aux,O,op) |= V293_rdy_raw_cells updated R);
      [eapply (V293_rdy_assign before a tp old after value lhs rhs rt R P ge le M ir aux O op);
       [assumption | assumption | cbn [snd];apply Int.unsigned_repr;lia |
        first [assumption | V293_rdy_eval] |
        first [solve [apply eq_int;auto] | solve [apply eq_vptr;do 2 eexists;split;reflexivity] |
          solve [apply eq_tnull;first [left;eexists;reflexivity | right;left;eexists;reflexivity | right;right;reflexivity]]] |
        first [assumption | V293_rdy_eval] | first [assumption | reflexivity] | exact H] |
       destruct T as (next & step & owned)]
    end
  end.

Theorem V293_OS_TCBInit_fields_execution : forall P ks ge le M ir aux O op R
  ptcb prio ptos pbos id stk_size pext opt bc bp bs bb bi bz be bo bt base
  p top bottom identity size ext options old,
  p<13 -> (0<=base)%Z -> (base+55<=Int.max_unsigned)%Z ->
  V293_tcb_init_env le ptcb prio ptos pbos id stk_size pext opt bc bp bs bb bi bz be bo ->
  V293_tcb_init_values_valid top bottom identity size ext options ->
  (ge,le,M,ir,aux,O,op) |= V293_rdy_raw_cells
    (V293_tcb_init_old_fields bt base old ++
     V293_tcb_init_input_cells bc bp bs bb bi bz be bo bt base p top bottom identity size ext options) R ->
  exists Mf,
    cstepstar P (curs (V293_TCBInit_fields ptcb prio ptos pbos id stk_size pext opt),(kenil,ks)) (ge,le,M)
      (curs (sskip None),(kenil,ks)) (ge,le,Mf) /\
    (ge,le,Mf,ir,aux,O,op) |= V293_rdy_raw_cells
      (V293_tcb_init_final_fields bt base p top bottom identity size ext options ++
       V293_tcb_init_input_cells bc bp bs bb bi bz be bo bt base p top bottom identity size ext options) R.
Proof.
  intros P ks ge le M ir aux O op R ptcb prio ptos pbos id stk_size pext opt
    bc bp bs bb bi bz be bo bt base p top bottom identity size ext options old
    Range Base Bound Env Valid Owned.
  destruct Env as (Bc & Bp & Bs & Bb & Bi & Bz & Be & Bo).
  destruct Valid as (Vs & Vb & Vi & Vz & Ve & Vo).
  destruct (V293_tcb_init_byte_valid p Range) as (Vp & Vy & Vx & Vby & Vbx).
  destruct (V293_prio_coordinates p Range) as [Yrange Xrange].
  unfold V293_tcb_init_old_fields,V293_tcb_init_input_cells in Owned.
  cbn [app] in Owned.
  V293_tcb_init_read Owned 18 Ptr0.
  destruct (V293_tcb_init_field_address ge le M ptcb bc bt base 1%Z 0%Z (Tptr Tint32) Bc Ptr0 ltac:(reflexivity) ltac:(reflexivity) Base ltac:(lia) ltac:(lia)) as [Ty0 Addr0].
  V293_tcb_init_read Owned 20 Rhs0.
  V293_tcb_init_write P Owned 0 (efield (ederef (evar ptcb)) 1%Z) (evar ptos) (Tptr Tint32) (top) M1 S1 H1.
  V293_tcb_init_read H1 18 Ptr1.
  destruct (V293_tcb_init_field_address ge le M1 ptcb bc bt base 16%Z 50%Z (Tint8) Bc Ptr1 ltac:(reflexivity) ltac:(reflexivity) Base ltac:(lia) ltac:(lia)) as [Ty1 Addr1].
  V293_tcb_init_read H1 19 Rhs1.
  V293_tcb_init_write P H1 1 (efield (ederef (evar ptcb)) 16%Z) (evar prio) (Tint8) (V293_byteval p) M2 S2 H2.
  V293_tcb_init_read H2 18 Ptr2.
  destruct (V293_tcb_init_field_address ge le M2 ptcb bc bt base 14%Z 48%Z (Tint8) Bc Ptr2 ltac:(reflexivity) ltac:(reflexivity) Base ltac:(lia) ltac:(lia)) as [Ty2 Addr2].
  V293_tcb_init_write P H2 2 (efield (ederef (evar ptcb)) 14%Z) (ecast (econst32 Int.zero) Tint8) (Tint8) (Vint32 Int.zero) M3 S3 H3.
  V293_tcb_init_read H3 18 Ptr3.
  destruct (V293_tcb_init_field_address ge le M3 ptcb bc bt base 15%Z 49%Z (Tint8) Bc Ptr3 ltac:(reflexivity) ltac:(reflexivity) Base ltac:(lia) ltac:(lia)) as [Ty3 Addr3].
  V293_tcb_init_write P H3 3 (efield (ederef (evar ptcb)) 15%Z) (ecast (econst32 Int.zero) Tint8) (Tint8) (Vint32 Int.zero) M4 S4 H4.
  V293_tcb_init_read H4 18 Ptr4.
  destruct (V293_tcb_init_field_address ge le M4 ptcb bc bt base 13%Z 44%Z (Tint32) Bc Ptr4 ltac:(reflexivity) ltac:(reflexivity) Base ltac:(lia) ltac:(lia)) as [Ty4 Addr4].
  V293_tcb_init_write P H4 4 (efield (ederef (evar ptcb)) 13%Z) (econst32 Int.zero) (Tint32) (Vint32 Int.zero) M5 S5 H5.
  V293_tcb_init_read H5 18 Ptr5.
  destruct (V293_tcb_init_field_address ge le M5 ptcb bc bt base 2%Z 4%Z (Tptr Tvoid) Bc Ptr5 ltac:(reflexivity) ltac:(reflexivity) Base ltac:(lia) ltac:(lia)) as [Ty5 Addr5].
  V293_tcb_init_read H5 24 Rhs5.
  V293_tcb_init_write P H5 5 (efield (ederef (evar ptcb)) 2%Z) (evar pext) (Tptr Tvoid) (ext) M6 S6 H6.
  V293_tcb_init_read H6 18 Ptr6.
  destruct (V293_tcb_init_field_address ge le M6 ptcb bc bt base 4%Z 12%Z (Tint32) Bc Ptr6 ltac:(reflexivity) ltac:(reflexivity) Base ltac:(lia) ltac:(lia)) as [Ty6 Addr6].
  V293_tcb_init_read H6 23 Rhs6.
  V293_tcb_init_write P H6 6 (efield (ederef (evar ptcb)) 4%Z) (evar stk_size) (Tint32) (size) M7 S7 H7.
  V293_tcb_init_read H7 18 Ptr7.
  destruct (V293_tcb_init_field_address ge le M7 ptcb bc bt base 3%Z 8%Z (Tptr Tint32) Bc Ptr7 ltac:(reflexivity) ltac:(reflexivity) Base ltac:(lia) ltac:(lia)) as [Ty7 Addr7].
  V293_tcb_init_read H7 21 Rhs7.
  V293_tcb_init_write P H7 7 (efield (ederef (evar ptcb)) 3%Z) (evar pbos) (Tptr Tint32) (bottom) M8 S8 H8.
  V293_tcb_init_read H8 18 Ptr8.
  destruct (V293_tcb_init_field_address ge le M8 ptcb bc bt base 5%Z 16%Z (Tint16) Bc Ptr8 ltac:(reflexivity) ltac:(reflexivity) Base ltac:(lia) ltac:(lia)) as [Ty8 Addr8].
  V293_tcb_init_read H8 25 Rhs8.
  V293_tcb_init_write P H8 8 (efield (ederef (evar ptcb)) 5%Z) (evar opt) (Tint16) (options) M9 S9 H9.
  V293_tcb_init_read H9 18 Ptr9.
  destruct (V293_tcb_init_field_address ge le M9 ptcb bc bt base 6%Z 18%Z (Tint16) Bc Ptr9 ltac:(reflexivity) ltac:(reflexivity) Base ltac:(lia) ltac:(lia)) as [Ty9 Addr9].
  V293_tcb_init_read H9 22 Rhs9.
  V293_tcb_init_write P H9 9 (efield (ederef (evar ptcb)) 6%Z) (evar id) (Tint16) (identity) M10 S10 H10.
  V293_tcb_init_read H10 18 Ptr10.
  destruct (V293_tcb_init_field_address ge le M10 ptcb bc bt base 21%Z 55%Z (Tint8) Bc Ptr10 ltac:(reflexivity) ltac:(reflexivity) Base ltac:(lia) ltac:(lia)) as [Ty10 Addr10].
  V293_tcb_init_write P H10 10 (efield (ederef (evar ptcb)) 21%Z) (ecast (econst32 Int.zero) Tint8) (Tint8) (Vint32 Int.zero) M11 S11 H11.
  V293_tcb_init_read H11 18 Ptr11.
  destruct (V293_tcb_init_field_address ge le M11 ptcb bc bt base 18%Z 52%Z (Tint8) Bc Ptr11 ltac:(reflexivity) ltac:(reflexivity) Base ltac:(lia) ltac:(lia)) as [Ty11 Addr11].
  V293_tcb_init_read H11 19 Rhs11.
  destruct (V293_coordinate_rhs_eval ge le M11 prio bp p Range Bp Rhs11) as (YT11 & XT11 & YV11 & XV11).
  V293_tcb_init_write P H11 11 (efield (ederef (evar ptcb)) 18%Z) (V293_task_prio_y_expr prio) (Tint8) (V293_byteval (V293_prio_row p)) M12 S12 H12.
  V293_tcb_init_read H12 18 Ptr12.
  destruct (V293_tcb_init_field_address ge le M12 ptcb bc bt base 17%Z 51%Z (Tint8) Bc Ptr12 ltac:(reflexivity) ltac:(reflexivity) Base ltac:(lia) ltac:(lia)) as [Ty12 Addr12].
  V293_tcb_init_read H12 19 Rhs12.
  destruct (V293_coordinate_rhs_eval ge le M12 prio bp p Range Bp Rhs12) as (YT12 & XT12 & YV12 & XV12).
  V293_tcb_init_write P H12 12 (efield (ederef (evar ptcb)) 17%Z) (V293_task_prio_x_expr prio) (Tint8) (V293_byteval (V293_prio_bit p)) M13 S13 H13.
  V293_tcb_init_read H13 18 Ptr13.
  destruct (V293_tcb_init_field_address ge le M13 ptcb bc bt base 20%Z 54%Z (Tint8) Bc Ptr13 ltac:(reflexivity) ltac:(reflexivity) Base ltac:(lia) ltac:(lia)) as [Ty13 Addr13].
  V293_tcb_init_read H13 11 Coord13.
  destruct (V293_tcb_init_field_address ge le M13 ptcb bc bt base 18%Z 52%Z Tint8 Bc Ptr13 ltac:(reflexivity) ltac:(reflexivity) Base ltac:(lia) ltac:(lia)) as [CT13 CA13].
  assert (CV13 : evalval (efield (ederef (evar ptcb)) 18%Z) (ge,le,M13)=Some (V293_byteval (V293_prio_row p))).
  { exact (proj2 (V293_tcb_byte_field_eval ge le M13 ptcb bc bt base 18%Z 52%Z _ Bc Ptr13 ltac:(reflexivity) ltac:(reflexivity) Base ltac:(lia) ltac:(lia) Coord13)). }
  destruct (V293_tcb_init_mask_eval ge le M13 (efield (ederef (evar ptcb)) 18%Z) (V293_prio_row p) ltac:(lia) CT13 CV13) as [MT13 MV13].
  V293_tcb_init_write P H13 13 (efield (ederef (evar ptcb)) 20%Z) (V293_tcb_init_mask_expr ptcb 18%Z) (Tint8) (V293_byteval (2 ^ V293_prio_row p)) M14 S14 H14.
  V293_tcb_init_read H14 18 Ptr14.
  destruct (V293_tcb_init_field_address ge le M14 ptcb bc bt base 19%Z 53%Z (Tint8) Bc Ptr14 ltac:(reflexivity) ltac:(reflexivity) Base ltac:(lia) ltac:(lia)) as [Ty14 Addr14].
  V293_tcb_init_read H14 12 Coord14.
  destruct (V293_tcb_init_field_address ge le M14 ptcb bc bt base 17%Z 51%Z Tint8 Bc Ptr14 ltac:(reflexivity) ltac:(reflexivity) Base ltac:(lia) ltac:(lia)) as [CT14 CA14].
  assert (CV14 : evalval (efield (ederef (evar ptcb)) 17%Z) (ge,le,M14)=Some (V293_byteval (V293_prio_bit p))).
  { exact (proj2 (V293_tcb_byte_field_eval ge le M14 ptcb bc bt base 17%Z 51%Z _ Bc Ptr14 ltac:(reflexivity) ltac:(reflexivity) Base ltac:(lia) ltac:(lia) Coord14)). }
  destruct (V293_tcb_init_mask_eval ge le M14 (efield (ederef (evar ptcb)) 17%Z) (V293_prio_bit p) ltac:(lia) CT14 CV14) as [MT14 MV14].
  V293_tcb_init_write P H14 14 (efield (ederef (evar ptcb)) 19%Z) (V293_tcb_init_mask_expr ptcb 17%Z) (Tint8) (V293_byteval (2 ^ V293_prio_bit p)) M15 S15 H15.
  V293_tcb_init_read H15 18 Ptr15.
  destruct (V293_tcb_init_field_address ge le M15 ptcb bc bt base 9%Z 28%Z (Tcom_ptr 411%Z) Bc Ptr15 ltac:(reflexivity) ltac:(reflexivity) Base ltac:(lia) ltac:(lia)) as [Ty15 Addr15].
  V293_tcb_init_write P H15 15 (efield (ederef (evar ptcb)) 9%Z) (enull) (Tnull) (Vnull) M16 S16 H16.
  V293_tcb_init_read H16 18 Ptr16.
  destruct (V293_tcb_init_field_address ge le M16 ptcb bc bt base 11%Z 36%Z (Tcom_ptr 412%Z) Bc Ptr16 ltac:(reflexivity) ltac:(reflexivity) Base ltac:(lia) ltac:(lia)) as [Ty16 Addr16].
  V293_tcb_init_write P H16 16 (efield (ederef (evar ptcb)) 11%Z) (enull) (Tnull) (Vnull) M17 S17 H17.
  V293_tcb_init_read H17 18 Ptr17.
  destruct (V293_tcb_init_field_address ge le M17 ptcb bc bt base 10%Z 32%Z (Tptr Tvoid) Bc Ptr17 ltac:(reflexivity) ltac:(reflexivity) Base ltac:(lia) ltac:(lia)) as [Ty17 Addr17].
  V293_tcb_init_write P H17 17 (efield (ederef (evar ptcb)) 10%Z) (enull) (Tnull) (Vnull) M18 S18 H18.
  exists M18. split.
  - unfold V293_TCBInit_fields.
    eapply V293_rekey_sequence_execution;[exact S1 | ].
    eapply V293_rekey_sequence_execution;[exact S2 | ].
    eapply V293_rekey_sequence_execution;[exact S3 | ].
    eapply V293_rekey_sequence_execution;[exact S4 | ].
    eapply V293_rekey_sequence_execution;[exact S5 | ].
    eapply V293_rekey_sequence_execution;[exact S6 | ].
    eapply V293_rekey_sequence_execution;[exact S7 | ].
    eapply V293_rekey_sequence_execution;[exact S8 | ].
    eapply V293_rekey_sequence_execution;[exact S9 | ].
    eapply V293_rekey_sequence_execution;[exact S10 | ].
    eapply V293_rekey_sequence_execution;[exact S11 | ].
    eapply V293_rekey_sequence_execution;[exact S12 | ].
    eapply V293_rekey_sequence_execution;[exact S13 | ].
    eapply V293_rekey_sequence_execution;[exact S14 | ].
    eapply V293_rekey_sequence_execution;[exact S15 | ].
    eapply V293_rekey_sequence_execution;[exact S16 | ].
    eapply V293_rekey_sequence_execution;[exact S17 | ].
    apply S18.
  - exact H18.
Qed.

Lemma V293_tcb_init_final_valid : forall bt base p top bottom identity size ext options,
  p<13 -> V293_tcb_init_values_valid top bottom identity size ext options ->
  Forall (fun cell => let '(_,tp,v) := cell in rule_type_val_match tp v=true)
    (V293_tcb_init_final_fields bt base p top bottom identity size ext options).
Proof.
  intros bt base p top bottom identity size ext options Range Valid.
  destruct Valid as (Vs & Vb & Vi & Vz & Ve & Vo).
  destruct (V293_tcb_init_byte_valid p Range) as (Vp & Vy & Vx & Vby & Vbx).
  unfold V293_tcb_init_final_fields. repeat constructor;first [assumption | reflexivity].
Qed.

(* A ready STATUS inside the TCB does not assert ready-bitmap membership,
   task-map publication, allocated stack validity or API success. *)
Lemma V293_tcb_init_record_connection : forall ge le M ir aux O op R inputs
  bt base p top bottom identity size ext options,
  p<13 -> (0<=base<=Int.max_unsigned)%Z ->
  V293_tcb_init_values_valid top bottom identity size ext options ->
  (ge,le,M,ir,aux,O,op) |= V293_rdy_raw_cells
    (V293_tcb_init_final_fields bt base p top bottom identity size ext options ++ inputs) R ->
  V293_task_record M (bt,Int.repr base) (Int.repr (Z.of_nat p)) rdy Vnull.
Proof.
  intros ge le M ir aux O op R inputs bt base p top bottom identity size ext options Range Bound Valid Owned.
  pose proof (V293_tcb_init_final_valid bt base p top bottom identity size ext options Range Valid) as FValid.
  rewrite Forall_forall in FValid.
  eapply V293_record_layout_sound with (p:=p) (pend:=0);[exact Range | reflexivity | lia | ].
  intros a tp v Member.
  assert (Inside : In (a,tp,v) (V293_tcb_init_final_fields bt base p top bottom identity size ext options)).
  { unfold V293_record_layout in Member. cbn [fst snd] in Member.
    rewrite Int.unsigned_repr in Member by exact Bound.
    unfold V293_tcb_init_final_fields. cbn [In app] in *;tauto. }
  change (load tp (getmem (ge,le,M,ir,aux,O,op)) a=Some v).
  eapply V293_rdy_raw_load;[apply in_or_app;left;exact Inside | exact (FValid _ Inside) | exact Owned].
Qed.
