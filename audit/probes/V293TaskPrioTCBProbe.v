(* Expected configured source fields/statements and independent entry memory.
   This local oracle does not assert outer ready/API/invariant restoration. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import Coq.Lists.List.
Local Open Scope nat_scope.
Local Opaque HalfPermMap.set.
Definition checked_fields : decllist :=
  dcons 1%Z (Tptr Tint32) (dcons 2%Z (Tptr Tvoid)
  (dcons 3%Z (Tptr Tint32) (dcons 4%Z Tint32
  (dcons 5%Z Tint16 (dcons 6%Z Tint16
  (dcons 7%Z (Tcom_ptr 410%Z) (dcons 8%Z (Tcom_ptr 410%Z)
  (dcons 9%Z (Tcom_ptr 411%Z) (dcons 10%Z (Tptr Tvoid)
  (dcons 11%Z (Tcom_ptr 412%Z) (dcons 12%Z Tint16
  (dcons (Z.opp 1) (Tarray Tint8 2) (dcons 13%Z Tint32
  (dcons 14%Z Tint8 (dcons 15%Z Tint8 (dcons 16%Z Tint8
  (dcons 17%Z Tint8 (dcons 18%Z Tint8 (dcons 19%Z Tint8
  (dcons 20%Z Tint8 (dcons 21%Z Tint8 dnil))))))))))))))))))))).
Definition checked_tcb := Tstruct 410%Z checked_fields.
Definition checked_reads (p yo byo xo : var) :=
  sseq (sassign (evar yo) (efield (ederef (evar p)) 18%Z))
    (sseq (sassign (evar byo) (efield (ederef (evar p)) 20%Z))
      (sassign (evar xo) (efield (ederef (evar p)) 19%Z))).
Definition checked_put (M : mem) (a : addr) n :=
  set M a (true,Byte (Byte.repr (Int.unsigned (Int.repr (Z.of_nat n))))).
Definition checked_post M dy dby dx y byv x :=
  checked_put (checked_put (checked_put M (dy,0%Z) y) (dby,0%Z) byv) (dx,0%Z) x.
Definition checked_loads M bt base y byv x :=
  load Tint8 M (bt,(base+52)%Z) = Some (V293_byteval y) /\
  load Tint8 M (bt,(base+54)%Z) = Some (V293_byteval byv) /\
  load Tint8 M (bt,(base+53)%Z) = Some (V293_byteval x).
Definition checked_le : env :=
  set (set (set (set (emp : env) 400%Z (40%positive,Tptr checked_tcb))
    401%Z (42%positive,Tint8)) 402%Z (43%positive,Tint8)) 403%Z (44%positive,Tint8).
Definition checked_pointer : mem :=
  set (set (set (set (emp : mem)
    (40%positive,0%Z) (true,Pointer 41%positive (Int.repr 8) 3))
    (40%positive,1%Z) (true,Pointer 41%positive (Int.repr 8) 2))
    (40%positive,2%Z) (true,Pointer 41%positive (Int.repr 8) 1))
    (40%positive,3%Z) (true,Pointer 41%positive (Int.repr 8) 0).
Definition checked_memory y byv x :=
  checked_put (checked_put (checked_put
    (checked_put (checked_put (checked_put checked_pointer
      (41%positive,60%Z) y) (41%positive,62%Z) byv) (41%positive,61%Z) x)
    (42%positive,0%Z) 255) (43%positive,0%Z) 255) (44%positive,0%Z) 255.

Definition checked_layout :
  typelen checked_tcb = 56 /\
  ftype 18%Z checked_fields = Some Tint8 /\ ftype 20%Z checked_fields = Some Tint8 /\
  ftype 19%Z checked_fields = Some Tint8 /\
  field_offset 18%Z checked_fields = Some (Int.repr 52) /\
  field_offset 20%Z checked_fields = Some (Int.repr 54) /\
  field_offset 19%Z checked_fields = Some (Int.repr 53) := V293_tcb_old_field_layout.

Definition checked_field :
  forall P ks ge le M p dest bc bt bd base field delta n,
  n < 256 -> get le p = Some (bc,Tptr checked_tcb) -> get le dest = Some (bd,Tint8) ->
  load (Tptr checked_tcb) M (bc,0%Z) = Some (Vptr (bt,Int.repr base)) ->
  ftype field checked_fields = Some Tint8 ->
  field_offset field checked_fields = Some (Int.repr delta) ->
  (0 <= base)%Z -> (0 <= delta)%Z -> (base+delta <= Int.max_unsigned)%Z ->
  load Tint8 M (bt,(base+delta)%Z) = Some (V293_byteval n) ->
  (exists v, get M (bd,0%Z) = Some (true,v)) ->
  let M' := checked_put M (bd,0%Z) n in
  cstepstar P (curs (sassign (evar dest) (efield (ederef (evar p)) field)),(kenil,ks))
    (ge,le,M) (curs (sskip None),(kenil,ks)) (ge,le,M') /\
  load Tint8 M' (bd,0%Z) = Some (V293_byteval n) /\
  (forall other, other <> (bd,0%Z) -> get M' other = get M other) := V293_tcb_field_assignment.

Definition checked_execution :
  forall P ks ge le M p yo byo xo bc bt dy dby dx base y byv x,
  y < 256 -> byv < 256 -> x < 256 ->
  (0 <= base)%Z -> (base+55 <= Int.max_unsigned)%Z ->
  get le p = Some (bc,Tptr checked_tcb) ->
  get le yo = Some (dy,Tint8) -> get le byo = Some (dby,Tint8) -> get le xo = Some (dx,Tint8) ->
  dy <> dby -> dy <> dx -> dby <> dx ->
  (forall b, b = dy \/ b = dby \/ b = dx -> b <> bc /\ b <> bt) ->
  load (Tptr checked_tcb) M (bc,0%Z) = Some (Vptr (bt,Int.repr base)) ->
  checked_loads M bt base y byv x ->
  (exists v, get M (dy,0%Z) = Some (true,v)) ->
  (exists v, get M (dby,0%Z) = Some (true,v)) ->
  (exists v, get M (dx,0%Z) = Some (true,v)) ->
  let M' := checked_post M dy dby dx y byv x in
  cstepstar P (curs (checked_reads p yo byo xo),(kenil,ks))
    (ge,le,M) (curs (sskip None),(kenil,ks)) (ge,le,M') /\
  load Tint8 M' (dy,0%Z) = Some (V293_byteval y) /\
  load Tint8 M' (dby,0%Z) = Some (V293_byteval byv) /\
  load Tint8 M' (dx,0%Z) = Some (V293_byteval x) /\
  load (Tptr checked_tcb) M' (bc,0%Z) = Some (Vptr (bt,Int.repr base)) /\
  checked_loads M' bt base y byv x /\
  (forall b i, b <> dy -> b <> dby -> b <> dx -> get M' (b,i) = get M (b,i)) :=
  V293_task_prio_read_old_execution.

Definition checked_entry : forall y byv x,
  y < 256 -> byv < 256 -> x < 256 -> let M := checked_memory y byv x in
  get checked_le 400%Z = Some (40%positive,Tptr checked_tcb) /\
  get checked_le 401%Z = Some (42%positive,Tint8) /\
  get checked_le 402%Z = Some (43%positive,Tint8) /\
  get checked_le 403%Z = Some (44%positive,Tint8) /\
  load (Tptr checked_tcb) M (40%positive,0%Z) = Some (Vptr (41%positive,Int.repr 8)) /\
  checked_loads M 41%positive 8%Z y byv x /\
  (exists v, get M (42%positive,0%Z) = Some (true,v)) /\
  (exists v, get M (43%positive,0%Z) = Some (true,v)) /\
  (exists v, get M (44%positive,0%Z) = Some (true,v)) := V293_tcb_read_entry_witness.

Definition checked_witness : forall P ks y byv x,
  y < 256 -> byv < 256 -> x < 256 -> let M := checked_memory y byv x in
  let M' := checked_post M 42%positive 43%positive 44%positive y byv x in
  cstepstar P (curs (checked_reads 400%Z 401%Z 402%Z 403%Z),(kenil,ks))
    ((emp : env),checked_le,M) (curs (sskip None),(kenil,ks)) ((emp : env),checked_le,M') /\
  load Tint8 M' (42%positive,0%Z) = Some (V293_byteval y) /\
  load Tint8 M' (43%positive,0%Z) = Some (V293_byteval byv) /\
  load Tint8 M' (44%positive,0%Z) = Some (V293_byteval x) := V293_tcb_read_execution_witness.

Definition checked_control : forall P ks, let M := checked_memory 1 2 4 in
  let M' := checked_post M 42%positive 43%positive 44%positive 1 2 4 in
  cstepstar P (curs (checked_reads 400%Z 401%Z 402%Z 403%Z),(kenil,ks))
    ((emp : env),checked_le,M) (curs (sskip None),(kenil,ks)) ((emp : env),checked_le,M') /\
  load Tint8 M' (42%positive,0%Z) = Some (V293_byteval 1) /\
  load Tint8 M' (43%positive,0%Z) = Some (V293_byteval 2) /\
  load Tint8 M' (44%positive,0%Z) = Some (V293_byteval 4) := V293_tcb_read_physical_control.

Definition checked_alias : let M := checked_memory 1 2 4 in
  exists M', store Tint8 M (40%positive,0%Z) (V293_byteval 1) = Some M' /\
    load (Tptr checked_tcb) M' (40%positive,0%Z) = Some Vundef := V293_tcb_pointer_alias_control.

Print Assumptions checked_layout.
Print Assumptions checked_field.
Print Assumptions checked_execution.
Print Assumptions checked_entry.
Print Assumptions checked_witness.
Print Assumptions checked_control.
Print Assumptions checked_alias.
