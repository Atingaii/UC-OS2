(* Static literal contracts for actual event-field updates. Shared expected
   definitions are reused from the preceding static probe, not extracted from
   the candidate interfaces. This is not an independent C front end. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import Coq.Lists.List.
Local Open Scope nat_scope.
Local Opaque HalfPermMap.set.

Definition checked_group lo hi :=
  (if lo =? 0 then 0 else 1) + (if hi =? 0 then 0 else 2).
Definition checked_clear row mask :=
  ecast (ebinop obitand (ecast row Tint32)
    (ecast (ecast (eunop negation (ecast mask Tint32)) Tint8) Tint32)) Tint8.
Definition checked_set row mask :=
  ecast (ebinop obitor (ecast row Tint32) (ecast mask Tint32)) Tint8.
Definition checked_put (M : mem) (a : addr) (n : nat) :=
  set M a (true,Byte (Byte.repr (Int.unsigned (Int.repr (Z.of_nat n))))).
Definition checked_row p := if p <? 8 then 0 else 1.
Definition checked_bit p := if p <? 8 then p else p-8.
Definition checked_mask bit := Vint32 (Int.shl Int.one (Int.repr (Z.of_nat bit))).
Definition checked_bindings (yo yn xo xn byo byn : var) old new :=
  (yo,V293_byteval (checked_row old)) :: (yn,V293_byteval (checked_row new)) ::
  (xo,checked_mask (checked_bit old)) :: (xn,checked_mask (checked_bit new)) ::
  (byo,checked_mask (checked_row old)) :: (byn,checked_mask (checked_row new)) :: nil.
Definition checked_loads M br bg lo hi g :=
  load Tint8 M (br,0%Z) = Some (V293_byteval lo) /\
  load Tint8 M (br,1%Z) = Some (V293_byteval hi) /\
  load Tint8 M (bg,0%Z) = Some (V293_byteval g).
Definition checked_locals (ge le : env) (M : mem) (br bg : block) (bindings : list (var*val)) :=
  forall x value, In (x,value) bindings -> exists b,
    get le x = Some (b,Tint8) /\ b <> br /\ b <> bg /\ load Tint8 M (b,0%Z) = Some value.
Definition checked_cleared lo hi old :=
  if old <? 8 then (Nat.clearbit lo old,hi) else (lo,Nat.clearbit hi (old-8)).
Definition checked_rows lo hi old new :=
  let c := checked_cleared lo hi old in
  if new <? 8 then (Nat.setbit (fst c) new,snd c)
  else (fst c,Nat.setbit (snd c) (new-8)).
Definition checked_gc lo hi old :=
  let c := checked_cleared lo hi old in
  if (if old <? 8 then fst c else snd c) =? 0
  then Nat.clearbit (checked_group lo hi) (checked_row old) else checked_group lo hi.
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
Definition checked_bytes_writable (M : mem) b i n :=
  forall k, k < n -> exists v, get M (b,(i+Z.of_nat k)%Z) = Some (true,v).
Fixpoint checked_put_bytes (M : mem) (b : block) (i : Z) (bytes : list memval) : mem :=
  match bytes with
  | nil => M
  | v :: rest => set (checked_put_bytes M b (i+1)%Z rest) (b,i) (true,v)
  end.
Definition checked_event_fields : decllist :=
  dcons 1%Z Tint8 (dcons (Z.opp 1) (Tarray Tint8 3)
  (dcons 2%Z (Tptr Tvoid) (dcons 3%Z Tint16
  (dcons 4%Z Tint8 (dcons 5%Z (Tarray Tint8 2)
  (dcons (Z.opp 2) (Tarray Tint8 3) dnil)))))).
Definition checked_event := Tstruct 411%Z checked_event_fields.
Definition checked_event_then pevent yo yn xo xn byo byn :=
  sseq (sassign (earrayelem (efield (ederef (evar pevent)) 5%Z) (evar yo))
    (checked_clear (earrayelem (efield (ederef (evar pevent)) 5%Z) (evar yo)) (evar xo)))
    (sseq (sifthen (ebinop oeq
      (ecast (earrayelem (efield (ederef (evar pevent)) 5%Z) (evar yo)) Tint32) (econst32 Int.zero))
      (sassign (efield (ederef (evar pevent)) 4%Z)
        (checked_clear (efield (ederef (evar pevent)) 4%Z) (evar byo))))
      (sseq (sassign (efield (ederef (evar pevent)) 4%Z)
        (checked_set (efield (ederef (evar pevent)) 4%Z) (evar byn)))
        (sassign (earrayelem (efield (ederef (evar pevent)) 5%Z) (evar yn))
          (checked_set (earrayelem (efield (ederef (evar pevent)) 5%Z) (evar yn)) (evar xn))))).
Definition checked_event_read ptcb pevent :=
  sassign (evar pevent) (efield (ederef (evar ptcb)) 9%Z).
Definition checked_event_test pevent :=
  eunop oppsite (ebinop oeq (evar pevent) (ecast enull (Tptr checked_event))).
Definition checked_event_fragment ptcb pevent yo yn xo xn byo byn :=
  sseq (checked_event_read ptcb pevent)
    (sifthen (checked_event_test pevent) (checked_event_then pevent yo yn xo xn byo byn)).
Definition checked_event_loads M be base lo hi group :=
  load Tint8 M (be,(base+11)%Z) = Some (V293_byteval lo) /\
  load Tint8 M (be,(base+12)%Z) = Some (V293_byteval hi) /\
  load Tint8 M (be,(base+10)%Z) = Some (V293_byteval group).
Definition checked_event_writable M be base :=
  (exists v, get M (be,(base+11)%Z) = Some (true,v)) /\
  (exists v, get M (be,(base+12)%Z) = Some (true,v)) /\
  (exists v, get M (be,(base+10)%Z) = Some (true,v)).
Definition checked_event_memory M be base lo hi old new :=
  let c := checked_cleared lo hi old in
  let cv := if checked_row old =? 0 then fst c else snd c in
  let M1 := checked_put M (be,(base+11+Z.of_nat (checked_row old))%Z) cv in
  let M2 := if cv =? 0 then checked_put M1 (be,(base+10)%Z) (checked_gc lo hi old) else M1 in
  let M3 := checked_put M2 (be,(base+10)%Z) (Nat.setbit (checked_gc lo hi old) (checked_row new)) in
  let r := checked_rows lo hi old new in
  checked_put M3 (be,(base+11+Z.of_nat (checked_row new))%Z)
    (if checked_row new =? 0 then fst r else snd r).
Definition checked_ready_ge : env :=
  set (set emp 300%Z (30%positive,Tarray Tint8 2)) 301%Z (31%positive,Tint8).
Definition checked_ready_le : env :=
  set (set (set (set (set (set emp 302%Z (32%positive,Tint8))
    303%Z (33%positive,Tint8)) 304%Z (34%positive,Tint8))
    305%Z (35%positive,Tint8)) 306%Z (36%positive,Tint8)) 307%Z (37%positive,Tint8).
Definition checked_ready_mem old new : mem :=
  checked_put (checked_put (checked_put (checked_put
    (checked_put (checked_put (checked_put (checked_put
      (checked_put emp (30%positive,0%Z) 16) (30%positive,1%Z) 0)
      (31%positive,0%Z) 1)
      (32%positive,0%Z) (checked_row old))
      (33%positive,0%Z) (checked_row new))
      (34%positive,0%Z) (2 ^ checked_bit old))
      (35%positive,0%Z) (2 ^ checked_bit new))
      (36%positive,0%Z) (2 ^ checked_row old))
      (37%positive,0%Z) (2 ^ checked_row new).
Definition checked_body_le : env :=
  set (set checked_ready_le 600%Z (70%positive,Tptr checked_event))
    601%Z (40%positive,Tptr checked_tcb).
Definition checked_body_mem lo hi old new : mem :=
  checked_put_bytes
    (checked_put_bytes
      (checked_put_bytes
        (checked_put (checked_put (checked_put (checked_ready_mem old new)
          (72%positive,16%Z) lo) (72%positive,17%Z) hi) (72%positive,15%Z) (checked_group lo hi))
        40%positive 0%Z (encode_val (Tptr checked_tcb) (Vptr (41%positive,Int.repr 8))))
      41%positive 36%Z (encode_val (Tcom_ptr 411%Z) (Vptr (72%positive,Int.repr 5))))
    70%positive 0%Z (encode_val (Tptr checked_event) (Vptr (71%positive,Int.repr 3))).

Definition checked_row_address : forall ge le M pevent index bc be base lo hi g y,
  get le pevent = Some (bc,Tptr checked_event) ->
  load (Tptr checked_event) M (bc,0%Z) = Some (Vptr (be,Int.repr base)) ->
  (0 <= base)%Z -> (base+12 <= Int.max_unsigned)%Z ->
  evaltype index (ge,le,M) = Some Tint8 ->
  evalval index (ge,le,M) = Some (V293_byteval y) -> y < 2 ->
  checked_event_loads M be base lo hi g ->
  evaltype (earrayelem (efield (ederef (evar pevent)) 5%Z) index) (ge,le,M) = Some Tint8 /\
  evaladdr (earrayelem (efield (ederef (evar pevent)) 5%Z) index) (ge,le,M) =
    Some (Vptr (be,Int.repr (base+11+Z.of_nat y))) /\
  evalval (earrayelem (efield (ederef (evar pevent)) 5%Z) index) (ge,le,M) =
    Some (V293_byteval (if y =? 0 then lo else hi))
  := V293_event_row_eval.

Definition checked_body_execution :
  forall P ks ge le M pevent yo yn xo xn byo byn be bc base lo hi old new,
  old < 13 -> new < 13 -> lo < 256 -> hi < 256 -> bc <> be ->
  get le pevent = Some (bc,Tptr checked_event) ->
  load (Tptr checked_event) M (bc,0%Z) = Some (Vptr (be,Int.repr base)) ->
  (0 <= base)%Z -> (base+12 <= Int.max_unsigned)%Z ->
  checked_event_loads M be base lo hi (checked_group lo hi) ->
  checked_event_writable M be base ->
  checked_locals ge le M be be (checked_bindings yo yn xo xn byo byn old new) ->
  let M' := checked_event_memory M be base lo hi old new in
  let fr := checked_rows lo hi old new in
  cstepstar P (curs (checked_event_then pevent yo yn xo xn byo byn),(kenil,ks))
    (ge,le,M) (curs (sskip None),(kenil,ks)) (ge,le,M') /\
  checked_event_loads M' be base (fst fr) (snd fr) (checked_group (fst fr) (snd fr)) /\
  checked_event_writable M' be base /\
  checked_locals ge le M' be be (checked_bindings yo yn xo xn byo byn old new) /\
  load (Tptr checked_event) M' (bc,0%Z) = Some (Vptr (be,Int.repr base)) /\
  (forall c i, c <> be \/ (i < base+10)%Z \/ (base+12 < i)%Z -> get M' (c,i) = get M (c,i))
  := V293_task_prio_event_then_execution.

Definition checked_nonnull_execution :
  forall P ks ge le M ptcb pevent yo yn xo xn byo byn bc bt bp tcbbase be base lo hi old new,
  old < 13 -> new < 13 -> lo < 256 -> hi < 256 -> bp <> be ->
  get le ptcb = Some (bc,Tptr checked_tcb) -> get le pevent = Some (bp,Tptr checked_event) ->
  load (Tptr checked_tcb) M (bc,0%Z) = Some (Vptr (bt,Int.repr tcbbase)) ->
  (0 <= tcbbase)%Z -> (tcbbase+28 <= Int.max_unsigned)%Z ->
  load (Tcom_ptr 411%Z) M (bt,(tcbbase+28)%Z) = Some (Vptr (be,Int.repr base)) ->
  checked_bytes_writable M bp 0%Z 4 ->
  (0 <= base)%Z -> (base+12 <= Int.max_unsigned)%Z ->
  checked_event_loads M be base lo hi (checked_group lo hi) -> checked_event_writable M be base ->
  checked_locals ge le M be be (checked_bindings yo yn xo xn byo byn old new) ->
  (forall x v c, In (x,v) (checked_bindings yo yn xo xn byo byn old new) ->
    get le x = Some (c,Tint8) -> c <> bp) ->
  exists Me,
  let Mf := checked_event_memory Me be base lo hi old new in
  let fr := checked_rows lo hi old new in
  store (Tptr checked_event) M (bp,0%Z) (Vptr (be,Int.repr base)) = Some Me /\
  cstepstar P (curs (checked_event_fragment ptcb pevent yo yn xo xn byo byn),(kenil,ks))
    (ge,le,M) (curs (sskip None),(kenil,ks)) (ge,le,Mf) /\
  checked_event_loads Mf be base (fst fr) (snd fr) (checked_group (fst fr) (snd fr)) /\
  checked_event_writable Mf be base /\
  checked_locals ge le Mf be be (checked_bindings yo yn xo xn byo byn old new) /\
  load (Tptr checked_event) Mf (bp,0%Z) = Some (Vptr (be,Int.repr base)) /\
  (forall c i, c <> bp -> c <> be -> get Mf (c,i) = get M (c,i))
  := V293_task_prio_event_nonnull_execution.

Definition checked_entry : forall lo hi old new,
  lo < 256 -> hi < 256 -> old < 13 -> new < 13 ->
  let M := checked_body_mem lo hi old new in let le := checked_body_le in
  load (Tptr checked_tcb) M (40%positive,0%Z) = Some (Vptr (41%positive,Int.repr 8)) /\
  load (Tcom_ptr 411%Z) M (41%positive,36%Z) = Some (Vptr (72%positive,Int.repr 5)) /\
  load (Tptr checked_event) M (70%positive,0%Z) = Some (Vptr (71%positive,Int.repr 3)) /\
  checked_bytes_writable M 70%positive 0%Z 4 /\
  checked_event_loads M 72%positive 5%Z lo hi (checked_group lo hi) /\
  checked_event_writable M 72%positive 5%Z /\
  checked_locals checked_ready_ge le M 72%positive 72%positive
    (checked_bindings 302%Z 303%Z 304%Z 305%Z 306%Z 307%Z old new) /\
  (forall x v c, In (x,v) (checked_bindings 302%Z 303%Z 304%Z 305%Z 306%Z 307%Z old new) ->
    get le x = Some (c,Tint8) -> c <> 70%positive) /\
  checked_loads M 30%positive 31%positive 16 0 1
  := V293_event_body_fixture_entry.

Definition checked_witness : forall P ks lo hi old new,
  lo < 256 -> hi < 256 -> old < 13 -> new < 13 ->
  exists Mf,
  cstepstar P (curs (checked_event_fragment 601%Z 600%Z 302%Z 303%Z 304%Z 305%Z 306%Z 307%Z),
    (kenil,ks)) (checked_ready_ge,checked_body_le,checked_body_mem lo hi old new)
    (curs (sskip None),(kenil,ks)) (checked_ready_ge,checked_body_le,Mf) /\
  checked_event_loads Mf 72%positive 5%Z
    (fst (checked_rows lo hi old new)) (snd (checked_rows lo hi old new))
    (checked_group (fst (checked_rows lo hi old new)) (snd (checked_rows lo hi old new))) /\
  load (Tptr checked_event) Mf (70%positive,0%Z) = Some (Vptr (72%positive,Int.repr 5)) /\
  checked_loads Mf 30%positive 31%positive 16 0 1
  := V293_event_nonnull_execution_witness.
Definition checked_observes lo hi old new expectedlo expectedhi expectedgroup : Prop :=
  forall P ks, exists Mf,
  cstepstar P (curs (checked_event_fragment 601%Z 600%Z 302%Z 303%Z 304%Z 305%Z 306%Z 307%Z),
    (kenil,ks)) (checked_ready_ge,checked_body_le,checked_body_mem lo hi old new)
    (curs (sskip None),(kenil,ks)) (checked_ready_ge,checked_body_le,Mf) /\
  checked_event_loads Mf 72%positive 5%Z expectedlo expectedhi expectedgroup /\
  load (Tptr checked_event) Mf (70%positive,0%Z) = Some (Vptr (72%positive,Int.repr 5)) /\
  checked_loads Mf 30%positive 31%positive 16 0 1.
Definition checked_controls :
  checked_observes 0 1 8 6 64 0 1 /\
  checked_observes 0 1 8 10 0 4 2 /\
  checked_observes 20 0 2 6 80 0 1 /\
  checked_observes 0 129 8 6 64 128 3
  := V293_event_nonnull_physical_controls.
Definition checked_raw_alias :
  let M := checked_put_bytes emp 72%positive 0%Z
    (encode_val (Tptr checked_event) (Vptr (72%positive,Int.repr 5))) in
  load (Tptr checked_event) M (72%positive,0%Z) = Some (Vptr (72%positive,Int.repr 5)) /\
  load (Tptr checked_event) (checked_put M (72%positive,0%Z) 0) (72%positive,0%Z) = Some Vundef
  := V293_event_pointer_raw_alias_control.
Print Assumptions checked_row_address.
Print Assumptions checked_body_execution.
Print Assumptions checked_nonnull_execution.
Print Assumptions checked_entry.
Print Assumptions checked_witness.
Print Assumptions checked_controls.
Print Assumptions checked_raw_alias.
