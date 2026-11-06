(* Literal condition, statements, bytes and frames for reads -> ready if.
   Not the following independent event handling or the full API. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import Coq.Lists.List.
Local Open Scope nat_scope.
(* Keep bounded-map implementation proofs out of definitional conversion.
   Both sides still use the same real set operation; no axiom is added. *)
Local Opaque HalfPermMap.set.

Definition checked_clear row mask :=
  ecast (ebinop obitand (ecast row Tint32)
    (ecast (ecast (eunop negation (ecast mask Tint32)) Tint8) Tint32)) Tint8.
Definition checked_set row mask :=
  ecast (ebinop obitor (ecast row Tint32) (ecast mask Tint32)) Tint8.
Definition checked_then rows group yo yn xo xn byo byn :=
  sseq (sassign (earrayelem (evar rows) (evar yo))
    (checked_clear (earrayelem (evar rows) (evar yo)) (evar xo)))
    (sseq (sifthen (ebinop oeq
      (ecast (earrayelem (evar rows) (evar yo)) Tint32) (econst32 Int.zero))
      (sassign (evar group) (checked_clear (evar group) (evar byo))))
      (sseq (sassign (evar group) (checked_set (evar group) (evar byn)))
        (sassign (earrayelem (evar rows) (evar yn))
          (checked_set (earrayelem (evar rows) (evar yn)) (evar xn))))).
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
Definition checked_writable M br bg :=
  (exists v, get M (br,0%Z) = Some (true,v)) /\
  (exists v, get M (br,1%Z) = Some (true,v)) /\
  (exists v, get M (bg,0%Z) = Some (true,v)).
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
  then Nat.clearbit (V293_ready_group lo hi) (checked_row old) else V293_ready_group lo hi.
Definition checked_memory M br bg lo hi old new :=
  let c := checked_cleared lo hi old in
  let cv := if checked_row old =? 0 then fst c else snd c in
  let M1 := checked_put M (br,Z.of_nat (checked_row old)) cv in
  let M2 := if cv =? 0 then checked_put M1 (bg,0%Z) (checked_gc lo hi old) else M1 in
  let M3 := checked_put M2 (bg,0%Z) (Nat.setbit (checked_gc lo hi old) (checked_row new)) in
  let r := checked_rows lo hi old new in
  checked_put M3 (br,Z.of_nat (checked_row new)) (if checked_row new =? 0 then fst r else snd r).

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
Definition checked_test rows yo xo :=
  eunop oppsite (ebinop oeq
    (ebinop obitand (ecast (earrayelem (evar rows) (evar yo)) Tint32)
      (ecast (evar xo) Tint32)) (econst32 Int.zero)).
Definition checked_branch rows group yo yn xo xn byo byn :=
  sifthen (checked_test rows yo xo) (checked_then rows group yo yn xo xn byo byn).
Definition checked_read_ready p rows group yo yn xo xn byo byn :=
  sseq (checked_reads p yo byo xo) (checked_branch rows group yo yn xo xn byo byn).
Definition checked_flag lo hi old :=
  Nat.testbit (if checked_row old =? 0 then lo else hi) (checked_bit old).
Definition checked_branch_memory M br bg lo hi old new :=
  if checked_flag lo hi old then checked_memory M br bg lo hi old new else M.
Definition checked_branch_rows lo hi old new :=
  if checked_flag lo hi old then checked_rows lo hi old new else (lo,hi).
Definition checked_new (yn xn byn : var) new :=
  (yn,V293_byteval (checked_row new)) :: (xn,checked_mask (checked_bit new)) ::
  (byn,checked_mask (checked_row new)) :: nil.
Definition checked_tcb_loads M bt base y byv x :=
  load Tint8 M (bt,(base+52)%Z) = Some (V293_byteval y) /\
  load Tint8 M (bt,(base+54)%Z) = Some (V293_byteval byv) /\
  load Tint8 M (bt,(base+53)%Z) = Some (V293_byteval x).
Definition checked_read_post M dy dby dx y byv x :=
  checked_put (checked_put (checked_put M (dy,0%Z) y) (dby,0%Z) byv) (dx,0%Z) x.
Definition checked_ge : env :=
  set (set emp 300%Z (30%positive,Tarray Tint8 2)) 301%Z (31%positive,Tint8).
Definition checked_le : env :=
  set (set (set (set (set (set (set emp 302%Z (32%positive,Tint8))
    303%Z (33%positive,Tint8)) 304%Z (34%positive,Tint8)) 305%Z (35%positive,Tint8))
    306%Z (36%positive,Tint8)) 307%Z (37%positive,Tint8)) 400%Z (40%positive,Tptr checked_tcb).
Definition checked_pointer : mem :=
  set (set (set (set emp (40%positive,0%Z) (true,Pointer 41%positive (Int.repr 8) 3))
    (40%positive,1%Z) (true,Pointer 41%positive (Int.repr 8) 2))
    (40%positive,2%Z) (true,Pointer 41%positive (Int.repr 8) 1))
    (40%positive,3%Z) (true,Pointer 41%positive (Int.repr 8) 0).
Definition checked_fixture lo hi old new : mem :=
  checked_put (checked_put (checked_put
    (checked_put (checked_put (checked_put
      (checked_put (checked_put (checked_put
        (checked_put (checked_put (checked_put checked_pointer
          (41%positive,60%Z) (checked_row old)) (41%positive,62%Z) (2 ^ checked_row old))
          (41%positive,61%Z) (2 ^ checked_bit old))
        (30%positive,0%Z) lo) (30%positive,1%Z) hi) (31%positive,0%Z) (V293_ready_group lo hi))
      (32%positive,0%Z) 255) (36%positive,0%Z) 255) (34%positive,0%Z) 255)
    (33%positive,0%Z) (checked_row new)) (35%positive,0%Z) (2 ^ checked_bit new))
    (37%positive,0%Z) (2 ^ checked_row new).

Definition checked_arithmetic : forall row bit, row < 256 -> bit < 8 ->
  negb (Int.eq (Int.and (Int.repr (Z.of_nat row))
    (Int.shl Int.one (Int.repr (Z.of_nat bit)))) Int.zero) = Nat.testbit row bit :=
  V293_ready_test_arithmetic.
Definition checked_expr : forall ge le M row mask r bit,
  r < 256 -> bit < 8 ->
  evaltype row (ge,le,M) = Some Tint8 -> evalval row (ge,le,M) = Some (V293_byteval r) ->
  evaltype mask (ge,le,M) = Some Tint8 -> evalval mask (ge,le,M) = Some (checked_mask bit) ->
  evalval (eunop oppsite (ebinop oeq
    (ebinop obitand (ecast row Tint32) (ecast mask Tint32)) (econst32 Int.zero)))
    (ge,le,M) = Some (Vint32 (if Nat.testbit r bit then Int.one else Int.zero)) :=
  V293_ready_test_expr_eval.
Definition checked_branch_execution :
  forall P ks ge le M rows group yo yn xo xn byo byn br bg lo hi old new,
  old < 13 -> new < 13 -> lo < 256 -> hi < 256 -> br <> bg ->
  get le rows = None -> get ge rows = Some (br,Tarray Tint8 2) ->
  get le group = None -> get ge group = Some (bg,Tint8) ->
  checked_loads M br bg lo hi (V293_ready_group lo hi) -> checked_writable M br bg ->
  checked_locals ge le M br bg (checked_bindings yo yn xo xn byo byn old new) ->
  let M' := checked_branch_memory M br bg lo hi old new in
  let r := checked_branch_rows lo hi old new in
  evalval (checked_test rows yo xo) (ge,le,M) =
    Some (Vint32 (if checked_flag lo hi old then Int.one else Int.zero)) /\
  cstepstar P (curs (checked_branch rows group yo yn xo xn byo byn),(kenil,ks))
    (ge,le,M) (curs (sskip None),(kenil,ks)) (ge,le,M') /\
  checked_loads M' br bg (fst r) (snd r) (V293_ready_group (fst r) (snd r)) /\
  checked_writable M' br bg /\
  checked_locals ge le M' br bg (checked_bindings yo yn xo xn byo byn old new) /\
  (forall b i, b <> br -> b <> bg -> get M' (b,i) = get M (b,i)) :=
  V293_task_prio_ready_branch_execution.

Definition checked_continuous :
  forall P ks ge le M p rows group yo yn xo xn byo byn bc bt dy dby dx base br bg lo hi old new,
  old < 13 -> new < 13 -> lo < 256 -> hi < 256 -> br <> bg ->
  (0 <= base)%Z -> (base+55 <= Int.max_unsigned)%Z ->
  get le p = Some (bc,Tptr checked_tcb) ->
  get le yo = Some (dy,Tint8) -> get le byo = Some (dby,Tint8) -> get le xo = Some (dx,Tint8) ->
  get le rows = None -> get ge rows = Some (br,Tarray Tint8 2) ->
  get le group = None -> get ge group = Some (bg,Tint8) ->
  dy <> dby -> dy <> dx -> dby <> dx ->
  (forall b, b = dy \/ b = dby \/ b = dx -> b <> bc /\ b <> bt /\ b <> br /\ b <> bg) ->
  load (Tptr checked_tcb) M (bc,0%Z) = Some (Vptr (bt,Int.repr base)) ->
  checked_tcb_loads M bt base (checked_row old) (2 ^ checked_row old) (2 ^ checked_bit old) ->
  (exists v, get M (dy,0%Z) = Some (true,v)) ->
  (exists v, get M (dby,0%Z) = Some (true,v)) ->
  (exists v, get M (dx,0%Z) = Some (true,v)) ->
  checked_loads M br bg lo hi (V293_ready_group lo hi) -> checked_writable M br bg ->
  checked_locals ge le M br bg (checked_new yn xn byn new) ->
  (forall x v b, In (x,v) (checked_new yn xn byn new) ->
    get le x = Some (b,Tint8) -> b <> dy /\ b <> dby /\ b <> dx) ->
  let Mr := checked_read_post M dy dby dx (checked_row old) (2 ^ checked_row old) (2 ^ checked_bit old) in
  let Mf := checked_branch_memory Mr br bg lo hi old new in
  let r := checked_branch_rows lo hi old new in
  cstepstar P (curs (checked_read_ready p rows group yo yn xo xn byo byn),(kenil,ks))
    (ge,le,M) (curs (sskip None),(kenil,ks)) (ge,le,Mf) /\
  evalval (checked_test rows yo xo) (ge,le,Mr) =
    Some (Vint32 (if checked_flag lo hi old then Int.one else Int.zero)) /\
  checked_loads Mf br bg (fst r) (snd r) (V293_ready_group (fst r) (snd r)) /\
  checked_writable Mf br bg /\
  checked_locals ge le Mf br bg (checked_bindings yo yn xo xn byo byn old new) /\
  (forall b i, b <> dy -> b <> dby -> b <> dx -> b <> br -> b <> bg -> get Mf (b,i) = get M (b,i)) :=
  V293_task_prio_read_ready_execution.

Definition checked_entry : forall lo hi old new,
  lo < 256 -> hi < 256 -> old < 13 -> new < 13 ->
  let M := checked_fixture lo hi old new in
  load (Tptr checked_tcb) M (40%positive,0%Z) = Some (Vptr (41%positive,Int.repr 8)) /\
  checked_tcb_loads M 41%positive 8%Z (checked_row old) (2 ^ checked_row old) (2 ^ checked_bit old) /\
  (exists v, get M (32%positive,0%Z) = Some (true,v)) /\
  (exists v, get M (36%positive,0%Z) = Some (true,v)) /\
  (exists v, get M (34%positive,0%Z) = Some (true,v)) /\
  checked_loads M 30%positive 31%positive lo hi (V293_ready_group lo hi) /\
  checked_writable M 30%positive 31%positive /\
  checked_locals checked_ge checked_le M 30%positive 31%positive (checked_new 303%Z 305%Z 307%Z new) :=
  V293_read_ready_entry_witness.
Definition checked_witness : forall P ks lo hi old new,
  lo < 256 -> hi < 256 -> old < 13 -> new < 13 ->
  let M := checked_fixture lo hi old new in
  let Mr := checked_read_post M 32%positive 36%positive 34%positive
    (checked_row old) (2 ^ checked_row old) (2 ^ checked_bit old) in
  let Mf := checked_branch_memory Mr 30%positive 31%positive lo hi old new in
  let r := checked_branch_rows lo hi old new in
  cstepstar P (curs (checked_read_ready 400%Z 300%Z 301%Z 302%Z 303%Z 304%Z 305%Z 306%Z 307%Z),(kenil,ks))
    (checked_ge,checked_le,M) (curs (sskip None),(kenil,ks)) (checked_ge,checked_le,Mf) /\
  evalval (checked_test 300%Z 302%Z 304%Z) (checked_ge,checked_le,Mr) =
    Some (Vint32 (if checked_flag lo hi old then Int.one else Int.zero)) /\
  checked_loads Mf 30%positive 31%positive (fst r) (snd r) (V293_ready_group (fst r) (snd r)) :=
  V293_read_ready_execution_witness.
Definition checked_observes lo hi old new (flag : bool) elo ehi eg := forall P ks,
  let M := checked_fixture lo hi old new in
  let Mr := checked_read_post M 32%positive 36%positive 34%positive
    (checked_row old) (2 ^ checked_row old) (2 ^ checked_bit old) in
  let Mf := checked_branch_memory Mr 30%positive 31%positive lo hi old new in
  cstepstar P (curs (checked_read_ready 400%Z 300%Z 301%Z 302%Z 303%Z 304%Z 305%Z 306%Z 307%Z),(kenil,ks))
    (checked_ge,checked_le,M) (curs (sskip None),(kenil,ks)) (checked_ge,checked_le,Mf) /\
  evalval (checked_test 300%Z 302%Z 304%Z) (checked_ge,checked_le,Mr) =
    Some (Vint32 (if flag then Int.one else Int.zero)) /\
  checked_loads Mf 30%positive 31%positive elo ehi eg.
Definition checked_controls :
  checked_observes 20 0 2 6 true 80 0 1 /\ checked_observes 16 0 2 6 false 16 0 1 :=
  V293_read_ready_physical_controls.

Print Assumptions checked_arithmetic.
Print Assumptions checked_expr.
Print Assumptions checked_branch_execution.
Print Assumptions checked_continuous.
Print Assumptions checked_entry.
Print Assumptions checked_witness.
Print Assumptions checked_controls.
