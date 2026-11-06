(* Literal statement order and memory observations for the ready THEN fragment.
   No import of an implementation alias decides the expected statement AST. *)
Require Import CertiOS.framework.include_frm.
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

Definition checked_rmw : forall P ks ge le M lhs mask b off row bit (clear : bool),
  row < 256 -> bit < 8 -> (0 <= off <= Int.max_unsigned)%Z ->
  evaltype lhs (ge,le,M) = Some Tint8 ->
  evaladdr lhs (ge,le,M) = Some (Vptr (b,Int.repr off)) ->
  evalval lhs (ge,le,M) = Some (V293_byteval row) ->
  evaltype mask (ge,le,M) = Some Tint8 -> evalval mask (ge,le,M) = Some (checked_mask bit) ->
  (exists v, get M (b,off) = Some (true,v)) ->
  let v := if clear then Nat.clearbit row bit else Nat.setbit row bit in
  let M' := checked_put M (b,off) v in
  v < 256 /\ store Tint8 M (b,off) (V293_byteval v) = Some M' /\
  cstepstar P (curs (sassign lhs (if clear then checked_clear lhs mask else checked_set lhs mask)),
    (kenil,ks)) (ge,le,M) (curs (sskip None),(kenil,ks)) (ge,le,M') /\
  load Tint8 M' (b,off) = Some (V293_byteval v) /\
  (forall other, other <> (b,off) -> get M' other = get M other) := V293_rekey_byte_rmw_execution.

Definition checked_execution :
  forall P ks ge le M rows group yo yn xo xn byo byn br bg lo hi old new,
  old < 13 -> new < 13 -> lo < 256 -> hi < 256 -> br <> bg ->
  get le rows = None -> get ge rows = Some (br,Tarray Tint8 2) ->
  get le group = None -> get ge group = Some (bg,Tint8) ->
  checked_loads M br bg lo hi (V293_ready_group lo hi) -> checked_writable M br bg ->
  checked_locals ge le M br bg (checked_bindings yo yn xo xn byo byn old new) ->
  let M' := checked_memory M br bg lo hi old new in
  let r := checked_rows lo hi old new in
  cstepstar P (curs (checked_then rows group yo yn xo xn byo byn),(kenil,ks)) (ge,le,M)
    (curs (sskip None),(kenil,ks)) (ge,le,M') /\
  checked_loads M' br bg (fst r) (snd r) (V293_ready_group (fst r) (snd r)) /\
  checked_writable M' br bg /\
  checked_locals ge le M' br bg (checked_bindings yo yn xo xn byo byn old new) /\
  (forall b i, b <> br -> b <> bg -> get M' (b,i) = get M (b,i)) :=
  V293_task_prio_ready_then_execution.

Definition checked_entry : forall lo hi old new,
  lo < 256 -> hi < 256 -> old < 13 -> new < 13 ->
  checked_loads (V293_ready_fragment_fixture_mem lo hi old new)
    30%positive 31%positive lo hi (V293_ready_group lo hi) /\
  checked_writable (V293_ready_fragment_fixture_mem lo hi old new) 30%positive 31%positive /\
  checked_locals V293_ready_fragment_fixture_ge V293_ready_fragment_fixture_le
    (V293_ready_fragment_fixture_mem lo hi old new) 30%positive 31%positive
    (checked_bindings 302%Z 303%Z 304%Z 305%Z 306%Z 307%Z old new) :=
  V293_ready_fragment_entry_witness.
Definition checked_witness : forall P ks lo hi old new,
  lo < 256 -> hi < 256 -> old < 13 -> new < 13 ->
  let M := V293_ready_fragment_fixture_mem lo hi old new in
  let M' := checked_memory M 30%positive 31%positive lo hi old new in
  let r := checked_rows lo hi old new in
  cstepstar P (curs (checked_then 300%Z 301%Z 302%Z 303%Z 304%Z 305%Z 306%Z 307%Z),(kenil,ks))
    (V293_ready_fragment_fixture_ge,V293_ready_fragment_fixture_le,M)
    (curs (sskip None),(kenil,ks)) (V293_ready_fragment_fixture_ge,V293_ready_fragment_fixture_le,M') /\
  checked_loads M' 30%positive 31%positive (fst r) (snd r) (V293_ready_group (fst r) (snd r)) :=
  V293_ready_fragment_execution_witness.
Definition checked_observes lo hi old new elo ehi eg :=
  checked_loads (checked_memory (V293_ready_fragment_fixture_mem lo hi old new)
    30%positive 31%positive lo hi old new) 30%positive 31%positive elo ehi eg.
Definition checked_controls :
  checked_observes 0 1 8 6 64 0 1 /\ checked_observes 0 1 8 10 0 4 2 /\
  checked_observes 20 0 2 6 80 0 1 /\ checked_observes 0 129 8 6 64 128 3 :=
  V293_ready_fragment_physical_controls.
Definition checked_alias :
  let M := checked_put emp (30%positive,0%Z) 2 in
  let M' := checked_put M (30%positive,0%Z) 0 in
  load Tint8 M (30%positive,0%Z) = Some (checked_mask 1) /\
  store Tint8 M (30%positive,0%Z) (V293_byteval 0) = Some M' /\
  load Tint8 M' (30%positive,0%Z) = Some (V293_byteval 0) /\
  load Tint8 M' (30%positive,0%Z) <> Some (checked_mask 1) :=
  V293_ready_fragment_alias_control.

Print Assumptions checked_rmw.
Print Assumptions checked_execution.
Print Assumptions checked_entry.
Print Assumptions checked_witness.
Print Assumptions checked_controls.
Print Assumptions checked_alias.

Definition checked_correspondence :
  forall P ks ge le M rows group yo yn xo xn byo byn br bg bt tp lo hi old new entries tasks next message,
  old < 13 -> new < 13 -> lo < 256 -> hi < 256 -> br <> bg -> bt <> br -> bt <> bg ->
  get le rows = None -> get ge rows = Some (br,Tarray Tint8 2) ->
  get le group = None -> get ge group = Some (bg,Tint8) ->
  checked_loads M br bg lo hi (V293_ready_group lo hi) -> checked_writable M br bg ->
  checked_locals ge le M br bg (checked_bindings yo yn xo xn byo byn old new) ->
  V293_priority_table entries tasks -> V293_bitmap_tasks lo hi tasks ->
  get tasks next = Some (Int.repr (Z.of_nat old),rdy,message) -> nth new entries Vnull = Vnull ->
  (forall p, p < 13 -> load (Tptr tp) M (bt,(4*Z.of_nat p)%Z) =
    Some (nth p (update_nth_val new (update_nth_val old entries Vnull) (Vptr next)) Vnull)) ->
  let M' := checked_memory M br bg lo hi old new in
  let r := checked_rows lo hi old new in
  let tasks' := set tasks next (Int.repr (Z.of_nat new),rdy,message) in
  let entries' := update_nth_val new (update_nth_val old entries Vnull) (Vptr next) in
  cstepstar P (curs (checked_then rows group yo yn xo xn byo byn),(kenil,ks)) (ge,le,M)
    (curs (sskip None),(kenil,ks)) (ge,le,M') /\
  checked_loads M' br bg (fst r) (snd r) (V293_ready_group (fst r) (snd r)) /\
  V293_bitmap_tasks (fst r) (snd r) tasks' /\ V293_priority_table entries' tasks' /\
  (forall p, p < 13 -> load (Tptr tp) M' (bt,(4*Z.of_nat p)%Z) = Some (nth p entries' Vnull)) /\
  exists chosen msg,
    get tasks' chosen = Some (Int.repr (Z.of_nat
      (V293_ready_select (fst r) (snd r) (V293_ready_group (fst r) (snd r)))),rdy,msg) /\
    V293_highest_ready tasks' chosen /\
    load (Tptr tp) M' (bt,(4*Z.of_nat
      (V293_ready_select (fst r) (snd r) (V293_ready_group (fst r) (snd r))))%Z) = Some (Vptr chosen) :=
  V293_task_prio_ready_then_correspondence.
Print Assumptions checked_correspondence.
