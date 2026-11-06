(* Static literal contracts for table writes -> TCB reads -> ready if.
   No candidate program, fixture or post-memory aliases in expected types. *)
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

Definition checked_group lo hi :=
  (if lo =? 0 then 0 else 1) + (if hi =? 0 then 0 else 2).
Definition checked_bitmap_ready (lo hi p : nat) : Prop :=
  (p < 8 /\ Nat.testbit lo p = true) \/
  (8 <= p /\ p < 13 /\ Nat.testbit hi (p-8) = true).
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
  then Nat.clearbit (checked_group lo hi) (checked_row old) else checked_group lo hi.
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
        (30%positive,0%Z) lo) (30%positive,1%Z) hi) (31%positive,0%Z) (checked_group lo hi))
      (32%positive,0%Z) 255) (36%positive,0%Z) 255) (34%positive,0%Z) 255)
    (33%positive,0%Z) (checked_row new)) (35%positive,0%Z) (2 ^ checked_bit new))
    (37%positive,0%Z) (2 ^ checked_row new).


Definition checked_prefix table oldprio newprio p rows group yo yn xo xn byo byn :=
  sseq (sseq (sassign (earrayelem (evar table) (evar oldprio)) enull)
    (sassign (earrayelem (evar table) (evar newprio)) (evar p)))
    (checked_read_ready p rows group yo yn xo xn byo byn).
Definition checked_bytes_writable (M : mem) b i n :=
  forall k, k < n -> exists v, get M (b,(i+Z.of_nat k)%Z) = Some (true,v).
Definition checked_table_loads tp M b (entries : list val) :=
  forall p, p < 13 -> load (Tptr tp) M (b,(4*Z.of_nat p)%Z) = Some (nth p entries Vnull).
Fixpoint checked_put_bytes (M : mem) (b : block) (i : Z) (bytes : list memval) : mem :=
  match bytes with
  | nil => M
  | v :: rest => set (checked_put_bytes M b (i+1)%Z rest) (b,i) (true,v)
  end.
Fixpoint checked_put_table (M : mem) (b : block) (i : Z) (entries : list val) : mem :=
  match entries with
  | nil => M
  | v :: rest => checked_put_bytes (checked_put_table M b (i+4)%Z rest)
      b i (encode_val (Tptr checked_tcb) v)
  end.
Definition checked_entries : list val :=
  Vnull :: Vnull :: Vnull :: Vnull :: Vptr (60%positive,Int.zero) :: Vnull :: Vnull ::
  Vnull :: Vptr (41%positive,Int.repr 8) :: Vnull :: Vnull :: Vnull :: Vnull :: nil.
Definition checked_prefix_ge : env :=
  set checked_ge 500%Z (50%positive,Tarray (Tptr checked_tcb) 13).
Definition checked_prefix_le : env :=
  set (set checked_le 501%Z (51%positive,Tint8)) 502%Z (52%positive,Tint8).
Definition checked_prefix_mem (live : bool) : mem :=
  checked_put (checked_put
    (checked_put_table (checked_fixture 16 (if live then 1 else 0) 8 6)
      50%positive 0%Z checked_entries) (51%positive,0%Z) 8) (52%positive,0%Z) 6.
Definition checked_tasks (live : bool) : TcbMod.map :=
  set (sig (60%positive,Int.zero) (Int.repr 4,rdy,Vnull))
    (41%positive,Int.repr 8)
    (Int.repr 8,(if live then rdy else wait os_stat_time Int.one),Vnull).
Definition checked_priority_table (entries : list val) (tasks : TcbMod.map) : Prop :=
  length entries = 13 /\
  forall t priority status m, get tasks t = Some (priority,status,m) ->
    exists p, p < 13 /\ priority = Int.repr (Z.of_nat p) /\ nth p entries Vnull = Vptr t.
Definition checked_bitmap_tasks lo hi (tasks : TcbMod.map) : Prop :=
  forall p, p < 13 ->
    (checked_bitmap_ready lo hi p <-> exists t m, get tasks t = Some (Int.repr (Z.of_nat p),rdy,m)).
Definition checked_observes (live flag : bool) final_lo final_hi final_group old_slot : Prop :=
  forall P ks, exists M1 M2,
  let M := checked_prefix_mem live in
  let Mr := checked_read_post M2 32%positive 36%positive 34%positive 1 2 1 in
  let Mf := checked_branch_memory Mr 30%positive 31%positive 16 (if live then 1 else 0) 8 6 in
  store (Tptr checked_tcb) M (50%positive,32%Z) Vnull = Some M1 /\
  store (Tptr checked_tcb) M1 (50%positive,24%Z) (Vptr (41%positive,Int.repr 8)) = Some M2 /\
  cstepstar P (curs (checked_prefix 500%Z 501%Z 502%Z 400%Z
    300%Z 301%Z 302%Z 303%Z 304%Z 305%Z 306%Z 307%Z),(kenil,ks))
    (checked_prefix_ge,checked_prefix_le,M)
    (curs (sskip None),(kenil,ks)) (checked_prefix_ge,checked_prefix_le,Mf) /\
  evalval (checked_test 300%Z 302%Z 304%Z) (checked_prefix_ge,checked_prefix_le,Mr) =
    Some (Vint32 (if flag then Int.one else Int.zero)) /\
  checked_loads Mf 30%positive 31%positive final_lo final_hi final_group /\
  checked_table_loads checked_tcb Mf 50%positive
    (update_nth_val 6 (update_nth_val 8 checked_entries Vnull) (Vptr (41%positive,Int.repr 8))) /\
  load (Tptr checked_tcb) Mf (50%positive,32%Z) = Some old_slot /\
  load (Tptr checked_tcb) Mf (50%positive,24%Z) = Some (Vptr (41%positive,Int.repr 8)).

Definition checked_execution :
  forall P ks ge le M table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi old new entries,
  old < 13 -> new < 13 -> old <> new -> lo < 256 -> hi < 256 -> br <> bg ->
  (0 <= base)%Z -> (base+55 <= Int.max_unsigned)%Z ->
  get le table = None -> get ge table = Some (b,Tarray (Tptr checked_tcb) 13) ->
  get le oldprio = Some (bo,Tint8) -> get le newprio = Some (bn,Tint8) ->
  get le ptcb = Some (bc,Tptr checked_tcb) ->
  b <> bo -> b <> bn -> b <> bc -> b <> bt ->
  b <> dy -> b <> dby -> b <> dx -> b <> br -> b <> bg ->
  load Tint8 M (bo,0%Z) = Some (V293_byteval old) ->
  load Tint8 M (bn,0%Z) = Some (V293_byteval new) ->
  load (Tptr checked_tcb) M (bc,0%Z) = Some (Vptr (bt,Int.repr base)) ->
  checked_bytes_writable M b (4*Z.of_nat old)%Z 4 ->
  checked_bytes_writable M b (4*Z.of_nat new)%Z 4 ->
  length entries = 13 -> checked_table_loads checked_tcb M b entries ->
  get le yo = Some (dy,Tint8) -> get le byo = Some (dby,Tint8) -> get le xo = Some (dx,Tint8) ->
  get le rows = None -> get ge rows = Some (br,Tarray Tint8 2) ->
  get le group = None -> get ge group = Some (bg,Tint8) ->
  dy <> dby -> dy <> dx -> dby <> dx ->
  (forall c, c = dy \/ c = dby \/ c = dx -> c <> bc /\ c <> bt /\ c <> br /\ c <> bg) ->
  checked_tcb_loads M bt base (checked_row old)
    (2 ^ checked_row old) (2 ^ checked_bit old) ->
  (exists v, get M (dy,0%Z) = Some (true,v)) ->
  (exists v, get M (dby,0%Z) = Some (true,v)) ->
  (exists v, get M (dx,0%Z) = Some (true,v)) ->
  checked_loads M br bg lo hi (checked_group lo hi) ->
  checked_writable M br bg ->
  checked_locals ge le M br bg (checked_new yn xn byn new) ->
  (forall x v c, In (x,v) (checked_new yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> b /\ c <> dy /\ c <> dby /\ c <> dx) ->
  exists M1 M2,
  let Mr := checked_read_post M2 dy dby dx (checked_row old)
    (2 ^ checked_row old) (2 ^ checked_bit old) in
  let Mf := checked_branch_memory Mr br bg lo hi old new in
  let fr := checked_branch_rows lo hi old new in
  store (Tptr checked_tcb) M (b,(4*Z.of_nat old)%Z) Vnull = Some M1 /\
  store (Tptr checked_tcb) M1 (b,(4*Z.of_nat new)%Z) (Vptr (bt,Int.repr base)) = Some M2 /\
  cstepstar P (curs (checked_prefix table oldprio newprio ptcb rows group yo yn xo xn byo byn),
    (kenil,ks)) (ge,le,M) (curs (sskip None),(kenil,ks)) (ge,le,Mf) /\
  evalval (checked_test rows yo xo) (ge,le,Mr) =
    Some (Vint32 (if checked_flag lo hi old then Int.one else Int.zero)) /\
  checked_loads Mf br bg (fst fr) (snd fr) (checked_group (fst fr) (snd fr)) /\
  checked_table_loads checked_tcb Mf b
    (update_nth_val new (update_nth_val old entries Vnull) (Vptr (bt,Int.repr base))) /\
  load (Tptr checked_tcb) Mf (b,(4*Z.of_nat old)%Z) = Some Vnull /\
  load (Tptr checked_tcb) Mf (b,(4*Z.of_nat new)%Z) = Some (Vptr (bt,Int.repr base)) /\
  checked_writable Mf br bg /\
  checked_locals ge le Mf br bg (checked_bindings yo yn xo xn byo byn old new) /\
  (forall c i, c <> b -> c <> dy -> c <> dby -> c <> dx -> c <> br -> c <> bg ->
    get Mf (c,i) = get M (c,i)) :=
  V293_task_prio_prefix_execution.

Definition checked_table_entry : forall live,
  checked_table_loads checked_tcb (checked_prefix_mem live) 50%positive checked_entries /\
  checked_bytes_writable (checked_prefix_mem live) 50%positive 32%Z 4 /\
  checked_bytes_writable (checked_prefix_mem live) 50%positive 24%Z 4 :=
  V293_prefix_fixture_table_entry.

Definition checked_body_entry : forall live,
  let M := checked_prefix_mem live in
  load (Tptr checked_tcb) M (40%positive,0%Z) = Some (Vptr (41%positive,Int.repr 8)) /\
  checked_tcb_loads M 41%positive 8%Z 1 2 1 /\
  (exists v, get M (32%positive,0%Z) = Some (true,v)) /\
  (exists v, get M (36%positive,0%Z) = Some (true,v)) /\
  (exists v, get M (34%positive,0%Z) = Some (true,v)) /\
  checked_loads M 30%positive 31%positive 16 (if live then 1 else 0)
    (checked_group 16 (if live then 1 else 0)) /\
  checked_writable M 30%positive 31%positive /\
  checked_locals checked_prefix_ge checked_prefix_le M
    30%positive 31%positive (checked_new 303%Z 305%Z 307%Z 6) :=
  V293_prefix_fixture_body_entry.

Definition checked_witness : forall live,
  checked_observes live live (if live then 80 else 16) 0 1 Vnull :=
  V293_prefix_execution_witness.

Definition checked_controls :
  checked_observes true true 80 0 1 Vnull /\
  checked_observes false false 16 0 1 Vnull :=
  V293_prefix_physical_controls.

Definition checked_relations : forall live,
  checked_priority_table checked_entries (checked_tasks live) /\
  checked_bitmap_tasks 16 (if live then 1 else 0) (checked_tasks live) /\
  get (checked_tasks live) (41%positive,Int.repr 8) =
    Some (Int.repr 8,(if live then rdy else wait os_stat_time Int.one),Vnull) /\
  nth 6 checked_entries Vnull = Vnull :=
  V293_prefix_fixture_relations.

Definition checked_combined : forall live,
  let M := checked_prefix_mem live in
  let tasks := checked_tasks live in
  checked_table_loads checked_tcb M 50%positive checked_entries /\
  checked_priority_table checked_entries tasks /\
  checked_bitmap_tasks 16 (if live then 1 else 0) tasks /\
  get tasks (41%positive,Int.repr 8) =
    Some (Int.repr 8,(if live then rdy else wait os_stat_time Int.one),Vnull) /\
  nth 6 checked_entries Vnull = Vnull /\
  checked_observes live live (if live then 80 else 16) 0 1 Vnull :=
  V293_prefix_combined_witness.

Print Assumptions checked_execution.
Print Assumptions checked_table_entry.
Print Assumptions checked_body_entry.
Print Assumptions checked_witness.
Print Assumptions checked_controls.
Print Assumptions checked_relations.
Print Assumptions checked_combined.
