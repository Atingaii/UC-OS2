(* Fixed literal expected interfaces, stored separately from the candidate.
   The interfaces were transcribed at this checkpoint; the gate never derives
   or refreshes this file from the candidate under test. Not a second proof. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition expected_success_entry table oldprio newprio ptcb current reserved :=
  sseq
    (sseq
      (sifthen (eunop oppsite (V293_task_prio_null_test
        (earrayelem (evar table) (evar newprio))))
        (sseq (sprim excrit) (srete (econst32 (Int.repr 40)))))
      (sseq (V293_task_prio_self_read oldprio current)
        (sseq (V293_task_prio_lookup table oldprio ptcb)
          (sifthen (V293_task_prio_null_test (evar ptcb))
            (sseq (sprim excrit) (srete (econst32 (Int.repr 41))))))))
    (sifthen (V293_task_prio_reserved_test ptcb reserved)
      (sseq (sprim excrit) (srete (econst32 (Int.repr 67))))).
Definition expected_success_program table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent xi current reserved :=
  sseq
    (sseq (V293_task_prio_argument_guards oldprio newprio)
      (sseq (sprim encrit) (expected_success_entry table oldprio newprio ptcb current reserved)))
    (sseq (V293_task_prio_coordinates_update table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent xi)
      (sprim excrit)).

Example expected_success_entry_interface :
  forall P ks ge le M table oldprio newprio ptcb current reserved
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
  cstepstar P (curs (expected_success_entry table oldprio newprio ptcb current reserved),
    (kenil,ks)) (ge,le,M) (curs (sskip None),(kenil,ks)) (ge,le,Mf) /\
  load Tint8 Mf (bo,0%Z) = Some (V293_byteval resolved) /\
  load Tint8 Mf (bn,0%Z) = Some (V293_byteval new) /\
  load (Tptr V293_tcb_type) Mf (bc,0%Z) = Some (Vptr next) /\
  load (Tptr V293_tcb_type) Mf (b,(4*Z.of_nat resolved)%Z) = Some (Vptr next) /\
  load (Tptr V293_tcb_type) Mf (b,(4*Z.of_nat new)%Z) = Some Vnull /\
  V293_bytes_writable Mf bc 0%Z 4 /\
  (forall c i, c <> bo -> c <> bc -> get Mf (c,i) = get M (c,i)).
Proof. exact V293_primitive_entry_success. Qed.

Example expected_null_success_interface :
  forall P ks ge le M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp xi bi ny nby nbx
    current reserved bcur bct curbase rb curprio,
  initial < 256 -> (initial < 12 \/ initial = 255) -> new < 12 ->
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
  V293_local_steps P (curs (expected_success_program table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent xi
    current reserved),
    (kenil,ks)) ((ge,le,M),ir,(enabled,si,ci)) (curs (sskip None),(kenil,ks)) ((ge,le,Mh),ir,(enabled,si,ci)) /\
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
Proof. exact V293_critical_null_update_execution. Qed.

Example expected_event_success_interface :
  forall P ks ge le M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp be ebase elo ehi xi bi ny nby nbx
    current reserved bcur bct curbase rb curprio,
  initial < 256 -> (initial < 12 \/ initial = 255) -> new < 12 ->
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
  V293_local_steps P (curs (expected_success_program table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent xi
    current reserved),
    (kenil,ks)) ((ge,le,M),ir,(enabled,si,ci)) (curs (sskip None),(kenil,ks)) ((ge,le,Mh),ir,(enabled,si,ci)) /\
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
Proof. exact V293_critical_event_update_execution. Qed.

Definition expected_null_physical self live elo ehi P ks ir enabled si ci :=
  exists Mh,
  load (Tptr V293_tcb_type) (V293_entry_null_fixture_mem self live elo ehi)
    (40%positive,0%Z) = Some Vnull /\
  (forall c, In c [33%positive;73%positive;37%positive;35%positive] ->
    load Tint8 (V293_entry_null_fixture_mem self live elo ehi) (c,0%Z) = Some (V293_byteval 255)) /\
  V293_local_steps P (curs (expected_success_program
    500%Z 501%Z 502%Z 400%Z 300%Z 301%Z 302%Z 303%Z 304%Z 305%Z 306%Z 307%Z 600%Z 601%Z
    750%Z 900%Z),(kenil,ks))
    ((V293_entry_update_fixture_ge,V293_tcb_update_fixture_le,V293_entry_null_fixture_mem self live elo ehi),ir,(enabled,si,ci))
    (curs (sskip None),(kenil,ks)) ((V293_entry_update_fixture_ge,V293_tcb_update_fixture_le,Mh),ir,(enabled,si,ci)) /\
  V293_tcb_updated_loads Mh 41%positive 8%Z 6 /\
  V293_rekey_bitmap_loads Mh 30%positive 31%positive (if live then 80 else 16) 0 1 /\
  V293_table_loads V293_tcb_type Mh 50%positive
    (update_nth_val 6 (update_nth_val 8 V293_prefix_fixture_entries Vnull) (Vptr (41%positive,Int.repr 8))) /\
  load (Tptr V293_tcb_type) Mh (50%positive,32%Z) = Some Vnull /\
  load (Tptr V293_tcb_type) Mh (50%positive,24%Z) = Some (Vptr (41%positive,Int.repr 8)) /\
  load (Tcom_ptr 411%Z) Mh (41%positive,36%Z) = Some Vnull /\
  load (Tptr V293_event_type) Mh (70%positive,0%Z) = Some Vnull /\
  (forall i, get Mh (72%positive,i) = get (V293_entry_null_fixture_mem self live elo ehi) (72%positive,i)).

Example expected_null_success_witness : forall self live elo ehi,
  elo < 256 -> ehi < 256 -> forall P ks ir enabled si ci,
  expected_null_physical self live elo ehi P ks ir enabled si ci.
Proof. exact V293_critical_null_update_witness. Qed.

Definition expected_event_physical self live elo ehi P ks ir enabled si ci :=
  exists Mh,
  load (Tptr V293_tcb_type) (V293_entry_update_fixture_mem self live elo ehi)
    (40%positive,0%Z) = Some Vnull /\
  (forall c, In c [33%positive;73%positive;37%positive;35%positive] ->
    load Tint8 (V293_entry_update_fixture_mem self live elo ehi) (c,0%Z) = Some (V293_byteval 255)) /\
  V293_local_steps P (curs (expected_success_program
    500%Z 501%Z 502%Z 400%Z 300%Z 301%Z 302%Z 303%Z 304%Z 305%Z 306%Z 307%Z 600%Z 601%Z
    750%Z 900%Z),(kenil,ks))
    ((V293_entry_update_fixture_ge,V293_tcb_update_fixture_le,V293_entry_update_fixture_mem self live elo ehi),ir,(enabled,si,ci))
    (curs (sskip None),(kenil,ks)) ((V293_entry_update_fixture_ge,V293_tcb_update_fixture_le,Mh),ir,(enabled,si,ci)) /\
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

Example expected_event_success_witness : forall self live elo ehi,
  elo < 256 -> ehi < 256 -> forall P ks ir enabled si ci,
  expected_event_physical self live elo ehi P ks ir enabled si ci.
Proof. exact V293_critical_event_update_witness. Qed.

(* Both event choices, both selectors and both ready choices; IE/si/ci arbitrary. *)
Example expected_success_samples : forall P ks ir enabled si ci,
  (forall self live, expected_null_physical self live 23 1 P ks ir enabled si ci) /\
  (forall self live, expected_event_physical self live 23 1 P ks ir enabled si ci).
Proof.
  intros P ks ir enabled si ci. split; intros self live.
  - apply expected_null_success_witness;lia.
  - apply expected_event_success_witness;lia.
Qed.
Print Assumptions expected_success_entry_interface.
Print Assumptions expected_null_success_interface.
Print Assumptions expected_event_success_interface.
Print Assumptions expected_null_success_witness.
Print Assumptions expected_event_success_witness.
Print Assumptions expected_success_samples.
