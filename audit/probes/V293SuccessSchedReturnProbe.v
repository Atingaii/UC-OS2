(* Fixed literal checkpoint interfaces. The checker never regenerates these
   definitions or statements from the candidate under test. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition expected_scheduler saved interrupt lock schednew table high target current counter : function :=
  (Tvoid,dnil,dcons saved Tint32 dnil,
    sseq (sassign (evar saved) (econst32 Int.zero))
      (sseq (sprim encrit)
        (sseq
          (sifthen (ebinop oeq (ecast (evar interrupt) Tint32) (econst32 (Int.repr 0)))
            (sifthen (ebinop oeq (ecast (evar lock) Tint32) (econst32 (Int.repr 0)))
              (sseq
                (sseq (scall schednew nil) (sassign (evar target) (earrayelem (evar table) (evar high))))
                (sifthen (eunop oppsite (ebinop oeq (ecast (evar high) Tint32) (ecast (evar current) Tint32)))
                  (sseq (sassign (evar counter) (ebinop oplus (evar counter) (econst32 Int.one)))
                    (sprim (switch target)))))))
          (sseq (sprim excrit) sret)))).
Definition expected_schedule running sched :=
  sifthen (ebinop oeq (ecast (evar running) Tint32) (econst32 Int.one)) (scall sched nil).
Definition expected_tail running sched :=
  sseq (expected_schedule running sched) (srete (econst32 Int.zero)).
Definition expected_blocked ge M interrupt lock : Prop :=
  exists bi ni,
    get ge interrupt = Some (bi,Tint8) /\ load Tint8 M (bi,0%Z) = Some (V293_byteval ni) /\ ni < 256 /\
    (ni <> 0 \/ exists bl nl,
      get ge lock = Some (bl,Tint8) /\ load Tint8 M (bl,0%Z) = Some (V293_byteval nl) /\ nl < 256 /\ nl <> 0).
Definition expected_away (ge : env) (names : list var) (written : list block) :=
  forall x b, In x names -> get ge x = Some (b,Tint8) -> ~ In b written.
Definition expected_ge : env :=
  set (set (set emp 1001%Z (100%positive,Tint8)) 1002%Z (101%positive,Tint8)) 1003%Z (102%positive,Tint8).
Definition expected_mem (saved : bool) run nesting locked :=
  V293_put_byte (V293_put_byte (V293_put_byte (V293_return_fixture_mem saved)
    (100%positive,0%Z) run) (101%positive,0%Z) nesting) (102%positive,0%Z) locked.
Definition expected_program (f : fid) : option function :=
  if Z.eq_dec f 999%Z then
    Some (expected_scheduler 1004%Z 1002%Z 1003%Z 1005%Z 500%Z 1006%Z 1007%Z 1008%Z 1009%Z)
  else None.

Theorem expected_root_0 :
  forall P ks ge caller M ir enabled si ci sched saved interrupt lock schednew table high target current counter,
  P sched = Some (expected_scheduler saved interrupt lock schednew table high target current counter) ->
  saved <> interrupt -> saved <> lock ->
  expected_blocked ge M interrupt lock ->
  V293_local_steps P (curs (scall sched nil),(kenil,ks))
    ((ge,caller,M),ir,(enabled,si,ci))
    (curs (sskip None),(kenil,ks)) ((ge,caller,M),ir,(enabled,si,ci)).
Proof. exact V293_success_sched_call_execution. Qed.
Print Assumptions expected_root_0.

Theorem expected_root_1 :
  forall P ks ge le M ir enabled si ci running rb run sched saved interrupt lock schednew table high target current counter,
  run < 256 -> get le running = None -> get ge running = Some (rb,Tint8) ->
  load Tint8 M (rb,0%Z) = Some (V293_byteval run) ->
  (run = 1 ->
    P sched = Some (expected_scheduler saved interrupt lock schednew table high target current counter) /\
    saved <> interrupt /\ saved <> lock /\ expected_blocked ge M interrupt lock) ->
  V293_local_steps P (curs (expected_schedule running sched),(kenil,ks)) ((ge,le,M),ir,(enabled,si,ci))
    (curs (sskip None),(kenil,ks)) ((ge,le,M),ir,(enabled,si,ci)).
Proof. exact V293_success_schedule_execution. Qed.
Print Assumptions expected_root_1.

Theorem expected_root_2 :
  forall P ks ge le caller M ir enabled si ci running rb run sched saved interrupt lock schednew table high target current counter
    f body next,
  run < 256 -> get le running = None -> get ge running = Some (rb,Tint8) ->
  load Tint8 M (rb,0%Z) = Some (V293_byteval run) ->
  (run = 1 ->
    P sched = Some (expected_scheduler saved interrupt lock schednew table high target current counter) /\
    saved <> interrupt /\ saved <> lock /\ expected_blocked ge M interrupt lock) ->
  callcont ks = Some (kcall f body caller next) ->
  NoDup (map fst (getaddr le)) ->
  (forall b t, In (b,t) (getaddr le) -> V293_bytes_writable M b 0%Z (typelen t)) ->
  exists Mf,
    V293_local_steps P (curs (expected_tail running sched),(kenil,ks)) ((ge,le,M),ir,(enabled,si,ci))
      (curs (sskip (Some (Vint32 Int.zero))),(kenil,next)) ((ge,caller,Mf),ir,(enabled,si,ci)) /\
    (forall b i, ~ In b (map fst (getaddr le)) -> get Mf (b,i) = get M (b,i)) /\
    (forall b t k, In (b,t) (getaddr le) -> k < typelen t -> get Mf (b,Z.of_nat k) = None).
Proof. exact V293_success_tail_return_execution. Qed.
Print Assumptions expected_root_2.

Theorem expected_root_3 :
  forall P ks ge le M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp xi bi ny nby nbx
    current reserved bcur bct curbase rb curprio
    running runblock run sched saved interrupt lock schednew high target schedcurrent counter,
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
  run < 256 -> get le running = None -> get ge running = Some (runblock,Tint8) ->
  load Tint8 M (runblock,0%Z) = Some (V293_byteval run) ->
  (run = 1 ->
    P sched = Some (expected_scheduler saved interrupt lock schednew table high target schedcurrent counter) /\
    saved <> interrupt /\ saved <> lock /\ expected_blocked ge M interrupt lock) ->
  expected_away ge [running;interrupt;lock] [bo;bc;b;dy;dby;dx;br;bg;bp;bt;ny;bi;nby;nbx] ->
  exists Mg,
  let Mh := V293_tcb_update_memory Mg bt base new in
  let fr := V293_ready_branch_rows lo hi old new in
  V293_local_steps P (curs (sseq (V293_primitive_success_update table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent xi
    current reserved) (expected_schedule running sched)),
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
Proof. exact V293_critical_null_schedule_execution. Qed.
Print Assumptions expected_root_3.

Theorem expected_root_4 :
  forall P ks ge le M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp be ebase elo ehi xi bi ny nby nbx
    current reserved bcur bct curbase rb curprio
    running runblock run sched saved interrupt lock schednew high target schedcurrent counter,
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
  run < 256 -> get le running = None -> get ge running = Some (runblock,Tint8) ->
  load Tint8 M (runblock,0%Z) = Some (V293_byteval run) ->
  (run = 1 ->
    P sched = Some (expected_scheduler saved interrupt lock schednew table high target schedcurrent counter) /\
    saved <> interrupt /\ saved <> lock /\ expected_blocked ge M interrupt lock) ->
  expected_away ge [running;interrupt;lock] [bo;bc;b;dy;dby;dx;br;bg;bp;bt;ny;bi;nby;nbx;be] ->
  exists Mg,
  let Mh := V293_tcb_update_memory Mg bt base new in
  let fr := V293_ready_branch_rows lo hi old new in
  let er := V293_ready_rekey_rows elo ehi old new in
  V293_local_steps P (curs (sseq (V293_primitive_success_update table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent xi
    current reserved) (expected_schedule running sched)),
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
Proof. exact V293_critical_event_schedule_execution. Qed.
Print Assumptions expected_root_4.

Theorem expected_root_5 : forall saved run nesting locked enabled si ci ir,
  run < 256 -> nesting < 256 -> locked < 256 ->
  (run = 1 -> nesting <> 0 \/ locked <> 0) ->
  exists Mf,
    V293_local_steps expected_program
      (curs (expected_tail 1001%Z 999%Z),(kenil,kcall 700%Z sret emp kstop))
      ((expected_ge,V293_return_fixture_le,expected_mem saved run nesting locked),ir,(enabled,si,ci))
      (curs (sskip (Some (Vint32 Int.zero))),(kenil,kstop))
      ((expected_ge,emp,Mf),ir,(enabled,si,ci)) /\
    get Mf (51%positive,0%Z) = None /\
    (forall k, k < 4 -> get Mf (61%positive,Z.of_nat k) = None) /\
    load Tint8 Mf (100%positive,0%Z) = Some (V293_byteval run) /\
    load Tint8 Mf (101%positive,0%Z) = Some (V293_byteval nesting) /\
    load Tint8 Mf (102%positive,0%Z) = Some (V293_byteval locked).
Proof. exact V293_success_tail_return_witness. Qed.
Print Assumptions expected_root_5.

Example expected_nonrunning : forall enabled si ci ir,
  exists Mf,
  V293_local_steps expected_program
    (curs (expected_tail 1001%Z 999%Z),(kenil,kcall 700%Z sret emp kstop))
    ((expected_ge,V293_return_fixture_le,expected_mem false 0 0 0),ir,(enabled,si,ci))
    (curs (sskip (Some (Vint32 Int.zero))),(kenil,kstop)) ((expected_ge,emp,Mf),ir,(enabled,si,ci)).
Proof. intros. destruct (expected_root_5 false 0 0 0 enabled si ci ir ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [Mf [E _]]. eauto. Qed.
Example expected_isr : forall enabled si ci ir,
  exists Mf,
  V293_local_steps expected_program
    (curs (expected_tail 1001%Z 999%Z),(kenil,kcall 700%Z sret emp kstop))
    ((expected_ge,V293_return_fixture_le,expected_mem true 1 2 0),ir,(enabled,si,ci))
    (curs (sskip (Some (Vint32 Int.zero))),(kenil,kstop)) ((expected_ge,emp,Mf),ir,(enabled,si,ci)).
Proof. intros. destruct (expected_root_5 true 1 2 0 enabled si ci ir ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [Mf [E _]]. eauto. Qed.
Example expected_locked : forall enabled si ci ir,
  exists Mf,
  V293_local_steps expected_program
    (curs (expected_tail 1001%Z 999%Z),(kenil,kcall 700%Z sret emp kstop))
    ((expected_ge,V293_return_fixture_le,expected_mem false 1 0 1),ir,(enabled,si,ci))
    (curs (sskip (Some (Vint32 Int.zero))),(kenil,kstop)) ((expected_ge,emp,Mf),ir,(enabled,si,ci)).
Proof. intros. destruct (expected_root_5 false 1 0 1 enabled si ci ir ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [Mf [E _]]. eauto. Qed.

Example expected_nonrunning_missing_function : forall ks ir enabled si ci,
  V293_local_steps (fun _ => None)
    (curs (expected_schedule 1001%Z 999%Z),(kenil,ks))
    ((set emp 1001%Z (100%positive,Tint8),emp,V293_put_byte emp (100%positive,0%Z) 0),ir,(enabled,si,ci))
    (curs (sskip None),(kenil,ks))
    ((set emp 1001%Z (100%positive,Tint8),emp,V293_put_byte emp (100%positive,0%Z) 0),ir,(enabled,si,ci)).
Proof.
  intros. eapply V293_success_schedule_execution with (rb:=100%positive) (run:=0)
    (saved:=1004%Z) (interrupt:=1002%Z) (lock:=1003%Z) (schednew:=1005%Z)
    (table:=500%Z) (high:=1006%Z) (target:=1007%Z) (current:=1008%Z) (counter:=1009%Z).
  - lia.
  - apply map_emp_get.
  - apply map_get_set.
  - apply V293_put_byte_load;lia.
  - discriminate.
Qed.

Example expected_isr_missing_lock_binding : forall P ks ir enabled si ci,
  P 999%Z = Some (expected_scheduler 1004%Z 1002%Z 1003%Z 1005%Z 500%Z 1006%Z 1007%Z 1008%Z 1009%Z) ->
  V293_local_steps P (curs (scall 999%Z nil),(kenil,ks))
    ((set emp 1002%Z (101%positive,Tint8),emp,V293_put_byte emp (101%positive,0%Z) 1),ir,(enabled,si,ci))
    (curs (sskip None),(kenil,ks))
    ((set emp 1002%Z (101%positive,Tint8),emp,V293_put_byte emp (101%positive,0%Z) 1),ir,(enabled,si,ci)).
Proof.
  intros. eapply V293_success_sched_call_execution with
    (saved:=1004%Z) (interrupt:=1002%Z) (lock:=1003%Z) (schednew:=1005%Z)
    (table:=500%Z) (high:=1006%Z) (target:=1007%Z) (current:=1008%Z) (counter:=1009%Z).
  - exact H.
  - discriminate.
  - discriminate.
  - exists 101%positive. exists 1. split; [apply map_get_set | ].
    split; [apply V293_put_byte_load;lia | ]. split; [lia | left;lia].
Qed.
