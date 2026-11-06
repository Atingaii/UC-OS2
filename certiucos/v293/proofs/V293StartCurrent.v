(* Bridge the real startup store to the framework's reserved current-task
   identifier. Two half shares replace, never duplicate, full ownership.
   This is not the full kernel invariant or execution of the CPU port. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.certiucos.v293.code.V293OSStart.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.proofs.V293Start.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.sep_combine_lemmas.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope nat_scope.

Lemma V293_start_global_owned : forall ge le M ir aux O op b tp t,
  get ge OSTCBCur=Some (b,Tptr tp) ->
  (ge,le,M,ir,aux,O,op) |= Amapsto (b,0%Z) (Tptr tp) true (Vptr t) ->
  (ge,le,M,ir,aux,O,op) |= GV OSTCBCur @ (Tptr tp) |-> Vptr t.
Proof.
  intros ge le M ir aux O op b tp t Binding Owned.
  exists b. apply sat_split'. exists (emp:mem). exists M. exists (emp:osabst). exists O.
  split;[apply map_join_comm;apply map_join_emp | ].
  split;[apply map_join_comm;apply map_join_emp | ]. split.
  - exists b. split;[exact Binding | ]. repeat split;reflexivity.
  - exact Owned.
Qed.

Lemma V293_start_current_halves : forall before after R ge le M ir aux O op b tp t,
  get ge OSTCBCur=Some (b,Tptr tp) ->
  (ge,le,M,ir,aux,O,op) |=
    V293_rdy_raw_cells (before++((b,0%Z),Tptr tp,Vptr t)::after) R ->
  (ge,le,M,ir,aux,O,op) |=
    CurTid t ** CurTid t ** V293_rdy_raw_cells (before++after) R.
Proof.
  intros before after R ge le M ir aux O op b tp t Binding Owned.
  apply V293_rdy_cell_out in Owned. apply sat_split in Owned.
  destruct Owned as (mh&mt&oh&ot&JM&JO&Head&Tail).
  assert (Global : (ge,le,M,ir,aux,O,op) |=
    GV OSTCBCur @ (Tptr tp) |-> Vptr t ** V293_rdy_raw_cells (before++after) R).
  { apply sat_split'. exists mh. exists mt. exists oh. exists ot.
    split;[exact JM | ]. split;[exact JO | ]. split;[ | exact Tail].
    eapply V293_start_global_owned;eassumption. }
  apply GV_separate_rw_frm in Global.
  unfold CurTid. clear -Global. sep auto.
Qed.

Definition V293_start_other_cells bh bc bt brun bp n target frame : list V293_record_cell :=
  [((bh,0%Z),Tint8,V293_byteval n);((bc,0%Z),Tint8,V293_byteval n);
   ((bt,0%Z),Tptr V293_tcb_type,Vptr target);
   ((brun,0%Z),Tint8,Vint32 Int.zero);
   ((bp,(4*Z.of_nat n)%Z),Tptr V293_tcb_type,Vptr target)]++frame.

Lemma V293_start_final_current : forall ge le M ir aux O op bh bc bt bu brun bp n target frame,
  get ge OSTCBCur=Some (bu,Tptr V293_tcb_type) ->
  (ge,le,M,ir,aux,O,op) |= V293_rdy_raw_cells
    (V293_start_final bh bc bt bu brun bp n target frame) Atrue ->
  (ge,le,M,ir,aux,O,op) |= CurTid target ** CurTid target **
    V293_rdy_raw_cells (V293_start_other_cells bh bc bt brun bp n target frame) Atrue.
Proof.
  intros ge le M ir aux O op bh bc bt bu brun bp n target frame Binding Owned.
  eapply (V293_start_current_halves
    (((bh,0%Z),Tint8,V293_byteval n)::((bc,0%Z),Tint8,V293_byteval n)::
     ((bt,0%Z),Tptr V293_tcb_type,Vptr target)::nil)
    (((brun,0%Z),Tint8,Vint32 Int.zero)::
      ((bp,(4*Z.of_nat n)%Z),Tptr V293_tcb_type,Vptr target)::frame)
    Atrue ge le M ir aux O op bu V293_tcb_type target Binding Owned).
Qed.

Theorem V293_OSStart_call_establishes_current : forall frame P ks ge caller M ir aux O op
  startfn running sched prio high table top port unmap group rows y
  brun bc bh bp bt bu bm bg br lo hi hv cv tv uv target,
  P startfn=Some (V293_OSStart_function running sched prio high table top OSTCBCur port) ->
  P sched=Some (V293_OSSchedNew_function unmap group rows high y) ->
  y<>unmap -> y<>group -> y<>rows -> y<>high ->
  get ge unmap=Some (bm,Tarray Tint8 256) -> get ge group=Some (bg,Tint8) ->
  get ge rows=Some (br,Tarray Tint8 2) -> get ge high=Some (bh,Tint8) ->
  get ge running=Some (brun,Tint8) -> get ge prio=Some (bc,Tint8) ->
  get ge table=Some (bp,Tarray (Tptr V293_tcb_type) 13) ->
  get ge top=Some (bt,Tptr V293_tcb_type) -> get ge OSTCBCur=Some (bu,Tptr V293_tcb_type) ->
  lo<256 -> hi<256 -> (exists p,V293_bitmap_ready lo hi p) ->
  V293_sched_read_memory M bm bg br lo hi (V293_ready_group lo hi) ->
  (ge,emp,M,ir,aux,O,op) |= V293_rdy_raw_cells
    (V293_start_cells bh bc bt bu brun bp (V293_ready_select lo hi (V293_ready_group lo hi))
      hv cv tv uv (Vint32 Int.zero) (Vptr target) frame) Atrue ->
  exists Mf,
    cstepstar P (curs (scall startfn nil),(kenil,ks)) (ge,caller,M)
      (curs (sfexec port nil nil),(kenil,kseq sret (kcall startfn
        (V293_OSStart_body running sched prio high table top OSTCBCur port) caller ks))) (ge,emp,Mf) /\
    (ge,emp,Mf,ir,aux,O,op) |= CurTid target ** CurTid target **
      V293_rdy_raw_cells (V293_start_other_cells bh bc bt brun bp
        (V293_ready_select lo hi (V293_ready_group lo hi)) target frame) Atrue.
Proof.
  intros frame P ks ge caller M ir aux O op startfn running sched prio high table top port
    unmap group rows y brun bc bh bp bt bu bm bg br lo hi hv cv tv uv target
    Program Scheduler Nu Ng Nr Nh Gm Gg Gr Gh Grun Gc Gp Gt Gu Lo Hi Nonempty Reads Owned.
  destruct (V293_OSStart_call_to_port frame P ks ge caller M ir aux O op
    startfn running sched prio high table top OSTCBCur port unmap group rows y
    brun bc bh bp bt bu bm bg br lo hi hv cv tv uv target
    Program Scheduler Nu Ng Nr Nh Gm Gg Gr Gh Grun Gc Gp Gt Gu Lo Hi Nonempty Reads Owned)
    as (Mf&Exec&Final).
  exists Mf. split;[exact Exec | ]. eapply V293_start_final_current;eassumption.
Qed.
Print Assumptions V293_start_current_halves.
Print Assumptions V293_OSStart_call_establishes_current.

Theorem V293_OSStart_highest_establishes_current : forall entries tasks frame P ks ge caller M ir aux O op
  startfn running sched prio high table top port unmap group rows y
  brun bc bh bp bt bu bm bg br lo hi hv cv tv uv,
  P startfn=Some (V293_OSStart_function running sched prio high table top OSTCBCur port) ->
  P sched=Some (V293_OSSchedNew_function unmap group rows high y) ->
  y<>unmap -> y<>group -> y<>rows -> y<>high ->
  get ge unmap=Some (bm,Tarray Tint8 256) -> get ge group=Some (bg,Tint8) ->
  get ge rows=Some (br,Tarray Tint8 2) -> get ge high=Some (bh,Tint8) ->
  get ge running=Some (brun,Tint8) -> get ge prio=Some (bc,Tint8) ->
  get ge table=Some (bp,Tarray (Tptr V293_tcb_type) 13) ->
  get ge top=Some (bt,Tptr V293_tcb_type) -> get ge OSTCBCur=Some (bu,Tptr V293_tcb_type) ->
  lo<256 -> hi<256 -> (exists p,V293_bitmap_ready lo hi p) ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks ->
  get O abstcblsid=Some (abstcblist tasks) ->
  V293_sched_read_memory M bm bg br lo hi (V293_ready_group lo hi) ->
  (ge,emp,M,ir,aux,O,op) |= V293_rdy_raw_cells
    (V293_start_cells bh bc bt bu brun bp (V293_ready_select lo hi (V293_ready_group lo hi))
      hv cv tv uv (Vint32 Int.zero) (nth (V293_ready_select lo hi (V293_ready_group lo hi)) entries Vnull) frame) Atrue ->
  exists target message Mf,
    get tasks target=Some (Int.repr (Z.of_nat (V293_ready_select lo hi (V293_ready_group lo hi))),rdy,message) /\
    V293_scheduler O target /\
    cstepstar P
      (curs (scall startfn nil),(kenil,ks)) (ge,caller,M)
      (curs (sfexec port nil nil),(kenil,kseq sret (kcall startfn
        (V293_OSStart_body running sched prio high table top OSTCBCur port) caller ks))) (ge,emp,Mf) /\
    (ge,emp,Mf,ir,aux,O,op) |= CurTid target ** CurTid target **
      V293_rdy_raw_cells (V293_start_other_cells bh bc bt brun bp
        (V293_ready_select lo hi (V293_ready_group lo hi)) target frame) Atrue.
Proof.
  intros entries tasks frame P ks ge caller M ir aux O op startfn running sched prio high table top port unmap group rows y
    brun bc bh bp bt bu bm bg br lo hi hv cv tv uv StartProgram
    Program Nu Ng Nr Nh Gm Gg Gr Gh Grun Gc Gp Gt Gu Lo Hi Nonempty Bitmap Table Abstract Reads Owned.
  destruct (V293_OSStart_highest_ready_call_to_port entries tasks frame P ks ge caller M ir aux O op
    startfn running sched prio high table top OSTCBCur port unmap group rows y
    brun bc bh bp bt bu bm bg br lo hi hv cv tv uv StartProgram
    Program Nu Ng Nr Nh Gm Gg Gr Gh Grun Gc Gp Gt Gu Lo Hi Nonempty Bitmap Table Abstract Reads Owned)
    as (target&message&Mf&Member&Selected&Exec&Final).
  exists target. exists message. exists Mf.
  split;[exact Member | ]. split;[exact Selected | ]. split;[exact Exec | ].
  eapply V293_start_final_current;eassumption.
Qed.
Print Assumptions V293_OSStart_highest_establishes_current.
