(* Real startup to the CPU-port boundary. Existential uninterleaved execution;
   this does not execute OSStartHighRdy, set OSRunning, or establish global Inv. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSStart.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.certiucos.v293.code.V293OSSchedDispatch.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewStartup.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.framework.proof.cstepLib.
Require Import Coq.Lists.List Lia.
Import Coq.Lists.List.ListNotations.
Local Open Scope nat_scope.

Definition V293_start_cells bh bc bt bu brun bp n hv cv tv uv run target frame : list V293_record_cell :=
  ((bh,0%Z),Tint8,hv)::((bc,0%Z),Tint8,cv)::
  ((bt,0%Z),Tptr V293_tcb_type,tv)::((bu,0%Z),Tptr V293_tcb_type,uv)::
  ((brun,0%Z),Tint8,run)::
  ((bp,(4*Z.of_nat n)%Z),Tptr V293_tcb_type,target)::frame.
Definition V293_start_final bh bc bt bu brun bp n target frame :=
  V293_start_cells bh bc bt bu brun bp n (V293_byteval n) (V293_byteval n)
    (Vptr target) (Vptr target) (Vint32 Int.zero) (Vptr target) frame.

Lemma V293_start_owned_load : forall cells R a tp v ge le M ir aux O op,
  In (a,tp,v) cells -> rule_type_val_match tp v=true ->
  (ge,le,M,ir,aux,O,op) |= V293_rdy_raw_cells cells R -> load tp M a=Some v.
Proof.
  intros. change (load tp (getmem (ge,le,M,ir,aux,O,op)) a=Some v).
  eapply V293_rdy_raw_load;eassumption.
Qed.

Theorem V293_OSStart_body_to_port : forall frame P ks ge M ir aux O op
  running sched prio high table top current port unmap group rows y
  brun bc bh bp bt bu bm bg br lo hi hv cv tv uv target,
  P sched=Some (V293_OSSchedNew_function unmap group rows high y) ->
  y<>unmap -> y<>group -> y<>rows -> y<>high ->
  get ge unmap=Some (bm,Tarray Tint8 256) -> get ge group=Some (bg,Tint8) ->
  get ge rows=Some (br,Tarray Tint8 2) -> get ge high=Some (bh,Tint8) ->
  get ge running=Some (brun,Tint8) -> get ge prio=Some (bc,Tint8) ->
  get ge table=Some (bp,Tarray (Tptr V293_tcb_type) 13) ->
  get ge top=Some (bt,Tptr V293_tcb_type) -> get ge current=Some (bu,Tptr V293_tcb_type) ->
  lo<256 -> hi<256 -> (exists p,V293_bitmap_ready lo hi p) ->
  V293_sched_read_memory M bm bg br lo hi (V293_ready_group lo hi) ->
  (ge,emp,M,ir,aux,O,op) |= V293_rdy_raw_cells
    (V293_start_cells bh bc bt bu brun bp (V293_ready_select lo hi (V293_ready_group lo hi))
      hv cv tv uv (Vint32 Int.zero) (Vptr target) frame) Atrue ->
  exists Mf,
    cstepstar P
      (curs (V293_OSStart_body running sched prio high table top current port),(kenil,ks)) (ge,emp,M)
      (curs (sfexec port nil nil),(kenil,kseq sret ks)) (ge,emp,Mf) /\
    (ge,emp,Mf,ir,aux,O,op) |= V293_rdy_raw_cells
      (V293_start_final bh bc bt bu brun bp (V293_ready_select lo hi (V293_ready_group lo hi)) target frame) Atrue.
Proof.
  intros frame P ks ge M ir aux O op running sched prio high table top current port unmap group rows y
    brun bc bh bp bt bu bm bg br lo hi hv cv tv uv target
    Program Nu Ng Nr Nh Gm Gg Gr Gh Grun Gc Gp Gt Gu Lo Hi Nonempty Reads Owned.
  set (n:=V293_ready_select lo hi (V293_ready_group lo hi)).
  assert (Nbound : n<13) by (unfold n;apply V293_ready_selection_range;auto).
  assert (Bbound : n<256) by lia.
  assert (Run : load Tint8 M (brun,0%Z)=Some (Vint32 Int.zero)).
  { eapply V293_start_owned_load;[ | |exact Owned];[unfold V293_start_cells;do 4 right;left;reflexivity|reflexivity]. }
  assert (Guard : evalval (V293_OSStart_guard running) (ge,emp,M)=Some (Vint32 Int.one)).
  { unfold V293_OSStart_guard. cbn [evalval evaltype get_lenv get_genv get_mem].
    rewrite map_emp_get,Grun,Run. reflexivity. }
  unfold V293_start_cells in Owned.
  destruct (V293_OSSchedNew_startup_fresh_call _ P
    (kseq (V293_OSStart_dispatch prio high table top current port) (kseq sret ks))
    ge emp M ir aux O op sched unmap group rows high y bm bg br bh lo hi (V293_ready_group lo hi) hv
    Program Nu Ng Nr Nh Gm Gg Gr Gh Lo Hi eq_refl Nonempty Reads Owned) as (M1&Select&One).
  assert (Nc : get (emp:env) prio=None) by apply map_emp_get.
  assert (Nh' : get (emp:env) high=None) by apply map_emp_get.
  assert (Np : get (emp:env) table=None) by apply map_emp_get.
  assert (Nt : get (emp:env) top=None) by apply map_emp_get.
  assert (Nu' : get (emp:env) current=None) by apply map_emp_get.
  assert (High : load Tint8 M1 (bh,0%Z)=Some (V293_byteval n)).
  { eapply V293_start_owned_load;[ | |exact One];[left;reflexivity|apply V293_byte_type;exact Bbound]. }
  assert (WritePrio : exists M2,
    (forall tail,cstepstar P (curs (sassign (evar prio) (evar high)),(kenil,tail)) (ge,emp,M1)
      (curs (sskip None),(kenil,tail)) (ge,emp,M2)) /\
    (ge,emp,M2,ir,aux,O,op) |= V293_rdy_raw_cells
      (V293_start_cells bh bc bt bu brun bp n (V293_byteval n) (V293_byteval n) tv uv
        (Vint32 Int.zero) (Vptr target) frame) Atrue).
  { unfold V293_start_cells. eapply (V293_rdy_assign
      (cons ((bh,0%Z),Tint8,V293_byteval n) nil) (bc,0%Z) Tint8 cv
      (((bt,0%Z),Tptr V293_tcb_type,tv)::((bu,0%Z),Tptr V293_tcb_type,uv)::
       ((brun,0%Z),Tint8,Vint32 Int.zero)::((bp,(4*Z.of_nat n)%Z),Tptr V293_tcb_type,Vptr target)::frame)
      (V293_byteval n) (evar prio) (evar high) Tint8 Atrue P ge emp M1 ir aux O op).
    - V293_rdy_eval.
    - V293_rdy_eval.
    - reflexivity.
    - V293_rdy_eval.
    - apply eq_int;auto.
    - V293_rdy_eval.
    - apply V293_byte_type;exact Bbound.
    - exact One. }
  destruct WritePrio as (M2&CurrentPrio&Two). unfold V293_start_cells in Two.
  assert (High2 : load Tint8 M2 (bh,0%Z)=Some (V293_byteval n)).
  { eapply V293_start_owned_load;[ | |exact Two];[left;reflexivity|apply V293_byte_type;exact Bbound]. }
  assert (Slot2 : load (Tptr V293_tcb_type) M2 (bp,(4*Z.of_nat n)%Z)=Some (Vptr target)).
  { eapply V293_start_owned_load;[ | |exact Two];[do 5 right;left;reflexivity|reflexivity]. }
  destruct (V293_eval_pointer_array ge emp M2 table high V293_tcb_type bp bh n (Vptr target)
    Np Nh' Gp Gh High2 Nbound Slot2) as [TargetVal TargetTy].
  change (evalval (earrayelem (evar table) (evar high)) (ge,emp,M2)=Some (Vptr target)) in TargetVal.
  change (evaltype (earrayelem (evar table) (evar high)) (ge,emp,M2)=Some (Tptr V293_tcb_type)) in TargetTy.
  destruct (V293_rdy_assign
    (cons ((bh,0%Z),Tint8,V293_byteval n) (cons ((bc,0%Z),Tint8,V293_byteval n) nil))
    (bt,0%Z) (Tptr V293_tcb_type) tv
    (((bu,0%Z),Tptr V293_tcb_type,uv)::((brun,0%Z),Tint8,Vint32 Int.zero)::
     ((bp,(4*Z.of_nat n)%Z),Tptr V293_tcb_type,Vptr target)::frame)
    (Vptr target) (evar top) (earrayelem (evar table) (evar high))
    (Tptr V293_tcb_type) Atrue P ge emp M2 ir aux O op)
    as (M3&Top&Three).
  - V293_rdy_eval.
  - V293_rdy_eval.
  - reflexivity.
  - exact TargetTy.
  - apply eq_vptr;do 2 eexists;split;reflexivity.
  - exact TargetVal.
  - reflexivity.
  - exact Two.
  - assert (Top3 : load (Tptr V293_tcb_type) M3 (bt,0%Z)=Some (Vptr target)).
    { eapply V293_start_owned_load;[ | |exact Three];[do 2 right;left;reflexivity|reflexivity]. }
    V293_rdy_write P Three 3 (evar current) (evar top) (Vptr target) M4 Current Four.
    exists M4. split;[ | exact Four].
    unfold V293_OSStart_body,V293_OSStart_branch,V293_OSStart_dispatch.
    eapply c_stepstarn. { eapply stmt_step;[reflexivity|apply sseq_step]. }
    eapply c_stepstarn. { eapply stmt_step;[reflexivity|apply sifthen_step]. }
    eapply V293_cstepstar_trans. { apply V293_expr_steps;apply evalval_imply_estepstar;exact Guard. }
    eapply c_stepstarn. { eapply stmt_step;[reflexivity|apply svift_step;reflexivity]. }
    eapply c_stepstarn. { eapply stmt_step;[reflexivity|apply sseq_step]. }
    eapply V293_cstepstar_trans;[exact Select| ].
    eapply c_stepstarn. { eapply stmt_step;[reflexivity|apply sskip_step]. }
    eapply c_stepstarn. { eapply stmt_step;[reflexivity|apply sseq_step]. }
    eapply V293_cstepstar_trans;[apply CurrentPrio| ].
    eapply c_stepstarn. { eapply stmt_step;[reflexivity|apply sskip_step]. }
    eapply c_stepstarn. { eapply stmt_step;[reflexivity|apply sseq_step]. }
    eapply V293_cstepstar_trans;[apply Top| ].
    eapply c_stepstarn. { eapply stmt_step;[reflexivity|apply sskip_step]. }
    eapply c_stepstarn. { eapply stmt_step;[reflexivity|apply sseq_step]. }
    eapply V293_cstepstar_trans;[apply Current| ].
    eapply c_stepstarn. { eapply stmt_step;[reflexivity|apply sskip_step]. }
    eapply c_stepstarn. { eapply stmt_step;[reflexivity|apply snpcall_step]. }
    apply c_stepstar0.
Qed.
Print Assumptions V293_OSStart_body_to_port.

Theorem V293_OSStart_call_to_port : forall frame P ks ge caller M ir aux O op
  startfn running sched prio high table top current port unmap group rows y
  brun bc bh bp bt bu bm bg br lo hi hv cv tv uv target,
  P startfn=Some (V293_OSStart_function running sched prio high table top current port) ->
  P sched=Some (V293_OSSchedNew_function unmap group rows high y) ->
  y<>unmap -> y<>group -> y<>rows -> y<>high ->
  get ge unmap=Some (bm,Tarray Tint8 256) -> get ge group=Some (bg,Tint8) ->
  get ge rows=Some (br,Tarray Tint8 2) -> get ge high=Some (bh,Tint8) ->
  get ge running=Some (brun,Tint8) -> get ge prio=Some (bc,Tint8) ->
  get ge table=Some (bp,Tarray (Tptr V293_tcb_type) 13) ->
  get ge top=Some (bt,Tptr V293_tcb_type) -> get ge current=Some (bu,Tptr V293_tcb_type) ->
  lo<256 -> hi<256 -> (exists p,V293_bitmap_ready lo hi p) ->
  V293_sched_read_memory M bm bg br lo hi (V293_ready_group lo hi) ->
  (ge,emp,M,ir,aux,O,op) |= V293_rdy_raw_cells
    (V293_start_cells bh bc bt bu brun bp (V293_ready_select lo hi (V293_ready_group lo hi))
      hv cv tv uv (Vint32 Int.zero) (Vptr target) frame) Atrue ->
  exists Mf,
    cstepstar P
      (curs (scall startfn nil),(kenil,ks)) (ge,caller,M)
      (curs (sfexec port nil nil),(kenil,kseq sret (kcall startfn
        (V293_OSStart_body running sched prio high table top current port) caller ks))) (ge,emp,Mf) /\
    (ge,emp,Mf,ir,aux,O,op) |= V293_rdy_raw_cells
      (V293_start_final bh bc bt bu brun bp (V293_ready_select lo hi (V293_ready_group lo hi)) target frame) Atrue.
Proof.
  intros frame P ks ge caller M ir aux O op startfn running sched prio high table top current port unmap group rows y
    brun bc bh bp bt bu bm bg br lo hi hv cv tv uv target StartProgram
    Program Nu Ng Nr Nh Gm Gg Gr Gh Grun Gc Gp Gt Gu Lo Hi Nonempty Reads Owned.
  set (body:=V293_OSStart_body running sched prio high table top current port).
  destruct (V293_OSStart_body_to_port frame P (kcall startfn body caller ks) ge M ir aux O op
    running sched prio high table top current port unmap group rows y
    brun bc bh bp bt bu bm bg br lo hi hv cv tv uv target
    Program Nu Ng Nr Nh Gm Gg Gr Gh Grun Gc Gp Gt Gu Lo Hi Nonempty Reads Owned) as (Mf&Exec&Final).
  exists Mf. split;[ | exact Final].
  eapply c_stepstarn. { eapply stmt_step;[reflexivity|apply snpcall_step]. }
  eapply c_stepstarn.
  { eapply stmt_step;[reflexivity| ]. eapply sfexec_step with (d1:=dnil) (d2:=dnil);
    [reflexivity|reflexivity|exact StartProgram|exact I|reflexivity]. }
  eapply c_stepstarn. { eapply stmt_step;[reflexivity|apply sallocend_step]. }
  exact Exec.
Qed.

Theorem V293_OSStart_already_running_call : forall P ks ge caller M
    startfn running sched prio high table top current port brun,
  P startfn=Some (V293_OSStart_function running sched prio high table top current port) ->
  get ge running=Some (brun,Tint8) -> load Tint8 M (brun,0%Z)=Some (Vint32 Int.one) ->
  cstepstar P (curs (scall startfn nil),(kenil,ks)) (ge,caller,M)
    (curs (sskip None),(kenil,ks)) (ge,caller,M).
Proof.
  intros P ks ge caller M startfn running sched prio high table top current port brun Program Global Run.
  assert (Guard : evalval (V293_OSStart_guard running) (ge,emp,M)=Some (Vint32 Int.zero)).
  { unfold V293_OSStart_guard. cbn [evalval evaltype get_lenv get_genv get_mem].
    rewrite map_emp_get,Global,Run. reflexivity. }
  eapply c_stepstarn. { eapply stmt_step;[reflexivity|apply snpcall_step]. }
  eapply c_stepstarn.
  { eapply stmt_step;[reflexivity| ]. eapply sfexec_step with (d1:=dnil) (d2:=dnil);
    [reflexivity|reflexivity|exact Program|exact I|reflexivity]. }
  eapply c_stepstarn. { eapply stmt_step;[reflexivity|apply sallocend_step]. }
  unfold V293_OSStart_body.
  eapply c_stepstarn. { eapply stmt_step;[reflexivity|apply sseq_step]. }
  eapply c_stepstarn. { eapply stmt_step;[reflexivity|apply sifthen_step]. }
  eapply V293_cstepstar_trans. { apply V293_expr_steps;apply evalval_imply_estepstar;exact Guard. }
  eapply c_stepstarn. { eapply stmt_step;[reflexivity|apply sviff_step;reflexivity]. }
  eapply c_stepstarn. { eapply stmt_step;[reflexivity|apply sskip_step]. }
  eapply c_stepstarn. { eapply stmt_step;[reflexivity| ]. eapply sret_step;reflexivity. }
  eapply c_stepstarn. { eapply stmt_step;[reflexivity| ]. eapply sfreeend_step;reflexivity. }
  apply c_stepstar0.
Qed.
Print Assumptions V293_OSStart_call_to_port.
Print Assumptions V293_OSStart_already_running_call.

Theorem V293_OSStart_highest_ready_call_to_port : forall entries tasks frame P ks ge caller M ir aux O op
  startfn running sched prio high table top current port unmap group rows y
  brun bc bh bp bt bu bm bg br lo hi hv cv tv uv,
  P startfn=Some (V293_OSStart_function running sched prio high table top current port) ->
  P sched=Some (V293_OSSchedNew_function unmap group rows high y) ->
  y<>unmap -> y<>group -> y<>rows -> y<>high ->
  get ge unmap=Some (bm,Tarray Tint8 256) -> get ge group=Some (bg,Tint8) ->
  get ge rows=Some (br,Tarray Tint8 2) -> get ge high=Some (bh,Tint8) ->
  get ge running=Some (brun,Tint8) -> get ge prio=Some (bc,Tint8) ->
  get ge table=Some (bp,Tarray (Tptr V293_tcb_type) 13) ->
  get ge top=Some (bt,Tptr V293_tcb_type) -> get ge current=Some (bu,Tptr V293_tcb_type) ->
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
        (V293_OSStart_body running sched prio high table top current port) caller ks))) (ge,emp,Mf) /\
    (ge,emp,Mf,ir,aux,O,op) |= V293_rdy_raw_cells
      (V293_start_final bh bc bt bu brun bp (V293_ready_select lo hi (V293_ready_group lo hi)) target frame) Atrue.
Proof.
  intros entries tasks frame P ks ge caller M ir aux O op startfn running sched prio high table top current port unmap group rows y
    brun bc bh bp bt bu bm bg br lo hi hv cv tv uv StartProgram
    Program Nu Ng Nr Nh Gm Gg Gr Gh Grun Gc Gp Gt Gu Lo Hi Nonempty Bitmap Table Abstract Reads Owned.
  destruct (V293_ready_selection_task lo hi entries tasks Lo Hi Nonempty Bitmap Table)
    as (target&message&Member&Entry&Highest).
  rewrite Entry in Owned.
  destruct (V293_OSStart_call_to_port frame P ks ge caller M ir aux O op startfn
    running sched prio high table top current port unmap group rows y
    brun bc bh bp bt bu bm bg br lo hi hv cv tv uv target
    StartProgram Program Nu Ng Nr Nh Gm Gg Gr Gh Grun Gc Gp Gt Gu Lo Hi Nonempty Reads Owned)
    as (Mf&Exec&Final).
  exists target. exists message. exists Mf. split;[exact Member| ]. split.
  - exists tasks. split;assumption.
  - split;assumption.
Qed.
Print Assumptions V293_OSStart_highest_ready_call_to_port.
