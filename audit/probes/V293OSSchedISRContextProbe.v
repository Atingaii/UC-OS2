(* Concrete assertions and a single-field contract/state identity control.
   The enabled path is not a task switch or a complete exit function. *)
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedISRContext.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitDispatch.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBoundarySwitch.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPrefix.
Require Import CertiOS.certiucos.v293.code.V293OSIntExit.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.code.V293OSSchedDispatch.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.audit.probes.V293OSIntExitBuildersProbe.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition QScontext (I:Inv) := V293_sched_ISR_context I false (fun _=>false) nil nil.
Definition QSpre I nc nest old c := V293_exit_ready_pre
 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive 0 16
 V293_witness_li V293_idle_tid(spec_done None)106%Z 107%Z Tvoid 8%positive 10%positive
 V293_idle_entries V293_idle_tasks 110%Z 111%Z 13%positive 14%positive 11%positive 12%positive
 nc (QScontext I ** BLnames) nest 0 old c.
Definition QStail I c := V293_OSSched_tail_state
 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive 0 16
 V293_witness_li V293_idle_tid(spec_done None)106%Z 107%Z Tvoid 8%positive 10%positive
 V293_idle_entries V293_idle_tasks 110%Z 111%Z 13%positive 14%positive 12
 (V293_rdy_raw_cells(V293_exit_cells 11%positive 12%positive 0 0)(QScontext I ** BLnames)) c.
Definition QSspec I := V293_ISR_sched_spec 200%Z 100%Z 101%Z 102%Z 103%Z
 1%positive 2%positive 3%positive 4%positive V293_witness_li I V293_witness_li_good.
Definition QSlg ci := V293_ISR_sched_call_lg 0 16(spec_done None)false(fun _=>false)nil ci.
Definition QSselected I ci := getasrt(V293_ISR_sched_fpre 100%Z 101%Z 102%Z 103%Z
 1%positive 2%positive 3%positive 4%positive V293_witness_li I V293_witness_li_good
 nil(QSlg ci)V293_idle_tid).

Lemma QSframe_good : GoodFrm BLnames.
Proof. unfold BLnames;cbn[GoodFrm];tauto. Qed.
Theorem QSpre_nonempty : forall I hv out nc nest c,
 BLstate(BLmemory hv out nest 0 nc c) |= QSpre I nc nest out c.
Proof.
 intros Inv hv out nc nest c. pose proof(BLnonempty hv out nest 0 nc c)as H.
 apply astar_l_aie_intro with(i:=false)in H;[ |reflexivity].
 apply astar_l_aisr_intro with(i:=fun _=>false)in H;[ |reflexivity].
 apply astar_l_ais_intro with(i:=nil)in H;[ |reflexivity].
 apply astar_l_acs_intro with(i:=nil)in H;[ |reflexivity].
 unfold QSpre,QScontext,V293_sched_ISR_context,BLpre,V293_exit_ready_pre in *.
 unfold V293_prefix_frame,V293_exit_cells,V293_interrupt_cells in *.
 cbn [V293_rdy_raw_cells] in *. clear -H;sep auto.
Qed.
Theorem QSselector_nonempty : forall I hv out nc nest c,
 BLstate(BLmemory hv out nest 0 nc c) |= QSselected I nil ** Atrue.
Proof.
 intros Inv hv out nc nest c. pose proof(QSpre_nonempty Inv hv out nc nest c)as H.
 change(BLstate(BLmemory hv out nest 0 nc c) |=
  V293_ISR_sched_pre 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive
   V293_witness_li Inv V293_idle_tid(QSlg nil) ** Atrue).
 unfold V293_ISR_sched_pre,QSlg.
 rewrite V293_ISR_sched_args_roundtrip by lia.
 unfold QSpre,QScontext,V293_exit_ready_pre,V293_prefix_frame,
 V293_exit_cells,V293_interrupt_cells in H.
 cbn[V293_rdy_raw_cells]in H. clear -H;sep auto.
Qed.
(* Both encodings decode; the negative control changes only logic_cs. *)
Theorem QSboth_decoders :
 V293_ISR_sched_args(QSlg nil)=Some(0,16,spec_done None,false,(fun _=>false),nil,nil) /\
 V293_ISR_sched_args(QSlg(cons true nil))=Some(0,16,spec_done None,false,(fun _=>false),nil,cons true nil).
Proof. split;apply V293_ISR_sched_args_roundtrip;lia. Qed.
Theorem QSwrong_stack : forall I hv out nc nest c,
 ~(BLstate(BLmemory hv out nest 0 nc c) |= QSselected I(cons true nil) ** Atrue).
Proof.
 intros Inv hv out nc nest c Bad.
 change(BLstate(BLmemory hv out nest 0 nc c) |=
  V293_ISR_sched_pre 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive
   V293_witness_li Inv V293_idle_tid(QSlg(cons true nil)) ** Atrue)in Bad.
 unfold V293_ISR_sched_pre,QSlg in Bad.
 rewrite V293_ISR_sched_args_roundtrip in Bad by lia.
 unfold V293_sched_ISR_context in Bad.
 assert(C:BLstate(BLmemory hv out nest 0 nc c) |= Acs(cons true nil) ** Atrue)by(sep auto).
 apply astar_l_acs_elim in C as[E _]. discriminate.
Qed.
Theorem QSenabled_same_dispatch : forall resourceI RI sd r ri old c handoff,
 InfRules (QSspec resourceI) sd V293_witness_li RI r ri (QSpre resourceI 12 1 old c)
 (V293_OSIntExit_nesting_dispatch 108%Z 109%Z
  (V293_exit_boundary_dispatch 106%Z 103%Z 107%Z 110%Z 111%Z 200%Z handoff))
 (QStail resourceI c)V293_idle_tid.
Proof.
 intros. unfold QSpre,QStail,QScontext.
 apply V293_OSIntExit_context_same_dispatch with(Hli:=V293_witness_li_good);
 try lia;try reflexivity.
 - exists 12;vm_compute;repeat split;lia.
 - exact(proj1 V293_idle_relations).
 - exact(proj2 V293_idle_relations).
 - apply QSframe_good.
 - exact BLenv.
Qed.
Theorem QSscheduler_environment : forall resourceI RI sd,
 WFFunEnv(V293_OSSchedNew_internal_unit 200%Z 100%Z 101%Z 102%Z 103%Z 104%Z)
  (QSspec resourceI)sd V293_witness_li RI.
Proof. intros;apply V293_OSSchedNew_ISR_WFFunEnv;discriminate. Qed.
Theorem QSreject_empty : forall I,
 QSselected I nil <> Afalse /\
 V293_ISR_sched_args nil=None.
Proof.
 intros Inv. split;[ |reflexivity]. intro Bad.
 pose proof(QSselector_nonempty Inv 0 Vnull 12 1 Int.zero)as H.
 rewrite Bad in H. destruct H as[? [? [? [? [? [? [? [? [? [? [F _]]]]]]]]]]]. exact F.
Qed.
