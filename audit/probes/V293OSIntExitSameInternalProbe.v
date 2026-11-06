(* Actual builders of the accepted normalized function, not the raw CPU-call
   implementation. The contract covers the running, same-priority path only. *)
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitSamePriority.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBuilders.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitResourceBridge.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCall.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitResourceCodec.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedISRContext.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.code.V293OSIntExit.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitNondispatch.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBody.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickDelayHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitDispatch.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBoundarySwitch.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptExitEnvironment.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptFunctionEnvironment.
Require Import CertiOS.certiucos.v293.code.V293OSIntEnter.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.framework.proof.toptheorem.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitSameInternal.
Require Import CertiOS.audit.probes.V293OSIntExitSamePriorityProbe.
Require Import CertiOS.audit.probes.V293OSIntExitResourceCodecProbe.
Require Import CertiOS.audit.probes.V293OSIntExitBuildersProbe.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.framework.proof.rulesoundlib.
Definition BIprogram := V293_exit_env_unit 300%Z 301%Z 200%Z
 112%Z 108%Z 100%Z 101%Z 102%Z 103%Z 104%Z 120%Z
 (V293_exit_boundary_body 112%Z 108%Z 109%Z 120%Z 106%Z 103%Z 107%Z 110%Z
 111%Z 200%Z(V293_interrupt_handoff 103%Z 110%Z 107%Z)).
Definition BIfp := V293_same_exit_fpre
 100%Z 101%Z 102%Z 103%Z 106%Z 107%Z 110%Z 111%Z 108%Z 109%Z 112%Z
 1%positive 2%positive 3%positive 4%positive 8%positive 10%positive
 13%positive 14%positive 11%positive 12%positive 16%positive
 Tvoid V293_witness_li Aemp V293_witness_li_good Logic.I.
Definition BIfq := V293_same_exit_fpost
 100%Z 101%Z 102%Z 103%Z 106%Z 107%Z 110%Z 111%Z 108%Z 109%Z 112%Z
 1%positive 2%positive 3%positive 4%positive 8%positive 10%positive
 13%positive 14%positive 11%positive 12%positive 16%positive
 Tvoid V293_witness_li Aemp V293_witness_li_good Logic.I.
Definition BIspec I := V293_same_exit_env_spec
 100%Z 101%Z 102%Z 103%Z 106%Z 107%Z 110%Z 111%Z 108%Z 109%Z 112%Z
 1%positive 2%positive 3%positive 4%positive 8%positive 10%positive
 13%positive 14%positive 11%positive 12%positive 16%positive
 Tvoid V293_witness_li Aemp V293_witness_li_good Logic.I I 300%Z 301%Z 200%Z.
Definition BIpre lg t := V293_exit_builder_cells 120%Z **
 getasrt(BIfp nil lg t) ** V293_exit_builder_domain 120%Z.
Definition BIpost lg t r := V293_exit_builder_cells 120%Z **
 getasrt(BIfq nil r lg t) ** V293_exit_builder_domain 120%Z.
Lemma BIbuilders : forall lg t,
 BuildPreI BIprogram 300%Z nil lg BIfp t=Some(BIpre lg t) /\
 BuildRetI BIprogram 300%Z nil lg BIfq t=Some(BIpost lg t).
Proof. intros;split;reflexivity. Qed.
Theorem BIenvironment : forall sd I,
 WFFunEnv BIprogram(BIspec I)sd V293_witness_li I /\
 WFIFun BIprogram(BIspec I)sd I V293_witness_li.
Proof.
 intros;split;unfold BIprogram,BIspec.
 - apply V293_same_exit_env_WFFunEnv;try discriminate;exact Logic.I.
 - apply V293_same_exit_env_WFIFun;try discriminate;exact Logic.I.
Qed.
Definition BIlogic enabled := V293_same_exit_args enabled(fun _=>false)
 (cons 0 nil)(cons false nil)(RCsnapshot 12 1 Int.one).
Lemma BIvalid : V293_same_exit_valid(cons 0 nil)(RCsnapshot 12 1 Int.one).
Proof.
 unfold V293_same_exit_valid,V293_exit_snapshot_bounded,RCsnapshot;
 cbn[V293_xlo V293_xhi V293_xnest V293_xlocked V293_xcurrent V293_xentries V293_xtasks].
 split;[cbn[gettopis];lia| ].
 split;[repeat split;lia| ].
 split;[lia| ]. split;[reflexivity| ].
 split;[exists 12;vm_compute;repeat split;lia| ].
 split;[exact(proj1 V293_idle_relations)| ].
 split;[exact(proj2 V293_idle_relations)|reflexivity].
Qed.
Lemma BIdecode : forall enabled,
 V293_same_exit_index(BIlogic enabled)=Some(enabled,(fun _=>false),
 (cons 0 nil),(cons false nil),RCsnapshot 12 1 Int.one).
Proof. intro;apply V293_same_exit_index_roundtrip;exact(proj1(proj2 BIvalid)). Qed.
Definition BImemory := V293_same_exit_memory
 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive
 8%positive 10%positive 13%positive 14%positive 11%positive 12%positive Tvoid V293_witness_li.
Definition BIglobals := V293_exit_builder_globals
 106%Z 107%Z 110%Z 111%Z 108%Z 109%Z 112%Z Tvoid
 8%positive 10%positive 13%positive 14%positive 11%positive 12%positive 16%positive.
Lemma BIowned : forall enabled si ci nest c old,
 QPstate enabled si ci nest c old |=
 EX hv:val,V293_exit_builder_cells 120%Z **
 (<||spec_done None||> ** OS[(fun _=>false),enabled,si,ci] **
 (BImemory 0 16 V293_idle_entries V293_idle_tasks 12 nest hv Vnull c V293_idle_tid **
 (BIglobals ** (Amapsto(16%positive,0%Z)Tint8 false(V293_byteval 1) ** Aemp)))) **
 V293_exit_builder_domain 120%Z.
Proof.
 intros enabled si ci nest c old.
 pose proof(QPpre_nonempty enabled si ci nest c old)as Held.
 unfold QPpre in Held;destruct Held as[hv Held];exists hv.
 apply astar_l_adomlenv_intro with(d:=cons(120%Z,Tint32)nil)in Held;
 [ |exact BLdomain].
 assert(U:QPstate enabled si ci nest c old |=
 (BLbindings ** (Agvarenv 112%Z Tint8(16%positive,0%Z) //\\ A_notin_lenv 112%Z)) **
 (V293_exit_builder_cells 120%Z ** <||spec_done None||> ** OS[(fun _=>false),enabled,si,ci] **
 (BImemory 0 16 V293_idle_entries V293_idle_tasks 12 nest hv Vnull c V293_idle_tid **
 (Amapsto(16%positive,0%Z)Tint8 false(V293_byteval 1) ** V293_exit_builder_domain 120%Z)))).
 { unfold QPdata,V293_exit_same_data,V293_exit_same_core,BImemory,V293_same_exit_memory,
   V293_time_cell,V293_time_binding,V293_guard_cell,V293_counter_cell,V293_prefix_frame,
   V293_exit_builder_cells,Alvarmapsto,Alvarenv',Aptrmapsto in *.
   unfold V293_exit_cells,V293_interrupt_cells in *;cbn[V293_rdy_raw_cells]in *.
   unfold BLbindings,V293_exit_caller_bindings,BLnames,V293_exit_guard_bindings in *.
   sep normal in Held. sep normal. exists old;exists 15%positive.
   unfold V293_exit_builder_domain in *;cbn[addrval_to_addr]in *.
   sep rearr in Held with(2::3::4::1::11::12::18::25::6::7::8::9::10::14::15::16::17::19::20::21::22::23::24::26::13::5::nil).
   exact Held. }
 eapply astar_mono in U.
 2:{ apply V293_exit_builder_forget_names. }
 2:{ intros st Hst;exact Hst. }
 unfold BIglobals. clear -U;sep auto.
Qed.
Theorem BIpre_nonempty : forall enabled,
 QPstate enabled(cons 0 nil)(cons false nil)1 Int.one(Vint32 Int.one) |=
 BIpre(BIlogic enabled)V293_idle_tid.
Proof.
 intro enabled. pose proof(BIowned enabled(cons 0 nil)(cons false nil)1 Int.one(Vint32 Int.one))as Held.
 destruct Held as[hv Held].
 unfold BIpre,BIfp,V293_same_exit_fpre,getasrt,V293_same_exit_pre.
 rewrite BIdecode. cbn[V293_xlo V293_xhi V293_xcurrent V293_xnest V293_xold
 V293_xcounter V293_xentries V293_xtasks V293_xaop RCsnapshot].
 assert(U:QPstate enabled(cons 0 nil)(cons false nil)1 Int.one(Vint32 Int.one) |=
 V293_exit_builder_cells 120%Z **
 (EX v:val,V293_same_exit_external
 100%Z 101%Z 102%Z 103%Z 106%Z 107%Z 110%Z 111%Z 108%Z 109%Z 112%Z
 1%positive 2%positive 3%positive 4%positive 8%positive 10%positive
 13%positive 14%positive 11%positive 12%positive 16%positive Tvoid V293_witness_li Aemp
 enabled(fun _=>false)(cons 0 nil)(cons false nil)0 16 V293_idle_entries V293_idle_tasks
 12 1 v Vnull Int.one(spec_done None)V293_idle_tid) ** V293_exit_builder_domain 120%Z).
 { unfold V293_same_exit_external,BIglobals,BImemory in *;clear -Held;sep auto. }
 assert(Valid:V293_same_exit_valid(cons 0 nil)(RCsnapshot 12 1 Int.one))by exact BIvalid.
 clear -U Valid;sep auto.
Qed.
(* Only the logical IE field changes; both snapshots decode and are valid.
   This is an assertion identity control, not two complete program executions. *)
Theorem BIie_control :
 (QPstate true(cons 0 nil)(cons false nil)1 Int.one(Vint32 Int.one) |=
 BIpre(BIlogic true)V293_idle_tid) /\
 ~(QPstate true(cons 0 nil)(cons false nil)1 Int.one(Vint32 Int.one) |=
 BIpre(BIlogic false)V293_idle_tid).
Proof.
 split;[apply BIpre_nonempty| ]. intro Bad.
 unfold BIpre,BIfp,V293_same_exit_fpre,getasrt,V293_same_exit_pre in Bad.
 rewrite BIdecode in Bad.
 assert(IE:QPstate true(cons 0 nil)(cons false nil)1 Int.one(Vint32 Int.one) |= Aie false ** Atrue).
 { unfold V293_same_exit_external in Bad;clear -Bad;sep auto. }
 apply astar_l_aie_elim in IE as[E _]. discriminate.
Qed.
Theorem BIarity_control : forall lg t,
 BuildPreI BIprogram 300%Z(cons(Vint32 Int.zero)nil)lg BIfp t=None.
Proof. intros;reflexivity. Qed.
(* Return construction does not check the formal argument count. *)
Lemma BIreturn_arity_observation : forall lg t,
 BuildRetI BIprogram 300%Z(cons(Vint32 Int.zero)nil)lg BIfq t=Some(BIpost lg t).
Proof. intros;reflexivity. Qed.
