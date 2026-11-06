(* Independent nonempty full-body entry and an assignment-boundary control. *)
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitNondispatch.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPrefix.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBoundarySwitch.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitResourceBridge.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitResourceCodec.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.audit.probes.V293OSIntExitResourceCodecProbe.
Require Import CertiOS.audit.probes.V293OSIntExitBuildersProbe.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitSamePriority.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedISRContext.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.code.V293OSIntExit.
Require Import CertiOS.audit.probes.V293OSSchedISRContextProbe.

Definition QPdata := V293_exit_same_data
 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive 0 16
 V293_witness_li V293_idle_tid 106%Z 107%Z Tvoid 8%positive 10%positive
 V293_idle_entries V293_idle_tasks 110%Z 111%Z 112%Z 120%Z
 13%positive 14%positive 16%positive 11%positive 12%positive 15%positive 12 BLnames.
Definition QPout := V293_exit_same_result
 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive 0 16
 V293_witness_li V293_idle_tid 106%Z 107%Z Tvoid 8%positive 10%positive
 V293_idle_entries V293_idle_tasks 110%Z 111%Z 112%Z 120%Z
 13%positive 14%positive 16%positive 11%positive 12%positive 15%positive 12 BLnames.
Definition QPstate enabled si ci nest c old : RstateOP :=
 (BLge,BLle,RCbigmemory 12 nest c 1 old,(fun _=>false),
  (enabled,si,ci),V293_target_fixture_abs,spec_done None).
Definition QPpre enabled si ci nest c old :=
 EX hv:val,<||spec_done None||> ** OS[(fun _=>false),enabled,si,ci] **
 QPdata nest hv Vnull c old.
Lemma QPdata_owned : forall nest c old,
 RCbigstate 12 nest c 1 old |= EX hv:val,QPdata nest hv Vnull c old.
Proof.
 intros nest c old. pose proof(RCbig_owned 12 nest c 1 old)as Held.
 unfold RCshared,V293_exit_snapshot_pre,V293_exit_physical_pre,
 V293_sched_internal_pre,V293_sched_internal_resource in Held.
 unfold QPdata,V293_exit_same_data,V293_exit_same_core,BLnames,BLbindings,
 V293_exit_caller_bindings,V293_exit_guard_bindings,V293_prefix_frame in *.
 unfold V293_exit_cells,V293_interrupt_cells in *.
 cbn [RCsnapshot V293_xlo V293_xhi V293_xnest V293_xlocked V293_xold
 V293_xcounter V293_xcurrent V293_xentries V293_xtasks V293_xaop V293_rdy_raw_cells] in *.
 unfold V293_time_cell,V293_time_binding,V293_guard_cell,V293_counter_cell,
 V293_counter_bindings in *.
 sep normal in Held. destruct Held as[hv Held]. exists hv.
 sep lift 6 in Held;apply astar_l_aop'_elim in Held as[_ Held].
 sep lift 9 in Held;apply astar_l_aie_elim in Held as[_ Held].
 ssplit_apure_in Held;sclearemp_in Held.
 sep rearr in Held with (1::2::4::5::3::19::17::18::6::7::8::9::20::10::11::12::13::14::15::16::nil).
 sep normal. exact Held.
Qed.
Theorem QPpre_nonempty : forall enabled si ci nest c old,
 QPstate enabled si ci nest c old |= QPpre enabled si ci nest c old.
Proof.
 intros enabled si ci nest c old.
 assert(Data:QPstate enabled si ci nest c old |= EX hv:val,QPdata nest hv Vnull c old).
 { eapply goodfrm_prop.
   - intro hv;unfold QPdata. apply V293_exit_same_data_good;[apply V293_witness_li_good|apply QSframe_good].
   - exact(QPdata_owned nest c old). }
 destruct Data as[hv Data]. unfold QPpre. exists hv. apply astar_l_aop'_intro;[ |reflexivity].
 apply astar_l_aie_intro with(i:=enabled)in Data;[ |reflexivity].
 apply astar_l_ais_intro with(i:=si)in Data;[ |reflexivity].
 apply astar_l_aisr_intro with(i:=fun _=>false)in Data;[ |reflexivity].
 apply astar_l_acs_intro with(i:=ci)in Data;[ |reflexivity].
 clear -Data;sep auto.
Qed.
Theorem QPbody : forall sd I enabled si ci nest c old,
 (gettopis si<=INUM)%nat -> nest<=1 ->
 InfRules(QSspec I)sd V293_witness_li I
 (fun result=>[|result=None|] **
 (<||spec_done None||> ** OS[(fun _=>false),enabled,si,ci] ** QPout c(Vint32 Int.zero))) Afalse
 (QPpre enabled si ci nest c old)
 (V293_exit_boundary_body 112%Z 108%Z 109%Z 120%Z 106%Z 103%Z 107%Z 110%Z
 111%Z 200%Z(V293_interrupt_handoff 103%Z 110%Z 107%Z)) Afalse V293_idle_tid.
Proof.
 intros. unfold QPpre,QPdata,QPout. apply ex_intro_rule;intro hv.
 apply V293_OSIntExit_same_priority_body with(Hli:=V293_witness_li_good);
 try assumption;try lia;try reflexivity.
 - exists 12;vm_compute;repeat split;lia.
 - exact(proj1 V293_idle_relations).
 - exact(proj2 V293_idle_relations).
 - exact QSframe_good.
 - exact BLenv.
Qed.
Theorem QPboth_ie_and_nonempty_stacks :
 QPstate true (cons 0 nil)(cons false nil) 1 Int.one(Vint32 Int.one) |=
  QPpre true (cons 0 nil)(cons false nil) 1 Int.one(Vint32 Int.one) /\
 QPstate false (cons 0 nil)(cons false nil) 1 Int.one(Vint32 Int.one) |=
  QPpre false (cons 0 nil)(cons false nil) 1 Int.one(Vint32 Int.one).
Proof. split;apply QPpre_nonempty. Qed.

(* This pair checks the saved assignment only, not two full executions. *)
Theorem QPzero : forall Spec sd I r ri old,
 InfRules Spec sd V293_witness_li I r ri
 (<||spec_done None||> ** (V293_time_cell true 120%Z 15%positive old **
 CurLINV V293_witness_li V293_idle_tid))
 (sassign(evar 120%Z)(econst32 Int.zero))
 (<||spec_done None||> ** (V293_time_cell true 120%Z 15%positive(Vint32 Int.zero) **
 CurLINV V293_witness_li V293_idle_tid)) V293_idle_tid.
Proof. intros;apply V293_time_zero;intros s H;exact H. Qed.
Lemma QPsaved_read : forall enabled si ci nest c v s,
 s |= QPpre enabled si ci nest c(Vint32 v) ->
 evalval(evar 120%Z)(getsmem s)=Some(Vint32 v).
Proof.
 intros enabled si ci nest c v s [hv H].
 assert(C:s |= V293_time_cell true 120%Z 15%positive(Vint32 v) ** Atrue).
 { unfold QPdata,V293_exit_same_data in H;clear -H;sep auto. }
 exact(proj1(V293_time_cell_read true 120%Z 15%positive v Atrue s C)).
Qed.
Theorem QPwithout_zero : forall enabled si ci nest c,
 ~(QPstate enabled si ci nest c(Vint32 Int.one) |=
 QPpre enabled si ci nest c(Vint32 Int.zero)).
Proof.
 intros enabled si ci nest c Bad.
 pose proof(QPsaved_read _ _ _ _ _ _ _ Bad)as Wrong.
 pose proof(QPsaved_read _ _ _ _ _ _ _(QPpre_nonempty enabled si ci nest c(Vint32 Int.one)))as Actual.
 rewrite Actual in Wrong;discriminate.
Qed.
