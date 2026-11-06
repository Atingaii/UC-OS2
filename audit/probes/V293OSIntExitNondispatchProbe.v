(* Concrete nonempty assertions and an explicitly tail-only ablation. *)
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitNondispatch.
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

Definition QNframe := BLnames ** (CurLINV V293_witness_li V293_idle_tid ** Atrue).
Lemma QNframe_good : GoodFrm QNframe.
Proof.
 unfold QNframe,BLnames,CurLINV,CurTid,LINV,V293_witness_li,Agvarmapsto.
 cbn [GoodFrm]. firstorder.
Qed.
Lemma QNframe_local : QNframe ==> CurLINV V293_witness_li V293_idle_tid.
Proof. apply V293_star_CurLINV_r. apply V293_star_CurLINV_l. intros s H;exact H. Qed.
Lemma QNframe_env : forall st, st |= QNframe ->
 V293_interrupt_env 108%Z 109%Z 11%positive 12%positive (getgenv st)(getlenv st).
Proof. eapply V293_star_env_l;exact BLenv. Qed.
Definition QNdata run nest old :=
 V293_exit_quiet_data 112%Z 16%positive run 11%positive 12%positive nest 0
 120%Z 15%positive old QNframe.
Definition QNstate enabled si ci run nest old : RstateOP :=
 (BLge,BLle,RCbigmemory 0 nest Int.zero run old,(fun _=>false),
  (enabled,si,ci),V293_target_fixture_abs,spec_done None).

Lemma QNdata_owned : forall run nest old,
 RCbigstate 0 nest Int.zero run old |= QNdata run nest old.
Proof.
 intros run nest old. pose proof(RCbig_owned 0 nest Int.zero run old)as Held.
 unfold RCshared,V293_exit_snapshot_pre,V293_exit_physical_pre,
 V293_sched_internal_pre,V293_sched_internal_resource in Held.
 unfold QNdata,V293_exit_quiet_data,QNframe,BLnames,BLbindings,
 V293_exit_caller_bindings,V293_exit_guard_bindings in *.
 unfold V293_exit_cells,V293_interrupt_cells in *.
 cbn [RCsnapshot V293_xlo V293_xhi V293_xnest V293_xlocked V293_xold
 V293_xcounter V293_xcurrent V293_xentries V293_xtasks V293_xaop V293_rdy_raw_cells] in *.
 unfold V293_time_cell,V293_time_binding. clear -Held. sep auto.
Qed.
Theorem QNpre_nonempty : forall enabled si ci run nest old,
 QNstate enabled si ci run nest old |=
 <||spec_done None||> ** OS[(fun _=>false),enabled,si,ci] ** QNdata run nest old.
Proof.
 intros enabled si ci run nest old.
 assert(Data: QNstate enabled si ci run nest old |= QNdata run nest old).
 { eapply goodfrm_prop.
   - unfold QNdata. apply V293_exit_quiet_good;apply QNframe_good.
   - exact(QNdata_owned run nest old). }
 apply astar_l_aop'_intro;[ |reflexivity].
 apply astar_l_aie_intro with(i:=enabled)in Data;[ |reflexivity].
 apply astar_l_ais_intro with(i:=si)in Data;[ |reflexivity].
 apply astar_l_aisr_intro with(i:=fun _=>false)in Data;[ |reflexivity].
 apply astar_l_acs_intro with(i:=ci)in Data;[ |reflexivity].
 clear -Data;sep auto.
Qed.

(* Same actual normalized function, arbitrary Spec and ambient I. No call
   contract is consulted on these paths. Local bytes remain allocated. *)
Theorem QNbody : forall Spec sd I enabled si ci run nest old,
 (gettopis si<=INUM)%nat -> run<256 -> nest<256 -> (run=1 -> 2<=nest) ->
 InfRules Spec sd V293_witness_li I
 (fun result => [|result=None|] **
 (<||spec_done None||> ** OS[(fun _=>false),enabled,si,ci] **
 QNdata run (V293_exit_quiet_depth run nest)(Vint32 Int.zero))) Afalse
 (<||spec_done None||> ** OS[(fun _=>false),enabled,si,ci] ** QNdata run nest old)
 (V293_exit_boundary_body 112%Z 108%Z 109%Z 120%Z 106%Z 103%Z 107%Z 110%Z
 111%Z 200%Z (V293_interrupt_handoff 103%Z 110%Z 107%Z)) Afalse V293_idle_tid.
Proof.
 intros. apply V293_OSIntExit_nondispatch_body;try assumption;try lia.
 - apply QNframe_good.
 - apply QNframe_local.
 - exact QNframe_env.
Qed.
Theorem QNdepth_cases :
 V293_exit_quiet_depth 1 2=1 /\ V293_exit_quiet_depth 1 255=254 /\
 V293_exit_quiet_depth 0 1=1 /\ V293_exit_quiet_depth 2 255=255.
Proof. repeat split;reflexivity. Qed.

(* Only the final primitive is removed: both sides have the same memory,
   ISR and pushed stack. This does not compare two full-body executions. *)
Theorem QNtail_exit : forall P ks ge le M ir enabled si ci,
 loststep P (curs(sprim excrit),(kenil,ks))
 ((ge,le,M),ir,(false,si,enabled::ci))
 (curs(sskip None),(kenil,ks)) ((ge,le,M),ir,(enabled,si,ci)).
Proof. intros;apply excrit_step;reflexivity. Qed.
Theorem QNtail_without_exit : forall ge le M ir enabled si ci O aop,
 ~((ge,le,M,ir,(false,si,enabled::ci),O,aop) |=
   OS[ir,enabled,si,ci] ** Atrue).
Proof.
 intros ge le M ir enabled si ci O aop Bad.
 assert(C: (ge,le,M,ir,(false,si,enabled::ci),O,aop) |= Acs ci ** Atrue)by(sep auto).
 apply astar_l_acs_elim in C as [E _].
 change (enabled::ci=ci) in E.
 apply(f_equal(@length bool))in E;cbn in E;lia.
Qed.
Theorem QNtail_both_ie : forall P ks ge le M ir si ci,
 loststep P (curs(sprim excrit),(kenil,ks)) ((ge,le,M),ir,(false,si,true::ci))
  (curs(sskip None),(kenil,ks)) ((ge,le,M),ir,(true,si,ci)) /\
 loststep P (curs(sprim excrit),(kenil,ks)) ((ge,le,M),ir,(false,si,false::ci))
  (curs(sskip None),(kenil,ks)) ((ge,le,M),ir,(false,si,ci)).
Proof. intros;split;apply QNtail_exit. Qed.
