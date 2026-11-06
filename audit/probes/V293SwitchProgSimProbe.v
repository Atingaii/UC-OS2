Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.simulation.
Require Import CertiOS.certiucos.v293.proofs.V293SwitchProgSim.
Require Import CertiOS.audit.probes.V293CurrentHandoffPrefixProbe.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyStorageInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293ReadySwitchStep.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCurrentInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293CurrentHandoffPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBoundarySwitch.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyHandoff.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.audit.probes.V293OSIntExitReadyHandoffProbe.
Require Import CertiOS.audit.probes.V293ReadyCriticalGlobalProbe.
Require Import CertiOS.audit.probes.V293ReadyFullCallProbe.
Require Import CertiOS.audit.probes.V293ReadyGlobalTraceProbe.
Require Import CertiOS.audit.probes.V293ReadySwitchStepProbe.
Require Import CertiOS.audit.probes.V293ReadySchedCallProbe.
Require Import CertiOS.audit.probes.V293TaskRecordInvariantProbe.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import Coq.Lists.List.
Import ListNotations.

(* Finite terminal context only: no claim about arbitrary suspended clients. *)
Lemma SPterminal_cstep : forall p m C m',
 ~cstep p (SKIP,(kenil,kstop)) m C m'.
Proof.
 intros p m C m' H;inversion H;subst;
 match goal with
 | H:estep _ _ _ _ _ _ |- _ =>inversion H;subst;try discriminate
 | H:sstep _ _ _ _ _ _ _ |- _ =>inversion H;subst;try discriminate
 end.
Qed.
Lemma SPterminal_ltstep : forall p t cst o C cst' o',
 ~ltstep p t (SKIP,(kenil,kstop)) cst o C cst' o'.
Proof.
 intros p t cst o C cst' o' H;inversion H;subst.
 - eapply SPterminal_cstep;eassumption.
 - match goal with H:loststep _ _ _ _ _ |- _ =>inversion H;subst end;
   try discriminate;eapply SPterminal_cstep;eassumption.
Qed.
Lemma SPterminal_ltstepev : forall p t cst o C cst' o' ev,
 ~ltstepev p t (SKIP,(kenil,kstop)) cst o C cst' o' ev.
Proof.
 intros p t cst o C cst' o' ev H;inversion H;subst.
 match goal with H:cstepev _ _ _ _ _ _ |- _ =>inversion H;subst end.
 match goal with H:sstepev _ _ _ _ _ _ _ _ |- _ =>inversion H;subst;discriminate end.
Qed.
Lemma SPterminal : forall p T cst S t m ir si cs ph Th O,
 get T t=Some((SKIP,(kenil,kstop)):code) ->
 projS S t=Some(m,ir,(false,si,cs)) ->
 get O curtid=Some(oscurt t) ->
 ProgSim p T S ph Th O cst t.
Proof.
 intros p T cst S t m ir si cs ph Th O Code Projection Cur.
 apply simulation.prog_sim;[exact Cur| | | ].
 - intros T' S' cst' t' H;inversion H;subst.
   + assert(C=(SKIP,(kenil,kstop)))by congruence;subst C.
     assert(tst=(m,ir,(false,si,cs)))by congruence;subst tst.
     match goal with H:lintstep _ _ _ _ _ |- _ =>inversion H;subst;discriminate end.
   + assert(C=(SKIP,(kenil,kstop)))by congruence;subst C.
     exfalso;eapply SPterminal_ltstep;eassumption.
   + change (get T t=Some((curs(sprim(switch x)),(kenil,ks)):code))in H4.
     rewrite Code in H4;discriminate.
   + change (get T t'=Some((curs(sprim(stkinit e1 e2 e3)),(kenil,ks)):code))in H1.
     rewrite Code in H1;discriminate.
   + change (get T t'=Some((curs(sprim(stkinit e1 e2 e3)),(kenil,ks)):code))in H1.
     rewrite Code in H1;discriminate.
   + change (get T t'=Some((curs(sprim(stkfree e)),(kenil,ks)):code))in H1.
     rewrite Code in H1;discriminate.
 - intros T' S' cst' ev t' H;inversion H;subst.
   assert(C=(SKIP,(kenil,kstop)))by congruence;subst C.
   exfalso;eapply SPterminal_ltstepev;eassumption.
 - intro H;inversion H;subst.
   + assert(C=(SKIP,(kenil,kstop)))by congruence;subst C.
     exfalso;apply H5;unfold IsEnd;exists (@None val);reflexivity.
   + change (get T t=Some((curs(sprim(stkinit e1 e2 e3)),(kenil,ks)):code))in H0.
     rewrite Code in H0;discriminate.
   + change (get T t=Some((curs(sprim(stkfree e)),(kenil,ks)):code))in H0.
     rewrite Code in H0;discriminate.
   + change (get T t=Some((curs(sprim(switch x)),(kenil,ks)):code))in H0.
     rewrite Code in H0;discriminate.
Qed.

Definition SPph:hprog:=(RCprogram,((fun _=>None),(fun _=>None),V293_scheduler)).
Definition SPTh:tasks:=set GSbase OwnershipWaiting
 (curs(hapi_code(sched;;spec_done None)),(kenil,FCpending)).
Definition SPThf:tasks:=set SPTh OwnershipWaiting
 (curs(hapi_code(spec_done None)),(kenil,FCpending)).
Definition SPOf:=set(RIabstract OwnershipWaiting)curtid(oscurt OwnershipReady).
Definition SPTf:=set FCswitch_tasks OwnershipWaiting(SKIP,(kenil,FCpending)).
Definition SPS M enabled ci:osstate:=
 (CGge,CGswitch_envs,M,(fun _=>false),CGswitch_aux enabled ci).

Lemma SPschedule : forall cst,
 hpstep SPph SPTh cst(RIabstract OwnershipWaiting) SPThf cst SPOf.
Proof.
 intro cst;eapply hswi_step with(t:=OwnershipWaiting)(t':=OwnershipReady)
 (C:=(curs(hapi_code(sched;;spec_done None)),(kenil,FCpending)))
 (ke:=kenil)(ks:=FCpending)(s:=spec_done None);try reflexivity.
 - exists OwnershipTasks;split;[apply RIfixed_tasks|exact RIhighest].
Qed.
Lemma SPpost : forall Mf enabled ci cst ip,
 ProgSim(RCprogram,(CGpo,CGempty,ip)) SPTf(SPS Mf enabled ci)
 SPph SPThf SPOf cst OwnershipReady.
Proof.
 intros Mf enabled ci cst ip;eapply SPterminal with
 (m:=(CGge,emp,Mf))(ir:=fun _=>false)(si:=nil)(cs:=nil).
 - unfold SPTf,FCswitch_tasks,GSbase;rewrite !map_get_set' by discriminate;apply map_get_sig.
 - unfold SPS,projS,projD,CGswitch_envs,GSenvs,CGswitch_aux,RSaux;cbn.
   rewrite !map_get_set' by discriminate;rewrite !map_get_sig;reflexivity.
 - unfold SPOf;apply map_get_set.
Qed.
Lemma SPbridge : forall M Mf enabled ci cst ip,
 load(Tptr V293_tcb_type)M(93%positive,0%Z)=Some(Vptr OwnershipReady) ->
 store(Tptr V293_tcb_type)M(1%positive,0%Z)(Vptr OwnershipReady)=Some Mf ->
 ProgSim(RCprogram,(CGpo,CGempty,ip)) FCswitch_tasks(SPS M enabled ci)
 SPph SPTh(RIabstract OwnershipWaiting)cst OwnershipWaiting.
Proof.
 intros M Mf enabled ci cst ip Read Store.
 eapply V293_switch_progsim with(le:=CGle)(bt:=93%positive)(bc:=1%positive)
 (tp:=V293_tcb_type)(x:=106%Z)(ks:=FCpending)(Mf:=Mf)
 (si:=nil)(cs:=enabled::ci)(Thf:=SPThf)(Of:=SPOf);try reflexivity;try eassumption.
 - eapply hp_stepS;[apply SPschedule|apply hp_stepO].
 - apply SPpost.
Qed.

(* The concrete store is constructed from owned records, not presumed. The
   actual-copy context has CGpending; the physical-switch context FCpending.
   They share exactly the same heap, not an asserted whole-program trace. *)
Theorem SPactual_copy_simulation : forall enabled ci ip cst,
 exists M Mc Mf,
 cstepstar CGprogram(curs(V293_interrupt_handoff 103%Z 108%Z 106%Z),(kenil,CGpending))(CGge,CGle,M)
 (curs(sprim(switch 106%Z)),(kenil,CGpending))(CGge,CGle,Mc) /\
 (forall R,~CGstate OwnershipWaiting Mc(enabled::ci)|=SWINVt GHinv OwnershipWaiting ** R) /\
 JHswitch_result Mc Mf enabled ci ip cst /\
 hpstep SPph SPTh cst(RIabstract OwnershipWaiting)SPThf cst SPOf /\
 ProgSim(RCprogram,(CGpo,CGempty,ip))FCswitch_tasks(SPS Mc enabled ci)
 SPph SPTh(RIabstract OwnershipWaiting)cst OwnershipWaiting.
Proof.
 intros enabled ci ip cst.
 destruct(GHactual_copy_obstruction enabled ci)as(M&Mc&Copy&Store&Outside&Old&New&OldCopy&Reject&Guard&NoGuard&Read&ReadCopy&Target).
 destruct(V293_ready_storage_switch_step 80%positive 81%positive 82%positive 106%Z V293_tcb_type JHcells
 RCprogram CGpo CGempty ip FCswitch_tasks cst FCpending OwnershipWaiting OwnershipReady
 93%positive 1%positive CGge CGle CGswitch_envs Mc(fun _=>false)(false,nil,enabled::ci)
 (CGswitch_aux enabled ci)(RIabstract OwnershipWaiting)(spec_done None)JHprivate
 (map_get_set _ _ _)(map_get_set _ _ _)(map_get_set _ _ _)eq_refl Target eq_refl OldCopy)
 as(Mf&Step&PhysicalStore&After&Current&Frame).
 exists M;exists Mc;exists Mf;split;[exact Copy| ];split;[exact Reject| ];split.
 - split;assumption.
 - split;[apply SPschedule| ];eapply SPbridge;eassumption.
Qed.

(* Single-factor control: keep the post physical state and task maps, but
   omit the high current-task update. The required post simulation is false. *)
Theorem SPzero_high_match_rejected : forall Mf enabled ci ip cst,
 ~ProgSim(RCprogram,(CGpo,CGempty,ip))SPTf(SPS Mf enabled ci)
 SPph SPThf(RIabstract OwnershipWaiting)cst OwnershipReady.
Proof.
 intros Mf enabled ci ip cst H;inversion H.
 assert(get(RIabstract OwnershipWaiting)curtid=Some(oscurt OwnershipWaiting))by reflexivity.
 assert(OwnershipReady=OwnershipWaiting)by congruence;discriminate.
Qed.
