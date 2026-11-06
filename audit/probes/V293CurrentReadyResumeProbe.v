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

Require Import CertiOS.certiucos.v293.proofs.V293CurrentReadyResume.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.audit.probes.V293ReadyCurrentInvariantProbe.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Logic.Classical_Prop Lia.
Local Open Scope nat_scope.

(* The target code and saved auxiliary state are unrestricted except for
   the framework's interrupt-stack well-formedness. *)
Definition CRtasks (Cl:code):tasks:=set(sig OwnershipReady Cl)OwnershipWaiting
 (curs(sprim(switch 106%Z)),(kenil,CGpending)).
Definition CRaux enabled ci ie si cs:ltaskstset:=
 set(sig OwnershipReady (ie,si,cs))OwnershipWaiting(false,nil,enabled::ci).
Definition CRS M enabled ci ie si cs:osstate:=
 (CGge,CGswitch_envs,M,empisr,CRaux enabled ci ie si cs).
Definition CRold M enabled ci:taskst:=(CGge,CGle,M,empisr,(false,nil,enabled::ci)).
Definition CRnew M ie si cs:taskst:=(CGge,emp,M,empisr,(ie,si,cs)).
Definition CRabs:=set(RIabstract OwnershipWaiting)curtid(oscurt OwnershipReady).

Lemma CRempty_INV : forall ge le ir cs ab,
 (ge,le,(emp:mem),ir,(false,nil,cs),(emp:osabst),ab)|=INV JHinv.
Proof.
 intros;unfold INV;change((ge,le,(emp:mem),ir,(false,nil,cs),(emp:osabst),ab)|=
 Aemp ** (inv_ieon JHinv \\// inv_ieoff JHinv)).
 apply astar_l_aemp_intro;right;unfold inv_ieoff.
 apply sat_split';exists(emp:mem);exists(emp:mem);exists(emp:osabst);exists(emp:osabst).
 split;[apply map_join_emp| ];split;[apply map_join_emp| ];split;[repeat split;reflexivity| ].
 exists INUM;apply sat_split';exists(emp:mem);exists(emp:mem);exists(emp:osabst);exists(emp:osabst).
 split;[apply map_join_emp| ];split;[apply map_join_emp| ];split;[repeat split;reflexivity| ].
 right;repeat split;reflexivity.
Qed.

Lemma CRprojections : forall M enabled ci ie si cs,
 projS(CRS M enabled ci ie si cs)OwnershipWaiting=Some(CRold M enabled ci) /\
 projS(CRS M enabled ci ie si cs)OwnershipReady=Some(CRnew M ie si cs).
Proof. intros;split;reflexivity.
Qed.

Lemma CRgood : forall M enabled ci ie si cs,
 good_is si ->good_is_S(CRS M enabled ci ie si cs).
Proof.
 intros M enabled ci ie si cs Good t o H.
 destruct(classic(t=OwnershipWaiting))as[->|NW].
 - rewrite(proj1(CRprojections M enabled ci ie si cs))in H;inversion H;exact I.
 - destruct(classic(t=OwnershipReady))as[->|NR].
   + rewrite(proj2(CRprojections M enabled ci ie si cs))in H;inversion H;exact Good.
   + unfold CRS,projS,projD,CGswitch_envs in H;cbn in H.
     rewrite map_get_set' in H by congruence.
     unfold GSenvs in H;rewrite map_get_sig' in H by congruence;discriminate.
Qed.

Lemma CRabstract_frame : forall ge le M ir aux Ol Op,
 (ge,le,M,ir,aux,Ol,spec_done None)|=SWINVt JHinv OwnershipReady ->
 join Ol Op CRabs ->Ol=CRabs /\ Op=emp.
Proof.
 intros ge le M ir aux Ol Op Held JO.
 assert(Shared:(ge,le,M,ir,aux,Ol,spec_done None)|=V293_shared_core ** Atrue).
 { unfold SWINVt in Held.
   eapply astar_mono in Held;[ |apply V293_ready_storage_switch_open|intros st K;exact K].
   unfold V293_ready_storage_core,V293_ready_core,V293_shared_ready_records in Held.
   sep normal in Held;sep destruct Held.
   unfold V293_shared_core;sep eexists;sep auto. }
 assert(Empty:Op=emp)by(eapply V293_shared_no_abstract_frame;[exact Shared|exact JO]).
 subst Op;apply map_join_emp' in JO;split;[exact JO|reflexivity].
Qed.

Theorem CRactual_transfer : forall enabled ci ie si cs Cl ip cst,
 good_is si ->exists M Mc Mf Mr Ms Or Os Mp,
 cstepstar CGprogram(curs(V293_interrupt_handoff 103%Z 108%Z 106%Z),(kenil,CGpending))(CGge,CGle,M)
 (curs(sprim(switch 106%Z)),(kenil,CGpending))(CGge,CGle,Mc) /\
 (forall R,~CGstate OwnershipWaiting Mc(enabled::ci)|=SWINVt GHinv OwnershipWaiting ** R) /\
 lpstep(RCprogram,(CGpo,CGempty,ip))(CRtasks Cl)cst(CRS Mc enabled ci ie si cs)OwnershipWaiting
 (set(CRtasks Cl)OwnershipWaiting(SKIP,(kenil,CGpending)))cst(CRS Mf enabled ci ie si cs)OwnershipReady /\
 disjoint Mr Ms /\ disjoint(merge Mr Ms)Mp /\
 merge(merge Mr Ms)Mp=Mf /\
 disjoint Or Os /\ merge Or Os=CRabs /\
 (substaskst(CRold Mf enabled ci)Mp,emp,spec_done None)|=JHprivate /\
 (forall ab,(substaskst(CRnew Mf ie si cs)Ms,Os,ab)|=INV GHinv) /\
 (forall ab,(substaskst(CRnew Mf ie si cs)Mr,Or,ab)|=RDYINV GHinv OwnershipReady).
Proof.
 intros enabled ci ie si cs Cl ip cst Good.
 destruct(GHactual_copy_obstruction enabled ci)as(M&Mc&Copy&Store&Outside&Old&New&OldCopy&Reject&Guard&NoGuard&Read&ReadCopy&Target).
 destruct(V293_ready_storage_switch_step 80%positive 81%positive 82%positive 106%Z V293_tcb_type JHcells
 RCprogram CGpo CGempty ip(CRtasks Cl)cst CGpending OwnershipWaiting OwnershipReady
 93%positive 1%positive CGge CGle CGswitch_envs Mc empisr(false,nil,enabled::ci)
 (CRaux enabled ci ie si cs)(RIabstract OwnershipWaiting)(spec_done None)JHprivate
 (map_get_set _ _ _)(map_get_set _ _ _)(map_get_set _ _ _)eq_refl Target eq_refl OldCopy)
 as(Mf&Step&PhysicalStore&After&Current&Frame).
 apply sat_split in After;destruct After as(Ma&Mp&Oa&Op&JM&JO&Switch&Private).
 change(join Oa Op CRabs)in JO.
 destruct(CRabstract_frame _ _ _ _ _ _ _ Switch JO)as[EA EP];subst Oa Op.
 assert(SwitchAll:forall ab,(substaskst(CRold Mf enabled ci)Ma,CRabs,ab)|=SWINVt JHinv OwnershipReady).
 { intro ab;unfold CRold;cbn[substaskst];eapply swinv_aop_irev;exact Switch. }
 assert(High:sched_self V293_scheduler CRabs).
 { apply SCafter_sched;apply RIfixed_tasks. }
 assert(DM:disjoint Ma(emp:mem))by(apply disjoint_emp_l).
 assert(DO:disjoint CRabs(emp:osabst))by(apply disjoint_emp_l).
 destruct(V293_current_ready_transfer 80%positive 81%positive 82%positive 106%Z V293_tcb_type JHcells 94%positive
 (CRold Mf enabled ci)(CRnew Mf ie si cs)CRabs emp emp Ma OwnershipWaiting OwnershipReady
 (CRS Mf enabled ci ie si cs)eq_refl(CRgood _ _ _ _ _ _ Good)DO DM
 (CRempty_INV CGge CGle empisr(enabled::ci))SwitchAll High
 (proj1(CRprojections _ _ _ _ _ _))(proj2(CRprojections _ _ _ _ _ _)))
 as(Mr&Ms&Or&Os&DMS&EM&DOS&EO&Inv&Ready).
 assert(Total:merge Mr Ms=Ma)by(rewrite EM;apply jl_merge_emp).
 exists M;exists Mc;exists Mf;exists Mr;exists Ms;exists Or;exists Os;exists Mp.
 split;[exact Copy| ];split;[exact Reject| ];split;[exact Step| ];split;[exact DMS| ];split.
 - rewrite Total;exists Mf;exact JM.
 - split.
   + rewrite Total;apply join_merge in JM;symmetry;exact JM.
   + split;[exact DOS| ];split;[rewrite EO;apply jl_merge_emp| ];split;[exact Private| ];split;assumption.
Qed.

Definition CRnonterminal:code:=(curs(sseq(sskip None)(sskip None)),(kenil,kstop)).
Lemma CRnonterminal_progress : forall p m,
 ~IsEnd CRnonterminal /\
 cstep p CRnonterminal m (SKIP,(kenil,kseq(sskip None)kstop))m.
Proof.
 intros p m;split.
 - intros[v H];discriminate H.
 - eapply stmt_step;[reflexivity|apply sseq_step].
Qed.

Theorem CRenabled_nonterminal_transfer : forall enabled ci ip cst,exists M Mc Mf Mr Ms Or Os Mp,
 cstepstar CGprogram(curs(V293_interrupt_handoff 103%Z 108%Z 106%Z),(kenil,CGpending))(CGge,CGle,M)
 (curs(sprim(switch 106%Z)),(kenil,CGpending))(CGge,CGle,Mc) /\
 (forall R,~CGstate OwnershipWaiting Mc(enabled::ci)|=SWINVt GHinv OwnershipWaiting ** R) /\
 lpstep(RCprogram,(CGpo,CGempty,ip))(CRtasks CRnonterminal)cst(CRS Mc enabled ci true [0%nat] [false])OwnershipWaiting
 (set(CRtasks CRnonterminal)OwnershipWaiting(SKIP,(kenil,CGpending)))cst(CRS Mf enabled ci true [0%nat] [false])OwnershipReady /\
 disjoint Mr Ms /\ disjoint(merge Mr Ms)Mp /\
 merge(merge Mr Ms)Mp=Mf /\
 disjoint Or Os /\ merge Or Os=CRabs /\
 (substaskst(CRold Mf enabled ci)Mp,emp,spec_done None)|=JHprivate /\
 (forall ab,(substaskst(CRnew Mf true [0%nat] [false])Ms,Os,ab)|=INV GHinv) /\
 (forall ab,(substaskst(CRnew Mf true [0%nat] [false])Mr,Or,ab)|=RDYINV GHinv OwnershipReady).
Proof.
 intros enabled ci ip cst;apply CRactual_transfer;unfold good_is;split;[unfold INUM;lia|exact I].
Qed.
