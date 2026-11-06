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
Require Import CertiOS.audit.probes.V293CurrentReadyResumeProbe.
Require Import CertiOS.certiucos.v293.proofs.V293ClientSkipTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitch.
Import ListNotations.
Local Open Scope nat_scope.

Lemma CSnonterminal_progress : forall p m,
 ~IsEnd V293_skip_client_code /\
 cstep p V293_skip_client_code m (SKIP,(kenil,kseq(sskip None)kstop))m.
Proof. intros;apply CRnonterminal_progress. Qed.

(* The private frame below belongs to the old current task. The target's
   private memory and abstract frame are both empty in this typed witness. *)
Theorem CSactual_resume : forall enabled ci ip cst A,exists M Mc Mf Mr Ms Or Os OldPrivateM,
 cstepstar CGprogram(curs(V293_interrupt_handoff 103%Z 108%Z 106%Z),(kenil,CGpending))(CGge,CGle,M)
 (curs(sprim(switch 106%Z)),(kenil,CGpending))(CGge,CGle,Mc) /\
 (forall R,~CGstate OwnershipWaiting Mc(enabled::ci)|=SWINVt GHinv OwnershipWaiting ** R) /\
 lpstep(RCprogram,(CGpo,CGempty,ip))(CRtasks V293_skip_client_code)cst(CRS Mc enabled ci true nil nil)OwnershipWaiting
 (set(CRtasks V293_skip_client_code)OwnershipWaiting(SKIP,(kenil,CGpending)))cst(CRS Mf enabled ci true nil nil)OwnershipReady /\
 disjoint Mr Ms /\ disjoint(merge Mr Ms)OldPrivateM /\
 merge(merge Mr Ms)OldPrivateM=Mf /\
 disjoint Or Os /\ merge Or Os=CRabs /\
 (substaskst(CRold Mf enabled ci)OldPrivateM,emp,spec_done None)|=JHprivate /\
 satp(CGge,emp,(emp:mem),empisr,(true,nil,nil))(emp:osabst)
   (LINV V293_shared_li OwnershipReady init_lg) /\
 (forall ab,(substaskst(CRnew Mf true nil nil)Ms,Os,ab)|=INV GHinv) /\
 (forall ab,(substaskst(CRnew Mf true nil nil)Mr,Or,ab)|=RDYINV GHinv OwnershipReady) /\
 InitTaskSt V293_shared_li OwnershipReady(substaskst(CRnew Mf true nil nil)Mr,Or) /\
 satp(substaskst(CRnew Mf true nil nil)Mr)Or(CurLINV V293_shared_li OwnershipReady) /\
 TaskSim(RCprogram,(CGpo,CGempty,ip))V293_skip_client_code
 (substaskst(CRnew Mf true nil nil)Mr)(RCprogram,A)V293_skip_client_code Or
 V293_shared_li GHinv(InitTaskSt V293_shared_li OwnershipReady)OwnershipReady.
Proof.
 intros enabled ci ip cst A.
 destruct(GHactual_copy_obstruction enabled ci)as(M&Mc&Copy&Store&Outside&Old&New&OldCopy&Reject&Guard&NoGuard&Read&ReadCopy&Target).
 destruct(V293_ready_storage_switch_step 80%positive 81%positive 82%positive 106%Z V293_tcb_type JHcells
 RCprogram CGpo CGempty ip(CRtasks V293_skip_client_code)cst CGpending OwnershipWaiting OwnershipReady
 93%positive 1%positive CGge CGle CGswitch_envs Mc empisr(false,nil,enabled::ci)
 (CRaux enabled ci true nil nil)(RIabstract OwnershipWaiting)(spec_done None)JHprivate
 (map_get_set _ _ _)(map_get_set _ _ _)(map_get_set _ _ _)eq_refl Target eq_refl OldCopy)
 as(Mf&Step&PhysicalStore&After&Current&Frame).
 apply sat_split in After;destruct After as(Ma&OldPrivateM&Oa&Op&JM&JO&Switch&Private).
 change(join Oa Op CRabs)in JO.
 destruct(CRabstract_frame _ _ _ _ _ _ _ Switch JO)as[EA EP];subst Oa Op.
 assert(SwitchAll:forall ab,(substaskst(CRold Mf enabled ci)Ma,CRabs,ab)|=SWINVt JHinv OwnershipReady).
 { intro ab;unfold CRold;cbn[substaskst];eapply swinv_aop_irev;exact Switch. }
 assert(High:sched_self V293_scheduler CRabs).
 { apply SCafter_sched;apply RIfixed_tasks. }
 assert(DM:disjoint Ma(emp:mem))by(apply disjoint_emp_l).
 assert(DO:disjoint CRabs(emp:osabst))by(apply disjoint_emp_l).
 assert(FM:disjoint(merge Ma emp)(emp:mem))by(apply disjoint_emp_l).
 assert(FO:disjoint(merge CRabs emp)(emp:osabst))by(apply disjoint_emp_l).
 assert(PrivateTarget:satp(CGge,emp,(emp:mem),empisr,(true,nil,nil))(emp:osabst)
  (LINV V293_shared_li OwnershipReady init_lg)).
 { intro ab;apply V293_switch_local_empty;split;reflexivity. }
 destruct(V293_current_skip_resume 80%positive 81%positive 82%positive 106%Z V293_tcb_type JHcells 94%positive
 RCprogram CGpo CGempty ip A V293_shared_li
 (CRold Mf enabled ci)CRabs emp emp Ma emp emp OwnershipWaiting OwnershipReady
 (CRS Mf enabled ci true nil nil)CGge Mf
 eq_refl(CRgood Mf enabled ci true nil nil I)DO DM FM FO
 (CRempty_INV CGge CGle empisr(enabled::ci))SwitchAll High
 (proj1(CRprojections _ _ _ _ _ _))(proj2(CRprojections _ _ _ _ _ _))PrivateTarget)
 as(Mr&Ms&Or&Os&DMS&EM&DOS&EO&FrameMr&FrameOr&Inv&Ready&Sim).
 assert(Total:merge Mr Ms=Ma)by(rewrite EM;apply jl_merge_emp).
 pose proof(crt_init Mr emp Or emp CGge OwnershipReady V293_shared_li GHinv
  FrameMr FrameOr Ready PrivateTarget)as InitSat.
 rewrite !jl_merge_emp in InitSat,Sim.
 assert(Init:InitTaskSt V293_shared_li OwnershipReady
  (substaskst(CRnew Mf true nil nil)Mr,Or)).
 { split;[exact InitSat|reflexivity]. }
 pose proof(V293_init_curlinv _ _ _ _ Init)as Local.
 exists M;exists Mc;exists Mf;exists Mr;exists Ms;exists Or;exists Os;exists OldPrivateM.
 split;[exact Copy| ];split;[exact Reject| ];split;[exact Step| ];split;[exact DMS| ];split.
 - rewrite Total;exists Mf;exact JM.
 - split.
   + rewrite Total;apply join_merge in JM;symmetry;exact JM.
   + split;[exact DOS| ];split;[rewrite EO;apply jl_merge_emp| ];
     split;[exact Private| ];split;[exact PrivateTarget| ];split;[exact Inv| ];
     split;[exact Ready| ];split;[exact Init| ];split;[exact Local|exact Sim].
Qed.

Lemma CSinit_requires_clear_stacks : forall ge le M ir ie si cs O li t,
 InitTaskSt li t((ge,le,M,ir,(ie,si,cs)),O) ->si=nil /\ cs=nil.
Proof.
 intros ge le M ir ie si cs O li t[Held Empty].
 specialize(Held(spec_done None));cbn[fst snd]in Held.
 sep normal in Held;sep split in Held;auto.
Qed.

Lemma CSinterrupted_target_not_initial : forall ge le M ir O li t,
 ~InitTaskSt li t((ge,le,M,ir,(true,cons 0%nat nil,nil)),O).
Proof.
 intros ge le M ir O li t Init.
 destruct(CSinit_requires_clear_stacks _ _ _ _ _ _ _ _ _ _ Init)as[Bad Clear];discriminate.
Qed.

Lemma CScritical_target_not_initial : forall ge le M ir O li t,
 ~InitTaskSt li t((ge,le,M,ir,(true,nil,cons false nil)),O).
Proof.
 intros ge le M ir O li t Init.
 destruct(CSinit_requires_clear_stacks _ _ _ _ _ _ _ _ _ _ Init)as[Clear Bad];discriminate.
Qed.
