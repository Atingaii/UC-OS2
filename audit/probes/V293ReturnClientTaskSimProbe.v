(* Same real return and reached-snapshot control. Old saved/frame resources
   remain external; the target local candidate is the existing empty one. *)
Require Import CertiOS.audit.probes.V293ReturnInvariantSplitProbe.
Require Import CertiOS.audit.probes.V293SharedSwitchReturnProbe.
Require Import CertiOS.audit.probes.V293ActiveCallTraceProbe.
Require Import CertiOS.audit.probes.V293ActiveCallWitnessProbe.
Require Import CertiOS.audit.probes.V293ResumedReturnProgSimProbe.
Require Import CertiOS.audit.probes.V293ExitQuietCallProgSimProbe.
Require Import CertiOS.audit.probes.V293ExitNestingProgSimProbe.
Require Import CertiOS.audit.probes.V293CriticalReturnProgSimProbe.
Require Import CertiOS.audit.probes.V293HandoffProgSimProbe.
Require Import CertiOS.audit.probes.V293ReadyCriticalGlobalProbe.
Require Import CertiOS.audit.probes.V293ReadySchedCallProbe.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.audit.probes.V293TaskRecordInvariantProbe.
Require Import CertiOS.certiucos.v293.proofs.V293CurrentReturnInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitSharedReclose.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCurrentInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyGlobalTrace.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyFullCall.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Require Import CertiOS.certiucos.v293.proofs.V293ReturnClientTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293ClientSkipTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitch.
Require Import CertiOS.framework.proof.simulation.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.tactics.sepauto.seplog_tactics.

Definition RTpacket br bs ge M enabled ci O ip A C : Prop :=
 exists Ms Mt Mf Mtail Os Ot Of Otail,
 join Mt Mf Mtail /\join Ms Mtail M /\
 join Ot Of Otail /\join Os Otail O /\
 satp(ge,emp,Ms,(fun _=>false),(enabled,nil,ci))Os(INV(IPinv br)) /\
 satp(ge,emp,Mt,(fun _=>false),(enabled,nil,ci))Ot
 (RDYINV(IPinv br)OwnershipReady **LINV V293_shared_li OwnershipReady nil) /\
 (ge,emp,Mf,(fun _=>false),(enabled,nil,ci),Of,spec_done None)|=STframe bs /\
 TaskSim(RCprogram,(CPpo,CGempty,ip))C
 (ge,emp,Mt,(fun _=>false),(enabled,nil,ci))(RCprogram,A)C Ot
 V293_shared_li(IPinv br)
 (fun s=>satp(fst s)(snd s)
 (RDYINV(IPinv br)OwnershipReady **LINV V293_shared_li OwnershipReady nil))OwnershipReady.

Lemma RTclose : forall br bs ge M enabled ci O ip A C,
 V293_skip_client_state C ->
 (ge,emp,M,(fun _=>false),(enabled,nil,ci),O,spec_done None)|=STpost br bs ->
 RTpacket br bs ge M enabled ci O ip A C.
Proof.
 intros br bs ge M enabled ci O ip A C Cases Held.
 assert(Insert:STframe bs ==> LINV V293_shared_li OwnershipReady nil **STframe bs).
 { intros st H;apply astar_l_aemp_intro in H.
   eapply astar_mono;[apply V293_switch_local_empty|intros s K;exact K|exact H]. }
 unfold RTpacket,IPinv.
 apply V293_return_client_TaskSim;
 [exact Cases|reflexivity|intros;cbn[gettopis];unfold INUM;lia| ].
 unfold STpost in Held;unfold STframe at 1 in Insert.
 eapply astar_mono;[intros s K;exact K| |exact Held].
 eapply astar_mono;[intros s K;exact K|exact Insert].
Qed.

Theorem RTfull_call : forall br bs cs ncs ip A,
 fresh(NPinitial 1)br ->fresh(QPmemory br 1 1)bs ->
 exists Mc Ms Mf,
 V293_global_steps(RCprogram,(CPpo,CGempty,ip))HPcst
 (FWtasks,FWos br cs ncs,OwnershipWaiting)
 (FTreturned,FTreturnstate br bs Mf cs ncs,OwnershipReady) /\
 store(Tptr V293_tcb_type)Mc(1%positive,0%Z)(Vptr OwnershipReady)=Some Ms /\
 free Tint32 98%positive Ms=Some Mf /\
 RTpacket br bs(QPge br)Mf false ncs
 (set(RIabstract OwnershipWaiting)curtid(oscurt OwnershipReady))ip A(SKIP,(kenil,kstop)) /\
 load Tint32 Mf(bs,0%Z)=Some(Vint32 Int.zero) /\
 load Tint8 Mf(90%positive,0%Z)=Some(V293_byteval 99) /\
 (forall i,(0<=i<4)%Z ->get Mf(98%positive,i)=None).
Proof.
 intros br bs cs ncs ip A FR FS.
 destruct(STfull_call_shared_return br bs cs ncs ip FR FS)
 as(Mc&Ms&Mf&Prefix&Run&Store&Free&Post&Removed&Pointer).
 destruct(STsaved_retained br bs _ _ _ _ _ _ _ Post)as[Old Canary].
 exists Mc;exists Ms;exists Mf;split;[exact Run| ];split;[exact Store| ];
 split;[exact Free| ];split;[apply RTclose;[right;right;reflexivity|exact Post]| ];
 split;[exact Old| ];split;assumption.
Qed.

Theorem RTsaved_top_actual_ablation : forall br bs cs vci ip A,
 fresh(NPinitial 1)br ->fresh(QPmemory br 1 1)bs ->
 exists Mc Ms Mf,
 V293_global_steps(RCprogram,(CPpo,CGempty,ip))HPcst
 (FWtasks,FWos br cs(true::vci),OwnershipWaiting)
 (STswitch_tasks,(QPge br,FTenvs bs,Mc,(fun _=>false),FTaux cs(true::vci)),OwnershipWaiting) /\
 V293_global_steps(RCprogram,(CPpo,CGempty,ip))HPcst
 (STswitch_tasks,(QPge br,FTenvs bs,Mc,(fun _=>false),FTaux cs(true::vci)),OwnershipWaiting)
 (FTreturned,STreturned_os br bs Mf(FTaux cs(true::vci))false(true::vci),OwnershipReady) /\
 V293_global_steps(RCprogram,(CPpo,CGempty,ip))HPcst
 (STswitch_tasks,(QPge br,FTenvs bs,Mc,(fun _=>false),STaux_without_top cs vci),OwnershipWaiting)
 (FTreturned,STreturned_os br bs Mf(STaux_without_top cs vci)true vci,OwnershipReady) /\
 store(Tptr V293_tcb_type)Mc(1%positive,0%Z)(Vptr OwnershipReady)=Some Ms /\
 free Tint32 98%positive Ms=Some Mf /\
 RTpacket br bs(QPge br)Mf false (true::vci)
 (set(RIabstract OwnershipWaiting)curtid(oscurt OwnershipReady))ip A(SKIP,(kenil,kstop)) /\
 RTpacket br bs(QPge br)Mf true vci
 (set(RIabstract OwnershipWaiting)curtid(oscurt OwnershipReady))ip A(SKIP,(kenil,kstop)) /\
 (forall t,t<>OwnershipReady ->get(STaux_without_top cs vci)t=get(FTaux cs(true::vci))t).
Proof.
 intros br bs cs vci ip A FR FS.
 destruct(STsaved_top_actual_ablation br bs cs vci ip FR FS)
 as(Mc&Ms&Mf&Prefix&Positive&Negative&Store&Free&Off&On&OffAux&OnAux&Others).
 exists Mc;exists Ms;exists Mf;split;[exact Prefix| ];split;[exact Positive| ];
 split;[exact Negative| ];split;[exact Store| ];split;[exact Free| ];
 split;[apply RTclose;[right;right;reflexivity|exact Off]| ];split;[apply RTclose;[right;right;reflexivity|exact On]|exact Others].
Qed.

(* An assertion-boundary test, not a new pair of actual executions. *)
Lemma RTnot_initial : forall li t ge le M ir enabled si ci O,
 enabled=false \/ ci<>nil ->
 ~InitTaskSt li t(ge,le,M,ir,(enabled,si,ci),O).
Proof.
 intros li t ge le M ir enabled si ci O Bad [Held Empty].
 specialize(Held(spec_done None));cbn[fst snd]in Held.
 sep normal in Held;sep split in Held.
 cbn in *;destruct Bad;congruence.
Qed.

(* Generic client-family coverage; the actual full-call caller above is SKIP. *)
Theorem RTnonterminal_resume : forall br bs ge M enabled ci O ip A,
 (ge,emp,M,(fun _=>false),(enabled,nil,ci),O,spec_done None)|=STpost br bs ->
 RTpacket br bs ge M enabled ci O ip A V293_skip_client_code /\
 ~IsEnd V293_skip_client_code /\
 cstep RCprogram V293_skip_client_code(ge,emp,M)
 V293_skip_client_next(ge,emp,M).
Proof.
 intros br bs ge M enabled ci O ip A Held.
 split;[apply RTclose;[left;reflexivity|exact Held]| ].
 split;[unfold IsEnd,V293_skip_client_code;intros[v H];discriminate H| ].
 unfold V293_skip_client_code,V293_skip_client_next.
 eapply stmt_step;[reflexivity|apply sseq_step].
Qed.

Theorem RTnonvacuous : forall cs ncs ip A,
 exists br bs Mf,
 fresh(NPinitial 1)br /\fresh(QPmemory br 1 1)bs /\
 V293_global_steps(RCprogram,(CPpo,CGempty,ip))HPcst
 (FWtasks,FWos br cs ncs,OwnershipWaiting)
 (FTreturned,FTreturnstate br bs Mf cs ncs,OwnershipReady) /\
 RTpacket br bs(QPge br)Mf false ncs
 (set(RIabstract OwnershipWaiting)curtid(oscurt OwnershipReady))ip A(SKIP,(kenil,kstop)).
Proof.
 intros cs ncs ip A.
 destruct(STnonvacuous cs ncs ip)as(br&bs&Mf&FR&FS&Run&Post).
 exists br;exists bs;exists Mf;split;[exact FR| ];split;[exact FS| ];
 split;[exact Run|apply RTclose;[right;right;reflexivity|exact Post]].
Qed.
