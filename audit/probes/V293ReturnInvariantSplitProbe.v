(* The exact frozen full-call program, heap and reached-snapshot control.
   Original INV/RDYINV partition; no new execution or invariant definition. *)
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

Definition IPinv br := V293_ready_current_inv 80%positive 81%positive 82%positive
 106%Z V293_tcb_type(STcells br)94%positive.
Definition IPpost br bs := (INV(IPinv br) **RDYINV(IPinv br)OwnershipReady) **STframe bs.

Lemma IPclose : forall br bs ge le M cs enabled O op,
 (ge,le,M,(fun _=>false),(enabled,nil,cs),O,op)|=STpost br bs ->
 (ge,le,M,(fun _=>false),(enabled,nil,cs),O,op)|=IPpost br bs.
Proof.
 intros br bs ge le M cs enabled O op Held.
 unfold IPpost,IPinv;apply V293_current_return_invariants;
 [reflexivity|intros;cbn[gettopis];unfold INUM;lia|exact Held].
Qed.

Theorem IPfull_call : forall br bs cs ncs ip,
 fresh(NPinitial 1)br ->fresh(QPmemory br 1 1)bs ->
 exists Mc Ms Mf,
 V293_global_steps(RCprogram,(CPpo,CGempty,ip))HPcst
 (FWtasks,FWos br cs ncs,OwnershipWaiting)
 (FTreturned,FTreturnstate br bs Mf cs ncs,OwnershipReady) /\
 store(Tptr V293_tcb_type)Mc(1%positive,0%Z)(Vptr OwnershipReady)=Some Ms /\
 free Tint32 98%positive Ms=Some Mf /\
 (QPge br,emp,Mf,(fun _=>false),(false,nil,ncs),
 set(RIabstract OwnershipWaiting)curtid(oscurt OwnershipReady),spec_done None)|=IPpost br bs /\
 load Tint32 Mf(bs,0%Z)=Some(Vint32 Int.zero) /\
 load Tint8 Mf(90%positive,0%Z)=Some(V293_byteval 99) /\
 (forall i,(0<=i<4)%Z ->get Mf(98%positive,i)=None).
Proof.
 intros br bs cs ncs ip FR FS.
 destruct(STfull_call_shared_return br bs cs ncs ip FR FS)
 as(Mc&Ms&Mf&Prefix&Run&Store&Free&Post&Removed&Pointer).
 destruct(STsaved_retained br bs _ _ _ _ _ _ _ Post)as[Old Canary].
 exists Mc;exists Ms;exists Mf;split;[exact Run| ];split;[exact Store| ];
 split;[exact Free| ];split;[apply IPclose;exact Post| ];
 split;[exact Old| ];split;assumption.
Qed.

Theorem IPsaved_top_actual_ablation : forall br bs cs vci ip,
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
 (QPge br,emp,Mf,(fun _=>false),(false,nil,true::vci),
 set(RIabstract OwnershipWaiting)curtid(oscurt OwnershipReady),spec_done None)|=IPpost br bs /\
 (QPge br,emp,Mf,(fun _=>false),(true,nil,vci),
 set(RIabstract OwnershipWaiting)curtid(oscurt OwnershipReady),spec_done None)|=IPpost br bs /\
 (forall t,t<>OwnershipReady ->get(STaux_without_top cs vci)t=get(FTaux cs(true::vci))t).
Proof.
 intros br bs cs vci ip FR FS.
 destruct(STsaved_top_actual_ablation br bs cs vci ip FR FS)
 as(Mc&Ms&Mf&Prefix&Positive&Negative&Store&Free&Off&On&OffAux&OnAux&Others).
 exists Mc;exists Ms;exists Mf;split;[exact Prefix| ];split;[exact Positive| ];
 split;[exact Negative| ];split;[exact Store| ];split;[exact Free| ];
 split;[apply IPclose;exact Off| ];split;[apply IPclose;exact On|exact Others].
Qed.

(* A boundary necessity check, distinct from the actual two-run ablation. *)
Lemma IPdisabled_top_bound : forall I ge le M ir si ci O op,
 (ge,le,M,ir,(false,si,ci),O,op)|=INV I ->gettopis si<=INUM.
Proof.
 intros I ge le M ir si ci O op Held.
 unfold INV in Held;apply sat_split in Held.
 destruct Held as(m0&m1&o0&o1&JM&JO&Top&[On|Off]).
 - unfold inv_ieon in On;apply sat_split in On.
   destruct On as(ma&mb&oa&ob&JM'&JO'&[Bad Empty]&Rest);discriminate Bad.
 - unfold inv_ieoff in Off;apply sat_split in Off.
   destruct Off as(ma&mb&oa&ob&JM'&JO'&IE&k&Rest).
   apply sat_split in Rest;destruct Rest as(mc&md&oc&od&JM''&JO''&[Topis Empty]&Cases).
   change(gettopis si=k)in Topis;rewrite Topis.
   destruct Cases as[Less|[Equal Empty']];[ |lia].
   apply astar_l_apure_elim in Less;destruct Less as[Less _];lia.
Qed.

Theorem IPout_of_range_rejected : forall I ge le M ir si ci O op,
 ~(ge,le,M,ir,(false,3::si,ci),O,op)|=INV I.
Proof.
 intros I ge le M ir si ci O op Held.
 pose proof(IPdisabled_top_bound _ _ _ _ _ _ _ _ _ Held)as Bound.
 cbn[gettopis]in Bound;unfold INUM in Bound;lia.
Qed.

Theorem IPnonvacuous : forall cs ncs ip,
 exists br bs Mf,
 fresh(NPinitial 1)br /\fresh(QPmemory br 1 1)bs /\
 V293_global_steps(RCprogram,(CPpo,CGempty,ip))HPcst
 (FWtasks,FWos br cs ncs,OwnershipWaiting)
 (FTreturned,FTreturnstate br bs Mf cs ncs,OwnershipReady) /\
 (QPge br,emp,Mf,(fun _=>false),(false,nil,ncs),
 set(RIabstract OwnershipWaiting)curtid(oscurt OwnershipReady),spec_done None)|=IPpost br bs.
Proof.
 intros cs ncs ip.
 destruct(STnonvacuous cs ncs ip)as(br&bs&Mf&FR&FS&Run&Post).
 exists br;exists bs;exists Mf;split;[exact FR| ];split;[exact FS| ];
 split;[exact Run|apply IPclose;exact Post].
Qed.
