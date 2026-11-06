Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitch.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyEnter.
(* Existing concrete source prefix, then the original primitive. No boot claim. *)
Require Import CertiOS.certiucos.v293.proofs.V293ReadyStorageInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293ReadySwitchStep.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTargetHandoff.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchState.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrent.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCacheContract.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyGlobalTrace.
Require Import CertiOS.certiucos.v293.proofs.V293SharedStateWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.audit.probes.V293TaskRecordInvariantProbe.
Require Import CertiOS.audit.probes.V293ReadyTaskInvariantProbe.
Require Import CertiOS.audit.probes.V293ReadySchedCallProbe.
Require Import CertiOS.audit.probes.V293ReadySourceTailProbe.
Require Import CertiOS.audit.probes.V293ReadyCriticalGlobalProbe.
Require Import CertiOS.audit.probes.V293ReadyFullCallProbe.
Require Import CertiOS.audit.probes.V293ReadyGlobalTraceProbe.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.sep_combine_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyHandoff.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyDispatch.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBoundarySwitch.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitHandoffHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStoragePrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStorageTail.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import CertiOS.audit.probes.V293OSIntExitReadyHandoffProbe.
Require Import CertiOS.audit.probes.V293ReadyCurrentInvariantProbe.
Require Import CertiOS.audit.probes.V293InterruptBuilderCurrentCounterexample.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCurrentInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293CurrentHandoffPrefix.
(* Same typed prefix state; changing the candidate is not a kernel patch. *)
Definition GHinv:=V293_ready_current_inv 80%positive 81%positive 82%positive
 106%Z V293_tcb_type JHcells 94%positive.
Definition GHguard:=V293_current_guard 94%positive.
Lemma GHbyte : forall ge le M ir aux O op n,
 n<256 ->(ge,le,M,ir,aux,O,op)|=JHpost n ** Atrue ->
 load Tint8 M(94%positive,0%Z)=Some(V293_byteval n).
Proof.
 intros ge le M ir aux O op n Bound H.
 eapply V293_record_star_load_l with(s:=(ge,le,M,ir,aux,O,op))(P:=V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval n))(Q:=Atrue).
 - intros st K;apply V293_owned_record_cell_load;exact K.
 - unfold JHpost in H;sep auto.
Qed.
Lemma GHguard_before : forall ge le M ir aux O op,
 (ge,le,M,ir,aux,O,op)|=JHpost 6 ** Atrue ->
 (ge,le,M,ir,aux,O,op)|=GHguard OwnershipWaiting OwnershipTasks.
Proof.
 intros ge le M ir aux O op H;left;exists 6.
 apply astar_l_apure_intro;[ |exact(proj1(proj2 NCcurrent_mismatch))].
 assert(Cell:(ge,le,M,ir,aux,O,op)|=
 V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval 6) ** Atrue).
 { unfold JHpost in H;sep auto. }
 eapply astar_mono;[ |intros st K;exact K|exact Cell].
 intros st K;apply astar_l_apure_elim in K;exact(proj2 K).
Qed.
Lemma GHenrich : forall ct M ci,
 CGstate ct M ci|=SWINVt JHinv ct ** JHprivate ->
 CGstate ct M ci|=GHguard ct OwnershipTasks ->
 CGstate ct M ci|=SWINVt GHinv ct ** JHprivate.
Proof.
 intros ct M ci H G.
 unfold SWINVt in *;fold(CurTid ct)in *.
 eapply astar_mono in H;[ |apply astar_mono;[apply V293_ready_storage_switch_open|intros st K;exact K]|intros st K;exact K].
 assert(Core:CGstate ct M ci|=
 V293_ready_storage_core 80%positive 81%positive 82%positive 106%Z V293_tcb_type JHcells **
 (V293_shared_flags ** (CurTid ct ** JHprivate)))by(clear G;sep auto).
 assert(Own:V293_ready_storage_core 80%positive 81%positive 82%positive 106%Z V293_tcb_type JHcells ==>
 EX n:nat,[|n<256|] ** (Amapsto(94%positive,0%Z)Tint8 true(V293_byteval n) ** Atrue)).
 { intros st K;unfold V293_ready_storage_core,V293_ready_storage_extra,JHcells in K;cbn[V293_storage]in K.
   assert(B:st|=V293_storage_cell(94%positive,0%Z)Tint8 ** Atrue)by(sep auto).
   eapply astar_mono in B;[ |apply V293_storage_byte_open|intros s S;exact S].
   sep normal in B;sep destruct B;exists x;clear K;sep auto. }
 pose proof(V293_current_handoff_core_enrich 80%positive 81%positive 82%positive
 106%Z V293_tcb_type JHcells 94%positive Own _ ct OwnershipTasks
 CGge CGle M (fun _:hid=>false)(false,nil,ci)(RIabstract ct)(spec_done None)Core
 ltac:(reflexivity)(RIfixed_tasks ct) G)as New.
 eapply astar_mono;[ |intros st K;exact K| ].
 - apply astar_mono;[apply V293_current_switch_close|intros st K;exact K].
 - clear H G Core;sep auto.
Qed.
Lemma GHrejected : forall M ci,
 load Tint8 M(94%positive,0%Z)=Some(V293_byteval 4) ->
 forall R,~CGstate OwnershipWaiting M ci|=SWINVt GHinv OwnershipWaiting ** R.
Proof.
 intros M ci L R;unfold GHinv,CGstate.
 eapply V293_current_handoff_switch_reject with(ct:=OwnershipWaiting)(tasks:=OwnershipTasks)(nc:=4).
 - reflexivity.
 - apply RIfixed_tasks.
 - lia.
 - exact L.
 - exact(proj1(proj2(proj2 NCcurrent_mismatch))).
 - exact SCwaiting_not_highest.
Qed.
Theorem GHactual_copy_obstruction : forall enabled ci,
 exists M Mc,
 cstepstar CGprogram(curs(V293_interrupt_handoff 103%Z 108%Z 106%Z),(kenil,CGpending))(CGge,CGle,M)
 (curs(sprim(switch 106%Z)),(kenil,CGpending))(CGge,CGle,Mc) /\
 store Tint8 M(94%positive,0%Z)(V293_byteval 4)=Some Mc /\
 (forall b i,b<>94%positive \/i<>0%Z ->get Mc(b,i)=get M(b,i)) /\
 CGstate OwnershipWaiting M(enabled::ci)|=SWINVt JHinv OwnershipWaiting ** JHprivate /\
 CGstate OwnershipWaiting M(enabled::ci)|=SWINVt GHinv OwnershipWaiting ** JHprivate /\
 CGstate OwnershipWaiting Mc(enabled::ci)|=SWINVt JHinv OwnershipWaiting ** JHprivate /\
 (forall R,~CGstate OwnershipWaiting Mc(enabled::ci)|=SWINVt GHinv OwnershipWaiting ** R) /\
 CGstate OwnershipWaiting M(enabled::ci)|=GHguard OwnershipWaiting OwnershipTasks /\
 ~CGstate OwnershipWaiting Mc(enabled::ci)|=GHguard OwnershipWaiting OwnershipTasks /\
 load Tint8 M(94%positive,0%Z)=Some(V293_byteval 6) /\
 load Tint8 Mc(94%positive,0%Z)=Some(V293_byteval 4) /\
 load(Tptr V293_tcb_type)Mc(93%positive,0%Z)=Some(Vptr OwnershipReady).
Proof.
 intros enabled ci.
 destruct(CGlocal_ready true enabled ci)as(M&Trace&Held&Target&Counter&Cache).
 assert(Old:CGstate OwnershipWaiting M(enabled::ci)|=
 SWINVt(V293ReadyTaskInvariant.V293_ready_inv 80%positive 81%positive 82%positive)OwnershipWaiting ** JHpost 6)by exact Held.
 assert(Before:CGstate OwnershipWaiting M(enabled::ci)|=GHguard OwnershipWaiting OwnershipTasks).
 { apply GHguard_before;clear Held;sep auto. }
 assert(Raw:CGstate OwnershipWaiting M(enabled::ci)|=
 SWINVt(V293ReadyTaskInvariant.V293_ready_inv 80%positive 81%positive 82%positive)OwnershipWaiting **
 (V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval 6) **
 (V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval 4) **
 (V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady) **
 (V293_owned_record_cell((95%positive,0%Z),Tint32,Vint32 Int.zero) ** CGframe 0 0))))).
 { unfold JHpost in Old;clear Held Before;sep auto. }
 destruct(V293_handoff_copy_execution 80%positive 81%positive 82%positive CGprogram CGpending
 CGge CGle M(fun _=>false)(false,nil,enabled::ci)(RIabstract OwnershipWaiting)(spec_done None)
 OwnershipWaiting(V293_owned_record_cell((95%positive,0%Z),Tint32,Vint32 Int.zero) ** CGframe 0 0)
 103%Z 108%Z 106%Z 91%positive 94%positive 93%positive 4 6 OwnershipReady
 ltac:(lia)eq_refl eq_refl eq_refl eq_refl Raw)as(Mc&Copy&Store&Copied&OutsideCopy).
 assert(OldCopy:CGstate OwnershipWaiting Mc(enabled::ci)|=
 SWINVt(V293ReadyTaskInvariant.V293_ready_inv 80%positive 81%positive 82%positive)OwnershipWaiting ** JHpost 4).
 { unfold JHpost;clear Held Raw Old Before;sep auto. }
 assert(CacheCopy:load Tint8 Mc(94%positive,0%Z)=Some(V293_byteval 4)).
 { apply(GHbyte CGge CGle Mc (fun _=>false)(false,nil,enabled::ci)(RIabstract OwnershipWaiting)(spec_done None)4);[lia|clear Held Raw Old Copied Before;sep auto]. }
 exists M;exists Mc;split;[exact Copy| ];split;[exact Store| ];split;[exact OutsideCopy| ];split.
 - apply JHclose with(n:=6);exact Old.
 - split.
   + apply GHenrich;[apply JHclose with(n:=6);exact Old|exact Before].
   + split;[apply JHclose with(n:=4);exact OldCopy| ];split.
     * apply GHrejected;exact CacheCopy.
     * split;[exact Before| ];split.
       -- eapply V293_current_handoff_guard_reject with(nc:=4);[lia|exact CacheCopy|exact(proj1(proj2(proj2 NCcurrent_mismatch)))|exact SCwaiting_not_highest].
       -- split;[exact Cache| ];split;[exact CacheCopy| ].
          rewrite(V293_load_block_frame _ M Mc 93%positive 0%Z ltac:(intros;apply OutsideCopy;left;discriminate));exact Target.
Qed.
Theorem GHphysical_switch_still_works : forall enabled ci ip cst,
 exists M Mc Mf,
 cstepstar CGprogram(curs(V293_interrupt_handoff 103%Z 108%Z 106%Z),(kenil,CGpending))(CGge,CGle,M)
 (curs(sprim(switch 106%Z)),(kenil,CGpending))(CGge,CGle,Mc) /\
 (forall R,~CGstate OwnershipWaiting Mc(enabled::ci)|=SWINVt GHinv OwnershipWaiting ** R) /\
 JHswitch_result Mc Mf enabled ci ip cst /\
 (CGge,CGle,Mf,(fun _=>false),(false,nil,enabled::ci),
 set(RIabstract OwnershipWaiting)curtid(oscurt OwnershipReady),spec_done None)|=
 SWINVt GHinv OwnershipReady ** JHprivate.
Proof.
 intros enabled ci ip cst.
 destruct(GHactual_copy_obstruction enabled ci)as(M&Mc&Copy&Store&Outside&Old&New&OldCopy&Reject&Guard&NoGuard&Read&ReadCopy&Target).
 destruct(JHswitch Mc enabled ci ip cst Target OldCopy)as(Mf&After&Frame).
 exists M;exists Mc;exists Mf;split;[exact Copy| ];split;[exact Reject| ];split;[exact After| ].
 destruct After as[Step InvAfter].
 eapply V293_current_handoff_switch_highest_frame;[exact InvAfter| ].
 exists OwnershipReady;split;[apply map_get_set| ];exists OwnershipTasks;split;
 [rewrite map_get_set' by discriminate;apply RIfixed_tasks|exact RIhighest].
Qed.
Theorem GHprefix_in_new_candidate : forall Spec r ri events now aop ci,
 InfRules Spec V293_scheduler V293_shared_li GHinv r ri
 (JHtail events now aop ci)
 (sseq(V293_OSSched_increment 109%Z)
  (sseq(sskip None)(sassign(evar 108%Z)(evar 103%Z))))
 (V293_ready_exit_tail 80%positive 81%positive 82%positive 103%Z 108%Z 109%Z 106%Z
 91%positive 94%positive 95%positive V293_tcb_type JHrest OwnershipWaiting OwnershipTasks
 events now OwnershipReady aop nil ci JHprivate 4 4(Int.add Int.zero Int.one))OwnershipWaiting.
Proof.
 intros;apply V293_current_handoff_prefix;[lia| ].
 intros st H;unfold LINV,V293_shared_li;sep auto;exact V293_switch_li_good.
Qed.
Theorem GHcandidate_still_good : GoodI GHinv V293_scheduler V293_shared_li.
Proof. apply V293_ready_current_good. Qed.
