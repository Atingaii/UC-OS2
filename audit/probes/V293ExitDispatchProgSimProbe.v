Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Lia.
Require Import CertiOS.certiucos.v293.proofs.V293SwitchProgSim.
Require Import CertiOS.audit.probes.V293CurrentHandoffPrefixProbe.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyStorageInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293ReadySwitchStep.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCurrentInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293CurrentHandoffPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBoundarySwitch.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyHandoff.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.audit.probes.V293OSIntExitReadyHandoffProbe.
Require Import CertiOS.audit.probes.V293ReadyCriticalGlobalProbe.
Require Import CertiOS.audit.probes.V293ReadyFullCallProbe.
Require Import CertiOS.audit.probes.V293ReadyGlobalTraceProbe.
Require Import CertiOS.audit.probes.V293ReadySwitchStepProbe.
Require Import CertiOS.audit.probes.V293ReadySchedCallProbe.
Require Import CertiOS.audit.probes.V293TaskRecordInvariantProbe.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.certiucos.v293.proofs.V293HandoffProgSim.
Require Import CertiOS.audit.probes.V293SwitchProgSimProbe.
Require Import CertiOS.certiucos.v293.proofs.V293ClientSkipTaskSim.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.simulation.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.framework.proof.step_prop.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import CertiOS.audit.probes.V293HandoffProgSimProbe.
Require Import CertiOS.audit.probes.V293ReadyTaskInvariantProbe.
Require Import CertiOS.audit.probes.V293ReadySourceTailProbe.
Require Import CertiOS.certiucos.v293.proofs.V293ExitDispatchProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293ReadySchedCall.
Require Import CertiOS.certiucos.v293.proofs.V293ReadySourceTail.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPointerCompare.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitDispatchCall.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.code.V293OSSchedDispatch.
Local Open Scope nat_scope.

Definition EPbody:=sif(V293_OSSched_different 103%Z 108%Z)
 (sseq(V293_OSSched_increment 109%Z)
 (sseq(sskip None)(V293_interrupt_handoff 103%Z 108%Z 106%Z)))(sskip None).
Definition EPcode:code:=(curs EPbody,(kenil,HPpending)).
Definition EPtasks:tasks:=set HPtasks OwnershipWaiting EPcode.
Definition EPbefore:=
 V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval 4) **
 (V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval 6) **
 (V293_owned_record_cell((95%positive,0%Z),Tint32,Vint32 Int.mone) **
 (V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady) ** CGframe 0 0))).

(* Only the real scheduler/target-update prefix is used here, not the old
   already-incremented CGlocal_ready endpoint. The counter is still mone. *)
Lemma EPscheduled : forall enabled ci,
 exists M,
 cstepstar CGprogram
 (curs(V293_OSSched_unlocked_prefix 107%Z 105%Z 103%Z 106%Z),(kenil,HPpending))
 (CGge,CGle,CGmemory OwnershipWaiting true 0 0)
 (SKIP,(kenil,HPpending))(CGge,CGle,M) /\
 CGstate OwnershipWaiting M(enabled::ci)|=
 SWINVt(V293ReadyTaskInvariant.V293_ready_inv 80%positive 81%positive 82%positive)OwnershipWaiting ** EPbefore.
Proof.
 intros enabled ci.
 assert(Held:CGstate OwnershipWaiting(CGmemory OwnershipWaiting true 0 0)(enabled::ci)|=
 SWINVt(V293ReadyTaskInvariant.V293_ready_inv 80%positive 81%positive 82%positive)OwnershipWaiting **
 (V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval 88) **
 (V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipWaiting) **
 (V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval 6) **
 (V293_owned_record_cell((95%positive,0%Z),Tint32,Vint32 Int.mone) ** CGframe 0 0))))).
 { exact(CGentry OwnershipWaiting true 0 0(enabled::ci)ltac:(lia)ltac:(lia)). }
 destruct(V293_ready_dispatch_call 80%positive 81%positive 82%positive CGprogram HPpending
 CGge CGle(CGmemory OwnershipWaiting true 0 0)(fun _=>false)(false,nil,enabled::ci)
 (RIabstract OwnershipWaiting)(spec_done None)OwnershipWaiting
 (V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval 6) **
 (V293_owned_record_cell((95%positive,0%Z),Tint32,Vint32 Int.mone) ** CGframe 0 0))
 107%Z 100%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z
 92%positive 91%positive 93%positive(V293_byteval 88)(Vptr OwnershipWaiting)
 ltac:(vm_compute;reflexivity)
 ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)
 ltac:(discriminate)ltac:(discriminate)
 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
 ltac:(repeat split;try exact I;apply CGframe_good)
 (CGlookup OwnershipWaiting true 0 0)Held)
 as(tasks&lo&hi&entries&next&message&b&Ms&Mskip&M&Fresh&Map&Rel&Task&Call&Skipped&Free&Removed&High&Exec&Store&After&Target&Sched&Pre&Live&Dead&CallFrame&TargetFrame).
 pose proof(RIfixed_tasks OwnershipWaiting).
 assert(tasks=OwnershipTasks)by congruence;subst tasks.
 assert(Range:V293_ready_select lo hi(V293_ready_group lo hi)<13).
 { destruct Rel as[Lo[Hi[Nonempty[Bitmap Table]]]];apply V293_ready_selection_range;assumption||reflexivity. }
 destruct(RTonly_ready _ _ _ Range Task)as[Selected[Next Message]];subst next message.
 rewrite Selected in After;exists M;split;[exact Exec| ].
 unfold EPbefore,CGstate;clear -After;sep auto.
Qed.

Lemma EPbridge : forall M M1 Mc Mf enabled ci ip,
 evalval(V293_OSSched_different 103%Z 108%Z)(CGge,CGle,M)=Some(Vint32 Int.one) ->
 load Tint32 M(95%positive,0%Z)=Some(Vint32 Int.mone) ->
 store Tint32 M(95%positive,0%Z)(Vint32(Int.add Int.mone Int.one))=Some M1 ->
 load Tint8 M1(91%positive,0%Z)=Some(V293_byteval 4) ->
 store Tint8 M1(94%positive,0%Z)(V293_byteval 4)=Some Mc ->
 load(Tptr V293_tcb_type)Mc(93%positive,0%Z)=Some(Vptr OwnershipReady) ->
 store(Tptr V293_tcb_type)Mc(1%positive,0%Z)(Vptr OwnershipReady)=Some Mf ->
 ProgSim(RCprogram,(CGpo,CGempty,ip))EPtasks(SPS M enabled ci)
 SPph HPTh(RIabstract OwnershipWaiting)HPcst OwnershipWaiting.
Proof.
 intros M M1 Mc Mf enabled ci ip Guard Counter Increment High Copy Target Store.
 eapply V293_exit_dispatch_progsim with(le:=CGle)(M1:=M1)(Mc:=Mc)(Mf:=Mf)(next:=OwnershipReady)
 (high:=103%Z)(current:=108%Z)(counter:=109%Z)(target:=106%Z)(ks:=HPpending)
 (bk:=95%positive)(c:=Int.mone)(b:=94%positive)(v:=V293_byteval 4)
 (bt:=93%positive)(bc:=1%positive)(tp:=V293_tcb_type)(si:=nil)(cs:=enabled::ci)
 (Thf:=HPThf)(Of:=SPOf);try reflexivity;try eassumption.
 - exact HPcontext.
 - eapply hp_stepS;[apply HPschedule|apply hp_stepO].
 - unfold EPtasks;rewrite tasks_set_a_set_a;apply HPpost.
Qed.

Theorem EPactual_dispatch_simulation : forall enabled ci ip,
 exists M M1 Mc Mf,
 cstepstar CGprogram
 (curs(V293_OSSched_unlocked_prefix 107%Z 105%Z 103%Z 106%Z),(kenil,HPpending))
 (CGge,CGle,CGmemory OwnershipWaiting true 0 0)
 (SKIP,(kenil,HPpending))(CGge,CGle,M) /\
 load Tint32 M(95%positive,0%Z)=Some(Vint32 Int.mone) /\
 store Tint32 M(95%positive,0%Z)(Vint32 Int.zero)=Some M1 /\
 load Tint32 M1(95%positive,0%Z)=Some(Vint32 Int.zero) /\
 cstepstar CGprogram EPcode(CGge,CGle,M)
 (curs(sprim(switch 106%Z)),(kenil,HPpending))(CGge,CGle,Mc) /\
 (forall R,~CGstate OwnershipWaiting Mc(enabled::ci)|=SWINVt GHinv OwnershipWaiting ** R) /\
 store(Tptr V293_tcb_type)Mc(1%positive,0%Z)(Vptr OwnershipReady)=Some Mf /\
 ProgSim(RCprogram,(CGpo,CGempty,ip))EPtasks(SPS M enabled ci)
 SPph HPTh(RIabstract OwnershipWaiting)HPcst OwnershipWaiting.
Proof.
 intros enabled ci ip.
 destruct(EPscheduled enabled ci)as(M&Schedule&Before).
 assert(Wrap:Int.add Int.mone Int.one=Int.zero)by(vm_compute;apply Int.mkint_eq;reflexivity).
 assert(Owned:CGstate OwnershipWaiting M(enabled::ci)|=
 V293_owned_record_cell((95%positive,0%Z),Tint32,Vint32 Int.mone) **
 (SWINVt(V293ReadyTaskInvariant.V293_ready_inv 80%positive 81%positive 82%positive)OwnershipWaiting **
 (V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval 4) **
 (V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval 6) **
 (V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady) ** CGframe 0 0))))).
 { unfold EPbefore in Before;sep auto. }
 assert(Counter:load Tint32 M(95%positive,0%Z)=Some(Vint32 Int.mone)).
 { eapply V293_record_star_load_l with(s:=CGstate OwnershipWaiting M(enabled::ci));
 [intros st H;apply V293_owned_record_cell_load;exact H|exact Owned]. }
 assert(High0:load Tint8 M(91%positive,0%Z)=Some(V293_byteval 4)).
 { eapply V293_record_star_load_l with(s:=CGstate OwnershipWaiting M(enabled::ci))
 (P:=V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval 4))(Q:=Atrue).
 - intros st H;apply V293_owned_record_cell_load;exact H.
 - unfold EPbefore in Before;sep auto. }
 assert(Cache0:load Tint8 M(94%positive,0%Z)=Some(V293_byteval 6)).
 { eapply V293_record_star_load_l with(s:=CGstate OwnershipWaiting M(enabled::ci))
 (P:=V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval 6))(Q:=Atrue).
 - intros st H;apply V293_owned_record_cell_load;exact H.
 - unfold EPbefore in Before;sep auto. }
 destruct(V293_OSSched_byte_comparison_eval CGge CGle M 103%Z 108%Z 91%positive 94%positive
 4 6 ltac:(lia)ltac:(lia)eq_refl eq_refl eq_refl eq_refl High0 Cache0)as[Guard _].
 change(evalval(V293_OSSched_different 103%Z 108%Z)(CGge,CGle,M)=Some(Vint32 Int.one))in Guard.
 destruct(V293_owned_record_cell_update (95%positive,0%Z) Tint32(Vint32 Int.mone)(Vint32 Int.zero)
 _ _ _ _ _ _ _ _ eq_refl Owned)as(M1&Increment&Updated).
 destruct(V293_exit_boundary_tail CGprogram HPpending CGge CGle M(fun _=>false)
 (false,nil,enabled::ci)(RIabstract OwnershipWaiting)(spec_done None) _
 103%Z 108%Z 109%Z(V293_interrupt_handoff 103%Z 108%Z 106%Z)
 91%positive 94%positive 95%positive 4 6 Int.mone
 ltac:(lia)ltac:(lia)ltac:(lia)eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
 High0 Cache0 Owned)as(Mtail&Prefix&Inc2&After2&Outside2).
 rewrite Wrap in Inc2;change(store Tint32 M(95%positive,0%Z)(Vint32 Int.zero)=Some Mtail)in Inc2.
 assert(Mtail=M1)by congruence;subst Mtail.
 assert(After:CGstate OwnershipWaiting M1(enabled::ci)|=
 SWINVt(V293ReadyTaskInvariant.V293_ready_inv 80%positive 81%positive 82%positive)OwnershipWaiting ** JHpost 6).
 { unfold JHpost;clear Before Owned;sep auto. }
 assert(High:load Tint8 M1(91%positive,0%Z)=Some(V293_byteval 4)).
 { eapply V293_record_star_load_l with(s:=CGstate OwnershipWaiting M1(enabled::ci))
 (P:=V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval 4))(Q:=Atrue).
 - intros st H;apply V293_owned_record_cell_load;exact H.
 - unfold JHpost in After;clear Before Owned Updated;sep auto. }
 assert(Counter1:load Tint32 M1(95%positive,0%Z)=Some(Vint32 Int.zero)).
 { eapply V293_record_star_load_l with(s:=CGstate OwnershipWaiting M1(enabled::ci));
 [intros st H;apply V293_owned_record_cell_load;exact H|exact Updated]. }
 assert(Raw:CGstate OwnershipWaiting M1(enabled::ci)|=
 SWINVt(V293ReadyTaskInvariant.V293_ready_inv 80%positive 81%positive 82%positive)OwnershipWaiting **
 (V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval 6) **
 (V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval 4) **
 (V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady) **
 (V293_owned_record_cell((95%positive,0%Z),Tint32,Vint32 Int.zero) ** CGframe 0 0))))).
 { unfold JHpost in After;clear Before Owned Updated;sep auto. }
 destruct(V293_handoff_copy_execution 80%positive 81%positive 82%positive CGprogram HPpending
 CGge CGle M1(fun _=>false)(false,nil,enabled::ci)(RIabstract OwnershipWaiting)(spec_done None)
 OwnershipWaiting(V293_owned_record_cell((95%positive,0%Z),Tint32,Vint32 Int.zero) ** CGframe 0 0)
 103%Z 108%Z 106%Z 91%positive 94%positive 93%positive 4 6 OwnershipReady
 ltac:(lia)eq_refl eq_refl eq_refl eq_refl Raw)as(Mc&Copy&Store&Copied&OutsideCopy).
 assert(OldCopy:CGstate OwnershipWaiting Mc(enabled::ci)|=
 SWINVt(V293ReadyTaskInvariant.V293_ready_inv 80%positive 81%positive 82%positive)OwnershipWaiting ** JHpost 4).
 { unfold JHpost;clear Before Owned Updated After Raw;sep auto. }
 assert(CacheCopy:load Tint8 Mc(94%positive,0%Z)=Some(V293_byteval 4)).
 { apply(GHbyte CGge CGle Mc(fun _=>false)(false,nil,enabled::ci)(RIabstract OwnershipWaiting)(spec_done None)4);
 [lia|clear Before Owned Updated After Raw Copied;sep auto]. }
 assert(InvCopy:CGstate OwnershipWaiting Mc(enabled::ci)|=SWINVt JHinv OwnershipWaiting ** JHprivate).
 { apply JHclose with(n:=4);exact OldCopy. }
 assert(TargetCopy:load(Tptr V293_tcb_type)Mc(93%positive,0%Z)=Some(Vptr OwnershipReady)).
 { eapply V293_record_star_load_l with(s:=CGstate OwnershipWaiting Mc(enabled::ci))
 (P:=V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady))(Q:=Atrue).
 - intros st H;apply V293_owned_record_cell_load;exact H.
 - unfold JHpost in OldCopy;clear -OldCopy;sep auto. }
 destruct(V293_ready_storage_switch_step 80%positive 81%positive 82%positive 106%Z V293_tcb_type JHcells
 RCprogram CGpo CGempty ip
 (set EPtasks OwnershipWaiting(curs(sprim(switch 106%Z)),(kenil,HPpending)))HPcst HPpending OwnershipWaiting OwnershipReady
 93%positive 1%positive CGge CGle CGswitch_envs Mc(fun _=>false)(false,nil,enabled::ci)
 (CGswitch_aux enabled ci)(RIabstract OwnershipWaiting)(spec_done None)JHprivate
 (map_get_set _ _ _)(map_get_set _ _ _)(map_get_set _ _ _)eq_refl TargetCopy eq_refl InvCopy)
 as(Mf&Step&PhysicalStore&Switched&Current&Frame).
 exists M;exists M1;exists Mc;exists Mf;split;[exact Schedule| ];split;[exact Counter| ];
 split;[exact Increment| ];split;[exact Counter1| ];split.
 - eapply V293_cstepstar_trans;[ |exact Copy].
   exact Prefix.
 - split;[apply GHrejected;exact CacheCopy| ];split;[exact PhysicalStore| ].
   eapply EPbridge;try eassumption;rewrite Wrap;exact Increment.
Qed.


(* Omitting only the counter write does not satisfy its exact storage post.
   This does not assert that the counter is observable in every client. *)
Theorem EPcounter_omission_rejected : forall M,
 load Tint32 M(95%positive,0%Z)=Some(Vint32 Int.mone) ->
 ~load Tint32 M(95%positive,0%Z)=Some(Vint32 Int.zero).
Proof.
 intros M Before After;rewrite Before in After;inversion After as[Equal].
Qed.

(* Fix the scheduled heap and change only the current-priority byte 6 to 4.
   The unchanged code now takes the equal branch, leaving mone untouched. *)
Theorem EPsame_single_byte_control : forall enabled ci,
 exists M Ms,
 CGstate OwnershipWaiting M(enabled::ci)|=
 SWINVt(V293ReadyTaskInvariant.V293_ready_inv 80%positive 81%positive 82%positive)OwnershipWaiting ** EPbefore /\
 store Tint8 M(94%positive,0%Z)(V293_byteval 4)=Some Ms /\
 (forall b i,b<>94%positive \/ (i<0)%Z \/ (1<=i)%Z ->get Ms(b,i)=get M(b,i)) /\
 load Tint8 Ms(91%positive,0%Z)=Some(V293_byteval 4) /\
 load Tint8 Ms(94%positive,0%Z)=Some(V293_byteval 4) /\
 load Tint32 Ms(95%positive,0%Z)=Some(Vint32 Int.mone) /\
 evalval(V293_OSSched_different 103%Z 108%Z)(CGge,CGle,Ms)=Some(Vint32 Int.zero) /\
 cstepstar CGprogram EPcode(CGge,CGle,Ms)(SKIP,(kenil,HPpending))(CGge,CGle,Ms).
Proof.
 intros enabled ci;destruct(EPscheduled enabled ci)as(M&Schedule&Before).
 assert(Owned:CGstate OwnershipWaiting M(enabled::ci)|=
 V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval 6) **
 (SWINVt(V293ReadyTaskInvariant.V293_ready_inv 80%positive 81%positive 82%positive)OwnershipWaiting **
 (V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval 4) **
 (V293_owned_record_cell((95%positive,0%Z),Tint32,Vint32 Int.mone) **
 (V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady) ** CGframe 0 0))))).
 { unfold EPbefore in Before;sep auto. }
 destruct(V293_owned_record_cell_update (94%positive,0%Z) Tint8(V293_byteval 6)(V293_byteval 4)
 _ _ _ _ _ _ _ _ eq_refl Owned)as(Ms&Store&Updated).
 assert(High:load Tint8 Ms(91%positive,0%Z)=Some(V293_byteval 4)).
 { eapply V293_record_star_load_l with(s:=CGstate OwnershipWaiting Ms(enabled::ci))
 (P:=V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval 4))(Q:=Atrue).
 - intros st H;apply V293_owned_record_cell_load;exact H.
 - clear -Updated;sep auto. }
 assert(Cache:load Tint8 Ms(94%positive,0%Z)=Some(V293_byteval 4)).
 { eapply V293_record_star_load_l with(s:=CGstate OwnershipWaiting Ms(enabled::ci));
 [intros st H;apply V293_owned_record_cell_load;exact H|exact Updated]. }
 assert(Counter:load Tint32 Ms(95%positive,0%Z)=Some(Vint32 Int.mone)).
 { eapply V293_record_star_load_l with(s:=CGstate OwnershipWaiting Ms(enabled::ci))
 (P:=V293_owned_record_cell((95%positive,0%Z),Tint32,Vint32 Int.mone))(Q:=Atrue).
 - intros st H;apply V293_owned_record_cell_load;exact H.
 - clear -Updated;sep auto. }
 destruct(V293_OSSched_byte_comparison_eval CGge CGle Ms 103%Z 108%Z 91%positive 94%positive
 4 4 ltac:(lia)ltac:(lia)eq_refl eq_refl eq_refl eq_refl High Cache)as[Guard _].
 exists M;exists Ms;split;[exact Before| ];split;[exact Store| ];split.
 - intros b i Outside;eapply V293_storebytes_outside;
 [exact Store|cbn[V293_byteval encode_val inj_bytes length];exact Outside].
 - split;[exact High| ];split;[exact Cache| ];split;[exact Counter| ];split;[exact Guard| ].
   unfold EPcode,EPbody;eapply V293_exit_same_priority_skip with(bh:=91%positive)(bc:=94%positive)(nc:=4);
   try reflexivity;try eassumption;lia.
Qed.
