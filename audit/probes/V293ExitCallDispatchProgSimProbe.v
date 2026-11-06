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

Require Import CertiOS.audit.probes.V293ExitDispatchProgSimProbe.
Require Import CertiOS.audit.probes.V293SchedCallProgSimProbe.
Require Import CertiOS.audit.probes.V293SchedCallEntryProgSimProbe.
Require Import CertiOS.certiucos.v293.proofs.V293ExitCallDispatchProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.

Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.framework.auxlibs.MapLib.

Definition XPbody:=V293_exit_boundary_dispatch 105%Z 103%Z 106%Z 108%Z 109%Z 107%Z
 (V293_interrupt_handoff 103%Z 108%Z 106%Z).
Definition XPcode:code:=(curs XPbody,(kenil,HPpending)).
Definition XPtasks:tasks:=set HPtasks OwnershipWaiting XPcode.

Lemma XPtable : load(Tptr V293_tcb_type)CFfinal(82%positive,(4*Z.of_nat 4)%Z)=Some(Vptr OwnershipReady).
Proof.
 assert(Ready:V293_ready_loads CEM 80%positive 81%positive 82%positive 16 0 RTentries).
 { eapply V293_ready_loads_sub with(M:=CGwith OwnershipWaiting true 0 0).
   - exists RTdecoder;apply CGdecoder_join.
   - eapply V293_ready_loads_sub with(M:=RTfull OwnershipWaiting).
     + exists(CGoutputs true 0 0);apply CGoutputs_join.
     + apply RTliteral_loads. }
 destruct Ready as[Low[High[Group Table]]].
 specialize(Table 4 ltac:(lia)).
 unfold V293_table_loads in *.
 change(load(Tptr V293_tcb_type)CEM(82%positive,(4*Z.of_nat 4)%Z)=Some(Vptr OwnershipReady))in Table.
 unfold CFfinal;unfold load,loadm in *;cbn[typelen loadbytes]in *.
 repeat rewrite V293_write_byte_other by discriminate;exact Table.
Qed.

Lemma XPscheduled_canonical : forall enabled ci,
 exists M,
 store(Tptr V293_tcb_type)CFfinal(93%positive,0%Z)(Vptr OwnershipReady)=Some M /\
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
 rewrite Selected in After,Skipped,High.
 assert(Cells:CGstate OwnershipWaiting Mskip(enabled::ci)|=
 V293_owned_record_cells (((91%positive,0%Z),Tint8,V293_byteval 4)::nil) ** Atrue).
 { cbn[V293_owned_record_cells];clear -Skipped;sep auto. }
 destruct(V293_owned_cells_byte_writable (((91%positive,0%Z),Tint8,V293_byteval 4)::nil)
 (91%positive,0%Z)(V293_byteval 4)Atrue CGge CGle Mskip(fun _=>false)
 (false,nil,enabled::ci)(RIabstract OwnershipWaiting)(spec_done None)
 ltac:(simpl;auto)Cells)as[raw Full].
 pose proof(V293_full_byte_load_encoding Mskip(91%positive,0%Z)4 raw Full High)as Output.
 assert(Canonical:Mskip=CFfinal).
 { apply HalfPermMap.extensionality;intros[c i].
   change(get Mskip(c,i)=get CFfinal(c,i)).
   destruct(Pos.eq_dec c 91%positive)as[E|E].
   - subst c;destruct(Z.eq_dec i 0)as[Z0|Z0].
     + subst i;unfold CFfinal,V293_write_byte;rewrite map_get_set;exact Output.
     + unfold CFfinal,V293_write_byte;rewrite map_get_set' by congruence.
       apply CallFrame;congruence.
   - unfold CFfinal,V293_write_byte;rewrite map_get_set' by congruence.
     apply CallFrame;congruence. }
 rewrite Canonical in Store.
 exists M;split;[exact Store| ];split;[exact Exec| ].
 unfold EPbefore,CGstate;clear -After;sep auto.
Qed.

Lemma XPbridge : forall M M1 Mc Mf enabled ci ip,
 store(Tptr V293_tcb_type)CFfinal(93%positive,0%Z)(Vptr OwnershipReady)=Some M ->
 evalval(V293_OSSched_different 103%Z 108%Z)(CGge,CGle,M)=Some(Vint32 Int.one) ->
 load Tint32 M(95%positive,0%Z)=Some(Vint32 Int.mone) ->
 store Tint32 M(95%positive,0%Z)(Vint32(Int.add Int.mone Int.one))=Some M1 ->
 load Tint8 M1(91%positive,0%Z)=Some(V293_byteval 4) ->
 store Tint8 M1(94%positive,0%Z)(V293_byteval 4)=Some Mc ->
 load(Tptr V293_tcb_type)Mc(93%positive,0%Z)=Some(Vptr OwnershipReady) ->
 store(Tptr V293_tcb_type)Mc(1%positive,0%Z)(Vptr OwnershipReady)=Some Mf ->
 ProgSim(RCprogram,(CGpo,CGempty,ip))XPtasks(SPS CEM enabled ci)
 SPph HPTh(RIabstract OwnershipWaiting)HPcst OwnershipWaiting.
Proof.
 intros M M1 Mc Mf enabled ci ip TargetStore Guard Counter Increment High Copy Target Store.
 unfold SPS.
 eapply V293_exit_call_dispatch_progsim with(le:=CGle)(Mt:=M)(M1:=M1)(Mc:=Mc)(Mf:=Mf)
 (next:=OwnershipReady)(current:=108%Z)(counter:=109%Z)(ks:=HPpending)
 (f:=107%Z)(unmap:=100%Z)(group:=101%Z)(rows:=102%Z)(high:=103%Z)(y:=104%Z)
 (table:=105%Z)(target:=106%Z)(bt:=92%positive)(bg:=81%positive)(br:=80%positive)
 (bh:=91%positive)(bp:=82%positive)(bo:=93%positive)(lo:=16)(hi:=0)(g:=1)
 (oldhigh:=Byte(Byte.repr 88))(value:=Vptr OwnershipReady)
 (bk:=95%positive)(count:=Int.mone)(b:=94%positive)(v:=V293_byteval 4)
 (bc:=1%positive)(tp:=V293_tcb_type)(si:=nil)(cs:=enabled::ci)(Thf:=HPThf)(Of:=SPOf);
 try reflexivity;try eassumption;try discriminate;try lia.
 - exact(proj1 CFinput).
 - exact(proj2 CFinput).
 - exists 4;left;repeat split;try lia;reflexivity.
 - change(4<13);lia.
 - exact XPtable.
 - exact HPcontext.
 - eapply hp_stepS;[apply HPschedule|apply hp_stepO].
 - unfold XPtasks;rewrite tasks_set_a_set_a;apply HPpost.
Qed.

Theorem XPactual_call_dispatch_simulation : forall enabled ci ip,
 exists M M1 Mc Mf,
 store(Tptr V293_tcb_type)CFfinal(93%positive,0%Z)(Vptr OwnershipReady)=Some M /\
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
 ProgSim(RCprogram,(CGpo,CGempty,ip))XPtasks(SPS CEM enabled ci)
 SPph HPTh(RIabstract OwnershipWaiting)HPcst OwnershipWaiting.
Proof.
 intros enabled ci ip.
 destruct(XPscheduled_canonical enabled ci)as(M&TargetStore&Schedule&Before).
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
 exists M;exists M1;exists Mc;exists Mf;split;[exact TargetStore| ];split;[exact Schedule| ];split;[exact Counter| ];
 split;[exact Increment| ];split;[exact Counter1| ];split.
 - eapply V293_cstepstar_trans;[ |exact Copy].
   exact Prefix.
 - split;[apply GHrejected;exact CacheCopy| ];split;[exact PhysicalStore| ].
   eapply XPbridge;try eassumption;rewrite Wrap;exact Increment.
Qed.
(* Keep the computed priority and every other byte; omit only the target
   pointer store. This checks its exact heap contract, not a mutant program. *)
Theorem XPomit_target_rejected :
 load Tint8 CFfinal(91%positive,0%Z)=Some(V293_byteval 4) /\
 load(Tptr V293_tcb_type)CFfinal(93%positive,0%Z)=Some(Vptr OwnershipWaiting) /\
 ~load(Tptr V293_tcb_type)CFfinal(93%positive,0%Z)=Some(Vptr OwnershipReady).
Proof.
 assert(Read:load(Tptr V293_tcb_type)CEM(93%positive,0%Z)=Some(Vptr OwnershipWaiting)).
 { eapply V293_record_star_load_l with(s:=CGstate OwnershipWaiting CEM nil)
 (P:=V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipWaiting))(Q:=Atrue).
   - intros st Held;apply V293_owned_record_cell_load;exact Held.
   - pose proof(CEtyped_heap nil)as Held;sep auto. }
 assert(Still:load(Tptr V293_tcb_type)CFfinal(93%positive,0%Z)=Some(Vptr OwnershipWaiting)).
 { unfold CFfinal;unfold load,loadm in *;cbn[typelen loadbytes]in *.
   repeat rewrite V293_write_byte_other by discriminate;exact Read. }
 split;[unfold CFfinal;apply V293_write_byte_load;lia| ];split;[exact Still| ].
 intro Equal;rewrite Still in Equal;discriminate.
Qed.
