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
Definition JHrest:list(addr*type):=
 [((96%positive,0%Z),Tint8);((97%positive,0%Z),Tint8)].
Definition JHcells:list(addr*type):=
 ((95%positive,0%Z),Tint32)::((91%positive,0%Z),Tint8)::((94%positive,0%Z),Tint8)::JHrest.
Definition JHinv:=V293_ready_storage_inv 80%positive 81%positive 82%positive 106%Z V293_tcb_type JHcells.
Definition JHprivate:=V293_owned_record_cell((98%positive,0%Z),Tint32,Vint32 Int.zero) ** RCframe.
Definition JHpost n:=
 V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval 4) **
 (V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval n) **
 (V293_owned_record_cell((95%positive,0%Z),Tint32,Vint32 Int.zero) **
 (V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady) ** CGframe 0 0))).
Definition JHstate M ci op:RstateOP:=
 (CGge,CGle,M,(fun _=>false),(false,nil,ci),RIabstract OwnershipWaiting,op).
Definition JHtail events now aop ci:=
 V293_ready_exit_tail 80%positive 81%positive 82%positive 103%Z 108%Z 109%Z 106%Z
 91%positive 94%positive 95%positive V293_tcb_type JHrest OwnershipWaiting OwnershipTasks
 events now OwnershipReady aop nil ci JHprivate 4 6 Int.zero.
Lemma JHaction_free : forall P,GoodInvAsrt P ->can_change_aop P.
Proof. induction P;simpl;intuition eauto. Qed.
Lemma JHpost_good : forall n,GoodInvAsrt(JHpost n).
Proof.
 intro n;unfold JHpost;repeat split;try apply V293_owned_cell_good;apply CGframe_good.
Qed.
Lemma JHtail_nonempty : forall enabled ci aop,exists M events now,
 load Tint8 M(94%positive,0%Z)=Some(V293_byteval 6) /\
 JHstate M(enabled::ci)(sched;;aop) |=JHtail events now aop(enabled::ci).
Proof.
 intros enabled ci aop.
 destruct(CGlocal_ready true enabled ci)as(M&Trace&Held&Target&Counter&Cache).
 change(CGstate OwnershipWaiting M(enabled::ci) |=
 SWINVt(V293ReadyTaskInvariant.V293_ready_inv 80%positive 81%positive 82%positive)OwnershipWaiting ** JHpost 6)in Held.
 eapply astar_mono in Held;[ |apply V293ReadyTaskInvariant.V293_ready_switch_full|intros s S;exact S].
 assert(Free:can_change_aop
 ((V293_shared_flags ** V293ReadyTaskInvariant.V293_ready_full 80%positive 81%positive 82%positive OwnershipWaiting) ** JHpost 6)).
 { split;[split|apply JHaction_free;apply JHpost_good].
   - unfold V293_shared_flags,isrclr;cbn[can_change_aop];repeat split;intros;exact I.
   - unfold V293ReadyTaskInvariant.V293_ready_full;cbn[can_change_aop];intros tasks events now;split.
     + intros tp;unfold Agvarmapsto,Aptrmapsto;cbn[can_change_aop];repeat split;intros;exact I.
     + split;[unfold V293_shared_fields;cbn[can_change_aop];auto|
       apply JHaction_free;apply V293_ready_payload_good]. }
 unfold CGstate in Held;pose proof(@change_aop_rule _ _ _ (sched;;aop) _ Held Free)as Changed.
 change(JHstate M(enabled::ci)(sched;;aop) |=
 ((V293_shared_flags ** V293ReadyTaskInvariant.V293_ready_full 80%positive 81%positive 82%positive OwnershipWaiting) ** JHpost 6))in Changed.
 unfold V293ReadyTaskInvariant.V293_ready_full in Changed;sep normal in Changed;sep destruct Changed.
 assert(Fixed:x=OwnershipTasks).
 { assert(Map:get(RIabstract OwnershipWaiting)abstcblsid=Some(abstcblist x)).
   { change(get(getabst(JHstate M(enabled::ci)(sched;;aop)))abstcblsid=Some(abstcblist x)).
     eapply V293_star_abst_get_l with(p:=Aabsdata abstcblsid(abstcblist x))(q:=Atrue).
     - apply V293_shared_abs_get.
     - unfold V293_shared_fields in Changed;clear Held;sep auto. }
   pose proof(RIfixed_tasks OwnershipWaiting);congruence. }subst x.
 assert(Halves:JHstate M(enabled::ci)(sched;;aop) |=
 (CurTid OwnershipWaiting ** CurTid OwnershipWaiting) **
 ((V293_shared_flags ** (V293_shared_fields OwnershipWaiting OwnershipTasks x0 x1 **
 V293_ready_payload 80%positive 81%positive 82%positive OwnershipTasks)) ** JHpost 6)).
 { eapply astar_mono with(P:=GV OSTCBCur@(Tptr x2)|->Vptr OwnershipWaiting).
   - intros s S;apply GV_separate_rw in S;unfold CurTid;sep auto.
   - intros s S;exact S.
   - clear Held;sep auto. }
 assert(Named:JHstate M(enabled::ci)(sched;;aop) |=
 V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady) **
 ((CurTid OwnershipWaiting ** CurTid OwnershipWaiting) **
 ((V293_shared_flags ** (V293_shared_fields OwnershipWaiting OwnershipTasks x0 x1 **
 V293_ready_payload 80%positive 81%positive 82%positive OwnershipTasks)) **
 (V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval 4) **
 (V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval 6) **
 (V293_owned_record_cell((95%positive,0%Z),Tint32,Vint32 Int.zero) ** CGframe 0 0)))))).
 { unfold JHpost in Halves;clear Changed Held;sep auto. }
 unfold JHstate in Named.
 apply V293_ready_named_target_frame with(target:=106%Z)in Named;[ |reflexivity].
 assert(B:(CGge,CGle,emp,(fun _=>false),(false,nil,enabled::ci),emp,sched;;aop) |=
 (V293_handoff_binding 103%Z 91%positive **
 (V293_handoff_binding 108%Z 94%positive **
 (V293_counter_bindings 109%Z 95%positive **
 (Agvarenv 106%Z(Tptr V293_tcb_type)(93%positive,0%Z) ** (Ais nil ** Acs(enabled::ci))))))).
 { repeat match goal with |- _ |= _ ** _ =>
     apply sat_split';exists(emp:mem);exists(emp:mem);exists(emp:osabst);exists(emp:osabst);
     split;[apply map_join_emp| ];split;[apply map_join_emp| ];split end;
   unfold V293_handoff_binding,V293_counter_bindings;cbn;
   repeat split;try reflexivity;
   try(exists 91%positive;repeat split;reflexivity);
   try(exists 94%positive;repeat split;reflexivity);
   try(exists 95%positive;repeat split;reflexivity);
   try(exists 93%positive;repeat split;reflexivity);
   intros[v E];vm_compute in E;discriminate. }
 assert(WithBindings:JHstate M(enabled::ci)(sched;;aop) |=
 (V293_handoff_binding 103%Z 91%positive **
 (V293_handoff_binding 108%Z 94%positive **
 (V293_counter_bindings 109%Z 95%positive **
 (Agvarenv 106%Z(Tptr V293_tcb_type)(93%positive,0%Z) ** (Ais nil ** Acs(enabled::ci)))))) **
 (<||sched;;aop||> ** ((GV 106%Z@(Tptr V293_tcb_type)|->Vptr OwnershipReady) **
 ((CurTid OwnershipWaiting ** CurTid OwnershipWaiting) **
 ((V293_shared_flags ** (V293_shared_fields OwnershipWaiting OwnershipTasks x0 x1 **
 V293_ready_payload 80%positive 81%positive 82%positive OwnershipTasks)) **
 (V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval 4) **
 (V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval 6) **
 (V293_owned_record_cell((95%positive,0%Z),Tint32,Vint32 Int.zero) ** CGframe 0 0)))))))).
 { apply sat_split';exists(emp:mem);exists M;exists(emp:osabst);exists(RIabstract OwnershipWaiting).
   split;[apply map_join_comm;apply map_join_emp| ];split;[apply map_join_comm;apply map_join_emp| ];split;[exact B| ].
   apply astar_l_aop'_intro with(aop:=sched;;aop)in Named;[exact Named|reflexivity]. }
 exists M;exists x0;exists x1;split;[exact Cache| ].
 unfold JHtail,V293_ready_exit_tail,V293_storage_open,V293_handoff_byte,V293_counter_cell.
 unfold JHpost,CGframe,CGextra in WithBindings;cbn[V293_owned_record_cells]in WithBindings.
 unfold V293_owned_record_cell in WithBindings.
 unfold JHprivate,JHrest;cbn[V293_storage];unfold V293_storage_cell,V293_owned_record_cell,
 Aptrmapsto;cbn[addrval_to_addr Int.unsigned].
 clear Halves Changed Held Named B;sep auto.

Qed.

Definition JHvalues n : list V293_record_cell :=
 [((95%positive,0%Z),Tint32,Vint32 Int.zero);((91%positive,0%Z),Tint8,V293_byteval 4);
  ((94%positive,0%Z),Tint8,V293_byteval n);((96%positive,0%Z),Tint8,V293_byteval 0);
  ((97%positive,0%Z),Tint8,V293_byteval 0)].
Definition JHextra := V293_ready_storage_extra 106%Z V293_tcb_type JHcells.
Lemma JHdispatch : forall ge le M ir aux O op,
 get ge 106%Z=Some(93%positive,Tptr V293_tcb_type) ->
 (ge,le,M,ir,aux,O,op) |= V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady) ->
 (ge,le,M,ir,aux,O,op) |= V293_dispatch_cell 106%Z V293_tcb_type.
Proof.
 intros ge le M ir aux O op Env Cell.
 exists(Vptr OwnershipReady);apply astar_l_apure_intro;[ |reflexivity].
 eapply V293_ready_named_target;[exact Env|exact Cell].
Qed.
Lemma JHclose : forall M ci n,
 CGstate OwnershipWaiting M ci |=
 SWINVt(V293ReadyTaskInvariant.V293_ready_inv 80%positive 81%positive 82%positive)OwnershipWaiting ** JHpost n ->
 CGstate OwnershipWaiting M ci |= SWINVt JHinv OwnershipWaiting ** JHprivate.
Proof.
 intros M ci n Held.
 assert(Raw:CGstate OwnershipWaiting M ci |= V293_owned_record_cells(JHvalues n) **
   (V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady) **
   (SWINVt(V293ReadyTaskInvariant.V293_ready_inv 80%positive 81%positive 82%positive)OwnershipWaiting ** JHprivate))).
 { unfold JHpost,CGframe,CGextra,JHvalues,JHprivate in *.
   cbn [V293_owned_record_cells STcache] in *;sep auto. }
 eapply astar_mono in Raw;[ |apply V293_owned_cells_storage|intros st H;exact H].
 change(CGstate OwnershipWaiting M ci |= V293_storage JHcells **
   (V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady) **
   (SWINVt(V293ReadyTaskInvariant.V293_ready_inv 80%positive 81%positive 82%positive)OwnershipWaiting ** JHprivate)))in Raw.
 assert(Env:get CGge 106%Z=Some(93%positive,Tptr V293_tcb_type))by reflexivity.
 destruct (CGstate OwnershipWaiting M ci) as [[[[[[ge le] mem] ir] aux] O] op] eqn:State.
 assert(Env':get ge 106%Z=Some(93%positive,Tptr V293_tcb_type)).
 { unfold CGstate in State;inversion State;subst;exact Env. }
 assert(Named:(ge,le,mem,ir,aux,O,op) |=
 V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady) **
 (SWINVt(V293ReadyTaskInvariant.V293_ready_inv 80%positive 81%positive 82%positive)OwnershipWaiting **
 (V293_storage JHcells ** JHprivate)))by(sep auto).
 apply sat_split in Named;destruct Named as(m1&m2&o1&o2&JM&JO&Target&Rest).
 assert(Packed:(ge,le,mem,ir,aux,O,op) |= V293_dispatch_cell 106%Z V293_tcb_type **
 (SWINVt(V293ReadyTaskInvariant.V293_ready_inv 80%positive 81%positive 82%positive)OwnershipWaiting **
 (V293_storage JHcells ** JHprivate))).
 { apply sat_split';exists m1;exists m2;exists o1;exists o2.
   split;[exact JM| ];split;[exact JO| ];split;[eapply JHdispatch;[exact Env'|exact Target]|exact Rest]. }
 change((ge,le,mem,ir,aux,O,op) |= SWINVt JHinv OwnershipWaiting ** JHprivate).
 eapply astar_mono with(P:=SWINVt(V293ReadyTaskInvariant.V293_ready_inv 80%positive 81%positive 82%positive)OwnershipWaiting ** JHextra)(Q:=JHprivate).
 - intros st H;apply V293_ready_storage_switch_resources;exact H.
 - intros st H;exact H.
 - unfold JHextra,V293_ready_storage_extra;clear Held Raw Rest Target;sep auto.
Qed.


Definition JHswitch_result M Mf enabled ci ip cst :=
 lpstep(RCprogram,(CGpo,CGempty,ip))FCswitch_tasks cst
 (CGge,CGswitch_envs,M,(fun _=>false),CGswitch_aux enabled ci)OwnershipWaiting
 (set FCswitch_tasks OwnershipWaiting(SKIP,(kenil,FCpending)))cst
 (CGge,CGswitch_envs,Mf,(fun _=>false),CGswitch_aux enabled ci)OwnershipReady /\
 (CGge,CGle,Mf,(fun _=>false),(false,nil,enabled::ci),
 set(RIabstract OwnershipWaiting)curtid(oscurt OwnershipReady),spec_done None) |=
 SWINVt JHinv OwnershipReady ** JHprivate.
Lemma JHswitch : forall M enabled ci ip cst,
 load(Tptr V293_tcb_type)M(93%positive,0%Z)=Some(Vptr OwnershipReady) ->
 CGstate OwnershipWaiting M(enabled::ci) |=SWINVt JHinv OwnershipWaiting ** JHprivate ->
 exists Mf,JHswitch_result M Mf enabled ci ip cst /\
 (forall b i,b<>1%positive ->get Mf(b,i)=get M(b,i)).
Proof.
 intros M enabled ci ip cst Target Held.
 destruct(V293_ready_storage_switch_step 80%positive 81%positive 82%positive 106%Z V293_tcb_type JHcells
 RCprogram CGpo CGempty ip FCswitch_tasks cst FCpending OwnershipWaiting OwnershipReady
 93%positive 1%positive CGge CGle CGswitch_envs M(fun _=>false)(false,nil,enabled::ci)
 (CGswitch_aux enabled ci)(RIabstract OwnershipWaiting)(spec_done None)JHprivate
 (map_get_set _ _ _)(map_get_set _ _ _)(map_get_set _ _ _)eq_refl Target eq_refl Held)
 as(Mf&Step&Store&After&Current&Outside).
 exists Mf;split;[split;assumption| ]. intros b i Apart;apply Outside;left;exact Apart.
Qed.

(* The shared starting heap is AFTER the existing call/guard/counter prefix.
   We compare only this suffix; we do not increment its counter a second time. *)
Theorem JHcopy_ablation : forall enabled ci ip cst,exists M Mc Mwith Mwithout,
 cstepstar CGprogram(curs(V293_interrupt_handoff 103%Z 108%Z 106%Z),(kenil,CGpending))(CGge,CGle,M)
 (curs(sprim(switch 106%Z)),(kenil,CGpending))(CGge,CGle,Mc) /\
 store Tint8 M(94%positive,0%Z)(V293_byteval 4)=Some Mc /\
 (forall b i,b<>94%positive \/i<>0%Z ->get Mc(b,i)=get M(b,i)) /\
 JHswitch_result M Mwithout enabled ci ip cst /\
 JHswitch_result Mc Mwith enabled ci ip cst /\
 load Tint8 Mwith(94%positive,0%Z)=Some(V293_byteval 4) /\
 load Tint8 Mwithout(94%positive,0%Z)=Some(V293_byteval 6).
Proof.
 intros enabled ci ip cst.
 destruct(CGlocal_ready true enabled ci)as(M&Trace&Held&Target&Counter&Cache).
 assert(Old:CGstate OwnershipWaiting M(enabled::ci) |=
 SWINVt(V293ReadyTaskInvariant.V293_ready_inv 80%positive 81%positive 82%positive)OwnershipWaiting ** JHpost 6).
 { exact Held. }
 assert(Raw:CGstate OwnershipWaiting M(enabled::ci) |=
 SWINVt(V293ReadyTaskInvariant.V293_ready_inv 80%positive 81%positive 82%positive)OwnershipWaiting **
 (V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval 6) **
 (V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval 4) **
 (V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady) **
 (V293_owned_record_cell((95%positive,0%Z),Tint32,Vint32 Int.zero) ** CGframe 0 0))))).
 { unfold JHpost in Old;clear Held;sep auto. }
 destruct(V293_handoff_copy_execution 80%positive 81%positive 82%positive CGprogram CGpending
 CGge CGle M(fun _=>false)(false,nil,enabled::ci)(RIabstract OwnershipWaiting)(spec_done None)
 OwnershipWaiting(V293_owned_record_cell((95%positive,0%Z),Tint32,Vint32 Int.zero) ** CGframe 0 0)
 103%Z 108%Z 106%Z 91%positive 94%positive 93%positive 4 6 OwnershipReady
 ltac:(lia)eq_refl eq_refl eq_refl eq_refl Raw)as(Mc&Copy&Store&Copied&OutsideCopy).
 assert(OldCopy:CGstate OwnershipWaiting Mc(enabled::ci) |=
 SWINVt(V293ReadyTaskInvariant.V293_ready_inv 80%positive 81%positive 82%positive)OwnershipWaiting ** JHpost 4).
 { unfold JHpost;clear Held Raw Old;sep auto. }
 assert(TargetCopy:load(Tptr V293_tcb_type)Mc(93%positive,0%Z)=Some(Vptr OwnershipReady)).
 { rewrite(V293_load_block_frame _ M Mc 93%positive 0%Z ltac:(intros;apply OutsideCopy;left;discriminate));exact Target. }
 assert(CacheCopy:load Tint8 Mc(94%positive,0%Z)=Some(V293_byteval 4)).
 { eapply V293_record_star_load_l with(s:=(CGge,CGle,Mc,(fun _=>false),(false,nil,enabled::ci),RIabstract OwnershipWaiting,spec_done None))
 (P:=V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval 4))(Q:=Atrue).
 - intros st H;apply V293_owned_record_cell_load;exact H.
 - clear Held Raw Old OldCopy;sep auto. }
 destruct(JHswitch M enabled ci ip cst Target (JHclose M(enabled::ci)6 Old))as(Mwithout&Without&OutsideWithout).
 destruct(JHswitch Mc enabled ci ip cst TargetCopy (JHclose Mc(enabled::ci)4 OldCopy))as(Mwith&With&OutsideWith).
 exists M;exists Mc;exists Mwith;exists Mwithout.
 split;[exact Copy| ];split;[exact Store| ];split;[exact OutsideCopy| ];
 split;[exact Without| ];split;[exact With| ];split.
 - rewrite(V293_load_block_frame _ Mc Mwith 94%positive 0%Z ltac:(intros;apply OutsideWith;discriminate));exact CacheCopy.
 - rewrite(V293_load_block_frame _ M Mwithout 94%positive 0%Z ltac:(intros;apply OutsideWithout;discriminate));exact Cache.
Qed.
