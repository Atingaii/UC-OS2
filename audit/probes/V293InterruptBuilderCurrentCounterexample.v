Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStoragePrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBuilders.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.audit.probes.V293InterruptBoundDispatchContinuousProbe.
Require Import CertiOS.audit.probes.V293InterruptChangedContinuousProbe.
Require Import CertiOS.audit.probes.V293OSIntExitReadyDynamicProbe.
Require Import CertiOS.audit.probes.V293OSIntExitReadyBodyProbe.
Require Import CertiOS.audit.probes.V293OSIntExitLocalDispatchProbe.
Require Import CertiOS.audit.probes.V293ReadyTaskInvariantProbe.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.audit.probes.V293TaskRecordInvariantProbe.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptBoundEntry.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrent.
Require Import CertiOS.audit.probes.V293InterruptBoundEntryProbe.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptChangedContinuous.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyInternal.
(* A typed builder counterexample, not a reachable kernel execution. *)
Require Import CertiOS.audit.probes.V293InterruptCommonDispatchProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.framework.proof.memory_prop.
Require Import CertiOS.framework.proof.lmachLib.
Import ListNotations.
Local Open Scope nat_scope.

Definition NCsnapshot n:=V293_changed_irq_snapshot
 100%Z 101%Z 102%Z 103%Z 105%Z 106%Z 108%Z 109%Z 112%Z 110%Z 111%Z
 92%positive 81%positive 80%positive 91%positive 82%positive 93%positive 94%positive 95%positive
 99%positive 96%positive 97%positive nil 16 0 n RTentries OwnershipTasks emp Int.zero
 (V293_byteval 88)(Vptr OwnershipWaiting)Int.zero 0(spec_done None)
 (isrupd(fun _:hid=>false)0 true)[0]OwnershipWaiting.
Definition NCframe:asrt:=
 (<||sched;;spec_done None||> ** OS[isrupd(fun _:hid=>false)0 true,false,[0],nil]) **
 ((GV OSTCBCur@(Tptr V293_tcb_type)|->Vptr OwnershipWaiting) **
 (V293_shared_fields OwnershipWaiting OwnershipTasks emp Int.zero **
 ((GV 106%Z@(Tptr V293_tcb_type)|->Vptr OwnershipWaiting) **
 (V293_inputs_full 92%positive 81%positive 80%positive 16 0 **
 ((PV(91%positive,Int.zero)@Tint8|->V293_byteval 88) **
 (V293_array true 82%positive 0 4(Tptr V293_tcb_type)RTentries **
 ((PV(95%positive,Int.zero)@Tint32|->Vint32 Int.zero) **
 (V293_storage nil **
 (V293_sched_globals 100%Z 101%Z 102%Z 103%Z 92%positive 81%positive 80%positive 91%positive **
 ((Aemp ** V293_owned_task_records OwnershipTasks) **
 (V293_exit_builder_globals 105%Z 106%Z 108%Z 109%Z 110%Z 111%Z 112%Z V293_tcb_type
 82%positive 93%positive 94%positive 95%positive 96%positive 97%positive 99%positive **
 (Amapsto(99%positive,0%Z)Tint8 true(V293_byteval 1) **
 (Amapsto(96%positive,0%Z)Tint8 true(V293_byteval 0) **
 (Amapsto(97%positive,0%Z)Tint8 true(V293_byteval 0) ** A_dom_lenv nil)))))))))))))).
Lemma NCsplit : forall n,NCsnapshot n <==>
 Amapsto(94%positive,0%Z)Tint8 true(V293_byteval n) ** NCframe.
Proof.
 intros n st;unfold NCsnapshot,V293_changed_irq_snapshot,V293_changed_irq_physical,
 V293_ready_builder_memory,NCframe;split;intro H;sep auto.
Qed.
Lemma NCbuilder : forall n,n<256 ->NCsnapshot n ==>BCpre.
Proof.
 intros n Bound st H;unfold NCsnapshot in H.
 apply(V293_changed_entry_BuildintPre
 100%Z 101%Z 102%Z 103%Z 105%Z 106%Z 108%Z 109%Z 112%Z 110%Z 111%Z
 92%positive 81%positive 80%positive 91%positive 82%positive 93%positive 94%positive 95%positive
 99%positive 96%positive 97%positive nil 16 0 n RTentries OwnershipTasks emp Int.zero
 (V293_byteval 88)(Vptr OwnershipWaiting)Int.zero 0(spec_done None)(fun _:hid=>false)nil
 OwnershipWaiting BCintspec BCpre);try reflexivity;try lia.
 - exact RTliteral_rel.
 - vm_compute;repeat constructor.
 - exact H.
Qed.
Lemma NCwrite : forall M O,CCstate M O|=NCsnapshot 6 ->
 exists M4,store Tint8 M(94%positive,0%Z)(V293_byteval 4)=Some M4 /\
 CCstate M4 O|=NCsnapshot 4.
Proof.
 intros M O H;apply NCsplit in H;unfold CCstate in *.
 destruct(V293_tick_raw_slot_update (94%positive,0%Z) Tint8 (V293_byteval 6)
 (V293_byteval 4) NCframe JBge emp M (isrupd(fun _:hid=>false)0 true)
 (false,[0],nil) O (sched;;spec_done None) eq_refl H)as(M4&S&K).
 exists M4;split;[exact S|apply NCsplit].
 unfold V293_owned_record_cell in K;sep auto.
Qed.
Lemma NCload : forall n M O,n<256 ->CCstate M O|=NCsnapshot n ->
 load Tint8 M(94%positive,0%Z)=Some(V293_byteval n).
Proof.
 intros n M O Bound H;apply NCsplit in H.
 change(load Tint8(getmem(CCstate M O))(94%positive,0%Z)=Some(V293_byteval n)).
 eapply V293_record_star_load_l;[ |exact H].
 intros st K;eapply mapstoval_load;[apply V293_byte_type;exact Bound|exact(proj1 K)].
Qed.
Lemma NCstore_only : forall M M4,
 store Tint8 M(94%positive,0%Z)(V293_byteval 4)=Some M4 ->
 M4=V293_put_byte M(94%positive,0%Z)4.
Proof.
 intros M M4 S.
 change(match get M(94%positive,0%Z)with
 |Some(true,_)=>Some(V293_put_byte M(94%positive,0%Z)4)
 |_=>None end=Some M4)in S.
 destruct(get M(94%positive,0%Z))as [[permission previous] | ] in S;try discriminate.
 destruct permission;inversion S;reflexivity.
Qed.
Theorem NCtyped_single_byte : exists M Mf O Of M4 F4,
 join M Mf(JBmemory 0 Int.zero Int.zero) /\join O Of(RIabstract OwnershipWaiting) /\
 store Tint8 M(94%positive,0%Z)(V293_byteval 4)=Some M4 /\
 store Tint8(JBmemory 0 Int.zero Int.zero)(94%positive,0%Z)(V293_byteval 4)=Some F4 /\
 join M4 Mf F4 /\CCstate M O|=BCpre /\CCstate M4 O|=BCpre /\
 CCstate M4 O|=NCsnapshot 4 /\
 load Tint8 M(94%positive,0%Z)=Some(V293_byteval 6) /\
 load Tint8 M4(94%positive,0%Z)=Some(V293_byteval 4) /\
 (forall a,a<>(94%positive,0%Z)->get M4 a=get M a) /\
 (forall a,a<>(94%positive,0%Z)->get F4 a=get(JBmemory 0 Int.zero Int.zero)a).
Proof.
 destruct BEchanged_same_state as(M&Mf&O&Of&JM&JO&H&B&W).
 change(CCstate M O|=NCsnapshot 6)in H.
 destruct(NCwrite M O H)as(M4&S&K).
 destruct(store_mono _ _ _ _ _ _ _ JM S)as(F4&SF).
 exists M;exists Mf;exists O;exists Of;exists M4;exists F4.
 split;[exact JM| ];split;[exact JO| ];split;[exact S| ];split;[exact SF| ];split.
 - apply map_join_comm;eapply join_store_join;[apply map_join_comm;exact JM|exact S|exact SF].
 - split;[exact B| ];split;[apply(NCbuilder 4);[lia|exact K]| ];split;[exact K| ];split.
   + apply(NCload 6 M O);[lia|exact H].
   + split;[apply(NCload 4 M4 O);[lia|exact K]| ];split.
     * intros a D;rewrite(NCstore_only M M4 S);apply V293_put_byte_other;exact D.
     * intros a D;rewrite(NCstore_only _ F4 SF);apply V293_put_byte_other;exact D.
Qed.
Lemma NCcurrent_mismatch :
 V293_ready_select 16 0(V293_ready_group 16 0)=4 /\
 V293_current_task OwnershipTasks OwnershipWaiting 6 /\
 ~V293_current_task OwnershipTasks OwnershipWaiting 4 /\
 ~sched_self V293_scheduler(RIabstract OwnershipWaiting).
Proof.
 split;[reflexivity| ];split.
 - split;[lia| ];eexists;eexists;vm_compute;reflexivity.
 - split;[ |exact(proj2 CDcurrent_ablation)].
   intros[_[st[msg H]]];vm_compute in H;discriminate.
Qed.
Definition NCcurrent_relation(st:RstateOP):Prop:=exists t tasks n,
 get(getabst st)curtid=Some(oscurt t) /\
 get(getabst st)abstcblsid=Some(abstcblist tasks) /\n<256 /\
 load Tint8(getmem st)(94%positive,0%Z)=Some(V293_byteval n) /\
 V293_current_task tasks t n.
Lemma NCabstract : forall n M O,CCstate M O|=NCsnapshot n ->
 get O curtid=Some(oscurt OwnershipWaiting) /\
 get O abstcblsid=Some(abstcblist OwnershipTasks).
Proof.
 intros n M O H;unfold NCsnapshot,V293_changed_irq_snapshot,V293_changed_irq_physical,
 V293_ready_builder_memory in H.
 assert(P:CCstate M O|=V293_shared_fields OwnershipWaiting OwnershipTasks emp Int.zero **Atrue)by(sep auto).
 split.
 - change(get(getabst(CCstate M O))curtid=Some(oscurt OwnershipWaiting)).
   eapply V293_star_abst_get_l;[ |exact P].
   intros st K;exact(proj1(V293_shared_fields_get _ _ _ _ st K)).
 - change(get(getabst(CCstate M O))abstcblsid=Some(abstcblist OwnershipTasks)).
   eapply V293_star_abst_get_l;[ |exact P].
   intros st K;exact(proj1(proj2(V293_shared_fields_get _ _ _ _ st K))).
Qed.
Lemma NCnegative_relation : forall M O,CCstate M O|=NCsnapshot 4 ->
 ~NCcurrent_relation(CCstate M O).
Proof.
 intros M O H[t[tasks[n[C[T[N[L Cur]]]]]]].
 destruct(NCabstract 4 M O H)as[C0 T0].
 change(get O curtid=Some(oscurt t))in C.
 change(get O abstcblsid=Some(abstcblist tasks))in T.
 assert(t=OwnershipWaiting)by congruence;assert(tasks=OwnershipTasks)by congruence;subst t tasks.
 change(load Tint8 M(94%positive,0%Z)=Some(V293_byteval n))in L.
 pose proof(NCload 4 M O ltac:(lia) H)as L4.
 assert(n=4)by(eapply RTbyte_injective;[exact N|lia|congruence]);subst n.
 exact(proj1(proj2(proj2 NCcurrent_mismatch))Cur).
Qed.
Theorem NCbuilder_not_current_relation :
 Some BCpre=BuildintPre 0 BCintspec(fun _:hid=>false)nil RDinv LDli OwnershipWaiting nil /\
 ~(forall st,st|=BCpre ->NCcurrent_relation st).
Proof.
 split;[reflexivity| ];intro All.
 destruct NCtyped_single_byte as(M&Mf&O&Of&M4&F4&JM&JO&S&SF&J4&B&B4&H&Rest).
 exact(NCnegative_relation M4 O H(All(CCstate M4 O)B4)).
Qed.
Lemma NCpositive_relation : forall M O,CCstate M O|=NCsnapshot 6 ->
 NCcurrent_relation(CCstate M O).
Proof.
 intros M O H;destruct(NCabstract 6 M O H)as[C T].
 exists OwnershipWaiting;exists OwnershipTasks;exists 6.
 split;[exact C| ];split;[exact T| ];split;[lia| ];split.
 - apply(NCload 6 M O);[lia|exact H].
 - exact(proj1(proj2 NCcurrent_mismatch)).
Qed.
Theorem NCrelation_single_factor : exists M O M4,
 CCstate M O|=BCpre /\CCstate M4 O|=BCpre /\
 NCcurrent_relation(CCstate M O) /\~NCcurrent_relation(CCstate M4 O) /\
 store Tint8 M(94%positive,0%Z)(V293_byteval 4)=Some M4 /\
 (forall a,a<>(94%positive,0%Z)->get M4 a=get M a).
Proof.
 destruct BEchanged_same_state as(M&Mf&O&Of&JM&JO&H&B&W).
 change(CCstate M O|=NCsnapshot 6)in H.
 destruct(NCwrite M O H)as(M4&S&K).
 exists M;exists O;exists M4;split;[exact B| ];split;[apply(NCbuilder 4);[lia|exact K]| ];split.
 - apply NCpositive_relation;exact H.
 - split;[apply NCnegative_relation;exact K| ];split;[exact S| ].
   intros a D;rewrite(NCstore_only _ _ S);apply V293_put_byte_other;exact D.
Qed.
