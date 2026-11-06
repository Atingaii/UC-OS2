(* Same finite CallSpec and frozen byte fixtures; only global 98 / block710 added. *)
Require Import CertiOS.audit.probes.V293TaskCreateTCBCallProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPublish.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateBodyFailure.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtSuffix.
Require Import CertiOS.audit.probes.V293TCBSuccessInternalProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateSuccessHoare.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.proofs.V293TCBSnapshotInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TCBSuccessInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEmptyInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitFunction.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.audit.probes.V293TCBSuccessInternalProbe.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import Coq.Lists.List.ListNotations.
Local Open Scope nat_scope.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateTCBCall.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtCalls.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBClear.
Require Import CertiOS.certiucos.v293.proofs.V293StartRecord.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293TCBHookCall.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293TCBLinkedHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitPrefix.
Import Coq.Lists.List.ListNotations.
Local Open Scope nat_scope.



Definition IdleGE : env := set SuccessGE 98%Z (710%positive,Tint8).
Definition IdleState M cs : RstateOP :=
 (IdleGE,CallLE,M,(fun _=>false),(false,[],cs),(emp:osabst),spec_done None).
Definition IdleByte := V293_encoded_memory 710%positive 0 false (encode_val Tint8(Vint32 Int.zero)).
Definition IdlePre present cs :=
 getasrt(CallFpre present cs SuccessArguments[logic_val SuccessHead]SuccessTid) **
 LV 209%Z @ Tint8 |->Vundef **
 V293_create_tcb_arguments 11 Vnull Vnull(Vint32 Int.zero)(Vint32(Int.repr 128))Vnull(Vint32 Int.zero)
 (V293_create_idle_running 98%Z 710%positive ** CallFrame).
Definition IdlePost present cs := V293_create_success_return 98%Z 710%positive
 (getasrt(CallFpost present cs SuccessArguments(Some(Vint32 Int.zero))[logic_val SuccessHead]SuccessTid) **
 CallArgs Vnull Vnull).
Definition IdleBody := sseq
 (V293_TaskCreateExt_TCB_call 209%Z 900%Z 101%Z 108%Z 205%Z 206%Z 207%Z 208%Z 204%Z)
 (V293_TaskCreateExt_suffix 92%Z 101%Z 209%Z 98%Z 901%Z).
Theorem IdleSameSpecCallee : forall present cs saved,
 InfRules(CallSpec present cs)V293_scheduler V293_witness_li V293_shared_inv
 (CallInternalPost present cs saved) Afalse (CallInternalPre present cs saved)
 (V293_TCBInit_function_body 501%Z 502%Z) Afalse SuccessTid.
Proof. apply CallCalleeContractChecked. Qed.
Theorem IdleHoareChecked : forall present cs,
 InfRules(CallSpec present cs)V293_scheduler V293_witness_li V293_shared_inv
 (IdlePost present cs) Afalse (IdlePre present cs) IdleBody Afalse SuccessTid.
Proof.
 intros present cs. unfold IdlePre,IdlePost,IdleBody,CallArgs.
 eapply V293_OSTaskCreateExt_success_call_suffix_hoare with
 (good:=SuccessRFun) (old:=fun _=>Vundef) (oldprev:=Vundef) (oldback:=Vundef)
 (slot:=Vundef) (table:=211%positive) (bg:=210%positive) (bt:=301%positive)
 (base:=128%Z) (p:=11) (top:=Vnull) (bottom:=Vnull) (identity:=Vint32 Int.zero)
 (size:=Vint32(Int.repr 128)) (ext:=Vnull) (options:=Vint32 Int.zero) (next:=SuccessNext)
 (bh:=212%positive) (bgrp:=213%positive) (br:=214%positive) (bn:=215%positive)
 (oldblock:=301%positive) (oldbase:=256%Z) (present:=present) (g:=1) (row:=129) (n:=254)
 (aop:=spec_done None) (isr:=fun _=>false) (is:=[]) (cs:=cs).
 - exact I.
 - lia.
 - repeat split;reflexivity.
 - apply SuccessRCurLINV.
 - apply CallLookup.
Qed.

Lemma IdleStar : forall m1 m2 m cs A B,
 join m1 m2 m -> IdleState m1 cs |= A -> IdleState m2 cs |= B ->
 IdleState m cs |= A ** B.
Proof.
 intros. apply sat_split'. exists m1. exists m2. exists(emp:osabst). exists(emp:osabst).
 split;[exact H| ]. split;[apply map_join_emp| ]. split;assumption.
Qed.
Lemma IdleLVar : forall b x tp v cs,
 get CallLE x=Some(b,tp) -> IdleState(CallByte b tp v)cs |= LV x @ tp |->v.
Proof.
 intros b x tp v cs Env. exists b.
 eapply IdleStar with(m1:=emp)(m2:=CallByte b tp v).
 - apply map_join_comm;apply map_join_emp.
 - exists b. split;[exact Env| ]. repeat split;reflexivity.
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Ltac IdleLocalTactic :=
 lazymatch goal with
 | |- IdleState(merge(CallByte ?b ?tp ?v)?tail)?cs |= LV ?x @ ?tp |-> ?v ** _ =>
   eapply IdleStar with(m1:=CallByte b tp v)(m2:=tail);
   [CallLocalApart b|apply IdleLVar;vm_compute;reflexivity|IdleLocalTactic]
 | |- IdleState(CallByte 709%positive Tint8(Vint32(Int.repr 77)))?cs |= _ =>
   split;[apply V293_encoded_memory_mapsto|reflexivity]
 end.
Theorem IdleLocalsSpatial : forall top bottom result cs,
 IdleState(CallLocals top bottom result)cs |= LV 209%Z @ Tint8 |->result ** CallArgs top bottom.
Proof.
 intros. unfold CallLocals,CallArgs,V293_create_tcb_arguments,CallFrame. IdleLocalTactic.
Qed.

Lemma IdleCurrentSpatial : forall cs, IdleState SuccessCurrent cs |= CurTid SuccessTid.
Proof.
 intro cs. exists Tvoid. exists 402%positive.
 eapply IdleStar with (m1:=emp) (m2:=SuccessCurrent).
 - apply map_join_comm;apply map_join_emp.
 - exists 402%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Lemma IdleLInvSpatial : forall cs, IdleState emp cs |= LINV V293_witness_li SuccessTid [].
Proof.
 intro cs. unfold LINV. apply astar_comm. apply astar_l_apure_intro.
 - split;reflexivity.
 - apply V293_witness_li_good.
Qed.
Lemma IdleRSpatial : forall cs,
 IdleState (merge SuccessCurrent SuccessSentinel) cs |= SuccessR.
Proof.
 intro cs. unfold SuccessR.
 eapply IdleStar with (m1:=SuccessCurrent) (m2:=SuccessSentinel).
 - SuccessFrameApart 402%positive.
 - apply IdleCurrentSpatial.
 - eapply IdleStar with (m1:=emp) (m2:=SuccessSentinel).
   + apply map_join_comm;apply map_join_emp.
   + apply IdleLInvSpatial.
   + split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.

Ltac IdleRawTactic :=
 lazymatch goal with
 | |- IdleState(merge(V293_encoded_memory ?b ?off true(encode_val ?tp ?v))?tail)?cs |= _ =>
   let bytes:=eval cbv in(Z.of_nat(typelen tp))in
   eapply IdleStar with(m1:=V293_encoded_memory b off true(encode_val tp v));
   [SuccessApart b off bytes|split;[apply V293_encoded_memory_mapsto|reflexivity]|IdleRawTactic]
 | |- IdleState emp _ |= Aemp => split;reflexivity
 end.
Lemma IdleRawExternal : forall present cs,
 IdleState(SuccessMemory(SuccessExternalCells present))cs |=
 V293_rdy_raw_cells(SuccessExternalCells present)Aemp.
Proof.
 intros. destruct present;unfold SuccessExternalCells,V293_tcb_success_pre_owned,
 V293_tcb_init_old_fields,V293_tcb_prefix_links,V293_link_extra;
 cbn[app tl SuccessMemory V293_rdy_raw_cells];IdleRawTactic.
Qed.
Lemma IdleGlobals : forall cs, IdleState emp cs |= SuccessGlobals.
Proof.
 intro cs. unfold SuccessGlobals,V293_tcb_success_global_bindings.
 repeat(eapply IdleStar with(m1:=emp)(m2:=emp);
 [apply map_join_emp|eexists;split;[vm_compute;reflexivity|repeat split;reflexivity]| ]).
 split;reflexivity.
Qed.
Lemma IdleReadySpatial : forall present cs,
 IdleState(CallReadyMemory present)cs |=
 V293_tcb_success_external 211%positive 210%positive 212%positive 213%positive 214%positive 215%positive
 (SuccessExternalCells present)SuccessR(spec_done None)(fun _=>false)[]cs.
Proof.
 intros. unfold V293_tcb_success_external,V293_hook_resource.
 apply astar_l_aop'_intro;[ |reflexivity]. apply V293_raw_cells_join.
 unfold CallReadyMemory. eapply IdleStar with(m1:=SuccessMemory(SuccessExternalCells present))
 (m2:=merge SuccessCurrent SuccessSentinel).
 - apply map_join_merge;apply map_disjoint;intros[b off].
   destruct(Pos.eq_dec b 402%positive);[subst b;left| ].
   + destruct present;unfold SuccessExternalCells,V293_tcb_success_pre_owned,
     V293_tcb_init_old_fields,V293_tcb_prefix_links,V293_link_extra;
     cbn[app tl SuccessMemory];SuccessOutside.
   + destruct(Pos.eq_dec b 601%positive);[subst b;left|right;left].
     * destruct present;unfold SuccessExternalCells,V293_tcb_success_pre_owned,
       V293_tcb_init_old_fields,V293_tcb_prefix_links,V293_link_extra;
       cbn[app tl SuccessMemory];SuccessOutside.
     * unfold SuccessCurrent,SuccessSentinel,SuccessBytes. rewrite map_merge_semp by reflexivity.
       rewrite !V293_encoded_memory_outside by(left;congruence). reflexivity.
 - apply IdleRawExternal.
 - assert(K:IdleState(merge SuccessCurrent SuccessSentinel)cs |=
     Aisr(fun _=>false) ** Aie false ** (Ais nil) ** Acs cs ** (SuccessGlobals ** SuccessR)).
   { apply astar_l_aisr_intro;[ |reflexivity].
     apply astar_l_aie_intro;[ |reflexivity].
     apply astar_l_ais_intro;[ |reflexivity]. apply astar_l_acs_intro;[ |reflexivity].
     eapply IdleStar with(m1:=emp)(m2:=merge SuccessCurrent SuccessSentinel).
     - apply map_join_comm;apply map_join_emp.
     - apply IdleGlobals.
     - apply IdleRSpatial. }
   unfold SuccessGlobals in K. clear -K. sep auto.
Qed.

Theorem IdleOriginalReadyEntry : forall present cs,
 IdleState(merge(CallReadyMemory present)(CallLocals Vnull Vnull Vundef))cs |= CallPre present cs SuccessHead.
Proof.
 intros. unfold CallPre,CallFpre,SuccessInternalFpre.
 cbn[V293_tcb_snapshot_fpre V293_tcb_guard_fpre getasrt].
 eapply IdleStar with(m1:=CallReadyMemory present)(m2:=CallLocals Vnull Vnull Vundef).
 - apply(CallFreshApart present false).
 - apply astar_l_apure_intro;[ |reflexivity].
   cbn[V293_tcb_success_fpre getasrt]. apply astar_l_apure_intro;[apply IdleReadySpatial|reflexivity].
 - apply IdleLocalsSpatial.
Qed.


Lemma IdleRunningSpatial : forall cs, IdleState IdleByte cs |= V293_create_idle_running 98%Z 710%positive.
Proof.
 intro cs. unfold V293_create_idle_running,V293_create_global_binding.
 eapply IdleStar with(m1:=emp)(m2:=IdleByte).
 - apply map_join_comm;apply map_join_emp.
 - split.
   + exists 710%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
   + split;[intros[v H];vm_compute in H;discriminate H|repeat split;reflexivity].
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Lemma IdleFresh : forall present top bottom result,
 join(merge(CallReadyMemory present)(CallLocals top bottom result))IdleByte
 (merge(merge(CallReadyMemory present)(CallLocals top bottom result))IdleByte).
Proof.
 intros. apply map_join_merge;apply map_disjoint;intros[b off].
 destruct(Pos.eq_dec b 710%positive);[subst b;left|right;left].
 - destruct present;unfold CallReadyMemory,CallLocals,CallByte,SuccessExternalCells,
   V293_tcb_success_pre_owned,V293_tcb_init_old_fields,V293_tcb_prefix_links,V293_link_extra,
   SuccessCurrent,SuccessSentinel,SuccessBytes;cbn[app tl SuccessMemory];SuccessOutside.
 - unfold IdleByte. apply V293_encoded_memory_outside;left;congruence.
Qed.
Theorem IdleLiteralEntry : forall present cs,
 IdleState(merge(merge(CallReadyMemory present)(CallLocals Vnull Vnull Vundef))IdleByte)cs |= IdlePre present cs.
Proof.
 intros. assert(H:IdleState(merge(merge(CallReadyMemory present)(CallLocals Vnull Vnull Vundef))IdleByte)cs |=
 CallPre present cs SuccessHead ** V293_create_idle_running 98%Z 710%positive).
 { eapply IdleStar.
   - apply IdleFresh.
   - apply IdleOriginalReadyEntry.
   - apply IdleRunningSpatial. }
 unfold IdlePre,CallPre,CallArgs,V293_create_tcb_arguments in *. clear -H. sep auto.
Qed.
Theorem IdleEntrySatisfiable : forall present cs, exists s, s |= IdlePre present cs.
Proof. intros. eexists. apply IdleLiteralEntry. Qed.

Definition IdleFinalReadyMemory present := merge(SuccessMemory(SuccessFinalExternalCells present))
 (merge SuccessCurrent SuccessSentinel).
Lemma IdleFinalRawExternal : forall present cs,
 IdleState(SuccessMemory(SuccessFinalExternalCells present))cs |=
 V293_rdy_raw_cells(SuccessFinalExternalCells present)Aemp.
Proof.
 intros. destruct present;unfold SuccessFinalExternalCells,V293_tcb_success_post_owned,
 V293_pub_cells,V293_tcb_prefix_links,V293_link_extra;
 cbn[app tl SuccessMemory V293_rdy_raw_cells];IdleRawTactic.
Qed.
Lemma IdleFinalReadySpatial : forall present cs,
 IdleState(IdleFinalReadyMemory present)cs |=
 V293_tcb_success_external 211%positive 210%positive 212%positive 213%positive 214%positive 215%positive
 (SuccessFinalExternalCells present)SuccessR(spec_done None)(fun _=>false)[]cs.
Proof.
 intros. unfold V293_tcb_success_external,V293_hook_resource.
 apply astar_l_aop'_intro;[ |reflexivity]. apply V293_raw_cells_join.
 unfold IdleFinalReadyMemory. eapply IdleStar with(m1:=SuccessMemory(SuccessFinalExternalCells present))
 (m2:=merge SuccessCurrent SuccessSentinel).
 - apply map_join_merge;apply map_disjoint;intros[b off].
   destruct(Pos.eq_dec b 402%positive);[subst b;left| ].
   + destruct present;unfold SuccessFinalExternalCells,V293_tcb_success_post_owned,
     V293_pub_cells,V293_tcb_prefix_links,V293_link_extra;
     cbn[app tl SuccessMemory];SuccessOutside.
   + destruct(Pos.eq_dec b 601%positive);[subst b;left|right;left].
     * destruct present;unfold SuccessFinalExternalCells,V293_tcb_success_post_owned,
       V293_pub_cells,V293_tcb_prefix_links,V293_link_extra;
       cbn[app tl SuccessMemory];SuccessOutside.
     * unfold SuccessCurrent,SuccessSentinel,SuccessBytes. rewrite map_merge_semp by reflexivity.
       rewrite !V293_encoded_memory_outside by(left;congruence). reflexivity.
 - apply IdleFinalRawExternal.
 - assert(K:IdleState(merge SuccessCurrent SuccessSentinel)cs |=
     Aisr(fun _=>false) ** Aie false ** (Ais nil) ** Acs cs ** (SuccessGlobals ** SuccessR)).
   { apply astar_l_aisr_intro;[ |reflexivity].
     apply astar_l_aie_intro;[ |reflexivity].
     apply astar_l_ais_intro;[ |reflexivity]. apply astar_l_acs_intro;[ |reflexivity].
     eapply IdleStar with(m1:=emp)(m2:=merge SuccessCurrent SuccessSentinel).
     - apply map_join_comm;apply map_join_emp.
     - apply IdleGlobals.
     - apply IdleRSpatial. }
   unfold SuccessGlobals in K. clear -K. sep auto.
Qed.

Lemma IdleFinalLocalsApart : forall present top bottom result,
 join (IdleFinalReadyMemory present)
 (CallLocals top bottom result)
 (merge(IdleFinalReadyMemory present)(CallLocals top bottom result)).
Proof.
 intros. apply map_join_merge;apply map_disjoint;intros[b off].
 destruct(Pos.eq_dec b 701%positive) as [Equal|Different701].
 { subst b;left. destruct present;unfold IdleFinalReadyMemory,SuccessFinalExternalCells,
   V293_tcb_success_post_owned,V293_pub_cells,V293_tcb_prefix_links,V293_link_extra,
   SuccessCurrent,SuccessSentinel,SuccessBytes;cbn[app tl SuccessMemory];SuccessOutside. }
 destruct(Pos.eq_dec b 702%positive) as [Equal|Different702].
 { subst b;left. destruct present;unfold IdleFinalReadyMemory,SuccessFinalExternalCells,
   V293_tcb_success_post_owned,V293_pub_cells,V293_tcb_prefix_links,V293_link_extra,
   SuccessCurrent,SuccessSentinel,SuccessBytes;cbn[app tl SuccessMemory];SuccessOutside. }
 destruct(Pos.eq_dec b 703%positive) as [Equal|Different703].
 { subst b;left. destruct present;unfold IdleFinalReadyMemory,SuccessFinalExternalCells,
   V293_tcb_success_post_owned,V293_pub_cells,V293_tcb_prefix_links,V293_link_extra,
   SuccessCurrent,SuccessSentinel,SuccessBytes;cbn[app tl SuccessMemory];SuccessOutside. }
 destruct(Pos.eq_dec b 704%positive) as [Equal|Different704].
 { subst b;left. destruct present;unfold IdleFinalReadyMemory,SuccessFinalExternalCells,
   V293_tcb_success_post_owned,V293_pub_cells,V293_tcb_prefix_links,V293_link_extra,
   SuccessCurrent,SuccessSentinel,SuccessBytes;cbn[app tl SuccessMemory];SuccessOutside. }
 destruct(Pos.eq_dec b 705%positive) as [Equal|Different705].
 { subst b;left. destruct present;unfold IdleFinalReadyMemory,SuccessFinalExternalCells,
   V293_tcb_success_post_owned,V293_pub_cells,V293_tcb_prefix_links,V293_link_extra,
   SuccessCurrent,SuccessSentinel,SuccessBytes;cbn[app tl SuccessMemory];SuccessOutside. }
 destruct(Pos.eq_dec b 706%positive) as [Equal|Different706].
 { subst b;left. destruct present;unfold IdleFinalReadyMemory,SuccessFinalExternalCells,
   V293_tcb_success_post_owned,V293_pub_cells,V293_tcb_prefix_links,V293_link_extra,
   SuccessCurrent,SuccessSentinel,SuccessBytes;cbn[app tl SuccessMemory];SuccessOutside. }
 destruct(Pos.eq_dec b 707%positive) as [Equal|Different707].
 { subst b;left. destruct present;unfold IdleFinalReadyMemory,SuccessFinalExternalCells,
   V293_tcb_success_post_owned,V293_pub_cells,V293_tcb_prefix_links,V293_link_extra,
   SuccessCurrent,SuccessSentinel,SuccessBytes;cbn[app tl SuccessMemory];SuccessOutside. }
 destruct(Pos.eq_dec b 708%positive) as [Equal|Different708].
 { subst b;left. destruct present;unfold IdleFinalReadyMemory,SuccessFinalExternalCells,
   V293_tcb_success_post_owned,V293_pub_cells,V293_tcb_prefix_links,V293_link_extra,
   SuccessCurrent,SuccessSentinel,SuccessBytes;cbn[app tl SuccessMemory];SuccessOutside. }
 destruct(Pos.eq_dec b 709%positive) as [Equal|Different709].
 { subst b;left. destruct present;unfold IdleFinalReadyMemory,SuccessFinalExternalCells,
   V293_tcb_success_post_owned,V293_pub_cells,V293_tcb_prefix_links,V293_link_extra,
   SuccessCurrent,SuccessSentinel,SuccessBytes;cbn[app tl SuccessMemory];SuccessOutside. }
 right;left. unfold CallLocals,CallByte. SuccessOutside.
Qed.
Lemma IdleFinalFresh : forall present top bottom result,
 join(merge(IdleFinalReadyMemory present)(CallLocals top bottom result))IdleByte
 (merge(merge(IdleFinalReadyMemory present)(CallLocals top bottom result))IdleByte).
Proof.
 intros. apply map_join_merge;apply map_disjoint;intros[b off].
 destruct(Pos.eq_dec b 710%positive);[subst b;left|right;left].
 - destruct present;unfold IdleFinalReadyMemory,CallLocals,CallByte,SuccessFinalExternalCells,
   V293_tcb_success_post_owned,V293_pub_cells,V293_tcb_prefix_links,V293_link_extra,
   SuccessCurrent,SuccessSentinel,SuccessBytes;cbn[app tl SuccessMemory];SuccessOutside.
 - unfold IdleByte. apply V293_encoded_memory_outside;left;congruence.
Qed.

Theorem IdleLiteralPost : forall present cs,
 IdleState(merge(merge(IdleFinalReadyMemory present)(CallLocals Vnull Vnull(Vint32 Int.zero)))IdleByte)cs |=
 IdlePost present cs(Some(Vint32 Int.zero)).
Proof.
 intros. assert(External:IdleState(IdleFinalReadyMemory present)cs |=
 getasrt(CallFpost present cs SuccessArguments(Some(Vint32 Int.zero))[logic_val SuccessHead]SuccessTid)).
 { unfold CallFpost,SuccessInternalFpost. cbn[V293_tcb_snapshot_fpost V293_tcb_guard_fpost getasrt].
   apply astar_l_apure_intro;[ |reflexivity].
   cbn[V293_tcb_success_fpost getasrt]. apply astar_l_apure_intro;[apply IdleFinalReadySpatial|reflexivity]. }
 assert(H:IdleState(merge(merge(IdleFinalReadyMemory present)(CallLocals Vnull Vnull(Vint32 Int.zero)))IdleByte)cs |=
 (getasrt(CallFpost present cs SuccessArguments(Some(Vint32 Int.zero))[logic_val SuccessHead]SuccessTid) **
  LV 209%Z @ Tint8 |->Vint32 Int.zero ** CallArgs Vnull Vnull) ** V293_create_idle_running 98%Z 710%positive).
 { eapply IdleStar.
   - apply IdleFinalFresh.
   - eapply IdleStar.
     + apply IdleFinalLocalsApart.
     + exact External.
     + apply IdleLocalsSpatial.
   - apply IdleRunningSpatial. }
 unfold IdlePost,V293_create_success_return,V293_create_success_state.
 apply astar_l_apure_intro;[clear -H;sep auto|reflexivity].
Qed.
Theorem IdlePostSatisfiable : forall present cs, exists s, s |= IdlePost present cs(Some(Vint32 Int.zero)).
Proof. intros. eexists. apply IdleLiteralPost. Qed.
Theorem IdlePostExternalLoad : forall present cs s a tp v,
 s |= IdlePost present cs(Some(Vint32 Int.zero)) -> In(a,tp,v)(SuccessFinalExternalCells present) ->
 rule_type_val_match tp v=true -> load tp(getmem s)a=Some v.
Proof.
 intros present cs s a tp v H Member Valid.
 unfold IdlePost,V293_create_success_return in H.
 apply astar_l_apure_elim in H. destruct H as[_ H].
 unfold V293_create_success_state in H.
 eapply V293_star_load_r;[ |exact H]. intros st H1.
 eapply V293_star_load_r;[ |exact H1]. intros st1 H2.
 eapply V293_star_load_l;[ |exact H2]. intros st2 H3.
 unfold CallFpost,SuccessInternalFpost in H3.
 cbn[V293_tcb_snapshot_fpost V293_tcb_guard_fpost V293_tcb_success_fpost getasrt]in H3.
 eapply V293_star_load_r;[ |exact H3]. intros st3 H4.
 eapply V293_star_load_r;[ |exact H4]. intros st4 H5.
 unfold V293_tcb_success_external,V293_hook_resource in H5.
 eapply V293_star_load_r;[ |exact H5]. intros st5 H6.
 eapply V293_rdy_raw_load;[exact Member|exact Valid|exact H6].
Qed.
Lemma IdleLiteralExternalLoad : forall present a tp v,
 In(a,tp,v)(SuccessFinalExternalCells present) -> rule_type_val_match tp v=true ->
 load tp(merge(merge(IdleFinalReadyMemory present)(CallLocals Vnull Vnull(Vint32 Int.zero)))IdleByte)a=Some v.
Proof.
 intros. eapply IdlePostExternalLoad with(cs:=nil)
 (s:=IdleState(merge(merge(IdleFinalReadyMemory present)(CallLocals Vnull Vnull(Vint32 Int.zero)))IdleByte)nil).
 - apply IdleLiteralPost.
 - exact H.
 - exact H0.
Qed.
Theorem IdleLiteralPhysicalPost : forall present,
 let M:=merge(merge(IdleFinalReadyMemory present)(CallLocals Vnull Vnull(Vint32 Int.zero)))IdleByte in
 load(Tptr V293_tcb_type)M(210%positive,0%Z)=Some SuccessNext /\
 load(Tptr V293_tcb_type)M(211%positive,44%Z)=Some SuccessHead /\
 load Tint8 M(213%positive,0%Z)=Some(V293_byteval 3) /\
 load Tint8 M(214%positive,1%Z)=Some(V293_byteval 137) /\
 load Tint8 M(215%positive,0%Z)=Some(V293_byteval 255) /\
 load Tint8 M(708%positive,0%Z)=Some(Vint32 Int.zero) /\
 load Tint8 M(710%positive,0%Z)=Some(Vint32 Int.zero) /\
 load Tint8 M(709%positive,0%Z)=Some(Vint32(Int.repr 77)).
Proof.
 intro present. cbn zeta.
 pose proof(IdleLiteralPost present nil)as H.
 repeat split.
 all: try solve [eapply IdleLiteralExternalLoad;
  [destruct present;unfold SuccessFinalExternalCells,V293_tcb_success_post_owned,V293_pub_cells;
  cbn[app tl];simpl;tauto|reflexivity]].
 - assert(Read:IdleState(merge(merge(IdleFinalReadyMemory present)(CallLocals Vnull Vnull(Vint32 Int.zero)))IdleByte)nil |=
 Rv(evar 209%Z) @ Tint8==Vint32 Int.zero).
   { eapply V293_create_success_err_read. unfold IdlePost,V293_create_success_return in H.
     apply astar_l_apure_elim in H;exact(proj2 H). }
   change(load Tint8(merge(merge(IdleFinalReadyMemory present)(CallLocals Vnull Vnull(Vint32 Int.zero)))IdleByte)
    (708%positive,0%Z)=Some(Vint32 Int.zero) /\ Some Tint8=Some Tint8 /\ Vint32 Int.zero<>Vundef)in Read.
   exact(proj1 Read).
 - change(load Tint8(getmem(IdleState(merge(merge(IdleFinalReadyMemory present)(CallLocals Vnull Vnull(Vint32 Int.zero)))IdleByte)nil))
   (710%positive,0%Z)=Some(Vint32 Int.zero)).
   assert(Running:IdleState(merge(merge(IdleFinalReadyMemory present)(CallLocals Vnull Vnull(Vint32 Int.zero)))IdleByte)nil |=
   Amapsto(710%positive,0%Z)Tint8 false(Vint32 Int.zero) ** Atrue).
   { unfold IdlePost,V293_create_success_return,V293_create_success_state,V293_create_idle_running in H. clear -H;sep auto. }
   eapply V293_star_load_l;[ |exact Running]. intros st Owned.
   eapply V293_mapsto_load with(n:=0);[lia|exact Owned].
 - change(load Tint8(getmem(IdleState(merge(merge(IdleFinalReadyMemory present)(CallLocals Vnull Vnull(Vint32 Int.zero)))IdleByte)nil))
   (709%positive,0%Z)=Some(Vint32(Int.repr 77))).
   assert(Frame:IdleState(merge(merge(IdleFinalReadyMemory present)(CallLocals Vnull Vnull(Vint32 Int.zero)))IdleByte)nil |=
   CallFrame ** Atrue).
   { unfold IdlePost,V293_create_success_return,V293_create_success_state,CallArgs,V293_create_tcb_arguments in H. clear -H;sep auto. }
   eapply V293_star_load_l;[ |exact Frame]. intros st Owned.
   eapply V293_mapsto_load with(n:=77);[lia|exact Owned].
Qed.
