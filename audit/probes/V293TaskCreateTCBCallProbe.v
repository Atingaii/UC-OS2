(* Composition tests intentionally reuse frozen Stage93 byte fixtures. *)
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

Definition CallFpre present cs := V293_tcb_snapshot_fpre SuccessHead
 (V293_tcb_empty_fpre 210%positive SuccessR(spec_done None)(fun _=>false)[]cs SuccessRFun)
 (SuccessInternalFpre present cs).
Definition CallFpost present cs := V293_tcb_snapshot_fpost SuccessHead
 (V293_tcb_empty_fpost 210%positive SuccessR(spec_done None)(fun _=>false)[]cs SuccessRFun)
 (SuccessInternalFpost present cs).
Definition CallSpec present cs : funspec := fun f =>
 if Z.eq_dec f 900%Z then Some(CallFpre present cs,CallFpost present cs,(Tint8,rev V293_TCBInit_argument_types))
 else SuccessDeclaredSpec present cs f.
Definition CallInternalPre present cs saved :=
 V293_tcb_internal_pre_cells (V293_byteval 11) Vnull Vnull (Vint32 Int.zero)
 (Vint32(Int.repr 128)) Vnull (Vint32 Int.zero) **
 getasrt(CallFpre present cs SuccessArguments [logic_val saved] SuccessTid) ** V293_tcb_internal_domain.
Definition CallInternalPost present cs saved : retasrt := fun result=>
 V293_tcb_internal_post_cells **
 getasrt(CallFpost present cs SuccessArguments result [logic_val saved] SuccessTid) ** V293_tcb_internal_domain.
Theorem CallLookup : forall present cs,
 CallSpec present cs 900%Z=Some(CallFpre present cs,CallFpost present cs,(Tint8,rev V293_TCBInit_argument_types)).
Proof. intros. unfold CallSpec. destruct(Z.eq_dec 900%Z 900%Z);[reflexivity|contradiction]. Qed.
Theorem CallCalleeContractChecked : forall present cs saved,
 InfRules(CallSpec present cs)V293_scheduler V293_witness_li V293_shared_inv
 (CallInternalPost present cs saved) Afalse (CallInternalPre present cs saved)
 (V293_TCBInit_function_body 501%Z 502%Z) Afalse SuccessTid.
Proof.
 intros present cs saved.
 eapply V293_OS_TCBInit_snapshot_internal_contract
 with (P:=SuccessProgram) (f:=900%Z) (vl:=rev SuccessArguments) (lg:=[logic_val saved])
 (Hfun:=SuccessRFun) (old:=fun _=>Vundef) (oldprev:=Vundef) (oldback:=Vundef)
 (slot:=Vundef) (table:=211%positive) (bg:=210%positive) (bt:=301%positive)
 (base:=128%Z) (p:=11) (top:=Vnull) (bottom:=Vnull) (identity:=Vint32 Int.zero)
 (size:=Vint32(Int.repr 128)) (ext:=Vnull) (options:=Vint32 Int.zero) (next:=SuccessNext)
 (bh:=212%positive) (bgrp:=213%positive) (br:=214%positive) (bn:=215%positive)
 (oldblock:=301%positive) (oldbase:=256%Z) (present:=present) (g:=1) (row:=129) (n:=254)
 (aop:=spec_done None) (isr:=fun _=>false) (is:=[]) (cs:=cs).
 - apply SuccessGoodIInhabited.
 - lia.
 - lia.
 - unfold Int.max_unsigned,Int.modulus,Int.wordsize;cbn;lia.
 - lia.
 - unfold Int.max_unsigned,Int.modulus,Int.wordsize;cbn;lia.
 - repeat split;reflexivity.
 - reflexivity.
 - lia.
 - lia.
 - lia.
 - apply SuccessRGood.
 - apply SuccessRCurLINV.
 - unfold CallSpec. destruct(Z.eq_dec 501%Z 900%Z);[discriminate|apply SuccessInitLookup].
 - unfold CallSpec. destruct(Z.eq_dec 502%Z 900%Z);[discriminate|apply SuccessCreateLookup].
 - reflexivity.
 - reflexivity.
 - reflexivity.
Qed.

(* Eight NEW caller variables and a separate writable caller sentinel.
   Existing callee external bytes/GE/R are explicitly reused, not retranslated. *)
Definition CallLE : env :=
 set (set (set (set (set (set (set (sig 101%Z (701%positive,Tint8))
 108%Z (702%positive,Tptr Tint32)) 205%Z (703%positive,Tptr Tint32))
 206%Z (704%positive,Tint16)) 207%Z (705%positive,Tint32))
 208%Z (706%positive,Tptr Tvoid)) 204%Z (707%positive,Tint16)) 209%Z (708%positive,Tint8).
Definition CallState M cs : RstateOP :=
 (SuccessGE,CallLE,M,(fun _=>false),(false,[],cs),(emp:osabst),spec_done None).
Definition CallByte b tp v := V293_encoded_memory b 0 true(encode_val tp v).
Definition CallFrame := Amapsto(709%positive,0%Z)Tint8 true(Vint32(Int.repr 77)).
Definition CallLocals top bottom result :=
 merge(CallByte 708%positive Tint8 result)
 (merge(CallByte 701%positive Tint8(V293_byteval 11))
 (merge(CallByte 702%positive(Tptr Tint32)top)
 (merge(CallByte 703%positive(Tptr Tint32)bottom)
 (merge(CallByte 704%positive Tint16(Vint32 Int.zero))
 (merge(CallByte 705%positive Tint32(Vint32(Int.repr 128)))
 (merge(CallByte 706%positive(Tptr Tvoid)Vnull)
 (merge(CallByte 707%positive Tint16(Vint32 Int.zero))
 (CallByte 709%positive Tint8(Vint32(Int.repr 77)))))))))).
Definition CallArgs top bottom := V293_create_tcb_arguments 11 top bottom (Vint32 Int.zero)
 (Vint32(Int.repr 128))Vnull(Vint32 Int.zero)CallFrame.
Definition CallPre present cs saved :=
 getasrt(CallFpre present cs SuccessArguments[logic_val saved]SuccessTid) **
 LV 209%Z @ Tint8 |-> Vundef ** CallArgs Vnull Vnull.
Definition CallPost present cs saved := EX result:val,
 [|(saved=Vnull /\ result=Vint32(Int.repr 66)) \/ (saved=SuccessHead /\ result=Vint32 Int.zero)|] **
 (getasrt(CallFpost present cs SuccessArguments(Some result)[logic_val saved]SuccessTid) **
 LV 209%Z @ Tint8 |-> result ** CallArgs Vnull Vnull).
Theorem CallHoareChecked : forall present cs saved,
 InfRules(CallSpec present cs)V293_scheduler V293_witness_li V293_shared_inv
 (fun _=>Afalse) Afalse (CallPre present cs saved)
 (V293_TaskCreateExt_TCB_call 209%Z 900%Z 101%Z 108%Z 205%Z 206%Z 207%Z 208%Z 204%Z)
 (CallPost present cs saved)SuccessTid.
Proof.
 intros present cs saved. unfold CallPre,CallPost,CallArgs.
 eapply V293_TaskCreateExt_TCB_snapshot_call with
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
Lemma CallStar : forall m1 m2 m cs A B,
 join m1 m2 m -> CallState m1 cs |= A -> CallState m2 cs |= B ->
 CallState m cs |= A ** B.
Proof.
 intros. apply sat_split'. exists m1. exists m2. exists(emp:osabst). exists(emp:osabst).
 split;[exact H| ]. split;[apply map_join_emp| ]. split;assumption.
Qed.
Lemma CallLVar : forall b x tp v cs,
 get CallLE x=Some(b,tp) -> CallState(CallByte b tp v)cs |= LV x @ tp |->v.
Proof.
 intros b x tp v cs Env. exists b.
 eapply CallStar with(m1:=emp)(m2:=CallByte b tp v).
 - apply map_join_comm;apply map_join_emp.
 - exists b. split;[exact Env| ]. repeat split;reflexivity.
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Ltac CallLocalApart b :=
 apply map_join_merge;apply map_disjoint;intros[other off];
 destruct(Pos.eq_dec other b);[subst other;right;left|left];
 unfold CallByte;
 repeat first[rewrite map_merge_semp by reflexivity|
 rewrite V293_encoded_memory_outside by(left;congruence)];reflexivity.
Ltac CallLocalTactic :=
 lazymatch goal with
 | |- CallState(merge(CallByte ?b ?tp ?v)?tail)?cs |= LV ?x @ ?tp |-> ?v ** _ =>
   eapply CallStar with(m1:=CallByte b tp v)(m2:=tail);
   [CallLocalApart b|apply CallLVar;vm_compute;reflexivity|CallLocalTactic]
 | |- CallState(CallByte 709%positive Tint8(Vint32(Int.repr 77)))?cs |= _ =>
   split;[apply V293_encoded_memory_mapsto|reflexivity]
 end.
Theorem CallLocalsSpatial : forall top bottom result cs,
 CallState(CallLocals top bottom result)cs |= LV 209%Z @ Tint8 |->result ** CallArgs top bottom.
Proof.
 intros. unfold CallLocals,CallArgs,V293_create_tcb_arguments,CallFrame. CallLocalTactic.
Qed.
Theorem CallDistinctArgumentsRead : forall cs,
 CallState(CallLocals(Vptr(801%positive,Int.zero))(Vptr(802%positive,Int.zero))Vundef)cs |=
 Rvl[evar 101%Z;evar 108%Z;evar 205%Z;evar 206%Z;evar 207%Z;evar 208%Z;evar 204%Z]
 @(rev V293_TCBInit_argument_types)==
 V293_tcb_success_arguments 11(Vptr(801%positive,Int.zero))(Vptr(802%positive,Int.zero))
 (Vint32 Int.zero)(Vint32(Int.repr 128))Vnull(Vint32 Int.zero).
Proof.
 intro cs. eapply V293_create_tcb_arguments_read with(F:=LV 209%Z @ Tint8 |->Vundef ** CallFrame).
 - lia.
 - repeat split;reflexivity.
 - pose proof(CallLocalsSpatial(Vptr(801%positive,Int.zero))(Vptr(802%positive,Int.zero))Vundef cs)as H.
   unfold CallArgs,V293_create_tcb_arguments in *. clear -H. sep auto.
Qed.

Theorem CallSwappedArgumentsRead : forall cs,
 CallState(CallLocals(Vptr(801%positive,Int.zero))(Vptr(802%positive,Int.zero))Vundef)cs |=
 Rvl[evar 101%Z;evar 205%Z;evar 108%Z;evar 206%Z;evar 207%Z;evar 208%Z;evar 204%Z]
 @(rev V293_TCBInit_argument_types)==
 V293_tcb_success_arguments 11(Vptr(802%positive,Int.zero))(Vptr(801%positive,Int.zero))
 (Vint32 Int.zero)(Vint32(Int.repr 128))Vnull(Vint32 Int.zero).
Proof.
 intro cs. pose proof(CallDistinctArgumentsRead cs)as Read.
 cbn[sat evalexprlist V293_TCBInit_argument_types rev app V293_tcb_success_arguments]in *.
 tauto.
Qed.
Theorem CallSwappedOrderRejected : forall cs,
 ~ (CallState(CallLocals(Vptr(801%positive,Int.zero))(Vptr(802%positive,Int.zero))Vundef)cs |=
 Rvl[evar 101%Z;evar 205%Z;evar 108%Z;evar 206%Z;evar 207%Z;evar 208%Z;evar 204%Z]
 @(rev V293_TCBInit_argument_types)==
 V293_tcb_success_arguments 11(Vptr(801%positive,Int.zero))(Vptr(802%positive,Int.zero))
 (Vint32 Int.zero)(Vint32(Int.repr 128))Vnull(Vint32 Int.zero)).
Proof.
 intros cs Bad. pose proof(CallDistinctArgumentsRead cs)as Read.
 cbn[sat evalexprlist V293_TCBInit_argument_types rev app V293_tcb_success_arguments]in *.
 intuition congruence.
Qed.

Lemma CallRSpatial : forall cs,
 CallState(merge SuccessCurrent SuccessSentinel)cs |= SuccessR.
Proof.
 intro cs. eapply good_fun_asrt_absop;[exact SuccessRFun|apply SuccessRSpatial].
Qed.
Definition CallEmptyMemory := merge(SuccessBytes 210%positive false(Tptr V293_tcb_type)Vnull)
 (merge SuccessCurrent SuccessSentinel).
Lemma CallEmptySpatial : forall cs,
 CallState CallEmptyMemory cs |= V293_tcb_empty_external 210%positive SuccessR
 (spec_done None)(fun _=>false)[]cs.
Proof.
 intro cs. unfold V293_tcb_empty_external.
 eapply CallStar with(m1:=emp)(m2:=CallEmptyMemory).
 - apply map_join_comm;apply map_join_emp.
 - exists 210%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
 - unfold CallEmptyMemory. eapply CallStar with(m1:=SuccessBytes 210%positive false(Tptr V293_tcb_type)Vnull).
   + unfold SuccessCurrent,SuccessSentinel,SuccessBytes. CallLocalApart 210%positive.
   + split;[apply V293_encoded_memory_mapsto|reflexivity].
   + apply astar_l_aop'_intro;[ |reflexivity].
     assert(K:CallState(merge SuccessCurrent SuccessSentinel)cs |=
      Aisr(fun _=>false) ** Aie false ** (Ais nil) ** Acs cs ** SuccessR).
     { apply astar_l_aisr_intro;[ |reflexivity].
       apply astar_l_aie_intro;[ |reflexivity].
       apply astar_l_ais_intro;[ |reflexivity].
       apply astar_l_acs_intro;[ |reflexivity]. apply CallRSpatial. }
     clear -K. sep auto.
Qed.
Definition CallReadyMemory present := merge(SuccessMemory(SuccessExternalCells present))
 (merge SuccessCurrent SuccessSentinel).
Ltac CallRawTactic :=
 lazymatch goal with
 | |- CallState(merge(V293_encoded_memory ?b ?off true(encode_val ?tp ?v))?tail)?cs |= _ =>
   let bytes:=eval cbv in(Z.of_nat(typelen tp))in
   eapply CallStar with(m1:=V293_encoded_memory b off true(encode_val tp v));
   [SuccessApart b off bytes|split;[apply V293_encoded_memory_mapsto|reflexivity]|CallRawTactic]
 | |- CallState emp _ |= Aemp => split;reflexivity
 end.
Lemma CallRawExternal : forall present cs,
 CallState(SuccessMemory(SuccessExternalCells present))cs |=
 V293_rdy_raw_cells(SuccessExternalCells present)Aemp.
Proof.
 intros. destruct present;unfold SuccessExternalCells,V293_tcb_success_pre_owned,
 V293_tcb_init_old_fields,V293_tcb_prefix_links,V293_link_extra;
 cbn[app tl SuccessMemory V293_rdy_raw_cells];CallRawTactic.
Qed.
Lemma CallGlobals : forall cs, CallState emp cs |= SuccessGlobals.
Proof.
 intro cs. unfold SuccessGlobals,V293_tcb_success_global_bindings.
 repeat(eapply CallStar with(m1:=emp)(m2:=emp);
 [apply map_join_emp|eexists;split;[vm_compute;reflexivity|repeat split;reflexivity]| ]).
 split;reflexivity.
Qed.
Lemma CallReadySpatial : forall present cs,
 CallState(CallReadyMemory present)cs |=
 V293_tcb_success_external 211%positive 210%positive 212%positive 213%positive 214%positive 215%positive
 (SuccessExternalCells present)SuccessR(spec_done None)(fun _=>false)[]cs.
Proof.
 intros. unfold V293_tcb_success_external,V293_hook_resource.
 apply astar_l_aop'_intro;[ |reflexivity]. apply V293_raw_cells_join.
 unfold CallReadyMemory. eapply CallStar with(m1:=SuccessMemory(SuccessExternalCells present))
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
 - apply CallRawExternal.
 - assert(K:CallState(merge SuccessCurrent SuccessSentinel)cs |=
     Aisr(fun _=>false) ** Aie false ** (Ais nil) ** Acs cs ** (SuccessGlobals ** SuccessR)).
   { apply astar_l_aisr_intro;[ |reflexivity].
     apply astar_l_aie_intro;[ |reflexivity].
     apply astar_l_ais_intro;[ |reflexivity]. apply astar_l_acs_intro;[ |reflexivity].
     eapply CallStar with(m1:=emp)(m2:=merge SuccessCurrent SuccessSentinel).
     - apply map_join_comm;apply map_join_emp.
     - apply CallGlobals.
     - apply CallRSpatial. }
   unfold SuccessGlobals in K. clear -K. sep auto.
Qed.
Lemma CallFreshApart : forall present (empty:bool) top bottom result,
 join (if empty then CallEmptyMemory else CallReadyMemory present)
 (CallLocals top bottom result)
 (merge(if empty then CallEmptyMemory else CallReadyMemory present)(CallLocals top bottom result)).
Proof.
 intros. apply map_join_merge;apply map_disjoint;intros[b off].
 destruct(Pos.eq_dec b 701%positive) as [Equal|Different701].
 { subst b;left. destruct empty,present;unfold CallEmptyMemory,CallReadyMemory,SuccessExternalCells,
   V293_tcb_success_pre_owned,V293_tcb_init_old_fields,V293_tcb_prefix_links,V293_link_extra,
   SuccessCurrent,SuccessSentinel,SuccessBytes;cbn[app tl SuccessMemory];SuccessOutside. }
 destruct(Pos.eq_dec b 702%positive) as [Equal|Different702].
 { subst b;left. destruct empty,present;unfold CallEmptyMemory,CallReadyMemory,SuccessExternalCells,
   V293_tcb_success_pre_owned,V293_tcb_init_old_fields,V293_tcb_prefix_links,V293_link_extra,
   SuccessCurrent,SuccessSentinel,SuccessBytes;cbn[app tl SuccessMemory];SuccessOutside. }
 destruct(Pos.eq_dec b 703%positive) as [Equal|Different703].
 { subst b;left. destruct empty,present;unfold CallEmptyMemory,CallReadyMemory,SuccessExternalCells,
   V293_tcb_success_pre_owned,V293_tcb_init_old_fields,V293_tcb_prefix_links,V293_link_extra,
   SuccessCurrent,SuccessSentinel,SuccessBytes;cbn[app tl SuccessMemory];SuccessOutside. }
 destruct(Pos.eq_dec b 704%positive) as [Equal|Different704].
 { subst b;left. destruct empty,present;unfold CallEmptyMemory,CallReadyMemory,SuccessExternalCells,
   V293_tcb_success_pre_owned,V293_tcb_init_old_fields,V293_tcb_prefix_links,V293_link_extra,
   SuccessCurrent,SuccessSentinel,SuccessBytes;cbn[app tl SuccessMemory];SuccessOutside. }
 destruct(Pos.eq_dec b 705%positive) as [Equal|Different705].
 { subst b;left. destruct empty,present;unfold CallEmptyMemory,CallReadyMemory,SuccessExternalCells,
   V293_tcb_success_pre_owned,V293_tcb_init_old_fields,V293_tcb_prefix_links,V293_link_extra,
   SuccessCurrent,SuccessSentinel,SuccessBytes;cbn[app tl SuccessMemory];SuccessOutside. }
 destruct(Pos.eq_dec b 706%positive) as [Equal|Different706].
 { subst b;left. destruct empty,present;unfold CallEmptyMemory,CallReadyMemory,SuccessExternalCells,
   V293_tcb_success_pre_owned,V293_tcb_init_old_fields,V293_tcb_prefix_links,V293_link_extra,
   SuccessCurrent,SuccessSentinel,SuccessBytes;cbn[app tl SuccessMemory];SuccessOutside. }
 destruct(Pos.eq_dec b 707%positive) as [Equal|Different707].
 { subst b;left. destruct empty,present;unfold CallEmptyMemory,CallReadyMemory,SuccessExternalCells,
   V293_tcb_success_pre_owned,V293_tcb_init_old_fields,V293_tcb_prefix_links,V293_link_extra,
   SuccessCurrent,SuccessSentinel,SuccessBytes;cbn[app tl SuccessMemory];SuccessOutside. }
 destruct(Pos.eq_dec b 708%positive) as [Equal|Different708].
 { subst b;left. destruct empty,present;unfold CallEmptyMemory,CallReadyMemory,SuccessExternalCells,
   V293_tcb_success_pre_owned,V293_tcb_init_old_fields,V293_tcb_prefix_links,V293_link_extra,
   SuccessCurrent,SuccessSentinel,SuccessBytes;cbn[app tl SuccessMemory];SuccessOutside. }
 destruct(Pos.eq_dec b 709%positive) as [Equal|Different709].
 { subst b;left. destruct empty,present;unfold CallEmptyMemory,CallReadyMemory,SuccessExternalCells,
   V293_tcb_success_pre_owned,V293_tcb_init_old_fields,V293_tcb_prefix_links,V293_link_extra,
   SuccessCurrent,SuccessSentinel,SuccessBytes;cbn[app tl SuccessMemory];SuccessOutside. }
 right;left. unfold CallLocals,CallByte. SuccessOutside.
Qed.
Theorem CallLiteralEmptyEntry : forall present cs,
 CallState(merge CallEmptyMemory(CallLocals Vnull Vnull Vundef))cs |= CallPre present cs Vnull.
Proof.
 intros. unfold CallPre. eapply CallStar with(m1:=CallEmptyMemory)(m2:=CallLocals Vnull Vnull Vundef).
 - apply(CallFreshApart present true).
 - apply CallEmptySpatial.
 - apply CallLocalsSpatial.
Qed.
Theorem CallLiteralReadyEntry : forall present cs,
 CallState(merge(CallReadyMemory present)(CallLocals Vnull Vnull Vundef))cs |= CallPre present cs SuccessHead.
Proof.
 intros. unfold CallPre,CallFpre,SuccessInternalFpre.
 cbn[V293_tcb_snapshot_fpre V293_tcb_guard_fpre getasrt].
 eapply CallStar with(m1:=CallReadyMemory present)(m2:=CallLocals Vnull Vnull Vundef).
 - apply(CallFreshApart present false).
 - apply astar_l_apure_intro;[ |reflexivity].
   cbn[V293_tcb_success_fpre getasrt]. apply astar_l_apure_intro;[apply CallReadySpatial|reflexivity].
 - apply CallLocalsSpatial.
Qed.
Theorem CallLiteralHeadRead : forall present cs saved M,
 CallState M cs |= CallPre present cs saved ->
 load(Tptr V293_tcb_type)M(210%positive,0%Z)=Some saved.
Proof.
 intros present cs saved M H. unfold CallPre in H.
 change(load(Tptr V293_tcb_type)(getmem(CallState M cs))(210%positive,0%Z)=Some saved).
 eapply V293_star_load_l;[ |exact H]. intros st Owned.
 eapply V293_tcb_snapshot_pre_load with(allocated:=SuccessHead)
 (empty:=V293_tcb_empty_fpre 210%positive SuccessR(spec_done None)(fun _=>false)[]cs SuccessRFun)
 (ready:=SuccessInternalFpre present cs)(vl:=SuccessArguments)(lg:=[logic_val saved])(tid:=SuccessTid).
 - intros args ghosts task state Entry. eapply V293_tcb_empty_pre_head with(good:=SuccessRFun)(vl:=args)(lg:=ghosts)(tid:=task);exact Entry.
 - intros args ghosts task state Entry. eapply V293_tcb_success_pre_head with(good:=SuccessRFun)(vl:=args)(lg:=ghosts)(tid:=task);exact Entry.
 - reflexivity.
 - exact Owned.
Qed.

Theorem CallLiteralEmptyPost : forall present cs,
 CallState(merge CallEmptyMemory(CallLocals Vnull Vnull(Vint32(Int.repr 66))))cs |=
 CallPost present cs Vnull.
Proof.
 intros. exists(Vint32(Int.repr 66)). apply astar_l_apure_intro;[ |left;auto].
 eapply CallStar with(m1:=CallEmptyMemory)(m2:=CallLocals Vnull Vnull(Vint32(Int.repr 66))).
 - apply(CallFreshApart present true).
 - cbn[CallFpost V293_tcb_snapshot_fpost V293_tcb_empty_fpost getasrt].
   apply astar_l_apure_intro;[apply CallEmptySpatial|reflexivity].
 - apply CallLocalsSpatial.
Qed.
Lemma CallPostCode : forall present cs saved M,
 CallState M cs |= CallPost present cs saved ->
 exists result,
 ((saved=Vnull /\ result=Vint32(Int.repr 66)) \/ (saved=SuccessHead /\ result=Vint32 Int.zero)) /\
 load Tint8 M(708%positive,0%Z)=Some result /\
 load Tint8 M(709%positive,0%Z)=Some(Vint32(Int.repr 77)).
Proof.
 intros present cs saved M[result H].
 apply astar_l_apure_elim in H. destruct H as[Code H]. exists result. split;[exact Code| ].
 assert(Typed:rule_type_val_match Tint8 result=true).
 { destruct Code as[[_ E]|[_ E]];subst result;reflexivity. }
 assert(Read:CallState M cs |= Rv(evar 209%Z) @ Tint8 ==result).
 { eapply CertiOS.tactics.hoareforward.symbolic_lemmas.lvar_rv with(perm:=true)
   (P:=getasrt(CallFpost present cs SuccessArguments(Some result)[logic_val saved]SuccessTid) ** CallArgs Vnull Vnull).
   - clear -H. sep auto.
   - exact Typed. }
 change(load Tint8 M(708%positive,0%Z)=Some result /\
        Some Tint8=Some Tint8 /\ result<>Vundef)in Read.
 split;[exact(proj1 Read)| ].
 change(load Tint8(getmem(CallState M cs))(709%positive,0%Z)=Some(Vint32(Int.repr 77))).
 unfold CallArgs,V293_create_tcb_arguments in H.
 eapply V293_star_load_r;[ |exact H]. intros first H1.
 eapply V293_star_load_r;[ |exact H1]. intros second H2.
 do 7(eapply V293_star_load_r;[ |exact H2];clear H2;let st:=fresh "part" in intros st H3;rename H3 into H2).
 eapply V293_mapsto_load with(n:=77);[lia|exact H2].
Qed.
Theorem CallNullWrongErrRejected : forall present cs M,
 CallState M cs |= CallPost present cs Vnull ->
 load Tint8 M(708%positive,0%Z)<>Some(Vint32 Int.zero).
Proof.
 intros present cs M H. destruct(CallPostCode present cs Vnull M H)as[result[Code[Read _]]].
 destruct Code as[[_ E]|[E _]];[subst result;rewrite Read;discriminate|discriminate].
Qed.
Theorem CallReadyWrongErrRejected : forall present cs M,
 CallState M cs |= CallPost present cs SuccessHead ->
 load Tint8 M(708%positive,0%Z)<>Some(Vint32(Int.repr 66)).
Proof.
 intros present cs M H. destruct(CallPostCode present cs SuccessHead M H)as[result[Code[Read _]]].
 destruct Code as[[E _]|[_ E]];[discriminate|subst result;rewrite Read;discriminate].
Qed.
