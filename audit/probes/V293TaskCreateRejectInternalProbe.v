(* Literal minimal early-exit fixtures: original 12 declarations, distinct byte
   ownership. Independent of success/empty TCB fixtures; empty LINV is test-only.
   Controls concern typed guards/return evaluation, not full execution traces. *)
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateRejectInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateEmptyInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateBodyFailure.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateStackEntry.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBClear.
Require Import CertiOS.certiucos.v293.proofs.V293TCBSuccessHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtFunction.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.tactics.hoareforward.init_spec.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.
Definition RIPriority k := match k with V293_create_bad_priority=>13 | _=>11 end.
Definition RINest k := match k with V293_create_from_isr=>1 | _=>0 end.
Definition RISlot : addrval := (701%positive,Int.zero).
Definition RITid : addrval := (601%positive,Int.zero).
Definition RIR := CurTid RITid ** LINV V293_witness_li RITid [].
Lemma RIRFun : GoodFunAsrt RIR.
Proof. cbn[RIR CurTid LINV V293_witness_li Agvarmapsto Agvarenv' Aptrmapsto GoodFunAsrt]. repeat split;exact I. Qed.
Lemma RIRFrame : GoodFrm RIR.
Proof. cbn[RIR CurTid LINV V293_witness_li Agvarmapsto Agvarenv' Aptrmapsto GoodFrm]. repeat split;exact I. Qed.
Lemma RIRInv : RIR ==> CurLINV V293_witness_li RITid.
Proof. unfold RIR,CurLINV. intros s H. exists([]:list logicvar). clear -H;sep auto. Qed.
Definition RIGE : env := set(set(set(emp:env)99%Z(501%positive,Tint8))
 92%Z(502%positive,Tarray(Tptr V293_tcb_type)13))OSTCBCur(503%positive,Tptr Tvoid).
Definition RILE : env := set(set(set(set(set(set(set(set(set(set(set(set((emp:env))204%Z(401%positive,(Tint16)))208%Z(402%positive,(Tptr Tvoid)))207%Z(403%positive,(Tint32)))205%Z(404%positive,(Tptr Tint32)))206%Z(405%positive,(Tint16)))101%Z(406%positive,(Tint8)))203%Z(407%positive,(Tptr Tint32)))202%Z(408%positive,(Tptr Tvoid)))201%Z(409%positive,(Tint32)))108%Z(410%positive,(Tptr Tint32)))209%Z(411%positive,(Tint8)))109%Z(412%positive,(Tint32)).
Definition RIState M : RstateOP :=
 (RIGE,RILE,M,(fun _=>false),(false,[],[]),(emp:osabst),spec_done None).
Definition RIByte b tp v := V293_encoded_memory b 0%Z true(encode_val tp v).
Definition RICurrent := V293_encoded_memory 503%positive 0%Z false(encode_val(Tptr Tvoid)(Vptr RITid)).
Definition RILocals p := merge(RIByte 401%positive(Tint16)(Vint32 Int.zero))(merge(RIByte 402%positive(Tptr Tvoid)(Vnull))(merge(RIByte 403%positive(Tint32)(Vint32 Int.zero))(merge(RIByte 404%positive(Tptr Tint32)(Vnull))(merge(RIByte 405%positive(Tint16)(Vint32 Int.zero))(merge(RIByte 406%positive(Tint8)(V293_byteval p))(merge(RIByte 407%positive(Tptr Tint32)(Vnull))(merge(RIByte 408%positive(Tptr Tvoid)(Vnull))(merge(RIByte 409%positive(Tint32)(V293_task_selector 17%Z))(merge(RIByte 410%positive(Tptr Tint32)(Vundef))(merge(RIByte 411%positive(Tint8)(Vundef))(merge(RIByte 412%positive(Tint32)(Vundef))((emp:mem))))))))))))).
Definition RILocalAsrt p := LV 204%Z @ (Tint16) |->(Vint32 Int.zero) ** (LV 208%Z @ (Tptr Tvoid) |->(Vnull) ** (LV 207%Z @ (Tint32) |->(Vint32 Int.zero) ** (LV 205%Z @ (Tptr Tint32) |->(Vnull) ** (LV 206%Z @ (Tint16) |->(Vint32 Int.zero) ** (LV 101%Z @ (Tint8) |->(V293_byteval p) ** (LV 203%Z @ (Tptr Tint32) |->(Vnull) ** (LV 202%Z @ (Tptr Tvoid) |->(Vnull) ** (LV 201%Z @ (Tint32) |->(V293_task_selector 17%Z) ** (LV 108%Z @ (Tptr Tint32) |->(Vundef) ** (LV 209%Z @ (Tint8) |->(Vundef) ** (LV 109%Z @ (Tint32) |->(Vundef) ** (Aemp)))))))))))).
Definition RIExtra k := match k with
 | V293_create_bad_priority=>(emp:mem)
 | V293_create_from_isr=>RIByte 501%positive Tint8(V293_byteval 1)
 | V293_create_occupied_priority=>merge(RIByte 501%positive Tint8(V293_byteval 0))
   (V293_encoded_memory 502%positive 44%Z true(encode_val(Tptr V293_tcb_type)(Vptr RISlot))) end.
Definition RIMemory k := merge(RILocals(RIPriority k))(merge(RIExtra k)RICurrent).
Lemma RIStar : forall m1 m2 m A B,
 join m1 m2 m -> RIState m1 |= A -> RIState m2 |= B -> RIState m |= A ** B.
Proof.
 intros. apply sat_split'. exists m1. exists m2. exists(emp:osabst). exists(emp:osabst).
 split;[exact H| ]. split;[apply map_join_emp| ]. split;assumption.
Qed.
Lemma RILVar : forall b x tp v,
 get RILE x=Some(b,tp) -> RIState(RIByte b tp v) |= LV x @ tp |->v.
Proof.
 intros b x tp v Env. exists b. eapply RIStar with(m1:=emp)(m2:=RIByte b tp v).
 - apply map_join_comm;apply map_join_emp.
 - exists b. split;[exact Env| ]. repeat split;reflexivity.
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Ltac RIOutside :=
 repeat first[rewrite map_merge_semp by reflexivity|
 rewrite V293_encoded_memory_outside by(left;congruence)];reflexivity.
Ltac RIApart b :=
 apply map_join_merge;apply map_disjoint;intros[other off];
 destruct(Pos.eq_dec other b);[subst other;right;left|left];unfold RIByte;RIOutside.
Lemma RILocalsSpatial : forall p, RIState(RILocals p) |= RILocalAsrt p.
Proof.
 intro p. unfold RILocals,RILocalAsrt.
 repeat lazymatch goal with
 | |- RIState(merge(RIByte ?b ?tp ?v)?tail) |= _ =>
   eapply RIStar with(m1:=RIByte b tp v)(m2:=tail);
   [RIApart b|apply RILVar;vm_compute;reflexivity| ]
 end.
 split;reflexivity.
Qed.
Lemma RICurrentSpatial : RIState RICurrent |= RIR.
Proof.
 unfold RIR. eapply RIStar with(m1:=RICurrent)(m2:=emp).
 - apply map_join_emp.
 - exists Tvoid. exists 503%positive. eapply RIStar with(m1:=emp)(m2:=RICurrent).
   + apply map_join_comm;apply map_join_emp.
   + exists 503%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
   + split;[apply V293_encoded_memory_mapsto|reflexivity].
 - unfold LINV. apply astar_comm. apply astar_l_apure_intro.
   + split;reflexivity.
   + apply V293_witness_li_good.
Qed.
Lemma RIGlobals : forall k,RIState emp |= V293_create_rejection_globals k 502%positive 501%positive.
Proof.
 intro k. destruct k;cbn[V293_create_rejection_globals].
 - split;reflexivity.
 - exists 501%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
 - eapply RIStar with(m1:=emp)(m2:=emp).
   + apply map_join_emp.
   + eexists;split;[vm_compute;reflexivity|repeat split;reflexivity].
   + eexists;split;[vm_compute;reflexivity|repeat split;reflexivity].
Qed.
Lemma RIExtraSpatial : forall k,RIState(RIExtra k) |=
 V293_rdy_raw_cells(V293_create_rejection_extra_cells k 502%positive 501%positive(RIPriority k)(RINest k)RISlot)Aemp.
Proof.
 intro k. destruct k;cbn[RIExtra V293_create_rejection_extra_cells RIPriority RINest V293_rdy_raw_cells].
 - split;reflexivity.
 - apply astar_r_aemp_intro. split;[apply V293_encoded_memory_mapsto|reflexivity].
 - eapply RIStar.
   + RIApart 501%positive.
   + split;[apply V293_encoded_memory_mapsto|reflexivity].
   + apply astar_r_aemp_intro. split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Lemma RIExactDomain : eq_dom_env RILE(getlenvdom V293_create_internal_declarations).
Proof.
 unfold eq_dom_env. intros x tp.
 destruct(Z.eq_dec x 109%Z)as[E109|E109].
 { subst x. cbn[V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
   unfold RILE. repeat rewrite map_get_set' by congruence. rewrite map_get_set. split.
   - intro H. repeat destruct H as[H|H];try discriminate;try contradiction;inversion H;subst;eexists;reflexivity.
   - intros[b H]. inversion H;subst. cbn. tauto. }
 destruct(Z.eq_dec x 209%Z)as[E209|E209].
 { subst x. cbn[V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
   unfold RILE. repeat rewrite map_get_set' by congruence. rewrite map_get_set. split.
   - intro H. repeat destruct H as[H|H];try discriminate;try contradiction;inversion H;subst;eexists;reflexivity.
   - intros[b H]. inversion H;subst. cbn. tauto. }
 destruct(Z.eq_dec x 108%Z)as[E108|E108].
 { subst x. cbn[V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
   unfold RILE. repeat rewrite map_get_set' by congruence. rewrite map_get_set. split.
   - intro H. repeat destruct H as[H|H];try discriminate;try contradiction;inversion H;subst;eexists;reflexivity.
   - intros[b H]. inversion H;subst. cbn. tauto. }
 destruct(Z.eq_dec x 201%Z)as[E201|E201].
 { subst x. cbn[V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
   unfold RILE. repeat rewrite map_get_set' by congruence. rewrite map_get_set. split.
   - intro H. repeat destruct H as[H|H];try discriminate;try contradiction;inversion H;subst;eexists;reflexivity.
   - intros[b H]. inversion H;subst. cbn. tauto. }
 destruct(Z.eq_dec x 202%Z)as[E202|E202].
 { subst x. cbn[V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
   unfold RILE. repeat rewrite map_get_set' by congruence. rewrite map_get_set. split.
   - intro H. repeat destruct H as[H|H];try discriminate;try contradiction;inversion H;subst;eexists;reflexivity.
   - intros[b H]. inversion H;subst. cbn. tauto. }
 destruct(Z.eq_dec x 203%Z)as[E203|E203].
 { subst x. cbn[V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
   unfold RILE. repeat rewrite map_get_set' by congruence. rewrite map_get_set. split.
   - intro H. repeat destruct H as[H|H];try discriminate;try contradiction;inversion H;subst;eexists;reflexivity.
   - intros[b H]. inversion H;subst. cbn. tauto. }
 destruct(Z.eq_dec x 101%Z)as[E101|E101].
 { subst x. cbn[V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
   unfold RILE. repeat rewrite map_get_set' by congruence. rewrite map_get_set. split.
   - intro H. repeat destruct H as[H|H];try discriminate;try contradiction;inversion H;subst;eexists;reflexivity.
   - intros[b H]. inversion H;subst. cbn. tauto. }
 destruct(Z.eq_dec x 206%Z)as[E206|E206].
 { subst x. cbn[V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
   unfold RILE. repeat rewrite map_get_set' by congruence. rewrite map_get_set. split.
   - intro H. repeat destruct H as[H|H];try discriminate;try contradiction;inversion H;subst;eexists;reflexivity.
   - intros[b H]. inversion H;subst. cbn. tauto. }
 destruct(Z.eq_dec x 205%Z)as[E205|E205].
 { subst x. cbn[V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
   unfold RILE. repeat rewrite map_get_set' by congruence. rewrite map_get_set. split.
   - intro H. repeat destruct H as[H|H];try discriminate;try contradiction;inversion H;subst;eexists;reflexivity.
   - intros[b H]. inversion H;subst. cbn. tauto. }
 destruct(Z.eq_dec x 207%Z)as[E207|E207].
 { subst x. cbn[V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
   unfold RILE. repeat rewrite map_get_set' by congruence. rewrite map_get_set. split.
   - intro H. repeat destruct H as[H|H];try discriminate;try contradiction;inversion H;subst;eexists;reflexivity.
   - intros[b H]. inversion H;subst. cbn. tauto. }
 destruct(Z.eq_dec x 208%Z)as[E208|E208].
 { subst x. cbn[V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
   unfold RILE. repeat rewrite map_get_set' by congruence. rewrite map_get_set. split.
   - intro H. repeat destruct H as[H|H];try discriminate;try contradiction;inversion H;subst;eexists;reflexivity.
   - intros[b H]. inversion H;subst. cbn. tauto. }
 destruct(Z.eq_dec x 204%Z)as[E204|E204].
 { subst x. cbn[V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
   unfold RILE. repeat rewrite map_get_set' by congruence. rewrite map_get_set. split.
   - intro H. repeat destruct H as[H|H];try discriminate;try contradiction;inversion H;subst;eexists;reflexivity.
   - intros[b H]. inversion H;subst. cbn. tauto. }
 cbn[V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
 unfold RILE. repeat rewrite map_get_set' by congruence. rewrite map_emp_get.
 split;[intro H;repeat destruct H as[H|H];try contradiction;inversion H;congruence|intros[b H];discriminate].
Qed.
Definition RIArgs k := V293_create_internal_values 17%Z Vnull Vnull(RIPriority k)
 (Vint32 Int.zero)Vnull(Vint32 Int.zero)Vnull(Vint32 Int.zero).
Definition RIFpre k := V293_create_reject_fpre k 502%positive 501%positive(RIPriority k)(RINest k)RISlot
 17%Z Vnull Vnull(Vint32 Int.zero)Vnull(Vint32 Int.zero)Vnull(Vint32 Int.zero)
 RIR(spec_done None)(fun _=>false)[][]RIRFun.
Definition RIFpost k := V293_create_reject_fpost k 502%positive 501%positive(RIPriority k)(RINest k)RISlot
 RIR(spec_done None)(fun _=>false)[][]RIRFun.
Definition RIProgram : progunit := fun f=>
 if Z.eq_dec f 903%Z then Some(V293_CreateExt_function 92%Z 99%Z 97%Z 98%Z 904%Z 902%Z 900%Z)else None.
Definition RIPre k := V293_create_internal_pre_cells 17%Z Vnull Vnull(RIPriority k)
 (Vint32 Int.zero)Vnull(Vint32 Int.zero)Vnull(Vint32 Int.zero) **
 getasrt(RIFpre k(RIArgs k)[]RITid) ** V293_create_internal_domain.
Definition RIPost k : retasrt := fun result=>V293_create_internal_post_cells **
 getasrt(RIFpost k(RIArgs k)result[]RITid) ** V293_create_internal_domain.
Lemma RITypedArguments : forall k,dl_vl_match V293_CreateExt_parameters(RIArgs k)=true.
Proof. intro k;destruct k;reflexivity. Qed.
Theorem RIRealBuilders : forall k,
 Some(RIPre k)=BuildPreI RIProgram 903%Z(rev(RIArgs k))[](RIFpre k)RITid /\ Some(RIPost k)=BuildRetI RIProgram 903%Z(rev(RIArgs k))[](RIFpost k)RITid.
Proof.
 intro k. destruct k;unfold BuildPreI,BuildRetI,RIProgram;
 destruct(Z.eq_dec 903%Z 903%Z);[ |contradiction| |contradiction| |contradiction];
 rewrite rev_involutive;split;reflexivity.
Qed.
Theorem RIContractChecked : forall k,
 InfRules(fun _=>None)V293_scheduler V293_witness_li V293_shared_inv
 (RIPost k)Afalse(RIPre k)(V293_CreateExt_body 92%Z 99%Z 97%Z 98%Z 904%Z 902%Z 900%Z)Afalse RITid.
Proof.
 intro k. eapply V293_OSTaskCreateExt_rejection_internal_contract with(P:=RIProgram)
 (creator:=903%Z)(k:=k)(p:=RIPriority k)(n:=RINest k)(vl:=rev(RIArgs k))(lg:=[])(good:=RIRFun).
 - destruct k;cbn[V293_create_rejection_valid RIPriority RINest];repeat split;lia.
 - apply RIRFrame.
 - apply RIRInv.
 - unfold RIProgram. destruct(Z.eq_dec 903%Z 903%Z);[reflexivity|contradiction].
 - apply RIRealBuilders.
 - apply RIRealBuilders.
Qed.

Lemma RIExternalSpatial : forall k,RIState(merge(RIExtra k)RICurrent) |=
 V293_create_reject_external k 502%positive 501%positive(RIPriority k)(RINest k)RISlot
 RIR(spec_done None)(fun _=>false)[][].
Proof.
 intro k. unfold V293_create_reject_external. apply astar_l_aop'_intro;[ |reflexivity].
 apply V293_raw_cells_join. eapply RIStar with(m1:=RIExtra k)(m2:=RICurrent).
 - destruct k;cbn[RIExtra];
   unfold RICurrent;apply map_join_merge;apply map_disjoint;intros[b off].
   all: destruct(Pos.eq_dec b 503%positive);[subst b;left|right;left];
   unfold RIByte;RIOutside.
 - apply RIExtraSpatial.
 - assert(K:RIState RICurrent |= Aisr(fun _=>false) ** Aie false ** (Ais nil) ** (Acs nil) **
   (V293_create_rejection_globals k 502%positive 501%positive ** RIR)).
   { apply astar_l_aisr_intro;[ |reflexivity].
     apply astar_l_aie_intro;[ |reflexivity].
     apply astar_l_ais_intro;[ |reflexivity].
     apply astar_l_acs_intro;[ |reflexivity].
     eapply RIStar with(m1:=emp)(m2:=RICurrent).
     - apply map_join_comm;apply map_join_emp.
     - apply RIGlobals.
     - apply RICurrentSpatial. }
   clear -K;sep auto.
Qed.
Lemma RILiteralSpatial : forall k,RIState(RIMemory k) |= RILocalAsrt(RIPriority k) **
 V293_create_reject_external k 502%positive 501%positive(RIPriority k)(RINest k)RISlot
 RIR(spec_done None)(fun _=>false)[][].
Proof.
 intro k. eapply RIStar with(m1:=RILocals(RIPriority k))(m2:=merge(RIExtra k)RICurrent).
 - unfold RILocals,RIByte. apply map_join_merge;apply map_disjoint;intros[b off].
   destruct(Pos.eq_dec b 501%positive);[subst b;left;unfold RILocals,RIByte;RIOutside| ].
   destruct(Pos.eq_dec b 502%positive);[subst b;left;unfold RILocals,RIByte;RIOutside| ].
   destruct(Pos.eq_dec b 503%positive);[subst b;left;unfold RILocals,RIByte;RIOutside|right;left].
   destruct k;cbn[RIExtra];unfold RICurrent,RIByte;RIOutside.
 - apply RILocalsSpatial.
 - apply RIExternalSpatial.
Qed.
Theorem RILiteralBuilderEntry : forall k,RIState(RIMemory k) |= RIPre k.
Proof.
 intro k. pose proof(RILiteralSpatial k)as H.
 assert(D:RIState(RIMemory k) |= V293_create_internal_domain **
 (RILocalAsrt(RIPriority k) ** V293_create_reject_external k 502%positive 501%positive
 (RIPriority k)(RINest k)RISlot RIR(spec_done None)(fun _=>false)[][])).
 { apply astar_l_adomlenv_intro;[exact H|apply RIExactDomain]. }
 unfold RIPre,RIFpre,V293_create_reject_fpre,getasrt,
 V293_create_internal_pre_cells,V293_create_internal_values,V293_create_internal_locals,RIArgs.
 unfold RILocalAsrt in D. clear -D. sep auto.
Qed.
Definition RIPriorityExpr := ebinop olt(econst32(Int.repr 12))(ecast(evar 101%Z)Tint32).
Definition RINestingExpr := ebinop olt(econst32 Int.zero)(ecast(evar 99%Z)Tint32).
Definition RISlotExpr := ebinop oeq(earrayelem(evar 92%Z)(evar 101%Z))(ecast enull(Tptr V293_tcb_type)).
Lemma RIGuardOwnership : forall k,exists bp bc cpu F,
 RIState(RIMemory k) |= V293_rdy_raw_cells
 (V293_create_rejection_cells k bp bc 502%positive 501%positive(RIPriority k)(RINest k)RISlot cpu)
 (OS[(fun _=>false),false,[],[]] ** (V293_create_rejection_bindings k bp bc 502%positive 501%positive ** F)).
Proof.
 intro k. pose proof(RILiteralBuilderEntry k)as H.
 assert(K:RIState(RIMemory k) |= V293_create_internal_pre_cells 17%Z Vnull Vnull(RIPriority k)
 (Vint32 Int.zero)Vnull(Vint32 Int.zero)Vnull(Vint32 Int.zero) **
 (V293_create_reject_external k 502%positive 501%positive(RIPriority k)(RINest k)RISlot
 RIR(spec_done None)(fun _=>false)[][] ** V293_create_internal_domain)).
 { unfold RIPre,RIFpre,V293_create_reject_fpre,getasrt in H. clear -H;sep auto. }
 apply V293_create_internal_unpack in K. destruct K as[cpu[err[psp[bp[bc K]]]]].
 assert(S:RIState(RIMemory k) |= V293_create_rejection_state k bp bc 502%positive 501%positive
 (RIPriority k)(RINest k)RISlot cpu
 (V293_create_reject_frame 17%Z Vnull Vnull(Vint32 Int.zero)Vnull(Vint32 Int.zero)Vnull(Vint32 Int.zero)err psp RIR)
 (spec_done None)(fun _=>false)[][]).
 { eapply V293_create_reject_entry. exact K. }
 exists bp. exists bc. exists cpu.
 exists(V293_create_reject_frame 17%Z Vnull Vnull(Vint32 Int.zero)Vnull(Vint32 Int.zero)Vnull(Vint32 Int.zero)err psp RIR).
 unfold V293_create_rejection_state in S. apply astar_l_aop'_elim in S;tauto.
Qed.
Lemma RIValid : forall k,V293_create_rejection_valid k(RIPriority k)(RINest k).
Proof. intro k;destruct k;cbn[V293_create_rejection_valid RIPriority RINest];repeat split;lia. Qed.
Lemma RIPriorityEval : forall k,
 evalval RIPriorityExpr(getsmem(RIState(RIMemory k)))=
 Some(Vint32(match k with V293_create_bad_priority=>Int.one|_=>Int.zero end)) /\
 evaltype RIPriorityExpr(getsmem(RIState(RIMemory k)))=Some Tint32.
Proof.
 intro k. destruct(RIGuardOwnership k)as[bp[bc[cpu[F H]]]].
 pose proof(V293_create_rejection_priority k bp bc 502%positive 501%positive(RIPriority k)(RINest k)RISlot cpu F
 (fun _=>false)[][](RIState(RIMemory k))(RIValid k)H)as E.
 destruct k;exact E.
Qed.
Lemma RINestingEval : forall k,k<>V293_create_bad_priority ->
 evalval RINestingExpr(getsmem(RIState(RIMemory k)))=
 Some(Vint32(match k with V293_create_from_isr=>Int.one|_=>Int.zero end)) /\
 evaltype RINestingExpr(getsmem(RIState(RIMemory k)))=Some Tint32.
Proof.
 intros k Needed. destruct(RIGuardOwnership k)as[bp[bc[cpu[F H]]]].
 pose proof(V293_create_rejection_nesting k bp bc 502%positive 501%positive(RIPriority k)(RINest k)RISlot cpu F
 (fun _=>false)[][](RIState(RIMemory k))Needed(RIValid k)H)as E.
 destruct k;[contradiction|exact E|exact E].
Qed.
Lemma RISlotEval :
 evalval RISlotExpr(getsmem(RIState(RIMemory V293_create_occupied_priority)))=Some(Vint32 Int.zero) /\
 evaltype RISlotExpr(getsmem(RIState(RIMemory V293_create_occupied_priority)))=Some Tint32.
Proof.
 destruct(RIGuardOwnership V293_create_occupied_priority)as[bp[bc[cpu[F H]]]].
 unfold RISlotExpr. eapply V293_create_rejection_slot with
 (bp:=bp)(bc:=bc)(table:=502%positive)(bn:=501%positive)(p:=11)(n:=0)(slot:=RISlot)(cpu:=cpu)(F:=F)
 (isr:=fun _=>false)(is:=[])(cs:=[]);[lia|exact H].
Qed.
Lemma RIReturnEval : forall k,
 evalval(econst32(Int.repr(V293_create_rejection_code k)))(getsmem(RIState(RIMemory k)))=
 Some(Vint32(Int.repr(V293_create_rejection_code k))) /\
 evaltype(econst32(Int.repr(V293_create_rejection_code k)))(getsmem(RIState(RIMemory k)))=Some Tint32.
Proof. intro k;destruct k;split;reflexivity. Qed.
Print Assumptions RIContractChecked.
Print Assumptions RILiteralBuilderEntry.
