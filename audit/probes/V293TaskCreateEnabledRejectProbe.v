Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateEnabledReject.
Require Import CertiOS.certiucos.v293.proofs.V293TimeShared.
(* Enabled-IE literal minimal early-exit fixtures: original 12 declarations, distinct byte
   ownership. Independent of success/empty TCB fixtures; empty LINV is test-only.
   Controls concern the actual critical-exit primitive and saved IE, not full function traces. *)
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
 (RIGE,RILE,M,(fun _=>false),(true,[],[]),(emp:osabst),spec_done None).
Definition RIByte b tp v := V293_encoded_memory b 0%Z true(encode_val tp v).
Definition RICurrent := V293_encoded_memory 503%positive 0%Z false(encode_val(Tptr Tvoid)(Vptr RITid)).
Definition RILocals p := merge(RIByte 401%positive(Tint16)(Vint32 Int.zero))(merge(RIByte 402%positive(Tptr Tvoid)(Vnull))(merge(RIByte 403%positive(Tint32)(Vint32 Int.zero))(merge(RIByte 404%positive(Tptr Tint32)(Vnull))(merge(RIByte 405%positive(Tint16)(Vint32 Int.zero))(merge(RIByte 406%positive(Tint8)(V293_byteval p))(merge(RIByte 407%positive(Tptr Tint32)(Vnull))(merge(RIByte 408%positive(Tptr Tvoid)(Vnull))(merge(RIByte 409%positive(Tint32)(V293_task_selector 17%Z))(merge(RIByte 410%positive(Tptr Tint32)(Vundef))(merge(RIByte 411%positive(Tint8)(Vundef))(merge(RIByte 412%positive(Tint32)(Vundef))((emp:mem))))))))))))).
Definition RILocalAsrt p := LV 204%Z @ (Tint16) |->(Vint32 Int.zero) ** (LV 208%Z @ (Tptr Tvoid) |->(Vnull) ** (LV 207%Z @ (Tint32) |->(Vint32 Int.zero) ** (LV 205%Z @ (Tptr Tint32) |->(Vnull) ** (LV 206%Z @ (Tint16) |->(Vint32 Int.zero) ** (LV 101%Z @ (Tint8) |->(V293_byteval p) ** (LV 203%Z @ (Tptr Tint32) |->(Vnull) ** (LV 202%Z @ (Tptr Tvoid) |->(Vnull) ** (LV 201%Z @ (Tint32) |->(V293_task_selector 17%Z) ** (LV 108%Z @ (Tptr Tint32) |->(Vundef) ** (LV 209%Z @ (Tint8) |->(Vundef) ** (LV 109%Z @ (Tint32) |->(Vundef) ** (Aemp)))))))))))).
Definition RIExtra k := match k with
 | V293_create_bad_priority=>(emp:mem)
 | V293_create_from_isr=>RIByte 501%positive Tint8(V293_byteval 1)
 | V293_create_occupied_priority=>merge(RIByte 501%positive Tint8(V293_byteval 0))
   (V293_encoded_memory 502%positive 44%Z true(encode_val(Tptr V293_tcb_type)(Vptr RISlot))) end.
Definition RIMemory k := merge(RILocals(RIPriority k))RICurrent.
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

Definition ERCore k := V293_create_borrowed k 502%positive 501%positive(RIPriority k)(RINest k)RISlot Aemp.
Lemma EREmptyPrecise : forall P,
 (forall s,s |= P -> getmem s=emp /\ getabst s=emp) -> precise P.
Proof.
 intros P Empty s M1 M2 O1 O2 H1 H2 M O HM1 HM2 HO1 HO2.
 destruct s as [[[[[[ge le] mem] ir] aux] oldO] op].
 pose proof(Empty _ H1)as[E1 F1]. specialize(Empty _ H2)as[E2 F2].
 change(M1=emp)in E1. change(M2=emp)in E2.
 change(O1=emp)in F1. change(O2=emp)in F2. split;congruence.
Qed.
Lemma ERPointPrecise : forall a tp v,precise(Amapsto a tp true v).
Proof.
 intros a tp v s M1 M2 O1 O2 H1 H2 M O HM1 HM2 HO1 HO2.
 destruct s as [[[[[[ge le] mem] ir] aux] oldO] op].
 change(mapstoval a tp true v M1 /\ O1=emp)in H1.
 change(mapstoval a tp true v M2 /\ O2=emp)in H2.
 destruct H1 as[[v1[E1 P1]]Oe1]. destruct H2 as[[v2[E2 P2]]Oe2].
 subst v1 v2. split;[eapply ptomvallist_mem_eq;eauto|congruence].
Qed.
Lemma ERGlobalsPrecise : forall k table bn,precise(V293_create_rejection_globals k table bn).
Proof.
 intros k table bn. destruct k;cbn[V293_create_rejection_globals].
 - apply EREmptyPrecise. intros [[[[[[ge le] M] ir] aux] O] op] H;exact H.
 - apply EREmptyPrecise. intros s[b[E[A[EM EO]]]];auto.
 - apply precise_star;apply EREmptyPrecise;intros s[b[E[A[EM EO]]]];auto.
Qed.
Lemma ERCorePrecise : forall k,precise(ERCore k).
Proof.
 intro k. unfold ERCore,V293_create_borrowed.
 destruct k;cbn[V293_create_rejection_extra_cells V293_rdy_raw_cells].
 - apply precise_star;[apply ERGlobalsPrecise|apply EREmptyPrecise;intros [[[[[[ge le] M] ir] aux] O] op] H;exact H].
 - apply precise_star;[apply ERPointPrecise| ]. apply precise_star;
   [apply ERGlobalsPrecise|apply EREmptyPrecise;intros [[[[[[ge le] M] ir] aux] O] op] H;exact H].
 - apply precise_star;[apply ERPointPrecise| ]. apply precise_star;[apply ERPointPrecise| ].
   apply precise_star;[apply ERGlobalsPrecise|apply EREmptyPrecise;intros [[[[[[ge le] M] ir] aux] O] op] H;exact H].
Qed.
Lemma ERCoreGood : forall k,GoodInvAsrt(ERCore k).
Proof.
 intro k. destruct k;cbn[ERCore V293_create_borrowed V293_create_rejection_extra_cells V293_create_rejection_globals V293_rdy_raw_cells GoodInvAsrt];tauto.
Qed.
Lemma ERCoreISR : forall k,assertion.inv_isr_prop(ERCore k).
Proof.
 intro k. destruct k;unfold assertion.inv_isr_prop,ERCore,V293_create_borrowed;
 cbn[V293_create_rejection_extra_cells V293_create_rejection_globals V293_rdy_raw_cells];repeat split;intros;
 destruct s as [[[[[[ge le] M] ir] [[ie si] cs]] O] op];exact H.
Qed.
Definition ERInv k : Inv := fun i=>match i with
 | O=>mkinvasrt(ERCoreGood k)(conj(ERCorePrecise k)(ERCoreISR k))
 | S j=>V293_shared_inv(S j) end.
Lemma ERNoisrTail : forall k n i,starinv_noisr(ERInv k)(S i)n <==> Aemp.
Proof.
 intros k. induction n;intros i s;cbn[starinv_noisr];[reflexivity| ].
 change(s |= Aemp ** starinv_noisr(ERInv k)(S(S i))n <-> s |= Aemp).
 split;intro H.
 - apply astar_l_aemp_elim in H. apply IHn in H;exact H.
 - apply astar_l_aemp_intro. apply IHn;exact H.
Qed.
Lemma ERNoisrCore : forall k n,starinv_noisr(ERInv k)0 n <==> ERCore k.
Proof.
 intros k[ |n]s;[reflexivity| ].
 change(s |= ERCore k ** starinv_noisr(ERInv k)1 n <-> s |= ERCore k).
 split;intro H.
 - apply astar_r_aemp_elim. eapply astar_mono;[intros st HS;exact HS|intros st HS;apply ERNoisrTail in HS;exact HS|exact H].
 - eapply astar_mono;[intros st HS;exact HS|intros st HS;apply ERNoisrTail;exact HS| ]. apply astar_r_aemp_intro;exact H.
Qed.
Theorem ERBorrowEquivalence : forall k n,
 Aisr(fun _=>false) ** invlth_isr(ERInv k)0 n <==> Aisr(fun _=>false) ** ERCore k.
Proof.
 intros k n s. destruct s as [[[[[[ge le] M] ir] aux] O] op]. split;intro H.
 all: (apply sat_split in H;destruct H as(m1&m2&o1&o2&JM&JO&H1&H2);
 destruct H1 as[E Empty];cbn in E;subst ir;
 apply sat_split';exists m1;exists m2;exists o1;exists o2;
 split;[exact JM| ];split;[exact JO| ];split;[split;[reflexivity|exact Empty]| ]).
 - unfold invlth_isr in H2. rewrite Nat.sub_0_r in H2.
   apply ERNoisrCore with(n:=n). eapply invisr_imply_noisr';[ |exact H2]. reflexivity.
 - unfold invlth_isr. rewrite Nat.sub_0_r.
   apply V293_shared_clear_noisr_close;[reflexivity| ]. apply ERNoisrCore;exact H2.
Qed.
Definition ERFpre k := V293_create_enabled_fpre 17%Z Vnull Vnull(RIPriority k)
 (Vint32 Int.zero)Vnull(Vint32 Int.zero)Vnull(Vint32 Int.zero)
 RIR(spec_done None)(fun _=>false)[][]RIRFun.
Definition ERFpost k := V293_create_enabled_fpost k RIR(spec_done None)(fun _=>false)[][]RIRFun.
Definition ERProgram : progunit := fun f=>
 if Z.eq_dec f 903%Z then Some(V293_CreateExt_function 92%Z 99%Z 97%Z 98%Z 904%Z 902%Z 900%Z)else None.
Definition ERPre k := V293_create_internal_pre_cells 17%Z Vnull Vnull(RIPriority k)
 (Vint32 Int.zero)Vnull(Vint32 Int.zero)Vnull(Vint32 Int.zero) **
 getasrt(ERFpre k(RIArgs k)[]RITid) ** V293_create_internal_domain.
Definition ERPost k : retasrt := fun result=>V293_create_internal_post_cells **
 getasrt(ERFpost k(RIArgs k)result[]RITid) ** V293_create_internal_domain.
Theorem ERRealBuilders : forall k,
 Some(ERPre k)=BuildPreI ERProgram 903%Z(rev(RIArgs k))[](ERFpre k)RITid /\
 Some(ERPost k)=BuildRetI ERProgram 903%Z(rev(RIArgs k))[](ERFpost k)RITid.
Proof.
 intro k. destruct k;unfold BuildPreI,BuildRetI,ERProgram;
 destruct(Z.eq_dec 903%Z 903%Z);[ |contradiction| |contradiction| |contradiction];
 rewrite rev_involutive;split;reflexivity.
Qed.
Theorem ERContractChecked : forall k,
 InfRules(fun _=>None)V293_scheduler V293_witness_li(ERInv k)
 (ERPost k)Afalse(ERPre k)(V293_CreateExt_body 92%Z 99%Z 97%Z 98%Z 904%Z 902%Z 900%Z)Afalse RITid.
Proof.
 intro k. eapply V293_OSTaskCreateExt_enabled_rejection_contract with(P:=ERProgram)
 (creator:=903%Z)(k:=k)(p:=RIPriority k)(n:=RINest k)(K:=Aemp)
 (vl:=rev(RIArgs k))(lg:=[])(good:=RIRFun)
 (isr:=fun _=>false)(is:=[])(cs:=[])(table:=502%positive)(bn:=501%positive)(slot:=RISlot)
 (R:=RIR)(aop:=spec_done None)(target:=17%Z)(argv:=Vnull)(inputtop:=Vnull)
 (identity:=Vint32 Int.zero)(bottom:=Vnull)(size:=Vint32 Int.zero)(ext:=Vnull)(options:=Vint32 Int.zero).
 - destruct k;cbn[V293_create_rejection_valid RIPriority RINest];repeat split;lia.
 - reflexivity.
 - apply RIRFrame.
 - apply RIRInv.
 - intro Needed. apply ERBorrowEquivalence.
 - unfold ERProgram. destruct(Z.eq_dec 903%Z 903%Z);[reflexivity|contradiction].
 - apply ERRealBuilders.
 - apply ERRealBuilders.
Qed.

Lemma ERExternalSpatial : RIState RICurrent |= V293_create_enabled_external
 RIR(spec_done None)(fun _=>false)[][].
Proof.
 unfold V293_create_enabled_external. apply astar_l_aop'_intro;[ |reflexivity].
 assert(K:RIState RICurrent |= Aisr(fun _=>false) ** Aie true ** Ais nil ** Acs nil ** RIR).
 { apply astar_l_aisr_intro;[ |reflexivity]. apply astar_l_aie_intro;[ |reflexivity].
   apply astar_l_ais_intro;[ |reflexivity]. apply astar_l_acs_intro;[ |reflexivity]. apply RICurrentSpatial. }
 clear -K;sep auto.
Qed.
Lemma ERLiteralSpatial : forall k,RIState(RIMemory k) |= RILocalAsrt(RIPriority k) **
 V293_create_enabled_external RIR(spec_done None)(fun _=>false)[][].
Proof.
 intro k. eapply RIStar with(m1:=RILocals(RIPriority k))(m2:=RICurrent).
 - unfold RILocals,RIByte. apply map_join_merge;apply map_disjoint;intros[b off].
   destruct(Pos.eq_dec b 503%positive);[subst b;left;unfold RILocals,RIByte;RIOutside|right;left;unfold RICurrent;RIOutside].
 - apply RILocalsSpatial.
 - apply ERExternalSpatial.
Qed.
Theorem ERLiteralBuilderEntry : forall k,RIState(RIMemory k) |= ERPre k.
Proof.
 intro k. pose proof(ERLiteralSpatial k)as H.
 assert(D:RIState(RIMemory k) |= V293_create_internal_domain **
 (RILocalAsrt(RIPriority k) ** V293_create_enabled_external RIR(spec_done None)(fun _=>false)[][])).
 { apply astar_l_adomlenv_intro;[exact H|apply RIExactDomain]. }
 unfold ERPre,ERFpre,V293_create_enabled_fpre,getasrt,
 V293_create_internal_pre_cells,V293_create_internal_values,V293_create_internal_locals,RIArgs.
 unfold RILocalAsrt in D. clear -D;sep auto.
Qed.
Theorem ERLiteralCore : forall k,RIState(RIExtra k) |= ERCore k.
Proof.
 intro k. unfold ERCore,V293_create_borrowed. apply V293_raw_cells_join.
 eapply RIStar with(m1:=RIExtra k)(m2:=emp).
 - apply map_join_emp.
 - apply RIExtraSpatial.
 - apply astar_r_aemp_intro. apply RIGlobals.
Qed.
Theorem ERLiteralAmbient : forall k,RIState(RIExtra k) |= invlth_isr(ERInv k)0 INUM.
Proof.
 intro k. unfold invlth_isr. rewrite Nat.sub_0_r.
 apply V293_shared_clear_noisr_close;[reflexivity| ]. apply ERNoisrCore. apply ERLiteralCore.
Qed.
Theorem ERLiteralDisjoint : forall k,
 join(RIMemory k)(RIExtra k)(merge(RIMemory k)(RIExtra k)).
Proof.
 intro k. apply map_join_merge;apply map_disjoint;intros[b off].
 destruct(Pos.eq_dec b 501%positive);[subst b;left;unfold RIMemory,RILocals,RICurrent,RIByte;RIOutside| ].
 destruct(Pos.eq_dec b 502%positive);[subst b;left;unfold RIMemory,RILocals,RICurrent,RIByte;RIOutside|right;left].
 destruct k;cbn[RIExtra];unfold RIByte;RIOutside.
Qed.
Theorem ERSharedByteNotInCaller : forall k,
 get(RIMemory k)(501%positive,0%Z)=None.
Proof. intro k. unfold RIMemory,RILocals,RICurrent,RIByte. RIOutside. Qed.
Theorem ERSharedPhysicalLoad :
 load Tint8(RIExtra V293_create_occupied_priority)(501%positive,0%Z)=Some(V293_byteval 0) /\
 load(Tptr V293_tcb_type)(RIExtra V293_create_occupied_priority)(502%positive,44%Z)=Some(Vptr RISlot).
Proof.
 pose proof(ERLiteralCore V293_create_occupied_priority)as H.
 unfold ERCore,V293_create_borrowed in H. split.
 - change(load Tint8(getmem(RIState(RIExtra V293_create_occupied_priority)))(501%positive,0%Z)=Some(V293_byteval 0)).
   eapply V293_rdy_raw_load with(cells:=V293_create_rejection_extra_cells V293_create_occupied_priority 502%positive 501%positive 11 0 RISlot);[left;reflexivity|reflexivity|exact H].
 - change(load(Tptr V293_tcb_type)(getmem(RIState(RIExtra V293_create_occupied_priority)))(502%positive,44%Z)=Some(Vptr RISlot)).
   eapply V293_rdy_raw_load with(cells:=V293_create_rejection_extra_cells V293_create_occupied_priority 502%positive 501%positive 11 0 RISlot);[right;left;reflexivity|reflexivity|exact H].
Qed.
Definition ERWhole k := merge(RIMemory k)(RIExtra k).
Theorem ERSavedExit : forall saved k,
 loststep ERProgram(curs(sprim excrit),(kenil,kstop))
 ((RIGE,RILE,ERWhole k),(fun _=>false),(false,[],[saved]))
 (SKIP,(kenil,kstop))((RIGE,RILE,ERWhole k),(fun _=>false),(saved,[],[])).
Proof. intros. apply excrit_step;reflexivity. Qed.
Theorem ERSavedExitCannotEnableFalse : forall k,
 ~loststep ERProgram(curs(sprim excrit),(kenil,kstop))
 ((RIGE,RILE,ERWhole k),(fun _=>false),(false,[],[false]))
 (SKIP,(kenil,kstop))((RIGE,RILE,ERWhole k),(fun _=>false),(true,[],[])).
Proof. intros k H. inversion H;subst;discriminate. Qed.
Print Assumptions ERContractChecked.
Print Assumptions ERLiteralBuilderEntry.
Print Assumptions ERLiteralAmbient.
Print Assumptions ERSavedExitCannotEnableFalse.

Lemma ERPriorityPhysicalLoad :
 load Tint8(RIMemory V293_create_occupied_priority)(406%positive,0%Z)=Some(V293_byteval 11).
Proof.
 pose proof(ERLiteralSpatial V293_create_occupied_priority)as H.
 assert(L:RIState(RIMemory V293_create_occupied_priority) |=
 (LV 101%Z @ Tint8 |-> V293_byteval 11) ** Atrue).
 { unfold RILocalAsrt in H. clear -H;sep auto. }
 apply sat_split in L. destruct L as(m1&m2&o1&o2&JM&JO&Local&Rest).
 destruct Local as[b Local]. apply sat_split in Local.
 destruct Local as(ma&mb&oa&ob&JML&JOL&Binding&[Points Empty]).
 destruct Binding as[actual[Env[Addr EmptyBinding]]].
 change(get RILE 101%Z=Some(actual,Tint8))in Env.
 assert(actual=406%positive)by(vm_compute in Env;inversion Env;reflexivity).
 subst actual. inversion Addr;subst b.
 eapply load_local;[exact JM| ]. eapply load_local;[apply map_join_comm;exact JML| ].
 eapply mapstoval_load;[reflexivity|exact Points].
Qed.
Definition ERSlotExpr := ebinop oeq(earrayelem(evar 92%Z)(evar 101%Z))(ecast enull(Tptr V293_tcb_type)).
Theorem ERTypedSlotGuard :
 evalval ERSlotExpr(RIGE,RILE,ERWhole V293_create_occupied_priority)=Some(Vint32 Int.zero) /\
 evaltype ERSlotExpr(RIGE,RILE,ERWhole V293_create_occupied_priority)=Some Tint32.
Proof.
 assert(PriorityRead:load Tint8(ERWhole V293_create_occupied_priority)(406%positive,0%Z)=Some(V293_byteval 11)).
 { exact(@load_local (ERWhole V293_create_occupied_priority) Tint8 (406%positive,0%Z) (V293_byteval 11)
 (RIMemory V293_create_occupied_priority)(RIExtra V293_create_occupied_priority)
 (ERLiteralDisjoint V293_create_occupied_priority) ERPriorityPhysicalLoad). }
 assert(SlotRead:load(Tptr V293_tcb_type)(ERWhole V293_create_occupied_priority)(502%positive,44%Z)=Some(Vptr RISlot)).
 { exact(@load_local (ERWhole V293_create_occupied_priority)(Tptr V293_tcb_type)(502%positive,44%Z)(Vptr RISlot)
 (RIExtra V293_create_occupied_priority)(RIMemory V293_create_occupied_priority)
 ltac:(apply map_join_comm;exact(ERLiteralDisjoint V293_create_occupied_priority))(proj2 ERSharedPhysicalLoad)). }
 assert(Nt:get RILE 92%Z=None)by(vm_compute;reflexivity).
 assert(Gt:get RIGE 92%Z=Some(502%positive,Tarray(Tptr V293_tcb_type)13))by(vm_compute;reflexivity).
 assert(Bp:get RILE 101%Z=Some(406%positive,Tint8))by(vm_compute;reflexivity).
 remember RIGE as ge in *. remember RILE as le in *.
 remember(ERWhole V293_create_occupied_priority)as M in *. clear Heqge Heqle HeqM.
 unfold ERSlotExpr. split.
 - cbn[evalval evaltype get_lenv get_genv get_mem].
   cbv delta[env var memory.ident Modules.ident block]in *. rewrite Nt,Gt,Bp.
   cbn beta iota. rewrite PriorityRead. cbn[load addr_to_addrval V293_byteval].
   rewrite Int.add_zero_l. unfold Int.mul.
   change(match load(Tptr V293_tcb_type)M
     (502%positive,Int.unsigned(Int.repr 44))with
     |Some v=>val_eq v Vnull|_=>None end=Some(Vint32 Int.zero)).
   rewrite Int.unsigned_repr by(change(0<=44<=4294967295)%Z;lia).
   rewrite SlotRead. reflexivity.
 - cbn[evaltype get_lenv get_genv].
   cbv delta[env var memory.ident Modules.ident block]in *.
   rewrite Nt,Gt,Bp. reflexivity.
Qed.
Print Assumptions ERTypedSlotGuard.
