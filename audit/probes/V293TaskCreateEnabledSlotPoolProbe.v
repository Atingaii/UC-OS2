(* Nullable pool probe: literal disjoint bytes, test-only empty LINV.
   No full function, global invariant or real Hook implementation claim. *)
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateEnabledSlotPool.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtCalls.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateStackCall.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateStackSuccess.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateExtPrefix.
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
Definition NPTid : addrval := (601%positive,Int.zero).
Definition NPR := CurTid NPTid ** LINV V293_witness_li NPTid [].
Lemma NPRFun : GoodFunAsrt NPR.
Proof. cbn[NPR CurTid LINV V293_witness_li Agvarmapsto Agvarenv' Aptrmapsto GoodFunAsrt]. repeat split;exact I. Qed.
Lemma NPRFrame : GoodFrm NPR.
Proof. cbn[NPR CurTid LINV V293_witness_li Agvarmapsto Agvarenv' Aptrmapsto GoodFrm]. repeat split;exact I. Qed.
Lemma NPRInv : NPR ==> CurLINV V293_witness_li NPTid.
Proof. unfold NPR,CurLINV. intros s H. exists([]:list logicvar). clear -H;sep auto. Qed.
Definition NPGE : env := set(set(set(set(emp:env)99%Z(501%positive,Tint8))
 92%Z(502%positive,Tarray(Tptr V293_tcb_type)13))OSTCBCur(503%positive,Tptr Tvoid))97%Z(504%positive,Tint8).
Definition NPLE : env := set(set(set(set(set(set(set(set(set(set(set(set((emp:env))204%Z(401%positive,(Tint16)))208%Z(402%positive,(Tptr Tvoid)))207%Z(403%positive,(Tint32)))205%Z(404%positive,(Tptr Tint32)))206%Z(405%positive,(Tint16)))101%Z(406%positive,(Tint8)))203%Z(407%positive,(Tptr Tint32)))202%Z(408%positive,(Tptr Tvoid)))201%Z(409%positive,(Tint32)))108%Z(410%positive,(Tptr Tint32)))209%Z(411%positive,(Tint8)))109%Z(412%positive,(Tint32)).
Definition NPState M : RstateOP :=
 (NPGE,NPLE,M,(fun _=>false),(true,[],[]),(emp:osabst),spec_done None).
Definition NPByte b tp v := V293_encoded_memory b 0%Z true(encode_val tp v).
Definition NPCurrent := V293_encoded_memory 503%positive 0%Z false(encode_val(Tptr Tvoid)(Vptr NPTid)).
Definition NPLocals p := merge(NPByte 401%positive(Tint16)(Vint32 Int.zero))(merge(NPByte 402%positive(Tptr Tvoid)(Vnull))(merge(NPByte 403%positive(Tint32)(Vint32 Int.zero))(merge(NPByte 404%positive(Tptr Tint32)(Vnull))(merge(NPByte 405%positive(Tint16)(Vint32 Int.zero))(merge(NPByte 406%positive(Tint8)(V293_byteval p))(merge(NPByte 407%positive(Tptr Tint32)(Vnull))(merge(NPByte 408%positive(Tptr Tvoid)(Vnull))(merge(NPByte 409%positive(Tint32)(V293_task_selector 17%Z))(merge(NPByte 410%positive(Tptr Tint32)(Vundef))(merge(NPByte 411%positive(Tint8)(Vundef))(merge(NPByte 412%positive(Tint32)(Vundef))((emp:mem))))))))))))).
Definition NPLocalAsrt p := LV 204%Z @ (Tint16) |->(Vint32 Int.zero) ** (LV 208%Z @ (Tptr Tvoid) |->(Vnull) ** (LV 207%Z @ (Tint32) |->(Vint32 Int.zero) ** (LV 205%Z @ (Tptr Tint32) |->(Vnull) ** (LV 206%Z @ (Tint16) |->(Vint32 Int.zero) ** ((Alvarenv 101%Z Tint8(406%positive,0%Z) ** Amapsto(406%positive,0%Z)Tint8 true(V293_byteval p)) ** (LV 203%Z @ (Tptr Tint32) |->(Vnull) ** (LV 202%Z @ (Tptr Tvoid) |->(Vnull) ** (LV 201%Z @ (Tint32) |->(V293_task_selector 17%Z) ** (LV 108%Z @ (Tptr Tint32) |->(Vundef) ** (LV 209%Z @ (Tint8) |->(Vundef) ** ((Alvarenv 109%Z Tint32(412%positive,0%Z) ** Amapsto(412%positive,0%Z)Tint32 true Vundef) ** (Aemp)))))))))))).
Lemma NPStar : forall m1 m2 m A B,
 join m1 m2 m -> NPState m1 |= A -> NPState m2 |= B -> NPState m |= A ** B.
Proof.
 intros. apply sat_split'. exists m1. exists m2. exists(emp:osabst). exists(emp:osabst).
 split;[exact H| ]. split;[apply map_join_emp| ]. split;assumption.
Qed.
Lemma NPBoundLVar : forall b x tp v,
 get NPLE x=Some(b,tp) -> NPState(NPByte b tp v) |=
 Alvarenv x tp(b,0%Z) ** Amapsto(b,0%Z)tp true v.
Proof.
 intros b x tp v Env. eapply NPStar with(m1:=emp)(m2:=NPByte b tp v).
 - apply map_join_comm;apply map_join_emp.
 - exists b. split;[exact Env| ]. repeat split;reflexivity.
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Lemma NPLVar : forall b x tp v,
 get NPLE x=Some(b,tp) -> NPState(NPByte b tp v) |= LV x @ tp |->v.
Proof. intros b x tp v Env. exists b. apply NPBoundLVar;exact Env. Qed.

Ltac NPOutside :=
 repeat first[rewrite map_merge_semp by reflexivity|
 rewrite V293_encoded_memory_outside by(left;congruence)];reflexivity.
Ltac NPApart b :=
 apply map_join_merge;apply map_disjoint;intros[other off];
 destruct(Pos.eq_dec other b);[subst other;right;left|left];unfold NPByte;NPOutside.
Lemma NPLocalsSpatial : forall p, NPState(NPLocals p) |= NPLocalAsrt p.
Proof.
 intro p. unfold NPLocals,NPLocalAsrt.
 repeat lazymatch goal with
 | |- NPState(merge(NPByte ?b ?tp ?v)?tail) |= _ =>
   eapply NPStar with(m1:=NPByte b tp v)(m2:=tail);
   [NPApart b|first[apply NPLVar|apply NPBoundLVar];vm_compute;reflexivity| ]
 end.
 split;reflexivity.
Qed.
Lemma NPCurrentSpatial : NPState NPCurrent |= NPR.
Proof.
 unfold NPR. eapply NPStar with(m1:=NPCurrent)(m2:=emp).
 - apply map_join_emp.
 - exists Tvoid. exists 503%positive. eapply NPStar with(m1:=emp)(m2:=NPCurrent).
   + apply map_join_comm;apply map_join_emp.
   + exists 503%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
   + split;[apply V293_encoded_memory_mapsto|reflexivity].
 - unfold LINV. apply astar_comm. apply astar_l_apure_intro.
   + split;reflexivity.
   + apply V293_witness_li_good.
Qed.
Lemma NPEmptyPrecise : forall P,
 (forall s,s |= P -> getmem s=emp /\ getabst s=emp) -> precise P.
Proof.
 intros P Empty s M1 M2 O1 O2 H1 H2 M O HM1 HM2 HO1 HO2.
 destruct s as [[[[[[ge le] mem] ir] aux] oldO] op].
 pose proof(Empty _ H1)as[E1 F1]. specialize(Empty _ H2)as[E2 F2].
 change(M1=emp)in E1. change(M2=emp)in E2.
 change(O1=emp)in F1. change(O2=emp)in F2. split;congruence.
Qed.
Definition NPExtra n slot := merge(NPByte 501%positive Tint8(V293_byteval n))
 (V293_encoded_memory 502%positive 44%Z true(encode_val(Tptr V293_tcb_type)(V293_create_slot_value slot))).
Definition NPCaller := merge(NPLocals 11)NPCurrent.
Definition NPWhole slot := merge NPCaller(NPExtra 0 slot).
Definition NPCore := V293_create_nullable_pool 502%positive 501%positive 504%positive 11 Aemp.
Lemma NPGlobals : NPState emp |= V293_create_slot_globals 502%positive 501%positive 504%positive.
Proof.
 unfold V293_create_slot_globals. cbn[V293_create_rejection_globals].
 eapply NPStar with(m1:=emp)(m2:=emp);[apply map_join_emp| | ].
 - eapply NPStar with(m1:=emp)(m2:=emp);[apply map_join_emp| | ].
   all:eexists;split;[vm_compute;reflexivity|repeat split;reflexivity].
 - eexists;split;[vm_compute;reflexivity|repeat split;reflexivity].
Qed.
Lemma NPExtraSpatial : forall n slot,
 NPState(NPExtra n slot) |= V293_create_slot_owned 502%positive 501%positive 504%positive 11 n slot Aemp.
Proof.
 intros n slot. unfold V293_create_slot_owned,V293_create_slot_cells.
 apply V293_raw_cells_join. eapply NPStar with(m1:=NPExtra n slot)(m2:=emp).
 - apply map_join_emp.
 - cbn[V293_rdy_raw_cells]. eapply NPStar.
   + unfold NPExtra. NPApart 501%positive.
   + split;[apply V293_encoded_memory_mapsto|reflexivity].
   + apply astar_r_aemp_intro. split;[apply V293_encoded_memory_mapsto|reflexivity].
 - apply astar_r_aemp_intro. apply NPGlobals.
Qed.
Theorem NPLiteralPool : forall n slot,n<256 -> NPState(NPExtra n slot) |= NPCore.
Proof.
 intros n slot Range. apply(V293_create_nullable_close 502%positive 501%positive 504%positive 11 n slot Aemp Range).
 apply NPExtraSpatial.
Qed.
Definition NPStorage :=
 V293_storage_cell(501%positive,0%Z)Tint8 **
 V293_storage_cell(502%positive,44%Z)(Tptr V293_tcb_type) **
 (V293_create_slot_globals 502%positive 501%positive 504%positive ** Aemp).
Lemma NPTypedCell : forall a tp v,
 rule_type_val_match tp v=true -> Amapsto a tp true v ==> V293_storage_cell a tp.
Proof. intros a tp v Typed s H. exists v. sep auto. Qed.
Lemma NPCoreStorage : NPCore ==> NPStorage.
Proof.
 intros s[n[slot H]]. apply astar_l_apure_elim in H. destruct H as[Range H].
 unfold V293_create_slot_owned,V293_create_slot_cells in H. cbn[V293_rdy_raw_cells]in H.
 unfold NPStorage. eapply astar_mono;[apply NPTypedCell;apply V293_byte_type;exact Range| |exact H].
 eapply astar_mono;[apply NPTypedCell;apply V293_create_slot_value_type|intros st HS;exact HS].
Qed.
Lemma NPCorePrecise : precise NPCore.
Proof.
 assert(P:precise NPStorage).
 { unfold NPStorage,V293_create_slot_globals. cbn[V293_create_rejection_globals].
   apply precise_star;[apply V293_storage_cell_precise| ].
   apply precise_star;[apply V293_storage_cell_precise| ].
   apply precise_star.
   - apply precise_star.
     + apply precise_star;apply NPEmptyPrecise;intros s[b[E[A[EM EO]]]];auto.
     + apply NPEmptyPrecise;intros s[b[E[A[EM EO]]]];auto.
   - apply NPEmptyPrecise;intros [[[[[[ge le] M] ir] aux] O] op] H;exact H. }
 intros s M1 M2 O1 O2 H1 H2 M O HM1 HM2 HO1 HO2.
 eapply P;[apply NPCoreStorage;exact H1|apply NPCoreStorage;exact H2|exact HM1|exact HM2|exact HO1|exact HO2].
Qed.
Lemma NPCoreGood : GoodInvAsrt NPCore.
Proof.
 cbn[NPCore V293_create_nullable_pool V293_create_slot_owned V293_create_slot_cells
 V293_create_slot_globals V293_create_rejection_globals V293_rdy_raw_cells GoodInvAsrt]. repeat split;exact I.
Qed.
Lemma NPCoreISR : assertion.inv_isr_prop NPCore.
Proof.
 unfold assertion.inv_isr_prop,NPCore,V293_create_nullable_pool,V293_create_slot_owned,
 V293_create_slot_cells,V293_create_slot_globals. cbn[V293_create_rejection_globals V293_rdy_raw_cells].
 repeat split;intros;destruct s as [[[[[[ge le] M] ir] [[ie si] cs]] O] op];exact H.
Qed.
Definition NPInv : Inv := fun i=>match i with
 | O=>mkinvasrt NPCoreGood(conj NPCorePrecise NPCoreISR)
 | S j=>V293_shared_inv(S j) end.
Lemma NPNoisrTail : forall n i,starinv_noisr NPInv(S i)n <==> Aemp.
Proof.
 induction n;intros i s;cbn[starinv_noisr];[reflexivity| ].
 change(s |= Aemp ** starinv_noisr NPInv(S(S i))n <-> s |= Aemp).
 split;intro H.
 - apply astar_l_aemp_elim in H. apply IHn in H;exact H.
 - apply astar_l_aemp_intro. apply IHn;exact H.
Qed.
Lemma NPNoisrCore : forall n,starinv_noisr NPInv 0 n <==> NPCore.
Proof.
 intros[ |n]s;[reflexivity| ].
 change(s |= NPCore ** starinv_noisr NPInv 1 n <-> s |= NPCore).
 split;intro H.
 - apply astar_r_aemp_elim. eapply astar_mono;[intros st HS;exact HS|intros st HS;apply NPNoisrTail in HS;exact HS|exact H].
 - eapply astar_mono;[intros st HS;exact HS|intros st HS;apply NPNoisrTail;exact HS| ]. apply astar_r_aemp_intro;exact H.
Qed.
Theorem NPBorrowEquivalence : forall n,
 Aisr(fun _=>false) ** invlth_isr NPInv 0 n <==> Aisr(fun _=>false) ** NPCore.
Proof.
 intros n s. destruct s as [[[[[[ge le] M] ir] aux] O] op]. split;intro H.
 all: (apply sat_split in H;destruct H as(m1&m2&o1&o2&JM&JO&H1&H2);
 destruct H1 as[E Empty];cbn in E;subst ir;
 apply sat_split';exists m1;exists m2;exists o1;exists o2;
 split;[exact JM| ];split;[exact JO| ];split;[split;[reflexivity|exact Empty]| ]).
 - unfold invlth_isr in H2. rewrite Nat.sub_0_r in H2.
   apply NPNoisrCore with(n:=n). eapply invisr_imply_noisr';[ |exact H2]. reflexivity.
 - unfold invlth_isr. rewrite Nat.sub_0_r.
   apply V293_shared_clear_noisr_close;[reflexivity| ]. apply NPNoisrCore;exact H2.
Qed.
Theorem NPSameInvariantBothSlots :
 NPState(NPExtra 0 None) |= invlth_isr NPInv 0 INUM /\
 NPState(NPExtra 0(Some(504%positive,Int.zero))) |= invlth_isr NPInv 0 INUM.
Proof.
 split;unfold invlth_isr;rewrite Nat.sub_0_r;
 apply V293_shared_clear_noisr_close;[reflexivity| |reflexivity| ];
 apply NPNoisrCore;apply NPLiteralPool;lia.
Qed.
Theorem NPCallerHasNoSharedBytes :
 get NPCaller(501%positive,0%Z)=None /\ get NPCaller(502%positive,44%Z)=None.
Proof. unfold NPCaller,NPLocals,NPCurrent,NPByte. split;NPOutside. Qed.
Lemma NPExactDomain : eq_dom_env NPLE(getlenvdom V293_create_internal_declarations).
Proof.
 unfold eq_dom_env. intros x tp.
 destruct(Z.eq_dec x 109%Z)as[E109|E109].
 { subst x. cbn[V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
   unfold NPLE. repeat rewrite map_get_set' by congruence. rewrite map_get_set. split.
   - intro H. repeat destruct H as[H|H];try discriminate;try contradiction;inversion H;subst;eexists;reflexivity.
   - intros[b H]. inversion H;subst. cbn. tauto. }
 destruct(Z.eq_dec x 209%Z)as[E209|E209].
 { subst x. cbn[V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
   unfold NPLE. repeat rewrite map_get_set' by congruence. rewrite map_get_set. split.
   - intro H. repeat destruct H as[H|H];try discriminate;try contradiction;inversion H;subst;eexists;reflexivity.
   - intros[b H]. inversion H;subst. cbn. tauto. }
 destruct(Z.eq_dec x 108%Z)as[E108|E108].
 { subst x. cbn[V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
   unfold NPLE. repeat rewrite map_get_set' by congruence. rewrite map_get_set. split.
   - intro H. repeat destruct H as[H|H];try discriminate;try contradiction;inversion H;subst;eexists;reflexivity.
   - intros[b H]. inversion H;subst. cbn. tauto. }
 destruct(Z.eq_dec x 201%Z)as[E201|E201].
 { subst x. cbn[V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
   unfold NPLE. repeat rewrite map_get_set' by congruence. rewrite map_get_set. split.
   - intro H. repeat destruct H as[H|H];try discriminate;try contradiction;inversion H;subst;eexists;reflexivity.
   - intros[b H]. inversion H;subst. cbn. tauto. }
 destruct(Z.eq_dec x 202%Z)as[E202|E202].
 { subst x. cbn[V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
   unfold NPLE. repeat rewrite map_get_set' by congruence. rewrite map_get_set. split.
   - intro H. repeat destruct H as[H|H];try discriminate;try contradiction;inversion H;subst;eexists;reflexivity.
   - intros[b H]. inversion H;subst. cbn. tauto. }
 destruct(Z.eq_dec x 203%Z)as[E203|E203].
 { subst x. cbn[V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
   unfold NPLE. repeat rewrite map_get_set' by congruence. rewrite map_get_set. split.
   - intro H. repeat destruct H as[H|H];try discriminate;try contradiction;inversion H;subst;eexists;reflexivity.
   - intros[b H]. inversion H;subst. cbn. tauto. }
 destruct(Z.eq_dec x 101%Z)as[E101|E101].
 { subst x. cbn[V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
   unfold NPLE. repeat rewrite map_get_set' by congruence. rewrite map_get_set. split.
   - intro H. repeat destruct H as[H|H];try discriminate;try contradiction;inversion H;subst;eexists;reflexivity.
   - intros[b H]. inversion H;subst. cbn. tauto. }
 destruct(Z.eq_dec x 206%Z)as[E206|E206].
 { subst x. cbn[V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
   unfold NPLE. repeat rewrite map_get_set' by congruence. rewrite map_get_set. split.
   - intro H. repeat destruct H as[H|H];try discriminate;try contradiction;inversion H;subst;eexists;reflexivity.
   - intros[b H]. inversion H;subst. cbn. tauto. }
 destruct(Z.eq_dec x 205%Z)as[E205|E205].
 { subst x. cbn[V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
   unfold NPLE. repeat rewrite map_get_set' by congruence. rewrite map_get_set. split.
   - intro H. repeat destruct H as[H|H];try discriminate;try contradiction;inversion H;subst;eexists;reflexivity.
   - intros[b H]. inversion H;subst. cbn. tauto. }
 destruct(Z.eq_dec x 207%Z)as[E207|E207].
 { subst x. cbn[V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
   unfold NPLE. repeat rewrite map_get_set' by congruence. rewrite map_get_set. split.
   - intro H. repeat destruct H as[H|H];try discriminate;try contradiction;inversion H;subst;eexists;reflexivity.
   - intros[b H]. inversion H;subst. cbn. tauto. }
 destruct(Z.eq_dec x 208%Z)as[E208|E208].
 { subst x. cbn[V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
   unfold NPLE. repeat rewrite map_get_set' by congruence. rewrite map_get_set. split.
   - intro H. repeat destruct H as[H|H];try discriminate;try contradiction;inversion H;subst;eexists;reflexivity.
   - intros[b H]. inversion H;subst. cbn. tauto. }
 destruct(Z.eq_dec x 204%Z)as[E204|E204].
 { subst x. cbn[V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
   unfold NPLE. repeat rewrite map_get_set' by congruence. rewrite map_get_set. split.
   - intro H. repeat destruct H as[H|H];try discriminate;try contradiction;inversion H;subst;eexists;reflexivity.
   - intros[b H]. inversion H;subst. cbn. tauto. }
 cbn[V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
 unfold NPLE. repeat rewrite map_get_set' by congruence. rewrite map_emp_get.
 split;[intro H;repeat destruct H as[H|H];try contradiction;inversion H;congruence|intros[b H];discriminate].
Qed.
Definition NPKept :=
 LV 208%Z @ (Tptr Tvoid) |->Vnull ** LV 207%Z @ Tint32 |->Vint32 Int.zero **
 LV 205%Z @ (Tptr Tint32) |->Vnull ** LV 206%Z @ Tint16 |->Vint32 Int.zero **
 LV 209%Z @ Tint8 |->Vundef ** V293_create_internal_domain.
Definition NPFrame := LV 108%Z @ (Tptr Tint32) |->Vundef **
 V293_create_stack_arguments 17%Z Vnull Vnull(Vint32 Int.zero)(NPR ** NPKept).
Lemma NPCallerSpatial : NPState NPCaller |=
 V293_create_enabled_state 406%positive 412%positive 11 Vundef NPFrame
 (spec_done None)(fun _=>false)[][].
Proof.
 assert(H:NPState NPCaller |= NPLocalAsrt 11 ** NPR).
 { eapply NPStar with(m1:=NPLocals 11)(m2:=NPCurrent).
   - unfold NPCaller,NPLocals,NPByte. apply map_join_merge;apply map_disjoint;intros[b off].
     destruct(Pos.eq_dec b 503%positive);[subst b;left;unfold NPLocals,NPByte;NPOutside|right;left;unfold NPCurrent;NPOutside].
   - apply NPLocalsSpatial.
   - apply NPCurrentSpatial. }
 pose proof(@astar_l_adomlenv_intro (NPState NPCaller) _ _ H NPExactDomain)as D.
 change(NPState NPCaller |= V293_create_internal_domain ** (NPLocalAsrt 11 ** NPR))in D.
 unfold V293_create_enabled_state,V293_create_enabled_locals,NPFrame,NPKept,
 V293_create_stack_arguments,NPLocalAsrt. cbn[V293_rdy_raw_cells].
 unfold NPLocalAsrt in D. clear -D;sep auto;reflexivity.
Qed.
Lemma NPFrameGood : GoodFrm NPFrame.
Proof.
 unfold NPFrame,NPKept,V293_create_stack_arguments,Alvarmapsto,Alvarenv',Aptrmapsto,
 V293_create_internal_domain. cbn[GoodFrm]. pose proof NPRFrame;tauto.
Qed.
Lemma NPFrameLINV : NPFrame ==> CurLINV V293_witness_li NPTid.
Proof.
 unfold NPFrame,V293_create_stack_arguments. do 5 apply V293_star_CurLINV_r.
 apply V293_star_CurLINV_l;apply NPRInv.
Qed.
Lemma NPViews : V293_create_slot_globals 502%positive 501%positive 504%positive ** NPFrame ==>
 V293_create_slot_views 502%positive 501%positive 504%positive ** NPFrame.
Proof.
 intros s H.
 assert(K:s |= (V293_create_slot_globals 502%positive 501%positive 504%positive ** V293_create_internal_domain) **
 (LV 108%Z @ (Tptr Tint32) |->Vundef ** V293_create_stack_arguments 17%Z Vnull Vnull(Vint32 Int.zero)
 (NPR ** (LV 208%Z @ (Tptr Tvoid) |->Vnull ** LV 207%Z @ Tint32 |->Vint32 Int.zero **
 LV 205%Z @ (Tptr Tint32) |->Vnull ** LV 206%Z @ Tint16 |->Vint32 Int.zero ** LV 209%Z @ Tint8 |->Vundef)))).
 { unfold NPFrame,NPKept,V293_create_stack_arguments in *;clear -H;sep auto. }
 eapply astar_mono in K;[ |apply V293_create_slot_global_views|intros st HS;exact HS].
 unfold NPFrame,NPKept,V293_create_stack_arguments in *;clear -K;sep auto.
Qed.
Theorem NPEnterChecked :
 InfRules(fun _=>None)V293_scheduler V293_witness_li NPInv(fun _=>Afalse) Afalse
 (V293_create_enabled_state 406%positive 412%positive 11 Vundef NPFrame(spec_done None)(fun _=>false)[][])
 (sprim encrit)
 (EX n:nat,EX slot:option addrval,[|n<256|] **
 V293_create_slot_state 406%positive 412%positive 502%positive 501%positive 504%positive 11 n slot
 Vundef Aemp NPFrame(spec_done None)(fun _=>false)[][])NPTid.
Proof.
 apply V293_create_nullable_enter.
 - vm_compute;lia.
 - apply NPFrameGood.
 - intros s H;apply NPBorrowEquivalence in H;exact H.
 - apply NPViews.
Qed.
Definition NPExternal := @mkfunasrt
 (V293_create_enabled_external NPR(spec_done None)(fun _=>false)[][])
 (V293_create_enabled_external_good NPR(spec_done None)(fun _=>false)[][]NPRFun).
Definition NPArgs := V293_create_stack_values 17%Z Vnull Vnull(Vint32 Int.zero).
Definition NPHookSpec : funspec := fun f=>if Z.eq_dec f 902%Z then Some
 (V293_create_stack_resource_fpre NPExternal NPArgs,
 V293_create_stack_resource_fpost NPExternal NPArgs Vnull,
 (Tptr Tint32,rev V293_stack_argument_types))else None.
Theorem NPReservationStackChecked :
 InfRules NPHookSpec V293_scheduler V293_witness_li NPInv(fun _=>Afalse) Afalse
 (V293_create_slot_state 406%positive 412%positive 502%positive 501%positive 504%positive 11 0 None
 Vundef Aemp NPFrame(spec_done None)(fun _=>false)[][])
 (sseq(sassign(earrayelem(evar 92%Z)(evar 101%Z))(V293_task_prio_reserved_expr 97%Z))
  (sseq(sprim excrit)(V293_TaskCreateExt_stack_call 108%Z 902%Z 201%Z 202%Z 203%Z 204%Z)))
 (V293_create_enabled_external NPR(spec_done None)(fun _=>false)[][] **
 LV 108%Z @ (Tptr Tint32) |->Vnull **
 V293_create_stack_arguments 17%Z Vnull Vnull(Vint32 Int.zero)
 (V293_create_enabled_locals 406%positive 412%positive 11 Vundef NPKept))NPTid.
Proof.
 apply V293_OSTaskCreateExt_enabled_stack_fragment with(BeforeGood:=NPRFun)(AfterGood:=NPRFun).
 - lia.
 - unfold NPKept,Alvarmapsto,Alvarenv',Aptrmapsto,V293_create_internal_domain. cbn[GoodFrm];tauto.
 - apply NPRFrame.
 - repeat split;reflexivity.
 - apply NPRInv.
 - apply NPRInv.
 - intros s H;apply NPBorrowEquivalence;exact H.
 - unfold NPHookSpec. destruct(Z.eq_dec 902%Z 902%Z);[reflexivity|contradiction].
Qed.
Theorem NPWholeSpatial : forall slot,
 NPState(NPWhole slot) |= (NPLocalAsrt 11 ** NPR) **
 V293_create_slot_owned 502%positive 501%positive 504%positive 11 0 slot Aemp.
Proof.
 intro slot. eapply NPStar with(m1:=NPCaller)(m2:=NPExtra 0 slot).
 - unfold NPWhole. apply map_join_merge;apply map_disjoint;intros[b off].
   destruct(Pos.eq_dec b 501%positive);[subst b;left;unfold NPCaller,NPLocals,NPCurrent,NPByte;NPOutside| ].
   destruct(Pos.eq_dec b 502%positive);[subst b;left;unfold NPCaller,NPLocals,NPCurrent,NPByte;NPOutside|right;left].
   unfold NPExtra,NPByte;NPOutside.
 - eapply NPStar with(m1:=NPLocals 11)(m2:=NPCurrent).
   + unfold NPCaller,NPLocals,NPByte. apply map_join_merge;apply map_disjoint;intros[b off].
     destruct(Pos.eq_dec b 503%positive);[subst b;left;unfold NPLocals,NPByte;NPOutside|right;left;unfold NPCurrent;NPOutside].
   + apply NPLocalsSpatial.
   + apply NPCurrentSpatial.
 - apply NPExtraSpatial.
Qed.
Definition NPStart :=
 (curs(V293_TaskCreateExt_prefix 92%Z 101%Z 99%Z 109%Z 97%Z
  (sseq(V293_TaskCreateExt_stack_call 108%Z 902%Z 201%Z 202%Z 203%Z 204%Z)(sskip None))),(kenil,kstop)).
Definition NPCallSetup :=
 (curs(scall 902%Z[evar 201%Z;evar 202%Z;evar 203%Z;evar 204%Z]),
 (kenil,kassignr(evar 108%Z)(Tptr Tint32)(kseq(sskip None)(kseq V293_TaskCreateExt_occupied kstop)))).
(* Bounded noninterleaved source execution to call setup: the occupied
   continuation is retained, and the Hook has NOT executed in this trace. *)
Theorem NPActualPrefixToCall : forall P,
 exists Mf,
 V293_local_steps P NPStart((NPGE,NPLE,NPWhole None),(fun _=>false),(true,[],[]))
 NPCallSetup((NPGE,NPLE,Mf),(fun _=>false),(true,[],[])) /\
 load(Tptr V293_tcb_type)Mf(502%positive,44%Z)=Some(Vptr(504%positive,Int.zero)) /\
 evaltype(earrayelem(evar 92%Z)(evar 101%Z))(NPGE,NPLE,Mf)=Some(Tptr V293_tcb_type).
Proof.
 intro P. pose proof(NPWholeSpatial None)as Owned.
 assert(Entry:NPState(NPWhole None) |= V293_rdy_raw_cells
 (V293_create_prefix_cells 406%positive 501%positive 412%positive 502%positive 11 Vundef Vnull)Atrue).
 { unfold V293_create_prefix_cells,NPLocalAsrt,V293_create_slot_owned in *.
   cbn[V293_rdy_raw_cells V293_create_slot_cells]in *;clear -Owned;sep auto. }
 destruct(V293_OSTaskCreateExt_to_stack_call_setup P kstop NPGE NPLE(NPWhole None)
 (fun _=>false)(true,[],[])(emp:osabst)(spec_done None)Atrue true[][]
 92%Z 101%Z 99%Z 109%Z 97%Z 406%positive 501%positive 412%positive 502%positive 504%positive 11 Vundef
 108%Z 902%Z 201%Z 202%Z 203%Z 204%Z 410%positive(sskip None))as(Mf&Exec&Post).
 all:try reflexivity.
 - lia.
 - exact Entry.
 - exists Mf. split;[exact Exec| ]. split.
   + change(load(Tptr V293_tcb_type)(getmem(NPState Mf))(502%positive,44%Z)=Some(Vptr(504%positive,Int.zero))).
     eapply V293_rdy_raw_load with(cells:=V293_create_prefix_cells 406%positive 501%positive 412%positive 502%positive 11 (Vint32 Int.zero)(Vptr(504%positive,Int.zero)));
     [right;right;right;left;reflexivity|reflexivity|exact Post].
   + unfold NPGE,NPLE. V293_rdy_eval.
Qed.
Print Assumptions NPEnterChecked.
Print Assumptions NPReservationStackChecked.
Print Assumptions NPActualPrefixToCall.
