(* A real node transferred out of the shared pool supplies the old bytes for
   the eighteen original field writes. Shared head stays in Inv. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFreePool.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFieldsHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBClear.
Require Import CertiOS.certiucos.v293.proofs.V293NullBytes.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEmptyEnabled.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEmptyHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitPrefix.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitFunction.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInit.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStoragePrefix.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition V293_tcb_allocated_spares b base :=
 V293_storage ([((b,(base+24)%Z),Tcom_ptr 410%Z);
 ((b,(base+40)%Z),Tint16);((b,(base+42)%Z),Tint8);((b,(base+43)%Z),Tint8)]).

Lemma V293_tcb_allocated_payload_open : forall b base,
 V293_tcb_free_payload b base ==>
 EX old:Z->val,V293_rdy_raw_cells(V293_tcb_init_old_fields b base old)
 (V293_tcb_allocated_spares b base).
Proof.
 intros b base s H.
 change(s |= V293_storage_cell (b,(base+0)%Z) (Tptr Tint32) **
  (V293_storage_cell (b,(base+50)%Z) (Tint8) **
  (V293_storage_cell (b,(base+48)%Z) (Tint8) **
  (V293_storage_cell (b,(base+49)%Z) (Tint8) **
  (V293_storage_cell (b,(base+44)%Z) (Tint32) **
  (V293_storage_cell (b,(base+4)%Z) (Tptr Tvoid) **
  (V293_storage_cell (b,(base+12)%Z) (Tint32) **
  (V293_storage_cell (b,(base+8)%Z) (Tptr Tint32) **
  (V293_storage_cell (b,(base+16)%Z) (Tint16) **
  (V293_storage_cell (b,(base+18)%Z) (Tint16) **
  (V293_storage_cell (b,(base+55)%Z) (Tint8) **
  (V293_storage_cell (b,(base+52)%Z) (Tint8) **
  (V293_storage_cell (b,(base+51)%Z) (Tint8) **
  (V293_storage_cell (b,(base+54)%Z) (Tint8) **
  (V293_storage_cell (b,(base+53)%Z) (Tint8) **
  (V293_storage_cell (b,(base+28)%Z) (Tcom_ptr 411%Z) **
  (V293_storage_cell (b,(base+36)%Z) (Tcom_ptr 412%Z) **
  (V293_storage_cell (b,(base+32)%Z) (Tptr Tvoid) ** (V293_tcb_allocated_spares b base)))))))))))))))))))in H.
 unfold V293_storage_cell in H. sep normal in H.
 destruct H as (v0&v1&v2&v3&v4&v5&v6&v7&v8&v9&v10&v11&v12&v13&v14&v15&v16&v17&H).
 exists(fun z => match z with
 | 0%Z=>v0
 | 50%Z=>v1
 | 48%Z=>v2
 | 49%Z=>v3
 | 44%Z=>v4
 | 4%Z=>v5
 | 12%Z=>v6
 | 8%Z=>v7
 | 16%Z=>v8
 | 18%Z=>v9
 | 55%Z=>v10
 | 52%Z=>v11
 | 51%Z=>v12
 | 54%Z=>v13
 | 53%Z=>v14
 | 28%Z=>v15
 | 36%Z=>v16
 | 32%Z=>v17
 | _=>Vundef end).
 cbn[V293_tcb_init_old_fields V293_rdy_raw_cells]. clear -H. sep auto.
Qed.

Definition V293_tcb_allocated_inputs bp bprio bs bb bi bz be bo p top bottom identity size ext options R :=
 V293_rdy_raw_cells
 ([((bprio,0%Z),Tint8,V293_byteval p);((bs,0%Z),Tptr Tint32,top);
 ((bb,0%Z),Tptr Tint32,bottom);((bi,0%Z),Tint16,identity);
 ((bz,0%Z),Tint32,size);((be,0%Z),Tptr Tvoid,ext);((bo,0%Z),Tint16,options)])
 (V293_tcb_fields_bindings 108%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z
 bp bprio bs bb bi bz be bo ** R).
Definition V293_tcb_allocated_remainder b off next :=
 V293_tcb_allocated_spares b(Int.unsigned off) **
 Amapsto(b,(Int.unsigned off+20)%Z)(Tcom_ptr 410%Z)true next.
Definition V293_tcb_allocated_initialized b off next p top bottom identity size ext options :=
 V293_rdy_raw_cells(V293_tcb_init_final_fields b(Int.unsigned off)p top bottom identity size ext options)
 (V293_tcb_allocated_remainder b off next).

(* No shared-head cell in this frame: it has already returned to Inv. *)
Definition V293_tcb_allocated_field_frame bf bp bc b off cpu next R ir si ci :=
 OS[ir,true,si,ci] ** V293_tcb_empty_bindings bf bp bc **
 Amapsto(bc,0%Z)Tint32 true cpu ** (V293_tcb_allocated_remainder b off next ** R).
Lemma V293_tcb_allocated_field_frame_linv : forall bf bp bc b off cpu next R ir si ci li tid,
 (R ==> CurLINV li tid) -> V293_tcb_allocated_field_frame bf bp bc b off cpu next R ir si ci ==> CurLINV li tid.
Proof.
 intros bf bp bc b off cpu next R ir si ci li tid HR.
 unfold V293_tcb_allocated_field_frame.
 repeat apply V293_star_CurLINV_r. exact HR.
Qed.

Lemma V293_tcb_allocated_fields_prepare : forall bf bp bc b off cpu next
 bprio bs bb bi bz be bo p top bottom identity size ext options R aop ir si ci,
 V293_tcb_enabled_state bf bp bc(Vptr(b,off))cpu
 (V293_tcb_free_node b off next **
  V293_tcb_allocated_inputs bp bprio bs bb bi bz be bo p top bottom identity size ext options R)aop ir si ci ==>
 EX old:Z->val,<||aop||> ** V293_rdy_raw_cells
 (V293_tcb_init_old_fields b(Int.unsigned off)old ++
  V293_tcb_init_input_cells bp bprio bs bb bi bz be bo b(Int.unsigned off)p top bottom identity size ext options)
 (V293_tcb_fields_bindings 108%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z bp bprio bs bb bi bz be bo **
  V293_tcb_allocated_field_frame bf bp bc b off cpu next R ir si ci).
Proof.
 intros bf bp bc b off cpu next bprio bs bb bi bz be bo p top bottom identity size ext options R aop ir si ci s H.
 assert(B:s |= V293_tcb_free_payload b(Int.unsigned off) **
 (<||aop||> ** OS[ir,true,si,ci] ** V293_tcb_enabled_resources bf bp bc(Vptr(b,off))cpu
 (Amapsto(b,(Int.unsigned off+20)%Z)(Tcom_ptr 410%Z)true next **
  V293_tcb_allocated_inputs bp bprio bs bb bi bz be bo p top bottom identity size ext options R))).
 { unfold V293_tcb_enabled_state,V293_tcb_enabled_resources,V293_tcb_free_node in *;clear -H;sep auto. }
 eapply astar_mono in B;[ |apply V293_tcb_allocated_payload_open|intros st HS;exact HS].
 sep normal in B. sep destruct B. exists x.
 unfold V293_tcb_enabled_resources,V293_tcb_allocated_field_frame,V293_tcb_allocated_remainder,
 V293_tcb_allocated_inputs in *.
 cbn[V293_tcb_init_old_fields V293_tcb_init_input_cells V293_rdy_raw_cells app]in B|-*.
 rewrite Int.repr_unsigned. clear -B;sep auto.
Qed.

Lemma V293_tcb_allocated_fields_finish : forall bf bp bc b off cpu next
 bprio bs bb bi bz be bo p top bottom identity size ext options R aop ir si ci,
 <||aop||> ** V293_rdy_raw_cells
 (V293_tcb_init_final_fields b(Int.unsigned off)p top bottom identity size ext options ++
  V293_tcb_init_input_cells bp bprio bs bb bi bz be bo b(Int.unsigned off)p top bottom identity size ext options)
 (V293_tcb_fields_bindings 108%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z bp bprio bs bb bi bz be bo **
  V293_tcb_allocated_field_frame bf bp bc b off cpu next R ir si ci) ==>
 V293_tcb_enabled_state bf bp bc(Vptr(b,off))cpu
 (V293_tcb_allocated_initialized b off next p top bottom identity size ext options **
  V293_tcb_allocated_inputs bp bprio bs bb bi bz be bo p top bottom identity size ext options R)aop ir si ci.
Proof.
 intros bf bp bc b off cpu next bprio bs bb bi bz be bo p top bottom identity size ext options R aop ir si ci s H.
 unfold V293_tcb_enabled_state,V293_tcb_enabled_resources,V293_tcb_allocated_field_frame,
 V293_tcb_allocated_initialized,V293_tcb_allocated_inputs in *.
 cbn[V293_tcb_init_final_fields V293_tcb_init_input_cells V293_rdy_raw_cells app]in H|-*.
 rewrite Int.repr_unsigned in H. clear -H;sep auto.
Qed.

Lemma V293_tcb_allocated_fields : forall Spec sd li I r ri tid
 bf bp bc b off cpu next bprio bs bb bi bz be bo p top bottom identity size ext options R aop ir si ci,
 p<13 -> (Int.unsigned off+55<=Int.max_unsigned)%Z ->
 V293_tcb_init_values_valid top bottom identity size ext options -> (R ==> CurLINV li tid) ->
 InfRules Spec sd li I r ri
 (V293_tcb_enabled_state bf bp bc(Vptr(b,off))cpu
 (V293_tcb_free_node b off next **
  V293_tcb_allocated_inputs bp bprio bs bb bi bz be bo p top bottom identity size ext options R)aop ir si ci)
 (V293_TCBInit_fields 108%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z)
 (V293_tcb_enabled_state bf bp bc(Vptr(b,off))cpu
 (V293_tcb_allocated_initialized b off next p top bottom identity size ext options **
  V293_tcb_allocated_inputs bp bprio bs bb bi bz be bo p top bottom identity size ext options R)aop ir si ci)tid.
Proof.
 intros Spec sd li I r ri tid bf bp bc b off cpu next bprio bs bb bi bz be bo p top bottom identity size ext options R aop ir si ci Range Bound Valid HR.
 eapply conseq_rule;[apply V293_tcb_allocated_fields_prepare|intros s H;exact H| ].
 apply ex_intro_rule. intro old.
 eapply conseq_rule;[intros s H;exact H|apply V293_tcb_allocated_fields_finish| ].
 apply V293_OS_TCBInit_fields_hoare;try assumption.
 - pose proof(Int.unsigned_range off);lia.
 - apply V293_tcb_allocated_field_frame_linv;exact HR.
Qed.

Lemma V293_tcb_allocated_inputs_good : forall bp bprio bs bb bi bz be bo p top bottom identity size ext options R,
 GoodFrm R -> GoodFrm(V293_tcb_allocated_inputs bp bprio bs bb bi bz be bo p top bottom identity size ext options R).
Proof.
 intros bp bprio bs bb bi bz be bo p top bottom identity size ext options R Frame.
 cbn[V293_tcb_allocated_inputs V293_rdy_raw_cells V293_tcb_fields_bindings GoodFrm]. tauto.
Qed.
Lemma V293_tcb_allocated_inputs_linv : forall bp bprio bs bb bi bz be bo p top bottom identity size ext options R li tid,
 (R ==> CurLINV li tid) ->
 V293_tcb_allocated_inputs bp bprio bs bb bi bz be bo p top bottom identity size ext options R ==> CurLINV li tid.
Proof.
 intros bp bprio bs bb bi bz be bo p top bottom identity size ext options R li tid HR.
 unfold V293_tcb_allocated_inputs. apply V293_raw_cells_CurLINV.
 apply V293_star_CurLINV_r;exact HR.
Qed.

(* Closed original right-associated pop; exit; eighteen stores. No success
   continuation, old-field snapshot, load oracle, or initialized node premise. *)
Lemma V293_tcb_free_pop_fields : forall Spec sd li I r ri tid
 bf bp bc b off cpu K bprio bs bb bi bz be bo p top bottom identity size ext options R aop ir si ci,
 p<13 -> GoodFrm R -> V293_tcb_init_values_valid top bottom identity size ext options ->
 (R ==> CurLINV li tid) ->
 (Aisr ir ** (V293_tcb_free_pool bf ** K) ==> Aisr ir ** invlth_isr I 0(gettopis si)) ->
 InfRules Spec sd li I r ri
 (V293_tcb_free_critical bf bp bc(Vptr(b,off))cpu(Vptr(b,off))K
 (V293_tcb_allocated_inputs bp bprio bs bb bi bz be bo p top bottom identity size ext options R)aop ir si(true::ci))
 (sseq(V293_TCBInit_pop 91%Z 108%Z)(sseq(sprim excrit)
 (V293_TCBInit_fields 108%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z)))
 (EX next:val,[|(Int.unsigned off+55<=Int.max_unsigned)%Z /\ rule_type_val_match(Tcom_ptr 410%Z)next=true|] **
 V293_tcb_enabled_state bf bp bc(Vptr(b,off))cpu
 (V293_tcb_allocated_initialized b off next p top bottom identity size ext options **
  V293_tcb_allocated_inputs bp bprio bs bb bi bz be bo p top bottom identity size ext options R)aop ir si ci)tid.
Proof.
 intros Spec sd li I r ri tid bf bp bc b off cpu K bprio bs bb bi bz be bo p top bottom identity size ext options R aop ir si ci Range Frame Valid HR Close.
 assert(F:GoodFrm(V293_tcb_allocated_inputs bp bprio bs bb bi bz be bo p top bottom identity size ext options R))
 by(apply V293_tcb_allocated_inputs_good;exact Frame).
 assert(L:V293_tcb_allocated_inputs bp bprio bs bb bi bz be bo p top bottom identity size ext options R ==> CurLINV li tid)
 by(apply V293_tcb_allocated_inputs_linv;exact HR).
 eapply conseq_rule with
 (p:=EX next:val,V293_tcb_free_pop_state bf bp bc b off cpu(Vptr(b,off))next K
 (V293_tcb_allocated_inputs bp bprio bs bb bi bz be bo p top bottom identity size ext options R)aop ir si(true::ci) **
 [|(Int.unsigned off+55<=Int.max_unsigned)%Z /\ rule_type_val_match(Tcom_ptr 410%Z)next=true|]).
 - intros s H. unfold V293_tcb_free_critical,V293_tcb_enabled_resources in H.
   cbn[V293_tcb_free_chain]in H. sep normal in H. sep destruct H.
   unfold V293_tcb_free_pop_state,V293_tcb_enabled_resources,V293_tcb_free_node. clear -H;sep auto.
 - intros s H;exact H.
 - apply ex_intro_rule. intro next. apply pure_split_rule. intros[Bound Typed].
   eapply seq_rule;[apply V293_tcb_free_pop;assumption| ].
   eapply seq_rule;[apply V293_tcb_free_exit;assumption| ].
   eapply conseq_rule;[intros s H;exact H| |apply V293_tcb_allocated_fields;assumption].
   intros s H. exists next. apply astar_l_apure_intro;[exact H|auto].
Qed.
Print Assumptions V293_tcb_free_pop_fields.

(* Whole original body interface: the remaining premise starts at the Hook,
   AFTER all eighteen field writes, and cannot be called success0 or WFIFun. *)
Theorem V293_OS_TCBInit_free_body_after_fields : forall Spec sd li I r tid hi hc
 bf bp bc pc cpu K bprio bs bb bi bz be bo p top bottom identity size ext options R aop ir si ci,
 p<13 -> (gettopis si<=INUM)%nat -> GoodFrm R ->
 V293_tcb_init_values_valid top bottom identity size ext options -> (R ==> CurLINV li tid) ->
 (Aisr ir ** invlth_isr I 0(gettopis si) ==> Aisr ir ** (V293_tcb_free_pool bf ** K)) ->
 (Aisr ir ** (V293_tcb_free_pool bf ** K) ==> Aisr ir ** invlth_isr I 0(gettopis si)) ->
 (V293_tcb_enabled_state bf bp bc Vnull(Vint32 Int.zero)
  (V293_tcb_allocated_inputs bp bprio bs bb bi bz be bo p top bottom identity size ext options R)aop ir si ci ==>
  r(Some(Vint32(Int.repr 66)))) ->
 (forall b off next,(Int.unsigned off+55<=Int.max_unsigned)%Z -> rule_type_val_match(Tcom_ptr 410%Z)next=true ->
 InfRules Spec sd li I r Afalse
 (V293_tcb_enabled_state bf bp bc(Vptr(b,off))(Vint32 Int.zero)
 (V293_tcb_allocated_initialized b off next p top bottom identity size ext options **
  V293_tcb_allocated_inputs bp bprio bs bb bi bz be bo p top bottom identity size ext options R)aop ir si ci)
 (V293_TCBInit_success_suffix hi hc)Afalse tid) ->
 InfRules Spec sd li I r Afalse
 (V293_tcb_enabled_state bf bp bc pc cpu
 (V293_tcb_allocated_inputs bp bprio bs bb bi bz be bo p top bottom identity size ext options R)aop ir si ci)
 (V293_TCBInit_function_body hi hc)Afalse tid.
Proof.
 intros Spec sd li I r tid hi hc bf bp bc pc cpu K bprio bs bb bi bz be bo p top bottom identity size ext options R aop ir si ci Range Bound Frame Valid HR Open Close Empty Success.
 apply V293_OS_TCBInit_free_body_with_success with(K:=K);try assumption.
 - apply V293_tcb_allocated_inputs_good;exact Frame.
 - apply V293_tcb_allocated_inputs_linv;exact HR.
 - intros b off next B T. eapply seq_rule;[apply V293_tcb_allocated_fields;assumption|apply Success;assumption].
Qed.
Print Assumptions V293_OS_TCBInit_free_body_after_fields.
