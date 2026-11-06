(* Connect the actual second CPU Hook after the reservation share was consumed.
   This is not a Hook implementation or a production allocator invariant. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFullPriority.
Require Import CertiOS.certiucos.v293.proofs.V293TCBOwnedPriority.
Require Import CertiOS.certiucos.v293.proofs.V293TCBAllocatedFields.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFieldsHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEmptyEnabled.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEmptyHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFreePool.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEnabledHook.
Require Import CertiOS.certiucos.v293.proofs.V293TCBHookCall.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateReservationOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPriorityHoare.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitFunction.
Require Import CertiOS.certiucos.v293.code.V293OSTCBPublish.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Lemma V293_tcb_second_hook : forall Spec sd li I r ri tid f table
 bf bp bc b off cpu next bprio bs bb bi bz be bo p top bottom identity size ext options R aop ir si ci
 (good:GoodFunAsrt R),
 (R ==> CurLINV li tid) ->
 Spec f=Some(V293_tcb_enabled_hook_fpre p top bottom identity size ext options R aop ir si ci tid good,
 V293_tcb_enabled_hook_fpost p top bottom identity size ext options R aop ir si ci tid good,
 (Tvoid,[Tptr V293_tcb_type])) ->
 InfRules Spec sd li I r ri
 (V293_tcb_enabled_state bf bp bc(Vptr(b,off))cpu
 (V293_tcb_allocated_initialized b off next p top bottom identity size ext options **
 V293_tcb_allocated_inputs bp bprio bs bb bi bz be bo p top bottom identity size ext options
 (V293_tcb_table_binding table ** R))aop ir si ci)
 (scall f[evar 108%Z])
 (V293_tcb_enabled_state bf bp bc(Vptr(b,off))cpu
 (V293_tcb_allocated_initialized b off next p top bottom identity size ext options **
 V293_tcb_allocated_inputs bp bprio bs bb bi bz be bo p top bottom identity size ext options
 (V293_tcb_table_binding table ** R))aop ir si ci)tid.
Proof.
 intros Spec sd li I r ri tid f table bf bp bc b off cpu next bprio bs bb bi bz be bo p top bottom identity size ext options R aop ir si ci good HR Lookup.
 eapply conseq_rule with
 (p:=V293_tcb_priority_state table bprio bp p(Vptr(b,off))
 (V293_tcb_allocated_initialized b off next p top bottom identity size ext options **
 (R ** V293_tcb_priority_caller_frame bf bp bc bprio bs bb bi bz be bo cpu top bottom identity size ext options))aop ir true si ci)
 (q:=V293_tcb_priority_state table bprio bp p(Vptr(b,off))
 (V293_tcb_allocated_initialized b off next p top bottom identity size ext options **
 (R ** V293_tcb_priority_caller_frame bf bp bc bprio bs bb bi bz be bo cpu top bottom identity size ext options))aop ir true si ci).
 - apply V293_tcb_full_priority_view.
 - apply V293_tcb_full_priority_restore.
 - apply V293_tcb_priority_first_hook with(good:=good);
   [apply V293_tcb_priority_caller_frame_good|exact HR|exact Lookup].
Qed.

(* Both calls are real typed scall nodes; only publication remains a Hoare
   premise. Freshness, pool open/close, and both Hook bodies remain obligations. *)
Theorem V293_OS_TCBInit_free_body_after_second_hook : forall Spec sd li I r tid hi hc
 table reserved bf bp bc pc cpu Kfree Kprio bprio bs bb bi bz be bo p top bottom identity size ext options R aop ir si ci
 (good:GoodFunAsrt(V293_create_owned_share table reserved p ** R)),
 p<13 -> (gettopis si<=INUM)%nat -> GoodFrm R ->
 V293_tcb_init_values_valid top bottom identity size ext options -> (R ==> CurLINV li tid) ->
 (Aisr ir ** invlth_isr I 0(gettopis si) ==> Aisr ir ** (V293_tcb_free_pool bf ** Kfree)) ->
 (Aisr ir ** (V293_tcb_free_pool bf ** Kfree) ==> Aisr ir ** invlth_isr I 0(gettopis si)) ->
 (Aisr ir ** invlth_isr I 0(gettopis si) ==> Aisr ir ** V293_create_owned_pool table reserved p Kprio) ->
 (Aisr ir ** V293_create_owned_pool table reserved p Kprio ==> Aisr ir ** invlth_isr I 0(gettopis si)) ->
 Spec hi=Some(V293_tcb_enabled_hook_fpre p top bottom identity size ext options
 (V293_create_owned_share table reserved p ** R)aop ir si ci tid good,
 V293_tcb_enabled_hook_fpost p top bottom identity size ext options
 (V293_create_owned_share table reserved p ** R)aop ir si ci tid good,(Tvoid,[Tptr V293_tcb_type])) ->
 Spec hc=Some(V293_tcb_enabled_hook_fpre p top bottom identity size ext options R aop ir si ci tid (proj2 good),
 V293_tcb_enabled_hook_fpost p top bottom identity size ext options R aop ir si ci tid (proj2 good),(Tvoid,[Tptr V293_tcb_type])) ->
 (V293_tcb_enabled_state bf bp bc Vnull(Vint32 Int.zero)
 (V293_tcb_allocated_inputs bp bprio bs bb bi bz be bo p top bottom identity size ext options
 (V293_tcb_table_binding table ** (V293_create_owned_share table reserved p ** R)))aop ir si ci ==>
 r(Some(Vint32(Int.repr 66)))) ->
 (forall b off next s,
 s |= V293_tcb_enabled_state bf bp bc(Vptr(b,off))(Vint32 Int.zero)
 (V293_tcb_allocated_initialized b off next p top bottom identity size ext options **
 V293_tcb_allocated_inputs bp bprio bs bb bi bz be bo p top bottom identity size ext options
 (V293_tcb_table_binding table ** (V293_create_owned_share table reserved p ** R)))aop ir si ci ->
 (b,off)<>reserved) ->
 (forall b off next,(Int.unsigned off+55<=Int.max_unsigned)%Z -> rule_type_val_match(Tcom_ptr 410%Z)next=true ->
 InfRules Spec sd li I r Afalse
 (V293_tcb_enabled_state bf bp bc(Vptr(b,off))(Vint32 Int.zero)
 (V293_tcb_allocated_initialized b off next p top bottom identity size ext options **
 V293_tcb_allocated_inputs bp bprio bs bb bi bz be bo p top bottom identity size ext options
 (V293_tcb_table_binding table ** R))aop ir si ci)
 (V293_TCB_publish 108%Z 93%Z 94%Z 95%Z 96%Z)Afalse tid) ->
 InfRules Spec sd li I r Afalse
 (V293_tcb_enabled_state bf bp bc pc cpu
 (V293_tcb_allocated_inputs bp bprio bs bb bi bz be bo p top bottom identity size ext options
 (V293_tcb_table_binding table ** (V293_create_owned_share table reserved p ** R)))aop ir si ci)
 (V293_TCBInit_function_body hi hc)Afalse tid.
Proof.
 intros Spec sd li I r tid hi hc table reserved bf bp bc pc cpu Kfree Kprio bprio bs bb bi bz be bo p top bottom identity size ext options R aop ir si ci good Range Bound Frame Valid HR FreeOpen FreeClose PriorityOpen PriorityClose FirstLookup SecondLookup Empty Fresh Publish.
 apply V293_OS_TCBInit_free_body_after_owned_priority with(reserved:=reserved)(Kfree:=Kfree)(Kprio:=Kprio)(good:=good);try assumption.
 intros b off next NodeBound NextTyped. eapply seq_rule.
 - apply V293_tcb_second_hook with(good:=proj2 good);assumption.
 - apply Publish;assumption.
Qed.
Print Assumptions V293_OS_TCBInit_free_body_after_second_hook.
