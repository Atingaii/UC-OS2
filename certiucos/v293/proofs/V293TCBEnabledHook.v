(* Real first CPU Hook on the allocated private node, with IE=true.
   The typed external contract preserves that node; no Hook body is assumed
   proved, and neither shared-head bytes nor caller locals enter the callee. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.certiucos.v293.proofs.V293TCBAllocatedFields.
Require Import CertiOS.certiucos.v293.proofs.V293TCBHookCall.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFreePool.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFieldsHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEmptyEnabled.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEmptyHoare.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitFunction.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitPrefix.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInit.
Require Import CertiOS.certiucos.v293.code.V293OSTCBPublish.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition V293_tcb_enabled_hook_resource b off next p top bottom identity size ext options R aop ir si ci :=
 <||aop||> ** OS[ir,true,si,ci] **
 (V293_tcb_allocated_initialized b off next p top bottom identity size ext options ** R).
Definition V293_tcb_enabled_hook_frame bf bp bc pc cpu bprio bs bb bi bz be bo p top bottom identity size ext options :=
 V293_tcb_enabled_resources bf bp bc pc cpu
 (V293_tcb_allocated_inputs bp bprio bs bb bi bz be bo p top bottom identity size ext options Aemp).
Lemma V293_tcb_enabled_hook_good : forall b off next p top bottom identity size ext options R aop ir si ci,
 GoodFunAsrt R -> GoodFunAsrt(V293_tcb_enabled_hook_resource b off next p top bottom identity size ext options R aop ir si ci).
Proof.
 intros. cbn[V293_tcb_enabled_hook_resource V293_tcb_allocated_initialized
 V293_tcb_init_final_fields V293_rdy_raw_cells V293_tcb_allocated_remainder
 V293_tcb_allocated_spares V293_storage V293_storage_cell GoodFunAsrt]. tauto.
Qed.
Lemma V293_tcb_enabled_hook_frame_good : forall bf bp bc pc cpu bprio bs bb bi bz be bo p top bottom identity size ext options,
 GoodFrm(V293_tcb_enabled_hook_frame bf bp bc pc cpu bprio bs bb bi bz be bo p top bottom identity size ext options).
Proof.
 intros. apply V293_tcb_enabled_good. apply V293_tcb_allocated_inputs_good. exact I.
Qed.
Lemma V293_tcb_enabled_hook_linv : forall b off next p top bottom identity size ext options R aop ir si ci li tid,
 (R ==> CurLINV li tid) ->
 V293_tcb_enabled_hook_resource b off next p top bottom identity size ext options R aop ir si ci ==> CurLINV li tid.
Proof.
 intros b off next p top bottom identity size ext options R aop ir si ci li tid HR.
 unfold V293_tcb_enabled_hook_resource. repeat apply V293_star_CurLINV_r. exact HR.
Qed.
Lemma V293_tcb_enabled_hook_view : forall bf bp bc pc cpu b off next bprio bs bb bi bz be bo p top bottom identity size ext options R aop ir si ci s,
 (s |= V293_tcb_enabled_state bf bp bc pc cpu
 (V293_tcb_allocated_initialized b off next p top bottom identity size ext options **
 V293_tcb_allocated_inputs bp bprio bs bb bi bz be bo p top bottom identity size ext options R)aop ir si ci) <->
 (s |= V293_tcb_enabled_hook_resource b off next p top bottom identity size ext options R aop ir si ci **
 V293_tcb_enabled_hook_frame bf bp bc pc cpu bprio bs bb bi bz be bo p top bottom identity size ext options).
Proof.
 intros. unfold V293_tcb_enabled_state,V293_tcb_enabled_hook_resource,
 V293_tcb_enabled_hook_frame,V293_tcb_enabled_resources,V293_tcb_allocated_inputs.
 cbn[V293_tcb_init_input_cells V293_rdy_raw_cells tl]. split;intro H;clear -H;sep auto.
Qed.
Lemma V293_tcb_enabled_hook_argument : forall bf bp bc b off cpu R aop ir si ci,
 V293_tcb_enabled_state bf bp bc(Vptr(b,off))cpu R aop ir si ci ==>
 Rvl [evar 108%Z] @ [Tptr V293_tcb_type] == [Vptr(b,off)].
Proof.
 intros bf bp bc b off cpu R aop ir si ci s H.
 assert(B:s |= V293_tcb_empty_bindings bf bp bc ** Atrue).
 { unfold V293_tcb_enabled_state,V293_tcb_enabled_resources in H;clear -H;sep auto. }
 destruct(V293_tcb_empty_env _ _ _ _ B)as[Env _].
 assert(Read:load(Tptr V293_tcb_type)(getmem s)(bp,0%Z)=Some(Vptr(b,off))).
 { eapply V293_star_load_r;[ |exact H]. intros st HS.
   unfold V293_tcb_enabled_resources in HS.
   eapply V293_star_load_r;[ |exact HS]. intros st1 H1.
   eapply V293_star_load_r;[ |exact H1]. intros st2 H2.
   eapply V293_star_load_l;[ |exact H2]. intros st3 H3.
   eapply mapstoval_load;[ |exact(proj1 H3)].
   reflexivity. }
 destruct s as [[[[[[ge le] M] irq] aux] O] op].
 change(get le 108%Z=Some(bp,Tptr V293_tcb_type))in Env.
 change(load(Tptr V293_tcb_type)M(bp,0%Z)=Some(Vptr(b,off)))in Read.
 cbn[sat getsmem evalexprlist evaltype evalval evaladdr get_smem get_lenv].
 cbv delta[env var memory.ident Modules.ident]in *. rewrite Env.
 repeat split;first[assumption|reflexivity|discriminate].
Qed.

(* A single finite Spec entry supports every physically allocated pointer.
   Pointer and Next are logical instantiations, not a different Spec per node. *)
Definition V293_tcb_enabled_hook_fpre p top bottom identity size ext options R aop ir si ci owner
 (good:GoodFunAsrt R) : fpre :=
 fun vl lg tid => match lg with
 | [logic_val(Vptr(b,off));logic_val next] =>
 V293_hook_fpre (Vptr(b,off)) owner
 (V293_tcb_enabled_hook_resource b off next p top bottom identity size ext options R aop ir si ci)
 (V293_tcb_enabled_hook_good b off next p top bottom identity size ext options R aop ir si ci good) vl [] tid
 | _ => @mkfunasrt Afalse I
 end.
Definition V293_tcb_enabled_hook_fpost p top bottom identity size ext options R aop ir si ci owner
 (good:GoodFunAsrt R) : fpost :=
 fun vl result lg tid => match lg with
 | [logic_val(Vptr(b,off));logic_val next] =>
 V293_hook_fpost (Vptr(b,off)) owner
 (V293_tcb_enabled_hook_resource b off next p top bottom identity size ext options R aop ir si ci)
 (V293_tcb_enabled_hook_good b off next p top bottom identity size ext options R aop ir si ci good) vl result [] tid
 | _ => @mkfunasrt Afalse I
 end.

Lemma V293_tcb_enabled_hook_call : forall Spec sd li I r ri tid f
 bf bp bc b off cpu next bprio bs bb bi bz be bo p top bottom identity size ext options R aop ir si ci
 (good:GoodFunAsrt R),
 (R ==> CurLINV li tid) ->
 Spec f=Some(V293_tcb_enabled_hook_fpre p top bottom identity size ext options R aop ir si ci tid good,
 V293_tcb_enabled_hook_fpost p top bottom identity size ext options R aop ir si ci tid good,
 (Tvoid,[Tptr V293_tcb_type])) ->
 InfRules Spec sd li I r ri
 (V293_tcb_enabled_state bf bp bc(Vptr(b,off))cpu
 (V293_tcb_allocated_initialized b off next p top bottom identity size ext options **
 V293_tcb_allocated_inputs bp bprio bs bb bi bz be bo p top bottom identity size ext options R)aop ir si ci)
 (scall f [evar 108%Z])
 (V293_tcb_enabled_state bf bp bc(Vptr(b,off))cpu
 (V293_tcb_allocated_initialized b off next p top bottom identity size ext options **
 V293_tcb_allocated_inputs bp bprio bs bb bi bz be bo p top bottom identity size ext options R)aop ir si ci)tid.
Proof.
 intros Spec sd li I r ri tid f bf bp bc b off cpu next bprio bs bb bi bz be bo p top bottom identity size ext options R aop ir si ci good HR Lookup.
 set(pre:=V293_tcb_enabled_hook_fpre p top bottom identity size ext options R aop ir si ci tid good).
 set(post:=V293_tcb_enabled_hook_fpost p top bottom identity size ext options R aop ir si ci tid good).
 set(frame:=V293_tcb_enabled_hook_frame bf bp bc(Vptr(b,off))cpu bprio bs bb bi bz be bo p top bottom identity size ext options).
 eapply conseq_rule with
 (q:=EX result:option val,getasrt(post ([Vptr(b,off)]) result ([logic_val(Vptr(b,off));logic_val next]) tid) ** frame).
 - intros s H;exact H.
 - intros s[result H]. apply V293_tcb_enabled_hook_view.
   cbn[post V293_tcb_enabled_hook_fpost V293_hook_fpost getasrt]in H.
   unfold frame in H. clear -H;sep auto.
 - eapply call_rule with(pre:=pre)(post:=post)(vl:=[Vptr(b,off)])
   (logicl:=[logic_val(Vptr(b,off));logic_val next])(tp:=Tvoid)(tl:=[Tptr V293_tcb_type])(p:=frame).
   + apply V293_tcb_enabled_hook_frame_good.
   + exact Lookup.
   + intros s H. apply V293_tcb_enabled_hook_view in H.
     cbn[pre V293_tcb_enabled_hook_fpre V293_hook_fpre getasrt]. unfold frame. clear -H;sep auto.
   + apply V293_tcb_enabled_hook_argument.
   + reflexivity.
   + cbn[pre V293_tcb_enabled_hook_fpre V293_hook_fpre getasrt].
     apply V293_star_CurLINV_r. apply V293_tcb_enabled_hook_linv;exact HR.
   + intros s[result H]. cbn[post V293_tcb_enabled_hook_fpost V293_hook_fpost getasrt]in H.
     eapply V293_star_CurLINV_r;[apply V293_tcb_enabled_hook_linv;exact HR|exact H].
Qed.

Lemma V293_tcb_allocated_fields_first_hook : forall Spec sd li I r ri tid f
 bf bp bc b off cpu next bprio bs bb bi bz be bo p top bottom identity size ext options R aop ir si ci
 (good:GoodFunAsrt R),
 p<13 -> (Int.unsigned off+55<=Int.max_unsigned)%Z ->
 V293_tcb_init_values_valid top bottom identity size ext options -> (R ==> CurLINV li tid) ->
 Spec f=Some(V293_tcb_enabled_hook_fpre p top bottom identity size ext options R aop ir si ci tid good,
 V293_tcb_enabled_hook_fpost p top bottom identity size ext options R aop ir si ci tid good,
 (Tvoid,[Tptr V293_tcb_type])) ->
 InfRules Spec sd li I r ri
 (V293_tcb_enabled_state bf bp bc(Vptr(b,off))cpu
 (V293_tcb_free_node b off next **
 V293_tcb_allocated_inputs bp bprio bs bb bi bz be bo p top bottom identity size ext options R)aop ir si ci)
 (sseq(V293_TCBInit_fields 108%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z)(scall f[evar 108%Z]))
 (V293_tcb_enabled_state bf bp bc(Vptr(b,off))cpu
 (V293_tcb_allocated_initialized b off next p top bottom identity size ext options **
 V293_tcb_allocated_inputs bp bprio bs bb bi bz be bo p top bottom identity size ext options R)aop ir si ci)tid.
Proof.
 intros. eapply seq_rule;[apply V293_tcb_allocated_fields;assumption| ].
 apply V293_tcb_enabled_hook_call with(good:=good);assumption.
Qed.
Print Assumptions V293_tcb_allocated_fields_first_hook.

(* One stable original-body interface. Only the continuation AFTER the real
   first Hook remains a Hoare premise. The same typed Spec handles all nodes. *)
Theorem V293_OS_TCBInit_free_body_after_first_hook : forall Spec sd li I r tid hi hc
 bf bp bc pc cpu K bprio bs bb bi bz be bo p top bottom identity size ext options R aop ir si ci
 (good:GoodFunAsrt R),
 p<13 -> (gettopis si<=INUM)%nat -> GoodFrm R ->
 V293_tcb_init_values_valid top bottom identity size ext options -> (R ==> CurLINV li tid) ->
 (Aisr ir ** invlth_isr I 0(gettopis si) ==> Aisr ir ** (V293_tcb_free_pool bf ** K)) ->
 (Aisr ir ** (V293_tcb_free_pool bf ** K) ==> Aisr ir ** invlth_isr I 0(gettopis si)) ->
 Spec hi=Some(V293_tcb_enabled_hook_fpre p top bottom identity size ext options R aop ir si ci tid good,
 V293_tcb_enabled_hook_fpost p top bottom identity size ext options R aop ir si ci tid good,
 (Tvoid,[Tptr V293_tcb_type])) ->
 (V293_tcb_enabled_state bf bp bc Vnull(Vint32 Int.zero)
 (V293_tcb_allocated_inputs bp bprio bs bb bi bz be bo p top bottom identity size ext options R)aop ir si ci ==>
 r(Some(Vint32(Int.repr 66)))) ->
 (forall b off next,(Int.unsigned off+55<=Int.max_unsigned)%Z -> rule_type_val_match(Tcom_ptr 410%Z)next=true ->
 InfRules Spec sd li I r Afalse
 (V293_tcb_enabled_state bf bp bc(Vptr(b,off))(Vint32 Int.zero)
 (V293_tcb_allocated_initialized b off next p top bottom identity size ext options **
 V293_tcb_allocated_inputs bp bprio bs bb bi bz be bo p top bottom identity size ext options R)aop ir si ci)
 (sseq(sprim encrit)
 (sseq(sassign(earrayelem(evar 92%Z)(evar 101%Z))(evar 108%Z))
 (sseq(sprim excrit)(sseq(scall hc[evar 108%Z])(V293_TCB_publish 108%Z 93%Z 94%Z 95%Z 96%Z)))))Afalse tid) ->
 InfRules Spec sd li I r Afalse
 (V293_tcb_enabled_state bf bp bc pc cpu
 (V293_tcb_allocated_inputs bp bprio bs bb bi bz be bo p top bottom identity size ext options R)aop ir si ci)
 (V293_TCBInit_function_body hi hc)Afalse tid.
Proof.
 intros Spec sd li I r tid hi hc bf bp bc pc cpu K bprio bs bb bi bz be bo p top bottom identity size ext options R aop ir si ci good Range Bound Frame Valid HR Open Close Lookup Empty Rest.
 apply V293_OS_TCBInit_free_body_after_fields with(K:=K);try assumption.
 intros b off next B T. unfold V293_TCBInit_success_suffix. eapply seq_rule.
 - apply V293_tcb_enabled_hook_call with(good:=good);assumption.
 - apply Rest;assumption.
Qed.
Print Assumptions V293_OS_TCBInit_free_body_after_first_hook.
