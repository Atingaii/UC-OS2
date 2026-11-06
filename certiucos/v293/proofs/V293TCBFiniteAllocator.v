Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPublicationPool.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPublishHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPublish.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEnabledHook.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateReservationOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPriorityHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEnabledPublication.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFreePool.
Require Import CertiOS.certiucos.v293.proofs.V293TCBAllocatedFields.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFullPriority.
Require Import CertiOS.certiucos.v293.proofs.V293TCBSecondHook.
Require Import CertiOS.certiucos.v293.proofs.V293TCBOwnedPriority.
(* Real bounded free-chain storage. A node leaves the shared pool on pop;
   no free-head or node snapshot is supplied by the enabled caller. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStoragePrefix.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEmptyEnabled.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEmptyHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.
Require Import CertiOS.certiucos.v293.proofs.V293TCBSuccessHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInit.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitFunction.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitPrefix.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Require Import CertiOS.certiucos.v293.proofs.V293TCBFiniteSites.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFiniteEnabled.

(* Only the missing allocator fact is added: each real free node belongs to
   the fixed TCB table. No duplicate ownership or new allocator operation. *)
Fixpoint V293_tcb_site_free_chain (sites:list (block*int32))(fuel:nat)(head:val) : asrt :=
 match head with
 | Vnull=>Aemp
 | Vptr(b,offset)=>match fuel with
   | O=>Afalse
   | S n=>[|(Int.unsigned offset+55<=Int.max_unsigned)%Z /\ In(b,offset)sites|] **
     (V293_tcb_free_payload b(Int.unsigned offset) **
      (EX next:val,[|rule_type_val_match(Tcom_ptr 410%Z)next=true|] **
       (Amapsto(b,(Int.unsigned offset+20)%Z)(Tcom_ptr 410%Z)true next **
        V293_tcb_site_free_chain sites n next)))
   end
 | _=>Afalse
 end.
Definition V293_tcb_site_free_pool tcbtable bf :=
 EX head:val,[|rule_type_val_match(Tptr V293_tcb_type)head=true|] **
 (Amapsto(bf,0%Z)(Tptr V293_tcb_type)true head **
 V293_tcb_site_free_chain(V293_tcb_table_sites tcbtable)13 head).

Lemma V293_tcb_site_free_forget : forall sites n head,
 V293_tcb_site_free_chain sites n head ==> V293_tcb_free_chain n head.
Proof.
 intros sites n;induction n as[ |n IH];intro head;destruct head;try destruct a;
 intros s H;cbn[V293_tcb_site_free_chain V293_tcb_free_chain]in H|-*;try contradiction;try exact H.
 apply astar_l_apure_elim in H. destruct H as[[Bound Member]H].
 apply astar_l_apure_intro;[ |exact Bound].
 eapply astar_mono;[intros st HS;exact HS| |exact H].
 intros st[next HS]. exists next. eapply astar_mono;[intros st' H';exact H'| |exact HS].
 apply astar_mono;[intros st' H';exact H'|apply IH].
Qed.
Lemma V293_tcb_site_free_pool_forget : forall tcbtable bf,
 V293_tcb_site_free_pool tcbtable bf ==> V293_tcb_free_pool bf.
Proof.
 intros tcbtable bf s[head H]. exists head.
 eapply astar_mono;[intros st HS;exact HS| |exact H].
 apply astar_mono;[intros st HS;exact HS|apply V293_tcb_site_free_forget].
Qed.
Lemma V293_tcb_site_free_weaken : forall sites n v,
 V293_tcb_site_free_chain sites n v ==> V293_tcb_site_free_chain sites(S n)v.
Proof.
 intros sites n;induction n as[ |n IH];intro v;destruct v;try destruct a;intros s H;cbn[V293_tcb_site_free_chain]in H|-*;try contradiction;try exact H.
 eapply astar_mono;[intros st HS;exact HS| |exact H].
 apply astar_mono;[intros st HS;exact HS| ].
 intros st[next HS]. exists next.
 eapply astar_mono;[intros st' H';exact H'| |exact HS].
 apply astar_mono;[intros st' H';exact H'|apply IH].
Qed.

Definition V293_tcb_site_free_critical tcbtable bf bp bc pc cpu head K R aop ir si ci :=
 <||aop||> ** OS[ir,false,si,ci] **
 V293_tcb_enabled_resources bf bp bc pc cpu
 (Amapsto(bf,0%Z)(Tptr V293_tcb_type)true head **
 (V293_tcb_site_free_chain(V293_tcb_table_sites tcbtable)13 head ** (K ** R))).
Lemma V293_tcb_site_free_critical_forget : forall tcbtable bf bp bc pc cpu head K R aop ir si ci,
 V293_tcb_site_free_critical tcbtable bf bp bc pc cpu head K R aop ir si ci ==>
 V293_tcb_free_critical bf bp bc pc cpu head K R aop ir si ci.
Proof.
 intros tcbtable bf bp bc pc cpu head K R aop ir si ci.
 unfold V293_tcb_site_free_critical,V293_tcb_free_critical,V293_tcb_enabled_resources.
 do 6 (apply astar_mono;[intros st HS;exact HS| ]).
 apply astar_mono;[apply V293_tcb_site_free_forget|intros st HS;exact HS].
Qed.
Lemma V293_tcb_site_free_enter : forall Spec sd li I r ri tid tcbtable bf bp bc pc cpu K R aop ir si ci,
 (gettopis si<=INUM)%nat -> GoodFrm R ->
 (Aisr ir ** invlth_isr I 0(gettopis si) ==> Aisr ir ** (V293_tcb_site_free_pool tcbtable bf ** K)) ->
 InfRules Spec sd li I r ri
 (V293_tcb_enabled_state bf bp bc pc cpu R aop ir si ci)(sprim encrit)
 (EX head:val,[|rule_type_val_match(Tptr V293_tcb_type)head=true|] **
 V293_tcb_site_free_critical tcbtable bf bp bc pc cpu head K R aop ir si(true::ci))tid.
Proof.
 intros Spec sd li I r ri tid tcbtable bf bp bc pc cpu K R aop ir si ci Bound Frame Open.
 unfold V293_tcb_enabled_state. eapply conseq_rule with
 (p:=<||aop||> ** OS[ir,true,si,ci] ** ATopis(gettopis si) ** [|(gettopis si<=INUM)%nat|] **
 V293_tcb_enabled_resources bf bp bc pc cpu R)
 (q:=<||aop||> ** OS[ir,false,si,true::ci] ** invlth_isr I 0(gettopis si) **
 V293_tcb_enabled_resources bf bp bc pc cpu R).
 - intros s H. assert(S:s |= Ais si ** Atrue)by(clear -H;sep auto).
   pose proof(V293_time_topis si Atrue s S)as Top.
   apply astar_l_atopis_elim in Top. destruct Top as[Top _].
   pose proof(@astar_l_atopis_intro s(gettopis si)_ H Top)as HT.
   clear -HT Bound;sep auto.
 - intros s H.
   assert(B:s |= (Aisr ir ** invlth_isr I 0(gettopis si)) **
    (<||aop||> ** Aie false ** Ais si ** Acs(true::ci) ** V293_tcb_enabled_resources bf bp bc pc cpu R))by(clear -H;sep auto).
   eapply astar_mono in B;[ |exact Open|intros st HS;exact HS].
   unfold V293_tcb_site_free_pool in B. sep normal in B. sep destruct B.
   unfold V293_tcb_site_free_critical,V293_tcb_enabled_resources in *.
   clear -B;sep auto.
 - apply encrit1_rule. apply V293_tcb_enabled_good;exact Frame.
Qed.
Lemma V293_tcb_site_free_pointer : forall Spec sd li I r ri tid tcbtable bf bp bc pc cpu head K R aop ir si ci,
 rule_type_val_match(Tptr V293_tcb_type)head=true -> (R ==> CurLINV li tid) ->
 InfRules Spec sd li I r ri
 (V293_tcb_site_free_critical tcbtable bf bp bc pc cpu head K R aop ir si ci)
 (sassign(evar 108%Z)(evar 91%Z))
 (V293_tcb_site_free_critical tcbtable bf bp bc head cpu head K R aop ir si ci)tid.
Proof.
 intros Spec sd li I r ri tid tcbtable bf bp bc pc cpu head K R aop ir si ci Typed HR.
 unfold V293_tcb_site_free_critical,V293_tcb_enabled_resources. eapply conseq_rule with
 (p:=<||aop||> ** (OS[ir,false,si,ci] **
 (V293_tcb_empty_bindings bf bp bc ** (Amapsto(bc,0%Z)Tint32 true cpu **
 (Amapsto(bf,0%Z)(Tptr V293_tcb_type)true head ** (V293_tcb_site_free_chain(V293_tcb_table_sites tcbtable) 13 head ** (K ** R)))))) **
 Amapsto(bp,0%Z)(Tptr V293_tcb_type)true pc)
 (q:=<||aop||> ** (OS[ir,false,si,ci] **
 (V293_tcb_empty_bindings bf bp bc ** (Amapsto(bc,0%Z)Tint32 true cpu **
 (Amapsto(bf,0%Z)(Tptr V293_tcb_type)true head ** (V293_tcb_site_free_chain(V293_tcb_table_sites tcbtable) 13 head ** (K ** R)))))) **
 Amapsto(bp,0%Z)(Tptr V293_tcb_type)true head).
 - intros s H;clear -H;sep auto.
 - intros s H;clear -H;sep auto.
 - eapply assign_rule with(tp2:=Tptr V293_tcb_type)(l:=(bp,Int.zero)).
   + apply eq_vptr. eexists. eexists. split;reflexivity.
   + intros s H.
     assert(B:s |= V293_tcb_empty_bindings bf bp bc ** Atrue)by(clear -H;sep auto).
     destruct(V293_tcb_empty_env _ _ _ _ B)as(P&_&N&G).
     assert(L:load(Tptr V293_tcb_type)(getmem s)(bf,0%Z)=Some head).
     { eapply V293_star_load_l with(p:=Amapsto(bf,0%Z)(Tptr V293_tcb_type)true head)(q:=Atrue).
       - intros st[HM _]. eapply mapstoval_load;[exact Typed|exact HM].
       - clear -H;sep auto. }
     destruct s as [[[[[[ge le] M] irq] aux] O] op].
     cbn[getlenv getgenv getmem getsmem get_smem get_lenv get_genv get_mem]in *.
     cbn[sat getsmem evaladdr evaltype evalval get_smem get_lenv get_genv get_mem].
     cbv delta[env var memory.ident Modules.ident]in *. rewrite P,N,G,L.
     repeat split;try reflexivity.
     destruct head;cbn[rule_type_val_match]in Typed;try discriminate;discriminate.
   + apply V293_star_CurLINV_l. repeat apply V293_star_CurLINV_r. exact HR.
Qed.

Definition V293_tcb_site_free_pop_state tcbtable bf bp bc b off cpu head next K R aop ir si ci :=
 <||aop||> ** OS[ir,false,si,ci] **
 V293_tcb_enabled_resources bf bp bc (Vptr(b,off)) cpu
 (Amapsto(bf,0%Z)(Tptr V293_tcb_type)true head **
 (V293_tcb_free_node b off next **
 (V293_tcb_site_free_chain(V293_tcb_table_sites tcbtable)12 next ** (K ** R)))).
Lemma V293_tcb_site_free_pop : forall Spec sd li I r ri tid tcbtable bf bp bc b off cpu next K R aop ir si ci,
 (Int.unsigned off+55<=Int.max_unsigned)%Z ->
 rule_type_val_match(Tcom_ptr 410%Z)next=true -> (R ==> CurLINV li tid) ->
 InfRules Spec sd li I r ri
 (V293_tcb_site_free_pop_state tcbtable bf bp bc b off cpu(Vptr(b,off))next K R aop ir si ci)
 (V293_TCBInit_pop 91%Z 108%Z)
 (V293_tcb_site_free_pop_state tcbtable bf bp bc b off cpu next next K R aop ir si ci)tid.
Proof.
 intros Spec sd li I r ri tid tcbtable bf bp bc b off cpu next K R aop ir si ci Bound Typed HR.
 unfold V293_tcb_site_free_pop_state,V293_tcb_enabled_resources,V293_TCBInit_pop.
 eapply conseq_rule with
 (p:=<||aop||> ** (OS[ir,false,si,ci] **
 V293_tcb_enabled_resources bf bp bc(Vptr(b,off))cpu
 (V293_tcb_free_node b off next ** (V293_tcb_site_free_chain(V293_tcb_table_sites tcbtable) 12 next ** (K ** R)))) **
 Amapsto(bf,0%Z)(Tptr V293_tcb_type)true(Vptr(b,off)))
 (q:=<||aop||> ** (OS[ir,false,si,ci] **
 V293_tcb_enabled_resources bf bp bc(Vptr(b,off))cpu
 (V293_tcb_free_node b off next ** (V293_tcb_site_free_chain(V293_tcb_table_sites tcbtable) 12 next ** (K ** R)))) **
 Amapsto(bf,0%Z)(Tptr V293_tcb_type)true next).
 - intros s H;unfold V293_tcb_enabled_resources;clear -H;sep auto.
 - intros s H;unfold V293_tcb_enabled_resources in H;clear -H;sep auto.
 - eapply assign_rule with(tp2:=Tcom_ptr 410%Z)(l:=(bf,Int.zero)).
   + apply eq_vcomptr. split;left;eexists;reflexivity.
   + intros s H. unfold V293_tcb_enabled_resources in H.
     assert(B:s |= V293_tcb_empty_bindings bf bp bc ** Atrue)by(clear -H;sep auto).
     destruct(V293_tcb_empty_env _ _ _ _ B)as(P&_&N&G).
     assert(L:load(Tptr V293_tcb_type)(getmem s)(bp,0%Z)=Some(Vptr(b,off))).
     { eapply V293_star_load_l with(p:=Amapsto(bp,0%Z)(Tptr V293_tcb_type)true(Vptr(b,off)))(q:=Atrue).
       - intros st[HM _]. eapply mapstoval_load;[reflexivity|exact HM].
       - clear -H;sep auto. }
     assert(LN:load(Tcom_ptr 410%Z)(getmem s)(b,(Int.unsigned off+20)%Z)=Some next).
     { eapply V293_star_load_l with(p:=Amapsto(b,(Int.unsigned off+20)%Z)(Tcom_ptr 410%Z)true next)(q:=Atrue).
       - intros st[HM _]. eapply mapstoval_load;[exact Typed|exact HM].
       - unfold V293_tcb_free_node in H. clear -H;sep auto. }
     destruct s as [[[[[[ge le] M] irq] aux] O] op].
     cbn[getlenv getgenv getmem getsmem get_smem get_lenv get_genv get_mem]in *.
     cbn[sat getsmem evaladdr evaltype get_smem get_lenv get_genv].
     cbv delta[env var memory.ident Modules.ident]in *. rewrite N,G. split;[auto| ].
     cbn[evalval evaladdr evaltype get_lenv get_genv get_mem].
     cbv delta[env var memory.ident Modules.ident]in *. rewrite P. cbn beta iota. rewrite L.
     unfold getoff. cbn[evaltype get_lenv get_genv].
     cbv delta[env var memory.ident Modules.ident]in *. rewrite P.
     assert(FT:ftype 7%Z V293_tcb_fields=Some(Tcom_ptr 410%Z))by reflexivity.
     assert(FO:field_offset 7%Z V293_tcb_fields=Some(Int.repr 20))by reflexivity.
     cbn[V293_tcb_type]. rewrite FT,FO. cbn[addrval_to_addr]. rewrite Int.repr_unsigned. unfold Int.add.
     change(load(Tcom_ptr 410%Z)M(b,Int.unsigned(Int.repr(Int.unsigned off+20)))=Some next /\
       Some(Tcom_ptr 410%Z)=Some(Tcom_ptr 410%Z) /\ next<>Vundef).
     rewrite Int.unsigned_repr by(pose proof(Int.unsigned_range off);lia).
     rewrite LN. repeat split;try reflexivity.
     destruct next;cbn[rule_type_val_match]in Typed;try discriminate;discriminate.
   + apply V293_star_CurLINV_l. unfold V293_tcb_enabled_resources.
     repeat apply V293_star_CurLINV_r. exact HR.
Qed.
Lemma V293_tcb_site_free_exit : forall Spec sd li I r ri tid tcbtable bf bp bc b off cpu next K R aop ir si ci,
 GoodFrm R -> (R ==> CurLINV li tid) ->
 rule_type_val_match(Tptr V293_tcb_type)next=true ->
 (Aisr ir ** (V293_tcb_site_free_pool tcbtable bf ** K) ==> Aisr ir ** invlth_isr I 0(gettopis si)) ->
 InfRules Spec sd li I r ri
 (V293_tcb_site_free_pop_state tcbtable bf bp bc b off cpu next next K R aop ir si(true::ci))(sprim excrit)
 (V293_tcb_enabled_state bf bp bc(Vptr(b,off))cpu(V293_tcb_free_node b off next ** R)aop ir si ci)tid.
Proof.
 intros Spec sd li I r ri tid tcbtable bf bp bc b off cpu next K R aop ir si ci Frame HR Typed Close.
 eapply conseq_rule with
 (p:=<||aop||> ** OS[ir,false,si,true::ci] ** ATopis(gettopis si) ** invlth_isr I 0(gettopis si) **
 V293_tcb_enabled_resources bf bp bc(Vptr(b,off))cpu(V293_tcb_free_node b off next ** R))
 (q:=V293_tcb_enabled_state bf bp bc(Vptr(b,off))cpu(V293_tcb_free_node b off next ** R)aop ir si ci).
 - intros s H.
   assert(B:s |= (Amapsto(bf,0%Z)(Tptr V293_tcb_type)true next ** V293_tcb_site_free_chain(V293_tcb_table_sites tcbtable) 12 next) **
    (Aisr ir ** K ** <||aop||> ** Aie false ** Ais si ** Acs(true::ci) **
     V293_tcb_enabled_resources bf bp bc(Vptr(b,off))cpu(V293_tcb_free_node b off next ** R))).
   { unfold V293_tcb_site_free_pop_state,V293_tcb_enabled_resources in *;clear -H;sep auto. }
   eapply astar_mono in B;[ |apply astar_mono;[intros st HS;exact HS|apply V293_tcb_site_free_weaken]|intros st HS;exact HS].
   assert(P:s |= (Aisr ir ** (V293_tcb_site_free_pool tcbtable bf ** K)) **
    (<||aop||> ** Aie false ** Ais si ** Acs(true::ci) **
     V293_tcb_enabled_resources bf bp bc(Vptr(b,off))cpu(V293_tcb_free_node b off next ** R))).
   { unfold V293_tcb_site_free_pool. clear -B Typed;sep auto. }
   eapply astar_mono in P;[ |exact Close|intros st HS;exact HS].
   assert(S:s |= Ais si ** Atrue)by(clear -P;sep auto).
   pose proof(V293_time_topis si Atrue s S)as Top.
   apply astar_l_atopis_elim in Top. destruct Top as[Top _].
   pose proof(@astar_l_atopis_intro s(gettopis si)_ P Top)as HT. clear -HT;sep auto.
 - intros s H;exact H.
 - apply excrit1_rule.
   + apply V293_tcb_enabled_good. cbn[V293_tcb_free_node GoodFrm]. split;[split;[apply V293_storage_frame_good|exact Logic.I]|exact Frame].
   + unfold V293_tcb_enabled_resources. repeat apply V293_star_CurLINV_r. exact HR.
Qed.
Lemma V293_tcb_site_free_return_pool : forall Spec sd li I r ri tid tcbtable bf bp bc pc cpu head K R aop ir si ci,
 GoodFrm R -> (R ==> CurLINV li tid) -> rule_type_val_match(Tptr V293_tcb_type)head=true ->
 (Aisr ir ** (V293_tcb_site_free_pool tcbtable bf ** K) ==> Aisr ir ** invlth_isr I 0(gettopis si)) ->
 InfRules Spec sd li I r ri
 (V293_tcb_site_free_critical tcbtable bf bp bc pc cpu head K R aop ir si(true::ci))(sprim excrit)
 (V293_tcb_enabled_state bf bp bc pc cpu R aop ir si ci)tid.
Proof.
 intros Spec sd li I r ri tid tcbtable bf bp bc pc cpu head K R aop ir si ci Frame HR Typed Close.
 eapply conseq_rule with
 (p:=<||aop||> ** OS[ir,false,si,true::ci] ** ATopis(gettopis si) ** invlth_isr I 0(gettopis si) **
 V293_tcb_enabled_resources bf bp bc pc cpu R)
 (q:=V293_tcb_enabled_state bf bp bc pc cpu R aop ir si ci).
 - intros s H.
   assert(B:s |= (Aisr ir ** (V293_tcb_site_free_pool tcbtable bf ** K)) **
    (<||aop||> ** Aie false ** Ais si ** Acs(true::ci) ** V293_tcb_enabled_resources bf bp bc pc cpu R)).
   { unfold V293_tcb_site_free_critical,V293_tcb_enabled_resources,V293_tcb_site_free_pool in *;clear -H Typed;sep auto. }
   eapply astar_mono in B;[ |exact Close|intros st HS;exact HS].
   assert(S:s |= Ais si ** Atrue)by(clear -B;sep auto).
   pose proof(V293_time_topis si Atrue s S)as Top.
   apply astar_l_atopis_elim in Top. destruct Top as[Top _].
   pose proof(@astar_l_atopis_intro s(gettopis si)_ B Top)as HT. clear -HT;sep auto.
 - intros s H;exact H.
 - apply excrit1_rule.
   + apply V293_tcb_enabled_good;exact Frame.
   + unfold V293_tcb_enabled_resources. repeat apply V293_star_CurLINV_r. exact HR.
Qed.

Lemma V293_tcb_site_free_guard_eval : forall tcbtable bf bp bc cpu head K R aop ir si ci s,
 rule_type_val_match(Tptr V293_tcb_type)head=true ->
 s |= V293_tcb_site_free_critical tcbtable bf bp bc head cpu head K R aop ir si ci ->
 evalval(eunop oppsite(V293_task_prio_null_test(evar 108%Z)))(getsmem s)=Some(Vint32(V293_tcb_free_test head)) /\
 evaltype(eunop oppsite(V293_task_prio_null_test(evar 108%Z)))(getsmem s)=Some Tint32.
Proof.
 intros tcbtable bf bp bc cpu head K R aop ir si ci s Typed H.
 apply V293_tcb_site_free_critical_forget in H.
 eapply V293_tcb_free_guard_eval;[exact Typed|exact H].
Qed.
Lemma V293_tcb_site_free_nonempty_continuation : forall Spec sd li I r ri tid tcbtable
 bf bp bc b off cpu K R aop ir si ci suffix,
 GoodFrm R -> (R ==> CurLINV li tid) ->
 (Aisr ir ** (V293_tcb_site_free_pool tcbtable bf ** K) ==> Aisr ir ** invlth_isr I 0(gettopis si)) ->
 (forall next,In(b,off)(V293_tcb_table_sites tcbtable) -> (Int.unsigned off+55<=Int.max_unsigned)%Z -> rule_type_val_match(Tcom_ptr 410%Z)next=true ->
 InfRules Spec sd li I r ri
 (V293_tcb_enabled_state bf bp bc(Vptr(b,off))cpu(V293_tcb_free_node b off next ** R)aop ir si ci)
 suffix Afalse tid) ->
 InfRules Spec sd li I r ri
 (V293_tcb_site_free_critical tcbtable bf bp bc(Vptr(b,off))cpu(Vptr(b,off))K R aop ir si(true::ci))
 (sseq(V293_TCBInit_pop 91%Z 108%Z)(sseq(sprim excrit)suffix))Afalse tid.
Proof.
 intros Spec sd li I r ri tid tcbtable bf bp bc b off cpu K R aop ir si ci suffix Frame HR Close Success.
 eapply conseq_rule with
 (p:=EX next:val,V293_tcb_site_free_pop_state tcbtable bf bp bc b off cpu(Vptr(b,off))next K R aop ir si(true::ci) **
 [|((Int.unsigned off+55<=Int.max_unsigned)%Z /\ In(b,off)(V293_tcb_table_sites tcbtable)) /\ rule_type_val_match(Tcom_ptr 410%Z)next=true|]).
 - intros s H. unfold V293_tcb_site_free_critical,V293_tcb_enabled_resources in H.
   cbn[V293_tcb_site_free_chain]in H. sep normal in H. sep destruct H.
   unfold V293_tcb_site_free_pop_state,V293_tcb_enabled_resources,V293_tcb_free_node. clear -H;sep auto.
 - intros s H;exact H.
 - apply ex_intro_rule. intro next. apply pure_split_rule. intros[[Bound Member]Typed].
   eapply seq_rule;[apply V293_tcb_site_free_pop;assumption| ].
   eapply seq_rule;[apply V293_tcb_site_free_exit;assumption| ].
   apply Success;assumption.
Qed.
Theorem V293_OS_TCBInit_site_free_body_with_success : forall Spec sd li I r tid hi hc tcbtable
 bf bp bc pc cpu K R aop ir si ci,
 (gettopis si<=INUM)%nat -> GoodFrm R -> (R ==> CurLINV li tid) ->
 (Aisr ir ** invlth_isr I 0(gettopis si) ==> Aisr ir ** (V293_tcb_site_free_pool tcbtable bf ** K)) ->
 (Aisr ir ** (V293_tcb_site_free_pool tcbtable bf ** K) ==> Aisr ir ** invlth_isr I 0(gettopis si)) ->
 (V293_tcb_enabled_state bf bp bc Vnull(Vint32 Int.zero)R aop ir si ci ==> r(Some(Vint32(Int.repr 66)))) ->
 (forall b off next,In(b,off)(V293_tcb_table_sites tcbtable) -> (Int.unsigned off+55<=Int.max_unsigned)%Z -> rule_type_val_match(Tcom_ptr 410%Z)next=true ->
 InfRules Spec sd li I r Afalse
 (V293_tcb_enabled_state bf bp bc(Vptr(b,off))(Vint32 Int.zero)(V293_tcb_free_node b off next ** R)aop ir si ci)
 (sseq(V293_TCBInit_fields 108%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z)
       (V293_TCBInit_success_suffix hi hc)) Afalse tid) ->
 InfRules Spec sd li I r Afalse
 (V293_tcb_enabled_state bf bp bc pc cpu R aop ir si ci)
 (V293_TCBInit_function_body hi hc)Afalse tid.
Proof.
 intros Spec sd li I r tid hi hc tcbtable bf bp bc pc cpu K R aop ir si ci Bound Frame HR Open Close Empty Success.
 unfold V293_TCBInit_function_body. eapply seq_rule;[apply V293_tcb_enabled_cpu;exact HR| ].
 unfold V293_TCBInit_prefix. eapply seq_rule;[apply V293_tcb_site_free_enter with(tcbtable:=tcbtable)(K:=K);assumption| ].
 eapply conseq_rule with
 (p:=EX head:val,V293_tcb_site_free_critical tcbtable bf bp bc pc(Vint32 Int.zero)head K R aop ir si(true::ci) **
 [|rule_type_val_match(Tptr V293_tcb_type)head=true|]).
 - intros s H. sep normal in H. sep destruct H. clear -H;sep auto.
 - intros s H;exact H.
 - apply ex_intro_rule. intro head. apply pure_split_rule. intro Typed.
   eapply seq_rule;[apply V293_tcb_site_free_pointer;assumption| ].
   destruct head;cbn[rule_type_val_match]in Typed;try discriminate.
   + eapply seq_rule with(p':=V293_tcb_site_free_critical tcbtable bf bp bc Vnull(Vint32 Int.zero)Vnull K R aop ir si(true::ci)).
     * eapply ift_rule with(tp:=Tint32).
       -- intros s H. exists(Vint32 Int.zero). cbn[sat].
          destruct(V293_tcb_site_free_guard_eval tcbtable bf bp bc (Vint32 Int.zero) Vnull K R aop ir si (true::ci) s eq_refl H)as[V T].
          split;[exact V|split;[exact T|discriminate]].
       -- intros s[H _];exact H.
       -- eapply conseq_rule with(p:=Afalse)(q:=Afalse).
          ++ intros s[H[v[V B]]].
             destruct(V293_tcb_site_free_guard_eval tcbtable bf bp bc (Vint32 Int.zero) Vnull K R aop ir si (true::ci) s eq_refl H)as[Z _].
             rewrite Z in V. inversion V;subst v. discriminate B.
          ++ intros s H;contradiction.
          ++ apply pfalse_rule.
     * unfold V293_TCBInit_empty. eapply seq_rule.
       -- apply V293_tcb_site_free_return_pool;assumption.
       -- apply rete_rule with(v:=Vint32(Int.repr 66))(t:=Tint32).
          intros s H. split;[apply Empty;exact H| ].
          destruct s as [[[[[[ge le] M] irq] aux] O] op].
          cbn[sat evalval evaltype getsmem get_smem]. repeat split;try reflexivity;discriminate.
   + destruct a as[b off]. eapply seq_rule with(p':=Afalse).
     * eapply ift_rule with(tp:=Tint32).
       -- intros s H. exists(Vint32 Int.one). cbn[sat].
          destruct(V293_tcb_site_free_guard_eval tcbtable bf bp bc (Vint32 Int.zero) (Vptr(b,off)) K R aop ir si (true::ci) s eq_refl H)as[V T].
          split;[exact V|split;[exact T|discriminate]].
       -- intros s[H[v[V B]]].
          destruct(V293_tcb_site_free_guard_eval tcbtable bf bp bc (Vint32 Int.zero) (Vptr(b,off)) K R aop ir si (true::ci) s eq_refl H)as[Z _].
          rewrite Z in V. inversion V;subst v. discriminate B.
       -- eapply conseq_rule;[intros s[H _];exact H|intros s H;exact H| ].
          apply V293_tcb_site_free_nonempty_continuation;try assumption. intros;apply Success;assumption.
     * apply pfalse_rule.
Qed.

(* Original complete body: selected table membership comes from the actual
   refined allocator above, not a post-Hook membership premise. *)
Theorem V293_OS_TCBInit_site_allocated_finite_published : forall Spec sd li I r tid hi hc tcbtable
 table reserved bf bp bc pc cpu Kfree Kprio Kpub bh bg br bn bprio bs bb bi bz be bo p top bottom identity size ext options R aop ir si ci
 (good:GoodFunAsrt(V293_create_owned_share table reserved p ** (V293_tcb_publication_globals bh bg br bn ** R))),
 p<13 -> (gettopis si<=INUM)%nat -> GoodFrm R ->
 V293_tcb_init_values_valid top bottom identity size ext options -> (R ==> CurLINV li tid) ->
 (Aisr ir ** invlth_isr I 0(gettopis si) ==> Aisr ir ** (V293_tcb_site_free_pool tcbtable bf ** Kfree)) ->
 (Aisr ir ** (V293_tcb_site_free_pool tcbtable bf ** Kfree) ==> Aisr ir ** invlth_isr I 0(gettopis si)) ->
 (Aisr ir ** invlth_isr I 0(gettopis si) ==> Aisr ir ** V293_create_owned_pool table reserved p Kprio) ->
 (Aisr ir ** V293_create_owned_pool table reserved p Kprio ==> Aisr ir ** invlth_isr I 0(gettopis si)) ->
 Spec hi=Some(V293_tcb_enabled_hook_fpre p top bottom identity size ext options
 (V293_create_owned_share table reserved p ** (V293_tcb_publication_globals bh bg br bn ** R))aop ir si ci tid good,
 V293_tcb_enabled_hook_fpost p top bottom identity size ext options
 (V293_create_owned_share table reserved p ** (V293_tcb_publication_globals bh bg br bn ** R))aop ir si ci tid good,(Tvoid,[Tptr V293_tcb_type])) ->
 Spec hc=Some(V293_tcb_enabled_hook_fpre p top bottom identity size ext options (V293_tcb_publication_globals bh bg br bn ** R) aop ir si ci tid (proj2 good),
 V293_tcb_enabled_hook_fpost p top bottom identity size ext options (V293_tcb_publication_globals bh bg br bn ** R) aop ir si ci tid (proj2 good),(Tvoid,[Tptr V293_tcb_type])) ->
 (V293_tcb_enabled_state bf bp bc Vnull(Vint32 Int.zero)
 (V293_tcb_allocated_inputs bp bprio bs bb bi bz be bo p top bottom identity size ext options
 (V293_tcb_table_binding table ** (V293_create_owned_share table reserved p ** (V293_tcb_publication_globals bh bg br bn ** R))))aop ir si ci ==>
 r(Some(Vint32(Int.repr 66)))) ->
 (forall b off next s,
 s |= V293_tcb_enabled_state bf bp bc(Vptr(b,off))(Vint32 Int.zero)
 (V293_tcb_allocated_initialized b off next p top bottom identity size ext options **
 V293_tcb_allocated_inputs bp bprio bs bb bi bz be bo p top bottom identity size ext options
 (V293_tcb_table_binding table ** (V293_create_owned_share table reserved p ** (V293_tcb_publication_globals bh bg br bn ** R))))aop ir si ci ->
 (b,off)<>reserved) ->
 (Aisr ir ** invlth_isr I 0(gettopis si) ==>
 Aisr ir ** (V293_tcb_finite_shared tcbtable bh bg br bn(V293_prio_row p) ** Kpub)) ->
 (Aisr ir ** (V293_tcb_finite_shared tcbtable bh bg br bn(V293_prio_row p) ** Kpub) ==>
 Aisr ir ** invlth_isr I 0(gettopis si)) ->
 (forall b off,
 V293_tcb_enabled_state bf bp bc(Vptr(b,off))(Vint32 Int.zero)
 (V293_tcb_allocated_inputs bp bprio bs bb bi bz be bo p top bottom identity size ext options
 (V293_tcb_table_binding table ** (V293_tcb_publication_globals bh bg br bn ** R)))aop ir si ci ==>
 r(Some(Vint32 Int.zero))) ->
 InfRules Spec sd li I r Afalse
 (V293_tcb_enabled_state bf bp bc pc cpu
 (V293_tcb_allocated_inputs bp bprio bs bb bi bz be bo p top bottom identity size ext options
 (V293_tcb_table_binding table ** (V293_create_owned_share table reserved p ** (V293_tcb_publication_globals bh bg br bn ** R))))aop ir si ci)
 (V293_TCBInit_function_body hi hc)Afalse tid.
Proof.
 intros Spec sd li I r tid hi hc tcbtable table reserved bf bp bc pc cpu Kfree Kprio Kpub bh bg br bn bprio bs bb bi bz be bo p top bottom identity size ext options R aop ir si ci good Range Bound Frame Valid HR FreeOpen FreeClose PriorityOpen PriorityClose FirstLookup SecondLookup Empty Fresh PubOpen PubClose Return.
 assert(PF:GoodFrm(V293_tcb_publication_globals bh bg br bn ** R))by(cbn[V293_tcb_publication_globals GoodFrm];tauto).
 assert(PL:(V293_tcb_publication_globals bh bg br bn ** R) ==> CurLINV li tid)by(apply V293_star_CurLINV_r;exact HR).
 assert(InputFrame:GoodFrm(V293_tcb_table_binding table ** (V293_create_owned_share table reserved p ** (V293_tcb_publication_globals bh bg br bn ** R)))).
 { unfold V293_tcb_table_binding,V293_create_owned_share,V293_reservation_owner;cbn[GoodFrm];tauto. }
 assert(InputLinv:(V293_tcb_table_binding table ** (V293_create_owned_share table reserved p ** (V293_tcb_publication_globals bh bg br bn ** R))) ==> CurLINV li tid).
 { repeat apply V293_star_CurLINV_r;exact HR. }
 apply V293_OS_TCBInit_site_free_body_with_success with(tcbtable:=tcbtable)(K:=Kfree);try assumption.
 - apply V293_tcb_allocated_inputs_good;exact InputFrame.
 - apply V293_tcb_allocated_inputs_linv;exact InputLinv.
 - intros b off next NodeMember NodeBound NextTyped.
   eapply seq_rule;[apply V293_tcb_allocated_fields;assumption| ].
   eapply conseq_rule with
   (p:=V293_tcb_enabled_state bf bp bc(Vptr(b,off))(Vint32 Int.zero)
    (V293_tcb_allocated_initialized b off next p top bottom identity size ext options **
     V293_tcb_allocated_inputs bp bprio bs bb bi bz be bo p top bottom identity size ext options
     (V293_tcb_table_binding table ** (V293_create_owned_share table reserved p ** (V293_tcb_publication_globals bh bg br bn ** R))))aop ir si ci **
     [|(b,off)<>reserved|]).
   + intros s H. apply astar_comm. apply astar_l_apure_intro;[exact H|eapply Fresh;exact H].
   + intros s H;exact H.
   + apply pure_split_rule. intro Distinct.
     eapply conseq_rule with
     (p:=V293_tcb_priority_state table bprio bp p(Vptr(b,off))
       (V293_tcb_allocated_initialized b off next p top bottom identity size ext options **
       ((V293_create_owned_share table reserved p ** (V293_tcb_publication_globals bh bg br bn ** R)) **
        V293_tcb_priority_caller_frame bf bp bc bprio bs bb bi bz be bo(Vint32 Int.zero)top bottom identity size ext options))aop ir true si ci).
     * apply V293_tcb_full_priority_view.
     * intros s H;exact H.
     * apply V293_OS_TCBInit_owned_suffix_after_first_hook with(reserved:=reserved)(K:=Kprio)(good:=good);try assumption.
       -- apply V293_tcb_priority_caller_frame_good.
       -- eapply conseq_rule;[apply V293_tcb_full_priority_restore|intros s H;exact H| ].
          eapply seq_rule;[apply V293_tcb_second_hook with(good:=proj2 good);assumption| ].
          eapply conseq_rule;[apply V293_tcb_full_publication_view;assumption|intros s H;exact H| ].
          apply ex_intro_rule. intro prev.
          apply V293_OS_TCBInit_publish_finite_enabled with(tcbtable:=tcbtable)(K:=Kpub);try assumption.
          ++ pose proof(Int.unsigned_range off);lia.
          ++ unfold V293_prio_row. destruct(p <? 8);lia.
          ++ unfold V293_prio_bit. destruct(p <? 8)eqn:E;apply Nat.ltb_lt in E||apply Nat.ltb_ge in E;lia.
          ++ rewrite Int.repr_unsigned. exact NodeMember.
          ++ apply V293_tcb_publication_caller_frame_good;exact Frame.
          ++ apply V293_tcb_publication_caller_frame_linv;exact HR.
          ++ intros s H. apply Return with(b:=b)(off:=off). eapply V293_tcb_full_publication_restore;exact H.
Qed.
Print Assumptions V293_OS_TCBInit_site_allocated_finite_published.

Lemma V293_tcb_site_free_chain_good : forall sites n v,GoodInvAsrt(V293_tcb_site_free_chain sites n v).
Proof.
 intro sites;induction n as[ |n IH];intro v;destruct v;try exact I;destruct a;cbn[V293_tcb_site_free_chain GoodInvAsrt];
 split;[exact I|split;[apply V293_storage_good| ]];intro next;split;[exact I|split;[exact I|apply IH]].
Qed.
Lemma V293_tcb_site_free_pool_good : forall tcbtable bf,GoodInvAsrt(V293_tcb_site_free_pool tcbtable bf).
Proof. intros tcbtable bf;intro v;split;[exact I|split;[exact I|apply V293_tcb_site_free_chain_good]]. Qed.

Lemma V293_tcb_site_free_chain_frame : forall sites n v,GoodFrm(V293_tcb_site_free_chain sites n v).
Proof.
 intro sites;induction n as[ |n IH];intro v;destruct v;try exact I;destruct a;cbn[V293_tcb_site_free_chain GoodFrm];
 split;[exact I|split;[apply V293_storage_frame_good| ]];intro next;split;[exact I|split;[exact I|apply IH]].
Qed.
Lemma V293_tcb_site_free_chain_aux_stable : forall sites n v ge le M ir aux O op ir' aux',
 (ge,le,M,ir,aux,O,op) |= V293_tcb_site_free_chain sites n v ->
 (ge,le,M,ir',aux',O,op) |= V293_tcb_site_free_chain sites n v.
Proof.
 intro sites;induction n as[ |n IH];intros v ge le M ir aux O op ir' aux' H;
 destruct v;try destruct a;cbn[V293_tcb_site_free_chain]in H|-*;try contradiction;try exact H.
 apply astar_l_apure_elim in H. destruct H as[Bound H].
 apply astar_l_apure_intro;[ |exact Bound].
 apply sat_split in H. destruct H as(m1&m2&o1&o2&JM&JO&HP&next&HN).
 apply sat_split'. exists m1. exists m2. exists o1. exists o2. split;[exact JM| ]. split;[exact JO| ]. split.
 - eapply V293_storage_aux_stable;exact HP.
 - exists next. apply astar_l_apure_elim in HN. destruct HN as[Typed HN].
   apply astar_l_apure_intro;[ |exact Typed].
   apply sat_split in HN. destruct HN as(m3&m4&o3&o4&JM2&JO2&HN&HT).
   apply sat_split'. exists m3. exists m4. exists o3. exists o4. split;[exact JM2| ]. split;[exact JO2| ].
   split;[exact HN|eapply IH;exact HT].
Qed.
Lemma V293_tcb_site_free_pool_aux_stable : forall tcbtable bf ge le M ir aux O op ir' aux',
 (ge,le,M,ir,aux,O,op) |= V293_tcb_site_free_pool tcbtable bf ->
 (ge,le,M,ir',aux',O,op) |= V293_tcb_site_free_pool tcbtable bf.
Proof.
 intros tcbtable bf ge le M ir aux O op ir' aux'[head H]. exists head.
 apply astar_l_apure_elim in H. destruct H as[Typed H].
 apply astar_l_apure_intro;[ |exact Typed].
 apply sat_split in H. destruct H as(m1&m2&o1&o2&JM&JO&HP&HT).
 apply sat_split'. exists m1. exists m2. exists o1. exists o2. split;[exact JM| ]. split;[exact JO| ].
 split;[exact HP|eapply V293_tcb_site_free_chain_aux_stable;exact HT].
Qed.
Lemma V293_tcb_site_free_pool_isr : forall tcbtable bf,assertion.inv_isr_prop(V293_tcb_site_free_pool tcbtable bf).
Proof.
 intros tcbtable bf. unfold assertion.inv_isr_prop. repeat split;intros;
 destruct s as [[[[[[ge le] M] ir] [[ie si] cs]] O] op];
 eapply V293_tcb_site_free_pool_aux_stable;exact H.
Qed.


Lemma V293_tcb_site_free_pool_precise : forall tcbtable bf,precise(V293_tcb_site_free_pool tcbtable bf).
Proof.
 intros tcbtable bf s M1 M2 O1 O2 H1 H2 M O HM1 HM2 HO1 HO2.
 apply V293_tcb_site_free_pool_forget in H1. apply V293_tcb_site_free_pool_forget in H2.
 eapply V293_tcb_free_pool_precise;eauto.
Qed.
Theorem V293_OS_TCBInit_site_free_pop_transfer : forall Spec sd li I r ri tid
 tcbtable bf bp bc b off cpu K R aop ir si ci,
 GoodFrm R -> (R ==> CurLINV li tid) ->
 (Aisr ir ** (V293_tcb_site_free_pool tcbtable bf ** K) ==> Aisr ir ** invlth_isr I 0(gettopis si)) ->
 InfRules Spec sd li I r ri
 (V293_tcb_site_free_critical tcbtable bf bp bc(Vptr(b,off))cpu(Vptr(b,off))K R aop ir si(true::ci))
 (sseq(V293_TCBInit_pop 91%Z 108%Z)(sprim excrit))
 (EX next:val,[|((Int.unsigned off+55<=Int.max_unsigned)%Z /\ In(b,off)(V293_tcb_table_sites tcbtable)) /\
   rule_type_val_match(Tcom_ptr 410%Z)next=true|] **
  V293_tcb_enabled_state bf bp bc(Vptr(b,off))cpu(V293_tcb_free_node b off next ** R)aop ir si ci)tid.
Proof.
 intros Spec sd li I r ri tid tcbtable bf bp bc b off cpu K R aop ir si ci Frame HR Close.
 eapply conseq_rule with
 (p:=EX next:val,V293_tcb_site_free_pop_state tcbtable bf bp bc b off cpu(Vptr(b,off))next K R aop ir si(true::ci) **
 [|((Int.unsigned off+55<=Int.max_unsigned)%Z /\ In(b,off)(V293_tcb_table_sites tcbtable)) /\ rule_type_val_match(Tcom_ptr 410%Z)next=true|]).
 - intros s H. unfold V293_tcb_site_free_critical,V293_tcb_enabled_resources in H.
   cbn[V293_tcb_site_free_chain]in H. sep normal in H. sep destruct H.
   unfold V293_tcb_site_free_pop_state,V293_tcb_enabled_resources,V293_tcb_free_node.
   clear -H. sep auto.
 - intros s H;exact H.
 - apply ex_intro_rule. intro next. apply pure_split_rule. intros[[Bound Member]Typed].
   eapply seq_rule.
   + apply V293_tcb_site_free_pop;assumption.
   + eapply conseq_rule.
     * intros s H;exact H.
     * intros s H. exists next. apply astar_l_apure_intro;[exact H|auto].
     * apply V293_tcb_site_free_exit;assumption.
Qed.
Print Assumptions V293_OS_TCBInit_site_free_pop_transfer.

