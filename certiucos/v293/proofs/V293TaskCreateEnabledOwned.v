(* Actual enabled creator entry; reservation-aware nullable shared slot.
   Counter0/empty allocator scope is explicit, not a production kernel Inv. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateEnabledReject.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateBodyFailure.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateExtPrefix.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtPrefix.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateEnabledFailure.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateFailureHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPriorityHoare.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtSuffix.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateEnabledSlotPool.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.tactics.sepauto.sep_combine_lemmas.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEmptyEnabled.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateTCBCall.
Require Import CertiOS.certiucos.v293.proofs.V293TCBSuccessInternal.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtCalls.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitFunction.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateStackSuccess.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateStackCall.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateStackEntry.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateReservationOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateRejectInternal.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtFunction.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateOwnedEmpty.

Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateEmptyInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateSuccessInternal.

Definition V293_create_owned_acquired bp bc table bn br p cpu v K F aop ir si ci :=
 <||aop||> ** OS[ir,false,si,true::ci] **
 V293_create_enabled_locals bp bc p cpu
 (V293_create_slot_views table bn br ** Amapsto(bn,0%Z)Tint8 true(V293_byteval 0) **
  Amapsto(table,(4*Z.of_nat p)%Z)(Tptr V293_tcb_type)
   (V293_reservation_permission(br,Int.zero)v)v ** K ** F).

Lemma V293_create_owned_initial_enter : forall Spec sd li I r ri tid
 bp bc table bn br p cpu K F aop ir si ci,
 (gettopis si<=INUM)%nat -> GoodFrm F ->
 (Aisr ir ** invlth_isr I 0(gettopis si) ==>
  Aisr ir ** V293_create_owned_pool table(br,Int.zero)p
   (Amapsto(bn,0%Z)Tint8 true(V293_byteval 0) ** K)) ->
 InfRules Spec sd li I r ri
 (V293_create_enabled_state bp bc p cpu(V293_create_slot_views table bn br ** F)aop ir si ci)
 (sprim encrit)
 (EX v:val,[|rule_type_val_match(Tptr V293_tcb_type)v=true|] **
  V293_create_owned_acquired bp bc table bn br p cpu v K F aop ir si ci)tid.
Proof.
 intros Spec sd li I r ri tid bp bc table bn br p cpu K F aop ir si ci Bound Frame Open.
 unfold V293_create_enabled_state. eapply conseq_rule with
 (p:=<||aop||> ** OS[ir,true,si,ci] ** ATopis(gettopis si) ** [|(gettopis si<=INUM)%nat|] **
  V293_create_enabled_locals bp bc p cpu(V293_create_slot_views table bn br ** F))
 (q:=<||aop||> ** OS[ir,false,si,true::ci] ** invlth_isr I 0(gettopis si) **
  V293_create_enabled_locals bp bc p cpu(V293_create_slot_views table bn br ** F)).
 - intros s H. assert(S:s |= Ais si ** Atrue)by(sep auto).
   pose proof(V293_time_topis si Atrue s S)as Top.
   apply astar_l_atopis_elim in Top. destruct Top as[Top _].
   pose proof(@astar_l_atopis_intro s(gettopis si)_ H Top)as HT. clear -HT Bound;sep auto.
 - intros s H.
   assert(B:s |= (Aisr ir ** invlth_isr I 0(gettopis si)) **
    (<||aop||> ** Aie false ** Ais si ** Acs(true::ci) **
     V293_create_enabled_locals bp bc p cpu(V293_create_slot_views table bn br ** F)))by(sep auto).
   eapply astar_mono in B;[ |exact Open|intros st HS;exact HS].
   unfold V293_create_owned_pool,V293_reservation_pool in B.
   sep normal in B. sep destruct B. sep split in B.
   exists x. apply astar_l_apure_intro;[ |assumption].
   unfold V293_create_owned_acquired,V293_create_enabled_locals in *.
   cbn[V293_rdy_raw_cells]in *. sep auto.
 - apply encrit1_rule. apply V293_create_enabled_good.
   cbn[V293_create_slot_views V293_create_global_binding GoodFrm];tauto.
Qed.


Lemma V293_create_owned_initial_exit : forall Spec sd li I r ri tid
 bp bc table bn br p cpu v K F aop ir si ci,
 rule_type_val_match(Tptr V293_tcb_type)v=true -> GoodFrm F -> (F ==> CurLINV li tid) ->
 (Aisr ir ** V293_create_owned_pool table(br,Int.zero)p
   (Amapsto(bn,0%Z)Tint8 true(V293_byteval 0) ** K) ==>
  Aisr ir ** invlth_isr I 0(gettopis si)) ->
 InfRules Spec sd li I r ri
 (V293_create_owned_acquired bp bc table bn br p cpu v K F aop ir si ci)
 (sprim excrit)
 (V293_create_enabled_state bp bc p cpu(V293_create_slot_views table bn br ** F)aop ir si ci)tid.
Proof.
 intros Spec sd li I r ri tid bp bc table bn br p cpu v K F aop ir si ci Typed Frame HR Close.
 eapply conseq_rule with
 (p:=<||aop||> ** OS[ir,false,si,true::ci] ** ATopis(gettopis si) ** invlth_isr I 0(gettopis si) **
  V293_create_enabled_locals bp bc p cpu(V293_create_slot_views table bn br ** F))
 (q:=V293_create_enabled_state bp bc p cpu(V293_create_slot_views table bn br ** F)aop ir si ci).
 - intros s H.
   assert(B:s |= (Aisr ir ** V293_create_owned_pool table(br,Int.zero)p
    (Amapsto(bn,0%Z)Tint8 true(V293_byteval 0) ** K)) **
    (<||aop||> ** Aie false ** Ais si ** Acs(true::ci) **
     V293_create_enabled_locals bp bc p cpu(V293_create_slot_views table bn br ** F))).
   { unfold V293_create_owned_pool.
     eapply astar_mono;[apply astar_mono;[intros st HS;exact HS| ]|intros st HS;exact HS| ].
     - apply astar_mono;[ |intros st HS;exact HS].
       intros st HS. unfold V293_reservation_pool. exists v.
       apply astar_l_apure_intro;[exact HS|exact Typed].
     - unfold V293_create_owned_acquired,V293_create_enabled_locals in *.
       cbn[V293_rdy_raw_cells]in *;clear -H;sep auto. }
   eapply astar_mono in B;[ |exact Close|intros st HS;exact HS].
   assert(S:s |= Ais si ** Atrue)by(clear -B;sep auto).
   pose proof(V293_time_topis si Atrue s S)as Top.
   apply astar_l_atopis_elim in Top. destruct Top as[Top _].
   pose proof(@astar_l_atopis_intro s(gettopis si)_ B Top)as HT. clear -HT;sep auto.
 - intros s H;exact H.
 - apply excrit1_rule.
   + apply V293_create_enabled_good. cbn[V293_create_slot_views V293_create_global_binding GoodFrm];tauto.
   + unfold V293_create_enabled_locals. do 2 apply V293_star_CurLINV_r.
     do 2 apply V293_star_CurLINV_r. apply V293_star_CurLINV_r;exact HR.
Qed.

Lemma V293_create_owned_acquired_null : forall bp bc table bn br p cpu K F aop ir si ci,
 V293_create_owned_acquired bp bc table bn br p cpu Vnull K F aop ir si ci ==>
 V293_create_slot_state bp bc table bn br p 0 None cpu K F aop ir si ci.
Proof.
 intros bp bc table bn br p cpu K F aop ir si ci s H.
 unfold V293_create_owned_acquired,V293_create_enabled_locals,V293_create_slot_state in *.
 cbn[V293_rdy_raw_cells V293_create_slot_cells V293_create_slot_value V293_reservation_permission app]in *.
 clear -H;sep auto.
Qed.

(* Reads do not need write permission. In particular RESERVED remains occupied
   when the pool owns only a half; no conversion to a full byte is assumed. *)
Lemma V293_create_owned_acquired_guards : forall bp bc table bn br p cpu v K F aop ir si ci s,
 p<13 -> rule_type_val_match(Tptr V293_tcb_type)v=true ->
 s |= V293_create_owned_acquired bp bc table bn br p cpu v K F aop ir si ci ->
 (evalval(ebinop olt(econst32 Int.zero)(ecast(evar 99%Z)Tint32))(getsmem s)=Some(Vint32 Int.zero) /\
  evaltype(ebinop olt(econst32 Int.zero)(ecast(evar 99%Z)Tint32))(getsmem s)=Some Tint32) /\
 (evalval(ebinop oeq(earrayelem(evar 92%Z)(evar 101%Z))(ecast enull(Tptr V293_tcb_type)))(getsmem s)=val_eq v Vnull /\
  evaltype(ebinop oeq(earrayelem(evar 92%Z)(evar 101%Z))(ecast enull(Tptr V293_tcb_type)))(getsmem s)=Some Tint32).
Proof.
 intros bp bc table bn br p cpu v K F aop ir si ci s Range Typed H.
 unfold V293_create_owned_acquired,V293_create_enabled_locals in H.
 cbn[V293_rdy_raw_cells]in H.
 assert(E:s |= V293_create_prefix_bindings bp bn bc table 99%Z 97%Z br ** Atrue).
 { unfold V293_create_prefix_bindings,V293_create_slot_views,V293_tcb_table_binding,V293_create_global_binding in *;clear -H;sep auto. }
 destruct(V293_create_prefix_bindings_env _ _ _ _ _ _ _ _ E)as(Bp&Bc&Nn&Gn&Nr&Gr&Nt&Gt).
 assert(PriorityRead:load Tint8(getmem s)(bp,0%Z)=Some(V293_byteval p)).
 { eapply V293_star_load_l;[ |assert(A:s |= Amapsto(bp,0%Z)Tint8 true(V293_byteval p) ** Atrue)by(clear -H;sep auto);exact A].
   intros st[P _];eapply mapstoval_load;[apply V293_byte_type;lia|exact P]. }
 assert(NestingRead:load Tint8(getmem s)(bn,0%Z)=Some(V293_byteval 0)).
 { eapply V293_star_load_l;[ |assert(A:s |= Amapsto(bn,0%Z)Tint8 true(V293_byteval 0) ** Atrue)by(clear -H;sep auto);exact A].
   intros st[P _];eapply mapstoval_load;[reflexivity|exact P]. }
 assert(SlotRead:load(Tptr V293_tcb_type)(getmem s)(table,(4*Z.of_nat p)%Z)=Some v).
 { eapply V293_star_load_l;[ |assert(A:s |= Amapsto(table,(4*Z.of_nat p)%Z)(Tptr V293_tcb_type)
    (V293_reservation_permission(br,Int.zero)v)v ** Atrue)by(clear -H;sep auto);exact A].
   intros st[P _];eapply mapstoval_load;[exact Typed|exact P]. }
 destruct s as [[[[[[ge le] M] irq] aux] O] op].
 cbn[getlenv getgenv getmem getsmem get_smem get_lenv get_genv]in *.
 cbv delta[env var memory.ident Modules.ident]in *.
 cbn[get_mem]in PriorityRead,NestingRead,SlotRead.
 split;split.
 - cbn[evalval evaltype get_lenv get_genv get_mem]. cbv delta[env var memory.ident Modules.ident]in *. rewrite Nn,Gn.
   cbn beta iota. rewrite NestingRead. reflexivity.
 - cbn[evaltype get_lenv get_genv]. cbv delta[env var memory.ident Modules.ident]in *. rewrite Nn,Gn. reflexivity.
 - cbn[evalval evaltype get_lenv get_genv get_mem]. cbv delta[env var memory.ident Modules.ident]in *. rewrite Nt,Gt,Bp.
   cbn beta iota. rewrite PriorityRead. cbn[load addr_to_addrval V293_byteval].
   rewrite Int.add_zero_l. unfold Int.mul.
   rewrite(Int.unsigned_repr(Z.of_nat p))by(unfold Int.max_unsigned,Int.modulus,Int.wordsize;cbn;lia).
   change(match load(Tptr V293_tcb_type)M(table,Int.unsigned(Int.repr(4*Z.of_nat p)))with
    |Some w=>val_eq w Vnull|_=>None end=val_eq v Vnull).
   rewrite Int.unsigned_repr by(change(0<=4*Z.of_nat p<=4294967295)%Z;lia). rewrite SlotRead;reflexivity.
 - cbn[evaltype get_lenv get_genv]. cbv delta[env var memory.ident Modules.ident]in *. rewrite Nt,Gt,Bp. reflexivity.
Qed.


(* Function contracts expose bindings but not shared bytes. Non-shadowing is
   derived from the exact local declaration domain inside the function. *)
Definition V293_create_owned_globals bf table bn br R :=
 Agvarenv 91%Z(Tptr V293_tcb_type)(bf,0%Z) **
 V293_create_slot_globals table bn br ** R.
Lemma V293_create_owned_globals_good : forall bf table bn br R,
 GoodFunAsrt R -> GoodFunAsrt(V293_create_owned_globals bf table bn br R).
Proof.
 intros. cbn[V293_create_owned_globals V293_create_slot_globals
 V293_create_rejection_globals GoodFunAsrt];tauto.
Qed.
Definition V293_create_owned_post bf table bn br Rbefore Rafter aop ir si ci result :=
 Adisj
 ([|result=Some(Vint32(Int.repr 42)) \/ result=Some(Vint32(Int.repr 40))|] **
  V293_create_enabled_external(V293_create_owned_globals bf table bn br Rbefore)aop ir si ci)
 ([|result=Some(Vint32(Int.repr 66))|] **
  V293_create_enabled_external(V293_create_owned_globals bf table bn br Rafter)aop ir si ci).
Definition V293_create_owned_fpost bf table bn br Rbefore Rafter aop ir si ci
 (gb:GoodFunAsrt Rbefore)(ga:GoodFunAsrt Rafter) : fpost :=
 fun vl result lg tid=>@mkfunasrt
 (V293_create_owned_post bf table bn br Rbefore Rafter aop ir si ci result)
 (conj
  (conj I(V293_create_enabled_external_good _ aop ir si ci
    (V293_create_owned_globals_good bf table bn br Rbefore gb)))
  (conj I(V293_create_enabled_external_good _ aop ir si ci
    (V293_create_owned_globals_good bf table bn br Rafter ga)))).

Lemma V293_create_owned_reject_cells : forall k target argv inputtop p identity bottom size ext options
 olderr oldpsp bp bc bf table bn br Rbefore Rafter aop ir si ci result,
 (k=V293_create_bad_priority \/ k=V293_create_occupied_priority) ->
 V293_create_enabled_return k bp bc p
 (V293_create_slot_views table bn br **
  (LV 108%Z @ (Tptr Tint32) |->oldpsp **
   V293_create_stack_arguments target argv inputtop options
    (Rbefore ** V293_create_owned_empty_aux bf bottom identity size ext olderr V293_create_internal_domain)))
 aop ir si ci result ==>
 V293_create_internal_post_cells **
 V293_create_owned_post bf table bn br Rbefore Rafter aop ir si ci result ** V293_create_internal_domain.
Proof.
 intros k target argv inputtop p identity bottom size ext options olderr oldpsp bp bc bf table bn br
 Rbefore Rafter aop ir si ci result Kind s H.
 assert(B:s |= V293_create_slot_views table bn br **
  V293_create_enabled_return k bp bc p
  (LV 108%Z @ (Tptr Tint32) |->oldpsp **
   V293_create_stack_arguments target argv inputtop options
    (Rbefore ** V293_create_owned_empty_aux bf bottom identity size ext olderr V293_create_internal_domain))
  aop ir si ci result).
 { unfold V293_create_enabled_return,V293_create_enabled_state,V293_create_enabled_locals in *.
   cbn[V293_rdy_raw_cells]in *;clear -H;sep auto. }
 eapply astar_mono in B;[ |apply V293_create_slot_drop_views|intros st HS;exact HS].
 assert(E:s |= V293_create_enabled_return k bp bc p
  (V293_create_reject_frame target argv inputtop identity bottom size ext options olderr oldpsp
   (V293_create_owned_globals bf table bn br Rbefore))aop ir si ci result).
 { unfold V293_create_enabled_return,V293_create_enabled_state,V293_create_enabled_locals,
   V293_create_reject_frame,V293_create_internal_other_parameters,V293_create_stack_arguments,
   V293_create_owned_empty_aux,V293_create_owned_globals in *.
   cbn[V293_rdy_raw_cells]in *;clear -B;sep auto. }
 pose proof(V293_create_enabled_return_cells k target argv inputtop p identity bottom size ext options
  olderr oldpsp bp bc (V293_create_owned_globals bf table bn br Rbefore)aop ir si ci result s E)as Ret.
 refine(@astar_mono _ _ _ _ _ _ s Ret);[intros st HS;exact HS| ].
 apply astar_mono;[ |intros st HS;exact HS].
 intros st HS. unfold V293_create_owned_post. left.
 apply astar_l_apure_elim in HS. destruct HS as[Code HS].
 apply astar_l_apure_intro;[exact HS| ].
 destruct Kind;subst k;cbn[V293_create_rejection_code]in Code;auto.
Qed.

Lemma V293_create_owned_failure_cells : forall target argv inputtop p identity bottom size ext options
 stack cpu bf table bn br Rbefore Rafter aop ir si ci result,
 V293_create_enabled_failure_return table p
 (V293_create_enabled_failure_kept bf stack bottom identity size ext options Rafter
  (V293_create_owned_empty_kept bn br cpu target argv inputtop V293_create_internal_domain))
 aop ir si ci result ==>
 V293_create_internal_post_cells **
 V293_create_owned_post bf table bn br Rbefore Rafter aop ir si ci result ** V293_create_internal_domain.
Proof.
 intros target argv inputtop p identity bottom size ext options stack cpu bf table bn br
 Rbefore Rafter aop ir si ci result s H.
 unfold V293_create_enabled_failure_return in H.
 apply astar_l_apure_elim in H. destruct H as[Code H].
 assert(B:s |= V293_create_slot_views table bn br **
  (V293_create_internal_pre_cells target argv inputtop p identity bottom size ext options **
   V293_create_enabled_external(Agvarenv 91%Z(Tptr V293_tcb_type)(bf,0%Z) ** Rafter)aop ir si ci **
   V293_create_internal_domain)).
 { unfold V293_create_internal_pre_cells,V293_create_internal_locals,
   V293_create_enabled_failure_state,V293_create_enabled_failure_resources,
   V293_create_enabled_failure_kept,V293_create_owned_empty_kept,V293_create_stack_kept,
   V293_create_enabled_external,V293_create_slot_views,V293_tcb_table_binding,V293_create_global_binding in *.
   clear -H;sep auto. }
 eapply astar_mono in B;[ |apply V293_create_slot_drop_views|intros st HS;exact HS].
 assert(E:s |= V293_create_internal_pre_cells target argv inputtop p identity bottom size ext options **
  (V293_create_enabled_external(V293_create_owned_globals bf table bn br Rafter)aop ir si ci **
   V293_create_internal_domain)).
 { unfold V293_create_owned_globals,V293_create_enabled_external in *;clear -B;sep auto. }
 eapply astar_mono in E;[ |apply V293_create_internal_pre_to_post|intros st HS;exact HS].
 refine(@astar_mono _ _ _ _ _ _ s E);[intros st HS;exact HS| ].
 apply astar_mono;[ |intros st HS;exact HS].
 intros st HS. unfold V293_create_owned_post. right.
 apply astar_l_apure_intro;[exact HS|exact Code].
Qed.

(* Whole unchanged function body, with a task-context (counter0) pool.
   A typed slot value is read after entry; it is not fixed by the caller. *)
Theorem V293_OSTaskCreateExt_enabled_owned_body : forall Spec sd li I tid hook f
 bp bc bf table bn br p cpu K Rbefore Rafter aop ir si ci
 (BeforeGood:GoodFunAsrt Rbefore)(AfterGood:GoodFunAsrt Rafter)
 target argv inputtop options stack oldpsp bottom identity size ext olderr running sched,
 p<256 -> (gettopis si<=INUM)%nat ->
 GoodFrm Rbefore -> GoodFrm Rafter ->
 V293_stack_argument_valid argv inputtop options ->
 V293_tcb_init_values_valid stack bottom identity size ext options ->
 (Rbefore ==> CurLINV li tid) -> (Rafter ==> CurLINV li tid) ->
 (p<13 -> Aisr ir ** invlth_isr I 0(gettopis si) <==>
  Aisr ir ** V293_create_owned_pool table(br,Int.zero)p
   (Amapsto(bn,0%Z)Tint8 true(V293_byteval 0) ** K)) ->
 let before:=@mkfunasrt (V293_create_enabled_external Rbefore aop ir si ci)
   (V293_create_enabled_external_good Rbefore aop ir si ci BeforeGood) in
 let after:=@mkfunasrt (V293_create_enabled_external Rafter aop ir si ci)
   (V293_create_enabled_external_good Rafter aop ir si ci AfterGood) in
 Spec hook=Some(V293_create_stack_resource_fpre before(V293_create_stack_values target argv inputtop options),
 V293_create_stack_resource_fpost after(V293_create_stack_values target argv inputtop options)stack,
 (Tptr Tint32,rev V293_stack_argument_types)) ->
 Spec f=Some(V293_tcb_enabled_fpre bf Rafter aop ir si ci AfterGood,
  V293_tcb_enabled_fpost bf Rafter aop ir si ci AfterGood,(Tint8,rev V293_TCBInit_argument_types)) ->
 InfRules Spec sd li I
 (fun result=>V293_create_internal_post_cells **
  V293_create_owned_post bf table bn br Rbefore Rafter aop ir si ci result ** V293_create_internal_domain)Afalse
 (V293_create_enabled_state bp bc p cpu
  (V293_create_slot_views table bn br **
   (LV 108%Z @ (Tptr Tint32) |->oldpsp **
    V293_create_stack_arguments target argv inputtop options
     (Rbefore ** V293_create_owned_empty_aux bf bottom identity size ext olderr V293_create_internal_domain)))
  aop ir si ci)
 (V293_CreateExt_body 92%Z 99%Z 97%Z running sched hook f)Afalse tid.
Proof.
 intros Spec sd li I tid hook f bp bc bf table bn br p cpu K Rbefore Rafter aop ir si ci
 BeforeGood AfterGood target argv inputtop options stack oldpsp bottom identity size ext olderr running sched
 PBound Bound BeforeFrame AfterFrame StackValid TCBValid Before After Borrow before after Hook TCB.
 set(F:=LV 108%Z @ (Tptr Tint32) |->oldpsp **
  V293_create_stack_arguments target argv inputtop options
   (Rbefore ** V293_create_owned_empty_aux bf bottom identity size ext olderr V293_create_internal_domain)).
 fold F.
 assert(Frame:GoodFrm F).
 { unfold F,V293_create_stack_arguments,V293_create_owned_empty_aux,
   Alvarmapsto,Alvarenv',Aptrmapsto. cbn[GoodFrm].
   pose proof V293_create_internal_domain_good;tauto. }
 assert(HR:F ==> CurLINV li tid).
 { unfold F. apply V293_star_CurLINV_r. unfold V293_create_stack_arguments.
   do 4 apply V293_star_CurLINV_r. apply V293_star_CurLINV_l;exact Before. }
 rewrite V293_create_owned_empty_tail_source.
 eapply seq_rule.
 { apply V293_create_enabled_cpu. apply V293_star_CurLINV_r;exact HR. }
 destruct(Nat.lt_ge_cases p 13)as[Range|Bad].
 - eapply seq_rule.
   { apply V293_create_reject_if_false. intros s H.
     exact(V293_create_enabled_priority V293_create_occupied_priority bp bc p 0
      (Vint32 Int.zero)(V293_create_slot_views table bn br ** F)aop ir si ci s Range H). }
   eapply seq_rule.
   { eapply V293_create_owned_initial_enter;[exact Bound|exact Frame|intros st HS;apply(Borrow Range);exact HS]. }
   apply ex_intro_rule. intro v.
   eapply conseq_rule with(p:=V293_create_owned_acquired bp bc table bn br p
    (Vint32 Int.zero)v K F aop ir si ci ** [|rule_type_val_match(Tptr V293_tcb_type)v=true|]);
    [intros s H;sep auto|intros s H;exact H| ].
   apply pure_split_rule. intro Typed.
   destruct v;try discriminate.
   + eapply conseq_rule;[apply V293_create_owned_acquired_null|intros s H;exact H| ].
     unfold F.
     eapply r_conseq_rule with(r:=V293_create_enabled_failure_return table p
      (V293_create_enabled_failure_kept bf stack bottom identity size ext options Rafter
       (V293_create_owned_empty_kept bn br(Vint32 Int.zero)target argv inputtop V293_create_internal_domain))
      aop ir si ci)(ri:=Afalse).
     * intro result;apply V293_create_owned_failure_cells.
     * intros s H;exact H.
     * eapply V293_OSTaskCreateExt_owned_empty_critical_tail;try eassumption.
       -- apply V293_create_internal_domain_good.
       -- intros st HS;apply(Borrow Range);exact HS.
       -- intros st HS;apply(Borrow Range);exact HS.
   + destruct a as[ab ao]. unfold V293_create_owned_empty_tail.
     eapply seq_rule.
     { apply V293_create_reject_if_false. intros s H.
       exact(proj1(V293_create_owned_acquired_guards _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Range Typed H)). }
     eapply seq_rule.
     { apply V293_create_reject_if_false. intros s H.
       exact(proj2(V293_create_owned_acquired_guards _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Range Typed H)). }
     unfold V293_TaskCreateExt_occupied.
     eapply seq_rule.
     { eapply V293_create_owned_initial_exit;[exact Typed|exact Frame|exact HR|intros st HS;apply(Borrow Range);exact HS]. }
     eapply r_conseq_rule with(r:=V293_create_enabled_return V293_create_occupied_priority bp bc p
      (V293_create_slot_views table bn br ** F)aop ir si ci)(ri:=Afalse).
     * intro result;unfold F;apply V293_create_owned_reject_cells;right;reflexivity.
     * intros s H;exact H.
     * apply(V293_create_enabled_ret _ _ _ _ _ V293_create_occupied_priority).
 - eapply seq_rule with(p':=Afalse);[ |apply pfalse_rule].
   apply V293_create_reject_if_true.
   + intros s H. apply(V293_create_enabled_priority V293_create_bad_priority bp bc p 0
      (Vint32 Int.zero)(V293_create_slot_views table bn br ** F)aop ir si ci s);[split;lia|exact H].
   + eapply r_conseq_rule with(r:=V293_create_enabled_return V293_create_bad_priority bp bc p
      (V293_create_slot_views table bn br ** F)aop ir si ci)(ri:=Afalse).
     * intro result;unfold F;apply V293_create_owned_reject_cells;left;reflexivity.
     * intros s H;exact H.
     * apply(V293_create_enabled_ret _ _ _ _ _ V293_create_bad_priority).
Qed.

Lemma V293_create_owned_entry : forall target argv inputtop p identity bottom size ext options
 cpu err psp bp bc bf table bn br R aop ir si ci,
 (Alvarenv 101%Z Tint8(bp,0%Z) ** Amapsto(bp,0%Z)Tint8 true(V293_byteval p)) **
 ((Alvarenv 109%Z Tint32(bc,0%Z) ** Amapsto(bc,0%Z)Tint32 true cpu) **
 (LV 209%Z @ Tint8 |->err ** LV 108%Z @ (Tptr Tint32) |->psp **
 (V293_create_internal_other_parameters target argv inputtop identity bottom size ext options **
 (V293_create_enabled_external(V293_create_owned_globals bf table bn br R)aop ir si ci **
  V293_create_internal_domain)))) ==>
 V293_create_enabled_state bp bc p cpu
 (V293_create_slot_views table bn br **
  (LV 108%Z @ (Tptr Tint32) |->psp **
   V293_create_stack_arguments target argv inputtop options
    (R ** V293_create_owned_empty_aux bf bottom identity size ext err V293_create_internal_domain)))
 aop ir si ci.
Proof.
 intros target argv inputtop p identity bottom size ext options cpu err psp bp bc bf table bn br R aop ir si ci s H.
 assert(B:s |= (V293_create_slot_globals table bn br ** V293_create_internal_domain) **
 ((Alvarenv 101%Z Tint8(bp,0%Z) ** Amapsto(bp,0%Z)Tint8 true(V293_byteval p)) **
 ((Alvarenv 109%Z Tint32(bc,0%Z) ** Amapsto(bc,0%Z)Tint32 true cpu) **
 (LV 209%Z @ Tint8 |->err ** LV 108%Z @ (Tptr Tint32) |->psp **
 V293_create_internal_other_parameters target argv inputtop identity bottom size ext options **
 V293_create_enabled_external(Agvarenv 91%Z(Tptr V293_tcb_type)(bf,0%Z) ** R)aop ir si ci)))).
 { unfold V293_create_enabled_external,V293_create_owned_globals in *;clear -H;sep auto. }
 eapply astar_mono in B;[ |apply V293_create_slot_global_views|intros st HS;exact HS].
 unfold V293_create_enabled_state,V293_create_enabled_locals,V293_create_enabled_external,
 V293_create_owned_empty_aux,V293_create_stack_arguments,V293_create_internal_other_parameters in *.
 cbn[V293_rdy_raw_cells]in *;clear -B;sep auto.
Qed.

Theorem V293_OSTaskCreateExt_enabled_owned_resources : forall Spec sd li I tid hook f
 bf table bn br p K Rbefore Rafter aop ir si ci
 (BeforeGood:GoodFunAsrt Rbefore)(AfterGood:GoodFunAsrt Rafter)
 target argv inputtop options stack bottom identity size ext running sched,
 p<256 -> (gettopis si<=INUM)%nat ->
 GoodFrm Rbefore -> GoodFrm Rafter ->
 V293_stack_argument_valid argv inputtop options ->
 V293_tcb_init_values_valid stack bottom identity size ext options ->
 (Rbefore ==> CurLINV li tid) -> (Rafter ==> CurLINV li tid) ->
 (p<13 -> Aisr ir ** invlth_isr I 0(gettopis si) <==>
  Aisr ir ** V293_create_owned_pool table(br,Int.zero)p
   (Amapsto(bn,0%Z)Tint8 true(V293_byteval 0) ** K)) ->
 let before:=@mkfunasrt (V293_create_enabled_external Rbefore aop ir si ci)
   (V293_create_enabled_external_good Rbefore aop ir si ci BeforeGood) in
 let after:=@mkfunasrt (V293_create_enabled_external Rafter aop ir si ci)
   (V293_create_enabled_external_good Rafter aop ir si ci AfterGood) in
 Spec hook=Some(V293_create_stack_resource_fpre before(V293_create_stack_values target argv inputtop options),
 V293_create_stack_resource_fpost after(V293_create_stack_values target argv inputtop options)stack,
 (Tptr Tint32,rev V293_stack_argument_types)) ->
 Spec f=Some(V293_tcb_enabled_fpre bf Rafter aop ir si ci AfterGood,
  V293_tcb_enabled_fpost bf Rafter aop ir si ci AfterGood,(Tint8,rev V293_TCBInit_argument_types)) ->
 InfRules Spec sd li I
 (fun result=>V293_create_internal_post_cells **
  V293_create_owned_post bf table bn br Rbefore Rafter aop ir si ci result ** V293_create_internal_domain)Afalse
 (V293_create_internal_pre_cells target argv inputtop p identity bottom size ext options **
  V293_create_enabled_external(V293_create_owned_globals bf table bn br Rbefore)aop ir si ci **
  V293_create_internal_domain)
 (V293_CreateExt_body 92%Z 99%Z 97%Z running sched hook f)Afalse tid.
Proof.
 intros Spec sd li I tid hook f bf table bn br p K Rbefore Rafter aop ir si ci
 BeforeGood AfterGood target argv inputtop options stack bottom identity size ext running sched
 PBound Bound BeforeFrame AfterFrame StackValid TCBValid Before After Borrow before after Hook TCB.
 eapply conseq_rule;[apply V293_create_internal_unpack|intros s H;exact H| ].
 apply ex_intro_rule. intro cpu. apply ex_intro_rule. intro err.
 apply ex_intro_rule. intro psp. apply ex_intro_rule. intro bp. apply ex_intro_rule. intro bc.
 eapply conseq_rule;[apply V293_create_owned_entry|intros s H;exact H| ].
 eapply V293_OSTaskCreateExt_enabled_owned_body with(K:=K);eassumption.
Qed.

(* Stable upper-layer interface: standard nine arguments and three locals. *)
Theorem V293_OSTaskCreateExt_enabled_owned_contract : forall P creator Spec sd li I tid hook f
 bf table bn br p K Rbefore Rafter aop ir si ci
 (BeforeGood:GoodFunAsrt Rbefore)(AfterGood:GoodFunAsrt Rafter)
 target argv inputtop options stack bottom identity size ext running sched vl lg pre post,
 p<256 -> (gettopis si<=INUM)%nat ->
 GoodFrm Rbefore -> GoodFrm Rafter ->
 V293_stack_argument_valid argv inputtop options ->
 V293_tcb_init_values_valid stack bottom identity size ext options ->
 (Rbefore ==> CurLINV li tid) -> (Rafter ==> CurLINV li tid) ->
 (p<13 -> Aisr ir ** invlth_isr I 0(gettopis si) <==>
  Aisr ir ** V293_create_owned_pool table(br,Int.zero)p
   (Amapsto(bn,0%Z)Tint8 true(V293_byteval 0) ** K)) ->
 let before:=@mkfunasrt (V293_create_enabled_external Rbefore aop ir si ci)
   (V293_create_enabled_external_good Rbefore aop ir si ci BeforeGood) in
 let after:=@mkfunasrt (V293_create_enabled_external Rafter aop ir si ci)
   (V293_create_enabled_external_good Rafter aop ir si ci AfterGood) in
 Spec hook=Some(V293_create_stack_resource_fpre before(V293_create_stack_values target argv inputtop options),
 V293_create_stack_resource_fpost after(V293_create_stack_values target argv inputtop options)stack,
 (Tptr Tint32,rev V293_stack_argument_types)) ->
 Spec f=Some(V293_tcb_enabled_fpre bf Rafter aop ir si ci AfterGood,
  V293_tcb_enabled_fpost bf Rafter aop ir si ci AfterGood,(Tint8,rev V293_TCBInit_argument_types)) ->
 P creator=Some(V293_CreateExt_function 92%Z 99%Z 97%Z running sched hook f) ->
 Some pre=BuildPreI P creator vl lg
 (V293_create_enabled_fpre target argv inputtop p identity bottom size ext options
  (V293_create_owned_globals bf table bn br Rbefore)aop ir si ci
  (V293_create_owned_globals_good bf table bn br Rbefore BeforeGood))tid ->
 Some post=BuildRetI P creator vl lg
 (V293_create_owned_fpost bf table bn br Rbefore Rafter aop ir si ci BeforeGood AfterGood)tid ->
 InfRules Spec sd li I post Afalse pre
 (V293_CreateExt_body 92%Z 99%Z 97%Z running sched hook f)Afalse tid.
Proof.
 intros P creator Spec sd li I tid hook f bf table bn br p K Rbefore Rafter aop ir si ci
 BeforeGood AfterGood target argv inputtop options stack bottom identity size ext running sched vl lg pre post
 PBound Bound BeforeFrame AfterFrame StackValid TCBValid Before After Borrow before after Hook TCB Code Pre Post.
 unfold BuildPreI in Pre. rewrite Code in Pre. cbn[V293_CreateExt_function]in Pre.
 destruct(dl_vl_match V293_CreateExt_parameters(rev vl))eqn:Typed;[ |discriminate].
 fold V293_create_internal_declarations in Pre.
 destruct(buildp V293_create_internal_declarations vl)as[owned | ]eqn:Owned;[ |discriminate].
 change(Some pre=Some(owned **
 ([|rev vl=V293_create_internal_values target argv inputtop p identity bottom size ext options|] **
 V293_create_enabled_external(V293_create_owned_globals bf table bn br Rbefore)aop ir si ci) **
 V293_create_internal_domain))in Pre.
 inversion Pre;subst pre.
 unfold BuildRetI in Post. rewrite Code in Post.
 change(Some post=Some(fun result=>V293_create_internal_post_cells **
 V293_create_owned_post bf table bn br Rbefore Rafter aop ir si ci result ** V293_create_internal_domain))in Post.
 inversion Post;subst post.
 eapply conseq_rule with(p:=(owned **
 V293_create_enabled_external(V293_create_owned_globals bf table bn br Rbefore)aop ir si ci **
 V293_create_internal_domain) **
 [|rev vl=V293_create_internal_values target argv inputtop p identity bottom size ext options|]).
 - intros s H;clear -H;sep auto.
 - intros s H;exact H.
 - apply pure_split_rule. intro Args.
   assert(VL:vl=rev(V293_create_internal_values target argv inputtop p identity bottom size ext options)).
   { rewrite <-Args. symmetry;apply rev_involutive. }
   subst vl. rewrite V293_create_internal_buildp in Owned. inversion Owned;subst owned.
   eapply V293_OSTaskCreateExt_enabled_owned_resources with(BeforeGood:=BeforeGood)(AfterGood:=AfterGood)(K:=K);eassumption.
Qed.
