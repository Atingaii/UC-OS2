(* Original between-Hook priority publication. Enabled caller owns only its
   reservation half; the shared half is borrowed/reunited by encrit1. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEnabledHook.
Require Import CertiOS.certiucos.v293.proofs.V293TCBAllocatedFields.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.proofs.V293TCBHookCall.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEmptyEnabled.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitFunction.
Require Import CertiOS.certiucos.v293.code.V293OSTCBPublish.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateReservationOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPriorityHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFieldsHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition V293_tcb_priority_bindings table bprio bp :=
 (Alvarenv 101%Z Tint8(bprio,0%Z) //\\ Alvarenv 108%Z(Tptr V293_tcb_type)(bp,0%Z)) **
 V293_tcb_table_binding table.
Definition V293_tcb_priority_locals bprio bp p pc : list V293_record_cell :=
 [((bprio,0%Z),Tint8,V293_byteval p);((bp,0%Z),Tptr V293_tcb_type,pc)].
Definition V293_tcb_priority_resources table bprio bp p pc R :=
 V293_rdy_raw_cells(V293_tcb_priority_locals bprio bp p pc)
 (V293_tcb_priority_bindings table bprio bp ** R).
Definition V293_tcb_priority_state table bprio bp p pc R aop ir ie si ci :=
 <||aop||> ** OS[ir,ie,si,ci] ** V293_tcb_priority_resources table bprio bp p pc R.
Lemma V293_tcb_priority_good : forall table bprio bp p pc R,
 GoodFrm R -> GoodFrm(V293_tcb_priority_resources table bprio bp p pc R).
Proof. intros. cbn[V293_tcb_priority_resources V293_tcb_priority_locals V293_tcb_priority_bindings V293_tcb_table_binding V293_rdy_raw_cells GoodFrm];tauto. Qed.
Lemma V293_tcb_priority_linv : forall table bprio bp p pc R li tid,
 (R ==> CurLINV li tid) -> V293_tcb_priority_resources table bprio bp p pc R ==> CurLINV li tid.
Proof. intros table bprio bp p pc R li tid HR. unfold V293_tcb_priority_resources. apply V293_raw_cells_CurLINV. apply V293_star_CurLINV_r;exact HR. Qed.

Lemma V293_tcb_priority_env : forall table bprio bp p pc R s,
 s |= V293_tcb_priority_resources table bprio bp p pc R ->
 get(getlenv s)101%Z=Some(bprio,Tint8) /\
 get(getlenv s)108%Z=Some(bp,Tptr V293_tcb_type) /\
 get(getlenv s)92%Z=None /\ get(getgenv s)92%Z=Some(table,Tarray(Tptr V293_tcb_type)13).
Proof.
 intros table bprio bp p pc R s H.
 eapply V293_raw_cells_frame_env with(E:=fun ge le=>
 get le 101%Z=Some(bprio,Tint8) /\ get le 108%Z=Some(bp,Tptr V293_tcb_type) /\
 get le 92%Z=None /\ get ge 92%Z=Some(table,Tarray(Tptr V293_tcb_type)13));[ |exact H].
 intros st HS. unfold V293_tcb_priority_bindings in HS.
 assert(L:get(getlenv st)101%Z=Some(bprio,Tint8) /\ get(getlenv st)108%Z=Some(bp,Tptr V293_tcb_type)).
 { refine(V293_star_env_l _ _ (fun ge le=>get le 101%Z=Some(bprio,Tint8) /\ get le 108%Z=Some(bp,Tptr V293_tcb_type)) _ st HS). intros st1 H1.
   refine(V293_star_env_l _ _ (fun ge le=>get le 101%Z=Some(bprio,Tint8) /\ get le 108%Z=Some(bp,Tptr V293_tcb_type)) _ st1 H1). intros st2 [P Q].
   destruct P as[b1[E1[B1 _]]]. destruct Q as[b2[E2[B2 _]]]. inversion B1;inversion B2;subst;auto. }
 assert(G:get(getlenv st)92%Z=None /\ get(getgenv st)92%Z=Some(table,Tarray(Tptr V293_tcb_type)13)).
 { refine(V293_star_env_l _ _ (fun ge le=>get le 92%Z=None /\ get ge 92%Z=Some(table,Tarray(Tptr V293_tcb_type)13)) _ st HS). intros st1 H1.
   refine(V293_star_env_r _ _ (fun ge le=>get le 92%Z=None /\ get ge 92%Z=Some(table,Tarray(Tptr V293_tcb_type)13)) _ st1 H1). intros st2 H2. apply V293_tcb_table_binding_env;exact H2. }
 tauto.
Qed.

Lemma V293_tcb_priority_enter : forall Spec sd li I r ri tid table reserved bprio bp p pc K R aop ir si ci,
 (gettopis si<=INUM)%nat -> GoodFrm R ->
 (Aisr ir ** invlth_isr I 0(gettopis si) ==> Aisr ir ** V293_create_owned_pool table reserved p K) ->
 InfRules Spec sd li I r ri
 (V293_tcb_priority_state table bprio bp p pc(V293_create_owned_share table reserved p ** R)aop ir true si ci)
 (sprim encrit)
 (V293_tcb_priority_state table bprio bp p pc
 (Amapsto(table,(4*Z.of_nat p)%Z)(Tptr V293_tcb_type)true(Vptr reserved) ** (K ** R))aop ir false si(true::ci))tid.
Proof.
 intros Spec sd li I r ri tid table reserved bprio bp p pc K R aop ir si ci Bound Frame Open.
 unfold V293_tcb_priority_state. eapply conseq_rule with
 (p:=<||aop||> ** OS[ir,true,si,ci] ** ATopis(gettopis si) ** [|(gettopis si<=INUM)%nat|] **
 V293_tcb_priority_resources table bprio bp p pc(V293_create_owned_share table reserved p ** R))
 (q:=<||aop||> ** OS[ir,false,si,true::ci] ** invlth_isr I 0(gettopis si) **
 V293_tcb_priority_resources table bprio bp p pc(V293_create_owned_share table reserved p ** R)).
 - intros s H. assert(S:s |= Ais si ** Atrue)by(clear -H;sep auto).
   pose proof(V293_time_topis si Atrue s S)as Top. apply astar_l_atopis_elim in Top.
   destruct Top as[Top _]. pose proof(@astar_l_atopis_intro s(gettopis si)_ H Top)as HT.
   clear -HT Bound;sep auto.
 - intros s H.
   assert(B:s |= (Aisr ir ** invlth_isr I 0(gettopis si)) **
   (<||aop||> ** Aie false ** Ais si ** Acs(true::ci) **
   V293_tcb_priority_resources table bprio bp p pc(V293_create_owned_share table reserved p ** R)))by(clear -H;sep auto).
   eapply astar_mono in B;[ |exact Open|intros st HS;exact HS].
   unfold V293_create_owned_pool,V293_create_owned_share,V293_tcb_priority_resources in B.
   cbn[V293_tcb_priority_locals V293_rdy_raw_cells]in B.
   assert(C:s |= (V293_reservation_owner(table,(4*Z.of_nat p)%Z)reserved **
   V293_reservation_pool(table,(4*Z.of_nat p)%Z)reserved) **
   (<||aop||> ** OS[ir,false,si,true::ci] ** V293_tcb_priority_resources table bprio bp p pc(K ** R))).
   { unfold V293_tcb_priority_resources;cbn[V293_tcb_priority_locals V293_rdy_raw_cells];clear -B;sep auto. }
   eapply astar_mono in C;[ |apply V293_reservation_reacquire|intros st HS;exact HS].
   unfold V293_tcb_priority_resources;cbn[V293_tcb_priority_locals V293_rdy_raw_cells];clear -C;sep auto.
 - apply encrit1_rule. apply V293_tcb_priority_good.
   unfold V293_create_owned_share,V293_reservation_owner;cbn[GoodFrm];tauto.
Qed.

Lemma V293_tcb_priority_store : forall Spec sd li I r ri tid table bprio bp p b off old R aop ir si ci,
 p<13 -> (R ==> CurLINV li tid) ->
 InfRules Spec sd li I r ri
 (V293_tcb_priority_state table bprio bp p(Vptr(b,off))
 (Amapsto(table,(4*Z.of_nat p)%Z)(Tptr V293_tcb_type)true old ** R)aop ir false si ci)
 (sassign(earrayelem(evar 92%Z)(evar 101%Z))(evar 108%Z))
 (V293_tcb_priority_state table bprio bp p(Vptr(b,off))
 (Amapsto(table,(4*Z.of_nat p)%Z)(Tptr V293_tcb_type)true(Vptr(b,off)) ** R)aop ir false si ci)tid.
Proof.
 intros Spec sd li I r ri tid table bprio bp p b off old R aop ir si ci Range HR.
 unfold V293_tcb_priority_state. eapply conseq_rule with
 (p:=<||aop||> ** V293_rdy_raw_cells
 (((table,(4*Z.of_nat p)%Z),Tptr V293_tcb_type,old)::V293_tcb_priority_locals bprio bp p(Vptr(b,off)))
 (OS[ir,false,si,ci] ** (V293_tcb_priority_bindings table bprio bp ** R)))
 (q:=<||aop||> ** V293_rdy_raw_cells
 (((table,(4*Z.of_nat p)%Z),Tptr V293_tcb_type,Vptr(b,off))::V293_tcb_priority_locals bprio bp p(Vptr(b,off)))
 (OS[ir,false,si,ci] ** (V293_tcb_priority_bindings table bprio bp ** R))).
 - intros s H. unfold V293_tcb_priority_resources in H;cbn[V293_tcb_priority_locals V293_rdy_raw_cells]in *;clear -H;sep auto.
 - intros s H. unfold V293_tcb_priority_resources;cbn[V293_tcb_priority_locals V293_rdy_raw_cells]in *;clear -H;sep auto.
 - eapply(V293_raw_assign_hoare Spec sd li I r ri tid aop [] (table,(4*Z.of_nat p)%Z)
   (Tptr V293_tcb_type)old _ (Vptr(b,off)) _ _ (Tptr V293_tcb_type)).
   + cbn[snd]. apply Int.unsigned_repr. change(0<=4*Z.of_nat p<=4294967295)%Z;lia.
   + apply eq_vptr. do 2 eexists;split;reflexivity.
   + intros s H.
     assert(C:s |= V293_tcb_priority_resources table bprio bp p(Vptr(b,off)) R ** Atrue).
     { unfold V293_tcb_priority_resources;cbn[app V293_tcb_priority_locals V293_rdy_raw_cells]in *;clear -H;sep auto. }
     assert(E:get(getlenv s)101%Z=Some(bprio,Tint8) /\
       get(getlenv s)108%Z=Some(bp,Tptr V293_tcb_type) /\
       get(getlenv s)92%Z=None /\ get(getgenv s)92%Z=Some(table,Tarray(Tptr V293_tcb_type)13)).
     { eapply V293_star_env_l;[ |exact C]. intros st HS. eapply V293_tcb_priority_env;exact HS. }
     destruct E as[PriorityLocal[PointerLocal[TableLocal TableGlobal]]].
     destruct s as [[[[[[ge le] M] irq] aux] O] op].
     cbn[getlenv getgenv get_smem get_lenv get_genv]in *.
     pose proof(V293_byte_type p ltac:(lia))as PriorityTyped.
     cbn[app]in H. V293_tcb_init_read H 1%nat PriorityRead.
     V293_tcb_init_read H 2%nat PointerRead.
     destruct(V293_rekey_array_address ge le M 92%Z 101%Z V293_tcb_type table bprio p
       TableLocal TableGlobal PriorityLocal PriorityRead Range)as[SlotType SlotAddress].
     split.
     * cbn[sat getsmem fst snd]. split;assumption.
     * cbn[sat getsmem get_smem]. repeat split;first[solve[V293_rdy_eval]|discriminate].
   + repeat apply V293_star_CurLINV_r;exact HR.
Qed.

Lemma V293_reservation_pool_pointer : forall a reserved pointer,
 pointer<>reserved -> Amapsto a(Tptr V293_tcb_type)true(Vptr pointer) ==>
 V293_reservation_pool a reserved.
Proof.
 intros a reserved pointer Distinct s H. exists(Vptr pointer).
 apply astar_l_apure_intro;[ |reflexivity].
 unfold V293_reservation_permission. rewrite tidspec.neq_beq_false by exact Distinct.
 exact H.
Qed.

Lemma V293_tcb_priority_exit : forall Spec sd li I r ri tid table reserved bprio bp p pointer K R aop ir si ci,
 pointer<>reserved -> GoodFrm R -> (R ==> CurLINV li tid) ->
 (Aisr ir ** V293_create_owned_pool table reserved p K ==> Aisr ir ** invlth_isr I 0(gettopis si)) ->
 InfRules Spec sd li I r ri
 (V293_tcb_priority_state table bprio bp p(Vptr pointer)
 (Amapsto(table,(4*Z.of_nat p)%Z)(Tptr V293_tcb_type)true(Vptr pointer) ** (K ** R))aop ir false si(true::ci))
 (sprim excrit)
 (V293_tcb_priority_state table bprio bp p(Vptr pointer)R aop ir true si ci)tid.
Proof.
 intros Spec sd li I r ri tid table reserved bprio bp p pointer K R aop ir si ci Distinct Frame HR Close.
 eapply conseq_rule with
 (p:=<||aop||> ** OS[ir,false,si,true::ci] ** ATopis(gettopis si) ** invlth_isr I 0(gettopis si) **
 V293_tcb_priority_resources table bprio bp p(Vptr pointer)R)
 (q:=<||aop||> ** OS[ir,true,si,ci] ** V293_tcb_priority_resources table bprio bp p(Vptr pointer)R).
 - intros s H.
   assert(B:s |= Amapsto(table,(4*Z.of_nat p)%Z)(Tptr V293_tcb_type)true(Vptr pointer) **
   (Aisr ir ** K ** <||aop||> ** Aie false ** Ais si ** Acs(true::ci) **
   V293_tcb_priority_resources table bprio bp p(Vptr pointer)R)).
   { unfold V293_tcb_priority_state,V293_tcb_priority_resources in *;
     cbn[V293_tcb_priority_locals V293_rdy_raw_cells]in *;clear -H;sep auto. }
   eapply astar_mono in B;[ |apply V293_reservation_pool_pointer;exact Distinct|intros st HS;exact HS].
   assert(C:s |= (Aisr ir ** V293_create_owned_pool table reserved p K) **
   (<||aop||> ** Aie false ** Ais si ** Acs(true::ci) ** V293_tcb_priority_resources table bprio bp p(Vptr pointer)R)).
   { unfold V293_create_owned_pool;clear -B;sep auto. }
   eapply astar_mono in C;[ |exact Close|intros st HS;exact HS].
   assert(S:s |= Ais si ** Atrue)by(clear -C;sep auto).
   pose proof(V293_time_topis si Atrue s S)as Top.
   apply astar_l_atopis_elim in Top. destruct Top as[Top _].
   pose proof(@astar_l_atopis_intro s(gettopis si)_ C Top)as HT. clear -HT;sep auto.
 - unfold V293_tcb_priority_state;intros s H;exact H.
 - apply excrit1_rule;[apply V293_tcb_priority_good;exact Frame|apply V293_tcb_priority_linv;exact HR].
Qed.

(* Stable real right-associated continuation: the old slot is not privately
   owned while IE=true. Freshness of the allocated pointer is still explicit. *)
Theorem V293_OS_TCBInit_owned_priority_then : forall Spec sd li I r ri tid table reserved bprio bp p b off K R aop ir si ci tail Q,
 p<13 -> (b,off)<>reserved -> (gettopis si<=INUM)%nat -> GoodFrm R -> (R ==> CurLINV li tid) ->
 (Aisr ir ** invlth_isr I 0(gettopis si) ==> Aisr ir ** V293_create_owned_pool table reserved p K) ->
 (Aisr ir ** V293_create_owned_pool table reserved p K ==> Aisr ir ** invlth_isr I 0(gettopis si)) ->
 InfRules Spec sd li I r ri
 (V293_tcb_priority_state table bprio bp p(Vptr(b,off))R aop ir true si ci)tail Q tid ->
 InfRules Spec sd li I r ri
 (V293_tcb_priority_state table bprio bp p(Vptr(b,off))(V293_create_owned_share table reserved p ** R)aop ir true si ci)
 (sseq(sprim encrit)(sseq(sassign(earrayelem(evar 92%Z)(evar 101%Z))(evar 108%Z))
 (sseq(sprim excrit)tail)))Q tid.
Proof.
 intros Spec sd li I r ri tid table reserved bprio bp p b off K R aop ir si ci tail Q Range Distinct Bound Frame HR Open Close Rest.
 eapply seq_rule;[apply V293_tcb_priority_enter with(reserved:=reserved)(K:=K);assumption| ].
 eapply seq_rule;[apply V293_tcb_priority_store;[exact Range|apply V293_star_CurLINV_r;exact HR]| ].
 eapply seq_rule;[apply V293_tcb_priority_exit with(reserved:=reserved)(K:=K);assumption|exact Rest].
Qed.
Print Assumptions V293_OS_TCBInit_owned_priority_then.

Lemma V293_tcb_priority_argument : forall table bprio bp p b off R aop ir si ci,
 V293_tcb_priority_state table bprio bp p(Vptr(b,off))R aop ir true si ci ==>
 Rvl [evar 108%Z] @ [Tptr V293_tcb_type] == [Vptr(b,off)].
Proof.
 intros table bprio bp p b off R aop ir si ci s H.
 assert(E:get(getlenv s)108%Z=Some(bp,Tptr V293_tcb_type)).
 { unfold V293_tcb_priority_state in H.
   refine(V293_star_env_r _ _ (fun ge le=>get le 108%Z=Some(bp,Tptr V293_tcb_type)) _ s H). intros st HS.
   refine(V293_star_env_r _ _ (fun ge le=>get le 108%Z=Some(bp,Tptr V293_tcb_type)) _ st HS). intros st1 H1.
   apply V293_tcb_priority_env in H1;tauto. }
 assert(Read:load(Tptr V293_tcb_type)(getmem s)(bp,0%Z)=Some(Vptr(b,off))).
 { unfold V293_tcb_priority_state in H.
   eapply V293_star_load_r;[ |exact H]. intros st HS.
   eapply V293_star_load_r;[ |exact HS]. intros st1 H1.
   unfold V293_tcb_priority_resources in H1.
   destruct st1 as [[[[[[ge le] M] irq] aux] O] op].
   V293_tcb_init_read H1 1%nat Load. exact Load. }
 destruct s as [[[[[[ge le] M] irq] aux] O] op].
 change(get le 108%Z=Some(bp,Tptr V293_tcb_type))in E.
 change(load(Tptr V293_tcb_type)M(bp,0%Z)=Some(Vptr(b,off)))in Read.
 cbn[sat getsmem evalexprlist evaltype evalval evaladdr get_smem get_lenv].
 cbv delta[env var memory.ident Modules.ident]in *. rewrite E.
 repeat split;first[assumption|reflexivity|discriminate].
Qed.

(* The same typed Hook contract as stage117. Caller table/local bindings remain
   in the GoodFrm frame, never smuggled into GoodFunAsrt callee resources. *)
Lemma V293_tcb_priority_first_hook : forall Spec sd li I r ri tid f table bprio bp p b off next
 top bottom identity size ext options R F aop ir si ci (good:GoodFunAsrt R),
 GoodFrm F -> (R ==> CurLINV li tid) ->
 Spec f=Some(V293_tcb_enabled_hook_fpre p top bottom identity size ext options R aop ir si ci tid good,
 V293_tcb_enabled_hook_fpost p top bottom identity size ext options R aop ir si ci tid good,
 (Tvoid,[Tptr V293_tcb_type])) ->
 InfRules Spec sd li I r ri
 (V293_tcb_priority_state table bprio bp p(Vptr(b,off))
 (V293_tcb_allocated_initialized b off next p top bottom identity size ext options ** (R ** F))aop ir true si ci)
 (scall f[evar 108%Z])
 (V293_tcb_priority_state table bprio bp p(Vptr(b,off))
 (V293_tcb_allocated_initialized b off next p top bottom identity size ext options ** (R ** F))aop ir true si ci)tid.
Proof.
 intros Spec sd li I r ri tid f table bprio bp p b off next top bottom identity size ext options R F aop ir si ci good Frame HR Lookup.
 set(pre:=V293_tcb_enabled_hook_fpre p top bottom identity size ext options R aop ir si ci tid good).
 set(post:=V293_tcb_enabled_hook_fpost p top bottom identity size ext options R aop ir si ci tid good).
 set(frame:=V293_tcb_priority_resources table bprio bp p(Vptr(b,off))F).
 eapply conseq_rule with
 (q:=EX result:option val,getasrt(post ([Vptr(b,off)]) result ([logic_val(Vptr(b,off));logic_val next]) tid) ** frame).
 - intros s H;exact H.
 - intros s[result H]. cbn[post V293_tcb_enabled_hook_fpost V293_hook_fpost getasrt]in H.
   unfold frame,V293_tcb_priority_state,V293_tcb_priority_resources,V293_tcb_enabled_hook_resource in *.
   cbn[V293_tcb_priority_locals V293_rdy_raw_cells]in *;clear -H;sep auto.
 - eapply call_rule with(pre:=pre)(post:=post)(vl:=[Vptr(b,off)])
   (logicl:=[logic_val(Vptr(b,off));logic_val next])(tp:=Tvoid)(tl:=[Tptr V293_tcb_type])(p:=frame).
   + apply V293_tcb_priority_good;exact Frame.
   + exact Lookup.
   + intros s H. cbn[pre V293_tcb_enabled_hook_fpre V293_hook_fpre getasrt].
     unfold frame,V293_tcb_priority_state,V293_tcb_priority_resources,V293_tcb_enabled_hook_resource in *.
     cbn[V293_tcb_priority_locals V293_rdy_raw_cells]in *;clear -H;sep auto.
   + apply V293_tcb_priority_argument.
   + reflexivity.
   + cbn[pre V293_tcb_enabled_hook_fpre V293_hook_fpre getasrt].
     apply V293_star_CurLINV_r. apply V293_tcb_enabled_hook_linv;exact HR.
   + intros s[result H]. cbn[post V293_tcb_enabled_hook_fpost V293_hook_fpost getasrt]in H.
     eapply V293_star_CurLINV_r;[apply V293_tcb_enabled_hook_linv;exact HR|exact H].
Qed.

Theorem V293_OS_TCBInit_owned_suffix_after_first_hook : forall Spec sd li I r ri tid hi hc table reserved bprio bp p b off next
 top bottom identity size ext options K R F aop ir si ci Q
 (good:GoodFunAsrt(V293_create_owned_share table reserved p ** R)),
 p<13 -> (b,off)<>reserved -> (gettopis si<=INUM)%nat -> GoodFrm R -> GoodFrm F -> (R ==> CurLINV li tid) ->
 (Aisr ir ** invlth_isr I 0(gettopis si) ==> Aisr ir ** V293_create_owned_pool table reserved p K) ->
 (Aisr ir ** V293_create_owned_pool table reserved p K ==> Aisr ir ** invlth_isr I 0(gettopis si)) ->
 Spec hi=Some(V293_tcb_enabled_hook_fpre p top bottom identity size ext options
 (V293_create_owned_share table reserved p ** R)aop ir si ci tid good,
 V293_tcb_enabled_hook_fpost p top bottom identity size ext options
 (V293_create_owned_share table reserved p ** R)aop ir si ci tid good,(Tvoid,[Tptr V293_tcb_type])) ->
 InfRules Spec sd li I r ri
 (V293_tcb_priority_state table bprio bp p(Vptr(b,off))
 (V293_tcb_allocated_initialized b off next p top bottom identity size ext options ** (R ** F))aop ir true si ci)
 (sseq(scall hc[evar 108%Z])(V293_TCB_publish 108%Z 93%Z 94%Z 95%Z 96%Z))Q tid ->
 InfRules Spec sd li I r ri
 (V293_tcb_priority_state table bprio bp p(Vptr(b,off))
 (V293_tcb_allocated_initialized b off next p top bottom identity size ext options **
 ((V293_create_owned_share table reserved p ** R) ** F))aop ir true si ci)
 (V293_TCBInit_success_suffix hi hc)Q tid.
Proof.
 intros Spec sd li I r ri tid hi hc table reserved bprio bp p b off next top bottom identity size ext options K R F aop ir si ci Q good Range Distinct Bound FrameR FrameF HR Open Close Lookup Rest.
 unfold V293_TCBInit_success_suffix. eapply seq_rule.
 - apply V293_tcb_priority_first_hook with(good:=good);[exact FrameF|apply V293_star_CurLINV_r;exact HR|exact Lookup].
 - eapply conseq_rule with
   (p:=V293_tcb_priority_state table bprio bp p(Vptr(b,off))
     (V293_create_owned_share table reserved p **
     (V293_tcb_allocated_initialized b off next p top bottom identity size ext options ** (R ** F)))aop ir true si ci).
   + intros s H. unfold V293_tcb_priority_state,V293_tcb_priority_resources in *.
     cbn[V293_tcb_priority_locals V293_rdy_raw_cells]in *;clear -H;sep auto.
   + intros s H;exact H.
   + apply V293_OS_TCBInit_owned_priority_then with(reserved:=reserved)(K:=K);try assumption.
     * cbn[V293_tcb_allocated_initialized V293_tcb_init_final_fields V293_rdy_raw_cells
       V293_tcb_allocated_remainder V293_tcb_allocated_spares V293_storage V293_storage_cell GoodFrm];tauto.
     * apply V293_star_CurLINV_r. apply V293_star_CurLINV_l;exact HR.
Qed.
Print Assumptions V293_OS_TCBInit_owned_suffix_after_first_hook.
