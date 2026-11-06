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

(* All 56 bytes except OSTCBNext; flags-ready and layout padding retained. *)
Definition V293_tcb_free_payload_cells b base : list(addr*type) :=
 [((b,(base+0)%Z),Tptr Tint32);((b,(base+50)%Z),Tint8);
  ((b,(base+48)%Z),Tint8);((b,(base+49)%Z),Tint8);
  ((b,(base+44)%Z),Tint32);((b,(base+4)%Z),Tptr Tvoid);
  ((b,(base+12)%Z),Tint32);((b,(base+8)%Z),Tptr Tint32);
  ((b,(base+16)%Z),Tint16);((b,(base+18)%Z),Tint16);
  ((b,(base+55)%Z),Tint8);((b,(base+52)%Z),Tint8);
  ((b,(base+51)%Z),Tint8);((b,(base+54)%Z),Tint8);
  ((b,(base+53)%Z),Tint8);((b,(base+28)%Z),Tcom_ptr 411%Z);
  ((b,(base+36)%Z),Tcom_ptr 412%Z);((b,(base+32)%Z),Tptr Tvoid);
  ((b,(base+24)%Z),Tcom_ptr 410%Z);((b,(base+40)%Z),Tint16);
  ((b,(base+42)%Z),Tint8);((b,(base+43)%Z),Tint8)].
Definition V293_tcb_free_payload b base := V293_storage(V293_tcb_free_payload_cells b base).

Fixpoint V293_tcb_free_chain (fuel:nat)(head:val) : asrt :=
 match head with
 | Vnull=>Aemp
 | Vptr(b,offset)=>match fuel with
   | O=>Afalse
   | S n=>[|(Int.unsigned offset+55<=Int.max_unsigned)%Z|] **
     (V293_tcb_free_payload b(Int.unsigned offset) **
      (EX next:val,[|rule_type_val_match(Tcom_ptr 410%Z)next=true|] **
       (Amapsto(b,(Int.unsigned offset+20)%Z)(Tcom_ptr 410%Z)true next **
        V293_tcb_free_chain n next)))
   end
 | _=>Afalse
 end.
Definition V293_tcb_free_pool bf :=
 EX head:val,[|rule_type_val_match(Tptr V293_tcb_type)head=true|] **
 (Amapsto(bf,0%Z)(Tptr V293_tcb_type)true head ** V293_tcb_free_chain 13 head).

Lemma V293_tcb_mapsto_precise : forall a tp v,
 precise(Amapsto a tp true v).
Proof.
 intros a tp v s M1 M2 O1 O2 H1 H2 M O HM1 HM2 HO1 HO2.
 destruct s as [[[[[[ge le] mem] ir] aux] o] op].
 change(mapstoval a tp true v M1 /\ O1=emp)in H1.
 change(mapstoval a tp true v M2 /\ O2=emp)in H2.
 destruct H1 as[[vl1[E1 P1]] O1E]. destruct H2 as[[vl2[E2 P2]] O2E].
 split;[ |congruence]. rewrite <-E1 in P1. rewrite <-E2 in P2.
 eapply ptomvallist_mem_eq;eauto.
Qed.
Lemma V293_tcb_pure_precise : forall P Q,precise Q -> precise([|P|] ** Q).
Proof.
 intros P Q Prec s M1 M2 O1 O2 H1 H2 M O HM1 HM2 HO1 HO2.
 apply astar_l_apure_elim in H1. apply astar_l_apure_elim in H2.
 eapply Prec;[exact(proj2 H1)|exact(proj2 H2)|exact HM1|exact HM2|exact HO1|exact HO2].
Qed.
Lemma V293_tcb_value_tail_precise : forall a tp (tail:val->asrt),
 (forall v,precise(tail v)) ->
 precise(EX v:val,[|rule_type_val_match tp v=true|] ** (Amapsto a tp true v ** tail v)).
Proof.
 intros a tp tail Prec s M1 M2 O1 O2 [v1 H1][v2 H2] M O HM1 HM2 HO1 HO2.
 apply astar_l_apure_elim in H1. destruct H1 as[T1 H1].
 apply astar_l_apure_elim in H2. destruct H2 as[T2 H2].
 destruct s as [[[[[[ge le] mem] ir] aux] o] op].
 assert(L1:load tp M1 a=Some v1).
 { refine (@V293_star_load_l _ _ tp a v1 _ (substmo (ge,le,mem,ir,aux,o,op) M1 O1) H1). intros st[H _]. eapply mapstoval_load;eauto. }
 assert(L2:load tp M2 a=Some v2).
 { refine (@V293_star_load_l _ _ tp a v2 _ (substmo (ge,le,mem,ir,aux,o,op) M2 O2) H2). intros st[H _]. eapply mapstoval_load;eauto. }
 pose proof(@load_mem_mono _ _ _ _ _ L1 HM1)as LM1.
 pose proof(@load_mem_mono _ _ _ _ _ L2 HM2)as LM2.
 assert(v1=v2)by congruence. subst v2.
 eapply(precise_star _ _ (V293_tcb_mapsto_precise a tp v1)(Prec v1));eauto.
Qed.
Lemma V293_tcb_free_chain_precise : forall n v,precise(V293_tcb_free_chain n v).
Proof.
 induction n as[ |n IH];intro v;destruct v;try(intros s M1 M2 O1 O2 H1;contradiction).
 - intros s M1 M2 O1 O2 H1 H2 M O HM1 HM2 HO1 HO2.
   destruct s as [[[[[[ge le] mem] ir] aux] o] op].
   change(M1=emp /\ O1=emp)in H1. change(M2=emp /\ O2=emp)in H2. intuition congruence.
 - destruct a. intros s M1 M2 O1 O2 H1;contradiction.
 - intros s M1 M2 O1 O2 H1 H2 M O HM1 HM2 HO1 HO2.
   destruct s as [[[[[[ge le] mem] ir] aux] o] op].
   change(M1=emp /\ O1=emp)in H1. change(M2=emp /\ O2=emp)in H2. intuition congruence.
 - destruct a. cbn[V293_tcb_free_chain]. apply V293_tcb_pure_precise.
   apply precise_star;[apply V293_storage_precise| ].
   apply V293_tcb_value_tail_precise. exact IH.
Qed.
Lemma V293_tcb_free_pool_precise : forall bf,precise(V293_tcb_free_pool bf).
Proof. intro bf;apply V293_tcb_value_tail_precise;apply V293_tcb_free_chain_precise. Qed.
Lemma V293_tcb_free_chain_weaken : forall n v,
 V293_tcb_free_chain n v ==> V293_tcb_free_chain(S n)v.
Proof.
 induction n as[ |n IH];intro v;destruct v;try destruct a;intros s H;cbn[V293_tcb_free_chain]in H|-*;try contradiction;try exact H.
 eapply astar_mono;[intros st HS;exact HS| |exact H].
 apply astar_mono;[intros st HS;exact HS| ].
 intros st[next HS]. exists next.
 eapply astar_mono;[intros st' H';exact H'| |exact HS].
 apply astar_mono;[intros st' H';exact H'|apply IH].
Qed.
Lemma V293_tcb_free_chain_good : forall n v,GoodInvAsrt(V293_tcb_free_chain n v).
Proof.
 induction n as[ |n IH];intro v;destruct v;try exact I;destruct a;cbn[V293_tcb_free_chain GoodInvAsrt];
 split;[exact I|split;[apply V293_storage_good| ]];intro next;split;[exact I|split;[exact I|apply IH]].
Qed.
Lemma V293_tcb_free_pool_good : forall bf,GoodInvAsrt(V293_tcb_free_pool bf).
Proof. intro bf;intro v;split;[exact I|split;[exact I|apply V293_tcb_free_chain_good]]. Qed.

Lemma V293_tcb_free_chain_frame : forall n v,GoodFrm(V293_tcb_free_chain n v).
Proof.
 induction n as[ |n IH];intro v;destruct v;try exact I;destruct a;cbn[V293_tcb_free_chain GoodFrm];
 split;[exact I|split;[apply V293_storage_frame_good| ]];intro next;split;[exact I|split;[exact I|apply IH]].
Qed.
Lemma V293_tcb_free_chain_aux_stable : forall n v ge le M ir aux O op ir' aux',
 (ge,le,M,ir,aux,O,op) |= V293_tcb_free_chain n v ->
 (ge,le,M,ir',aux',O,op) |= V293_tcb_free_chain n v.
Proof.
 induction n as[ |n IH];intros v ge le M ir aux O op ir' aux' H;
 destruct v;try destruct a;cbn[V293_tcb_free_chain]in H|-*;try contradiction;try exact H.
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
Lemma V293_tcb_free_pool_aux_stable : forall bf ge le M ir aux O op ir' aux',
 (ge,le,M,ir,aux,O,op) |= V293_tcb_free_pool bf ->
 (ge,le,M,ir',aux',O,op) |= V293_tcb_free_pool bf.
Proof.
 intros bf ge le M ir aux O op ir' aux'[head H]. exists head.
 apply astar_l_apure_elim in H. destruct H as[Typed H].
 apply astar_l_apure_intro;[ |exact Typed].
 apply sat_split in H. destruct H as(m1&m2&o1&o2&JM&JO&HP&HT).
 apply sat_split'. exists m1. exists m2. exists o1. exists o2. split;[exact JM| ]. split;[exact JO| ].
 split;[exact HP|eapply V293_tcb_free_chain_aux_stable;exact HT].
Qed.
Lemma V293_tcb_free_pool_isr : forall bf,assertion.inv_isr_prop(V293_tcb_free_pool bf).
Proof.
 intro bf. unfold assertion.inv_isr_prop. repeat split;intros;
 destruct s as [[[[[[ge le] M] ir] [[ie si] cs]] O] op];
 eapply V293_tcb_free_pool_aux_stable;exact H.
Qed.

(* Critical-section view: the head is chosen by the shared bytes, not Px. *)
Definition V293_tcb_free_critical bf bp bc pc cpu head K R aop ir si ci :=
 <||aop||> ** OS[ir,false,si,ci] **
 V293_tcb_enabled_resources bf bp bc pc cpu
 (Amapsto(bf,0%Z)(Tptr V293_tcb_type)true head **
 (V293_tcb_free_chain 13 head ** (K ** R))).
Lemma V293_tcb_free_enter : forall Spec sd li I r ri tid bf bp bc pc cpu K R aop ir si ci,
 (gettopis si<=INUM)%nat -> GoodFrm R ->
 (Aisr ir ** invlth_isr I 0(gettopis si) ==> Aisr ir ** (V293_tcb_free_pool bf ** K)) ->
 InfRules Spec sd li I r ri
 (V293_tcb_enabled_state bf bp bc pc cpu R aop ir si ci)(sprim encrit)
 (EX head:val,[|rule_type_val_match(Tptr V293_tcb_type)head=true|] **
 V293_tcb_free_critical bf bp bc pc cpu head K R aop ir si(true::ci))tid.
Proof.
 intros Spec sd li I r ri tid bf bp bc pc cpu K R aop ir si ci Bound Frame Open.
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
   unfold V293_tcb_free_pool in B. sep normal in B. sep destruct B.
   unfold V293_tcb_free_critical,V293_tcb_enabled_resources in *.
   clear -B;sep auto.
 - apply encrit1_rule. apply V293_tcb_enabled_good;exact Frame.
Qed.

Lemma V293_tcb_free_pointer : forall Spec sd li I r ri tid bf bp bc pc cpu head K R aop ir si ci,
 rule_type_val_match(Tptr V293_tcb_type)head=true -> (R ==> CurLINV li tid) ->
 InfRules Spec sd li I r ri
 (V293_tcb_free_critical bf bp bc pc cpu head K R aop ir si ci)
 (sassign(evar 108%Z)(evar 91%Z))
 (V293_tcb_free_critical bf bp bc head cpu head K R aop ir si ci)tid.
Proof.
 intros Spec sd li I r ri tid bf bp bc pc cpu head K R aop ir si ci Typed HR.
 unfold V293_tcb_free_critical,V293_tcb_enabled_resources. eapply conseq_rule with
 (p:=<||aop||> ** (OS[ir,false,si,ci] **
 (V293_tcb_empty_bindings bf bp bc ** (Amapsto(bc,0%Z)Tint32 true cpu **
 (Amapsto(bf,0%Z)(Tptr V293_tcb_type)true head ** (V293_tcb_free_chain 13 head ** (K ** R)))))) **
 Amapsto(bp,0%Z)(Tptr V293_tcb_type)true pc)
 (q:=<||aop||> ** (OS[ir,false,si,ci] **
 (V293_tcb_empty_bindings bf bp bc ** (Amapsto(bc,0%Z)Tint32 true cpu **
 (Amapsto(bf,0%Z)(Tptr V293_tcb_type)true head ** (V293_tcb_free_chain 13 head ** (K ** R)))))) **
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

Definition V293_tcb_free_node b off next :=
 V293_tcb_free_payload b(Int.unsigned off) **
 Amapsto(b,(Int.unsigned off+20)%Z)(Tcom_ptr 410%Z)true next.
Definition V293_tcb_free_pop_state bf bp bc b off cpu head next K R aop ir si ci :=
 <||aop||> ** OS[ir,false,si,ci] **
 V293_tcb_enabled_resources bf bp bc (Vptr(b,off)) cpu
 (Amapsto(bf,0%Z)(Tptr V293_tcb_type)true head **
 (V293_tcb_free_node b off next ** (V293_tcb_free_chain 12 next ** (K ** R)))).
Lemma V293_tcb_free_pop : forall Spec sd li I r ri tid bf bp bc b off cpu next K R aop ir si ci,
 (Int.unsigned off+55<=Int.max_unsigned)%Z ->
 rule_type_val_match(Tcom_ptr 410%Z)next=true -> (R ==> CurLINV li tid) ->
 InfRules Spec sd li I r ri
 (V293_tcb_free_pop_state bf bp bc b off cpu(Vptr(b,off))next K R aop ir si ci)
 (V293_TCBInit_pop 91%Z 108%Z)
 (V293_tcb_free_pop_state bf bp bc b off cpu next next K R aop ir si ci)tid.
Proof.
 intros Spec sd li I r ri tid bf bp bc b off cpu next K R aop ir si ci Bound Typed HR.
 unfold V293_tcb_free_pop_state,V293_tcb_enabled_resources,V293_TCBInit_pop.
 eapply conseq_rule with
 (p:=<||aop||> ** (OS[ir,false,si,ci] **
 V293_tcb_enabled_resources bf bp bc(Vptr(b,off))cpu
 (V293_tcb_free_node b off next ** (V293_tcb_free_chain 12 next ** (K ** R)))) **
 Amapsto(bf,0%Z)(Tptr V293_tcb_type)true(Vptr(b,off)))
 (q:=<||aop||> ** (OS[ir,false,si,ci] **
 V293_tcb_enabled_resources bf bp bc(Vptr(b,off))cpu
 (V293_tcb_free_node b off next ** (V293_tcb_free_chain 12 next ** (K ** R)))) **
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

Lemma V293_tcb_free_exit : forall Spec sd li I r ri tid bf bp bc b off cpu next K R aop ir si ci,
 GoodFrm R -> (R ==> CurLINV li tid) ->
 rule_type_val_match(Tptr V293_tcb_type)next=true ->
 (Aisr ir ** (V293_tcb_free_pool bf ** K) ==> Aisr ir ** invlth_isr I 0(gettopis si)) ->
 InfRules Spec sd li I r ri
 (V293_tcb_free_pop_state bf bp bc b off cpu next next K R aop ir si(true::ci))(sprim excrit)
 (V293_tcb_enabled_state bf bp bc(Vptr(b,off))cpu(V293_tcb_free_node b off next ** R)aop ir si ci)tid.
Proof.
 intros Spec sd li I r ri tid bf bp bc b off cpu next K R aop ir si ci Frame HR Typed Close.
 eapply conseq_rule with
 (p:=<||aop||> ** OS[ir,false,si,true::ci] ** ATopis(gettopis si) ** invlth_isr I 0(gettopis si) **
 V293_tcb_enabled_resources bf bp bc(Vptr(b,off))cpu(V293_tcb_free_node b off next ** R))
 (q:=V293_tcb_enabled_state bf bp bc(Vptr(b,off))cpu(V293_tcb_free_node b off next ** R)aop ir si ci).
 - intros s H.
   assert(B:s |= (Amapsto(bf,0%Z)(Tptr V293_tcb_type)true next ** V293_tcb_free_chain 12 next) **
    (Aisr ir ** K ** <||aop||> ** Aie false ** Ais si ** Acs(true::ci) **
     V293_tcb_enabled_resources bf bp bc(Vptr(b,off))cpu(V293_tcb_free_node b off next ** R))).
   { unfold V293_tcb_free_pop_state,V293_tcb_enabled_resources in *;clear -H;sep auto. }
   eapply astar_mono in B;[ |apply astar_mono;[intros st HS;exact HS|apply V293_tcb_free_chain_weaken]|intros st HS;exact HS].
   assert(P:s |= (Aisr ir ** (V293_tcb_free_pool bf ** K)) **
    (<||aop||> ** Aie false ** Ais si ** Acs(true::ci) **
     V293_tcb_enabled_resources bf bp bc(Vptr(b,off))cpu(V293_tcb_free_node b off next ** R))).
   { unfold V293_tcb_free_pool. clear -B Typed;sep auto. }
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

(* Closed extraction: the chain itself supplies the bound and successor bytes.
   Only the real head store and excrit occur; no success-suffix premise here. *)
Theorem V293_OS_TCBInit_free_pop_transfer : forall Spec sd li I r ri tid
 bf bp bc b off cpu K R aop ir si ci,
 GoodFrm R -> (R ==> CurLINV li tid) ->
 (Aisr ir ** (V293_tcb_free_pool bf ** K) ==> Aisr ir ** invlth_isr I 0(gettopis si)) ->
 InfRules Spec sd li I r ri
 (V293_tcb_free_critical bf bp bc(Vptr(b,off))cpu(Vptr(b,off))K R aop ir si(true::ci))
 (sseq(V293_TCBInit_pop 91%Z 108%Z)(sprim excrit))
 (EX next:val,[|(Int.unsigned off+55<=Int.max_unsigned)%Z /\
   rule_type_val_match(Tcom_ptr 410%Z)next=true|] **
  V293_tcb_enabled_state bf bp bc(Vptr(b,off))cpu(V293_tcb_free_node b off next ** R)aop ir si ci)tid.
Proof.
 intros Spec sd li I r ri tid bf bp bc b off cpu K R aop ir si ci Frame HR Close.
 eapply conseq_rule with
 (p:=EX next:val,V293_tcb_free_pop_state bf bp bc b off cpu(Vptr(b,off))next K R aop ir si(true::ci) **
 [|(Int.unsigned off+55<=Int.max_unsigned)%Z /\ rule_type_val_match(Tcom_ptr 410%Z)next=true|]).
 - intros s H. unfold V293_tcb_free_critical,V293_tcb_enabled_resources in H.
   cbn[V293_tcb_free_chain]in H. sep normal in H. sep destruct H.
   unfold V293_tcb_free_pop_state,V293_tcb_enabled_resources,V293_tcb_free_node.
   clear -H. sep auto.
 - intros s H;exact H.
 - apply ex_intro_rule. intro next. apply pure_split_rule. intros[Bound Typed].
   eapply seq_rule.
   + apply V293_tcb_free_pop;assumption.
   + eapply conseq_rule.
     * intros s H;exact H.
     * intros s H. exists next. apply astar_l_apure_intro;[exact H|auto].
     * apply V293_tcb_free_exit;assumption.
Qed.
Print Assumptions V293_OS_TCBInit_free_pop_transfer.

Lemma V293_tcb_free_return_pool : forall Spec sd li I r ri tid bf bp bc pc cpu head K R aop ir si ci,
 GoodFrm R -> (R ==> CurLINV li tid) -> rule_type_val_match(Tptr V293_tcb_type)head=true ->
 (Aisr ir ** (V293_tcb_free_pool bf ** K) ==> Aisr ir ** invlth_isr I 0(gettopis si)) ->
 InfRules Spec sd li I r ri
 (V293_tcb_free_critical bf bp bc pc cpu head K R aop ir si(true::ci))(sprim excrit)
 (V293_tcb_enabled_state bf bp bc pc cpu R aop ir si ci)tid.
Proof.
 intros Spec sd li I r ri tid bf bp bc pc cpu head K R aop ir si ci Frame HR Typed Close.
 eapply conseq_rule with
 (p:=<||aop||> ** OS[ir,false,si,true::ci] ** ATopis(gettopis si) ** invlth_isr I 0(gettopis si) **
 V293_tcb_enabled_resources bf bp bc pc cpu R)
 (q:=V293_tcb_enabled_state bf bp bc pc cpu R aop ir si ci).
 - intros s H.
   assert(B:s |= (Aisr ir ** (V293_tcb_free_pool bf ** K)) **
    (<||aop||> ** Aie false ** Ais si ** Acs(true::ci) ** V293_tcb_enabled_resources bf bp bc pc cpu R)).
   { unfold V293_tcb_free_critical,V293_tcb_enabled_resources,V293_tcb_free_pool in *;clear -H Typed;sep auto. }
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

Definition V293_tcb_free_test head := match head with Vnull=>Int.zero|_=>Int.one end.
Lemma V293_tcb_free_guard_eval : forall bf bp bc cpu head K R aop ir si ci s,
 rule_type_val_match(Tptr V293_tcb_type)head=true ->
 s |= V293_tcb_free_critical bf bp bc head cpu head K R aop ir si ci ->
 evalval(eunop oppsite(V293_task_prio_null_test(evar 108%Z)))(getsmem s)=Some(Vint32(V293_tcb_free_test head)) /\
 evaltype(eunop oppsite(V293_task_prio_null_test(evar 108%Z)))(getsmem s)=Some Tint32.
Proof.
 intros bf bp bc cpu head K R aop ir si ci s Typed H.
 unfold V293_tcb_free_critical,V293_tcb_enabled_resources in H.
 assert(B:s |= V293_tcb_empty_bindings bf bp bc ** Atrue)by(clear -H;sep auto).
 destruct(V293_tcb_empty_env _ _ _ _ B)as(P&_).
 assert(L:load(Tptr V293_tcb_type)(getmem s)(bp,0%Z)=Some head).
 { eapply V293_star_load_l with(p:=Amapsto(bp,0%Z)(Tptr V293_tcb_type)true head)(q:=Atrue).
   - intros st[HM _]. eapply mapstoval_load;[exact Typed|exact HM].
   - clear -H;sep auto. }
 destruct s as [[[[[[ge le] M] irq] aux] O] op].
 cbn[getlenv getmem getsmem get_smem get_lenv get_genv get_mem]in *.
 cbn[V293_task_prio_null_test evalval evaltype get_lenv get_genv get_mem].
 cbv delta[env var memory.ident Modules.ident]in *. rewrite P,L.
 destruct head;cbn[rule_type_val_match]in Typed;try discriminate;try destruct a;split;reflexivity.
Qed.

(* Right-associated original continuation: field initialization and Hook / publish
   remain an explicit premise; they are not inferred from the extraction proof. *)
Lemma V293_tcb_free_nonempty_continuation : forall Spec sd li I r ri tid
 bf bp bc b off cpu K R aop ir si ci suffix,
 GoodFrm R -> (R ==> CurLINV li tid) ->
 (Aisr ir ** (V293_tcb_free_pool bf ** K) ==> Aisr ir ** invlth_isr I 0(gettopis si)) ->
 (forall next,(Int.unsigned off+55<=Int.max_unsigned)%Z -> rule_type_val_match(Tcom_ptr 410%Z)next=true ->
 InfRules Spec sd li I r ri
 (V293_tcb_enabled_state bf bp bc(Vptr(b,off))cpu(V293_tcb_free_node b off next ** R)aop ir si ci)
 suffix Afalse tid) ->
 InfRules Spec sd li I r ri
 (V293_tcb_free_critical bf bp bc(Vptr(b,off))cpu(Vptr(b,off))K R aop ir si(true::ci))
 (sseq(V293_TCBInit_pop 91%Z 108%Z)(sseq(sprim excrit)suffix))Afalse tid.
Proof.
 intros Spec sd li I r ri tid bf bp bc b off cpu K R aop ir si ci suffix Frame HR Close Success.
 eapply conseq_rule with
 (p:=EX next:val,V293_tcb_free_pop_state bf bp bc b off cpu(Vptr(b,off))next K R aop ir si(true::ci) **
 [|(Int.unsigned off+55<=Int.max_unsigned)%Z /\ rule_type_val_match(Tcom_ptr 410%Z)next=true|]).
 - intros s H. unfold V293_tcb_free_critical,V293_tcb_enabled_resources in H.
   cbn[V293_tcb_free_chain]in H. sep normal in H. sep destruct H.
   unfold V293_tcb_free_pop_state,V293_tcb_enabled_resources,V293_tcb_free_node. clear -H;sep auto.
 - intros s H;exact H.
 - apply ex_intro_rule. intro next. apply pure_split_rule. intros[Bound Typed].
   eapply seq_rule;[apply V293_tcb_free_pop;assumption| ].
   eapply seq_rule;[apply V293_tcb_free_exit;assumption| ].
   apply Success;assumption.
Qed.

Theorem V293_OS_TCBInit_free_body_with_success : forall Spec sd li I r tid hi hc
 bf bp bc pc cpu K R aop ir si ci,
 (gettopis si<=INUM)%nat -> GoodFrm R -> (R ==> CurLINV li tid) ->
 (Aisr ir ** invlth_isr I 0(gettopis si) ==> Aisr ir ** (V293_tcb_free_pool bf ** K)) ->
 (Aisr ir ** (V293_tcb_free_pool bf ** K) ==> Aisr ir ** invlth_isr I 0(gettopis si)) ->
 (V293_tcb_enabled_state bf bp bc Vnull(Vint32 Int.zero)R aop ir si ci ==> r(Some(Vint32(Int.repr 66)))) ->
 (forall b off next,(Int.unsigned off+55<=Int.max_unsigned)%Z -> rule_type_val_match(Tcom_ptr 410%Z)next=true ->
 InfRules Spec sd li I r Afalse
 (V293_tcb_enabled_state bf bp bc(Vptr(b,off))(Vint32 Int.zero)(V293_tcb_free_node b off next ** R)aop ir si ci)
 (sseq(V293_TCBInit_fields 108%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z)
       (V293_TCBInit_success_suffix hi hc)) Afalse tid) ->
 InfRules Spec sd li I r Afalse
 (V293_tcb_enabled_state bf bp bc pc cpu R aop ir si ci)
 (V293_TCBInit_function_body hi hc)Afalse tid.
Proof.
 intros Spec sd li I r tid hi hc bf bp bc pc cpu K R aop ir si ci Bound Frame HR Open Close Empty Success.
 unfold V293_TCBInit_function_body. eapply seq_rule;[apply V293_tcb_enabled_cpu;exact HR| ].
 unfold V293_TCBInit_prefix. eapply seq_rule;[apply V293_tcb_free_enter with(K:=K);assumption| ].
 eapply conseq_rule with
 (p:=EX head:val,V293_tcb_free_critical bf bp bc pc(Vint32 Int.zero)head K R aop ir si(true::ci) **
 [|rule_type_val_match(Tptr V293_tcb_type)head=true|]).
 - intros s H. sep normal in H. sep destruct H. clear -H;sep auto.
 - intros s H;exact H.
 - apply ex_intro_rule. intro head. apply pure_split_rule. intro Typed.
   eapply seq_rule;[apply V293_tcb_free_pointer;assumption| ].
   destruct head;cbn[rule_type_val_match]in Typed;try discriminate.
   + eapply seq_rule with(p':=V293_tcb_free_critical bf bp bc Vnull(Vint32 Int.zero)Vnull K R aop ir si(true::ci)).
     * eapply ift_rule with(tp:=Tint32).
       -- intros s H. exists(Vint32 Int.zero). cbn[sat].
          destruct(V293_tcb_free_guard_eval bf bp bc (Vint32 Int.zero) Vnull K R aop ir si (true::ci) s eq_refl H)as[V T].
          split;[exact V|split;[exact T|discriminate]].
       -- intros s[H _];exact H.
       -- eapply conseq_rule with(p:=Afalse)(q:=Afalse).
          ++ intros s[H[v[V B]]].
             destruct(V293_tcb_free_guard_eval bf bp bc (Vint32 Int.zero) Vnull K R aop ir si (true::ci) s eq_refl H)as[Z _].
             rewrite Z in V. inversion V;subst v. discriminate B.
          ++ intros s H;contradiction.
          ++ apply pfalse_rule.
     * unfold V293_TCBInit_empty. eapply seq_rule.
       -- apply V293_tcb_free_return_pool;assumption.
       -- apply rete_rule with(v:=Vint32(Int.repr 66))(t:=Tint32).
          intros s H. split;[apply Empty;exact H| ].
          destruct s as [[[[[[ge le] M] irq] aux] O] op].
          cbn[sat evalval evaltype getsmem get_smem]. repeat split;try reflexivity;discriminate.
   + destruct a as[b off]. eapply seq_rule with(p':=Afalse).
     * eapply ift_rule with(tp:=Tint32).
       -- intros s H. exists(Vint32 Int.one). cbn[sat].
          destruct(V293_tcb_free_guard_eval bf bp bc (Vint32 Int.zero) (Vptr(b,off)) K R aop ir si (true::ci) s eq_refl H)as[V T].
          split;[exact V|split;[exact T|discriminate]].
       -- intros s[H[v[V B]]].
          destruct(V293_tcb_free_guard_eval bf bp bc (Vint32 Int.zero) (Vptr(b,off)) K R aop ir si (true::ci) s eq_refl H)as[Z _].
          rewrite Z in V. inversion V;subst v. discriminate B.
       -- eapply conseq_rule;[intros s[H _];exact H|intros s H;exact H| ].
          apply V293_tcb_free_nonempty_continuation;try assumption. intros;apply Success;assumption.
     * apply pfalse_rule.
Qed.
Print Assumptions V293_OS_TCBInit_free_body_with_success.
