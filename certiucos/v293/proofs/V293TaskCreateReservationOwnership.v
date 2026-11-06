(* A value-determined half share, using the existing physical permission model.
   RESERVED is protected by a caller-held half; no new ghost state is introduced.
   This component is not a complete kernel invariant or a whole API proof. *)
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

Definition V293_reservation_permission (reserved:addrval) (v:val) : bool :=
 match v with Vptr t=>negb(beq_tid t reserved) | _=>true end.
Definition V293_reservation_pool (a:addr) (reserved:addrval) :=
 EX v:val, [|rule_type_val_match(Tptr V293_tcb_type)v=true|] **
 Amapsto a (Tptr V293_tcb_type)(V293_reservation_permission reserved v)v.
Definition V293_reservation_owner (a:addr) (reserved:addrval) :=
 Amapsto a (Tptr V293_tcb_type)false(Vptr reserved).

Lemma V293_reservation_permission_reserved : forall reserved,
 V293_reservation_permission reserved(Vptr reserved)=false.
Proof. intros. change(negb(tidspec.beq reserved reserved)=false). rewrite (tidspec.eq_beq_true reserved reserved eq_refl). reflexivity. Qed.
Lemma V293_reservation_permission_null : forall reserved,
 V293_reservation_permission reserved Vnull=true.
Proof. reflexivity. Qed.

Lemma V293_reservation_bytes_exact : forall bytes a perm m1 m2,
 ptomvallist a perm bytes m1 -> ptomvallist a perm bytes m2 -> m1=m2.
Proof.
 induction bytes as [ | raw bytes IH];intros[b off]perm m1 m2 H1 H2.
 - cbn[ptomvallist]in H1,H2;congruence.
 - cbn[ptomvallist]in H1,H2.
   destruct H1 as[h1[t1[J1[P1 T1]]]]. destruct H2 as[h2[t2[J2[P2 T2]]]].
   unfold ptomval in P1,P2. subst h1 h2.
   assert(t1=t2)by(eapply IH;eauto). subst t2. eapply map_join_deter;eauto.
Qed.

Lemma V293_reservation_pool_precise : forall a reserved,
 precise(V293_reservation_pool a reserved).
Proof.
 intros a reserved s M1 M2 O1 O2 [v1 H1] [v2 H2] M O HM1 HM2 HO1 HO2.
 apply astar_l_apure_elim in H1. destruct H1 as[T1 P1].
 apply astar_l_apure_elim in H2. destruct H2 as[T2 P2].
 destruct s as [[[[[[ge le] mem] ir] aux] o] op].
 change(mapstoval a(Tptr V293_tcb_type)(V293_reservation_permission reserved v1)v1 M1 /\ O1=emp)in P1.
 change(mapstoval a(Tptr V293_tcb_type)(V293_reservation_permission reserved v2)v2 M2 /\ O2=emp)in P2.
 destruct P1 as[P1 E1]. destruct P2 as[P2 E2].
 pose proof(@mapstoval_load _ _ _ _ _ T1 P1)as L1.
 pose proof(@mapstoval_load _ _ _ _ _ T2 P2)as L2.
 pose proof(@load_mem_mono _ _ _ _ _ L1 HM1)as LM1.
 pose proof(@load_mem_mono _ _ _ _ _ L2 HM2)as LM2.
 assert(v1=v2)by congruence. subst v2. split;[ |congruence].
 destruct P1 as[vl1[V1 P1]]. destruct P2 as[vl2[V2 P2]].
 rewrite <- V1 in P1. rewrite <- V2 in P2. eapply V293_reservation_bytes_exact;eauto.
Qed.
Lemma V293_reservation_pool_good : forall a reserved,
 GoodInvAsrt(V293_reservation_pool a reserved).
Proof. intros. unfold V293_reservation_pool. simpl;auto. Qed.
Lemma V293_reservation_pool_isr : forall a reserved,
 assertion.inv_isr_prop(V293_reservation_pool a reserved).
Proof.
 intros. unfold assertion.inv_isr_prop. repeat split;intros;
 destruct s as [[[[[[ge le] M] ir] [[ie si] cs]] O] op];exact H.
Qed.

(* Both reads are derived from the joined physical memory, not an abstract
   assertion that a reservation survived interference. *)
Lemma V293_reservation_compatible_values : forall a p1 p2 v1 v2 s,
 rule_type_val_match(Tptr V293_tcb_type)v1=true ->
 rule_type_val_match(Tptr V293_tcb_type)v2=true ->
 s |= Amapsto a(Tptr V293_tcb_type)p1 v1 ** Amapsto a(Tptr V293_tcb_type)p2 v2 -> v1=v2.
Proof.
 intros a p1 p2 v1 v2 s T1 T2 H. destruct s as [[[[[[ge le] M] ir] aux] O] op]. apply sat_split in H.
 destruct H as[m1[m2[o1[o2[JM[JO[[P1 E1][P2 E2]]]]]]]].
 pose proof(@mapstoval_load _ _ _ _ _ T1 P1)as L1.
 pose proof(@mapstoval_load _ _ _ _ _ T2 P2)as L2.
 pose proof(@load_local _ _ _ _ _ _ JM L1)as LM1.
 apply map_join_comm in JM.
 pose proof(@load_local _ _ _ _ _ _ JM L2)as LM2. congruence.
Qed.

Theorem V293_reservation_reacquire : forall a reserved,
 V293_reservation_owner a reserved ** V293_reservation_pool a reserved ==>
 Amapsto a(Tptr V293_tcb_type)true(Vptr reserved).
Proof.
 intros a reserved s H. unfold V293_reservation_pool in H. sep normal in H.
 sep destruct H. sep split in H.
 assert(E:x=Vptr reserved).
 { eapply V293_reservation_compatible_values;[exact H0|reflexivity|exact H]. }
 subst x. rewrite V293_reservation_permission_reserved in H.
 eapply combine_ro2rw_p1;exact H.
Qed.
Theorem V293_reservation_publish : forall a reserved,
 Amapsto a(Tptr V293_tcb_type)true(Vptr reserved) ==>
 V293_reservation_owner a reserved ** V293_reservation_pool a reserved.
Proof.
 intros a reserved s H. apply separate_rw2ro in H.
 eapply astar_mono;[intros st HS;exact HS| |exact H].
 intros st HS. exists(Vptr reserved). apply astar_l_apure_intro;[ |reflexivity].
 rewrite V293_reservation_permission_reserved. exact HS.
Qed.
Lemma V293_reservation_pool_null : forall a reserved,
 Amapsto a(Tptr V293_tcb_type)true Vnull ==> V293_reservation_pool a reserved.
Proof.
 intros a reserved s H. exists Vnull. apply astar_l_apure_intro;[ |reflexivity].
 rewrite V293_reservation_permission_null;exact H.
Qed.

Definition V293_create_owned_pool table reserved p K :=
 V293_reservation_pool(table,(4*Z.of_nat p)%Z)reserved ** K.
Definition V293_create_owned_share table reserved p :=
 V293_reservation_owner(table,(4*Z.of_nat p)%Z)reserved.

(* The caller retains its half in F across enabled interrupts. The shared
   half is borrowed by the real encrit1 and is forced to match this owner. *)
Lemma V293_create_owned_enter : forall Spec sd li I r ri tid
 table reserved p K F aop ir si ci,
 (gettopis si<=INUM)%nat -> GoodFrm F ->
 (Aisr ir ** invlth_isr I 0(gettopis si) ==>
  Aisr ir ** V293_create_owned_pool table reserved p K) ->
 InfRules Spec sd li I r ri
 (V293_create_enabled_failure_state table p(V293_create_owned_share table reserved p ** F)aop ir si ci)
 (sprim encrit)
 (V293_create_failure_state table p(Vptr reserved)(K ** F)aop ir si(true::ci))tid.
Proof.
 intros Spec sd li I r ri tid table reserved p K F aop ir si ci Bound Frame Open.
 unfold V293_create_enabled_failure_state. eapply conseq_rule with
 (p:=<||aop||> ** OS[ir,true,si,ci] ** ATopis(gettopis si) **
  [|(gettopis si<=INUM)%nat|] ** V293_create_enabled_failure_resources table p(V293_create_owned_share table reserved p ** F))
 (q:=<||aop||> ** OS[ir,false,si,true::ci] ** invlth_isr I 0(gettopis si) **
  V293_create_enabled_failure_resources table p(V293_create_owned_share table reserved p ** F)).
 - intros s H. assert(S:s |= Ais si ** Atrue)by(clear -H;sep auto).
   pose proof(V293_time_topis si Atrue s S)as Top.
   apply astar_l_atopis_elim in Top. destruct Top as[Top _].
   pose proof(@astar_l_atopis_intro s(gettopis si)_ H Top)as HT. clear -HT Bound;sep auto.
 - intros s H.
   assert(B:s |= (Aisr ir ** invlth_isr I 0(gettopis si)) **
    (<||aop||> ** Aie false ** Ais si ** Acs(true::ci) **
     V293_create_enabled_failure_resources table p(V293_create_owned_share table reserved p ** F)))by(clear -H;sep auto).
   eapply astar_mono in B;[ |exact Open|intros st HS;exact HS].
   unfold V293_create_owned_pool,V293_create_enabled_failure_resources,V293_create_owned_share in B.
   assert(C:s |= (V293_reservation_owner(table,(4*Z.of_nat p)%Z)reserved **
      V293_reservation_pool(table,(4*Z.of_nat p)%Z)reserved) **
     (<||aop||> ** OS[ir,false,si,true::ci] **
      LV 101%Z @ Tint8 |->V293_byteval p ** LV 209%Z @ Tint8 |->Vint32(Int.repr 66) **
      V293_tcb_table_binding table ** K ** F))by(clear -B;sep auto).
   eapply astar_mono in C;[ |apply V293_reservation_reacquire|intros st HS;exact HS].
   unfold V293_create_failure_state,V293_create_failure_resources. clear -C;sep auto.
 - apply encrit1_rule. apply V293_create_enabled_failure_good.
   unfold V293_create_owned_share,V293_reservation_owner. cbn[GoodFrm];tauto.
Qed.

Lemma V293_create_owned_exit : forall Spec sd li I r ri tid
 table reserved p K F aop ir si ci,
 GoodFrm F -> (F ==> CurLINV li tid) ->
 (Aisr ir ** V293_create_owned_pool table reserved p K ==>
  Aisr ir ** invlth_isr I 0(gettopis si)) ->
 InfRules Spec sd li I r ri
 (V293_create_failure_state table p Vnull(K ** F)aop ir si(true::ci))
 (sprim excrit)(V293_create_enabled_failure_state table p F aop ir si ci)tid.
Proof.
 intros Spec sd li I r ri tid table reserved p K F aop ir si ci Frame HR Close.
 eapply conseq_rule with
 (p:=<||aop||> ** OS[ir,false,si,true::ci] ** ATopis(gettopis si) **
  invlth_isr I 0(gettopis si) ** V293_create_enabled_failure_resources table p F)
 (q:=<||aop||> ** OS[ir,true,si,ci] ** V293_create_enabled_failure_resources table p F).
 - intros s H.
   assert(B:s |= (Amapsto(table,(4*Z.of_nat p)%Z)(Tptr V293_tcb_type)true Vnull) **
    (Aisr ir ** K ** <||aop||> ** Aie false ** Ais si ** Acs(true::ci) **
     V293_create_enabled_failure_resources table p F)).
   { unfold V293_create_failure_state,V293_create_failure_resources,
      V293_create_enabled_failure_resources in *;clear -H;sep auto. }
   eapply astar_mono in B;[ |apply V293_reservation_pool_null with(reserved:=reserved)|intros st HS;exact HS].
   assert(C:s |= (Aisr ir ** V293_create_owned_pool table reserved p K) **
    (<||aop||> ** Aie false ** Ais si ** Acs(true::ci) ** V293_create_enabled_failure_resources table p F)).
   { unfold V293_create_owned_pool;clear -B;sep auto. }
   eapply astar_mono in C;[ |exact Close|intros st HS;exact HS].
   assert(S:s |= Ais si ** Atrue)by(clear -C;sep auto).
   pose proof(V293_time_topis si Atrue s S)as Top.
   apply astar_l_atopis_elim in Top. destruct Top as[Top _].
   pose proof(@astar_l_atopis_intro s(gettopis si)_ C Top)as HT. clear -HT;sep auto.
 - unfold V293_create_enabled_failure_state. intros s H;exact H.
 - apply excrit1_rule.
   + apply V293_create_enabled_failure_good;exact Frame.
   + unfold V293_create_enabled_failure_resources. repeat apply V293_star_CurLINV_r. exact HR.
Qed.

Theorem V293_OSTaskCreateExt_owned_rollback : forall Spec sd li I r ri tid
 table reserved p K F aop ir si ci,
 p<13 -> (gettopis si<=INUM)%nat -> GoodFrm F -> (F ==> CurLINV li tid) ->
 (Aisr ir ** invlth_isr I 0(gettopis si) ==>
  Aisr ir ** V293_create_owned_pool table reserved p K) ->
 (Aisr ir ** V293_create_owned_pool table reserved p K ==>
  Aisr ir ** invlth_isr I 0(gettopis si)) ->
 InfRules Spec sd li I r ri
 (V293_create_enabled_failure_state table p(V293_create_owned_share table reserved p ** F)aop ir si ci)
 (V293_TaskCreateExt_rollback 92%Z 101%Z)
 (V293_create_enabled_failure_state table p F aop ir si ci)tid.
Proof.
 intros Spec sd li I r ri tid table reserved p K F aop ir si ci Range Bound Frame HR Open Close.
 unfold V293_TaskCreateExt_rollback. eapply seq_rule.
 - apply V293_create_owned_enter with(reserved:=reserved)(K:=K);assumption.
 - eapply seq_rule.
   + apply V293_create_failure_store_hoare;[exact Range|apply V293_star_CurLINV_r;exact HR].
   + apply V293_create_owned_exit with(reserved:=reserved)(K:=K);assumption.
Qed.

(* Publish after the actual RESERVED store. Only the creator keeps the other
   half; the ISR counter and K return to the same pool used by rollback. *)
Lemma V293_create_reservation_owned_exit : forall Spec sd li I r ri tid
 bp bc table bn br p cpu K F aop ir si ci,
 GoodFrm F -> (F ==> CurLINV li tid) ->
 (Aisr ir ** V293_create_owned_pool table (br,Int.zero) p
   (Amapsto(bn,0%Z)Tint8 true(V293_byteval 0) ** K) ==>
  Aisr ir ** invlth_isr I 0(gettopis si)) ->
 InfRules Spec sd li I r ri
 (V293_create_slot_state bp bc table bn br p 0(Some(br,Int.zero))cpu K F aop ir si ci)
 (sprim excrit)
 (V293_create_enabled_state bp bc p cpu
  (V293_create_owned_share table(br,Int.zero)p ** V293_create_slot_views table bn br ** F)
  aop ir si ci)tid.
Proof.
 intros Spec sd li I r ri tid bp bc table bn br p cpu K F aop ir si ci Frame HR Close.
 eapply conseq_rule with
 (p:=<||aop||> ** OS[ir,false,si,true::ci] ** ATopis(gettopis si) ** invlth_isr I 0(gettopis si) **
  V293_create_enabled_locals bp bc p cpu
   (V293_create_owned_share table(br,Int.zero)p ** V293_create_slot_views table bn br ** F))
 (q:=<||aop||> ** OS[ir,true,si,ci] ** V293_create_enabled_locals bp bc p cpu
   (V293_create_owned_share table(br,Int.zero)p ** V293_create_slot_views table bn br ** F)).
 - intros s H.
   assert(B:s |= Amapsto(table,(4*Z.of_nat p)%Z)(Tptr V293_tcb_type)true(Vptr(br,Int.zero)) **
    (Aisr ir ** Amapsto(bn,0%Z)Tint8 true(V293_byteval 0) ** K **
     <||aop||> ** Aie false ** Ais si ** Acs(true::ci) **
     V293_create_enabled_locals bp bc p cpu(V293_create_slot_views table bn br ** F))).
   { unfold V293_create_slot_state,V293_create_enabled_locals in *.
     cbn[V293_rdy_raw_cells V293_create_slot_cells V293_create_slot_value app]in *;clear -H;sep auto. }
   eapply astar_mono in B;[ |apply V293_reservation_publish with(reserved:=(br,Int.zero))|intros st HS;exact HS].
   assert(C:s |= (Aisr ir ** V293_create_owned_pool table(br,Int.zero)p
       (Amapsto(bn,0%Z)Tint8 true(V293_byteval 0) ** K)) **
    (<||aop||> ** Aie false ** Ais si ** Acs(true::ci) **
     V293_create_enabled_locals bp bc p cpu
      (V293_create_owned_share table(br,Int.zero)p ** V293_create_slot_views table bn br ** F))).
   { unfold V293_create_owned_pool,V293_create_owned_share,V293_create_enabled_locals in *.
     cbn[V293_rdy_raw_cells]in *;clear -B;sep auto. }
   eapply astar_mono in C;[ |exact Close|intros st HS;exact HS].
   assert(S:s |= Ais si ** Atrue)by(clear -C;sep auto).
   pose proof(V293_time_topis si Atrue s S)as Top.
   apply astar_l_atopis_elim in Top. destruct Top as[Top _].
   pose proof(@astar_l_atopis_intro s(gettopis si)_ C Top)as HT. clear -HT;sep auto.
 - unfold V293_create_enabled_state. intros s H;exact H.
 - apply excrit1_rule.
   + apply V293_create_enabled_good.
     unfold V293_create_owned_share,V293_reservation_owner,V293_create_slot_views,V293_create_global_binding.
     cbn[GoodFrm]. tauto.
   + unfold V293_create_enabled_locals.
     repeat apply V293_star_CurLINV_r. exact HR.
Qed.

Theorem V293_OSTaskCreateExt_owned_reservation : forall Spec sd li I r ri tid
 bp bc table bn br p cpu K F aop ir si ci,
 p<13 -> GoodFrm F -> (F ==> CurLINV li tid) ->
 (Aisr ir ** V293_create_owned_pool table(br,Int.zero)p
   (Amapsto(bn,0%Z)Tint8 true(V293_byteval 0) ** K) ==>
  Aisr ir ** invlth_isr I 0(gettopis si)) ->
 InfRules Spec sd li I r ri
 (V293_create_slot_state bp bc table bn br p 0 None cpu K F aop ir si ci)
 (sseq(sassign(earrayelem(evar 92%Z)(evar 101%Z))(V293_task_prio_reserved_expr 97%Z))(sprim excrit))
 (V293_create_enabled_state bp bc p cpu
   (V293_create_owned_share table(br,Int.zero)p ** V293_create_slot_views table bn br ** F)
   aop ir si ci)tid.
Proof.
 intros Spec sd li I r ri tid bp bc table bn br p cpu K F aop ir si ci Range Frame HR Close.
 eapply seq_rule with(p':=V293_create_slot_state bp bc table bn br p 0(Some(br,Int.zero))cpu K F aop ir si ci).
 - eapply conseq_rule;[apply V293_create_slot_prefix_zero|intros s H;apply V293_create_slot_prefix_zero;exact H| ].
   apply V293_create_prefix_reserve_hoare;[exact Range|apply V293_star_CurLINV_r;exact HR].
 - apply V293_create_reservation_owned_exit;assumption.
Qed.

(* The original guard, rollback and return, consuming the owner on failure. *)
Theorem V293_OSTaskCreateExt_owned_failure_suffix : forall Spec sd li I tid
 table reserved p K F aop ir si ci running sched,
 p<13 -> (gettopis si<=INUM)%nat -> GoodFrm F -> (F ==> CurLINV li tid) ->
 (Aisr ir ** invlth_isr I 0(gettopis si) ==>
  Aisr ir ** V293_create_owned_pool table reserved p K) ->
 (Aisr ir ** V293_create_owned_pool table reserved p K ==>
  Aisr ir ** invlth_isr I 0(gettopis si)) ->
 InfRules Spec sd li I(V293_create_enabled_failure_return table p F aop ir si ci)Afalse
 (V293_create_enabled_failure_state table p(V293_create_owned_share table reserved p ** F)aop ir si ci)
 (V293_TaskCreateExt_suffix 92%Z 101%Z 209%Z running sched)Afalse tid.
Proof.
 intros Spec sd li I tid table reserved p K F aop ir si ci running sched Range Bound Frame HR Open Close.
 assert(Guard:forall s,s |= V293_create_enabled_failure_state table p(V293_create_owned_share table reserved p ** F)aop ir si ci ->
  evalval(ebinop oeq(evar 209%Z)(econst32 Int.zero))(getsmem s)=Some(Vint32 Int.zero) /\
  evaltype(ebinop oeq(evar 209%Z)(econst32 Int.zero))(getsmem s)=Some Tint32).
 { intros s H. apply V293_create_error66_guard. eapply V293_create_enabled_failure_error;exact H. }
 unfold V293_TaskCreateExt_suffix. eapply seq_rule.
 - eapply if_rule with(tp:=Tint32).
   + intros s H. exists(Vint32 Int.zero). destruct(Guard s H)as[V T].
     cbn[sat]. repeat split;try assumption;discriminate.
   + eapply conseq_rule with(p:=Afalse)(q:=V293_create_enabled_failure_state table p F aop ir si ci).
     * intros s[H[v[V B]]]. destruct(Guard s H)as[Z _].
       rewrite Z in V. inversion V;subst v. discriminate B.
     * intros s H;exact H.
     * apply pfalse_rule.
   + eapply conseq_rule with(p:=V293_create_enabled_failure_state table p(V293_create_owned_share table reserved p ** F)aop ir si ci).
     * intros s[H _];exact H.
     * intros s H;exact H.
     * apply V293_OSTaskCreateExt_owned_rollback with(reserved:=reserved)(K:=K);assumption.
 - apply rete_rule with(v:=Vint32(Int.repr 66))(t:=Tint8).
   intros s H. split.
   + unfold V293_create_enabled_failure_return. apply astar_l_apure_intro;[exact H|reflexivity].
   + apply V293_create_error66_read. eapply V293_create_enabled_failure_error;exact H.
Qed.


(* Actual seven-argument call preserves the owner in its frame; the unchanged
   suffix then consumes it. Callee body remains a separate same-Spec obligation. *)
Theorem V293_OSTaskCreateExt_owned_empty_call_suffix : forall Spec sd li I tid f
 bf table reserved p top bottom identity size ext options K R aop ir si ci
 (good:GoodFunAsrt R) F olderr running sched,
 p<13 -> (gettopis si<=INUM)%nat -> GoodFrm R -> GoodFrm F ->
 V293_tcb_init_values_valid top bottom identity size ext options ->
 (R ==> CurLINV li tid) ->
 (Aisr ir ** invlth_isr I 0(gettopis si) ==>
  Aisr ir ** V293_create_owned_pool table reserved p K) ->
 (Aisr ir ** V293_create_owned_pool table reserved p K ==>
  Aisr ir ** invlth_isr I 0(gettopis si)) ->
 Spec f=Some(V293_tcb_enabled_fpre bf R aop ir si ci good,
  V293_tcb_enabled_fpost bf R aop ir si ci good,(Tint8,rev V293_TCBInit_argument_types)) ->
 InfRules Spec sd li I
 (V293_create_enabled_failure_return table p
  (V293_create_enabled_failure_kept bf top bottom identity size ext options R F)aop ir si ci)Afalse
 (V293_tcb_enabled_external bf R aop ir si ci ** LV 209%Z @ Tint8 |->olderr **
  V293_create_tcb_arguments p top bottom identity size ext options(V293_tcb_table_binding table ** (V293_create_owned_share table reserved p ** F)))
 (sseq(V293_TaskCreateExt_TCB_call 209%Z f 101%Z 108%Z 205%Z 206%Z 207%Z 208%Z 204%Z)
  (V293_TaskCreateExt_suffix 92%Z 101%Z 209%Z running sched))Afalse tid.
Proof.
 intros Spec sd li I tid f bf table reserved p top bottom identity size ext options K R aop ir si ci
 good F olderr running sched Range Bound ResourceFrame Frame Valid HR Open Close Lookup.
 eapply seq_rule.
 - apply V293_TaskCreateExt_TCB_empty_enabled_call with(good:=good).
   + unfold V293_create_owned_share,V293_reservation_owner. cbn[GoodFrm V293_tcb_table_binding];tauto.
   + lia.
   + exact Valid.
   + exact HR.
   + exact Lookup.
 - eapply conseq_rule with(p:=V293_create_enabled_failure_state table p
    (V293_create_owned_share table reserved p ** V293_create_enabled_failure_kept bf top bottom identity size ext options R F)aop ir si ci).
   + unfold V293_tcb_enabled_external,V293_create_tcb_arguments,
      V293_create_enabled_failure_state,V293_create_enabled_failure_resources,
      V293_create_enabled_failure_kept. intros s H;clear -H;sep auto.
   + intros s H;exact H.
   + apply V293_OSTaskCreateExt_owned_failure_suffix with(reserved:=reserved)(K:=K).
     * exact Range.
     * exact Bound.
     * unfold V293_create_enabled_failure_kept,Alvarmapsto,Alvarenv',Aptrmapsto.
       cbn[GoodFrm];tauto.
     * unfold V293_create_enabled_failure_kept. do 6 apply V293_star_CurLINV_r.
       apply V293_star_CurLINV_r. apply V293_star_CurLINV_l;exact HR.
     * exact Open.
     * exact Close.
Qed.


Lemma V293_reservation_first_byte : forall b off perm raw bytes M,
 ptomvallist(b,off)perm(raw::bytes)M -> get M(b,off)=Some(perm,raw).
Proof.
 intros b off perm raw bytes M H. cbn[ptomvallist]in H.
 destruct H as[head[tail[J[P T]]]]. unfold ptomval in P. subst head.
 assert(N:get tail(b,off)=None).
 { eapply ptomvallist_get_none' with(i:=1%Z);[lia|exact T]. }
 apply map_join_comm in J.
 transitivity(get(sig(b,off)(perm,raw))(b,off)).
 - eapply map_join_get_none;eauto.
 - apply map_get_sig.
Qed.

Lemma V293_reservation_full_half_conflict : forall a reserved s,
 s |= Amapsto a(Tptr V293_tcb_type)true(Vptr reserved) **
      V293_reservation_owner a reserved -> False.
Proof.
 intros[b off][rb ro]s H. destruct s as [[[[[[ge le] M] ir] aux] O] op]. apply sat_split in H.
 destruct H as[m1[m2[o1[o2[JM[JO[[P1 E1][P2 E2]]]]]]]].
 destruct P1 as[vl1[V1 P1]]. destruct P2 as[vl2[V2 P2]].
 rewrite <- V1 in P1. rewrite <- V2 in P2. cbn[encode_val inj_pointer]in P1,P2.
 pose proof(V293_reservation_first_byte _ _ _ _ _ _ P1)as G1.
 pose proof(V293_reservation_first_byte _ _ _ _ _ _ P2)as G2.
 change(HalfPermMap.join m1 m2 M)in JM. destruct JM as[D _].
 specialize(D(b,off)). change(m1(b,off)=Some(true,Pointer rb ro 3))in G1.
 change(m2(b,off)=Some(false,Pointer rb ro 3))in G2.
 rewrite G1,G2 in D. exact D.
Qed.

(* Two isolated read halves are compatible. Exclusivity is asserted only in
   the presence of the shared pool's required third half. *)
Theorem V293_reservation_single_owner : forall a reserved,
 (V293_reservation_owner a reserved ** V293_reservation_pool a reserved) **
 V293_reservation_owner a reserved ==> Afalse.
Proof.
 intros a reserved s H.
 eapply astar_mono in H;[ |apply V293_reservation_reacquire|intros st HS;exact HS].
 exact(V293_reservation_full_half_conflict a reserved s H).
Qed.

Theorem V293_reservation_excludes_other_value : forall a reserved v s,
 rule_type_val_match(Tptr V293_tcb_type)v=true -> v<>Vptr reserved ->
 s |= V293_reservation_owner a reserved ** Amapsto a(Tptr V293_tcb_type)
       (V293_reservation_permission reserved v)v -> False.
Proof.
 intros a reserved v s Typed Different H. apply Different.
 symmetry. eapply V293_reservation_compatible_values;[reflexivity|exact Typed|exact H].
Qed.

(* The literal reservation/exit/Hook sequence, framing the retained half
   around the external call rather than trusting a Hook-side ownership claim. *)
Theorem V293_OSTaskCreateExt_owned_stack_fragment : forall Spec sd li I r ri tid hook
 bp bc table bn br p cpu K F Rbefore Rafter aop ir si ci
 (BeforeGood:GoodFunAsrt Rbefore)(AfterGood:GoodFunAsrt Rafter)
 target argv inputtop options stack oldpsp,
 p<13 -> GoodFrm F -> GoodFrm Rbefore ->
 V293_stack_argument_valid argv inputtop options ->
 (Rbefore ==> CurLINV li tid) -> (Rafter ==> CurLINV li tid) ->
 (Aisr ir ** V293_create_owned_pool table(br,Int.zero)p
   (Amapsto(bn,0%Z)Tint8 true(V293_byteval 0) ** K) ==>
  Aisr ir ** invlth_isr I 0(gettopis si)) ->
 let before:=@mkfunasrt (V293_create_enabled_external Rbefore aop ir si ci)
   (V293_create_enabled_external_good Rbefore aop ir si ci BeforeGood) in
 let after:=@mkfunasrt (V293_create_enabled_external Rafter aop ir si ci)
   (V293_create_enabled_external_good Rafter aop ir si ci AfterGood) in
 Spec hook=Some(V293_create_stack_resource_fpre before(V293_create_stack_values target argv inputtop options),
 V293_create_stack_resource_fpost after(V293_create_stack_values target argv inputtop options)stack,
 (Tptr Tint32,rev V293_stack_argument_types)) ->
 InfRules Spec sd li I r ri
 (V293_create_slot_state bp bc table bn br p 0 None cpu K
  (LV 108%Z @ (Tptr Tint32) |->oldpsp **
   V293_create_stack_arguments target argv inputtop options(Rbefore ** F))aop ir si ci)
 (sseq(sassign(earrayelem(evar 92%Z)(evar 101%Z))(V293_task_prio_reserved_expr 97%Z))
  (sseq(sprim excrit)(V293_TaskCreateExt_stack_call 108%Z hook 201%Z 202%Z 203%Z 204%Z)))
 (V293_create_enabled_external Rafter aop ir si ci **
  LV 108%Z @ (Tptr Tint32) |->stack **
  V293_create_stack_arguments target argv inputtop options
   (V293_create_enabled_locals bp bc p cpu
     (V293_create_owned_share table(br,Int.zero)p ** V293_create_slot_views table bn br ** F)))tid.
Proof.
 intros Spec sd li I r ri tid hook bp bc table bn br p cpu K F Rbefore Rafter aop ir si ci
 BeforeGood AfterGood target argv inputtop options stack oldpsp
 Range Frame ResourceFrame Valid Before After Close before after Lookup.
 eapply seq_rule with(p':=V293_create_slot_state bp bc table bn br p 0(Some(br,Int.zero))cpu K
  (LV 108%Z @ (Tptr Tint32) |->oldpsp **
   V293_create_stack_arguments target argv inputtop options(Rbefore ** F))aop ir si ci).
 - eapply conseq_rule;[apply V293_create_slot_prefix_zero|intros s H;apply V293_create_slot_prefix_zero;exact H| ].
   apply V293_create_prefix_reserve_hoare;[exact Range| ].
   apply V293_star_CurLINV_r. apply V293_star_CurLINV_r.
   unfold V293_create_stack_arguments. do 4 apply V293_star_CurLINV_r.
   apply V293_star_CurLINV_l;exact Before.
 - eapply seq_rule with(p':=V293_create_enabled_state bp bc p cpu
   (V293_create_owned_share table(br,Int.zero)p ** V293_create_slot_views table bn br **
   (LV 108%Z @ (Tptr Tint32) |->oldpsp **
    V293_create_stack_arguments target argv inputtop options(Rbefore ** F)))aop ir si ci).
   + apply V293_create_reservation_owned_exit.
     * unfold V293_create_stack_arguments,Alvarmapsto,Alvarenv',Aptrmapsto.
       cbn[GoodFrm]. tauto.
     * apply V293_star_CurLINV_r. unfold V293_create_stack_arguments.
       do 4 apply V293_star_CurLINV_r. apply V293_star_CurLINV_l;exact Before.
     * exact Close.
   + eapply conseq_rule with
     (p:=getasrt before ** LV 108%Z @ (Tptr Tint32) |->oldpsp **
       V293_create_stack_arguments target argv inputtop options(V293_create_enabled_locals bp bc p cpu
     (V293_create_owned_share table(br,Int.zero)p ** V293_create_slot_views table bn br ** F)))
     (q:=getasrt after ** LV 108%Z @ (Tptr Tint32) |->stack **
       V293_create_stack_arguments target argv inputtop options(V293_create_enabled_locals bp bc p cpu
     (V293_create_owned_share table(br,Int.zero)p ** V293_create_slot_views table bn br ** F))).
     * unfold before,V293_create_enabled_state,V293_create_enabled_locals,
       V293_create_enabled_external,V293_create_stack_arguments. cbn[getasrt V293_rdy_raw_cells].
       intros s H;sep auto.
     * unfold after. cbn[getasrt]. intros s H;exact H.
     * eapply V293_OSTaskCreateExt_stack_resource_call_hoare.
       -- apply V293_create_enabled_good.
          unfold V293_create_owned_share,V293_reservation_owner,V293_create_slot_views,V293_create_global_binding.
          cbn[GoodFrm];tauto.
       -- exact Valid.
       -- unfold before,V293_create_enabled_external. cbn[getasrt].
          do 2 apply V293_star_CurLINV_r. exact Before.
       -- unfold after,V293_create_enabled_external. cbn[getasrt].
          do 2 apply V293_star_CurLINV_r. exact After.
       -- exact Lookup.
Qed.
