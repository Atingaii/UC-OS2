(* Original early exits of OSTaskCreateExt. No external calls on these paths.
   Canonical global symbols, exact original declarations; disabled IE only. *)
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateSuccessInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateBodyFailure.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateExtPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateEmptyInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293TCBSuccessHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtFunction.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtPrefix.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtSuffix.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.tactics.hoareforward.init_spec.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.proofs.V293InitAllRecords.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEmptyInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPriorityHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFieldsHoare.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Inductive V293_create_rejection :=
| V293_create_bad_priority
| V293_create_from_isr
| V293_create_occupied_priority.
Definition V293_create_rejection_code k : Z :=
 match k with V293_create_bad_priority=>42%Z
 | V293_create_from_isr=>60%Z | V293_create_occupied_priority=>40%Z end.
Definition V293_create_rejection_valid k p n :=
 match k with
 | V293_create_bad_priority=>12<p /\ p<256
 | V293_create_from_isr=>p<13 /\ 0<n /\ n<256
 | V293_create_occupied_priority=>p<13
 end.
Definition V293_create_rejection_extra_cells k (table bn:block) p n (slot:addrval) : list V293_record_cell :=
 match k with
 | V293_create_bad_priority=>[]
 | V293_create_from_isr=>[((bn,0%Z),Tint8,V293_byteval n)]
 | V293_create_occupied_priority=>[((bn,0%Z),Tint8,V293_byteval 0);
    ((table,(4*Z.of_nat p)%Z),Tptr V293_tcb_type,Vptr slot)]
 end.
Definition V293_create_rejection_globals k table bn :=
 match k with
 | V293_create_bad_priority=>Aemp
 | V293_create_from_isr=>Agvarenv 99%Z Tint8(bn,0%Z)
 | V293_create_occupied_priority=>Agvarenv 99%Z Tint8(bn,0%Z) **
   Agvarenv 92%Z(Tarray(Tptr V293_tcb_type)13)(table,0%Z)
 end.
Definition V293_create_rejection_views k table bn :=
 match k with
 | V293_create_bad_priority=>Aemp
 | V293_create_from_isr=>V293_create_global_binding 99%Z Tint8 bn
 | V293_create_occupied_priority=>V293_create_global_binding 99%Z Tint8 bn **
   V293_create_global_binding 92%Z(Tarray(Tptr V293_tcb_type)13)table
 end.
Definition V293_create_rejection_cells k bp bc table bn p n slot cpu :=
 ((bp,0%Z),Tint8,V293_byteval p)::((bc,0%Z),Tint32,cpu)::
 V293_create_rejection_extra_cells k table bn p n slot.
Definition V293_create_rejection_bindings k bp bc table bn :=
 Alvarenv 101%Z Tint8(bp,0%Z) ** Alvarenv 109%Z Tint32(bc,0%Z) **
 V293_create_rejection_views k table bn.
Definition V293_create_rejection_state k bp bc table bn p n slot cpu F aop isr is cs :=
 <||aop||> ** V293_rdy_raw_cells(V293_create_rejection_cells k bp bc table bn p n slot cpu)
 (OS[isr,false,is,cs] ** (V293_create_rejection_bindings k bp bc table bn ** F)).
Definition V293_create_rejection_return k bp bc table bn p n slot F aop isr is cs : retasrt :=
 fun result=>[|result=Some(Vint32(Int.repr(V293_create_rejection_code k)))|] **
 V293_create_rejection_state k bp bc table bn p n slot(Vint32 Int.zero)F aop isr is cs.

Lemma V293_create_rejection_good : forall k bp bc table bn p n slot cpu F,
 GoodFrm F -> GoodFrm(V293_rdy_raw_cells(V293_create_rejection_cells k bp bc table bn p n slot cpu)
 (V293_create_rejection_bindings k bp bc table bn ** F)).
Proof.
 intros. destruct k;cbn[V293_rdy_raw_cells V293_create_rejection_cells
 V293_create_rejection_extra_cells V293_create_rejection_bindings V293_create_rejection_views
 V293_create_global_binding GoodFrm];tauto.
Qed.
Lemma V293_create_rejection_env : forall k bp bc table bn s,
 s |= V293_create_rejection_bindings k bp bc table bn ** Atrue ->
 get(getlenv s)101%Z=Some(bp,Tint8) /\ get(getlenv s)109%Z=Some(bc,Tint32) /\
 (k<>V293_create_bad_priority -> get(getlenv s)99%Z=None /\ get(getgenv s)99%Z=Some(bn,Tint8)) /\
 (k=V293_create_occupied_priority -> get(getlenv s)92%Z=None /\
 get(getgenv s)92%Z=Some(table,Tarray(Tptr V293_tcb_type)13)).
Proof.
 intros k bp bc table bn s H.
 assert(P:s |= Alvarenv 101%Z Tint8(bp,0%Z) ** Atrue).
 { unfold V293_create_rejection_bindings in H. clear -H. sep auto. }
 assert(C:s |= Alvarenv 109%Z Tint32(bc,0%Z) ** Atrue).
 { unfold V293_create_rejection_bindings in H. clear -H. sep auto. }
 assert(Bp:get(getlenv s)101%Z=Some(bp,Tint8)).
 { refine(V293_star_env_l _ _ (fun ge le=>get le 101%Z=Some(bp,Tint8)) _ s P).
   intros st[actual[E[B _]]]. inversion B;subst actual;exact E. }
 assert(Bc:get(getlenv s)109%Z=Some(bc,Tint32)).
 { refine(V293_star_env_l _ _ (fun ge le=>get le 109%Z=Some(bc,Tint32)) _ s C).
   intros st[actual[E[B _]]]. inversion B;subst actual;exact E. }
 split;[exact Bp| ]. split;[exact Bc| ]. split.
 - intro Needed. assert(N:s |= V293_create_global_binding 99%Z Tint8 bn ** Atrue).
   { destruct k;try contradiction;unfold V293_create_rejection_bindings,V293_create_rejection_views in H;
     clear -H;sep auto. }
   exact(V293_star_env_l _ _ (fun ge le=>get le 99%Z=None /\ get ge 99%Z=Some(bn,Tint8)) (V293_create_global_binding_env 99%Z Tint8 bn)s N).
 - intro Kind. subst k. assert(T:s |= V293_create_global_binding 92%Z(Tarray(Tptr V293_tcb_type)13)table ** Atrue).
   { unfold V293_create_rejection_bindings,V293_create_rejection_views in H. clear -H;sep auto. }
   exact(V293_star_env_l _ _ (fun ge le=>get le 92%Z=None /\ get ge 92%Z=Some(table,Tarray(Tptr V293_tcb_type)13)) (V293_create_global_binding_env 92%Z(Tarray(Tptr V293_tcb_type)13)table)s T).
Qed.
Lemma V293_create_rejection_raw_env : forall k cells bp bc table bn F isr is cs s,
 s |= V293_rdy_raw_cells cells(OS[isr,false,is,cs] **
 (V293_create_rejection_bindings k bp bc table bn ** F)) ->
 get(getlenv s)101%Z=Some(bp,Tint8) /\ get(getlenv s)109%Z=Some(bc,Tint32) /\
 (k<>V293_create_bad_priority -> get(getlenv s)99%Z=None /\ get(getgenv s)99%Z=Some(bn,Tint8)) /\
 (k=V293_create_occupied_priority -> get(getlenv s)92%Z=None /\
 get(getgenv s)92%Z=Some(table,Tarray(Tptr V293_tcb_type)13)).
Proof.
 intros. eapply V293_raw_cells_frame_env;[ |exact H]. intros st H1.
 eapply V293_star_env_r;[ |exact H1]. intros st1 H2.
 apply V293_create_rejection_env. clear -H2;sep auto.
Qed.
Lemma V293_create_rejection_cpu : forall Spec sd li I r ri tid
 k bp bc table bn p n slot old F aop isr is cs,
 (F ==> CurLINV li tid) ->
 InfRules Spec sd li I r ri
 (V293_create_rejection_state k bp bc table bn p n slot old F aop isr is cs)
 (sassign(evar 109%Z)(econst32 Int.zero))
 (V293_create_rejection_state k bp bc table bn p n slot(Vint32 Int.zero)F aop isr is cs)tid.
Proof.
 intros. unfold V293_create_rejection_state,V293_create_rejection_cells.
 eapply V293_raw_assign_hoare with(before:=[((bp,0%Z),Tint8,V293_byteval p)])
 (a:=(bc,0%Z))(rt:=Tint32).
 - reflexivity.
 - apply eq_int;auto.
 - intros s Owned.
   destruct(V293_create_rejection_raw_env _ _ _ _ _ _ _ _ _ _ _ Owned)as[_[Bc _]].
   destruct s as [[[[[[ge le] M] ir] aux] O] op].
   change(get le 109%Z=Some(bc,Tint32))in Bc.
   cbn[sat getsmem get_smem evaladdr evaltype evalval get_lenv].
   cbv delta[env var memory.ident Modules.ident]in *. rewrite Bc.
   repeat split;try reflexivity;discriminate.
 - apply V293_star_CurLINV_r. apply V293_star_CurLINV_r. exact H.
Qed.

Lemma V293_create_rejection_priority : forall k bp bc table bn p n slot cpu F isr is cs s,
 V293_create_rejection_valid k p n ->
 s |= V293_rdy_raw_cells(V293_create_rejection_cells k bp bc table bn p n slot cpu)
 (OS[isr,false,is,cs] ** (V293_create_rejection_bindings k bp bc table bn ** F)) ->
 evalval(ebinop olt(econst32(Int.repr 12))(ecast(evar 101%Z)Tint32))(getsmem s)=
 Some(Vint32(if Z.eqb (V293_create_rejection_code k) 42%Z then Int.one else Int.zero)) /\
 evaltype(ebinop olt(econst32(Int.repr 12))(ecast(evar 101%Z)Tint32))(getsmem s)=Some Tint32.
Proof.
 intros k bp bc table bn p n slot cpu F isr is cs s Range Owned.
 destruct(V293_create_rejection_raw_env _ _ _ _ _ _ _ _ _ _ _ Owned)as[Bp _].
 destruct s as [[[[[[ge le] M] ir] aux] O] op].
 cbn[getlenv getgenv get_lenv get_genv get_smem]in *.
 unfold V293_create_rejection_cells in Owned.
 assert(PBound:p<256)by(destruct k;cbn[V293_create_rejection_valid]in Range;lia).
 pose proof(V293_byte_type p PBound)as PValid.
 V293_tcb_init_read Owned 0%nat PriorityRead.
 cbn[getsmem get_smem]. split.
 - cbn[evalval evaltype get_lenv get_genv get_mem].
   cbv delta[env var memory.ident Modules.ident]in *. rewrite Bp.
   cbn beta iota. rewrite PriorityRead.
   cbn[cast_eval V293_byteval is_int_type bop_eval cmp_val cmpu].
   destruct k;cbn[V293_create_rejection_code]in *.
   + unfold Int.ltu. rewrite !Int.unsigned_repr by(unfold Int.max_unsigned,Int.modulus,Int.wordsize;cbn;lia).
     destruct(zlt 12(Z.of_nat p));[reflexivity|cbn[V293_create_rejection_valid]in Range;lia].
   + rewrite V293_create_priority_guard_false by(cbn[V293_create_rejection_valid]in Range;lia). reflexivity.
   + rewrite V293_create_priority_guard_false by exact Range. reflexivity.
 - V293_rdy_eval.
Qed.

Lemma V293_create_rejection_nesting : forall k bp bc table bn p n slot cpu F isr is cs s,
 k<>V293_create_bad_priority -> V293_create_rejection_valid k p n ->
 s |= V293_rdy_raw_cells(V293_create_rejection_cells k bp bc table bn p n slot cpu)
 (OS[isr,false,is,cs] ** (V293_create_rejection_bindings k bp bc table bn ** F)) ->
 evalval(ebinop olt(econst32 Int.zero)(ecast(evar 99%Z)Tint32))(getsmem s)=
 Some(Vint32(if Z.eqb(V293_create_rejection_code k)60%Z then Int.one else Int.zero)) /\
 evaltype(ebinop olt(econst32 Int.zero)(ecast(evar 99%Z)Tint32))(getsmem s)=Some Tint32.
Proof.
 intros k bp bc table bn p n slot cpu F isr is cs s Needed Range Owned.
 destruct(V293_create_rejection_raw_env _ _ _ _ _ _ _ _ _ _ _ Owned)as[_[_[N _]]].
 destruct(N Needed)as[Nn Gn].
 destruct s as [[[[[[ge le] M] ir] aux] O] op].
 cbn[getlenv getgenv get_lenv get_genv get_smem]in *.
 destruct k;[contradiction| | ];
 try(pose proof(V293_byte_type n ltac:(cbn[V293_create_rejection_valid]in Range;lia))as NValid);
 unfold V293_create_rejection_cells,V293_create_rejection_extra_cells in Owned;
 V293_tcb_init_read Owned 2%nat NestingRead;cbn[getsmem get_smem];split.
 - cbn[evalval evaltype get_lenv get_genv get_mem].
   cbv delta[env var memory.ident Modules.ident]in *. rewrite Nn,Gn.
   cbn beta iota. rewrite NestingRead.
   cbn[cast_eval V293_byteval is_int_type bop_eval cmp_val cmpu V293_create_rejection_code].
   unfold Int.ltu. rewrite !Int.unsigned_repr by
    (cbn[V293_create_rejection_valid]in Range;unfold Int.max_unsigned,Int.modulus,Int.wordsize;cbn;lia).
   change (Int.unsigned Int.zero) with 0%Z.
   cbv [bop_type cmp_int_type is_int_type Z.eqb Pos.eqb].
   destruct(zlt 0(Z.of_nat n));[reflexivity|cbn[V293_create_rejection_valid]in Range;lia].
 - V293_rdy_eval.
 - V293_rdy_eval.
 - V293_rdy_eval.
Qed.

Lemma V293_create_rejection_slot : forall bp bc table bn p n slot cpu F isr is cs s,
 p<13 ->
 s |= V293_rdy_raw_cells(V293_create_rejection_cells V293_create_occupied_priority bp bc table bn p n slot cpu)
 (OS[isr,false,is,cs] ** (V293_create_rejection_bindings V293_create_occupied_priority bp bc table bn ** F)) ->
 evalval(ebinop oeq(earrayelem(evar 92%Z)(evar 101%Z))(ecast enull(Tptr V293_tcb_type)))(getsmem s)=Some(Vint32 Int.zero) /\
 evaltype(ebinop oeq(earrayelem(evar 92%Z)(evar 101%Z))(ecast enull(Tptr V293_tcb_type)))(getsmem s)=Some Tint32.
Proof.
 intros bp bc table bn p n slot cpu F isr is cs s Range Owned.
 destruct(V293_create_rejection_raw_env _ _ _ _ _ _ _ _ _ _ _ Owned)as[Bp[_[_ T]]].
 destruct(T eq_refl)as[Nt Gt]. destruct s as [[[[[[ge le] M] ir] aux] O] op].
 cbn[getlenv getgenv get_lenv get_genv get_smem]in *.
 unfold V293_create_rejection_cells,V293_create_rejection_extra_cells in Owned.
 pose proof(V293_byte_type p ltac:(lia))as PValid.
 V293_tcb_init_read Owned 0%nat PriorityRead.
 V293_tcb_init_read Owned 3%nat SlotRead.
 cbn[getsmem get_smem]. split.
 - cbn[evalval evaltype get_lenv get_genv get_mem].
   cbv delta[env var memory.ident Modules.ident]in *. rewrite Nt,Gt,Bp.
   cbn beta iota. rewrite PriorityRead. cbn[load addr_to_addrval V293_byteval].
   rewrite Int.add_zero_l. unfold Int.mul.
   rewrite(Int.unsigned_repr(Z.of_nat p))by(unfold Int.max_unsigned,Int.modulus,Int.wordsize;cbn;lia).
   change(match load(Tptr V293_tcb_type)M(table,Int.unsigned(Int.repr(4*Z.of_nat p)))with
    |Some v=>val_eq v Vnull|_=>None end=Some(Vint32 Int.zero)).
   rewrite Int.unsigned_repr by(change(0<=4*Z.of_nat p<=4294967295)%Z;lia).
   change(load(Tptr V293_tcb_type)M(table,(4*Z.of_nat p)%Z)=Some(Vptr slot))in SlotRead.
   rewrite SlotRead. destruct slot. reflexivity.
 - V293_rdy_eval.
Qed.

(* Private proof combinators. Their evaluation premises are discharged from
   owned bytes below; none occurs in the public contract. *)
Lemma V293_create_reject_if_false : forall Spec sd li I r ri tid pre e body,
 (forall s,s |= pre -> evalval e(getsmem s)=Some(Vint32 Int.zero) /\ evaltype e(getsmem s)=Some Tint32) ->
 InfRules Spec sd li I r ri pre(sifthen e body)pre tid.
Proof.
 intros Spec sd li I r ri tid pre e body Eval. eapply ift_rule with(tp:=Tint32).
 - intros s H. destruct(Eval s H)as[V T]. exists(Vint32 Int.zero).
   cbn[sat]. repeat split;try assumption;discriminate.
 - intros s[H _]. exact H.
 - eapply conseq_rule with(p:=Afalse)(q:=pre).
   + intros s[H[v[V B]]]. destruct(Eval s H)as[Zero _]. rewrite Zero in V.
     inversion V;subst v. discriminate B.
   + intros s H. exact H.
   + apply pfalse_rule.
Qed.
Lemma V293_create_reject_if_true : forall Spec sd li I r ri tid pre e body,
 (forall s,s |= pre -> evalval e(getsmem s)=Some(Vint32 Int.one) /\ evaltype e(getsmem s)=Some Tint32) ->
 InfRules Spec sd li I r ri pre body Afalse tid ->
 InfRules Spec sd li I r ri pre(sifthen e body)Afalse tid.
Proof.
 intros Spec sd li I r ri tid pre e body Eval Body. eapply ift_rule with(tp:=Tint32).
 - intros s H. destruct(Eval s H)as[V T]. exists(Vint32 Int.one).
   cbn[sat]. repeat split;try assumption;discriminate.
 - intros s[H[v[V B]]]. destruct(Eval s H)as[One _]. rewrite One in V.
   inversion V;subst v. discriminate B.
 - eapply conseq_rule;[ |intros s H;exact H|exact Body]. intros s[H _]. exact H.
Qed.

Lemma V293_create_rejection_enter : forall Spec sd li I r ri tid
 k bp bc table bn p n slot cpu F aop isr is cs,
 GoodFrm F ->
 InfRules Spec sd li I r ri
 (V293_create_rejection_state k bp bc table bn p n slot cpu F aop isr is cs)(sprim encrit)
 (V293_create_rejection_state k bp bc table bn p n slot cpu F aop isr is(false::cs))tid.
Proof.
 intros. unfold V293_create_rejection_state. eapply conseq_rule.
 - apply astar_mono;[intros s H1;exact H1|apply V293_raw_cells_move_frame].
 - apply astar_mono;[intros s H1;exact H1|apply V293_raw_cells_unmove_frame].
 - apply encrit2_rule. apply V293_create_rejection_good;exact H.
Qed.
Lemma V293_create_rejection_exit : forall Spec sd li I r ri tid
 k bp bc table bn p n slot cpu F aop isr is cs,
 GoodFrm F ->
 InfRules Spec sd li I r ri
 (V293_create_rejection_state k bp bc table bn p n slot cpu F aop isr is(false::cs))(sprim excrit)
 (V293_create_rejection_state k bp bc table bn p n slot cpu F aop isr is cs)tid.
Proof.
 intros. unfold V293_create_rejection_state. eapply conseq_rule.
 - apply astar_mono;[intros s H1;exact H1|apply V293_raw_cells_move_frame].
 - apply astar_mono;[intros s H1;exact H1|apply V293_raw_cells_unmove_frame].
 - apply excrit2_rule. apply V293_create_rejection_good;exact H.
Qed.
Lemma V293_create_rejection_ret : forall Spec sd li I tid
 k bp bc table bn p n slot F aop isr is cs,
 InfRules Spec sd li I
 (V293_create_rejection_return k bp bc table bn p n slot F aop isr is cs)Afalse
 (V293_create_rejection_state k bp bc table bn p n slot(Vint32 Int.zero)F aop isr is cs)
 (srete(econst32(Int.repr(V293_create_rejection_code k))))Afalse tid.
Proof.
 intros. apply rete_rule with(v:=Vint32(Int.repr(V293_create_rejection_code k)))(t:=Tint32).
 intros s H. split.
 - unfold V293_create_rejection_return. apply astar_l_apure_intro;[exact H|reflexivity].
 - destruct_s s. destruct k;cbn[sat V293_create_rejection_code];repeat split;try reflexivity;discriminate.
Qed.

Theorem V293_OSTaskCreateExt_rejection_body_hoare : forall Spec sd li I tid
 k bp bc table bn p n slot cpu F aop isr is cs sched hook tcb,
 V293_create_rejection_valid k p n -> GoodFrm F -> (F ==> CurLINV li tid) ->
 InfRules Spec sd li I
 (V293_create_rejection_return k bp bc table bn p n slot F aop isr is cs)Afalse
 (V293_create_rejection_state k bp bc table bn p n slot cpu F aop isr is cs)
 (V293_CreateExt_body 92%Z 99%Z 97%Z 98%Z sched hook tcb)Afalse tid.
Proof.
 intros Spec sd li I tid k bp bc table bn p n slot cpu F aop isr is cs sched hook tcb Range Frame HR.
 assert(Priority:forall ci s,s |= V293_create_rejection_state k bp bc table bn p n slot(Vint32 Int.zero)F aop isr is ci ->
 evalval(ebinop olt(econst32(Int.repr 12))(ecast(evar 101%Z)Tint32))(getsmem s)=
 Some(Vint32(if Z.eqb(V293_create_rejection_code k)42%Z then Int.one else Int.zero)) /\
 evaltype(ebinop olt(econst32(Int.repr 12))(ecast(evar 101%Z)Tint32))(getsmem s)=Some Tint32).
 { intros ci s H. unfold V293_create_rejection_state in H.
   apply astar_l_aop'_elim in H. destruct H as[_ H]. eapply V293_create_rejection_priority;eassumption. }
 assert(Nesting: k<>V293_create_bad_priority -> forall ci s,
 s |= V293_create_rejection_state k bp bc table bn p n slot(Vint32 Int.zero)F aop isr is ci ->
 evalval(ebinop olt(econst32 Int.zero)(ecast(evar 99%Z)Tint32))(getsmem s)=
 Some(Vint32(if Z.eqb(V293_create_rejection_code k)60%Z then Int.one else Int.zero)) /\
 evaltype(ebinop olt(econst32 Int.zero)(ecast(evar 99%Z)Tint32))(getsmem s)=Some Tint32).
 { intros Needed ci s H. unfold V293_create_rejection_state in H.
   apply astar_l_aop'_elim in H. destruct H as[_ H]. eapply V293_create_rejection_nesting;eassumption. }
 unfold V293_CreateExt_body,V293_TaskCreateExt_body,V293_TaskCreateExt_prefix.
 eapply seq_rule. { apply V293_create_rejection_cpu. exact HR. }
 destruct k.
 - eapply seq_rule with(p':=Afalse);[ |apply pfalse_rule].
   apply V293_create_reject_if_true.
   + exact(Priority cs).
   + apply(V293_create_rejection_ret _ _ _ _ _ V293_create_bad_priority).
 - eapply seq_rule. { apply V293_create_reject_if_false. exact(Priority cs). }
   eapply seq_rule. { apply V293_create_rejection_enter. exact Frame. }
   eapply seq_rule with(p':=Afalse);[ |apply pfalse_rule].
   apply V293_create_reject_if_true.
   + exact(Nesting ltac:(discriminate)(false::cs)).
   + unfold V293_TaskCreateExt_irq_error. eapply seq_rule.
     * apply V293_create_rejection_exit. exact Frame.
     * apply(V293_create_rejection_ret _ _ _ _ _ V293_create_from_isr).
 - eapply seq_rule. { apply V293_create_reject_if_false. exact(Priority cs). }
   eapply seq_rule. { apply V293_create_rejection_enter. exact Frame. }
   eapply seq_rule. { apply V293_create_reject_if_false. exact(Nesting ltac:(discriminate)(false::cs)). }
   eapply seq_rule.
   + apply V293_create_reject_if_false. intros s H.
     unfold V293_create_rejection_state in H. apply astar_l_aop'_elim in H. destruct H as[_ H].
     eapply V293_create_rejection_slot;[exact Range|exact H].
   + unfold V293_TaskCreateExt_occupied. eapply seq_rule.
     * apply V293_create_rejection_exit. exact Frame.
     * apply(V293_create_rejection_ret _ _ _ _ _ V293_create_occupied_priority).
Qed.

Definition V293_create_reject_external k table bn p n slot R aop isr is cs :=
 <||aop||> ** V293_rdy_raw_cells(V293_create_rejection_extra_cells k table bn p n slot)
 (OS[isr,false,is,cs] ** (V293_create_rejection_globals k table bn ** R)).
Lemma V293_create_reject_external_good : forall k table bn p n slot R aop isr is cs,
 GoodFunAsrt R -> GoodFunAsrt(V293_create_reject_external k table bn p n slot R aop isr is cs).
Proof.
 intros. destruct k;cbn[V293_create_reject_external V293_create_rejection_extra_cells
 V293_create_rejection_globals V293_rdy_raw_cells GoodFunAsrt];tauto.
Qed.
Definition V293_create_reject_fpre k table bn p n slot target argv inputtop identity bottom size ext options
 R aop isr is cs(good:GoodFunAsrt R) : fpre :=
 fun vl lg tid=>@mkfunasrt
 ([|vl=V293_create_internal_values target argv inputtop p identity bottom size ext options|] **
 V293_create_reject_external k table bn p n slot R aop isr is cs)
 (conj I(V293_create_reject_external_good k table bn p n slot R aop isr is cs good)).
Definition V293_create_reject_fpost k table bn p n slot R aop isr is cs(good:GoodFunAsrt R) : fpost :=
 fun vl result lg tid=>@mkfunasrt
 ([|result=Some(Vint32(Int.repr(V293_create_rejection_code k)))|] **
 V293_create_reject_external k table bn p n slot R aop isr is cs)
 (conj I(V293_create_reject_external_good k table bn p n slot R aop isr is cs good)).

Lemma V293_create_reject_global_views : forall k table bn,
 V293_create_rejection_globals k table bn ** V293_create_internal_domain ==>
 V293_create_rejection_views k table bn ** V293_create_internal_domain.
Proof.
 intros k table bn. destruct k;cbn[V293_create_rejection_globals V293_create_rejection_views].
 - intros s H;exact H.
 - apply V293_create_success_global_view;lia.
 - intros s H.
   assert(K:s |= (Agvarenv 99%Z Tint8(bn,0%Z) ** V293_create_internal_domain) **
   Agvarenv 92%Z(Tarray(Tptr V293_tcb_type)13)(table,0%Z)). { clear -H;sep auto. }
   eapply astar_mono in K;[ |apply V293_create_success_global_view;lia|intros st HS;exact HS].
   assert(K2:s |= (Agvarenv 92%Z(Tarray(Tptr V293_tcb_type)13)(table,0%Z) ** V293_create_internal_domain) **
   V293_create_global_binding 99%Z Tint8 bn). { clear -K;sep auto. }
   eapply astar_mono in K2;[ |apply V293_create_success_global_view;lia|intros st HS;exact HS].
   clear -K2;sep auto.
Qed.
Lemma V293_create_reject_drop_views : forall k table bn,
 V293_create_rejection_views k table bn ==> V293_create_rejection_globals k table bn.
Proof.
 intros k table bn. destruct k;cbn[V293_create_rejection_views V293_create_rejection_globals].
 - intros s H;exact H.
 - intros s[G N];exact G.
 - apply astar_mono;intros s[G N];exact G.
Qed.
Definition V293_create_reject_frame target argv inputtop identity bottom size ext options err psp R :=
 LV 209%Z @ Tint8 |->err ** LV 108%Z @ (Tptr Tint32) |->psp **
 (V293_create_internal_other_parameters target argv inputtop identity bottom size ext options **
 (R ** V293_create_internal_domain)).
Lemma V293_create_reject_frame_good : forall target argv inputtop identity bottom size ext options err psp R,
 GoodFrm R -> GoodFrm(V293_create_reject_frame target argv inputtop identity bottom size ext options err psp R).
Proof.
 intros. unfold V293_create_reject_frame,V293_create_internal_other_parameters,
 Alvarmapsto,Alvarenv',Aptrmapsto,V293_create_internal_domain. cbn[GoodFrm]. tauto.
Qed.
Lemma V293_create_reject_entry : forall k target argv inputtop p identity bottom size ext options
 cpu err psp bp bc table bn n slot R aop isr is cs,
 (Alvarenv 101%Z Tint8(bp,0%Z) ** Amapsto(bp,0%Z)Tint8 true(V293_byteval p)) **
 ((Alvarenv 109%Z Tint32(bc,0%Z) ** Amapsto(bc,0%Z)Tint32 true cpu) **
 (LV 209%Z @ Tint8 |->err ** LV 108%Z @ (Tptr Tint32) |->psp **
 (V293_create_internal_other_parameters target argv inputtop identity bottom size ext options **
 (V293_create_reject_external k table bn p n slot R aop isr is cs ** V293_create_internal_domain)))) ==>
 V293_create_rejection_state k bp bc table bn p n slot cpu
 (V293_create_reject_frame target argv inputtop identity bottom size ext options err psp R) aop isr is cs.
Proof.
 intros k target argv inputtop p identity bottom size ext options cpu err psp bp bc table bn n slot R aop isr is cs s H.
 unfold V293_create_reject_external in H.
 assert(K:s |= (V293_create_rejection_globals k table bn ** V293_create_internal_domain) **
 (<||aop||> ** V293_rdy_raw_cells(V293_create_rejection_extra_cells k table bn p n slot)
 (OS[isr,false,is,cs] ** R) **
 Alvarenv 101%Z Tint8(bp,0%Z) ** Amapsto(bp,0%Z)Tint8 true(V293_byteval p) **
 Alvarenv 109%Z Tint32(bc,0%Z) ** Amapsto(bc,0%Z)Tint32 true cpu **
 LV 209%Z @ Tint8 |->err ** LV 108%Z @ (Tptr Tint32) |->psp **
 V293_create_internal_other_parameters target argv inputtop identity bottom size ext options)).
 { destruct k;cbn[V293_create_rejection_extra_cells V293_rdy_raw_cells]in *;clear -H;sep auto. }
 eapply astar_mono in K;[ |apply V293_create_reject_global_views|intros st HS;exact HS].
 unfold V293_create_rejection_state,V293_create_rejection_cells,V293_create_rejection_bindings,V293_create_reject_frame.
 destruct k;cbn[V293_create_rejection_extra_cells V293_rdy_raw_cells]in *;clear -K;sep auto.
Qed.

Lemma V293_create_reject_exit : forall k target argv inputtop p identity bottom size ext options
 err psp bp bc table bn n slot R aop isr is cs result,
 V293_create_rejection_return k bp bc table bn p n slot
 (V293_create_reject_frame target argv inputtop identity bottom size ext options err psp R)aop isr is cs result ==>
 V293_create_internal_post_cells **
 ([|result=Some(Vint32(Int.repr(V293_create_rejection_code k)))|] **
 V293_create_reject_external k table bn p n slot R aop isr is cs) ** V293_create_internal_domain.
Proof.
 intros k target argv inputtop p identity bottom size ext options err psp bp bc table bn n slot R aop isr is cs result s H.
 unfold V293_create_rejection_return in H. apply astar_l_apure_elim in H. destruct H as[Code H].
 unfold V293_create_rejection_state,V293_create_rejection_cells,V293_create_rejection_bindings,V293_create_reject_frame in H.
 assert(K:s |= (V293_create_rejection_views k table bn **
 ((Alvarenv 101%Z Tint8(bp,0%Z) ** Amapsto(bp,0%Z)Tint8 true(V293_byteval p)) **
 (Alvarenv 109%Z Tint32(bc,0%Z) ** Amapsto(bc,0%Z)Tint32 true(Vint32 Int.zero)))) **
 (<||aop||> ** V293_rdy_raw_cells(V293_create_rejection_extra_cells k table bn p n slot)
 (OS[isr,false,is,cs] ** R) ** LV 209%Z @ Tint8 |->err ** LV 108%Z @ (Tptr Tint32) |->psp **
 V293_create_internal_other_parameters target argv inputtop identity bottom size ext options ** V293_create_internal_domain)).
 { destruct k;cbn[V293_create_rejection_extra_cells V293_rdy_raw_cells]in *;clear -H;sep auto. }
 eapply astar_mono in K.
 2:{ apply astar_mono;[apply V293_create_reject_drop_views|apply astar_mono;apply V293_create_raw_local]. }
 2:{ intros st HS;exact HS. }
 assert(Ret:s |= V293_create_internal_pre_cells target argv inputtop p identity bottom size ext options **
 (V293_create_reject_external k table bn p n slot R aop isr is cs ** V293_create_internal_domain)).
 { unfold V293_create_internal_pre_cells,V293_create_internal_locals,V293_create_reject_external,
 V293_create_internal_other_parameters in *.
 destruct k;cbn[V293_create_rejection_extra_cells V293_rdy_raw_cells]in *;clear -K;sep auto. }
 eapply astar_mono in Ret;[ |apply V293_create_internal_pre_to_post|intros st HS;exact HS].
 clear -Ret Code;sep auto.
Qed.

Theorem V293_OSTaskCreateExt_rejection_internal_resources : forall Spec sd li I tid
 k table bn p n slot R aop isr is cs(good:GoodFunAsrt R)
 target argv inputtop identity bottom size ext options sched hook tcb,
 V293_create_rejection_valid k p n -> GoodFrm R -> (R ==> CurLINV li tid) ->
 InfRules Spec sd li I
 (fun result=>V293_create_internal_post_cells **
 getasrt(V293_create_reject_fpost k table bn p n slot R aop isr is cs good
 (V293_create_internal_values target argv inputtop p identity bottom size ext options)result[]tid) ** V293_create_internal_domain)Afalse
 (V293_create_internal_pre_cells target argv inputtop p identity bottom size ext options **
 V293_create_reject_external k table bn p n slot R aop isr is cs ** V293_create_internal_domain)
 (V293_CreateExt_body 92%Z 99%Z 97%Z 98%Z sched hook tcb)Afalse tid.
Proof.
 intros Spec sd li I tid k table bn p n slot R aop isr is cs good target argv inputtop identity bottom size ext options sched hook tcb Range Frame HR.
 eapply conseq_rule;[apply V293_create_internal_unpack|intros s H;exact H| ].
 apply ex_intro_rule. intro cpu. apply ex_intro_rule. intro err.
 apply ex_intro_rule. intro psp. apply ex_intro_rule. intro bp. apply ex_intro_rule. intro bc.
 eapply conseq_rule;[apply V293_create_reject_entry|intros s H;exact H| ].
 eapply r_conseq_rule with(r:=V293_create_rejection_return k bp bc table bn p n slot
 (V293_create_reject_frame target argv inputtop identity bottom size ext options err psp R)aop isr is cs)(ri:=Afalse).
 - intro result. cbn[V293_create_reject_fpost getasrt]. apply V293_create_reject_exit.
 - intros s H;exact H.
 - apply V293_OSTaskCreateExt_rejection_body_hoare.
   + exact Range.
   + apply V293_create_reject_frame_good;exact Frame.
   + unfold V293_create_reject_frame. do 3 apply V293_star_CurLINV_r.
     apply V293_star_CurLINV_l. exact HR.
Qed.

(* Single public vertical interface, on the original entire function body.
   No spec lookup, stack precondition, TCB/list premise or execution oracle. *)
Theorem V293_OSTaskCreateExt_rejection_internal_contract : forall P creator Spec sd li I tid
 k table bn p n slot R aop isr is cs(good:GoodFunAsrt R)
 target argv inputtop identity bottom size ext options sched hook tcb vl lg pre post,
 V293_create_rejection_valid k p n -> GoodFrm R -> (R ==> CurLINV li tid) ->
 P creator=Some(V293_CreateExt_function 92%Z 99%Z 97%Z 98%Z sched hook tcb) ->
 Some pre=BuildPreI P creator vl lg
 (V293_create_reject_fpre k table bn p n slot target argv inputtop identity bottom size ext options R aop isr is cs good)tid ->
 Some post=BuildRetI P creator vl lg(V293_create_reject_fpost k table bn p n slot R aop isr is cs good)tid ->
 InfRules Spec sd li I post Afalse pre
 (V293_CreateExt_body 92%Z 99%Z 97%Z 98%Z sched hook tcb)Afalse tid.
Proof.
 intros P creator Spec sd li I tid k table bn p n slot R aop isr is cs good
 target argv inputtop identity bottom size ext options sched hook tcb vl lg pre post Range Frame HR Code Pre Post.
 unfold BuildPreI in Pre. rewrite Code in Pre. cbn[V293_CreateExt_function]in Pre.
 destruct(dl_vl_match V293_CreateExt_parameters(rev vl))eqn:Typed;[ |discriminate].
 fold V293_create_internal_declarations in Pre.
 destruct(buildp V293_create_internal_declarations vl)as[owned | ]eqn:Owned;[ |discriminate].
 change(Some pre=Some(owned **
 ([|rev vl=V293_create_internal_values target argv inputtop p identity bottom size ext options|] **
 V293_create_reject_external k table bn p n slot R aop isr is cs) ** V293_create_internal_domain))in Pre.
 inversion Pre;subst pre.
 unfold BuildRetI in Post. rewrite Code in Post.
 change(Some post=Some(fun result=>V293_create_internal_post_cells **
 getasrt(V293_create_reject_fpost k table bn p n slot R aop isr is cs good
 (V293_create_internal_values target argv inputtop p identity bottom size ext options)result[]tid) ** V293_create_internal_domain))in Post.
 inversion Post;subst post.
 eapply conseq_rule with(p:=(owned ** V293_create_reject_external k table bn p n slot R aop isr is cs **
 V293_create_internal_domain) ** [|rev vl=V293_create_internal_values target argv inputtop p identity bottom size ext options|]).
 - intros s H. clear -H;sep auto.
 - intros s H;exact H.
 - apply pure_split_rule. intro Args.
   assert(VL:vl=rev(V293_create_internal_values target argv inputtop p identity bottom size ext options)).
   { rewrite <-Args. symmetry;apply rev_involutive. }
   subst vl. rewrite V293_create_internal_buildp in Owned. inversion Owned;subst owned.
   apply V293_OSTaskCreateExt_rejection_internal_resources with(good:=good);assumption.
Qed.

Print Assumptions V293_OSTaskCreateExt_rejection_body_hoare.
Print Assumptions V293_OSTaskCreateExt_rejection_internal_contract.
