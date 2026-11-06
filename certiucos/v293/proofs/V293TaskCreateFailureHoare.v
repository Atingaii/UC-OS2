(* Actual TaskCreateExt failure suffix. The reserved priority cell is owned,
   not invented from the error code. Interrupts are already disabled. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateTCBCall.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPriorityHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEmptyInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TCBSnapshotInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TCBSuccessInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtSuffix.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitFunction.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtCalls.
Require Import CertiOS.certiucos.v293.proofs.V293TCBHookCall.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import Coq.Lists.List.ListNotations.
Local Open Scope nat_scope.

Definition V293_create_failure_resources table p slot F :=
 LV 101%Z @ Tint8 |-> V293_byteval p **
 LV 209%Z @ Tint8 |-> Vint32(Int.repr 66) **
 (V293_tcb_table_binding table **
 (Amapsto(table,(4*Z.of_nat p)%Z)(Tptr V293_tcb_type)true slot ** F)).
Definition V293_create_failure_state table p slot F aop isr is cs :=
 <||aop||> ** OS[isr,false,is,cs] ** V293_create_failure_resources table p slot F.
Definition V293_create_failure_return table p F aop isr is cs : retasrt :=
 fun result=>[|result=Some(Vint32(Int.repr 66))|] **
 V293_create_failure_state table p Vnull F aop isr is cs.

Lemma V293_create_failure_good : forall table p slot F,
 GoodFrm F -> GoodFrm(V293_create_failure_resources table p slot F).
Proof.
 intros. unfold V293_create_failure_resources,Alvarmapsto,Alvarenv',Aptrmapsto.
 cbn [GoodFrm V293_tcb_table_binding]. repeat split;auto.
Qed.

(* The six remaining actual arguments, read-only NULL free head, original R
   and extra frame are retained across the rollback. Priority is held once,
   by failure_resources; the reserved slot is held once, by the caller. *)
Definition V293_create_failure_kept bg top bottom identity size ext options R F :=
 LV 108%Z @ (Tptr Tint32) |-> top **
 LV 205%Z @ (Tptr Tint32) |-> bottom **
 LV 206%Z @ Tint16 |-> identity **
 LV 207%Z @ Tint32 |-> size **
 LV 208%Z @ (Tptr Tvoid) |-> ext **
 LV 204%Z @ Tint16 |-> options **
 (Agvarenv 91%Z (Tptr V293_tcb_type)(bg,0%Z) **
 (Amapsto(bg,0%Z)(Tptr V293_tcb_type)false Vnull ** (R ** F))).

Lemma V293_create_local_block : forall x tp v F s,
 s |= LV x @ tp |-> v ** F -> exists b,get(getlenv s)x=Some(b,tp).
Proof.
 intros x tp v F s H.
 refine(V293_star_env_l _ _ (fun ge le=>exists b,get le x=Some(b,tp)) _ s H).
 intros st [b Owned]. exists b.
 refine(V293_star_env_l _ _ (fun ge le=>get le x=Some(b,tp)) _ st Owned).
 intros st1 [b1 [Env [Address Empty]]].
 cbn [addrval_to_addr] in Address. inversion Address;subst b1. exact Env.
Qed.

Lemma V293_create_failure_address : forall table p slot F s,
 p<13 -> s |= V293_create_failure_resources table p slot F ->
 evaltype(earrayelem(evar 92%Z)(evar 101%Z))(getsmem s)=Some(Tptr V293_tcb_type) /\
 evaladdr(earrayelem(evar 92%Z)(evar 101%Z))(getsmem s)=
 Some(Vptr(table,Int.repr(4*Z.of_nat p))).
Proof.
 intros table p slot F s Range Owned.
 assert(Local:s |= LV 101%Z @ Tint8 |->V293_byteval p ** Atrue).
 { unfold V293_create_failure_resources in Owned. clear -Owned. sep auto. }
 destruct(V293_create_local_block _ _ _ _ _ Local)as[bp Env].
 assert(Read:s |= Rv(evar 101%Z) @ Tint8 == V293_byteval p).
 { eapply lvar_rv with(perm:=true)(P:=Atrue);[exact Local|apply V293_byte_type;lia]. }
 assert(Binding:s |= V293_tcb_table_binding table ** Atrue).
 { unfold V293_create_failure_resources in Owned. clear -Owned. sep auto. }
 pose proof(V293_star_env_l _ _ (fun ge le=>get le 92%Z=None /\
 get ge 92%Z=Some(table,Tarray(Tptr V293_tcb_type)13))
 (V293_tcb_table_binding_env table) s Binding)as[NoShadow Global].
 destruct s as [[[[[[ge le] M] ir] aux] O] op].
 change(get le 101%Z=Some(bp,Tint8))in Env.
 change(get le 92%Z=None)in NoShadow.
 change(get ge 92%Z=Some(table,Tarray(Tptr V293_tcb_type)13))in Global.
 cbn [sat getsmem get_smem evalval evaltype get_lenv get_mem] in Read.
 cbv delta [env var memory.ident Modules.ident] in *. rewrite Env in Read.
 destruct Read as[Read _].
 exact(V293_rekey_array_address ge le M 92%Z 101%Z V293_tcb_type table bp p
 NoShadow Global Env Read Range).
Qed.

Theorem V293_create_failure_store_hoare : forall Spec sd li I r ri tid
 table p slot F aop isr is cs,
 p<13 -> (F ==> CurLINV li tid) ->
 InfRules Spec sd li I r ri
 (V293_create_failure_state table p slot F aop isr is cs)
 (sassign(earrayelem(evar 92%Z)(evar 101%Z))(ecast enull(Tptr V293_tcb_type)))
 (V293_create_failure_state table p Vnull F aop isr is cs)tid.
Proof.
 intros Spec sd li I r ri tid table p slot F aop isr is cs Range HF.
 unfold V293_create_failure_state,V293_create_failure_resources.
 eapply conseq_rule with
 (p:=<||aop||> ** (OS[isr,false,is,cs] **
 (LV 101%Z @ Tint8 |-> V293_byteval p **
 (LV 209%Z @ Tint8 |-> Vint32(Int.repr 66) **
 (V293_tcb_table_binding table ** F)))) **
 Amapsto(table,(4*Z.of_nat p)%Z)(Tptr V293_tcb_type)true slot)
 (q:=<||aop||> ** (OS[isr,false,is,cs] **
 (LV 101%Z @ Tint8 |-> V293_byteval p **
 (LV 209%Z @ Tint8 |-> Vint32(Int.repr 66) **
 (V293_tcb_table_binding table ** F)))) **
 Amapsto(table,(4*Z.of_nat p)%Z)(Tptr V293_tcb_type)true Vnull).
 - intros s H. clear -H. sep auto.
 - intros s H. clear -H. sep auto.
 - replace (4*Z.of_nat p)%Z with (Int.unsigned(Int.repr(4*Z.of_nat p)))
    by (rewrite Int.unsigned_repr;[reflexivity|change(0<=4*Z.of_nat p<=4294967295)%Z;lia]).
   eapply assign_rule with(l:=(table,Int.repr(4*Z.of_nat p)))(tp2:=Tptr V293_tcb_type).
   + apply eq_vptr. do 2 eexists;split;reflexivity.
   + intros s H.
     assert(Resources:s |= V293_create_failure_resources table p slot F).
     { unfold V293_create_failure_resources.
       unfold Aptrmapsto in H. cbn [addrval_to_addr] in H.
       rewrite Int.unsigned_repr in H by(change(0<=4*Z.of_nat p<=4294967295)%Z;lia).
       clear -H. sep auto. }
     destruct(V293_create_failure_address _ _ _ _ _ Range Resources)as[Kind Address].
     split.
     * cbn [sat]. split;assumption.
     * destruct s as [[[[[[ge le] M] ir] aux] O] op].
       cbn [sat getsmem evalval evaltype get_smem]. repeat split;try reflexivity;discriminate.
   + apply V293_star_CurLINV_l. repeat apply V293_star_CurLINV_r. exact HF.
Qed.

Theorem V293_create_failure_rollback_hoare : forall Spec sd li I r ri tid
 table p slot F aop isr is cs,
 p<13 -> GoodFrm F -> (F ==> CurLINV li tid) ->
 InfRules Spec sd li I r ri
 (V293_create_failure_state table p slot F aop isr is cs)
 (V293_TaskCreateExt_rollback 92%Z 101%Z)
 (V293_create_failure_state table p Vnull F aop isr is cs)tid.
Proof.
 intros. unfold V293_TaskCreateExt_rollback.
 eapply seq_rule.
 - unfold V293_create_failure_state. apply encrit2_rule. apply V293_create_failure_good;assumption.
 - eapply seq_rule.
   + apply V293_create_failure_store_hoare;assumption.
   + unfold V293_create_failure_state. apply excrit2_rule. apply V293_create_failure_good;assumption.
Qed.

Lemma V293_create_failure_err_read : forall table p slot F aop isr is cs,
 V293_create_failure_state table p slot F aop isr is cs ==>
 Rv(evar 209%Z) @ Tint8 == Vint32(Int.repr 66).
Proof.
 intros table p slot F aop isr is cs s Owned.
 eapply lvar_rv with(perm:=true)(P:=Atrue).
 - unfold V293_create_failure_state,V293_create_failure_resources in Owned. clear -Owned. sep auto.
 - reflexivity.
Qed.

Lemma V293_create_failure_guard : forall table p slot F aop isr is cs s,
 s |= V293_create_failure_state table p slot F aop isr is cs ->
 evalval(ebinop oeq(evar 209%Z)(econst32 Int.zero))(getsmem s)=Some(Vint32 Int.zero) /\
 evaltype(ebinop oeq(evar 209%Z)(econst32 Int.zero))(getsmem s)=Some Tint32.
Proof.
 intros. pose proof(V293_create_failure_err_read _ _ _ _ _ _ _ _ _ H)as Read.
 cbn [sat] in Read. destruct Read as[Value[Kind Defined]].
 assert(Local:s |= LV 209%Z @ Tint8 |-> Vint32(Int.repr 66) ** Atrue).
 { unfold V293_create_failure_state,V293_create_failure_resources in H. clear -H. sep auto. }
 destruct(V293_create_local_block _ _ _ _ _ Local)as[b Env].
 destruct s as [[[[[[ge le] M] ir] aux] O] op].
 change(get le 209%Z=Some(b,Tint8))in Env.
 cbn [getsmem get_smem evalval evaltype get_lenv get_mem]in Value.
 cbv delta [env var memory.ident Modules.ident]in *. rewrite Env in Value.
 cbn [getsmem get_smem evalval evaltype get_lenv get_mem].
 cbv delta [env var memory.ident Modules.ident].
 rewrite Env. change(load Tint8 M(b,0%Z)=Some(Vint32(Int.repr 66)))in Value.
 cbn -[load]. rewrite Value. split;reflexivity.
Qed.

Theorem V293_OSTaskCreateExt_failure_suffix_hoare : forall Spec sd li I tid
 table p slot F aop isr is cs running sched,
 p<13 -> GoodFrm F -> (F ==> CurLINV li tid) ->
 InfRules Spec sd li I (V293_create_failure_return table p F aop isr is cs) Afalse
 (V293_create_failure_state table p slot F aop isr is cs)
 (V293_TaskCreateExt_suffix 92%Z 101%Z 209%Z running sched) Afalse tid.
Proof.
 intros. unfold V293_TaskCreateExt_suffix. eapply seq_rule.
 - eapply if_rule with(tp:=Tint32).
   + intros s Owned. exists(Vint32 Int.zero).
     destruct(V293_create_failure_guard _ _ _ _ _ _ _ _ _ Owned)as[Value Kind].
     cbn [sat]. repeat split;try assumption;discriminate.
   + eapply conseq_rule with(p:=Afalse)(q:=V293_create_failure_state table p Vnull F aop isr is cs).
     * intros s[Owned[v[Value Bool]]].
       destruct(V293_create_failure_guard _ _ _ _ _ _ _ _ _ Owned)as[Zero _].
       rewrite Zero in Value. inversion Value;subst v. discriminate Bool.
     * intros s Owned. exact Owned.
     * apply pfalse_rule.
   + eapply conseq_rule with(p:=V293_create_failure_state table p slot F aop isr is cs).
     * intros s[Owned _]. exact Owned.
     * intros s Owned. exact Owned.
     * apply V293_create_failure_rollback_hoare;assumption.
 - apply rete_rule with(v:=Vint32(Int.repr 66))(t:=Tint8).
   intros s Owned. split.
   + unfold V293_create_failure_return. apply astar_l_apure_intro;[exact Owned|reflexivity].
   + eapply V293_create_failure_err_read;exact Owned.
Qed.

(* A single stable caller interface: actual seven-argument call followed by
   the unchanged complete suffix, restricted to the physical NULL entry.
   The SAME full snapshot specification is used, not a new empty-only Spec. *)
Theorem V293_OSTaskCreateExt_empty_call_suffix_hoare : forall Spec sd li I tid f
 table reserved slot bg bt base old p top bottom identity size ext options next
 bh bgrp br bn oldblock oldbase present oldprev g row n oldback R aop isr is cs
 (good:GoodFunAsrt R) F olderr running sched,
 GoodFrm R -> GoodFrm F -> p<13 ->
 V293_tcb_init_values_valid top bottom identity size ext options ->
 (R ==> CurLINV li tid) ->
 let fp:=V293_tcb_snapshot_fpre (Vptr(bt,Int.repr base))
   (V293_tcb_empty_fpre bg R aop isr is cs good)
   (V293_tcb_success_fpre table slot bg bt base old p top bottom identity size ext options next
      bh bgrp br bn oldblock oldbase present oldprev g row n oldback R aop isr is cs good) in
 let fq:=V293_tcb_snapshot_fpost (Vptr(bt,Int.repr base))
   (V293_tcb_empty_fpost bg R aop isr is cs good)
   (V293_tcb_success_fpost table bg bt base p top bottom identity size ext options next
      bh bgrp br bn oldblock oldbase present g row n R aop isr is cs good) in
 Spec f=Some(fp,fq,(Tint8,rev V293_TCBInit_argument_types)) ->
 InfRules Spec sd li I
 (V293_create_failure_return table p
  (V293_create_failure_kept bg top bottom identity size ext options R F) aop isr is cs) Afalse
 (getasrt(fp (V293_tcb_success_arguments p top bottom identity size ext options) [logic_val Vnull] tid) **
 LV 209%Z @ Tint8 |-> olderr **
 V293_create_tcb_arguments p top bottom identity size ext options
 (V293_tcb_table_binding table ** (Amapsto(table,(4*Z.of_nat p)%Z)(Tptr V293_tcb_type)true reserved ** F)))
 (sseq (V293_TaskCreateExt_TCB_call 209%Z f 101%Z 108%Z 205%Z 206%Z 207%Z 208%Z 204%Z)
 (V293_TaskCreateExt_suffix 92%Z 101%Z 209%Z running sched)) Afalse tid.
Proof.
 intros Spec sd li I tid f table reserved slot bg bt base old p top bottom identity size ext options next
 bh bgrp br bn oldblock oldbase present oldprev g row n oldback R aop isr is cs good F olderr running sched
 RFrame Frame Range Valid HR fp fq Lookup.
 eapply seq_rule.
 - eapply V293_TaskCreateExt_TCB_snapshot_call with(good:=good).
   + cbn [V293_tcb_table_binding GoodFrm]. tauto.
   + lia.
   + exact Valid.
   + exact HR.
   + exact Lookup.
 - eapply conseq_rule with
   (p:=V293_create_failure_state table p reserved
    (V293_create_failure_kept bg top bottom identity size ext options R F) aop isr is cs)
   (q:=Afalse).
   + intros s[result Owned]. apply astar_l_apure_elim in Owned.
     destruct Owned as[Code Owned].
     destruct Code as[[_ Equal]|[Bad _]];[subst result|discriminate Bad].
     unfold fq in Owned. cbn [V293_tcb_snapshot_fpost V293_tcb_empty_fpost getasrt]in Owned.
     unfold V293_tcb_empty_external,V293_create_tcb_arguments in Owned.
     unfold V293_create_failure_state,V293_create_failure_resources,V293_create_failure_kept.
     clear -Owned. sep auto.
   + intros s H. exact H.
   + apply V293_OSTaskCreateExt_failure_suffix_hoare.
     * exact Range.
     * unfold V293_create_failure_kept,Alvarmapsto,Alvarenv',Aptrmapsto.
       cbn [GoodFrm]. repeat split;auto.
     * unfold V293_create_failure_kept. do 8 apply V293_star_CurLINV_r.
       apply V293_star_CurLINV_l. exact HR.
Qed.
