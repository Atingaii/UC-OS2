(* Direct framework Hoare for the actual between-Hook priority publication.
   Both actual CPU Hook calls and publish/return obligations remain OPEN. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.proofs.V293TCBSuccessHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFieldsHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293InitAllRecords.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBClear.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitFunction.
Require Import CertiOS.certiucos.v293.code.V293OSTCBPublish.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.framework.proof.soundness.
Require CertiOS.framework.proof.simulation.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition V293_tcb_table_binding table :=
 Agvarenv 92%Z (Tarray (Tptr V293_tcb_type) 13) (table,0%Z) //\\ A_notin_lenv 92%Z.
Definition V293_tcb_table_frame table p slot R :=
 Amapsto (table,(4*Z.of_nat p)%Z) (Tptr V293_tcb_type) true slot **
 (V293_tcb_table_binding table ** R).
Definition V293_tcb_table_state table slot bg bu bc bp bs bb bi bz be bo bt base
 p top bottom identity size ext options fields pc cpu head next R aop isr is cs :=
 <||aop||> ** V293_rdy_raw_cells
 (((table,(4*Z.of_nat p)%Z),Tptr V293_tcb_type,slot)::
  V293_tcb_success_cells bg bu bc bp bs bb bi bz be bo bt base
   p top bottom identity size ext options fields pc cpu head next)
 (OS[isr,false,is,cs] ** (V293_tcb_success_bindings bg bu bc bp bs bb bi bz be bo **
  (V293_tcb_table_binding table ** R))).
Lemma V293_tcb_table_frame_good : forall table p slot R,
 GoodFrm R -> GoodFrm (V293_tcb_table_frame table p slot R).
Proof. intros. cbn [V293_tcb_table_frame V293_tcb_table_binding GoodFrm]. tauto. Qed.
Lemma V293_tcb_table_frame_linv : forall table p slot R li tid,
 (R ==> CurLINV li tid) -> V293_tcb_table_frame table p slot R ==> CurLINV li tid.
Proof. intros table p slot R li tid HR. unfold V293_tcb_table_frame. do 2 apply V293_star_CurLINV_r. exact HR. Qed.
Lemma V293_tcb_table_binding_env : forall table s,
 s |= V293_tcb_table_binding table ->
 get (getlenv s) 92%Z=None /\ get (getgenv s) 92%Z=Some(table,Tarray (Tptr V293_tcb_type) 13).
Proof.
 intros table s [G [N Empty]]. destruct G as [b [G [B _]]]. inversion B;subst b.
 split;[ |exact G]. destruct (get (getlenv s) 92%Z) eqn:L;[ |reflexivity].
 exfalso. apply N. exists p. exact L.
Qed.
Lemma V293_tcb_table_raw_env : forall cells bg bu bc bp bs bb bi bz be bo table R isr is cs s,
 s |= V293_rdy_raw_cells cells
 (OS[isr,false,is,cs] ** (V293_tcb_success_bindings bg bu bc bp bs bb bi bz be bo **
  (V293_tcb_table_binding table ** R))) ->
 get (getlenv s) 92%Z=None /\ get (getgenv s) 92%Z=Some(table,Tarray (Tptr V293_tcb_type) 13).
Proof.
 intros. eapply V293_raw_cells_frame_env with (E:=fun ge le=>
 get le 92%Z=None /\ get ge 92%Z=Some(table,Tarray (Tptr V293_tcb_type) 13));[ |exact H].
 intros st HS.
 refine (V293_star_env_r _ _ (fun ge le=> get le 92%Z=None /\ get ge 92%Z=Some(table,Tarray (Tptr V293_tcb_type) 13)) _ st HS).
 intros st1 H1.
 refine (V293_star_env_r _ _ (fun ge le=> get le 92%Z=None /\ get ge 92%Z=Some(table,Tarray (Tptr V293_tcb_type) 13)) _ st1 H1).
 intros st2 H2.
 refine (V293_star_env_l _ _ (fun ge le=> get le 92%Z=None /\ get ge 92%Z=Some(table,Tarray (Tptr V293_tcb_type) 13)) _ st2 H2).
 intros st3 H3. apply V293_tcb_table_binding_env;exact H3.
Qed.

Lemma V293_tcb_table_success_view : forall table slot bg bu bc bp bs bb bi bz be bo bt base
 p top bottom identity size ext options fields pc cpu head next R aop isr is cs s,
 (s |= V293_tcb_table_state table slot bg bu bc bp bs bb bi bz be bo bt base
 p top bottom identity size ext options fields pc cpu head next R aop isr is cs) <->
 (s |= V293_tcb_success_state bg bu bc bp bs bb bi bz be bo bt base
 p top bottom identity size ext options fields pc cpu head next
 (V293_tcb_table_frame table p slot R) aop isr is cs).
Proof.
 intros. unfold V293_tcb_table_state,V293_tcb_success_state,V293_tcb_table_frame.
 cbn [V293_rdy_raw_cells]. split;intro HS;
 (eapply astar_mono;[intros st H;exact H| |exact HS]).
 - intros st H. apply V293_raw_cells_unmove_frame in H.
   eapply V293_raw_cells_mono;[ |exact H]. intros st1 H1. clear -H1. sep auto.
 - intros st H. apply V293_raw_cells_move_frame.
   eapply V293_raw_cells_mono;[ |exact H]. intros st1 H1. clear -H1. sep auto.
Qed.

(* Real store. The old slot is arbitrary, including Vundef; the address is
   computed using the actual priority load, not assumed as an evaluator oracle. *)
Theorem V293_OS_TCBInit_priority_store_hoare : forall Spec sd li I r ri tid aop R
 table slot bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options
 cpu head next isr is cs,
 p<13 -> (R ==> CurLINV li tid) ->
 InfRules Spec sd li I r ri
 (V293_tcb_table_state table slot bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options
 (V293_tcb_init_final_fields bt base p top bottom identity size ext options)
 (Vptr(bt,Int.repr base)) cpu head next R aop isr is cs)
 (sassign (earrayelem(evar 92%Z)(evar 101%Z)) (evar 108%Z))
 (V293_tcb_table_state table (Vptr(bt,Int.repr base)) bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options
 (V293_tcb_init_final_fields bt base p top bottom identity size ext options)
 (Vptr(bt,Int.repr base)) cpu head next R aop isr is cs) tid.
Proof.
 intros Spec sd li I r ri tid aop R table slot bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options cpu head next isr is cs Range HR.
 unfold V293_tcb_table_state,V293_tcb_success_cells,V293_tcb_init_final_fields,
 V293_tcb_prefix_inputs,V293_tcb_init_input_cells,V293_tcb_prefix_links. cbn [app].
 eapply (V293_raw_assign_hoare Spec sd li I r ri tid aop [] (table,(4*Z.of_nat p)%Z)
  (Tptr V293_tcb_type) slot _ (Vptr(bt,Int.repr base)) _ _ (Tptr V293_tcb_type)).
 - cbn [snd]. apply Int.unsigned_repr. change (0<=4*Z.of_nat p<=4294967295)%Z;lia.
 - apply eq_vptr. do 2 eexists;split;reflexivity.
 - intros s Owned. destruct s as [[[[[[ge le] M] ir] aux] O] op].
   V293_success_env Owned.
   pose proof (V293_tcb_table_raw_env _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Owned) as [TableLocal TableGlobal].
   cbn [getlenv getgenv get_smem get_lenv get_genv] in *.
   pose proof (V293_byte_type p ltac:(lia)) as PriorityValid.
   V293_tcb_init_read Owned 20 PointerRead.
   V293_tcb_init_read Owned 21 PriorityRead.
   destruct (V293_rekey_array_address ge le M 92%Z 101%Z V293_tcb_type table bp p
    TableLocal TableGlobal Bp PriorityRead Range) as [SlotType SlotAddress].
   split.
   + cbn [sat getsmem fst snd]. split;assumption.
   + cbn [sat getsmem get_smem]. repeat split;first [solve [V293_rdy_eval]|discriminate].
 - repeat apply V293_star_CurLINV_r. exact HR.
Qed.

(* The actual suffix has a right-associated continuation, so the stable
   between-Hooks rule accepts only the continuation AFTER the second excrit. *)
Theorem V293_OS_TCBInit_priority_then_hoare : forall Spec sd li I r ri tid aop R tail Q
 table slot bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options
 cpu head next isr is cs,
 p<13 -> GoodFrm R -> (R ==> CurLINV li tid) ->
 InfRules Spec sd li I r ri
 (V293_tcb_table_state table (Vptr(bt,Int.repr base)) bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options
 (V293_tcb_init_final_fields bt base p top bottom identity size ext options)
 (Vptr(bt,Int.repr base)) cpu head next R aop isr is cs) tail Q tid ->
 InfRules Spec sd li I r ri
 (V293_tcb_table_state table slot bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options
 (V293_tcb_init_final_fields bt base p top bottom identity size ext options)
 (Vptr(bt,Int.repr base)) cpu head next R aop isr is cs)
 (sseq (sprim encrit) (sseq (sassign (earrayelem(evar 92%Z)(evar 101%Z)) (evar 108%Z))
  (sseq (sprim excrit) tail))) Q tid.
Proof.
 intros. eapply seq_rule.
 - unfold V293_tcb_table_state. apply V293_tcb_success_enter.
   cbn [GoodFrm V293_tcb_table_binding]. tauto.
 - eapply seq_rule.
   + apply V293_OS_TCBInit_priority_store_hoare;assumption.
   + eapply seq_rule.
     * unfold V293_tcb_table_state. apply V293_tcb_success_exit.
       cbn [GoodFrm V293_tcb_table_binding]. tauto.
     * assumption.
Qed.

Theorem V293_OS_TCBInit_priority_bracket_hoare : forall Spec sd li I r ri tid aop R
 table slot bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options
 cpu head next isr is cs,
 p<13 -> GoodFrm R -> (R ==> CurLINV li tid) ->

 InfRules Spec sd li I r ri (V293_tcb_table_state table slot bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options
 (V293_tcb_init_final_fields bt base p top bottom identity size ext options)
 (Vptr(bt,Int.repr base)) cpu head next R aop isr is cs)
 (sseq (sprim encrit) (sseq (sassign (earrayelem(evar 92%Z)(evar 101%Z)) (evar 108%Z)) (sprim excrit)))
 (V293_tcb_table_state table (Vptr(bt,Int.repr base)) bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options
 (V293_tcb_init_final_fields bt base p top bottom identity size ext options)
 (Vptr(bt,Int.repr base)) cpu head next R aop isr is cs) tid.
Proof.
 intros. eapply seq_rule.
 - unfold V293_tcb_table_state. apply V293_tcb_success_enter.
   cbn [GoodFrm V293_tcb_table_binding]. tauto.
 - eapply seq_rule.
   + apply V293_OS_TCBInit_priority_store_hoare;assumption.
   + unfold V293_tcb_table_state. apply V293_tcb_success_exit.
     cbn [GoodFrm V293_tcb_table_binding]. tauto.
Qed.

(* OPEN contracts concern exactly two real scall statements and the actual
   publication/return block. The between-Hooks store is no longer a premise. *)
Theorem V293_OS_TCBInit_suffix_split_hoare : forall Spec sd li I r ri tid hi hc aop R
 table slot bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options
 cpu head next isr is cs,
 p<13 -> GoodFrm R -> (R ==> CurLINV li tid) ->

 InfRules Spec sd li I r ri (V293_tcb_table_state table slot bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options
 (V293_tcb_init_final_fields bt base p top bottom identity size ext options)
 (Vptr(bt,Int.repr base)) cpu head next R aop isr is cs) (scall hi [evar 108%Z]) (V293_tcb_table_state table slot bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options
 (V293_tcb_init_final_fields bt base p top bottom identity size ext options)
 (Vptr(bt,Int.repr base)) cpu head next R aop isr is cs) tid ->
 InfRules Spec sd li I r ri (V293_tcb_table_state table (Vptr(bt,Int.repr base)) bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options
 (V293_tcb_init_final_fields bt base p top bottom identity size ext options)
 (Vptr(bt,Int.repr base)) cpu head next R aop isr is cs) (scall hc [evar 108%Z]) (V293_tcb_table_state table (Vptr(bt,Int.repr base)) bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options
 (V293_tcb_init_final_fields bt base p top bottom identity size ext options)
 (Vptr(bt,Int.repr base)) cpu head next R aop isr is cs) tid ->
 InfRules Spec sd li I r ri (V293_tcb_table_state table (Vptr(bt,Int.repr base)) bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options
 (V293_tcb_init_final_fields bt base p top bottom identity size ext options)
 (Vptr(bt,Int.repr base)) cpu head next R aop isr is cs) (V293_TCB_publish 108%Z 93%Z 94%Z 95%Z 96%Z) Afalse tid ->
 InfRules Spec sd li I r ri (V293_tcb_table_state table slot bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options
 (V293_tcb_init_final_fields bt base p top bottom identity size ext options)
 (Vptr(bt,Int.repr base)) cpu head next R aop isr is cs) (V293_TCBInit_success_suffix hi hc) Afalse tid.
Proof.
 intros. unfold V293_TCBInit_success_suffix. eapply seq_rule;[eassumption| ].
 eapply V293_OS_TCBInit_priority_then_hoare;try eassumption.
 eapply seq_rule;eassumption.
Qed.

Theorem V293_OS_TCBInit_nonempty_body_split_hoare : forall Spec sd li I r ri tid hi hc aop R
 table slot bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options
 old pc cpu next isr is cs,
 p<13 -> (0<=base)%Z -> (base+55<=Int.max_unsigned)%Z ->
 V293_tcb_init_values_valid top bottom identity size ext options ->
 rule_type_val_match (Tptr V293_tcb_type) next=true -> GoodFrm R -> (R ==> CurLINV li tid) ->
 InfRules Spec sd li I r ri (V293_tcb_table_state table slot bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options
 (V293_tcb_init_final_fields bt base p top bottom identity size ext options)
 (Vptr(bt,Int.repr base)) (Vint32 Int.zero) next next R aop isr is cs) (scall hi [evar 108%Z]) (V293_tcb_table_state table slot bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options
 (V293_tcb_init_final_fields bt base p top bottom identity size ext options)
 (Vptr(bt,Int.repr base)) (Vint32 Int.zero) next next R aop isr is cs) tid ->
 InfRules Spec sd li I r ri (V293_tcb_table_state table (Vptr(bt,Int.repr base)) bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options
 (V293_tcb_init_final_fields bt base p top bottom identity size ext options)
 (Vptr(bt,Int.repr base)) (Vint32 Int.zero) next next R aop isr is cs) (scall hc [evar 108%Z]) (V293_tcb_table_state table (Vptr(bt,Int.repr base)) bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options
 (V293_tcb_init_final_fields bt base p top bottom identity size ext options)
 (Vptr(bt,Int.repr base)) (Vint32 Int.zero) next next R aop isr is cs) tid ->
 InfRules Spec sd li I r ri (V293_tcb_table_state table (Vptr(bt,Int.repr base)) bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options
 (V293_tcb_init_final_fields bt base p top bottom identity size ext options)
 (Vptr(bt,Int.repr base)) (Vint32 Int.zero) next next R aop isr is cs) (V293_TCB_publish 108%Z 93%Z 94%Z 95%Z 96%Z) Afalse tid ->
 InfRules Spec sd li I r ri
 (V293_tcb_table_state table slot bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options
 (V293_tcb_init_old_fields bt base old)
 pc cpu (Vptr(bt,Int.repr base)) next R aop isr is cs)
 (V293_TCBInit_function_body hi hc) Afalse tid.
Proof.
 intros Spec sd li I r ri tid hi hc aop R table slot bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options old pc cpu next isr is cs Range Base Bound Valid Next Frame HR InitHook CreateHook Publish.
 eapply conseq_rule.
 - intros s HS. exact (proj1 (V293_tcb_table_success_view table slot bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options (V293_tcb_init_old_fields bt base old) pc cpu (Vptr(bt,Int.repr base)) next R aop isr is cs s) HS).
 - intros s HS. exact HS.
 - apply V293_OS_TCBInit_nonempty_body_with_suffix_hoare;try assumption.
   + apply V293_tcb_table_frame_good;exact Frame.
   + apply V293_tcb_table_frame_linv;exact HR.
   + eapply conseq_rule.
     * intros s HS. exact (proj2 (V293_tcb_table_success_view table slot bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options (V293_tcb_init_final_fields bt base p top bottom identity size ext options) (Vptr(bt,Int.repr base)) (Vint32 Int.zero) next next R aop isr is cs s) HS).
     * intros s HS. exact HS.
     * apply V293_OS_TCBInit_suffix_split_hoare;assumption.
Qed.

Theorem V293_OS_TCBInit_priority_bracket_semantics : forall Spec sd li I r ri tid aop R
 table slot bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options
 cpu head next isr is cs,
 p<13 -> GoodFrm R -> (R ==> CurLINV li tid) ->

 simulation.RuleSem Spec sd li I r ri (V293_tcb_table_state table slot bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options
 (V293_tcb_init_final_fields bt base p top bottom identity size ext options)
 (Vptr(bt,Int.repr base)) cpu head next R aop isr is cs)
 (sseq (sprim encrit) (sseq (sassign (earrayelem(evar 92%Z)(evar 101%Z)) (evar 108%Z)) (sprim excrit)))
 (V293_tcb_table_state table (Vptr(bt,Int.repr base)) bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options
 (V293_tcb_init_final_fields bt base p top bottom identity size ext options)
 (Vptr(bt,Int.repr base)) cpu head next R aop isr is cs) tid.
Proof. intros. apply RuleSound. apply V293_OS_TCBInit_priority_bracket_hoare;assumption. Qed.
