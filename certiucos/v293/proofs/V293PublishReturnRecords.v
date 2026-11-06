(* Joint task-record/raw-cell ownership survives actual local-object freeing.
   Only memory-only resources cross the caller-environment restoration. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.tactics.basetac.join_lib.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.proofs.V293PublishRecords.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPublish.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.proofs.V293TCBSuccessReturn.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateReturn.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPriorityHook.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFunction.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBCall.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBList.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBClear.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293NullBytes.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitFunction.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitPrefix.
Require Import CertiOS.certiucos.v293.code.V293OSTCBPublish.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Lemma V293_records_raw_return_many : forall tasks cells R freed ge le M ir aux O op caller Mf,
 (forall t value, In (t,value) (TcbMod.lst tasks) -> ~In (fst t) freed) ->
 (forall a tp v, In (a,tp,v) cells -> ~In (fst a) freed) ->
 (forall c i, ~In c freed -> get Mf (c,i)=get M (c,i)) ->
 (ge,le,M,ir,aux,O,op) |=
   V293_owned_task_records tasks ** V293_rdy_raw_cells cells R ->
 (ge,caller,Mf,ir,aux,O,op) |=
   V293_owned_task_records tasks ** V293_rdy_raw_cells cells Atrue.
Proof.
 intros tasks cells R freed ge le M ir aux O op caller Mf TasksAway CellsAway Frame Owned.
 assert (Joint : (ge,le,M,ir,aux,O,op) |=
  (V293_owned_task_records tasks ** V293_rdy_raw_cells cells Aemp) ** R).
 { assert (Split : (ge,le,M,ir,aux,O,op) |=
    V293_owned_task_records tasks ** (V293_rdy_raw_cells cells Aemp ** R)).
   { eapply astar_mono;[intros st HS;exact HS |apply V293_raw_cells_separate |exact Owned]. }
   clear -Split. sep auto. }
 apply sat_split in Joint. destruct Joint as (mp&mr&opart&orest&JM&JO&Part&Rest).
 pose proof Part as Pieces. apply sat_split in Pieces.
 destruct Pieces as (mt&mc&ot&oc&JMC&JOC&Tasks&Cells).
 destruct (V293_owned_task_list_local _ _ _ _ _ _ _ _ Tasks) as [Empty [Support Rebase]].
 subst ot.
 assert (Absent : forall c i, In c freed -> get mp (c,i)=None).
 { intros c i Member. erewrite map_join_get_none;[ |exact JMC | ].
   - eapply V293_raw_cells_absent_block;[ |exact Cells].
     intros a tp v InCell Same. apply (CellsAway a tp v InCell). rewrite Same. exact Member.
   - apply Support. intros t value InTask Same.
     apply (TasksAway t value InTask). rewrite <-Same. exact Member. }
 assert (Sub : Maps.sub mp Mf).
 { unfold addr in *. apply sub_semp;[reflexivity | ]. intros [c i].
   destruct (in_dec Pos.eq_dec c freed) as [Member |Outside].
   - rewrite Absent by exact Member. destruct (get Mf (c,i));exact I.
   - rewrite Frame by exact Outside.
     destruct (get mp (c,i)) as [[permission value] | ] eqn:Cell.
     + destruct (@sub_semp1 (block*offset) (bool*memval) mem memMap mp M (c,i)
         (permission,value) eq_refl ltac:(exists mr;exact JM) Cell) as [Same |[Split Read]].
       * rewrite Same. destruct permission;reflexivity.
       * rewrite Split. destruct permission;cbn in *;try discriminate;reflexivity.
     + destruct (get M (c,i));exact I. }
 destruct Sub as [remaining Joined].
 assert (Rebased : (ge,caller,mp,ir,aux,opart,op) |=
   V293_owned_task_records tasks ** V293_rdy_raw_cells cells Aemp).
 { apply sat_split'. exists mt. exists mc. exists (emp:osabst). exists oc.
   split;[exact JMC | ]. split;[exact JOC | ]. split;[apply Rebase | ].
   eapply V293_raw_cells_environment;[left;reflexivity |exact Cells]. }
 assert (Kept : (ge,caller,Mf,ir,aux,O,op) |=
   (V293_owned_task_records tasks ** V293_rdy_raw_cells cells Aemp) ** Atrue).
 { apply sat_split'. exists mp. exists remaining. exists opart. exists orest.
   split;[exact Joined | ]. split;[exact JO | ]. split;[exact Rebased |exact I]. }
 apply astar_assoc_elim in Kept.
 eapply astar_mono;[intros st HS;exact HS |apply V293_raw_cells_join |exact Kept].
Qed.

Theorem V293_OS_TCBInit_publication_return_preserves_records :
 forall tasks P f hi hc caller ks ge M ir aux O op enabled si ci
 b1 b2 b3 b4 b5 b6 b7 b8 b9 bt base bh bg br bn bo obase present p g r n
 oldnext oldprev oldback v1 v2 v3 v4 v5 v6 v7 saved frame,
 let le:=V293_tcb_function_env b1 b2 b3 b4 b5 b6 b7 b8 b9 in
 let blocks:=V293_tcb_function_blocks b1 b2 b3 b4 b5 b6 b7 b8 b9 in
 let tasks':=set tasks (bt,Int.repr base) (Int.repr(Z.of_nat p),rdy,Vnull) in
 let before:=V293_pub_link_cells b8 bt base bh bg br bn bo obase present p oldnext oldprev
   (V293_pub_old_head present bo obase) g r n oldback in
 let after:=V293_pub_link_cells b8 bt base bh bg br bn bo obase present p
   (V293_pub_old_head present bo obase) Vnull (Vptr(bt,Int.repr base))
   (Nat.setbit g (V293_prio_row p)) (Nat.setbit r (V293_prio_bit p)) (S n) (Vptr(bt,Int.repr base)) in
 get tasks (bt,Int.repr base)=None -> p<13 ->
 V293_pub_env ge le 108%Z 93%Z 94%Z 95%Z 96%Z b8 bh bg br bn ->
 NoDup blocks -> (0<=base)%Z -> (base+54<=Int.max_unsigned)%Z ->
 (0<=obase)%Z -> (obase+24<=Int.max_unsigned)%Z -> g<256 -> r<256 -> n<255 ->
 (forall t value, In (t,value) (TcbMod.lst tasks') -> ~In (fst t) blocks) ->
 (forall a tp v, In (a,tp,v) (tl after++frame) -> ~In (fst a) blocks) ->
 (ge,le,M,ir,aux,O,op) |= V293_rdy_raw_cells before
  (V293_owned_task_records tasks' ** V293_rdy_raw_cells
   (V293_tcb_other_locals b1 b2 b3 b4 b5 b6 b7 b9 v1 v2 v3 v4 v5 v6 v7 saved++frame) Atrue) ->
 exists Mf,
 V293_local_steps P
  (curs(sskip None),(kenil,V293_tcb_second_hook_cont f hi hc caller ks))
  ((ge,le,M),ir,(enabled,si,ci))
  (curs(sskip(Some(Vint32 Int.zero))),(kenil,ks)) ((ge,caller,Mf),ir,(enabled,si,ci)) /\
 (ge,caller,Mf,ir,aux,O,op) |=
  V293_owned_task_records tasks' ** V293_rdy_raw_cells (tl after++frame) Atrue /\
 (forall b tp k, In (b,tp) (V293_tcb_function_addresses b1 b2 b3 b4 b5 b6 b7 b8 b9) ->
   (k<typelen tp)%nat -> get Mf (b,Z.of_nat k)=None).
Proof.
 intros tasks P f hi hc caller ks ge M ir aux O op enabled si ci
 b1 b2 b3 b4 b5 b6 b7 b8 b9 bt base bh bg br bn bo obase present p g r n
 oldnext oldprev oldback v1 v2 v3 v4 v5 v6 v7 saved frame
 le blocks tasks' before after Fresh Range Env ND Base Bound OldBase OldBound G Row Count TasksAway CellsAway Owned.
 destruct (V293_OS_TCBInit_publication_preserves_records tasks P
  (kseq V293_TCBInit_empty (kcall f (V293_TCBInit_function_body hi hc) caller ks))
  ge le M ir aux O op _ enabled si ci 108%Z 93%Z 94%Z 95%Z 96%Z
  b8 bt base bh bg br bn bo obase present p g r n oldnext oldprev oldback
  Fresh Range Env Base Bound OldBase OldBound G Row Count Owned) as (Ms&Publish&Final).
 assert (Layout : getaddr le=V293_tcb_function_addresses b1 b2 b3 b4 b5 b6 b7 b8 b9)
   by apply V293_tcb_function_layout.
 assert (Locals : (ge,le,Ms,ir,aux,O,op) |=
   V293_rdy_raw_cells (V293_tcb_function_cells b1 b2 b3 b4 b5 b6 b7 b8 b9
    v1 v2 v3 v4 v5 v6 v7 (Vptr(bt,Int.repr base)) saved) Atrue).
 { unfold after,V293_pub_link_cells,V293_tcb_other_locals in Final.
   unfold V293_tcb_function_cells. destruct present;cbn [app V293_rdy_raw_cells] in Final |- *;
   clear -Final;sep auto. }
 assert (Writable : forall b tp, In (b,tp) (getaddr le) -> V293_bytes_writable Ms b 0 (typelen tp)).
 { intros b tp Member. rewrite Layout in Member. unfold V293_tcb_function_addresses in Member.
   repeat destruct Member as [E|Member];try contradiction;inversion E;subst.
   all: eapply V293_create_owned_writable;[ |exact Locals].
   all: unfold V293_tcb_function_cells;cbn [In];eauto 15. }
 assert (FreeND : NoDup (map fst (getaddr le))) by (rewrite Layout;exact ND).
 destruct (V293_error_return_execution P
  (kseq V293_TCBInit_empty (kcall f (V293_TCBInit_function_body hi hc) caller ks))
  ge le caller Ms f (V293_TCBInit_function_body hi hc) ks 0 eq_refl FreeND Writable)
  as (Mf&Return&Preserve&Removed).
 exists Mf. split.
 - eapply V293_local_cons. { unfold V293_tcb_second_hook_cont. V293_prefix_stmt. }
   eapply V293_local_trans;[exact Publish |apply V293_csteps_local;exact Return].
 - split.
   + eapply V293_records_raw_return_many with (M:=Ms) (le:=le) (freed:=blocks)
      (R:=V293_rdy_raw_cells (V293_tcb_function_cells b1 b2 b3 b4 b5 b6 b7 b8 b9
       v1 v2 v3 v4 v5 v6 v7 (Vptr(bt,Int.repr base)) saved) Atrue).
     * exact TasksAway.
     * exact CellsAway.
     * intros b i Outside. apply Preserve. rewrite Layout. exact Outside.
     * eapply astar_mono;[intros st HS;exact HS | |exact Final].
       intros st HS. rewrite V293_raw_cells_append.
       eapply V293_raw_cells_mono;[apply V293_raw_cells_swap | ].
       unfold after,V293_pub_link_cells,V293_tcb_function_cells,V293_tcb_other_locals in HS |- *.
       destruct present;cbn [tl app V293_rdy_raw_cells] in HS |- *;clear -HS;sep auto.
   + intros b tp k Member BoundK. apply (Removed b tp k);[rewrite Layout;exact Member |exact BoundK].
Qed.
Print Assumptions V293_records_raw_return_many.
Print Assumptions V293_OS_TCBInit_publication_return_preserves_records.
