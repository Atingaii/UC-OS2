(* One concrete prefix-to-return trace, not disconnected initializer and
   publication memories. The two real Hook executions remain open contracts.
   Entry is after call allocation and CPU_SR initialization, not sfexec f. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293PublishReturnRecords.
Require Import CertiOS.certiucos.v293.proofs.V293InitAllRecords.
Require Import CertiOS.certiucos.v293.proofs.V293StartRecord.
Require Import CertiOS.certiucos.v293.proofs.V293TCBCallSuccess.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitEntry.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPriorityHook.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFunction.
Require Import CertiOS.certiucos.v293.proofs.V293TCBSuccessReturn.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293PublishRecords.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPublish.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBCall.
Require Import CertiOS.certiucos.v293.proofs.V293NullBytes.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitFunction.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitPrefix.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInit.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition V293_record_hook_cells b1 b2 b3 b4 b5 b6 b7 b8 b9 bf table bt base p
 top bottom identity size ext options next slot frame : list V293_record_cell :=
 V293_tcb_init_record_remainder bt base top bottom identity size ext options ++
 V293_tcb_init_input_cells b8 b1 b2 b3 b4 b5 b6 b7 bt base p top bottom identity size ext options ++
 V293_tcb_prefix_links bf bt base next next ++
 ((b9,0%Z),Tint32,Vint32 Int.zero)::((table,(4*Z.of_nat p)%Z),Tptr V293_tcb_type,slot)::frame.

Definition V293_records_hook_return tasks P hook bt base cont ge le ir aux O op enabled si ci cells :=
 forall Mh,
 (ge,le,Mh,ir,aux,O,op) |= V293_owned_task_records tasks ** V293_rdy_raw_cells cells Atrue ->
 exists Mr,
 V293_local_steps P
  (curs(sfexec hook [Vptr(bt,Int.repr base)] [Tptr V293_tcb_type]),(kenil,cont))
  ((ge,le,Mh),ir,(enabled,si,ci))
  (curs(sskip None),(kenil,cont)) ((ge,le,Mr),ir,(enabled,si,ci)) /\
 (ge,le,Mr,ir,aux,O,op) |= V293_owned_task_records tasks ** V293_rdy_raw_cells cells Atrue.

(* This prefix result is unconditional in both Hooks. It establishes the new
   record from actual stores and retains all old records spatially. *)
Lemma V293_TCBInit_prefix_to_record_hook : forall tasks P ks ge caller M ir aux O op enabled si ci
 f hi hc b1 b2 b3 b4 b5 b6 b7 b8 b9 bf table bt base p top bottom identity size ext options
 pc next old slot frame,
 let le:=V293_tcb_function_env b1 b2 b3 b4 b5 b6 b7 b8 b9 in
 get ge 91%Z=Some(bf,Tptr V293_tcb_type) ->
 p<13 -> (0<=base)%Z -> (base+55<=Int.max_unsigned)%Z ->
 get tasks (bt,Int.repr base)=None ->
 V293_tcb_init_values_valid top bottom identity size ext options ->
 rule_type_val_match (Tptr V293_tcb_type) next=true ->
 (ge,le,M,ir,aux,O,op) |= V293_rdy_raw_cells
  (V293_tcb_init_old_fields bt base old ++
   V293_tcb_prefix_inputs b8 b1 b2 b3 b4 b5 b6 b7 pc p top bottom identity size ext options ++
   V293_tcb_prefix_links bf bt base (Vptr(bt,Int.repr base)) next ++
   ((b9,0%Z),Tint32,Vint32 Int.zero)::((table,(4*Z.of_nat p)%Z),Tptr V293_tcb_type,slot)::frame)
  (V293_owned_task_records tasks ** Atrue) ->
 exists Mf,
 V293_local_steps P
  (curs(V293_TCBInit_prefix 91%Z 108%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z
    (V293_TCBInit_success_suffix hi hc)),
   (kenil,kcall f (V293_TCBInit_function_body hi hc) caller ks)) ((ge,le,M),ir,(enabled,si,ci))
  (curs(sfexec hi [Vptr(bt,Int.repr base)] [Tptr V293_tcb_type]),
   (kenil,V293_tcb_first_hook_cont f hi hc caller ks)) ((ge,le,Mf),ir,(enabled,si,ci)) /\
 (ge,le,Mf,ir,aux,O,op) |=
  V293_owned_task_records (set tasks (bt,Int.repr base) (Int.repr(Z.of_nat p),rdy,Vnull)) **
  V293_rdy_raw_cells (V293_record_hook_cells b1 b2 b3 b4 b5 b6 b7 b8 b9 bf table bt base p
   top bottom identity size ext options next slot frame) Atrue.
Proof.
 intros tasks P ks ge caller M ir aux O op enabled si ci f hi hc b1 b2 b3 b4 b5 b6 b7 b8 b9
 bf table bt base p top bottom identity size ext options pc next old slot frame le
 Global Range Base Bound Fresh Valid Next Entry.
 assert (Env : V293_tcb_init_env le 108%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z
  b8 b1 b2 b3 b4 b5 b6 b7).
 { unfold V293_tcb_init_env,le,V293_tcb_function_env. repeat split;
   repeat rewrite map_get_set' by discriminate;apply map_get_set. }
 assert (FreeLocal : get le 91%Z=None).
 { unfold le,V293_tcb_function_env. repeat rewrite map_get_set' by discriminate;apply map_emp_get. }
 set (tail:=((b9,0%Z),Tint32,Vint32 Int.zero)::
  ((table,(4*Z.of_nat p)%Z),Tptr V293_tcb_type,slot)::frame).
 assert (Start : (ge,le,M,ir,aux,O,op) |= V293_rdy_raw_cells
  (V293_tcb_init_old_fields bt base old ++
   V293_tcb_prefix_inputs b8 b1 b2 b3 b4 b5 b6 b7 pc p top bottom identity size ext options ++
   V293_tcb_prefix_links bf bt base (Vptr(bt,Int.repr base)) next)
  (V293_rdy_raw_cells tail (V293_owned_task_records tasks ** Atrue))).
 { rewrite <-V293_raw_cells_append. unfold tail. rewrite <-app_assoc,<-app_assoc. exact Entry. }
 destruct (V293_OS_TCBInit_prefix_execution P
  (kcall f (V293_TCBInit_function_body hi hc) caller ks) ge le M ir aux O op _ enabled si ci
  91%Z 108%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z b8 b1 b2 b3 b4 b5 b6 b7 bf bt base
  p top bottom identity size ext options pc next old (V293_TCBInit_success_suffix hi hc)
  Range Base Bound FreeLocal Global Env Valid Next Start) as (Mf&Prefix&Final).
 assert (PtrRead : load (Tptr V293_tcb_type) Mf (b8,0%Z)=Some(Vptr(bt,Int.repr base))).
 { change (load (Tptr V293_tcb_type) (getmem (ge,le,Mf,ir,aux,O,op)) (b8,0%Z)=Some(Vptr(bt,Int.repr base))).
   eapply V293_rdy_raw_load;[ |reflexivity |exact Final].
   apply in_or_app. right. apply in_or_app. left. unfold V293_tcb_init_input_cells. cbn. tauto. }
 assert (Extended : (ge,le,Mf,ir,aux,O,op) |=
  V293_owned_task_records (set tasks (bt,Int.repr base) (Int.repr(Z.of_nat p),rdy,Vnull)) **
  V293_rdy_raw_cells (V293_record_hook_cells b1 b2 b3 b4 b5 b6 b7 b8 b9 bf table bt base p
   top bottom identity size ext options next slot frame) Atrue).
 { rewrite <-V293_raw_cells_append in Final. rewrite !app_assoc in Final.
   apply V293_raw_cells_move_frame in Final. rewrite !V293_raw_cells_append in Final.
   assert (Record : (ge,le,Mf,ir,aux,O,op) |= V293_owned_task_records tasks **
    (V293_owned_task_record (bt,Int.repr base) (Int.repr(Z.of_nat p)) rdy Vnull **
     V293_rdy_raw_cells (V293_tcb_init_record_remainder bt base top bottom identity size ext options)
      (V293_rdy_raw_cells
       (V293_tcb_init_input_cells b8 b1 b2 b3 b4 b5 b6 b7 bt base p top bottom identity size ext options ++
        V293_tcb_prefix_links bf bt base next next) (V293_rdy_raw_cells tail Atrue)))).
   { rewrite !V293_raw_cells_append.
     eapply astar_mono;[intros st HS;exact HS | |exact Final].
     apply V293_initialized_ready_record;[exact Range |lia |exact Valid]. }
   assert (Reordered : (ge,le,Mf,ir,aux,O,op) |=
    V293_owned_task_record (bt,Int.repr base) (Int.repr(Z.of_nat p)) rdy Vnull **
     (V293_owned_task_records tasks ** V293_rdy_raw_cells
      (V293_record_hook_cells b1 b2 b3 b4 b5 b6 b7 b8 b9 bf table bt base p
       top bottom identity size ext options next slot frame) Atrue)).
   { unfold V293_record_hook_cells. rewrite !V293_raw_cells_append. unfold tail in Record.
     rewrite !V293_raw_cells_append in Record. clear -Record. sep auto. }
   eapply V293_task_records_insert;[exact Fresh |exact Reordered]. }
 exists Mf. split;[ |exact Extended].
 eapply V293_local_trans;[exact Prefix | ].
 unfold V293_TCBInit_success_suffix,V293_tcb_first_hook_cont,V293_tcb_after_init_hook.
 assert (PtcbBinding : get le 108%Z=Some(b8,Tptr V293_tcb_type)) by exact (proj1 Env).
 eapply V293_local_cons. { V293_prefix_stmt. }
 eapply V293_local_cons. { apply ostc_step;eapply stmt_step;[reflexivity | ].
   apply spcall_step with (t:=Tptr V293_tcb_type). V293_rdy_eval. }
 eapply V293_local_trans.
 { apply V293_csteps_local. apply V293_expr_steps. apply evalval_imply_estepstar.
   assert (HookValue : evalval (evar 108%Z) (ge,le,Mf)=Some(Vptr(bt,Int.repr base))) by V293_rdy_eval.
   exact HookValue. }
 eapply V293_local_cons. { apply ostc_step;eapply stmt_step;[reflexivity |apply svfevalnil_step]. }
 apply V293_local_refl.
Qed.

Theorem V293_OS_TCBInit_prefix_return_records_under_hooks :
 forall tasks P f hi hc caller ks ge M ir aux O op enabled si ci
 b1 b2 b3 b4 b5 b6 b7 b8 b9 bf table bt base bh bg br bn bo obase present p g r n
 top bottom identity size ext options pc next old slot prev back frame,
 let le:=V293_tcb_function_env b1 b2 b3 b4 b5 b6 b7 b8 b9 in
 let blocks:=V293_tcb_function_blocks b1 b2 b3 b4 b5 b6 b7 b8 b9 in
 let tasks':=set tasks (bt,Int.repr base) (Int.repr(Z.of_nat p),rdy,Vnull) in
 let tail:=V293_tcb_creation_tail bt base bh bg br bn bo obase present p prev g r n back++frame in
 let survivors:=V293_tcb_init_record_remainder bt base top bottom identity size ext options++
  [((bf,0%Z),Tptr V293_tcb_type,next);((table,(4*Z.of_nat p)%Z),Tptr V293_tcb_type,Vptr(bt,Int.repr base))]++frame in
 let after:=V293_pub_link_cells b8 bt base bh bg br bn bo obase present p
  (V293_pub_old_head present bo obase) Vnull (Vptr(bt,Int.repr base))
  (Nat.setbit g (V293_prio_row p)) (Nat.setbit r (V293_prio_bit p)) (S n) (Vptr(bt,Int.repr base)) in
 get ge 91%Z=Some(bf,Tptr V293_tcb_type) -> get ge 92%Z=Some(table,Tarray(Tptr V293_tcb_type) 13) ->
 V293_pub_env ge le 108%Z 93%Z 94%Z 95%Z 96%Z b8 bh bg br bn ->
 get tasks (bt,Int.repr base)=None -> p<13 -> NoDup blocks ->
 (0<=base)%Z -> (base+55<=Int.max_unsigned)%Z ->
 (0<=obase)%Z -> (obase+24<=Int.max_unsigned)%Z -> g<256 -> r<256 -> n<255 ->
 V293_tcb_init_values_valid top bottom identity size ext options ->
 rule_type_val_match (Tptr V293_tcb_type) next=true ->
 (forall t value, In (t,value) (TcbMod.lst tasks') -> ~In (fst t) blocks) ->
 (forall a tp v, In (a,tp,v) (tl after++survivors) -> ~In (fst a) blocks) ->
 V293_records_hook_return tasks' P hi bt base (V293_tcb_first_hook_cont f hi hc caller ks)
  ge le ir aux O op enabled si ci
  (V293_record_hook_cells b1 b2 b3 b4 b5 b6 b7 b8 b9 bf table bt base p
   top bottom identity size ext options next slot tail) ->
 V293_records_hook_return tasks' P hc bt base (V293_tcb_second_hook_cont f hi hc caller ks)
  ge le ir aux O op enabled si ci
  (V293_record_hook_cells b1 b2 b3 b4 b5 b6 b7 b8 b9 bf table bt base p
   top bottom identity size ext options next (Vptr(bt,Int.repr base)) tail) ->
 (ge,le,M,ir,aux,O,op) |= V293_rdy_raw_cells
  (V293_tcb_init_old_fields bt base old ++
   V293_tcb_prefix_inputs b8 b1 b2 b3 b4 b5 b6 b7 pc p top bottom identity size ext options ++
   V293_tcb_prefix_links bf bt base (Vptr(bt,Int.repr base)) next ++
   ((b9,0%Z),Tint32,Vint32 Int.zero)::((table,(4*Z.of_nat p)%Z),Tptr V293_tcb_type,slot)::tail)
  (V293_owned_task_records tasks ** Atrue) ->
 exists Mf,
 V293_local_steps P
  (curs(V293_TCBInit_prefix 91%Z 108%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z
   (V293_TCBInit_success_suffix hi hc)),(kenil,kcall f (V293_TCBInit_function_body hi hc) caller ks))
  ((ge,le,M),ir,(enabled,si,ci))
  (curs(sskip(Some(Vint32 Int.zero))),(kenil,ks)) ((ge,caller,Mf),ir,(enabled,si,ci)) /\
 (ge,caller,Mf,ir,aux,O,op) |= V293_owned_task_records tasks' **
  V293_rdy_raw_cells (tl after++survivors) Atrue /\
 (forall b tp k, In (b,tp) (V293_tcb_function_addresses b1 b2 b3 b4 b5 b6 b7 b8 b9) ->
  k<typelen tp -> get Mf (b,Z.of_nat k)=None).
Proof.
 intros tasks P f hi hc caller ks ge M ir aux O op enabled si ci
 b1 b2 b3 b4 b5 b6 b7 b8 b9 bf table bt base bh bg br bn bo obase present p g r n
 top bottom identity size ext options pc next old slot prev back frame
 le blocks tasks' tail survivors after FreeGlobal TableGlobal PubEnv Fresh Range ND Base Bound
 OldBase OldBound G Row Count Valid Next TasksAway CellsAway Hook1 Hook2 Entry.
 destruct (V293_TCBInit_prefix_to_record_hook tasks P ks ge caller M ir aux O op enabled si ci
  f hi hc b1 b2 b3 b4 b5 b6 b7 b8 b9 bf table bt base p top bottom identity size ext options
  pc next old slot tail FreeGlobal Range Base Bound Fresh Valid Next Entry) as (Mi&Prefix&Initialized).
 destruct (Hook1 Mi Initialized) as (Mr&FirstExec&Returned).
 assert (PriorityLocal : get le 101%Z=Some(b1,Tint8)).
 { unfold le,V293_tcb_function_env. repeat rewrite map_get_set' by discriminate;apply map_get_set. }
 assert (PtcbLocal : get le 108%Z=Some(b8,Tptr V293_tcb_type)).
 { exact (proj1 PubEnv). }
 assert (TableLocal : get le 92%Z=None).
 { unfold le,V293_tcb_function_env. repeat rewrite map_get_set' by discriminate;apply map_emp_get. }
 set (rest:=V293_tcb_init_record_remainder bt base top bottom identity size ext options++
  tl(tl(V293_tcb_init_input_cells b8 b1 b2 b3 b4 b5 b6 b7 bt base p top bottom identity size ext options))++
  V293_tcb_prefix_links bf bt base next next++((b9,0%Z),Tint32,Vint32 Int.zero)::tail).
 assert (Bridge : (ge,le,Mr,ir,aux,O,op) |= V293_rdy_raw_cells
  (V293_tcb_priority_cells b1 b8 table bt base p slot)
  (V293_owned_task_records tasks' ** V293_rdy_raw_cells rest Atrue)).
 { unfold V293_record_hook_cells in Returned. unfold rest,V293_tcb_priority_cells.
   unfold V293_tcb_init_record_remainder,V293_tcb_init_input_cells,V293_tcb_prefix_links in Returned |- *.
   cbn [V293_rdy_raw_cells app tl] in Returned |- *. clear -Returned. sep auto. }
 destruct (V293_OS_TCBInit_priority_to_second_hook P f hi hc caller ks ge le Mr ir aux O op _
  enabled si ci b1 b8 table bt base p slot PriorityLocal PtcbLocal TableLocal TableGlobal Range Bridge)
 as (Mh&PriorityExec&PriorityFinal&MissingSecond).
 assert (SecondOwned : (ge,le,Mh,ir,aux,O,op) |= V293_owned_task_records tasks' ** V293_rdy_raw_cells
  (V293_record_hook_cells b1 b2 b3 b4 b5 b6 b7 b8 b9 bf table bt base p
   top bottom identity size ext options next (Vptr(bt,Int.repr base)) tail) Atrue).
 { unfold V293_record_hook_cells. unfold rest,V293_tcb_priority_cells in PriorityFinal.
   unfold V293_tcb_init_record_remainder,V293_tcb_init_input_cells,V293_tcb_prefix_links in PriorityFinal |- *.
   cbn [V293_rdy_raw_cells app tl] in PriorityFinal |- *. clear -PriorityFinal. sep auto. }
 destruct (Hook2 Mh SecondOwned) as (Mc&SecondExec&SecondReturned).
 assert (PubOwned : (ge,le,Mc,ir,aux,O,op) |= V293_rdy_raw_cells
  (V293_pub_link_cells b8 bt base bh bg br bn bo obase present p next prev
   (V293_pub_old_head present bo obase) g r n back)
  (V293_owned_task_records tasks' ** V293_rdy_raw_cells
   (V293_tcb_other_locals b1 b2 b3 b4 b5 b6 b7 b9 (V293_byteval p) top bottom identity size ext options
    (Vint32 Int.zero)++survivors) Atrue)).
 { unfold V293_record_hook_cells in SecondReturned. unfold tail,survivors,V293_tcb_creation_tail.
   unfold V293_tcb_creation_tail in SecondReturned.
   unfold V293_pub_link_cells,V293_tcb_other_locals,V293_tcb_init_record_remainder,
    V293_tcb_init_input_cells,V293_tcb_prefix_links in SecondReturned |- *.
   destruct present;cbn [V293_rdy_raw_cells app] in SecondReturned |- *;clear -SecondReturned;sep auto. }
 destruct (V293_OS_TCBInit_publication_return_preserves_records tasks P f hi hc caller ks ge Mc ir aux O op
  enabled si ci b1 b2 b3 b4 b5 b6 b7 b8 b9 bt base bh bg br bn bo obase present p g r n
  next prev back (V293_byteval p) top bottom identity size ext options (Vint32 Int.zero) survivors
  Fresh Range PubEnv ND Base ltac:(lia) OldBase OldBound G Row Count TasksAway CellsAway PubOwned)
 as (Mf&Suffix&Final&Freed).
 exists Mf. split.
 - eapply V293_local_trans;[exact Prefix | ]. eapply V293_local_trans;[exact FirstExec | ].
   eapply V293_local_trans;[exact PriorityExec | ]. eapply V293_local_trans;[exact SecondExec |exact Suffix].
 - split;[exact Final |exact Freed].
Qed.
Print Assumptions V293_TCBInit_prefix_to_record_hook.
Print Assumptions V293_OS_TCBInit_prefix_return_records_under_hooks.
