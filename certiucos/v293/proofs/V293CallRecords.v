(* Actual allocation-to-return composition. Raw views retain every pure record
   witness and reassemble the very same spatial cells, including waiting tasks.
   Concrete Hook implementations remain open, independent obligations. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.certiucos.v293.proofs.V293InitPublishRecords.
Require Import CertiOS.certiucos.v293.proofs.V293InitAllRecords.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBList.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293PublishRecords.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293StartRecord.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitEntry.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFunction.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293TCBCallSuccess.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPublish.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPriorityHook.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293NullBytes.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBClear.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitFunction.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitPrefix.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Lemma V293_owned_cells_types : forall cells ge le M ir aux O op,
 (ge,le,M,ir,aux,O,op) |= V293_owned_record_cells cells ->
 Forall (fun cell => let '(_,tp,v):=cell in rule_type_val_match tp v=true) cells.
Proof.
 induction cells as [ | [[a tp] v] tail IH];intros ge le M ir aux O op Owned;
 cbn [V293_owned_record_cells] in Owned;[constructor | ].
 apply sat_split in Owned. destruct Owned as (mh&mt&oh&ot&JM&JO&Head&Tail).
 unfold V293_owned_record_cell in Head. apply astar_l_apure_elim in Head.
 constructor;[exact (proj1 Head) |eapply IH;exact Tail].
Qed.

(* The reconstructing entailment is valid for every new frame/environment.
   Type and existential witnesses are extracted once, never guessed later. *)
Lemma V293_task_list_raw_view : forall entries R ge le M ir aux O op,
 (ge,le,M,ir,aux,O,op) |= V293_owned_task_list entries ** R ->
 exists cells,
 (ge,le,M,ir,aux,O,op) |= V293_rdy_raw_cells cells R /\
 (forall Q, V293_rdy_raw_cells cells Q ==> V293_owned_task_list entries ** Q).
Proof.
 induction entries as [ | [t [[priority status] message]] tail IH];
 intros R ge le M ir aux O op Owned.
 - exists ([] : list V293_record_cell). split;cbn [V293_rdy_raw_cells V293_owned_task_list] in *;
   [clear -Owned;sep auto |intros Q s HS;clear -HS;sep auto].
 - cbn [V293_owned_task_list] in Owned. apply astar_assoc_elim in Owned.
   apply sat_split in Owned. destruct Owned as (mh&mt&oh&ot&JM&JO&Head&Tail).
   destruct Head as [p [pend Head]]. apply astar_l_apure_elim in Head.
   destruct Head as [Bounds Head].
   pose proof (V293_owned_cells_types _ _ _ _ _ _ _ _ Head) as Types.
   apply V293_record_cells_to_raw in Head.
   destruct (IH R ge le mt ir aux ot op Tail) as (rest&Raw&Rebuild).
   exists (V293_record_layout t p status message pend++rest). split.
   + rewrite V293_raw_cells_append. apply V293_raw_cells_join.
     apply sat_split'. exists mh. exists mt. exists oh. exists ot.
     split;[exact JM | ]. split;[exact JO | ]. split;assumption.
   + intros Q s HS. rewrite V293_raw_cells_append in HS.
     apply (V293_raw_record_ownership _ _ Types) in HS.
     assert (Reassembled : s |= V293_owned_task_record t priority status message **
       (V293_owned_task_list tail ** Q)).
     { eapply astar_mono;[ |apply Rebuild |exact HS]. intros st Cell.
       exists p. exists pend. apply astar_l_apure_intro;assumption. }
     cbn [V293_owned_task_list]. clear -Reassembled. sep auto.
Qed.

Lemma V293_tcb_call_prologue_records : forall tasks P ks ge caller M ir aux O op enabled si ci
 f hi hc b1 b2 b3 b4 b5 b6 b7 b8 b9 v1 v2 v3 v4 v5 v6 v7 frame,
 P f=Some(V293_TCBInit_function hi hc) ->
 NoDup(V293_tcb_function_blocks b1 b2 b3 b4 b5 b6 b7 b8 b9) ->
 (forall b, In b(V293_tcb_function_blocks b1 b2 b3 b4 b5 b6 b7 b8 b9) -> fresh M b) ->
 V293_tcb_function_values_valid v1 v2 v3 v4 v5 v6 v7 ->
 (ge,caller,M,ir,aux,O,op) |= V293_owned_task_records tasks ** V293_rdy_raw_cells frame Atrue ->
 exists Mi,
 V293_local_steps P
  (curs(sfexec f [v7;v6;v5;v4;v3;v2;v1] V293_TCBInit_argument_types),(kenil,ks))
  ((ge,caller,M),ir,(enabled,si,ci))
  (curs(V293_TCBInit_prefix 91%Z 108%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z
    (V293_TCBInit_success_suffix hi hc)),(kenil,kcall f (V293_TCBInit_function_body hi hc) caller ks))
  ((ge,V293_tcb_function_env b1 b2 b3 b4 b5 b6 b7 b8 b9,Mi),ir,(enabled,si,ci)) /\
 (ge,V293_tcb_function_env b1 b2 b3 b4 b5 b6 b7 b8 b9,Mi,ir,aux,O,op) |=
 V293_owned_task_records tasks ** V293_rdy_raw_cells
 (V293_tcb_function_cells b1 b2 b3 b4 b5 b6 b7 b8 b9 v1 v2 v3 v4 v5 v6 v7 Vundef (Vint32 Int.zero)++frame) Atrue.
Proof.
 intros tasks P ks ge caller M ir aux O op enabled si ci f hi hc
 b1 b2 b3 b4 b5 b6 b7 b8 b9 v1 v2 v3 v4 v5 v6 v7 frame Program ND Fresh Valid Owned.
 destruct (V293_task_list_raw_view (TcbMod.lst tasks) _ _ _ _ _ _ _ _ Owned)
 as (cells&Raw&Rebuild).
 rewrite <-V293_raw_cells_append in Raw.
 destruct (V293_tcb_call_prologue P ks ge caller M ir aux O op enabled si ci f hi hc
  b1 b2 b3 b4 b5 b6 b7 b8 b9 v1 v2 v3 v4 v5 v6 v7 (cells++frame)
  Program ND Fresh Valid Raw) as (Mi&Exec&Final).
 exists Mi. split;[exact Exec | ].
 rewrite V293_raw_cells_append in Final. rewrite V293_raw_cells_append in Final.
 apply V293_raw_cells_swap in Final.
 apply Rebuild in Final. unfold V293_owned_task_records. exact Final.
Qed.

Lemma V293_raw_cells_collect_frame : forall cells A B,
 A ** V293_rdy_raw_cells cells B ==> V293_rdy_raw_cells cells (A ** B).
Proof.
 induction cells as [ | [[a tp] v] tail IH];intros A B s Owned;
 cbn [V293_rdy_raw_cells] in *;[exact Owned | ].
 assert (Reordered : s |= Amapsto a tp true v ** (A ** V293_rdy_raw_cells tail B))
 by (clear -Owned;sep auto).
 eapply astar_mono;[intros st HS;exact HS |apply IH |exact Reordered].
Qed.

Theorem V293_OS_TCBInit_call_return_records_under_hooks :
 forall tasks P f hi hc caller ks ge M ir aux O op enabled si ci
 b1 b2 b3 b4 b5 b6 b7 b8 b9 bf table bt base bh bg br bn bo obase present p g r n
 top bottom identity size ext options next old slot prev back frame,
 let le:=V293_tcb_function_env b1 b2 b3 b4 b5 b6 b7 b8 b9 in
 let blocks:=V293_tcb_function_blocks b1 b2 b3 b4 b5 b6 b7 b8 b9 in
 let tasks':=set tasks (bt,Int.repr base) (Int.repr(Z.of_nat p),rdy,Vnull) in
 let tail:=V293_tcb_creation_tail bt base bh bg br bn bo obase present p prev g r n back++frame in
 let survivors:=V293_tcb_init_record_remainder bt base top bottom identity size ext options++
  [((bf,0%Z),Tptr V293_tcb_type,next);((table,(4*Z.of_nat p)%Z),Tptr V293_tcb_type,Vptr(bt,Int.repr base))]++frame in
 let after:=V293_pub_link_cells b8 bt base bh bg br bn bo obase present p
  (V293_pub_old_head present bo obase) Vnull (Vptr(bt,Int.repr base))
  (Nat.setbit g (V293_prio_row p)) (Nat.setbit r (V293_prio_bit p)) (S n) (Vptr(bt,Int.repr base)) in
 P f=Some(V293_TCBInit_function hi hc) ->
 (forall b, In b blocks -> fresh M b) ->
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
 (ge,caller,M,ir,aux,O,op) |= V293_rdy_raw_cells
  (V293_tcb_init_old_fields bt base old ++
   V293_tcb_prefix_links bf bt base (Vptr(bt,Int.repr base)) next ++
   ((table,(4*Z.of_nat p)%Z),Tptr V293_tcb_type,slot)::tail)
  (V293_owned_task_records tasks ** Atrue) ->
 exists Mf,
 V293_local_steps P
  (curs(sfexec f [options;ext;size;identity;bottom;top;V293_byteval p]
   V293_TCBInit_argument_types),(kenil,ks)) ((ge,caller,M),ir,(enabled,si,ci))
  (curs(sskip(Some(Vint32 Int.zero))),(kenil,ks)) ((ge,caller,Mf),ir,(enabled,si,ci)) /\
 (ge,caller,Mf,ir,aux,O,op) |= V293_owned_task_records tasks' **
  V293_rdy_raw_cells (tl after++survivors) Atrue /\
 (forall b tp k, In (b,tp) (V293_tcb_function_addresses b1 b2 b3 b4 b5 b6 b7 b8 b9) ->
  k<typelen tp -> get Mf (b,Z.of_nat k)=None).
Proof.
 intros tasks P f hi hc caller ks ge M ir aux O op enabled si ci
 b1 b2 b3 b4 b5 b6 b7 b8 b9 bf table bt base bh bg br bn bo obase present p g r n
 top bottom identity size ext options next old slot prev back frame
 le blocks tasks' tail survivors after Program LocalsFresh FreeGlobal TableGlobal PubEnv Fresh Range ND Base Bound
 OldBase OldBound G Row Count Valid Next TasksAway CellsAway Hook1 Hook2 Entry.
 assert (Values : V293_tcb_function_values_valid (V293_byteval p) top bottom identity size ext options).
 { unfold V293_tcb_function_values_valid. unfold V293_tcb_init_values_valid in Valid.
   split;[apply V293_byte_type;lia |exact Valid]. }
 apply V293_raw_cells_move_frame in Entry.
 destruct (V293_tcb_call_prologue_records tasks P ks ge caller M ir aux O op enabled si ci f hi hc
  b1 b2 b3 b4 b5 b6 b7 b8 b9 (V293_byteval p) top bottom identity size ext options _
  Program ND LocalsFresh Values Entry) as (Mi&Prologue&Allocated).
 assert (PrefixEntry : (ge,le,Mi,ir,aux,O,op) |= V293_rdy_raw_cells
  (V293_tcb_init_old_fields bt base old ++
   V293_tcb_prefix_inputs b8 b1 b2 b3 b4 b5 b6 b7 Vundef p top bottom identity size ext options ++
   V293_tcb_prefix_links bf bt base (Vptr(bt,Int.repr base)) next ++
   ((b9,0%Z),Tint32,Vint32 Int.zero)::((table,(4*Z.of_nat p)%Z),Tptr V293_tcb_type,slot)::tail)
  (V293_owned_task_records tasks ** Atrue)).
 { unfold le,V293_tcb_function_cells,V293_tcb_prefix_inputs,V293_tcb_init_input_cells,
   V293_tcb_init_old_fields,V293_tcb_prefix_links in Allocated |- *.
   cbn [V293_rdy_raw_cells app tl] in Allocated |- *. clear -Allocated. sep auto. apply V293_raw_cells_collect_frame. exact Allocated. }
 destruct (V293_OS_TCBInit_prefix_return_records_under_hooks tasks P f hi hc caller ks ge Mi ir aux O op
  enabled si ci b1 b2 b3 b4 b5 b6 b7 b8 b9 bf table bt base bh bg br bn bo obase present p g r n
  top bottom identity size ext options Vundef next old slot prev back frame
  FreeGlobal TableGlobal PubEnv Fresh Range ND Base Bound OldBase OldBound G Row Count Valid Next
  TasksAway CellsAway Hook1 Hook2 PrefixEntry) as (Mf&Body&Final&Freed).
 exists Mf. split;[eapply V293_local_trans;[exact Prologue |exact Body] |split;assumption].
Qed.
Print Assumptions V293_owned_cells_types.
Print Assumptions V293_task_list_raw_view.
Print Assumptions V293_tcb_call_prologue_records.
Print Assumptions V293_OS_TCBInit_call_return_records_under_hooks.
Print Assumptions V293_raw_cells_collect_frame.
