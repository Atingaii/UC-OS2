(* Exact retained full-function code between two Hooks. No Hook is implemented
   or erased; the first statement starts AFTER a real first-Hook return. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293InitChain.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitEntry.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFunction.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitFunction.
Require Import CertiOS.certiucos.v293.code.V293OSTCBPublish.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.framework.proof.cstepLib.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope Z_scope.
Definition V293_tcb_priority_cells bp bc table bt base p slot : list V293_record_cell :=
 [((bp,0),Tint8,V293_byteval p);
  ((bc,0),Tptr V293_tcb_type,Vptr(bt,Int.repr base));
  ((table,4*Z.of_nat p),Tptr V293_tcb_type,slot)].
Definition V293_tcb_second_hook_cont f hook_init hook_create caller ks :=
 kseq (V293_TCB_publish 108%Z 93%Z 94%Z 95%Z 96%Z)
 (kseq V293_TCBInit_empty
  (kcall f (V293_TCBInit_function_body hook_init hook_create) caller ks)).

(* Stable unconditional between-Hooks interface: first Hook must have returned,
   then real priority-slot publication and second-Hook argument evaluation. *)
Theorem V293_OS_TCBInit_priority_to_second_hook : forall P f hook_init hook_create caller ks
 ge le M ir aux O op R enabled si ci bp bc table bt base p old,
 get le 101%Z=Some(bp,Tint8) -> get le 108%Z=Some(bc,Tptr V293_tcb_type) ->
 get le 92%Z=None -> get ge 92%Z=Some(table,Tarray (Tptr V293_tcb_type) 13) ->
 (p<13)%nat ->
 (ge,le,M,ir,aux,O,op) |= V293_rdy_raw_cells
  (V293_tcb_priority_cells bp bc table bt base p old) R ->
 exists Mf,
 V293_local_steps P (curs(sskip None),
  (kenil,V293_tcb_first_hook_cont f hook_init hook_create caller ks))
  ((ge,le,M),ir,(enabled,si,ci))
 (curs(sfexec hook_create (Vptr(bt,Int.repr base)::nil) (Tptr V293_tcb_type::nil)),
  (kenil,V293_tcb_second_hook_cont f hook_init hook_create caller ks))
  ((ge,le,Mf),ir,(enabled,si,ci)) /\
 (ge,le,Mf,ir,aux,O,op) |= V293_rdy_raw_cells
  (V293_tcb_priority_cells bp bc table bt base p (Vptr(bt,Int.repr base))) R /\
 (P hook_create=None -> ~exists C' state', loststep P
  (curs(sfexec hook_create (Vptr(bt,Int.repr base)::nil) (Tptr V293_tcb_type::nil)),
   (kenil,V293_tcb_second_hook_cont f hook_init hook_create caller ks))
   ((ge,le,Mf),ir,(enabled,si,ci)) C' state').
Proof.
 intros P f hook_init hook_create caller ks ge le M ir aux O op R enabled si ci
 bp bc table bt base p old PriorityLocal PtcbLocal TableLocal TableGlobal Range Owned.
 pose proof (V293_byte_type p ltac:(lia)) as PriorityValid.
 unfold V293_tcb_priority_cells in Owned.
 V293_tcb_init_read Owned 0%nat PriorityRead.
 V293_tcb_init_read Owned 1%nat PointerRead.
 destruct (V293_rekey_array_address ge le M 92%Z 101%Z V293_tcb_type table bp p
  TableLocal TableGlobal PriorityLocal PriorityRead Range) as (SlotType&SlotAddress).
 assert (Offset : (0<=4*Z.of_nat p<=Int.max_unsigned)%Z) by
  (change (0<=4*Z.of_nat p<=4294967295)%Z;lia).
 destruct (V293_rdy_assign
  (((bp,0),Tint8,V293_byteval p)::((bc,0),Tptr V293_tcb_type,Vptr(bt,Int.repr base))::nil)
  (table,4*Z.of_nat p) (Tptr V293_tcb_type) old [] (Vptr(bt,Int.repr base))
  (earrayelem(evar 92%Z)(evar 101%Z)) (evar 108%Z) (Tptr V293_tcb_type)
  R P ge le M ir aux O op) as (Mf&Assign&Final).
 { exact SlotType. }
 { exact SlotAddress. }
 { apply Int.unsigned_repr. exact Offset. }
 { V293_rdy_eval. }
 { apply eq_vptr. do 2 eexists;split;reflexivity. }
 { V293_rdy_eval. }
 { reflexivity. }
 { exact Owned. }
 V293_tcb_init_read Final 1%nat FinalPointer.
 exists Mf. split.
 - unfold V293_tcb_first_hook_cont,V293_tcb_after_init_hook,V293_TCBInit_success_suffix,
   V293_tcb_second_hook_cont.
   eapply V293_local_cons. { V293_prefix_stmt. }
   eapply V293_local_cons. { V293_prefix_stmt. }
   eapply V293_local_cons. { apply encrit_step;reflexivity. }
   eapply V293_local_cons. { V293_prefix_stmt. }
   eapply V293_local_cons. { V293_prefix_stmt. }
   eapply V293_local_trans. { apply V293_csteps_local. apply Assign. }
   eapply V293_local_cons. { V293_prefix_stmt. }
   eapply V293_local_cons. { V293_prefix_stmt. }
   eapply V293_local_cons. { apply excrit_step;reflexivity. }
   eapply V293_local_cons. { V293_prefix_stmt. }
   eapply V293_local_cons. { V293_prefix_stmt. }
   eapply V293_local_cons. { apply ostc_step. eapply stmt_step;[reflexivity| ].
     apply spcall_step with (t:=Tptr V293_tcb_type). V293_rdy_eval. }
   eapply V293_local_trans.
   { apply V293_csteps_local. apply V293_expr_steps. apply evalval_imply_estepstar.
     assert (Value : evalval (evar 108%Z) (ge,le,Mf)=Some(Vptr(bt,Int.repr base))) by V293_rdy_eval.
     exact Value. }
   eapply V293_local_cons. { apply ostc_step. eapply stmt_step;[reflexivity|apply svfevalnil_step]. }
   apply V293_local_refl.
 - split;[exact Final| ]. intros Missing. apply V293_missing_port_has_no_step. exact Missing.
Qed.
Print Assumptions V293_OS_TCBInit_priority_to_second_hook.

(* Exact cells protected across the external first-Hook obligation. The Hook
   may change unowned memory; equality of its input/output M is NOT required. *)
Definition V293_tcb_hook_cells b1 b2 b3 b4 b5 b6 b7 b8 b9 bf table bt base p
 top bottom identity size ext options next slot frame : list V293_record_cell :=
 V293_tcb_init_final_fields bt base p top bottom identity size ext options ++
 V293_tcb_init_input_cells b8 b1 b2 b3 b4 b5 b6 b7 bt base p top bottom identity size ext options ++
 V293_tcb_prefix_links bf bt base next next ++
 ((b9,0),Tint32,Vint32 Int.zero)::((table,4*Z.of_nat p),Tptr V293_tcb_type,slot)::frame.

(* CONDITIONAL longitudinal linkage, not an implementation or proof of the
   actual missing first Hook. HookReturn remains an explicit unproved premise. *)
Theorem V293_OS_TCBInit_call_to_second_hook_under_contract : forall P ks ge caller M ir aux O op enabled si ci
 f hook_init hook_create bf table bt base p top bottom identity size ext options next old slot frame,
 P f=Some (V293_TCBInit_function hook_init hook_create) ->
 get ge 91%Z=Some(bf,Tptr V293_tcb_type) ->
 get ge 92%Z=Some(table,Tarray (Tptr V293_tcb_type) 13) ->
 (p<13)%nat -> (0<=base)%Z -> (base+55<=Int.max_unsigned)%Z ->
 V293_tcb_init_values_valid top bottom identity size ext options ->
 rule_type_val_match (Tptr V293_tcb_type) next=true ->
 (forall b1 b2 b3 b4 b5 b6 b7 b8 b9 Mh,
  NoDup (V293_tcb_function_blocks b1 b2 b3 b4 b5 b6 b7 b8 b9) ->
  (ge,V293_tcb_function_env b1 b2 b3 b4 b5 b6 b7 b8 b9,Mh,ir,aux,O,op) |=
   V293_rdy_raw_cells (V293_tcb_hook_cells b1 b2 b3 b4 b5 b6 b7 b8 b9 bf table bt base p
     top bottom identity size ext options next slot frame) Atrue ->
  exists Mr,
  V293_local_steps P
   (curs(sfexec hook_init (Vptr(bt,Int.repr base)::nil) (Tptr V293_tcb_type::nil)),
    (kenil,V293_tcb_first_hook_cont f hook_init hook_create caller ks))
   ((ge,V293_tcb_function_env b1 b2 b3 b4 b5 b6 b7 b8 b9,Mh),ir,(enabled,si,ci))
   (curs(sskip None),(kenil,V293_tcb_first_hook_cont f hook_init hook_create caller ks))
   ((ge,V293_tcb_function_env b1 b2 b3 b4 b5 b6 b7 b8 b9,Mr),ir,(enabled,si,ci)) /\
  (ge,V293_tcb_function_env b1 b2 b3 b4 b5 b6 b7 b8 b9,Mr,ir,aux,O,op) |=
   V293_rdy_raw_cells (V293_tcb_hook_cells b1 b2 b3 b4 b5 b6 b7 b8 b9 bf table bt base p
     top bottom identity size ext options next slot frame) Atrue) ->
 (ge,caller,M,ir,aux,O,op) |= V293_rdy_raw_cells
 (V293_tcb_init_old_fields bt base old ++
  V293_tcb_prefix_links bf bt base (Vptr(bt,Int.repr base)) next ++
  ((table,4*Z.of_nat p),Tptr V293_tcb_type,slot)::frame) Atrue ->
 exists b1 b2 b3 b4 b5 b6 b7 b8 b9 Mf,
 NoDup (V293_tcb_function_blocks b1 b2 b3 b4 b5 b6 b7 b8 b9) /\
 V293_local_steps P
 (curs(sfexec f [options;ext;size;identity;bottom;top;V293_byteval p]
   V293_TCBInit_argument_types),(kenil,ks)) ((ge,caller,M),ir,(enabled,si,ci))
 (curs(sfexec hook_create (Vptr(bt,Int.repr base)::nil) (Tptr V293_tcb_type::nil)),
  (kenil,V293_tcb_second_hook_cont f hook_init hook_create caller ks))
 ((ge,V293_tcb_function_env b1 b2 b3 b4 b5 b6 b7 b8 b9,Mf),ir,(enabled,si,ci)) /\
 (ge,V293_tcb_function_env b1 b2 b3 b4 b5 b6 b7 b8 b9,Mf,ir,aux,O,op) |=
 V293_rdy_raw_cells (V293_tcb_hook_cells b1 b2 b3 b4 b5 b6 b7 b8 b9 bf table bt base p
  top bottom identity size ext options next (Vptr(bt,Int.repr base)) frame) Atrue /\
 (P hook_create=None -> ~exists C' state', loststep P
  (curs(sfexec hook_create (Vptr(bt,Int.repr base)::nil) (Tptr V293_tcb_type::nil)),
   (kenil,V293_tcb_second_hook_cont f hook_init hook_create caller ks))
  ((ge,V293_tcb_function_env b1 b2 b3 b4 b5 b6 b7 b8 b9,Mf),ir,(enabled,si,ci)) C' state').
Proof.
 intros P ks ge caller M ir aux O op enabled si ci f hook_init hook_create bf table bt base p
 top bottom identity size ext options next old slot frame Program FreeGlobal TableGlobal
 Range Base Bound Valid Next HookReturn Entry.
 destruct (V293_OS_TCBInit_call_to_first_hook P ks ge caller M ir aux O op enabled si ci
 f hook_init hook_create bf bt base p top bottom identity size ext options next old
 (((table,4*Z.of_nat p),Tptr V293_tcb_type,slot)::frame)
 Program FreeGlobal Range Base Bound Valid Next Entry)
 as (b1&b2&b3&b4&b5&b6&b7&b8&b9&Mi&ND&Prefix&Initialized&MissingFirst).
 destruct (HookReturn b1 b2 b3 b4 b5 b6 b7 b8 b9 Mi ND Initialized)
 as (Mr&HookExec&Returned).
 set (le:=V293_tcb_function_env b1 b2 b3 b4 b5 b6 b7 b8 b9).
 assert (PriorityLocal : get le 101%Z=Some(b1,Tint8)).
 { unfold le,V293_tcb_function_env. repeat rewrite map_get_set' by discriminate;apply map_get_set. }
 assert (PtcbLocal : get le 108%Z=Some(b8,Tptr V293_tcb_type)).
 { unfold le,V293_tcb_function_env. repeat rewrite map_get_set' by discriminate;apply map_get_set. }
 assert (TableLocal : get le 92%Z=None).
 { unfold le,V293_tcb_function_env. repeat rewrite map_get_set' by discriminate;apply map_emp_get. }
 set (rest:=V293_tcb_init_final_fields bt base p top bottom identity size ext options ++
  tl(tl(V293_tcb_init_input_cells b8 b1 b2 b3 b4 b5 b6 b7 bt base p top bottom identity size ext options)) ++
  V293_tcb_prefix_links bf bt base next next ++((b9,0),Tint32,Vint32 Int.zero)::frame).
 assert (BridgeOwned : (ge,le,Mr,ir,aux,O,op) |= V293_rdy_raw_cells
  (V293_tcb_priority_cells b1 b8 table bt base p slot) (V293_rdy_raw_cells rest Atrue)).
 { unfold V293_tcb_hook_cells in Returned.
   unfold rest,V293_tcb_priority_cells.
   unfold V293_tcb_init_final_fields,V293_tcb_init_input_cells,V293_tcb_prefix_links in Returned |- *.
   cbn [V293_rdy_raw_cells app tl] in Returned |- *. clear -Returned. sep auto. }
 destruct (V293_OS_TCBInit_priority_to_second_hook P f hook_init hook_create caller ks
  ge le Mr ir aux O op (V293_rdy_raw_cells rest Atrue) enabled si ci b1 b8 table bt base p slot
  PriorityLocal PtcbLocal TableLocal TableGlobal Range BridgeOwned)
 as (Mf&BridgeExec&Final&MissingSecond).
 exists b1. exists b2. exists b3. exists b4. exists b5. exists b6. exists b7. exists b8. exists b9. exists Mf.
 split;[exact ND| ]. split.
 - eapply V293_local_trans;[exact Prefix| ]. eapply V293_local_trans;[exact HookExec|exact BridgeExec].
 - split;[ |exact MissingSecond].
   unfold V293_tcb_hook_cells. unfold rest,V293_tcb_priority_cells in Final.
   unfold V293_tcb_init_final_fields,V293_tcb_init_input_cells,V293_tcb_prefix_links in Final |- *.
   cbn [V293_rdy_raw_cells app tl] in Final |- *. clear -Final. sep auto.
Qed.
Print Assumptions V293_OS_TCBInit_call_to_second_hook_under_contract.

(* The open HookReturn obligation cannot be discharged by a zero-step trace
   when the actual program has no definition for that Hook. *)
Theorem V293_missing_hook_cannot_return : forall P hook args types ks m ir au ks' state',
 P hook=None ->
 ~V293_local_steps P (curs(sfexec hook args types),(kenil,ks)) (m,ir,au)
    (curs(sskip None),(kenil,ks')) state'.
Proof.
 intros P hook args types ks m ir au ks' state' Missing Run.
 unfold V293_local_steps in Run.
 inversion Run as [ | y z Step Rest];subst.
 destruct y as [C1 state1]. cbn in Step.
 apply (V293_missing_port_has_no_step P hook args types ks m ir au Missing).
 exists C1. exists state1. exact Step.
Qed.
Print Assumptions V293_missing_hook_cannot_return.
