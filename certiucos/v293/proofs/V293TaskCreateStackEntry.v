(* ADR0007 lowers a task entry to the EXISTING framework integer selector.
   Continuous body-prefix plus four actual argument evaluations; no Hook
   implementation, call-allocation, source suffix or GOOD_OS claim. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtPrefix.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateExtPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293NullBytes.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.framework.proof.cstepLib.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope Z_scope.
Definition V293_task_selector f := Vint32(Int.repr f).
Lemma V293_task_selector_decode : forall f, 0<=f<=Int.max_unsigned ->
 vtoZ(V293_task_selector f)=Some f.
Proof. intros f Range. unfold V293_task_selector,vtoZ. rewrite Int.unsigned_repr by exact Range. reflexivity. Qed.
Lemma V293_task_selector_injective : forall f g,
 0<=f<=Int.max_unsigned -> 0<=g<=Int.max_unsigned ->
 V293_task_selector f=V293_task_selector g -> f=g.
Proof. intros f g F G E. pose proof(f_equal vtoZ E) as D.
 rewrite (V293_task_selector_decode f F),(V293_task_selector_decode g G) in D. inversion D. reflexivity. Qed.
Definition V293_stack_argument_types : typelist :=
 [Tint16;Tptr Tint32;Tptr Tvoid;Tint32].
Definition V293_stack_argument_cells btask barg btop bopt target argv topv optv : list V293_record_cell :=
 [((btask,0),Tint32,V293_task_selector target);((barg,0),Tptr Tvoid,argv);
  ((btop,0),Tptr Tint32,topv);((bopt,0),Tint16,optv)].
Definition V293_stack_argument_env le task arg top opt btask barg btop bopt :=
 get le task=Some(btask,Tint32) /\ get le arg=Some(barg,Tptr Tvoid) /\
 get le top=Some(btop,Tptr Tint32) /\ get le opt=Some(bopt,Tint16).
Definition V293_stack_argument_valid argv topv optv :=
 rule_type_val_match (Tptr Tvoid) argv=true /\
 rule_type_val_match (Tptr Tint32) topv=true /\
 rule_type_val_match Tint16 optv=true.

(* Internal standard evaluation lemma. The public body-entry theorem below
   derives every premise from entry ownership, not supplied intermediate runs. *)
Lemma V293_stack_four_argument_execution : forall P ks ge le M hook task arg top opt tv av sv ov,
 evaltype(evar task)(ge,le,M)=Some Tint32 -> evalval(evar task)(ge,le,M)=Some tv ->
 evaltype(evar arg)(ge,le,M)=Some(Tptr Tvoid) -> evalval(evar arg)(ge,le,M)=Some av ->
 evaltype(evar top)(ge,le,M)=Some(Tptr Tint32) -> evalval(evar top)(ge,le,M)=Some sv ->
 evaltype(evar opt)(ge,le,M)=Some Tint16 -> evalval(evar opt)(ge,le,M)=Some ov ->
 cstepstar P
  (curs(scall hook [evar task;evar arg;evar top;evar opt]),(kenil,ks)) (ge,le,M)
  (curs(sfexec hook [ov;sv;av;tv] V293_stack_argument_types),(kenil,ks)) (ge,le,M).
Proof.
 intros P ks ge le M hook task arg top opt tv av sv ov TT TV AT AV ST SV OT OV.
 eapply c_stepstarn. { eapply stmt_step;[reflexivity | eapply spcall_step;exact TT]. }
 eapply V293_cstepstar_trans.
 { apply V293_expr_steps. apply evalval_imply_estepstar. exact TV. }
 eapply c_stepstarn. { eapply stmt_step;[reflexivity | eapply svfeval_step;exact AT]. }
 eapply V293_cstepstar_trans.
 { apply V293_expr_steps. apply evalval_imply_estepstar. exact AV. }
 eapply c_stepstarn. { eapply stmt_step;[reflexivity | eapply svfeval_step;exact ST]. }
 eapply V293_cstepstar_trans.
 { apply V293_expr_steps. apply evalval_imply_estepstar. exact SV. }
 eapply c_stepstarn. { eapply stmt_step;[reflexivity | eapply svfeval_step;exact OT]. }
 eapply V293_cstepstar_trans.
 { apply V293_expr_steps. apply evalval_imply_estepstar. exact OV. }
 eapply c_stepstarn. { eapply stmt_step;[reflexivity | apply svfevalnil_step]. }
 apply c_stepstar0.
Qed.

Theorem V293_OSTaskCreateExt_to_stack_hook : forall P ks ge le M ir aux O op R
 enabled si ci table prio nesting cpu reserved bp bn bc bt br p old
 psp hook task arg top opt bpsp btask barg btop bopt target argv topv optv rest,
 get le prio=Some(bp,Tint8) -> get le cpu=Some(bc,Tint32) ->
 get le nesting=None -> get ge nesting=Some(bn,Tint8) ->
 get le table=None -> get ge table=Some(bt,Tarray(Tptr V293_tcb_type)13) ->
 get le reserved=None -> get ge reserved=Some(br,Tint8) ->
 get le psp=Some(bpsp,Tptr Tint32) -> (p<13)%nat ->
 0<=target<=Int.max_unsigned ->
 V293_stack_argument_env le task arg top opt btask barg btop bopt ->
 V293_stack_argument_valid argv topv optv ->
 (ge,le,M,ir,aux,O,op) |= V293_rdy_raw_cells
  (V293_create_prefix_cells bp bn bc bt p old Vnull ++
   V293_stack_argument_cells btask barg btop bopt target argv topv optv) R ->
 exists Mf,
 V293_local_steps P
  (curs(V293_TaskCreateExt_prefix table prio nesting cpu reserved
    (sseq (V293_TaskCreateExt_stack_call psp hook task arg top opt) rest)),(kenil,ks))
  ((ge,le,M),ir,(enabled,si,ci))
  (curs(sfexec hook [optv;topv;argv;V293_task_selector target] V293_stack_argument_types),
   (kenil,kassignr (evar psp) (Tptr Tint32) (kseq rest (kseq V293_TaskCreateExt_occupied ks))))
  ((ge,le,Mf),ir,(enabled,si,ci)) /\
 (ge,le,Mf,ir,aux,O,op) |= V293_rdy_raw_cells
  (V293_create_prefix_cells bp bn bc bt p (Vint32 Int.zero) (Vptr(br,Int.zero)) ++
   V293_stack_argument_cells btask barg btop bopt target argv topv optv) R /\
 vtoZ(V293_task_selector target)=Some target /\
 (P hook=None -> ~exists C' state', loststep P
  (curs(sfexec hook [optv;topv;argv;V293_task_selector target] V293_stack_argument_types),
   (kenil,kassignr (evar psp) (Tptr Tint32) (kseq rest (kseq V293_TaskCreateExt_occupied ks))))
  ((ge,le,Mf),ir,(enabled,si,ci)) C' state').
Proof.
 intros P ks ge le M ir aux O op R enabled si ci table prio nesting cpu reserved bp bn bc bt br p old
 psp hook task arg top opt bpsp btask barg btop bopt target argv topv optv rest
 Bp Bc Nn Gn Nt Gt Nr Gr Bs Range Target ArgEnv ArgValid Owned.
 rewrite V293_raw_cells_append in Owned.
 destruct(V293_OSTaskCreateExt_to_stack_call_setup P ks ge le M ir aux O op
  (V293_rdy_raw_cells (V293_stack_argument_cells btask barg btop bopt target argv topv optv) R)
  enabled si ci table prio nesting cpu reserved bp bn bc bt br p old
  psp hook task arg top opt bpsp rest Bp Bc Nn Gn Nt Gt Nr Gr Bs Range Owned)
 as (Mf&Prefix&Final).
 rewrite <-V293_raw_cells_append in Final.
 destruct ArgEnv as (TaskBinding&ArgBinding&TopBinding&OptBinding).
 destruct ArgValid as (ArgValid&TopValid&OptValid).
 V293_tcb_init_read Final 4%nat TaskRead.
 V293_tcb_init_read Final 5%nat ArgRead.
 V293_tcb_init_read Final 6%nat TopRead.
 V293_tcb_init_read Final 7%nat OptRead.
 assert (TT : evaltype(evar task)(ge,le,Mf)=Some Tint32) by V293_rdy_eval.
 assert (TV : evalval(evar task)(ge,le,Mf)=Some(V293_task_selector target)) by V293_rdy_eval.
 assert (AT : evaltype(evar arg)(ge,le,Mf)=Some(Tptr Tvoid)) by V293_rdy_eval.
 assert (AV : evalval(evar arg)(ge,le,Mf)=Some argv) by V293_rdy_eval.
 assert (ST : evaltype(evar top)(ge,le,Mf)=Some(Tptr Tint32)) by V293_rdy_eval.
 assert (SV : evalval(evar top)(ge,le,Mf)=Some topv) by V293_rdy_eval.
 assert (OT : evaltype(evar opt)(ge,le,Mf)=Some Tint16) by V293_rdy_eval.
 assert (OV : evalval(evar opt)(ge,le,Mf)=Some optv) by V293_rdy_eval.
 exists Mf. split.
 - eapply V293_local_trans;[exact Prefix | ]. apply V293_csteps_local.
   eapply V293_stack_four_argument_execution;assumption.
 - split;[exact Final | ]. split.
   + apply V293_task_selector_decode. exact Target.
   + intros Missing. apply V293_missing_port_has_no_step. exact Missing.
Qed.
Print Assumptions V293_OSTaskCreateExt_to_stack_hook.
