(* Actual value-return assignment and seven TCB arguments; body-entry
   composition requires a real Hook return. No missing Hook body is supplied. *)
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
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtCalls.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitFunction.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateStackEntry.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.

Local Open Scope Z_scope.

Require Import CertiOS.certiucos.v293.proofs.V293TCBCallSuccess.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPriorityHook.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFunction.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateTCBEntry.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBCall.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitEntry.
Require Import CertiOS.certiucos.v293.proofs.V293TCBSuccessReturn.
Local Open Scope Z_scope.

Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateTCBSuccess.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPointerCompare.
Local Open Scope Z_scope.

(* Success continuation: no scheduler execution is assumed. Running=false
   evaluates the real return expression; Running=true reaches a real call. *)
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtSuffix.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateResult.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.framework.proof.cstepLib.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope Z_scope.

Definition V293_create_success_stop (active:bool) err sched ks : code :=
 if active then
  (curs(sfexec sched nil nil),(kenil,kseq (srete(evar err)) ks))
 else (curs(sskip(Some(Vint32 Int.zero))),(kenil,kret ks)).

(* Both paths leave the entire reached memory unchanged. This is not a
   return/free theorem, and the active path has not queried the callee. *)
Theorem V293_OSTaskCreateExt_success_suffix : forall P ks ge le M table prio err running sched
 berr brun (active:bool),
 get le err=Some(berr,Tint8) ->
 get le running=None -> get ge running=Some(brun,Tint8) ->
 load Tint8 M (berr,0)=Some(Vint32 Int.zero) ->
 load Tint8 M (brun,0)=Some(Vint32(if active then Int.one else Int.zero)) ->
 cstepstar P
 (curs(sskip None),(kenil,kseq (V293_TaskCreateExt_suffix table prio err running sched) ks))
 (ge,le,M) (V293_create_success_stop active err sched ks) (ge,le,M).
Proof.
 intros P ks ge le M table prio err running sched berr brun active Err Nr Gr E R.
 assert (ErrZero : evalval (ebinop oeq (evar err)(econst32 Int.zero)) (ge,le,M)=Some(Vint32 Int.one)) by V293_rdy_eval.
 assert (Running : evalval (ebinop oeq (evar running)(econst32 Int.one)) (ge,le,M)=
  Some(Vint32(if active then Int.one else Int.zero))).
 { destruct active;V293_rdy_eval. }
 assert (Return : evalval(evar err)(ge,le,M)=Some(Vint32 Int.zero)) by V293_rdy_eval.
 unfold V293_TaskCreateExt_suffix,V293_create_success_stop.
 eapply c_stepstarn. { eapply stmt_step;[reflexivity|apply sskip_step]. }
 eapply c_stepstarn. { eapply stmt_step;[reflexivity|apply sseq_step]. }
 eapply c_stepstarn. { eapply stmt_step;[reflexivity|apply sif_step]. }
 eapply V293_cstepstar_trans. { apply V293_expr_steps. apply evalval_imply_estepstar. exact ErrZero. }
 eapply c_stepstarn. { eapply stmt_step;[reflexivity|apply svift_step;reflexivity]. }
 eapply c_stepstarn. { eapply stmt_step;[reflexivity|apply sseq_step]. }
 eapply c_stepstarn. { eapply stmt_step;[reflexivity|apply sskip_step]. }
 eapply V293_cstepstar_trans. { eapply V293_entry_if_select with (flag:=active). exact Running. }
 destruct active.
 - eapply c_stepstarn. { eapply stmt_step;[reflexivity|apply snpcall_step]. }
   apply c_stepstar0.
 - eapply c_stepstarn. { eapply stmt_step;[reflexivity|apply sskip_step]. }
   eapply c_stepstarn. { eapply stmt_step;[reflexivity|apply srete_step]. }
   apply V293_expr_steps. apply evalval_imply_estepstar. exact Return.
Qed.
Print Assumptions V293_OSTaskCreateExt_success_suffix.

(* The full success body to the source-level dispatch/return-value boundary.
   Three real Hook contracts remain explicit and unfulfilled. *)
Theorem V293_OSTaskCreateExt_success_dispatch_under_hooks : forall P ks ge le M ir aux O op
 enabled si ci table prio nesting cpu reserved bp bn bc bt br p old
 psp hook task arg top opt btask barg btop bopt target argv topv optv
 err tcb bottom identity size ext bs bb bi bz be berr oldpsp bottomv idv sizev extv olderr value
 hi hc bf block base bh bg rows count bo obase present next oldfields prev g r n back frame running sched brun (active:bool),
 let rest:=V293_TaskCreateExt_suffix table prio err running sched in
 let kept:=((brun,0),Tint8,Vint32(if active then Int.one else Int.zero))::frame in
 get le running=None -> get ge running=Some(brun,Tint8) ->
 get le prio=Some(bp,Tint8) -> get le cpu=Some(bc,Tint32) ->
 get le nesting=None -> get ge nesting=Some(bn,Tint8) ->
 get le table=None -> get ge table=Some(bt,Tarray(Tptr V293_tcb_type)13) ->
 get le reserved=None -> get ge reserved=Some(br,Tint8) ->
 (p<13)%nat -> 0<=target<=Int.max_unsigned ->
 V293_stack_argument_env le task arg top opt btask barg btop bopt ->
 V293_stack_argument_valid argv topv optv ->
 V293_create_TCB_env le psp bottom identity size ext err bs bb bi bz be berr ->
 V293_tcb_init_values_valid value bottomv idv sizev extv optv ->
 P tcb=Some (V293_TCBInit_function hi hc) ->
 get ge 91%Z=Some(bf,Tptr V293_tcb_type) ->
 get ge 92%Z=Some(bt,Tarray (Tptr V293_tcb_type) 13) ->
 get ge 93%Z=Some(bh,Tptr V293_tcb_type) -> get ge 94%Z=Some(bg,Tint8) ->
 get ge 95%Z=Some(rows,Tarray Tint8 2) -> get ge 96%Z=Some(count,Tint8) ->
 (0<=base)%Z -> (base+55<=Int.max_unsigned)%Z ->
 (0<=obase)%Z -> (obase+24<=Int.max_unsigned)%Z ->
 (g<256)%nat -> (r<256)%nat -> (n<255)%nat ->
 rule_type_val_match (Tptr V293_tcb_type) next=true ->
 (forall b1 b2 b3 b4 b5 b6 b7 b8 b9,
  NoDup (V293_tcb_function_blocks b1 b2 b3 b4 b5 b6 b7 b8 b9) ->
  V293_tcb_creation_hook_return P hi block base (V293_tcb_first_hook_cont tcb hi hc le (V293_create_TCB_cont err rest ks))
   ge (V293_tcb_function_env b1 b2 b3 b4 b5 b6 b7 b8 b9) ir aux O op enabled si ci
   (V293_tcb_hook_cells b1 b2 b3 b4 b5 b6 b7 b8 b9 bf bt block base p
    value bottomv idv sizev extv optv next (Vptr(br,Int.zero))
    (V293_tcb_creation_tail block base bh bg rows count bo obase present p prev g r n back++(V293_create_caller_cells bp bn bc p btask barg btop bopt target argv topv optv bs bb bi bz be berr value bottomv idv sizev extv olderr++kept)))) ->
 (forall b1 b2 b3 b4 b5 b6 b7 b8 b9,
  NoDup (V293_tcb_function_blocks b1 b2 b3 b4 b5 b6 b7 b8 b9) ->
  V293_tcb_creation_hook_return P hc block base (V293_tcb_second_hook_cont tcb hi hc le (V293_create_TCB_cont err rest ks))
   ge (V293_tcb_function_env b1 b2 b3 b4 b5 b6 b7 b8 b9) ir aux O op enabled si ci
   (V293_tcb_hook_cells b1 b2 b3 b4 b5 b6 b7 b8 b9 bf bt block base p
    value bottomv idv sizev extv optv next (Vptr(block,Int.repr base))
    (V293_tcb_creation_tail block base bh bg rows count bo obase present p prev g r n back++(V293_create_caller_cells bp bn bc p btask barg btop bopt target argv topv optv bs bb bi bz be berr value bottomv idv sizev extv olderr++kept)))) ->
 V293_create_stack_return P hook [optv;topv;argv;V293_task_selector target]
 (V293_create_stack_cont psp err tcb prio bottom identity size ext opt rest ks)
 ge le ir aux O op (V293_rdy_raw_cells (V293_create_TCB_support bf block base bh bg rows count bo obase present p next oldfields prev g r n back kept) Atrue) enabled si ci
 (V293_create_bridge_cells bp bn bc bt p (Vint32 Int.zero) (Vptr(br,Int.zero))
 btask barg btop bopt target argv topv optv bs bb bi bz be berr oldpsp bottomv idv sizev extv olderr) value ->
 (ge,le,M,ir,aux,O,op) |= V293_rdy_raw_cells
 (V293_create_bridge_cells bp bn bc bt p old Vnull
 btask barg btop bopt target argv topv optv bs bb bi bz be berr oldpsp bottomv idv sizev extv olderr) (V293_rdy_raw_cells (V293_create_TCB_support bf block base bh bg rows count bo obase present p next oldfields prev g r n back kept) Atrue) ->
 exists Mbridge, exists b1 b2 b3 b4 b5 b6 b7 b8 b9 Mf,
 NoDup (V293_tcb_function_blocks b1 b2 b3 b4 b5 b6 b7 b8 b9) /\
 (forall b, In b (V293_tcb_function_blocks b1 b2 b3 b4 b5 b6 b7 b8 b9) -> fresh Mbridge b) /\
 V293_local_steps P
 (curs(V293_TaskCreateExt_prefix table prio nesting cpu reserved
 (V293_TaskCreateExt_calls psp hook task arg top opt err tcb prio bottom identity size ext rest)),(kenil,ks))
 ((ge,le,M),ir,(enabled,si,ci))
 (curs(sfexec tcb [optv;extv;sizev;idv;bottomv;value;V293_byteval p] V293_TCBInit_argument_types),(kenil,V293_create_TCB_cont err rest ks))
 ((ge,le,Mbridge),ir,(enabled,si,ci)) /\
 V293_local_steps P
 (curs(V293_TaskCreateExt_prefix table prio nesting cpu reserved
 (V293_TaskCreateExt_calls psp hook task arg top opt err tcb prio bottom identity size ext rest)),(kenil,ks))
 ((ge,le,M),ir,(enabled,si,ci))
 (V293_create_success_stop active err sched (kseq V293_TaskCreateExt_occupied ks))
 ((ge,le,Mf),ir,(enabled,si,ci)) /\
 (ge,le,Mf,ir,aux,O,op) |= V293_rdy_raw_cells
 (V293_tcb_creation_result bf bt block base bh bg rows count bo obase present p
 value bottomv idv sizev extv optv next g r n (V293_create_caller_cells bp bn bc p btask barg btop bopt target argv topv optv bs bb bi bz be berr value bottomv idv sizev extv (Vint32 Int.zero)++kept)) Atrue /\
 (forall b tp k, In (b,tp) (V293_tcb_function_addresses b1 b2 b3 b4 b5 b6 b7 b8 b9) ->
 (k<typelen tp)%nat -> get Mf (b,Z.of_nat k)=None).
Proof.
 intros P ks ge le M ir aux O op enabled si ci table prio nesting cpu reserved bp bn bc bt br p old
 psp hook task arg top opt btask barg btop bopt target argv topv optv
 err tcb bottom identity size ext bs bb bi bz be berr oldpsp bottomv idv sizev extv olderr value
 hi hc bf block base bh bg rows count bo obase present next oldfields prev g r n back frame running sched brun active rest kept
 Nr Gr Bp Bc Nn Gn Nt Gt Nres Gres Range Target ArgEnv ArgValid Env Valid
 Program FreeGlobal TableGlobal HeadGlobal GroupGlobal RowsGlobal CountGlobal
 Base Bound OldBase OldBound G Row Count Next Hook1 Hook2 HookReturn Owned.
 destruct(V293_OSTaskCreateExt_result_assigned_under_hooks P ks ge le M ir aux O op enabled si ci table prio nesting cpu reserved bp bn bc bt br p old
 psp hook task arg top opt btask barg btop bopt target argv topv optv
 err tcb bottom identity size ext bs bb bi bz be berr oldpsp bottomv idv sizev extv olderr value rest
 hi hc bf block base bh bg rows count bo obase present next oldfields prev g r n back kept
 Bp Bc Nn Gn Nt Gt Nres Gres Range Target ArgEnv ArgValid Env Valid
 Program FreeGlobal TableGlobal HeadGlobal GroupGlobal RowsGlobal CountGlobal
 Base Bound OldBase OldBound G Row Count Next Hook1 Hook2 HookReturn Owned)
 as (Mbridge&b1&b2&b3&b4&b5&b6&b7&b8&b9&Mf&ND&Fresh&Prefix&Exec&Final&Freed).
 assert (ErrRead : load Tint8 Mf (berr,0)=Some(Vint32 Int.zero)).
 { eapply (V293_rdy_raw_load _ Atrue _ _ _ (ge,le,Mf,ir,aux,O,op));[ |reflexivity|exact Final].
   unfold V293_tcb_creation_result,V293_tcb_creation_frame.
   apply in_or_app;right. apply in_or_app;right. apply in_or_app;right.
   apply in_or_app;left. unfold V293_create_caller_cells,V293_stack_argument_cells,V293_create_bridge_extra.
   cbn [app]. repeat (first [left;reflexivity |right]). }
 assert (RunningRead : load Tint8 Mf (brun,0)=Some(Vint32(if active then Int.one else Int.zero))).
 { eapply (V293_rdy_raw_load _ Atrue _ _ _ (ge,le,Mf,ir,aux,O,op));[ |destruct active;reflexivity|exact Final].
   unfold V293_tcb_creation_result,V293_tcb_creation_frame.
   apply in_or_app;right. apply in_or_app;right. apply in_or_app;right.
   apply in_or_app;right. unfold kept. left;reflexivity. }
 assert (ErrEnv : get le err=Some(berr,Tint8)) by (destruct Env as (_&_&_&_&_&E);exact E).
 exists Mbridge. exists b1. exists b2. exists b3. exists b4. exists b5. exists b6. exists b7. exists b8. exists b9. exists Mf.
 split;[exact ND| ]. split;[exact Fresh| ]. split;[exact Prefix| ]. split.
 - eapply V293_local_trans;[exact Exec| ]. apply V293_csteps_local.
   eapply V293_OSTaskCreateExt_success_suffix;eassumption.
 - split;assumption.
Qed.
Print Assumptions V293_OSTaskCreateExt_success_dispatch_under_hooks.
