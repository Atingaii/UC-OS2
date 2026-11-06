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

(* The table slot belongs to the callee, not also to the caller frame. *)
Definition V293_create_caller_cells bp bn bc p btask barg btop bopt target argv topv optv
 bs bb bi bz be berr value bottomv idv sizev extv olderr : list V293_record_cell :=
 [((bp,0),Tint8,V293_byteval p);((bn,0),Tint8,V293_byteval 0);
  ((bc,0),Tint32,Vint32 Int.zero)] ++
 V293_stack_argument_cells btask barg btop bopt target argv topv optv ++
 V293_create_bridge_extra bs bb bi bz be berr value bottomv idv sizev extv olderr.
Definition V293_create_TCB_support bf block base bh bg rows count bo obase present p
 next oldfields prev g r n back frame :=
 V293_tcb_init_old_fields block base oldfields ++
 V293_tcb_prefix_links bf block base (Vptr(block,Int.repr base)) next ++
 V293_tcb_creation_tail block base bh bg rows count bo obase present p prev g r n back ++ frame.

Theorem V293_OSTaskCreateExt_to_TCB_success_under_hooks : forall P ks ge le M ir aux O op
 enabled si ci table prio nesting cpu reserved bp bn bc bt br p old
 psp hook task arg top opt btask barg btop bopt target argv topv optv
 err tcb bottom identity size ext bs bb bi bz be berr oldpsp bottomv idv sizev extv olderr value rest
 hi hc bf block base bh bg rows count bo obase present next oldfields prev g r n back frame,
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
    (V293_tcb_creation_tail block base bh bg rows count bo obase present p prev g r n back++(V293_create_caller_cells bp bn bc p btask barg btop bopt target argv topv optv bs bb bi bz be berr value bottomv idv sizev extv olderr++frame)))) ->
 (forall b1 b2 b3 b4 b5 b6 b7 b8 b9,
  NoDup (V293_tcb_function_blocks b1 b2 b3 b4 b5 b6 b7 b8 b9) ->
  V293_tcb_creation_hook_return P hc block base (V293_tcb_second_hook_cont tcb hi hc le (V293_create_TCB_cont err rest ks))
   ge (V293_tcb_function_env b1 b2 b3 b4 b5 b6 b7 b8 b9) ir aux O op enabled si ci
   (V293_tcb_hook_cells b1 b2 b3 b4 b5 b6 b7 b8 b9 bf bt block base p
    value bottomv idv sizev extv optv next (Vptr(block,Int.repr base))
    (V293_tcb_creation_tail block base bh bg rows count bo obase present p prev g r n back++(V293_create_caller_cells bp bn bc p btask barg btop bopt target argv topv optv bs bb bi bz be berr value bottomv idv sizev extv olderr++frame)))) ->
 V293_create_stack_return P hook [optv;topv;argv;V293_task_selector target]
 (V293_create_stack_cont psp err tcb prio bottom identity size ext opt rest ks)
 ge le ir aux O op (V293_rdy_raw_cells (V293_create_TCB_support bf block base bh bg rows count bo obase present p next oldfields prev g r n back frame) Atrue) enabled si ci
 (V293_create_bridge_cells bp bn bc bt p (Vint32 Int.zero) (Vptr(br,Int.zero))
 btask barg btop bopt target argv topv optv bs bb bi bz be berr oldpsp bottomv idv sizev extv olderr) value ->
 (ge,le,M,ir,aux,O,op) |= V293_rdy_raw_cells
 (V293_create_bridge_cells bp bn bc bt p old Vnull
 btask barg btop bopt target argv topv optv bs bb bi bz be berr oldpsp bottomv idv sizev extv olderr) (V293_rdy_raw_cells (V293_create_TCB_support bf block base bh bg rows count bo obase present p next oldfields prev g r n back frame) Atrue) ->
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
 (curs(sskip(Some(Vint32 Int.zero))),(kenil,V293_create_TCB_cont err rest ks))
 ((ge,le,Mf),ir,(enabled,si,ci)) /\
 (ge,le,Mf,ir,aux,O,op) |= V293_rdy_raw_cells
 (V293_tcb_creation_result bf bt block base bh bg rows count bo obase present p
 value bottomv idv sizev extv optv next g r n (V293_create_caller_cells bp bn bc p btask barg btop bopt target argv topv optv bs bb bi bz be berr value bottomv idv sizev extv olderr++frame)) Atrue /\
 (forall b tp k, In (b,tp) (V293_tcb_function_addresses b1 b2 b3 b4 b5 b6 b7 b8 b9) ->
 (k<typelen tp)%nat -> get Mf (b,Z.of_nat k)=None).
Proof.
 intros P ks ge le M ir aux O op enabled si ci table prio nesting cpu reserved bp bn bc bt br p old
 psp hook task arg top opt btask barg btop bopt target argv topv optv
 err tcb bottom identity size ext bs bb bi bz be berr oldpsp bottomv idv sizev extv olderr value rest
 hi hc bf block base bh bg rows count bo obase present next oldfields prev g r n back frame
 Bp Bc Nn Gn Nt Gt Nr Gr Range Target ArgEnv ArgValid Env Valid
 Program FreeGlobal TableGlobal HeadGlobal GroupGlobal RowsGlobal CountGlobal
 Base Bound OldBase OldBound G Row Count Next Hook1 Hook2 HookReturn Owned.
 destruct(V293_OSTaskCreateExt_to_TCB_under_stack_return P ks ge le M ir aux O op
 (V293_rdy_raw_cells (V293_create_TCB_support bf block base bh bg rows count bo obase present p next oldfields prev g r n back frame) Atrue) enabled si ci table prio nesting cpu reserved bp bn bc bt br p old
 psp hook task arg top opt btask barg btop bopt target argv topv optv
 err tcb bottom identity size ext bs bb bi bz be berr oldpsp bottomv idv sizev extv olderr value rest
 Bp Bc Nn Gn Nt Gt Nr Gr Range Target ArgEnv ArgValid Env Valid HookReturn Owned)
 as (Mbridge&Prefix&AtTCB).
 assert (CalleeOwned : (ge,le,Mbridge,ir,aux,O,op) |= V293_rdy_raw_cells
 (V293_tcb_init_old_fields block base oldfields ++
 V293_tcb_prefix_links bf block base (Vptr(block,Int.repr base)) next ++
 ((bt,4*Z.of_nat p),Tptr V293_tcb_type,Vptr(br,Int.zero))::
 (V293_tcb_creation_tail block base bh bg rows count bo obase present p prev g r n back ++ (V293_create_caller_cells bp bn bc p btask barg btop bopt target argv topv optv bs bb bi bz be berr value bottomv idv sizev extv olderr++frame))) Atrue).
 { unfold V293_create_bridge_cells,V293_create_prefix_cells,V293_create_TCB_support,
   V293_create_caller_cells,V293_create_bridge_extra,V293_stack_argument_cells in AtTCB |- *.
   repeat rewrite V293_raw_cells_append in AtTCB |- *.
   unfold V293_tcb_init_old_fields,V293_tcb_prefix_links,V293_tcb_creation_tail in AtTCB |- *.
   destruct present;cbn [V293_rdy_raw_cells app] in AtTCB |- *.
   all: repeat rewrite V293_raw_cells_append in AtTCB |- *.
   all: cbn [V293_rdy_raw_cells app] in AtTCB |- *;clear -AtTCB;sep auto. }
 destruct(V293_OS_TCBInit_success_call_under_hooks P (V293_create_TCB_cont err rest ks)
 ge le Mbridge ir aux O op enabled si ci tcb hi hc bf bt block base bh bg rows count bo obase present p
 value bottomv idv sizev extv optv next oldfields (Vptr(br,Int.zero)) prev g r n back (V293_create_caller_cells bp bn bc p btask barg btop bopt target argv topv optv bs bb bi bz be berr value bottomv idv sizev extv olderr++frame)
 Program FreeGlobal TableGlobal HeadGlobal GroupGlobal RowsGlobal CountGlobal
 Range Base Bound OldBase OldBound G Row Count Valid Next Hook1 Hook2 CalleeOwned)
 as (b1&b2&b3&b4&b5&b6&b7&b8&b9&Mf&ND&Fresh&TCB&Final&Freed).
 exists Mbridge. exists b1. exists b2. exists b3. exists b4. exists b5. exists b6. exists b7. exists b8. exists b9. exists Mf.
 split;[exact ND | ]. split;[exact Fresh | ]. split;[exact Prefix | ]. split.
 - eapply V293_local_trans;[exact Prefix |exact TCB].
 - split;[exact Final |exact Freed].
Qed.
Print Assumptions V293_OSTaskCreateExt_to_TCB_success_under_hooks.
