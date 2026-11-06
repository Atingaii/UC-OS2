(* Return/free of the exact creation body. Call allocation is not proved;
   complete local layout, unique blocks and survivor block separation remain
   explicit. Real Hook implementations are not supplied. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateSuffix.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateTCBSuccess.
Require Import CertiOS.certiucos.v293.proofs.V293TCBCallSuccess.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFunction.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPriorityHook.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitEntry.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateTCBEntry.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateStackEntry.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBCall.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBClear.
Require Import CertiOS.certiucos.v293.proofs.V293NullBytes.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtSuffix.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitFunction.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtPrefix.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtCalls.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Coq.Sorting.Permutation Lia.
Import ListNotations.
Local Open Scope Z_scope.

Definition V293_create_local_addresses (bp bc btask barg btop bopt bs bb bi bz be berr : block) :=
 [(bp,Tint8);(bs,Tptr Tint32);(bc,Tint32);(btask,Tint32);(barg,Tptr Tvoid);
  (btop,Tptr Tint32);(bopt,Tint16);(bb,Tptr Tint32);(bi,Tint16);
  (bz,Tint32);(be,Tptr Tvoid);(berr,Tint8)].
Definition V293_create_local_cells bp bc p btask barg btop bopt target argv topv optv
 bs bb bi bz be berr value bottomv idv sizev extv :=
 [((bp,0),Tint8,V293_byteval p);((bc,0),Tint32,Vint32 Int.zero)]++
 V293_stack_argument_cells btask barg btop bopt target argv topv optv++
 V293_create_bridge_extra bs bb bi bz be berr value bottomv idv sizev extv (Vint32 Int.zero).

Lemma V293_create_owned_writable : forall cells R b tp v ge le M ir aux O op,
 In ((b,0),tp,v) cells ->
 (ge,le,M,ir,aux,O,op) |= V293_rdy_raw_cells cells R ->
 V293_bytes_writable M b 0 (typelen tp).
Proof.
 intros cells R b tp v ge le M ir aux O op Member Owned.
 apply in_split in Member. destruct Member as (before&after&Shape). subst cells.
 apply V293_rdy_cell_out in Owned.
 eapply V293_tick_raw_owned_writable;exact Owned.
Qed.

(* Starts at the value produced by the ACTUAL return expression. No replacement
   of return err by a constant-expression execution. *)
Theorem V293_create_value_return : forall P ks ge le caller M f body next v,
 callcont ks=Some(kcall f body caller next) ->
 NoDup(map fst(getaddr le)) ->
 (forall b tp, In(b,tp)(getaddr le) -> V293_bytes_writable M b 0 (typelen tp)) ->
 exists Mr,
 cstepstar P (curs(sskip(Some v)),(kenil,kret ks)) (ge,le,M)
  (curs(sskip(Some v)),(kenil,next)) (ge,caller,Mr) /\
 (forall b i, ~In b (map fst(getaddr le)) -> get Mr (b,i)=get M (b,i)) /\
 (forall b tp k, In(b,tp)(getaddr le) -> (k<typelen tp)%nat -> get Mr (b,Z.of_nat k)=None).
Proof.
 intros P ks ge le caller M f body next v Call ND W.
 destruct(V293_sfree_construct_execution (getaddr le) P ks ge le M (Some v) ND W)
 as (Mr&Free&Outside&Removed).
 exists Mr. split.
 - eapply c_stepstarn.
   { eapply stmt_step;[reflexivity| ]. eapply(sretv_step P f _ body);[reflexivity|rewrite Call;discriminate|reflexivity]. }
   eapply V293_cstepstar_trans;[exact Free| ].
   eapply c_stepstarn. { eapply stmt_step;[reflexivity| ]. eapply sfreeend_step;eassumption||reflexivity. }
   apply c_stepstar0.
 - split;assumption.
Qed.
Print Assumptions V293_create_value_return.

Theorem V293_OSTaskCreateExt_success_return_under_hooks : forall P ks caller f body retks ge le M ir aux O op
 enabled si ci table prio nesting cpu reserved bp bn bc bt br p old
 psp hook task arg top opt btask barg btop bopt target argv topv optv
 err tcb bottom identity size ext bs bb bi bz be berr oldpsp bottomv idv sizev extv olderr value
 hi hc bf block base bh bg rows count bo obase present next oldfields prev g r n back frame running sched brun,
 let rest:=V293_TaskCreateExt_suffix table prio err running sched in
 let kept:=((brun,0),Tint8,Vint32 Int.zero)::frame in
 let addresses:=V293_create_local_addresses bp bc btask barg btop bopt bs bb bi bz be berr in
 let locals:=V293_create_local_cells bp bc p btask barg btop bopt target argv topv optv bs bb bi bz be berr value bottomv idv sizev extv in
 let live:=V293_tcb_creation_result bf bt block base bh bg rows count bo obase present p
 value bottomv idv sizev extv optv next g r n (((bn,0),Tint8,V293_byteval 0)::kept) in
 getaddr le=addresses -> NoDup(map fst addresses) ->
 callcont ks=Some(kcall f body caller retks) ->
 (forall a tp v, In(a,tp,v) live -> ~In(fst a)(map fst addresses)) ->
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
 exists Mbridge, exists b1 b2 b3 b4 b5 b6 b7 b8 b9 Mf, exists Mr,
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
 (curs(sskip(Some(Vint32 Int.zero))),(kenil,retks))
 ((ge,caller,Mr),ir,(enabled,si,ci)) /\
 (ge,caller,Mr,ir,aux,O,op) |= V293_rdy_raw_cells live Atrue /\
 (forall b tp k, In (b,tp) (V293_tcb_function_addresses b1 b2 b3 b4 b5 b6 b7 b8 b9) ->
 (k<typelen tp)%nat -> get Mr (b,Z.of_nat k)=None) /\
 (forall b tp k, In(b,tp) addresses -> (k<typelen tp)%nat -> get Mr(b,Z.of_nat k)=None) /\
 (forall b i, ~In b(map fst addresses) -> get Mr(b,i)=get Mf(b,i)).
Proof.
 intros P ks caller f body retks ge le M ir aux O op enabled si ci table prio nesting cpu reserved bp bn bc bt br p old
 psp hook task arg top opt btask barg btop bopt target argv topv optv
 err tcb bottom identity size ext bs bb bi bz be berr oldpsp bottomv idv sizev extv olderr value
 hi hc bf block base bh bg rows count bo obase present next oldfields prev g r n back frame running sched brun rest kept addresses locals live Layout ND Call Away
 Nr Gr Bp Bc Nn Gn Nt Gt Nres Gres Range Target ArgEnv ArgValid Env Valid
 Program FreeGlobal TableGlobal HeadGlobal GroupGlobal RowsGlobal CountGlobal
 Base Bound OldBase OldBound G Row Count Next Hook1 Hook2 HookReturn Owned.
 destruct(V293_OSTaskCreateExt_success_dispatch_under_hooks P ks ge le M ir aux O op enabled si ci table prio nesting cpu reserved bp bn bc bt br p old
 psp hook task arg top opt btask barg btop bopt target argv topv optv
 err tcb bottom identity size ext bs bb bi bz be berr oldpsp bottomv idv sizev extv olderr value
 hi hc bf block base bh bg rows count bo obase present next oldfields prev g r n back frame running sched brun false
 Nr Gr Bp Bc Nn Gn Nt Gt Nres Gres Range Target ArgEnv ArgValid Env Valid
 Program FreeGlobal TableGlobal HeadGlobal GroupGlobal RowsGlobal CountGlobal
 Base Bound OldBase OldBound G Row Count Next Hook1 Hook2 HookReturn Owned) as (Mbridge&b1&b2&b3&b4&b5&b6&b7&b8&b9&Mf&TCBND&Fresh&Prefix&Exec&Final&Freed).
 assert (Writable : forall b tp, In(b,tp)(getaddr le) -> V293_bytes_writable Mf b 0 (typelen tp)).
 { intros b tp Member. rewrite Layout in Member.
   assert (LocalCell : exists v, In((b,0),tp,v)
    (V293_create_caller_cells bp bn bc p btask barg btop bopt target argv topv optv bs bb bi bz be berr value bottomv idv sizev extv (Vint32 Int.zero))).
   { unfold addresses,V293_create_local_addresses in Member.
     unfold V293_create_caller_cells,V293_stack_argument_cells,V293_create_bridge_extra.
     cbn [app]. repeat destruct Member as [E|Member];try contradiction;inversion E;subst b tp.
     all: eexists;repeat(first[left;reflexivity|right]). }
   destruct LocalCell as (v&MemberCell).
   eapply V293_create_owned_writable;[ |exact Final].
   unfold V293_tcb_creation_result,V293_tcb_creation_frame.
   apply in_or_app;right. apply in_or_app;right. apply in_or_app;right.
   apply in_or_app;left;exact MemberCell. }
 destruct(V293_create_value_return P (kseq V293_TaskCreateExt_occupied ks)
 ge le caller Mf f body retks (Vint32 Int.zero) Call ltac:(rewrite Layout;exact ND) Writable)
 as (Mr&Return&Outside&Removed).
 assert (Order : Permutation
  (V293_create_caller_cells bp bn bc p btask barg btop bopt target argv topv optv bs bb bi bz be berr value bottomv idv sizev extv (Vint32 Int.zero)++kept)
  ((((bn,0),Tint8,V293_byteval 0)::kept)++locals)).
 { unfold V293_create_caller_cells,locals,V293_create_local_cells.
   cbn [app]. eapply perm_trans;[apply perm_swap| ]. apply perm_skip.
   change (Permutation
    (([((bp,0),Tint8,V293_byteval p);((bc,0),Tint32,Vint32 Int.zero)]++
      (V293_stack_argument_cells btask barg btop bopt target argv topv optv++
       V293_create_bridge_extra bs bb bi bz be berr value bottomv idv sizev extv (Vint32 Int.zero)))++kept)
    (kept++([((bp,0),Tint8,V293_byteval p);((bc,0),Tint32,Vint32 Int.zero)]++
      (V293_stack_argument_cells btask barg btop bopt target argv topv optv++
       V293_create_bridge_extra bs bb bi bz be berr value bottomv idv sizev extv (Vint32 Int.zero))))).
   apply Permutation_app_comm. }
 assert (Split : (ge,le,Mf,ir,aux,O,op) |= V293_rdy_raw_cells live (V293_rdy_raw_cells locals Atrue)).
 { rewrite <-V293_raw_cells_append.
   eapply V293_raw_cells_permutation;[ |exact Final].
   unfold live,V293_tcb_creation_result,V293_tcb_creation_frame.
   repeat rewrite <-app_assoc. repeat apply Permutation_app_head. exact Order. }
 assert (Live : (ge,caller,Mr,ir,aux,O,op) |= V293_rdy_raw_cells live Atrue).
 { eapply V293_raw_cells_return_many with (freed:=map fst addresses);[exact Away| |exact Split].
   intros b i NotLocal. apply Outside. rewrite Layout;exact NotLocal. }
 assert (TCBRemoved : forall b tp k, In(b,tp)(V293_tcb_function_addresses b1 b2 b3 b4 b5 b6 b7 b8 b9) ->
 (k<typelen tp)%nat -> get Mr (b,Z.of_nat k)=None).
 { intros b tp k Member K. rewrite Outside;[eapply Freed;eassumption| ].
   intro Local. apply in_map_iff in Local. destruct Local as ([c t]&Same&Local).
   cbn in Same. subst c.
   assert (Positive : (0<typelen t)%nat).
   { rewrite Layout in Local. unfold addresses,V293_create_local_addresses in Local.
     repeat destruct Local as [E|Local];try contradiction;inversion E;subst;cbn;lia. }
   destruct (Writable b t Local 0%nat Positive) as (w&Read).
   replace (0+Z.of_nat 0) with 0 in Read by reflexivity.
   assert (Zero : get Mf(b,0)=None).
   { apply (Freed b tp 0%nat Member).
     unfold V293_tcb_function_addresses in Member.
     repeat destruct Member as [E|Member];try contradiction;inversion E;subst;cbn;lia. }
   rewrite Zero in Read;discriminate. }
 exists Mbridge. exists b1. exists b2. exists b3. exists b4. exists b5. exists b6. exists b7. exists b8. exists b9. exists Mf. exists Mr.
 split;[exact TCBND| ]. split;[exact Fresh| ]. split;[exact Prefix| ]. split.
 - eapply V293_local_trans;[exact Exec| ]. apply V293_csteps_local;exact Return.
 - split;[exact Live| ]. split;[exact TCBRemoved| ]. split.
   + intros b tp k Member K. apply (Removed b tp k);[rewrite Layout;exact Member|exact K].
   + intros b i NotLocal. apply Outside. rewrite Layout;exact NotLocal.
Qed.
Print Assumptions V293_OSTaskCreateExt_success_return_under_hooks.
