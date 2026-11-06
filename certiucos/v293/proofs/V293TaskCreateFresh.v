(* Allocation choices are constructed from bounded actual memory and a finite
   survivor list. Real port contracts remain hypotheses, never no-op code. *)
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateExtPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateSuffix.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateTCBSuccess.
Require Import CertiOS.certiucos.v293.proofs.V293TCBCallSuccess.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPriorityHook.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitEntry.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateTCBEntry.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateStackEntry.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtSuffix.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtPrefix.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtCalls.
Require Import Coq.Lists.List Coq.Sorting.Permutation Lia.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitFunction.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitPrefix.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBCall.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBClear.
Require Import CertiOS.certiucos.v293.proofs.V293NullBytes.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBList.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import Coq.Lists.List Lia.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFunction.
Require Import CertiOS.certiucos.v293.proofs.V293InitChain.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtFunction.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateReturn.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateCall.
Import ListNotations.
Local Open Scope Z_scope.
Lemma V293_create_fresh_twelve_avoiding : forall M (cells : list V293_record_cell),
 exists btask, exists barg, exists btop, exists bp, exists bi, exists bb, exists bz, exists be, exists bopt, exists bs, exists berr, exists bc,
 NoDup(V293_create_function_blocks btask barg btop bp bi bb bz be bopt bs berr bc) /\
 (forall b, In b (V293_create_function_blocks btask barg btop bp bi bb bz be bopt bs berr bc) -> fresh M b) /\
 (forall a tp v, In(a,tp,v) cells -> ~In(fst a)(V293_create_function_blocks btask barg btop bp bi bb bz be bopt bs berr bc)).
Proof.
 intros M cells. destruct (HalfPermMap.bounded M) as [bound Below].
 set (start:=Pos.max bound (Pos.succ(V293_cells_upper cells))).
 exists (start).
 exists (Pos.succ (start)).
 exists (Pos.succ (Pos.succ (start))).
 exists (Pos.succ (Pos.succ (Pos.succ (start)))).
 exists (Pos.succ (Pos.succ (Pos.succ (Pos.succ (start))))).
 exists (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (start)))))).
 exists (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (start))))))).
 exists (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (start)))))))).
 exists (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (start))))))))).
 exists (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (start)))))))))).
 exists (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (start))))))))))).
 exists (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (start)))))))))))).
 assert (LT : (V293_cells_upper cells<start)%positive).
 { unfold start. eapply Pos.lt_le_trans;[apply Pos.lt_succ_diag_r|apply Pos.le_max_r]. }
 assert (Fresh : forall b, (start<=b)%positive -> fresh M b).
 { intros b B a i E [v Read];subst a.
   assert (Small : (b<bound)%positive) by (eapply Below;exact Read).
   assert (High : (bound<=start)%positive) by (unfold start;apply Pos.le_max_l). lia. }
 split.
 - unfold V293_create_function_blocks.
   apply NoDup_cons. { cbn [In]. intros Inside. repeat destruct Inside as [E|Inside];try contradiction;lia. }
   apply NoDup_cons. { cbn [In]. intros Inside. repeat destruct Inside as [E|Inside];try contradiction;lia. }
   apply NoDup_cons. { cbn [In]. intros Inside. repeat destruct Inside as [E|Inside];try contradiction;lia. }
   apply NoDup_cons. { cbn [In]. intros Inside. repeat destruct Inside as [E|Inside];try contradiction;lia. }
   apply NoDup_cons. { cbn [In]. intros Inside. repeat destruct Inside as [E|Inside];try contradiction;lia. }
   apply NoDup_cons. { cbn [In]. intros Inside. repeat destruct Inside as [E|Inside];try contradiction;lia. }
   apply NoDup_cons. { cbn [In]. intros Inside. repeat destruct Inside as [E|Inside];try contradiction;lia. }
   apply NoDup_cons. { cbn [In]. intros Inside. repeat destruct Inside as [E|Inside];try contradiction;lia. }
   apply NoDup_cons. { cbn [In]. intros Inside. repeat destruct Inside as [E|Inside];try contradiction;lia. }
   apply NoDup_cons. { cbn [In]. intros Inside. repeat destruct Inside as [E|Inside];try contradiction;lia. }
   apply NoDup_cons. { cbn [In]. intros Inside. repeat destruct Inside as [E|Inside];try contradiction;lia. }
   apply NoDup_cons. { cbn [In]. intros Inside. repeat destruct Inside as [E|Inside];try contradiction;lia. }
   apply NoDup_nil.
 - split.
   + intros b Member. apply Fresh. unfold V293_create_function_blocks in Member.
     cbn [In] in Member. repeat destruct Member as [E|Member];try contradiction;subst b;lia.
   + intros a tp v Member Inside.
     pose proof(V293_cells_upper_bound cells a tp v Member) as Bound.
     unfold V293_create_function_blocks in Inside. cbn [In] in Inside.
     repeat destruct Inside as [E|Inside];try contradiction.
     all: apply(Pos.lt_irrefl(fst a));eapply Pos.le_lt_trans;[exact Bound| ];
       eapply Pos.lt_le_trans;[exact LT| ];rewrite <-E;lia.
Qed.
Print Assumptions V293_create_fresh_twelve_avoiding.

Theorem V293_create_fresh_call_prologue : forall P ks ge caller M ir aux O op enabled si ci
 f table nesting reserved running sched hook tcb v1 v2 v3 v4 v5 v6 v7 v8 v9 frame (avoid : list V293_record_cell),
 P f=Some(V293_CreateExt_function table nesting reserved running sched hook tcb) ->
 V293_create_function_values_valid v1 v2 v3 v4 v5 v6 v7 v8 v9 ->
 (ge,caller,M,ir,aux,O,op) |= V293_rdy_raw_cells frame Atrue ->
 exists btask, exists barg, exists btop, exists bp, exists bi, exists bb, exists bz, exists be, exists bopt, exists bs, exists berr, exists bc, exists Mi,
 NoDup(V293_create_function_blocks btask barg btop bp bi bb bz be bopt bs berr bc) /\
 (forall b, In b(V293_create_function_blocks btask barg btop bp bi bb bz be bopt bs berr bc) -> fresh M b) /\
 (forall a tp v, In(a,tp,v) avoid -> ~In(fst a)(V293_create_function_blocks btask barg btop bp bi bb bz be bopt bs berr bc)) /\
 V293_local_steps P
 (curs(sfexec f [v9;v8;v7;v6;v5;v4;v3;v2;v1] V293_CreateExt_argument_types),(kenil,ks))
 ((ge,caller,M),ir,(enabled,si,ci))
 (curs(V293_CreateExt_body table nesting reserved running sched hook tcb),(kenil,kcall f (V293_CreateExt_body table nesting reserved running sched hook tcb) caller ks))
 ((ge,V293_create_function_env btask barg btop bp bi bb bz be bopt bs berr bc,Mi),ir,(enabled,si,ci)) /\
 (ge,V293_create_function_env btask barg btop bp bi bb bz be bopt bs berr bc,Mi,ir,aux,O,op) |=
 V293_rdy_raw_cells (V293_create_function_cells btask barg btop bp bi bb bz be bopt bs berr bc v1 v2 v3 v4 v5 v6 v7 v8 v9++frame) Atrue.
Proof.
 intros P ks ge caller M ir aux O op enabled si ci f table nesting reserved running sched hook tcb
 v1 v2 v3 v4 v5 v6 v7 v8 v9 frame avoid Function Valid Owned.
 destruct(V293_create_fresh_twelve_avoiding M avoid) as (btask&barg&btop&bp&bi&bb&bz&be&bopt&bs&berr&bc&ND&Fresh&Away).
 destruct(V293_create_call_prologue P ks ge caller M ir aux O op enabled si ci
 f table nesting reserved running sched hook tcb btask barg btop bp bi bb bz be bopt bs berr bc v1 v2 v3 v4 v5 v6 v7 v8 v9 frame
 Function ND Fresh Valid Owned) as (Mi&Exec&Final).
 exists btask. exists barg. exists btop. exists bp. exists bi. exists bb. exists bz. exists be. exists bopt. exists bs. exists berr. exists bc. exists Mi.
 split;[exact ND| ]. split;[exact Fresh| ]. split;[exact Away| ]. split;assumption.
Qed.
Print Assumptions V293_create_fresh_call_prologue.

Theorem V293_OSTaskCreateExt_fresh_success_call_under_hooks : forall P retks caller f ge M ir aux O op
 enabled si ci bn bt br p target argv topv optv bottomv idv sizev extv value
 hi hc bf block base bh bg rows count bo obase present next oldfields prev g r n back frame brun,
 let body:=V293_CreateExt_body 92%Z 97%Z 98%Z 99%Z 904%Z 900%Z 901%Z in
 let ks:=kcall f body caller retks in
 let rest:=V293_TaskCreateExt_suffix 92%Z 101%Z 209%Z 99%Z 904%Z in
 let kept:=((brun,0),Tint8,Vint32 Int.zero)::frame in
 let live:=V293_tcb_creation_result bf bt block base bh bg rows count bo obase present p
 value bottomv idv sizev extv optv next g r n (((bn,0),Tint8,V293_byteval 0)::kept) in
 P f=Some(V293_CreateExt_function 92%Z 97%Z 98%Z 99%Z 904%Z 900%Z 901%Z) ->
 get ge 99%Z=Some(brun,Tint8) ->
 get ge 97%Z=Some(bn,Tint8) ->
 get ge 92%Z=Some(bt,Tarray(Tptr V293_tcb_type)13) ->
 get ge 98%Z=Some(br,Tint8) ->
 (p<13)%nat -> 0<=target<=Int.max_unsigned ->
 V293_stack_argument_valid argv topv optv ->
 V293_tcb_init_values_valid value bottomv idv sizev extv optv ->
 P 901%Z=Some(V293_TCBInit_function hi hc) ->
 get ge 91%Z=Some(bf,Tptr V293_tcb_type) ->
 get ge 92%Z=Some(bt,Tarray(Tptr V293_tcb_type)13) ->
 get ge 93%Z=Some(bh,Tptr V293_tcb_type) -> get ge 94%Z=Some(bg,Tint8) ->
 get ge 95%Z=Some(rows,Tarray Tint8 2) -> get ge 96%Z=Some(count,Tint8) ->
 0<=base -> base+55<=Int.max_unsigned -> 0<=obase -> obase+24<=Int.max_unsigned ->
 (g<256)%nat -> (r<256)%nat -> (n<255)%nat ->
 rule_type_val_match (Tptr V293_tcb_type) next=true ->
 (forall btask barg btop bp bi bb bz be bopt bs berr bc,
 let le:=V293_create_function_env btask barg btop bp bi bb bz be bopt bs berr bc in
 NoDup(V293_create_function_blocks btask barg btop bp bi bb bz be bopt bs berr bc) ->
 (forall b, In b(V293_create_function_blocks btask barg btop bp bi bb bz be bopt bs berr bc) -> fresh M b) ->
 (forall a tp v, In(a,tp,v) live -> ~In(fst a)(map fst(V293_create_local_addresses bp bc btask barg btop bopt bs bb bi bz be berr))) ->
 (forall b1 b2 b3 b4 b5 b6 b7 b8 b9,
  NoDup (V293_tcb_function_blocks b1 b2 b3 b4 b5 b6 b7 b8 b9) ->
  V293_tcb_creation_hook_return P hi block base (V293_tcb_first_hook_cont 901%Z hi hc le (V293_create_TCB_cont 209%Z rest ks))
   ge (V293_tcb_function_env b1 b2 b3 b4 b5 b6 b7 b8 b9) ir aux O op enabled si ci
   (V293_tcb_hook_cells b1 b2 b3 b4 b5 b6 b7 b8 b9 bf bt block base p
    value bottomv idv sizev extv optv next (Vptr(br,Int.zero))
    (V293_tcb_creation_tail block base bh bg rows count bo obase present p prev g r n back++(V293_create_caller_cells bp bn bc p btask barg btop bopt target argv topv optv bs bb bi bz be berr value bottomv idv sizev extv Vundef++kept)))) /\
 (forall b1 b2 b3 b4 b5 b6 b7 b8 b9,
  NoDup (V293_tcb_function_blocks b1 b2 b3 b4 b5 b6 b7 b8 b9) ->
  V293_tcb_creation_hook_return P hc block base (V293_tcb_second_hook_cont 901%Z hi hc le (V293_create_TCB_cont 209%Z rest ks))
   ge (V293_tcb_function_env b1 b2 b3 b4 b5 b6 b7 b8 b9) ir aux O op enabled si ci
   (V293_tcb_hook_cells b1 b2 b3 b4 b5 b6 b7 b8 b9 bf bt block base p
    value bottomv idv sizev extv optv next (Vptr(block,Int.repr base))
    (V293_tcb_creation_tail block base bh bg rows count bo obase present p prev g r n back++(V293_create_caller_cells bp bn bc p btask barg btop bopt target argv topv optv bs bb bi bz be berr value bottomv idv sizev extv Vundef++kept)))) /\
 V293_create_stack_return P 900%Z [optv;topv;argv;V293_task_selector target]
 (V293_create_stack_cont 108%Z 209%Z 901%Z 101%Z 205%Z 206%Z 207%Z 208%Z 204%Z rest ks)
 ge le ir aux O op (V293_rdy_raw_cells (V293_create_TCB_support bf block base bh bg rows count bo obase present p next oldfields prev g r n back kept) Atrue) enabled si ci
 (V293_create_bridge_cells bp bn bc bt p (Vint32 Int.zero) (Vptr(br,Int.zero))
 btask barg btop bopt target argv topv optv bs bb bi bz be berr Vundef bottomv idv sizev extv Vundef) value) ->
 (ge,caller,M,ir,aux,O,op) |= V293_rdy_raw_cells
 ([((bn,0),Tint8,V293_byteval 0);((bt,4*Z.of_nat p),Tptr V293_tcb_type,Vnull)]++
 V293_create_TCB_support bf block base bh bg rows count bo obase present p next oldfields prev g r n back kept) Atrue ->
 exists btask, exists barg, exists btop, exists bp, exists bi, exists bb, exists bz, exists be, exists bopt, exists bs, exists berr, exists bc,
 let le:=V293_create_function_env btask barg btop bp bi bb bz be bopt bs berr bc in
 let addresses:=V293_create_local_addresses bp bc btask barg btop bopt bs bb bi bz be berr in
 NoDup(V293_create_function_blocks btask barg btop bp bi bb bz be bopt bs berr bc) /\
 (forall b, In b(V293_create_function_blocks btask barg btop bp bi bb bz be bopt bs berr bc) -> fresh M b) /\
 (forall a tp v, In(a,tp,v) live -> ~In(fst a)(map fst addresses)) /\
 exists Mbridge, exists b1, exists b2, exists b3, exists b4, exists b5, exists b6, exists b7, exists b8, exists b9, exists Mf, exists Mr,
 NoDup (V293_tcb_function_blocks b1 b2 b3 b4 b5 b6 b7 b8 b9) /\
 (forall b, In b (V293_tcb_function_blocks b1 b2 b3 b4 b5 b6 b7 b8 b9) -> fresh Mbridge b) /\
 V293_local_steps P
 (curs(sfexec f [optv;extv;sizev;bottomv;idv;V293_byteval p;topv;argv;V293_task_selector target] V293_CreateExt_argument_types),(kenil,retks))
 ((ge,caller,M),ir,(enabled,si,ci))
 (curs(sfexec 901%Z [optv;extv;sizev;idv;bottomv;value;V293_byteval p] V293_TCBInit_argument_types),(kenil,V293_create_TCB_cont 209%Z rest ks))
 ((ge,le,Mbridge),ir,(enabled,si,ci)) /\
 V293_local_steps P
 (curs(sfexec f [optv;extv;sizev;bottomv;idv;V293_byteval p;topv;argv;V293_task_selector target] V293_CreateExt_argument_types),(kenil,retks))
 ((ge,caller,M),ir,(enabled,si,ci))
 (curs(sskip(Some(Vint32 Int.zero))),(kenil,retks))
 ((ge,caller,Mr),ir,(enabled,si,ci)) /\
 (ge,caller,Mr,ir,aux,O,op) |= V293_rdy_raw_cells live Atrue /\
 (forall b tp k, In (b,tp) (V293_tcb_function_addresses b1 b2 b3 b4 b5 b6 b7 b8 b9) ->
 (k<typelen tp)%nat -> get Mr (b,Z.of_nat k)=None) /\
 (forall b tp k, In(b,tp) addresses -> (k<typelen tp)%nat -> get Mr(b,Z.of_nat k)=None) /\
 (forall b i, ~In b(map fst addresses) -> get Mr(b,i)=get Mf(b,i)).
Proof.
 intros P retks caller f ge M ir aux O op enabled si ci bn bt br p target argv topv optv bottomv idv sizev extv value
 hi hc bf block base bh bg rows count bo obase present next oldfields prev g r n back frame brun
 body ks rest kept live Function Gr Gn Gt Gres Range Target ArgValid Valid Program
 FreeGlobal TableGlobal HeadGlobal GroupGlobal RowsGlobal CountGlobal Base Bound OldBase OldBound G Row Count Next Hooks Owned.
 destruct(V293_create_fresh_twelve_avoiding M live) as (btask&barg&btop&bp&bi&bb&bz&be&bopt&bs&berr&bc&ND&Fresh&Disjoint).
 assert (Away : forall a tp v, In(a,tp,v) live ->
  ~In(fst a)(map fst(V293_create_local_addresses bp bc btask barg btop bopt bs bb bi bz be berr))).
 { intros a tp v Member Inside. apply(Disjoint a tp v Member).
   unfold V293_create_local_addresses in Inside. unfold V293_create_function_blocks.
   cbn [map fst In] in Inside |- *. tauto. }
 destruct(Hooks btask barg btop bp bi bb bz be bopt bs berr bc ND Fresh Away) as (Hook1&Hook2&Stack).
 exists btask. exists barg. exists btop. exists bp. exists bi. exists bb. exists bz. exists be. exists bopt. exists bs. exists berr. exists bc.
 split;[exact ND| ]. split;[exact Fresh| ]. split;[exact Away| ].
 eapply(V293_OSTaskCreateExt_success_call_under_hooks
 P retks caller f ge M ir aux O op enabled si ci 92%Z 97%Z 98%Z 99%Z 904%Z 900%Z 901%Z
 bp bn bc bt br p btask barg btop bopt target argv topv optv bs bb bi bz be berr bottomv idv sizev extv value
 hi hc bf block base bh bg rows count bo obase present next oldfields prev g r n back frame brun);
 eassumption||reflexivity.
Qed.
Print Assumptions V293_OSTaskCreateExt_fresh_success_call_under_hooks.
