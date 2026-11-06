(* Normalized success call from sfexec through allocation, initialization,
   priority store, publication, return and free, conditional on two real
   Hook-return contracts. No missing Hook implementation is fabricated. *)
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
Import ListNotations.
Local Open Scope Z_scope.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFunction.
Require Import CertiOS.certiucos.v293.proofs.V293InitChain.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.

Require Import CertiOS.certiucos.v293.proofs.V293TCBInitEntry.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPriorityHook.
Require Import CertiOS.certiucos.v293.proofs.V293TCBSuccessReturn.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPublish.

(* No port implementation is supplied here. Both Hook-return contracts are
   explicit hypotheses; the fixed declaration-only Hooks cannot satisfy them. *)
Lemma V293_tcb_fresh_nine_avoiding : forall M (cells : list V293_record_cell),
 exists b1 b2 b3 b4 b5 b6 b7 b8 b9,
 NoDup (V293_tcb_function_blocks b1 b2 b3 b4 b5 b6 b7 b8 b9) /\
 (forall b, In b (V293_tcb_function_blocks b1 b2 b3 b4 b5 b6 b7 b8 b9) -> fresh M b) /\
 (forall a tp v, In (a,tp,v) cells ->
  ~In (fst a) (V293_tcb_function_blocks b1 b2 b3 b4 b5 b6 b7 b8 b9)).
Proof.
 intros M cells. destruct (HalfPermMap.bounded M) as [bound Below].
 set (start:=Pos.max bound (Pos.succ (V293_cells_upper cells))).
 exists (start).
 exists (Pos.succ (start)).
 exists (Pos.succ (Pos.succ (start))).
 exists (Pos.succ (Pos.succ (Pos.succ (start)))).
 exists (Pos.succ (Pos.succ (Pos.succ (Pos.succ (start))))).
 exists (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (start)))))).
 exists (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (start))))))).
 exists (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (start)))))))).
 exists (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (start))))))))).

 assert (LT : (V293_cells_upper cells<start)%positive).
 { unfold start. eapply Pos.lt_le_trans;[apply Pos.lt_succ_diag_r|apply Pos.le_max_r]. }
 assert (Fresh : forall b, (start<=b)%positive -> fresh M b).
 { intros b B a i E [v Read];subst a.
   assert (Small : (b<bound)%positive) by (eapply Below;exact Read).
   assert (High : (bound<=start)%positive) by (unfold start;apply Pos.le_max_l). lia. }
 split.
 - unfold V293_tcb_function_blocks. repeat constructor;cbn;intuition lia.
 - split.
   + intros b Member. apply Fresh. unfold V293_tcb_function_blocks in Member.
     cbn in Member. repeat destruct Member as [E|Member];try contradiction;subst b;lia.
   + intros a tp v Member Inside.
     pose proof (V293_cells_upper_bound cells a tp v Member) as Bound.
     unfold V293_tcb_function_blocks in Inside. cbn in Inside.
     repeat destruct Inside as [E|Inside];try contradiction.
     all: apply (Pos.lt_irrefl (fst a));eapply Pos.le_lt_trans;[exact Bound| ];
      eapply Pos.lt_le_trans;[exact LT| ];rewrite <-E;lia.
Qed.

(* The same retained first-Hook entry proof with caller-selected fresh blocks,
   so their disjointness from every future survivor is not lost existentially. *)
Lemma V293_tcb_first_hook_with_blocks : forall P ks ge caller M ir aux O op enabled si ci
 f hook_init hook_create b1 b2 b3 b4 b5 b6 b7 b8 b9 bf bt base p top bottom identity size ext options next old frame,
 P f=Some (V293_TCBInit_function hook_init hook_create) ->
 get ge 91%Z=Some (bf,Tptr V293_tcb_type) ->
 (p<13)%nat -> (0<=base)%Z -> (base+55<=Int.max_unsigned)%Z ->
 V293_tcb_init_values_valid top bottom identity size ext options ->
 rule_type_val_match (Tptr V293_tcb_type) next=true ->
 NoDup (V293_tcb_function_blocks b1 b2 b3 b4 b5 b6 b7 b8 b9) ->
 (forall b, In b (V293_tcb_function_blocks b1 b2 b3 b4 b5 b6 b7 b8 b9) -> fresh M b) ->
 (ge,caller,M,ir,aux,O,op) |= V293_rdy_raw_cells
 (V293_tcb_init_old_fields bt base old ++
  V293_tcb_prefix_links bf bt base (Vptr (bt,Int.repr base)) next ++frame) Atrue ->
 exists Mf,
 V293_local_steps P
  (curs(sfexec f [options;ext;size;identity;bottom;top;V293_byteval p]
    V293_TCBInit_argument_types),(kenil,ks))
  ((ge,caller,M),ir,(enabled,si,ci))
  (curs(sfexec hook_init (Vptr(bt,Int.repr base)::nil) (Tptr V293_tcb_type::nil)),
   (kenil,V293_tcb_first_hook_cont f hook_init hook_create caller ks))
  ((ge,V293_tcb_function_env b1 b2 b3 b4 b5 b6 b7 b8 b9,Mf),ir,(enabled,si,ci)) /\
 (ge,V293_tcb_function_env b1 b2 b3 b4 b5 b6 b7 b8 b9,Mf,ir,aux,O,op) |=
 V293_rdy_raw_cells
 (V293_tcb_init_final_fields bt base p top bottom identity size ext options ++
  V293_tcb_init_input_cells b8 b1 b2 b3 b4 b5 b6 b7 bt base p top bottom identity size ext options ++
  V293_tcb_prefix_links bf bt base next next ++((b9,0),Tint32,Vint32 Int.zero)::frame) Atrue /\
 (P hook_init=None -> ~ exists C' state',
  loststep P
  (curs(sfexec hook_init (Vptr(bt,Int.repr base)::nil) (Tptr V293_tcb_type::nil)),
   (kenil,V293_tcb_first_hook_cont f hook_init hook_create caller ks))
  ((ge,V293_tcb_function_env b1 b2 b3 b4 b5 b6 b7 b8 b9,Mf),ir,(enabled,si,ci)) C' state').
Proof.
 intros P ks ge caller M ir aux O op enabled si ci f hook_init hook_create b1 b2 b3 b4 b5 b6 b7 b8 b9 bf bt base
 p top bottom identity size ext options next old frame Program Global Range Base Bound Valid Next ND Fresh Owned.
 set (le:=V293_tcb_function_env b1 b2 b3 b4 b5 b6 b7 b8 b9).
 assert (Values : V293_tcb_function_values_valid (V293_byteval p) top bottom identity size ext options).
 { unfold V293_tcb_function_values_valid. unfold V293_tcb_init_values_valid in Valid.
   split;[apply V293_byte_type;lia|exact Valid]. }
 destruct (V293_tcb_call_prologue P ks ge caller M ir aux O op enabled si ci
  f hook_init hook_create b1 b2 b3 b4 b5 b6 b7 b8 b9
  (V293_byteval p) top bottom identity size ext options _ Program ND Fresh Values Owned)
 as (Mi&Prologue&Allocated).
 assert (Env : V293_tcb_init_env le 108%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z b8 b1 b2 b3 b4 b5 b6 b7).
 { unfold V293_tcb_init_env,le,V293_tcb_function_env. repeat split;
   repeat rewrite map_get_set' by discriminate;apply map_get_set. }
 assert (FreeLocal : get le 91%Z=None).
 { unfold le,V293_tcb_function_env. repeat rewrite map_get_set' by discriminate. apply map_emp_get. }
 assert (Start : (ge,le,Mi,ir,aux,O,op) |= V293_rdy_raw_cells
 (V293_tcb_init_old_fields bt base old ++
  V293_tcb_prefix_inputs b8 b1 b2 b3 b4 b5 b6 b7 Vundef p top bottom identity size ext options ++
  V293_tcb_prefix_links bf bt base (Vptr(bt,Int.repr base)) next)
 (V293_rdy_raw_cells (((b9,0),Tint32,Vint32 Int.zero)::frame) Atrue)).
 { unfold V293_tcb_function_cells,V293_tcb_prefix_inputs,V293_tcb_init_input_cells,
     V293_tcb_init_old_fields,V293_tcb_prefix_links in Allocated |- *.
   cbn [V293_rdy_raw_cells app tl] in Allocated |- *. clear -Allocated. sep auto. }
 destruct (V293_OS_TCBInit_prefix_execution P
  (kcall f (V293_TCBInit_function_body hook_init hook_create) caller ks) ge le Mi ir aux O op
  _ enabled si ci 91%Z 108%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z
  b8 b1 b2 b3 b4 b5 b6 b7 bf bt base p top bottom identity size ext options Vundef next old
  (V293_TCBInit_success_suffix hook_init hook_create) Range Base Bound FreeLocal Global Env Valid Next Start)
 as (Mf&Prefix&Final).
 assert (PtcbBinding : get le 108%Z=Some(b8,Tptr V293_tcb_type)) by exact (proj1 Env).
 V293_tcb_init_read Final 18%nat PtrRead.
 exists Mf. split.
 - eapply V293_local_trans;[exact Prologue| ].
   eapply V293_local_trans;[exact Prefix| ].
   unfold V293_TCBInit_success_suffix,V293_tcb_first_hook_cont,V293_tcb_after_init_hook.
   eapply V293_local_cons. { apply ostc_step. eapply stmt_step;[reflexivity|apply sseq_step]. }
   eapply V293_local_cons. { apply ostc_step. eapply stmt_step;[reflexivity| ].
     apply spcall_step with (t:=Tptr V293_tcb_type). V293_rdy_eval. }
   eapply V293_local_trans.
   { apply V293_csteps_local. apply V293_expr_steps. apply evalval_imply_estepstar.
     assert (HookValue : evalval (evar 108%Z) (ge,le,Mf)=Some(Vptr(bt,Int.repr base))) by V293_rdy_eval.
     exact HookValue. }
   eapply V293_local_cons. { apply ostc_step. eapply stmt_step;[reflexivity|apply svfevalnil_step]. }
   apply V293_local_refl.
 - split.
   + rewrite <-V293_raw_cells_append in Final. rewrite app_assoc. exact Final.
   + intros Missing. apply V293_missing_port_has_no_step. exact Missing.
Qed.

(* Source fields needed only after initialization: old head/global bits and
   predecessor link. The TCB next link is already owned by prefix_links. *)
Definition V293_tcb_creation_tail bt base bh bg br bn bo obase present p prev g r n back
 : list V293_record_cell :=
 [((bt,base+24),Tcom_ptr 410%Z,prev);
  ((bh,0),Tptr V293_tcb_type,V293_pub_old_head present bo obase);
  ((bg,0),Tint8,V293_byteval g);
  ((br,Z.of_nat (V293_prio_row p)),Tint8,V293_byteval r);
  ((bn,0),Tint8,V293_byteval n)]++
 if present then [((bo,obase+24),Tcom_ptr 410%Z,back)] else [].

(* The fifteen initialized fields not changed by publication. *)
Definition V293_tcb_creation_fields bt base p top bottom identity size ext options
 : list V293_record_cell :=
 firstn 11 (V293_tcb_init_final_fields bt base p top bottom identity size ext options)++
 [((bt,base+51),Tint8,V293_byteval (V293_prio_bit p))]++
 skipn 15 (V293_tcb_init_final_fields bt base p top bottom identity size ext options).
Definition V293_tcb_creation_frame bf table bt base p top bottom identity size ext options next frame :=
 V293_tcb_creation_fields bt base p top bottom identity size ext options++
 [((bf,0),Tptr V293_tcb_type,next);
  ((table,4*Z.of_nat p),Tptr V293_tcb_type,Vptr(bt,Int.repr base))]++frame.
Definition V293_tcb_creation_result bf table bt base bh bg br bn bo obase present p
 top bottom identity size ext options next g r n frame :=
 tl (V293_pub_cells 1%positive bt base bh bg br bn bo obase present
  (V293_prio_row p) (V293_prio_bit p) (V293_pub_old_head present bo obase) Vnull
  (Vptr(bt,Int.repr base)) (Nat.setbit g (V293_prio_row p))
  (Nat.setbit r (V293_prio_bit p)) (S n) (Vptr(bt,Int.repr base)))++
 V293_tcb_creation_frame bf table bt base p top bottom identity size ext options next frame.

(* A contract is a real trace plus preservation of the listed owned cells.
   No identity of whole input/output memory, no assumed no-op Hook. *)
Definition V293_tcb_creation_hook_return P hook bt base cont ge le ir aux O op enabled si ci cells :=
 forall Mh, (ge,le,Mh,ir,aux,O,op) |= V293_rdy_raw_cells cells Atrue ->
 exists Mr,
 V293_local_steps P
  (curs(sfexec hook [Vptr(bt,Int.repr base)] [Tptr V293_tcb_type]),(kenil,cont))
  ((ge,le,Mh),ir,(enabled,si,ci))
  (curs(sskip None),(kenil,cont)) ((ge,le,Mr),ir,(enabled,si,ci)) /\
 (ge,le,Mr,ir,aux,O,op) |= V293_rdy_raw_cells cells Atrue.

(* Stable conditional full-call interface. Missing Hook implementations remain
   obligations, not axioms, hidden code replacements or a coverage promotion. *)
Theorem V293_OS_TCBInit_success_call_under_hooks : forall P ks ge caller M ir aux O op enabled si ci
 f hi hc bf table bt base bh bg br bn bo obase present p top bottom identity size ext options
 next old slot prev g r n back frame,
 P f=Some (V293_TCBInit_function hi hc) ->
 get ge 91%Z=Some(bf,Tptr V293_tcb_type) ->
 get ge 92%Z=Some(table,Tarray (Tptr V293_tcb_type) 13) ->
 get ge 93%Z=Some(bh,Tptr V293_tcb_type) -> get ge 94%Z=Some(bg,Tint8) ->
 get ge 95%Z=Some(br,Tarray Tint8 2) -> get ge 96%Z=Some(bn,Tint8) ->
 (p<13)%nat -> (0<=base)%Z -> (base+55<=Int.max_unsigned)%Z ->
 (0<=obase)%Z -> (obase+24<=Int.max_unsigned)%Z ->
 (g<256)%nat -> (r<256)%nat -> (n<255)%nat ->
 V293_tcb_init_values_valid top bottom identity size ext options ->
 rule_type_val_match (Tptr V293_tcb_type) next=true ->
 (forall b1 b2 b3 b4 b5 b6 b7 b8 b9,
  NoDup (V293_tcb_function_blocks b1 b2 b3 b4 b5 b6 b7 b8 b9) ->
  V293_tcb_creation_hook_return P hi bt base (V293_tcb_first_hook_cont f hi hc caller ks)
   ge (V293_tcb_function_env b1 b2 b3 b4 b5 b6 b7 b8 b9) ir aux O op enabled si ci
   (V293_tcb_hook_cells b1 b2 b3 b4 b5 b6 b7 b8 b9 bf table bt base p
    top bottom identity size ext options next slot
    (V293_tcb_creation_tail bt base bh bg br bn bo obase present p prev g r n back++frame))) ->
 (forall b1 b2 b3 b4 b5 b6 b7 b8 b9,
  NoDup (V293_tcb_function_blocks b1 b2 b3 b4 b5 b6 b7 b8 b9) ->
  V293_tcb_creation_hook_return P hc bt base (V293_tcb_second_hook_cont f hi hc caller ks)
   ge (V293_tcb_function_env b1 b2 b3 b4 b5 b6 b7 b8 b9) ir aux O op enabled si ci
   (V293_tcb_hook_cells b1 b2 b3 b4 b5 b6 b7 b8 b9 bf table bt base p
    top bottom identity size ext options next (Vptr(bt,Int.repr base))
    (V293_tcb_creation_tail bt base bh bg br bn bo obase present p prev g r n back++frame))) ->
 (ge,caller,M,ir,aux,O,op) |= V293_rdy_raw_cells
 (V293_tcb_init_old_fields bt base old++
  V293_tcb_prefix_links bf bt base (Vptr(bt,Int.repr base)) next++
  ((table,4*Z.of_nat p),Tptr V293_tcb_type,slot)::
  (V293_tcb_creation_tail bt base bh bg br bn bo obase present p prev g r n back++frame)) Atrue ->
 exists b1 b2 b3 b4 b5 b6 b7 b8 b9 Mf,
 NoDup (V293_tcb_function_blocks b1 b2 b3 b4 b5 b6 b7 b8 b9) /\
 (forall b, In b (V293_tcb_function_blocks b1 b2 b3 b4 b5 b6 b7 b8 b9) -> fresh M b) /\
 V293_local_steps P
  (curs(sfexec f [options;ext;size;identity;bottom;top;V293_byteval p]
    V293_TCBInit_argument_types),(kenil,ks)) ((ge,caller,M),ir,(enabled,si,ci))
  (curs(sskip(Some(Vint32 Int.zero))),(kenil,ks)) ((ge,caller,Mf),ir,(enabled,si,ci)) /\
 (ge,caller,Mf,ir,aux,O,op) |= V293_rdy_raw_cells
  (V293_tcb_creation_result bf table bt base bh bg br bn bo obase present p
   top bottom identity size ext options next g r n frame) Atrue /\
 (forall b tp k, In (b,tp) (V293_tcb_function_addresses b1 b2 b3 b4 b5 b6 b7 b8 b9) ->
  (k<typelen tp)%nat -> get Mf (b,Z.of_nat k)=None).
Proof.
 intros P ks ge caller M ir aux O op enabled si ci f hi hc bf table bt base bh bg br bn bo obase
 present p top bottom identity size ext options next old slot prev g r n back frame
 Program FreeGlobal TableGlobal HeadGlobal GroupGlobal RowsGlobal CountGlobal
 Range Base Bound OldBase OldBound G Row Count Valid Next Hook1 Hook2 Entry.
 set (result:=V293_tcb_creation_result bf table bt base bh bg br bn bo obase present p
   top bottom identity size ext options next g r n frame).
 set (tail:=V293_tcb_creation_tail bt base bh bg br bn bo obase present p prev g r n back++frame).
 destruct (V293_tcb_fresh_nine_avoiding M result)
  as (b1&b2&b3&b4&b5&b6&b7&b8&b9&ND&Fresh&Away).
 destruct (V293_tcb_first_hook_with_blocks P ks ge caller M ir aux O op enabled si ci
  f hi hc b1 b2 b3 b4 b5 b6 b7 b8 b9 bf bt base p top bottom identity size ext options next old
  (((table,4*Z.of_nat p),Tptr V293_tcb_type,slot)::tail)
  Program FreeGlobal Range Base Bound Valid Next ND Fresh Entry)
 as (Mi&Prefix&Initialized&MissingFirst).
 destruct (Hook1 b1 b2 b3 b4 b5 b6 b7 b8 b9 ND Mi Initialized)
 as (Mr&FirstExec&Returned).
 set (le:=V293_tcb_function_env b1 b2 b3 b4 b5 b6 b7 b8 b9).
 assert (PriorityLocal : get le 101%Z=Some(b1,Tint8)).
 { unfold le,V293_tcb_function_env. repeat rewrite map_get_set' by discriminate;apply map_get_set. }
 assert (PtcbLocal : get le 108%Z=Some(b8,Tptr V293_tcb_type)).
 { unfold le,V293_tcb_function_env. repeat rewrite map_get_set' by discriminate;apply map_get_set. }
 assert (TableLocal : get le 92%Z=None).
 { unfold le,V293_tcb_function_env. repeat rewrite map_get_set' by discriminate;apply map_emp_get. }
 set (rest:=V293_tcb_init_final_fields bt base p top bottom identity size ext options++
  tl(tl(V293_tcb_init_input_cells b8 b1 b2 b3 b4 b5 b6 b7 bt base p top bottom identity size ext options))++
  V293_tcb_prefix_links bf bt base next next++((b9,0),Tint32,Vint32 Int.zero)::tail).
 assert (BridgeOwned : (ge,le,Mr,ir,aux,O,op) |= V293_rdy_raw_cells
  (V293_tcb_priority_cells b1 b8 table bt base p slot) (V293_rdy_raw_cells rest Atrue)).
 { unfold V293_tcb_hook_cells in Returned. unfold rest,V293_tcb_priority_cells.
   unfold V293_tcb_init_final_fields,V293_tcb_init_input_cells,V293_tcb_prefix_links in Returned |- *.
   cbn [V293_rdy_raw_cells app tl] in Returned |- *. clear -Returned. sep auto. }
 destruct (V293_OS_TCBInit_priority_to_second_hook P f hi hc caller ks ge le Mr ir aux O op
  (V293_rdy_raw_cells rest Atrue) enabled si ci b1 b8 table bt base p slot
  PriorityLocal PtcbLocal TableLocal TableGlobal Range BridgeOwned)
 as (Mh&PriorityExec&PriorityFinal&MissingSecond).
 assert (SecondOwned : (ge,le,Mh,ir,aux,O,op) |= V293_rdy_raw_cells
  (V293_tcb_hook_cells b1 b2 b3 b4 b5 b6 b7 b8 b9 bf table bt base p
    top bottom identity size ext options next (Vptr(bt,Int.repr base)) tail) Atrue).
 { unfold V293_tcb_hook_cells. unfold rest,V293_tcb_priority_cells in PriorityFinal.
   unfold V293_tcb_init_final_fields,V293_tcb_init_input_cells,V293_tcb_prefix_links in PriorityFinal |- *.
   cbn [V293_rdy_raw_cells app tl] in PriorityFinal |- *. clear -PriorityFinal. sep auto. }
 destruct (Hook2 b1 b2 b3 b4 b5 b6 b7 b8 b9 ND Mh SecondOwned)
 as (Mc&SecondExec&SecondReturned).
 set (survivors:=V293_tcb_creation_frame bf table bt base p top bottom identity size ext options next frame).
 assert (PubEnv : V293_pub_env ge le 108%Z 93%Z 94%Z 95%Z 96%Z b8 bh bg br bn).
 { unfold V293_pub_env. repeat split;try assumption;
   unfold le,V293_tcb_function_env;repeat rewrite map_get_set' by discriminate;apply map_emp_get. }
 assert (PubOwned : (ge,le,Mc,ir,aux,O,op) |= V293_rdy_raw_cells
  (V293_pub_cells b8 bt base bh bg br bn bo obase present (V293_prio_row p) (V293_prio_bit p)
    next prev (V293_pub_old_head present bo obase) g r n back)
  (V293_rdy_raw_cells (V293_tcb_other_locals b1 b2 b3 b4 b5 b6 b7 b9
    (V293_byteval p) top bottom identity size ext options (Vint32 Int.zero)++survivors) Atrue)).
 { unfold V293_tcb_hook_cells in SecondReturned.
   unfold tail,V293_tcb_creation_tail,V293_pub_cells in SecondReturned |- *.
   unfold survivors,V293_tcb_creation_frame,V293_tcb_creation_fields,V293_tcb_init_final_fields,
     V293_tcb_init_input_cells,V293_tcb_prefix_links,V293_tcb_other_locals in SecondReturned |- *.
   destruct present;cbn [firstn skipn app V293_rdy_raw_cells] in SecondReturned |- *.
   all: clear -SecondReturned;sep auto. }
 assert (Y : (V293_prio_row p<2)%nat).
 { unfold V293_prio_row. destruct (p <? 8)%nat;lia. }
 assert (X : (V293_prio_bit p<8)%nat).
 { unfold V293_prio_bit. destruct (p <? 8)%nat eqn:E;[apply Nat.ltb_lt in E|apply Nat.ltb_ge in E];lia. }
 destruct (V293_OS_TCBInit_success_suffix_return P f hi hc caller ks ge Mc ir aux O op enabled si ci
  b1 b2 b3 b4 b5 b6 b7 b8 b9 bt base bh bg br bn bo obase present
  (V293_prio_row p) (V293_prio_bit p) g r n next prev back
  (V293_byteval p) top bottom identity size ext options (Vint32 Int.zero) survivors
  PubEnv ND Base ltac:(lia) OldBase OldBound Y X G Row Count Away PubOwned)
 as (Ms&Mf&Suffix&BeforeFree&Final&Freed).
 exists b1. exists b2. exists b3. exists b4. exists b5. exists b6. exists b7. exists b8. exists b9. exists Mf.
 split;[exact ND| ]. split;[exact Fresh| ]. split.
 - eapply V293_local_trans;[exact Prefix| ].
   eapply V293_local_trans;[exact FirstExec| ].
   eapply V293_local_trans;[exact PriorityExec| ].
   eapply V293_local_trans;[exact SecondExec|exact Suffix].
 - split;[exact Final|exact Freed].
Qed.
Print Assumptions V293_OS_TCBInit_success_call_under_hooks.
