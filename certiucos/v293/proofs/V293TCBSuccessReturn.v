(* Actual post-second-Hook suffix, including publication and physical return/free.
   No claim that this return anchor is reachable with missing port definitions. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPriorityHook.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPublish.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFunction.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBCall.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBClear.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBList.
Require Import CertiOS.certiucos.v293.proofs.V293NullBytes.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitFunction.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitPrefix.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.code.V293OSTCBPublish.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope Z_scope.
(* ptcb is already the first publication cell; do not own its bytes twice. *)
Definition V293_tcb_other_locals b1 b2 b3 b4 b5 b6 b7 b9 v1 v2 v3 v4 v5 v6 v7 saved
 : list V293_record_cell :=
 [((b9,0),Tint32,saved);((b1,0),Tint8,v1);((b2,0),Tptr Tint32,v2);
  ((b3,0),Tptr Tint32,v3);((b4,0),Tint16,v4);((b5,0),Tint32,v5);
  ((b6,0),Tptr Tvoid,v6);((b7,0),Tint16,v7)].

Theorem V293_OS_TCBInit_success_suffix_return : forall P f hi hc caller ks ge M ir aux O op enabled si ci
 b1 b2 b3 b4 b5 b6 b7 b8 b9 bt base bh bg br bn bo obase present y x g r n
 oldnext oldprev oldback v1 v2 v3 v4 v5 v6 v7 saved frame,
 let le:=V293_tcb_function_env b1 b2 b3 b4 b5 b6 b7 b8 b9 in
 let blocks:=V293_tcb_function_blocks b1 b2 b3 b4 b5 b6 b7 b8 b9 in
 let before:=V293_pub_cells b8 bt base bh bg br bn bo obase present y x
  oldnext oldprev (V293_pub_old_head present bo obase) g r n oldback in
 let after:=V293_pub_cells b8 bt base bh bg br bn bo obase present y x
  (V293_pub_old_head present bo obase) Vnull (Vptr(bt,Int.repr base))
  (Nat.setbit g y) (Nat.setbit r x) (S n) (Vptr(bt,Int.repr base)) in
 V293_pub_env ge le 108%Z 93%Z 94%Z 95%Z 96%Z b8 bh bg br bn ->
 NoDup blocks ->
 (0<=base)%Z -> (base+54<=Int.max_unsigned)%Z ->
 (0<=obase)%Z -> (obase+24<=Int.max_unsigned)%Z ->
 (y<2)%nat -> (x<8)%nat -> (g<256)%nat -> (r<256)%nat -> (n<255)%nat ->
 (forall a tp v, In (a,tp,v) (tl after++frame) -> ~In (fst a) blocks) ->
 (ge,le,M,ir,aux,O,op) |= V293_rdy_raw_cells before
   (V293_rdy_raw_cells (V293_tcb_other_locals b1 b2 b3 b4 b5 b6 b7 b9 v1 v2 v3 v4 v5 v6 v7 saved++frame) Atrue) ->
 exists Ms Mf,
 V293_local_steps P
  (curs(sskip None),(kenil,V293_tcb_second_hook_cont f hi hc caller ks))
  ((ge,le,M),ir,(enabled,si,ci))
  (curs(sskip(Some(Vint32 Int.zero))),(kenil,ks)) ((ge,caller,Mf),ir,(enabled,si,ci)) /\
 (ge,le,Ms,ir,aux,O,op) |= V293_rdy_raw_cells after
   (V293_rdy_raw_cells (V293_tcb_other_locals b1 b2 b3 b4 b5 b6 b7 b9 v1 v2 v3 v4 v5 v6 v7 saved++frame) Atrue) /\
 (ge,caller,Mf,ir,aux,O,op) |= V293_rdy_raw_cells (tl after++frame) Atrue /\
 (forall b tp k, In (b,tp) (V293_tcb_function_addresses b1 b2 b3 b4 b5 b6 b7 b8 b9) ->
   (k<typelen tp)%nat -> get Mf (b,Z.of_nat k)=None).
Proof.
 intros P f hi hc caller ks ge M ir aux O op enabled si ci
 b1 b2 b3 b4 b5 b6 b7 b8 b9 bt base bh bg br bn bo obase present y x g r n
 oldnext oldprev oldback v1 v2 v3 v4 v5 v6 v7 saved frame le blocks before after
 Env ND Base Bound OldBase OldBound Y X G Row Count Away Owned.
 destruct (V293_OS_TCBInit_publication_execution P
  (kseq V293_TCBInit_empty (kcall f (V293_TCBInit_function_body hi hc) caller ks))
  ge le M ir aux O op _ enabled si ci 108%Z 93%Z 94%Z 95%Z 96%Z
  b8 bt base bh bg br bn bo obase present y x g r n oldnext oldprev oldback
  Env Base Bound OldBase OldBound Y X G Row Count Owned) as (Ms&Publish&Final).
 assert (Layout : getaddr le=V293_tcb_function_addresses b1 b2 b3 b4 b5 b6 b7 b8 b9).
 { apply V293_tcb_function_layout. }
 assert (Writable : forall b tp, In (b,tp) (getaddr le) -> V293_bytes_writable Ms b 0 (typelen tp)).
 { intros b tp Member. rewrite Layout in Member. unfold V293_tcb_function_addresses in Member.
   change ((ge,le,Ms,ir,aux,O,op) |= V293_rdy_raw_cells after
    (V293_rdy_raw_cells (V293_tcb_other_locals b1 b2 b3 b4 b5 b6 b7 b9 v1 v2 v3 v4 v5 v6 v7 saved++frame) Atrue)) in Final.
   unfold after,V293_pub_cells,V293_tcb_other_locals in Final.
   destruct present;cbn [app V293_rdy_raw_cells] in Final.
   all: repeat destruct Member as [E|Member];try contradiction;inversion E;subst.
   - eapply V293_tick_raw_owned_writable with (v:=v1) (R:=Atrue) (ge:=ge) (le:=le) (ir:=ir) (aux:=aux) (O:=O) (op:=op);clear -Final;sep auto.
   - eapply V293_tick_raw_owned_writable with (v:=v2) (R:=Atrue) (ge:=ge) (le:=le) (ir:=ir) (aux:=aux) (O:=O) (op:=op);clear -Final;sep auto.
   - eapply V293_tick_raw_owned_writable with (v:=v3) (R:=Atrue) (ge:=ge) (le:=le) (ir:=ir) (aux:=aux) (O:=O) (op:=op);clear -Final;sep auto.
   - eapply V293_tick_raw_owned_writable with (v:=v4) (R:=Atrue) (ge:=ge) (le:=le) (ir:=ir) (aux:=aux) (O:=O) (op:=op);clear -Final;sep auto.
   - eapply V293_tick_raw_owned_writable with (v:=v5) (R:=Atrue) (ge:=ge) (le:=le) (ir:=ir) (aux:=aux) (O:=O) (op:=op);clear -Final;sep auto.
   - eapply V293_tick_raw_owned_writable with (v:=v6) (R:=Atrue) (ge:=ge) (le:=le) (ir:=ir) (aux:=aux) (O:=O) (op:=op);clear -Final;sep auto.
   - eapply V293_tick_raw_owned_writable with (v:=v7) (R:=Atrue) (ge:=ge) (le:=le) (ir:=ir) (aux:=aux) (O:=O) (op:=op);clear -Final;sep auto.
   - eapply V293_tick_raw_owned_writable with (v:=Vptr(bt,Int.repr base)) (R:=Atrue) (ge:=ge) (le:=le) (ir:=ir) (aux:=aux) (O:=O) (op:=op);clear -Final;sep auto.
   - eapply V293_tick_raw_owned_writable with (v:=saved) (R:=Atrue) (ge:=ge) (le:=le) (ir:=ir) (aux:=aux) (O:=O) (op:=op);clear -Final;sep auto.
   - eapply V293_tick_raw_owned_writable with (v:=v1) (R:=Atrue) (ge:=ge) (le:=le) (ir:=ir) (aux:=aux) (O:=O) (op:=op);clear -Final;sep auto.
   - eapply V293_tick_raw_owned_writable with (v:=v2) (R:=Atrue) (ge:=ge) (le:=le) (ir:=ir) (aux:=aux) (O:=O) (op:=op);clear -Final;sep auto.
   - eapply V293_tick_raw_owned_writable with (v:=v3) (R:=Atrue) (ge:=ge) (le:=le) (ir:=ir) (aux:=aux) (O:=O) (op:=op);clear -Final;sep auto.
   - eapply V293_tick_raw_owned_writable with (v:=v4) (R:=Atrue) (ge:=ge) (le:=le) (ir:=ir) (aux:=aux) (O:=O) (op:=op);clear -Final;sep auto.
   - eapply V293_tick_raw_owned_writable with (v:=v5) (R:=Atrue) (ge:=ge) (le:=le) (ir:=ir) (aux:=aux) (O:=O) (op:=op);clear -Final;sep auto.
   - eapply V293_tick_raw_owned_writable with (v:=v6) (R:=Atrue) (ge:=ge) (le:=le) (ir:=ir) (aux:=aux) (O:=O) (op:=op);clear -Final;sep auto.
   - eapply V293_tick_raw_owned_writable with (v:=v7) (R:=Atrue) (ge:=ge) (le:=le) (ir:=ir) (aux:=aux) (O:=O) (op:=op);clear -Final;sep auto.
   - eapply V293_tick_raw_owned_writable with (v:=Vptr(bt,Int.repr base)) (R:=Atrue) (ge:=ge) (le:=le) (ir:=ir) (aux:=aux) (O:=O) (op:=op);clear -Final;sep auto.
   - eapply V293_tick_raw_owned_writable with (v:=saved) (R:=Atrue) (ge:=ge) (le:=le) (ir:=ir) (aux:=aux) (O:=O) (op:=op);clear -Final;sep auto.

 }
 assert (FreeND : NoDup (map fst (getaddr le))) by (rewrite Layout;exact ND).
 destruct (V293_error_return_execution P
  (kseq V293_TCBInit_empty (kcall f (V293_TCBInit_function_body hi hc) caller ks))
  ge le caller Ms f (V293_TCBInit_function_body hi hc) ks 0 eq_refl FreeND Writable)
  as (Mf&Return&Preserve&Removed).
 exists Ms. exists Mf. split.
 - eapply V293_local_cons. { unfold V293_tcb_second_hook_cont. V293_prefix_stmt. }
   eapply V293_local_trans;[exact Publish|apply V293_csteps_local;exact Return].
 - split;[exact Final| ]. split.
   + eapply V293_raw_cells_return_many with (M:=Ms) (le:=le) (freed:=blocks)
       (R:=V293_rdy_raw_cells (V293_tcb_function_cells b1 b2 b3 b4 b5 b6 b7 b8 b9 v1 v2 v3 v4 v5 v6 v7 (Vptr(bt,Int.repr base)) saved) Atrue).
     * exact Away.
     * intros b i Outside. apply Preserve. rewrite Layout. exact Outside.
     * rewrite V293_raw_cells_append.
       eapply V293_raw_cells_mono;[apply V293_raw_cells_swap| ].
       unfold after,V293_pub_cells,V293_tcb_function_cells in Final |- *.
       destruct present;cbn [tl app V293_rdy_raw_cells] in Final |- *.
       all:
       unfold V293_tcb_other_locals in Final;cbn [app V293_rdy_raw_cells] in Final.
       all: clear -Final;sep auto.
   + intros b tp k Member BoundK. apply (Removed b tp k);[rewrite Layout;exact Member|exact BoundK].
Qed.
Print Assumptions V293_OS_TCBInit_success_suffix_return.
