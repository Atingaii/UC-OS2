(* Real call/allocation prefix reaches the existing shared suffix contract.
   The CPU hook is still a real call and remains an open boundary. *)
(* Original post-hook on REAL local storage, including Vundef.
   Existing canonical fields and ordered abstract actions are unchanged. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickChainOpen.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickPostHookHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickSuffix.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickShared.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFieldsHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickWhileCore.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickWhileHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickDelayHoare.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickCoreFocus.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickWhileShared.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickWhileRecords.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickRecordReassembly.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLosslessFields.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickReadyUpdate.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickTaskBridge.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLoop.
Require Import CertiOS.certiucos.v293.proofs.V293TimeReadyShared.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.code.V293OSTimeTick.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.soundness.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import Coq.Lists.List Coq.Sorting.Permutation Lia.
Import ListNotations.
Local Open Scope nat_scope.


Require Import CertiOS.certiucos.v293.proofs.V293TimeTickSwitchBoundary.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickPostHookCore.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickScanSlot.

Definition V293_tick_saved_frame bs frame :=
  V293_owned_record_cell ((bs,0%Z),Tint32,Vint32 Int.zero) ** frame.

Section CallContext.
Variables (bindings:list(V293_tick_task*(taskstatus*val))) (idle:addrval) (message:val)
  (ct:tid) (es:EcbMod.map) (br bg bp bn bc bs bu bh:block) (run:nat) (frame:asrt).
Let tasks:=V293_tick_record_map false bindings idle message.
Let code:=V293_tick_post_hook_core_code bindings run.
Definition V293_tick_call_shared clock :=
  V293_tick_switch_view br bg bp bn ct tasks es clock **
  (V293_owned_record_cells(V293_tick_chain_missing bindings idle) **
   (V293_owned_record_cells(V293_tick_post_hook_core_globals bindings idle bu bh run) ** frame)).
Definition V293_tick_call_suffix clock :=
  V293_tick_scan_switch_pre bindings idle message ct es br bg bp bn bc bu bh run
    (V293_tick_saved_frame bs frame) clock Vundef.

Lemma V293_tick_call_pack : forall clock ir si ci,
  V293_owned_record_cell ((bs,0%Z),Tint32,Vint32 Int.zero) **
  (Amapsto(bc,0%Z)(Tptr V293_tcb_type)true Vundef **
   (<||code||> ** OS[ir,false,si,ci] ** V293_tick_call_shared clock)) ==>
  <||code||> ** OS[ir,false,si,ci] ** V293_tick_call_suffix clock.
Proof.
  intros clock ir si ci s H.
  unfold V293_tick_call_shared,V293_tick_call_suffix,V293_tick_scan_switch_pre,
    V293_tick_scan_supplement,V293_tick_saved_frame in *;clear -H;sep auto.
Qed.

(* The resource premise is evaluated in the FINAL callee environment. This
   does not transport arbitrary caller assertions or assume locals exist in M.
   The trace itself starts at the caller and allocates both fresh local cells. *)
Theorem V293_tick_call_shared_to_hook :
  forall P ks ge caller M ir si ci O clock tickfn ptcb rows group saved now running head hook,
  P tickfn=Some(V293_tick_function ptcb rows group saved now running head hook) ->
  ptcb<>saved -> fresh M bc -> fresh(allocb M bc 0%Z(typelen(Tptr V293_tcb_type)))bs ->
  (ge,V293_tick_locals ptcb saved bc bs,M,ir,(false,si,ci),O,code) |=
    <||code||> ** OS[ir,false,si,ci] ** V293_tick_call_shared clock ->
  exists Ms,
    V293_local_steps P (curs(scall tickfn nil),(kenil,ks))
      ((ge,caller,M),ir,(false,si,ci))
      (curs(scall hook nil),(kenil,
       kseq(V293_tick_post_hook ptcb rows group now running head)
        (kseq sret(kcall tickfn
         (sseq(V293_tick_body ptcb rows group saved now running head hook)sret)caller ks))))
      ((ge,V293_tick_locals ptcb saved bc bs,Ms),ir,(false,si,ci)) /\
    load(Tptr V293_tcb_type)Ms(bc,0%Z)=Some Vundef /\
    load Tint32 Ms(bs,0%Z)=Some(Vint32 Int.zero) /\
    (ge,V293_tick_locals ptcb saved bc bs,Ms,ir,(false,si,ci),O,code) |=
      <||code||> ** OS[ir,false,si,ci] ** V293_tick_call_suffix clock.
Proof.
  intros P ks ge caller M ir si ci O clock tickfn ptcb rows group saved now running head hook
    Program Different FreshScan FreshSaved Held.
  destruct(V293_tick_call_to_hook P ks ge caller M ir false si ci O code
    tickfn ptcb rows group saved now running head hook bc bs _
    Program Different FreshScan FreshSaved Held)as(Ms&Exec&Scan&Saved&Owned).
  exists Ms;split;[exact Exec| ];split;[exact Scan| ];split;[exact Saved| ].
  eapply V293_tick_call_pack;exact Owned.
Qed.

(* The saved CPU_SR slot allocated by the call is preserved by the original
   suffix. This is an InfRules contract, not an assumed hook return trace. *)
Theorem V293_tick_call_suffix_hoare : forall Spec sd li r ri tid
  clock ptcb rows group now running head ir si ci,
  NoAbs li -> (Int.unsigned(snd idle)+50<=Int.max_unsigned)%Z ->
  Forall V293_tick_binding_valid bindings -> NoDup(V293_tick_record_keys bindings idle) -> run<256 ->
  (forall st,st |= frame -> V293_tick_post_env ptcb rows group now running head bc br bg bn bu bh(getgenv st)(getlenv st)) ->
  ((CurTid ct ** frame) ==> CurLINV li tid) -> GoodFrm frame -> can_change_aop frame ->
  (gettopis si<=INUM)%nat -> (forall i,ir i=false) ->
  InfRules Spec sd li (V293_time_ready_inv br bg bp bn) r ri
    (<||code||> ** OS[ir,false,si,ci] ** V293_tick_call_suffix clock)
    (V293_tick_post_hook ptcb rows group now running head)
    (V293_tick_scan_switch_result bindings idle br bg bp bn bc bu bh run
      (V293_tick_saved_frame bs frame)Vundef ir si ci)tid.
Proof.
  intros Spec sd li r ri tid clock ptcb rows group now running head ir si ci
    NA Limit Valid Unique Run Env Inv Good Change Bound Clear.
  unfold V293_tick_call_suffix.
  apply V293_tick_scan_switch_hoare;try assumption.
  - intros st H;eapply V293_star_env_r;[exact Env|exact H].
  - intros st H.
    assert(K:st |= (CurTid ct ** frame) **
      V293_owned_record_cell((bs,0%Z),Tint32,Vint32 Int.zero)).
    { unfold V293_tick_saved_frame in H;clear -H;sep auto. }
    eapply V293_CurLINV_extend with(extra:=V293_owned_record_cell((bs,0%Z),Tint32,Vint32 Int.zero)).
    eapply astar_mono;[exact Inv|intros s Hs;exact Hs|exact K].
  - unfold V293_tick_saved_frame,V293_owned_record_cell;cbn[GoodFrm];repeat split;try exact Logic.I;exact Good.
  - unfold V293_tick_saved_frame,V293_owned_record_cell;cbn[can_change_aop];repeat split;try exact Logic.I;exact Change.
Qed.
End CallContext.
