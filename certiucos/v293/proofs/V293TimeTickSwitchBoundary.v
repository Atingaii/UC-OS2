(* Close the original post-hook through the EXISTING shared time/ready SWINV.
   SWINV fixes IE=false and clear ISR flags; no enabled IRQ acquisition,
   production ISR installation, new Inv or initialized reachability is claimed. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickPostHookCore.
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
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.soundness.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import Coq.Lists.List Coq.Sorting.Permutation Lia.
Import ListNotations.
Local Open Scope nat_scope.

(* Additive conjunction observes the SAME abstract map, not another owned copy. *)
Definition V293_tick_switch_view br bg bp bn ct tasks es clock :=
  SWINV(V293_time_ready_inv br bg bp bn) //\\
    (V293_shared_fields ct tasks es clock ** Atrue).

Lemma V293_tick_switch_open : forall br bg bp bn ct tasks es clock,
  V293_tick_switch_view br bg bp bn ct tasks es clock ==>
  V293_shared_flags **
    (((CurTid ct ** V293_shared_fields ct tasks es clock) **
       V293_ready_payload br bg bp tasks) ** PV(bn,Int.zero)@Tint32|->Vint32 clock).
Proof.
  intros br bg bp bn ct tasks es clock s [Held View].
  apply V293_time_ready_switch_open in Held.
  unfold V293_time_ready_switch_core in Held;sep normal in Held;sep destruct Held.
  assert(Actual:get(getabst s)curtid=Some(oscurt x) /\
    get(getabst s)abstcblsid=Some(abstcblist x0) /\
    get(getabst s)absecblsid=Some(absecblist x1) /\
    get(getabst s)ostmid=Some(ostm x2)).
  { eapply V293_shared_fields_core_get.
    unfold V293_time_ready_switch_fields in Held;clear View;sep auto. }
  assert(Expected:get(getabst s)curtid=Some(oscurt ct) /\
    get(getabst s)abstcblsid=Some(abstcblist tasks) /\
    get(getabst s)absecblsid=Some(absecblist es) /\
    get(getabst s)ostmid=Some(ostm clock)).
  { repeat split; (eapply V293_star_abst_get_l; [ |exact View]);
      intros st H;destruct(V293_shared_fields_get _ _ _ _ st H)as[Hc[Ht[He Hn]]];assumption. }
  destruct Actual as[A[B[C D]]];destruct Expected as[E[F[G H]]].
  assert(x=ct /\ x0=tasks /\ x1=es /\ x2=clock)by(repeat split;congruence).
  destruct H0 as[Same[Same0[Same1 Same2]]];subst x x0 x1 x2.
  unfold V293_time_ready_switch_fields in Held;clear -Held;sep auto.
Qed.

(* Flags own empty resources. Rebuild them from the returned OS state instead
   of illegally putting Aie/Aisr/ATopis inside a GoodFrm. *)
Lemma V293_tick_switch_flags : forall ir si ci R,
  (forall i,ir i=false) ->
  OS[ir,false,si,ci] ** R ==> V293_shared_flags ** (OS[ir,false,si,ci] ** R).
Proof.
  intros ir si ci R Clear s Held.
  assert(Is:s |= Ais si ** Atrue)by(clear -Held;sep auto).
  pose proof(V293_time_topis si Atrue s Is)as Top.
  apply astar_l_atopis_elim in Top;destruct Top as[Top _].
  apply astar_l_atopis_intro with(i:=gettopis si)in Held;[ |exact Top].
  assert(IE:getie(gettaskst s)=false).
  { assert(K:s |= Aie false ** Atrue)by(clear -Held;sep auto).
    exact(proj1(astar_l_aie_elim K)). }
  assert(ISR:getisr(gettaskst s)=ir).
  { assert(K:s |= Aisr ir ** Atrue)by(clear -Held;sep auto).
    exact(proj1(astar_l_aisr_elim K)). }
  apply astar_l_aie_intro with(i:=false)in Held;[ |exact IE].
  apply astar_l_aisr_intro with(i:=ir)in Held;[ |exact ISR].
  assert(Clr:Aisr ir ==> isrclr).
  { intros st H;unfold isrclr;exists ir;split;[exact H| ].
    destruct st as[[[[[[g l]m]r]aux]O]op];cbn in *;tauto. }
  eapply astar_mono in Held;[ |exact Clr|intros st H;exact H].
  unfold V293_shared_flags;clear -Held;sep auto.
Qed.

Lemma V293_tick_switch_close : forall br bg bp bn ir si ci R,
  (forall i,ir i=false) ->
  OS[ir,false,si,ci] ** (V293_time_ready_core br bg bp bn ** R) ==>
  OS[ir,false,si,ci] ** (SWINV(V293_time_ready_inv br bg bp bn) ** R).
Proof.
  intros br bg bp bn ir si ci R Clear s Held.
  apply V293_tick_switch_flags in Held;[ |exact Clear].
  assert(Core:s |= (V293_shared_flags ** V293_time_ready_switch_core br bg bp bn) **
    (OS[ir,false,si,ci] ** R)).
  { unfold V293_time_ready_switch_core,V293_time_ready_switch_fields,
      V293_time_ready_core,V293_time_ready_fields in Held |- *;clear -Held;sep auto. }
  eapply astar_mono in Core;[ |apply V293_time_ready_switch_close|intros st H;exact H].
  clear -Core;sep auto.
Qed.

Section TickSwitchBoundary.
Variables (bindings:list(V293_tick_task*(taskstatus*val))) (idle:addrval) (message:val)
  (ct:tid) (es:EcbMod.map) (br bg bp bn bc bu bh:block) (run:nat) (frame:asrt).
Let tasks:=V293_tick_record_map false bindings idle message.
Let globals:=V293_tick_post_hook_core_globals bindings idle bu bh run.
Let coreframe:=V293_tick_post_hook_core_frame bindings idle bu bh run frame.
Let corepre:=V293_tick_post_hook_core_pre bindings idle message ct es br bg bp bn bc bu bh run frame.
Let coreresult:=V293_tick_post_hook_core_result bindings idle message ct es br bg bp bn bc bu bh run frame.

Definition V293_tick_switch_supplement scan :=
  V293_owned_record_cell(V293_tick_pointer_cell bc scan) **
  (V293_owned_record_cells(V293_tick_chain_missing bindings idle) **
   (V293_owned_record_cells globals ** frame)).
Definition V293_tick_switch_pre clock scan :=
  V293_tick_switch_view br bg bp bn ct tasks es clock ** V293_tick_switch_supplement scan.
Definition V293_tick_switch_result scan ir si ci :=
  if Nat.eqb run 1 then
    EX actual:list(V293_tick_task*(taskstatus*val)),
      (<||END None||> ** OS[ir,false,si,ci] **
       (SWINV(V293_time_ready_inv br bg bp bn) **
        (V293_owned_record_cell(V293_tick_pointer_cell bc idle) **
         (V293_owned_record_cells(V293_tick_chain_residual actual idle) ** coreframe)))) **
      [|V293_tick_pend_choices bindings actual|]
  else <||END None||> ** OS[ir,false,si,ci] **
    (SWINV(V293_time_ready_inv br bg bp bn) ** V293_tick_switch_supplement scan).

Lemma V293_tick_switch_entry : forall clock scan ir si ci aop,
  <||aop||> ** OS[ir,false,si,ci] ** V293_tick_switch_pre clock scan ==>
  <||aop||> ** OS[ir,false,si,ci] ** corepre clock scan.
Proof.
  intros clock scan ir si ci aop s Held.
  assert(Open:s |=
    (V293_shared_flags ** (((CurTid ct ** V293_shared_fields ct tasks es clock) **
       V293_ready_payload br bg bp tasks) ** PV(bn,Int.zero)@Tint32|->Vint32 clock)) **
    (V293_tick_switch_supplement scan ** (<||aop||> ** OS[ir,false,si,ci]))).
  { eapply astar_mono;[apply V293_tick_switch_open|intros st H;exact H| ].
    unfold V293_tick_switch_pre in Held;clear -Held;sep auto. }
  unfold corepre,V293_tick_post_hook_core_pre,V293_tick_post_hook_core_state,
    V293_tick_switch_supplement,V293_tick_post_hook_core_frame,coreframe,globals,
    V293_shared_flags,tasks,isrclr in *.
  clear Held;sep normal in Open;sep destruct Open.
  (* Modal flags can be discarded; no physical or abstract resource is lost. *)
  sep auto.
  destruct Open as[Open _];sep auto.
Qed.

Lemma V293_tick_switch_return : forall clock scan ir si ci,
  (forall i,ir i=false) ->
  coreresult clock scan ir false si ci ==> V293_tick_switch_result scan ir si ci.
Proof.
  intros clock scan ir si ci Clear s Held.
  unfold coreresult,V293_tick_post_hook_core_result,V293_tick_switch_result in *.
  destruct(Nat.eqb run 1)eqn:Running.
  - sep normal in Held;sep destruct Held.
    unfold V293_tick_while_core_post in Held.
    assert(Closed:s |=
      (OS[ir,false,si,ci] ** (SWINV(V293_time_ready_inv br bg bp bn) **
       (V293_owned_record_cell(V293_tick_pointer_cell bc idle) **
        (V293_owned_record_cells(V293_tick_chain_residual x idle) ** coreframe)))) **
      (<||END None||> ** [|V293_tick_pend_choices bindings x|])).
    { eapply astar_mono;[apply V293_tick_switch_close;exact Clear|intros st H;exact H| ].
      unfold coreframe;clear -Held;sep auto. }
    exists x;clear -Closed;sep auto.
  - assert(Core:s |= OS[ir,false,si,ci] **
      (V293_time_ready_core br bg bp bn ** (V293_tick_switch_supplement scan ** <||END None||>))).
    { unfold corepre,V293_tick_post_hook_core_pre,V293_tick_post_hook_core_state,
        V293_tick_post_hook_core_frame,V293_tick_switch_supplement,globals,
        V293_time_ready_core,V293_time_ready_fields in Held |- *.
      clear -Held;sep auto. }
    apply V293_tick_switch_close in Core;[ |exact Clear]. clear -Core;sep auto.
Qed.

Theorem V293_tick_post_hook_switch_hoare : forall Spec sd li r ri tid
  clock scan ptcb rows group now running head ir si ci,
  NoAbs li -> (Int.unsigned(snd idle)+50<=Int.max_unsigned)%Z ->
  Forall V293_tick_binding_valid bindings -> NoDup(V293_tick_record_keys bindings idle) -> run<256 ->
  (forall st,st |= frame -> V293_tick_post_env ptcb rows group now running head bc br bg bn bu bh(getgenv st)(getlenv st)) ->
  ((CurTid ct ** frame) ==> CurLINV li tid) -> GoodFrm frame -> can_change_aop frame ->
  (gettopis si<=INUM)%nat -> (forall i,ir i=false) ->
  InfRules Spec sd li (V293_time_ready_inv br bg bp bn) r ri
    (<||V293_tick_post_hook_core_code bindings run||> ** OS[ir,false,si,ci] ** V293_tick_switch_pre clock scan)
    (V293_tick_post_hook ptcb rows group now running head)
    (V293_tick_switch_result scan ir si ci)tid.
Proof.
  intros Spec sd li r ri tid clock scan ptcb rows group now running head ir si ci
    NA IdleLimit Valid Unique Run Env Inv GF Free Bound Clear.
  eapply conseq_rule with
    (p:=<||V293_tick_post_hook_core_code bindings run||> ** OS[ir,false,si,ci] ** corepre clock scan)
    (q:=coreresult(Int.add clock Int.one)scan ir false si ci).
  - apply V293_tick_switch_entry.
  - apply V293_tick_switch_return;exact Clear.
  - apply V293_tick_post_hook_core_hoare;assumption.
Qed.

Theorem V293_tick_post_hook_switch_semantics : forall Spec sd li r ri tid
  clock scan ptcb rows group now running head ir si ci,
  NoAbs li -> (Int.unsigned(snd idle)+50<=Int.max_unsigned)%Z ->
  Forall V293_tick_binding_valid bindings -> NoDup(V293_tick_record_keys bindings idle) -> run<256 ->
  (forall st,st |= frame -> V293_tick_post_env ptcb rows group now running head bc br bg bn bu bh(getgenv st)(getlenv st)) ->
  ((CurTid ct ** frame) ==> CurLINV li tid) -> GoodFrm frame -> can_change_aop frame ->
  (gettopis si<=INUM)%nat -> (forall i,ir i=false) ->
  simulation.RuleSem Spec sd li (V293_time_ready_inv br bg bp bn) r ri
    (<||V293_tick_post_hook_core_code bindings run||> ** OS[ir,false,si,ci] ** V293_tick_switch_pre clock scan)
    (V293_tick_post_hook ptcb rows group now running head)
    (V293_tick_switch_result scan ir si ci)tid.
Proof. intros;apply RuleSound;apply V293_tick_post_hook_switch_hoare;assumption. Qed.
End TickSwitchBoundary.
