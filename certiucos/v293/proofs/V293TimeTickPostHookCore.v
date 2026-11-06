(* The unchanged complete post-hook suffix over ONE canonical task/ready/clock
   resource. The caller already owns it: production IRQ borrowing is NOT proved. *)
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


Lemma V293_tick_post_payload_frame : forall br bg bp tasks,
  GoodFrm (V293_ready_payload br bg bp tasks).
Proof.
  intros;unfold V293_ready_payload;split;[apply V293_tick_records_frame| ].
  unfold V293_ready_owned;cbn [GoodFrm];intros lo hi entries.
  split;[exact Logic.I|apply V293_tick_cells_frame].
Qed.

Section PostHookCore.
Variables (bindings:list(V293_tick_task*(taskstatus*val))) (idle:addrval) (message:val)
  (ct:tid) (es:EcbMod.map) (br bg bp bn bc bu bh:block) (run:nat) (frame:asrt).
Let tasks:=V293_tick_record_map false bindings idle message.
Definition V293_tick_post_hook_core_globals : list V293_record_cell :=
  [((bu,0%Z),Tint8,V293_byteval run);
   ((bh,0%Z),Tptr V293_tcb_type,Vptr(V293_tick_head(map fst bindings)idle))].
Definition V293_tick_post_hook_core_frame :=
  V293_owned_record_cells V293_tick_post_hook_core_globals ** frame.
Definition V293_tick_post_hook_core_state abstract_clock physical_clock scan :=
  ((CurTid ct ** V293_shared_fields ct tasks es abstract_clock) **
    V293_ready_payload br bg bp tasks) **
  (PV(bn,Int.zero)@Tint32|->Vint32 physical_clock **
   (V293_owned_record_cell(V293_tick_pointer_cell bc scan) **
    (V293_owned_record_cells(V293_tick_chain_missing bindings idle) **
     V293_tick_post_hook_core_frame))).
Definition V293_tick_post_hook_core_pre clock scan :=
  V293_tick_post_hook_core_state clock clock scan.
Definition V293_tick_post_hook_core_tail :=
  if Nat.eqb run 1 then V293_tick_chain_code bindings else END None.
Definition V293_tick_post_hook_core_code :=
  spec_seq V293_tick_clock_action V293_tick_post_hook_core_tail.
Definition V293_tick_post_hook_core_result clock scan ir enabled si ci :=
  if Nat.eqb run 1 then
    EX actual:list(V293_tick_task*(taskstatus*val)),
      (<||END None||> ** OS[ir,enabled,si,ci] **
        V293_tick_while_core_post actual idle br bg bp bn bc V293_tick_post_hook_core_frame) **
      [|V293_tick_pend_choices bindings actual|]
  else <||END None||> ** OS[ir,enabled,si,ci] ** V293_tick_post_hook_core_pre clock scan.

Lemma V293_tick_post_hook_core_good : forall abstract_clock physical_clock scan,
  GoodFrm frame -> GoodFrm(V293_tick_post_hook_core_state abstract_clock physical_clock scan).
Proof.
  intros abstract_clock physical_clock scan GF.
  unfold V293_tick_post_hook_core_state,V293_tick_post_hook_core_frame.
  cbn [GoodFrm]. repeat split;try exact GF;try exact Logic.I;
    try apply V293_tick_records_frame;try apply V293_tick_cells_frame.
Qed.

Lemma V293_tick_post_hook_core_clock_close : forall sd clock scan tail extra,
  can_change_aop frame -> can_change_aop extra ->
  absinfer sd
    (<||spec_seq V293_tick_clock_action tail||> **
      (V293_tick_post_hook_core_state clock(Int.add clock Int.one)scan ** extra))
    (<||tail||> ** (V293_tick_post_hook_core_pre(Int.add clock Int.one)scan ** extra)).
Proof.
  intros sd clock scan tail extra Free ExtraFree.
  set(other:=(((CurTid ct **
    (Aabsdata curtid(oscurt ct) **
     (Aabsdata abstcblsid(abstcblist tasks) ** Aabsdata absecblsid(absecblist es)))) **
    V293_ready_payload br bg bp tasks) **
    (PV(bn,Int.zero)@Tint32|->Vint32(Int.add clock Int.one) **
      (V293_owned_record_cell(V293_tick_pointer_cell bc scan) **
       (V293_owned_record_cells(V293_tick_chain_missing bindings idle) ** V293_tick_post_hook_core_frame)))) ** extra).
  assert(OtherFree:can_change_aop other).
  { unfold other,V293_tick_post_hook_core_frame.
    cbn [can_change_aop]. repeat split;try exact Free;try exact ExtraFree;try exact Logic.I;
      try(apply V293_tick_update_change;apply V293_owned_cells_good);
      try(apply V293_tick_update_change;apply V293_task_list_good). }
  eapply absinfer_conseq with
    (p:=<||spec_seq V293_tick_clock_action tail||> ** (Aabsdata ostmid(ostm clock) ** other))
    (q:=<||tail||> ** (Aabsdata ostmid(ostm(Int.add clock Int.one)) ** other)).
  - unfold V293_tick_post_hook_core_pre,V293_tick_post_hook_core_state,V293_shared_fields,other.
    intros s H;sep auto.
  - eapply absinfer_trans with(q:=<||spec_seq(END None)tail||> **
      (Aabsdata ostmid(ostm(Int.add clock Int.one)) ** other)).
    + apply absinfer_seq;[split;[exact Logic.I|exact OtherFree]|split;[exact Logic.I|exact OtherFree]| ].
      apply V293_tick_clock_absinfer;exact OtherFree.
    + apply absinfer_seq_end;[split;[exact Logic.I|exact OtherFree]|split;[exact Logic.I|exact OtherFree]|intros st H;exact H].
  - unfold V293_tick_post_hook_core_state,V293_shared_fields,other.
    intros s H;sep auto.
Qed.

Lemma V293_tick_post_hook_core_clock_write : forall Spec sd li I r ri tid
  now clock scan extra tail,
  NoAbs li -> can_change_aop frame ->
  (forall st,st |= frame -> get(getlenv st)now=None /\ get(getgenv st)now=Some(bn,Tint32)) ->
  ((CurTid ct ** frame) ==> CurLINV li tid) -> can_change_aop extra ->
  InfRules Spec sd li I r ri
    (<||spec_seq V293_tick_clock_action tail||> ** extra ** V293_tick_post_hook_core_pre clock scan)
    (sassign(evar now)(ebinop oplus(evar now)(econst32 Int.one)))
    (<||tail||> ** extra ** V293_tick_post_hook_core_pre(Int.add clock Int.one)scan)tid.
Proof.
  intros Spec sd li I r ri tid now clock scan extra tail NA Free Env Inv ExtraFree.
  eapply abscsq_rule with
    (p:=<||spec_seq V293_tick_clock_action tail||> ** extra ** V293_tick_post_hook_core_pre clock scan)
    (q:=<||spec_seq V293_tick_clock_action tail||> ** extra **
      V293_tick_post_hook_core_state clock(Int.add clock Int.one)scan).
  - exact NA.
  - apply absinfer_eq.
  - eapply absinfer_conseq with
      (p:=<||spec_seq V293_tick_clock_action tail||> **
        (V293_tick_post_hook_core_state clock(Int.add clock Int.one)scan ** extra))
      (q:=<||tail||> ** (V293_tick_post_hook_core_pre(Int.add clock Int.one)scan ** extra)).
    + intros s H;sep auto.
    + apply V293_tick_post_hook_core_clock_close;assumption.
    + intros s H;sep auto.
  - set(R:=extra ** (((CurTid ct ** V293_shared_fields ct tasks es clock) **
      V293_ready_payload br bg bp tasks) **
      (V293_owned_record_cell(V293_tick_pointer_cell bc scan) **
       (V293_owned_record_cells(V293_tick_chain_missing bindings idle) ** V293_tick_post_hook_core_frame)))).
    eapply conseq_rule with
      (p:=<||spec_seq V293_tick_clock_action tail||> ** V293_rdy_raw_cells (((bn,0%Z),Tint32,Vint32 clock)::nil) R)
      (q:=<||spec_seq V293_tick_clock_action tail||> ** V293_rdy_raw_cells (((bn,0%Z),Tint32,Vint32(Int.add clock Int.one))::nil) R).
    + unfold V293_tick_post_hook_core_pre,V293_tick_post_hook_core_state,R.
      cbn [V293_rdy_raw_cells];intros s H;sep auto.
    + unfold V293_tick_post_hook_core_state,R.
      cbn [V293_rdy_raw_cells];intros s H;sep auto.
    + apply V293_tick_clock_assign_hoare with(before:=[])(after:=[]).
      * unfold R,V293_tick_post_hook_core_frame.
        intros st H;eapply V293_star_env_r;[ |exact H].
        intros st1 H1;eapply V293_star_env_r;[ |exact H1].
        intros st2 H2;eapply V293_star_env_r;[ |exact H2].
        intros st3 H3;eapply V293_star_env_r;[ |exact H3].
        intros st4 H4;eapply V293_star_env_r;[ |exact H4].
        exact Env.
      * unfold R,V293_tick_post_hook_core_frame.
        intros st H.
        assert(K:st |= (CurTid ct ** frame) ** Atrue) by(clear -H;sep auto).
        eapply V293_CurLINV_extend with(extra:=Atrue).
        eapply astar_mono;[exact Inv|intros s Hs;exact Hs|exact K].
Qed.

Lemma V293_tick_post_hook_core_guard : forall clock scan running extra,
  run<256 ->
  (forall st,st |= frame -> get(getlenv st)running=None /\ get(getgenv st)running=Some(bu,Tint8)) ->
  V293_tick_post_hook_core_pre clock scan ** extra ==>
    Rv(V293_tick_eq(ecast(evar running)Tint32)1)@Tint32 ==
      Vint32(if Nat.eqb run 1 then Int.one else Int.zero).
Proof.
  intros clock scan running extra Run Env.
  set(R:=(((CurTid ct ** V293_shared_fields ct tasks es clock) ** V293_ready_payload br bg bp tasks) **
    (PV(bn,Int.zero)@Tint32|->Vint32 clock **
     (V293_owned_record_cell(V293_tick_pointer_cell bc scan) **
      (V293_owned_record_cells(V293_tick_chain_missing bindings idle) **
       (V293_owned_record_cell((bh,0%Z),Tptr V293_tcb_type,Vptr(V293_tick_head(map fst bindings)idle)) ** frame))))) ** extra).
  intros st H.
  assert(Raw:st |= V293_rdy_raw_cells (((bu,0%Z),Tint8,V293_byteval run)::nil) R).
  { unfold V293_tick_post_hook_core_pre,V293_tick_post_hook_core_state,
      V293_tick_post_hook_core_frame,V293_tick_post_hook_core_globals in H.
    unfold R;cbn [V293_rdy_raw_cells V293_owned_record_cells V293_owned_record_cell] in H |- *.
    clear -H;sep auto. }
  eapply V293_tick_running_guard_owned with(cells:=(((bu,0%Z),Tint8,V293_byteval run)::nil))(R:=R)(bu:=bu);
    [left;reflexivity|exact Run| |exact Raw].
  unfold R;intros st00 H00.
  eapply V293_star_env_l;[ |exact H00]. intros st0 H0.
  eapply V293_star_env_r;[ |exact H0]. intros st1 H1.
  eapply V293_star_env_r;[ |exact H1]. intros st2 H2.
  eapply V293_star_env_r;[ |exact H2]. intros st3 H3.
  eapply V293_star_env_r;[ |exact H3]. intros st4 H4.
  eapply V293_star_env_r;[ |exact H4]. exact Env.
Qed.

Lemma V293_tick_post_hook_core_head : forall Spec sd li I r ri tid aop
  clock scan extra ptcb head,
  (forall st,st |= frame -> get(getlenv st)ptcb=Some(bc,Tptr V293_tcb_type) /\
    get(getlenv st)head=None /\ get(getgenv st)head=Some(bh,Tptr V293_tcb_type)) ->
  ((CurTid ct ** frame) ==> CurLINV li tid) ->
  InfRules Spec sd li I r ri
    (<||aop||> ** extra ** V293_tick_post_hook_core_pre clock scan)
    (sassign(evar ptcb)(evar head))
    (<||aop||> ** extra ** V293_tick_chain_core_pre bindings idle message ct es clock
      br bg bp bn bc V293_tick_post_hook_core_frame)tid.
Proof.
  intros Spec sd li I r ri tid aop clock scan extra ptcb head Env Inv.
  set(R:=extra ** (((CurTid ct ** V293_shared_fields ct tasks es clock) ** V293_ready_payload br bg bp tasks) **
    (PV(bn,Int.zero)@Tint32|->Vint32 clock **
     (V293_owned_record_cells(V293_tick_chain_missing bindings idle) **
      (V293_owned_record_cell((bu,0%Z),Tint8,V293_byteval run) ** frame))))).
  set(headcell:=((bh,0%Z),Tptr V293_tcb_type,Vptr(V293_tick_head(map fst bindings)idle))).
  eapply conseq_rule with
    (p:=<||aop||> ** V293_rdy_raw_cells(V293_tick_pointer_cell bc scan::headcell::nil) R)
    (q:=<||aop||> ** V293_rdy_raw_cells(V293_tick_pointer_cell bc(V293_tick_head(map fst bindings)idle)::headcell::nil) R).
  - unfold V293_tick_post_hook_core_pre,V293_tick_post_hook_core_state,
      V293_tick_post_hook_core_frame,V293_tick_post_hook_core_globals,R,headcell.
    cbn [V293_owned_record_cells V293_owned_record_cell V293_tick_pointer_cell V293_rdy_raw_cells].
    intros s H;clear -H;sep auto.
  - unfold V293_tick_chain_core_pre,V293_tick_post_hook_core_frame,V293_tick_post_hook_core_globals,R,headcell.
    cbn [V293_owned_record_cells V293_owned_record_cell V293_tick_pointer_cell V293_rdy_raw_cells].
    intros s H;clear -H;sep auto.
  - apply V293_tick_head_assign_hoare with(prefix:=[])(rest:=headcell::nil)(scan:=scan)(bh:=bh).
    + left;reflexivity.
    + unfold R;intros st H.
      eapply V293_star_env_r;[ |exact H]. intros st1 H1.
      eapply V293_star_env_r;[ |exact H1]. intros st2 H2.
      eapply V293_star_env_r;[ |exact H2]. intros st3 H3.
      eapply V293_star_env_r;[ |exact H3]. intros st4 H4.
      eapply V293_star_env_r;[ |exact H4]. exact Env.
    + unfold R;intros st H.
      assert(K:st |= (CurTid ct ** frame) ** Atrue) by(clear -H;sep auto).
      eapply V293_CurLINV_extend with(extra:=Atrue).
      eapply astar_mono;[exact Inv|intros s Hs;exact Hs|exact K].
Qed.

Theorem V293_tick_post_hook_core_branch : forall Spec sd li I r ri tid
  clock scan ptcb rows group now running head enabled ir si ci,
  NoAbs li -> (Int.unsigned(snd idle)+50<=Int.max_unsigned)%Z ->
  Forall V293_tick_binding_valid bindings -> NoDup(V293_tick_record_keys bindings idle) -> run<256 ->
  (forall st,st |= frame -> V293_tick_post_env ptcb rows group now running head bc br bg bn bu bh(getgenv st)(getlenv st)) ->
  ((CurTid ct ** frame) ==> CurLINV li tid) -> GoodFrm frame -> can_change_aop frame ->
  (gettopis si<=INUM)%nat ->
  InfRules Spec sd li I r ri
    (<||V293_tick_post_hook_core_tail||> ** OS[ir,enabled,si,ci] ** V293_tick_post_hook_core_pre clock scan)
    (sifthen(V293_tick_eq(ecast(evar running)Tint32)1)
      (sseq(sassign(evar ptcb)(evar head))(swhile(V293_tick_guard ptcb)(V293_tick_iteration ptcb rows group))))
    (V293_tick_post_hook_core_result clock scan ir enabled si ci)tid.
Proof.
  intros Spec sd li I r ri tid clock scan ptcb rows group now running head enabled ir si ci
    NA IdleLimit Valid Unique Run Env Inv GF Free Bound.
  eapply V293_tick_known_ift_hoare with(flag:=Nat.eqb run 1).
  - intros st H.
    assert(Core:st |= V293_tick_post_hook_core_pre clock scan **
      (<||V293_tick_post_hook_core_tail||> ** OS[ir,enabled,si,ci]))by(clear -H;sep auto).
    eapply V293_tick_post_hook_core_guard;[exact Run| |exact Core].
    intros st0 H0;exact(proj1(proj2(proj2(Env st0 H0)))).
  - destruct(Nat.eqb run 1)eqn:Running.
    + unfold V293_tick_post_hook_core_tail,V293_tick_post_hook_core_result;rewrite Running.
      eapply seq_rule.
      * apply V293_tick_post_hook_core_head.
        -- intros st H. destruct(Env st H)as[Delay[Clock[RunningEnv Head]]].
           split;[exact(proj1 Delay)|exact Head].
        -- exact Inv.
      * apply V293_tick_chain_core_hoare;try assumption.
        -- unfold V293_tick_post_hook_core_frame.
           intros st H;eapply V293_star_env_r;[ |exact H].
           intros st0 H0;exact(proj1(Env st0 H0)).
        -- unfold V293_tick_post_hook_core_frame.
           intros st H;assert(K:st |= (CurTid ct ** frame) ** Atrue)by(clear -H;sep auto).
           eapply V293_CurLINV_extend with(extra:=Atrue).
           eapply astar_mono;[exact Inv|intros s Hs;exact Hs|exact K].
        -- unfold V293_tick_post_hook_core_frame;split;[apply V293_tick_cells_frame|exact GF].
        -- unfold V293_tick_post_hook_core_frame;split;
             [apply V293_tick_update_change;apply V293_owned_cells_good|exact Free].
    + unfold V293_tick_post_hook_core_tail,V293_tick_post_hook_core_result;rewrite Running.
      intros st H;exact H.
Qed.

Lemma V293_tick_post_hook_borrow_change : forall IV low high,
  can_change_aop(invlth_isr IV low high).
Proof.
  intros IV low high;unfold invlth_isr.
  generalize (high-low);intro n;revert low.
  induction n as[ |n IH];intro first;cbn [starinv_isr can_change_aop].
  - intro ir;repeat split;try exact Logic.I.
    apply V293_tick_update_change;apply invp.
  - split;[ |apply IH]. intro ir;repeat split;try exact Logic.I.
    apply V293_tick_update_change;apply invp.
Qed.

Theorem V293_tick_post_hook_core_hoare : forall Spec sd li I r ri tid
  clock scan ptcb rows group now running head enabled ir si ci,
  NoAbs li -> (Int.unsigned(snd idle)+50<=Int.max_unsigned)%Z ->
  Forall V293_tick_binding_valid bindings -> NoDup(V293_tick_record_keys bindings idle) -> run<256 ->
  (forall st,st |= frame -> V293_tick_post_env ptcb rows group now running head bc br bg bn bu bh(getgenv st)(getlenv st)) ->
  ((CurTid ct ** frame) ==> CurLINV li tid) -> GoodFrm frame -> can_change_aop frame ->
  (gettopis si<=INUM)%nat ->
  InfRules Spec sd li I r ri
    (<||V293_tick_post_hook_core_code||> ** OS[ir,enabled,si,ci] ** V293_tick_post_hook_core_pre clock scan)
    (V293_tick_post_hook ptcb rows group now running head)
    (V293_tick_post_hook_core_result(Int.add clock Int.one)scan ir enabled si ci)tid.
Proof.
  intros Spec sd li I r ri tid clock scan ptcb rows group now running head enabled ir si ci
    NA IdleLimit Valid Unique Run Env Inv GF Free Bound.
  set(P:=V293_tick_post_hook_core_pre clock scan).
  set(Q:=V293_tick_post_hook_core_pre(Int.add clock Int.one)scan).
  set(branch:=sifthen(V293_tick_eq(ecast(evar running)Tint32)1)
    (sseq(sassign(evar ptcb)(evar head))(swhile(V293_tick_guard ptcb)(V293_tick_iteration ptcb rows group)))).
  set(target:=V293_tick_post_hook_core_result(Int.add clock Int.one)scan ir enabled si ci).
  assert(GP:GoodFrm P)by(apply V293_tick_post_hook_core_good;exact GF).
  assert(GQ:GoodFrm Q)by(apply V293_tick_post_hook_core_good;exact GF).
  assert(IQ:Q ==> CurLINV li tid).
  { unfold Q,V293_tick_post_hook_core_pre,V293_tick_post_hook_core_state,V293_tick_post_hook_core_frame.
    intros st H;assert(K:st |= (CurTid ct ** frame) ** Atrue)by(clear -H;sep auto).
    eapply V293_CurLINV_extend with(extra:=Atrue).
    eapply astar_mono;[exact Inv|intros s Hs;exact Hs|exact K]. }
  assert(Branch:InfRules Spec sd li I r ri
    (<||V293_tick_post_hook_core_tail||> ** OS[ir,enabled,si,ci] ** Q)branch target tid).
  { apply V293_tick_post_hook_core_branch with(now:=now);assumption. }
  assert(Work:forall extra tail out,can_change_aop extra ->
    InfRules Spec sd li I r ri(<||V293_tick_post_hook_core_tail||> ** extra ** Q)tail out tid ->
    InfRules Spec sd li I r ri(<||V293_tick_post_hook_core_code||> ** extra ** P)
      (sseq(sassign(evar now)(ebinop oplus(evar now)(econst32 Int.one)))tail)out tid).
  { intros extra tail out ExtraFree Tail.
    eapply seq_rule with(p':=<||V293_tick_post_hook_core_tail||> ** extra ** Q);[ |exact Tail].
    apply V293_tick_post_hook_core_clock_write;try assumption.
    intros st H;exact(proj1(proj2(Env st H))). }
  change(InfRules Spec sd li I r ri(<||V293_tick_post_hook_core_code||> ** OS[ir,enabled,si,ci] ** P)
    (sseq(sprim encrit)(sseq(sassign(evar now)(ebinop oplus(evar now)(econst32 Int.one)))
      (sseq(sprim excrit)branch)))target tid).
  destruct enabled.
  - eapply seq_rule.
    + eapply conseq_rule with
        (p:=<||V293_tick_post_hook_core_code||> ** OS[ir,true,si,ci] ** ATopis(gettopis si) **
          [|(gettopis si<=INUM)%nat|] ** P)
        (q:=<||V293_tick_post_hook_core_code||> ** OS[ir,false,si,true::ci] ** invlth_isr I 0(gettopis si) ** P).
      * intros st H;assert(IS:st |= Ais si ** Atrue)by(sep auto).
        pose proof(V293_time_topis si Atrue st IS)as Top.
        apply astar_l_atopis_elim in Top;destruct Top as[Top _].
        pose proof(@astar_l_atopis_intro st(gettopis si)_ H Top)as HT.
        clear H;rename HT into H;sep auto.
      * intros st H;exact H.
      * apply encrit1_rule;exact GP.
    + eapply conseq_rule with
        (p:=<||V293_tick_post_hook_core_code||> ** (OS[ir,false,si,true::ci] ** invlth_isr I 0(gettopis si)) ** P)
        (q:=target);[ |intros st H;exact H|apply Work].
      * intros st H;sep auto.
      * split;[repeat split;exact Logic.I|apply V293_tick_post_hook_borrow_change].
      * eapply seq_rule with(p':=<||V293_tick_post_hook_core_tail||> ** OS[ir,true,si,ci] ** Q);[ |exact Branch].
        eapply conseq_rule with
          (p:=<||V293_tick_post_hook_core_tail||> ** OS[ir,false,si,true::ci] ** ATopis(gettopis si) **
            invlth_isr I 0(gettopis si) ** Q)
          (q:=<||V293_tick_post_hook_core_tail||> ** OS[ir,true,si,ci] ** Q).
        -- intros st H;assert(IS:st |= Ais si ** Atrue)by(sep auto).
           pose proof(V293_time_topis si Atrue st IS)as Top.
           apply astar_l_atopis_elim in Top;destruct Top as[Top _].
           pose proof(@astar_l_atopis_intro st(gettopis si)_ H Top)as HT.
           clear H;rename HT into H;sep auto.
        -- intros st H;exact H.
        -- apply excrit1_rule;assumption.
  - eapply seq_rule;[apply encrit2_rule;exact GP| ].
    apply Work;[repeat split;exact Logic.I| ].
    eapply seq_rule;[apply excrit2_rule;exact GQ|exact Branch].
Qed.

Theorem V293_tick_post_hook_core_semantics : forall Spec sd li I r ri tid
  clock scan ptcb rows group now running head enabled ir si ci,
  NoAbs li -> (Int.unsigned(snd idle)+50<=Int.max_unsigned)%Z ->
  Forall V293_tick_binding_valid bindings -> NoDup(V293_tick_record_keys bindings idle) -> run<256 ->
  (forall st,st |= frame -> V293_tick_post_env ptcb rows group now running head bc br bg bn bu bh(getgenv st)(getlenv st)) ->
  ((CurTid ct ** frame) ==> CurLINV li tid) -> GoodFrm frame -> can_change_aop frame ->
  (gettopis si<=INUM)%nat ->
  simulation.RuleSem Spec sd li I r ri
    (<||V293_tick_post_hook_core_code||> ** OS[ir,enabled,si,ci] ** V293_tick_post_hook_core_pre clock scan)
    (V293_tick_post_hook ptcb rows group now running head)
    (V293_tick_post_hook_core_result(Int.add clock Int.one)scan ir enabled si ci)tid.
Proof. intros;apply RuleSound;apply V293_tick_post_hook_core_hoare;assumption. Qed.
End PostHookCore.
