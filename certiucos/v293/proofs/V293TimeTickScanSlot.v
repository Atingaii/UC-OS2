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
(* Safe overwrite: initial pointer storage need NOT contain a typed value.
   Neither the assignment rule nor this proof reads the old scan slot. *)
Lemma V293_tick_scan_head_store : forall Spec sd li I r ri tid aop R prefix rest ptcb head bc bh initial first,
 In ((bh,0%Z),Tptr V293_tcb_type,Vptr first) (prefix++rest) ->
 (forall st,st |= R -> get(getlenv st)ptcb=Some(bc,Tptr V293_tcb_type) /\
   get(getlenv st)head=None /\ get(getgenv st)head=Some(bh,Tptr V293_tcb_type)) ->
 (R ==> CurLINV li tid) ->
 InfRules Spec sd li I r ri
 (<||aop||> ** V293_rdy_raw_cells(prefix++((bc,0%Z),Tptr V293_tcb_type,initial)::rest)R)
 (sassign(evar ptcb)(evar head))
 (<||aop||> ** V293_rdy_raw_cells(prefix++V293_tick_pointer_cell bc first::rest)R)tid.
Proof.
 intros Spec sd li I r ri tid aop R prefix rest ptcb head bc bh initial first Member Env Inv.
 unfold V293_tick_pointer_cell.
 eapply V293_raw_assign_hoare with(rt:=Tptr V293_tcb_type);
 [reflexivity|apply eq_vptr;exists V293_tcb_type;exists V293_tcb_type;auto| |exact Inv].
 intros st Held;destruct st as[[[[[[ge le]M]ir]aux]O]op].
 pose proof(V293_raw_cells_frame_env _ R
   (fun ge le=>get le ptcb=Some(bc,Tptr V293_tcb_type) /\ get le head=None /\ get ge head=Some(bh,Tptr V293_tcb_type))Env _ Held)as Bindings.
 change(get le ptcb=Some(bc,Tptr V293_tcb_type) /\ get le head=None /\ get ge head=Some(bh,Tptr V293_tcb_type))in Bindings.
 destruct Bindings as[B[N H]].
 assert(Read:load(Tptr V293_tcb_type)M(bh,0%Z)=Some(Vptr first)).
 { eapply(V293_rdy_raw_load (prefix++((bc,0%Z),Tptr V293_tcb_type,initial)::rest) R (bh,0%Z)(Tptr V293_tcb_type)(Vptr first)(ge,le,M,ir,aux,O,op));
   [apply in_app_or in Member;apply in_or_app;destruct Member;[left|right;right];assumption|reflexivity|exact Held]. }
 cbn[sat getsmem get_smem evaltype evaladdr get_lenv get_genv];rewrite B,N,H.
 repeat split;try reflexivity;try discriminate.
 cbn[evalval evaltype get_lenv get_genv get_mem];rewrite N,H;exact Read.
Qed.

Section ScanSlot.
Variables (bindings:list(V293_tick_task*(taskstatus*val))) (idle:addrval) (message:val)
  (ct:tid) (es:EcbMod.map) (br bg bp bn bc bu bh:block) (run:nat) (frame:asrt).
Let tasks:=V293_tick_record_map false bindings idle message.
Let globals:=V293_tick_post_hook_core_globals bindings idle bu bh run.
Let coreframe:=V293_tick_post_hook_core_frame bindings idle bu bh run frame.
Definition V293_tick_scan_state abstract_clock physical_clock scan :=
  ((CurTid ct ** V293_shared_fields ct tasks es abstract_clock) **
    V293_ready_payload br bg bp tasks) **
  (PV(bn,Int.zero)@Tint32|->Vint32 physical_clock **
   (Amapsto(bc,0%Z)(Tptr V293_tcb_type)true scan **
    (V293_owned_record_cells(V293_tick_chain_missing bindings idle) **
     coreframe))).
Definition V293_tick_scan_pre clock scan :=
  V293_tick_scan_state clock clock scan.
Let tailcode:=V293_tick_post_hook_core_tail bindings run.
Let code:=V293_tick_post_hook_core_code bindings run.
Definition V293_tick_scan_result clock scan ir enabled si ci :=
  if Nat.eqb run 1 then
    EX actual:list(V293_tick_task*(taskstatus*val)),
      (<||END None||> ** OS[ir,enabled,si,ci] **
        V293_tick_while_core_post actual idle br bg bp bn bc coreframe) **
      [|V293_tick_pend_choices bindings actual|]
  else <||END None||> ** OS[ir,enabled,si,ci] ** V293_tick_scan_pre clock scan.

Lemma V293_tick_scan_good : forall abstract_clock physical_clock scan,
  GoodFrm frame -> GoodFrm(V293_tick_scan_state abstract_clock physical_clock scan).
Proof.
  intros abstract_clock physical_clock scan GF.
  unfold V293_tick_scan_state,coreframe,V293_tick_post_hook_core_frame.
  cbn [GoodFrm]. repeat split;try exact GF;try exact Logic.I;
    try apply V293_tick_records_frame;try apply V293_tick_cells_frame.
Qed.

Lemma V293_tick_scan_clock_close : forall sd clock scan tail extra,
  can_change_aop frame -> can_change_aop extra ->
  absinfer sd
    (<||spec_seq V293_tick_clock_action tail||> **
      (V293_tick_scan_state clock(Int.add clock Int.one)scan ** extra))
    (<||tail||> ** (V293_tick_scan_pre(Int.add clock Int.one)scan ** extra)).
Proof.
  intros sd clock scan tail extra Free ExtraFree.
  set(other:=(((CurTid ct **
    (Aabsdata curtid(oscurt ct) **
     (Aabsdata abstcblsid(abstcblist tasks) ** Aabsdata absecblsid(absecblist es)))) **
    V293_ready_payload br bg bp tasks) **
    (PV(bn,Int.zero)@Tint32|->Vint32(Int.add clock Int.one) **
      (Amapsto(bc,0%Z)(Tptr V293_tcb_type)true scan **
       (V293_owned_record_cells(V293_tick_chain_missing bindings idle) ** coreframe)))) ** extra).
  assert(OtherFree:can_change_aop other).
  { unfold other,coreframe,V293_tick_post_hook_core_frame.
    cbn [can_change_aop]. repeat split;try exact Free;try exact ExtraFree;try exact Logic.I;
      try(apply V293_tick_update_change;apply V293_owned_cells_good);
      try(apply V293_tick_update_change;apply V293_task_list_good). }
  eapply absinfer_conseq with
    (p:=<||spec_seq V293_tick_clock_action tail||> ** (Aabsdata ostmid(ostm clock) ** other))
    (q:=<||tail||> ** (Aabsdata ostmid(ostm(Int.add clock Int.one)) ** other)).
  - unfold V293_tick_scan_pre,V293_tick_scan_state,V293_shared_fields,other.
    intros s H;sep auto.
  - eapply absinfer_trans with(q:=<||spec_seq(END None)tail||> **
      (Aabsdata ostmid(ostm(Int.add clock Int.one)) ** other)).
    + apply absinfer_seq;[split;[exact Logic.I|exact OtherFree]|split;[exact Logic.I|exact OtherFree]| ].
      apply V293_tick_clock_absinfer;exact OtherFree.
    + apply absinfer_seq_end;[split;[exact Logic.I|exact OtherFree]|split;[exact Logic.I|exact OtherFree]|intros st H;exact H].
  - unfold V293_tick_scan_state,V293_shared_fields,other.
    intros s H;sep auto.
Qed.

Lemma V293_tick_scan_clock_write : forall Spec sd li I r ri tid
  now clock scan extra tail,
  NoAbs li -> can_change_aop frame ->
  (forall st,st |= frame -> get(getlenv st)now=None /\ get(getgenv st)now=Some(bn,Tint32)) ->
  ((CurTid ct ** frame) ==> CurLINV li tid) -> can_change_aop extra ->
  InfRules Spec sd li I r ri
    (<||spec_seq V293_tick_clock_action tail||> ** extra ** V293_tick_scan_pre clock scan)
    (sassign(evar now)(ebinop oplus(evar now)(econst32 Int.one)))
    (<||tail||> ** extra ** V293_tick_scan_pre(Int.add clock Int.one)scan)tid.
Proof.
  intros Spec sd li I r ri tid now clock scan extra tail NA Free Env Inv ExtraFree.
  eapply abscsq_rule with
    (p:=<||spec_seq V293_tick_clock_action tail||> ** extra ** V293_tick_scan_pre clock scan)
    (q:=<||spec_seq V293_tick_clock_action tail||> ** extra **
      V293_tick_scan_state clock(Int.add clock Int.one)scan).
  - exact NA.
  - apply absinfer_eq.
  - eapply absinfer_conseq with
      (p:=<||spec_seq V293_tick_clock_action tail||> **
        (V293_tick_scan_state clock(Int.add clock Int.one)scan ** extra))
      (q:=<||tail||> ** (V293_tick_scan_pre(Int.add clock Int.one)scan ** extra)).
    + intros s H;sep auto.
    + apply V293_tick_scan_clock_close;assumption.
    + intros s H;sep auto.
  - set(R:=extra ** (((CurTid ct ** V293_shared_fields ct tasks es clock) **
      V293_ready_payload br bg bp tasks) **
      (Amapsto(bc,0%Z)(Tptr V293_tcb_type)true scan **
       (V293_owned_record_cells(V293_tick_chain_missing bindings idle) ** coreframe)))).
    eapply conseq_rule with
      (p:=<||spec_seq V293_tick_clock_action tail||> ** V293_rdy_raw_cells (((bn,0%Z),Tint32,Vint32 clock)::nil) R)
      (q:=<||spec_seq V293_tick_clock_action tail||> ** V293_rdy_raw_cells (((bn,0%Z),Tint32,Vint32(Int.add clock Int.one))::nil) R).
    + unfold V293_tick_scan_pre,V293_tick_scan_state,R.
      cbn [V293_rdy_raw_cells];intros s H;sep auto.
    + unfold V293_tick_scan_state,R.
      cbn [V293_rdy_raw_cells];intros s H;sep auto.
    + apply V293_tick_clock_assign_hoare with(before:=[])(after:=[]).
      * unfold R,coreframe,V293_tick_post_hook_core_frame.
        intros st H;eapply V293_star_env_r;[ |exact H].
        intros st1 H1;eapply V293_star_env_r;[ |exact H1].
        intros st2 H2;eapply V293_star_env_r;[ |exact H2].
        intros st3 H3;eapply V293_star_env_r;[ |exact H3].
        intros st4 H4;eapply V293_star_env_r;[ |exact H4].
        exact Env.
      * unfold R,coreframe,V293_tick_post_hook_core_frame.
        intros st H.
        assert(K:st |= (CurTid ct ** frame) ** Atrue) by(clear -H;sep auto).
        eapply V293_CurLINV_extend with(extra:=Atrue).
        eapply astar_mono;[exact Inv|intros s Hs;exact Hs|exact K].
Qed.

Lemma V293_tick_scan_guard : forall clock scan running extra,
  run<256 ->
  (forall st,st |= frame -> get(getlenv st)running=None /\ get(getgenv st)running=Some(bu,Tint8)) ->
  V293_tick_scan_pre clock scan ** extra ==>
    Rv(V293_tick_eq(ecast(evar running)Tint32)1)@Tint32 ==
      Vint32(if Nat.eqb run 1 then Int.one else Int.zero).
Proof.
  intros clock scan running extra Run Env.
  set(R:=(((CurTid ct ** V293_shared_fields ct tasks es clock) ** V293_ready_payload br bg bp tasks) **
    (PV(bn,Int.zero)@Tint32|->Vint32 clock **
     (Amapsto(bc,0%Z)(Tptr V293_tcb_type)true scan **
      (V293_owned_record_cells(V293_tick_chain_missing bindings idle) **
       (V293_owned_record_cell((bh,0%Z),Tptr V293_tcb_type,Vptr(V293_tick_head(map fst bindings)idle)) ** frame))))) ** extra).
  intros st H.
  assert(Raw:st |= V293_rdy_raw_cells (((bu,0%Z),Tint8,V293_byteval run)::nil) R).
  { unfold V293_tick_scan_pre,V293_tick_scan_state,
      coreframe,V293_tick_post_hook_core_frame,globals,V293_tick_post_hook_core_globals in H.
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

Lemma V293_tick_scan_head : forall Spec sd li I r ri tid aop
  clock scan extra ptcb head,
  (forall st,st |= frame -> get(getlenv st)ptcb=Some(bc,Tptr V293_tcb_type) /\
    get(getlenv st)head=None /\ get(getgenv st)head=Some(bh,Tptr V293_tcb_type)) ->
  ((CurTid ct ** frame) ==> CurLINV li tid) ->
  InfRules Spec sd li I r ri
    (<||aop||> ** extra ** V293_tick_scan_pre clock scan)
    (sassign(evar ptcb)(evar head))
    (<||aop||> ** extra ** V293_tick_chain_core_pre bindings idle message ct es clock
      br bg bp bn bc coreframe)tid.
Proof.
  intros Spec sd li I r ri tid aop clock scan extra ptcb head Env Inv.
  set(R:=extra ** (((CurTid ct ** V293_shared_fields ct tasks es clock) ** V293_ready_payload br bg bp tasks) **
    (PV(bn,Int.zero)@Tint32|->Vint32 clock **
     (V293_owned_record_cells(V293_tick_chain_missing bindings idle) **
      (V293_owned_record_cell((bu,0%Z),Tint8,V293_byteval run) ** frame))))).
  set(headcell:=((bh,0%Z),Tptr V293_tcb_type,Vptr(V293_tick_head(map fst bindings)idle))).
  eapply conseq_rule with
    (p:=<||aop||> ** V293_rdy_raw_cells(((bc,0%Z),Tptr V293_tcb_type,scan)::headcell::nil) R)
    (q:=<||aop||> ** V293_rdy_raw_cells(V293_tick_pointer_cell bc(V293_tick_head(map fst bindings)idle)::headcell::nil) R).
  - unfold V293_tick_scan_pre,V293_tick_scan_state,
      coreframe,V293_tick_post_hook_core_frame,globals,V293_tick_post_hook_core_globals,R,headcell.
    cbn [V293_owned_record_cells V293_owned_record_cell V293_tick_pointer_cell V293_rdy_raw_cells].
    intros s H;clear -H;sep auto.
  - unfold V293_tick_chain_core_pre,coreframe,V293_tick_post_hook_core_frame,globals,V293_tick_post_hook_core_globals,R,headcell.
    cbn [V293_owned_record_cells V293_owned_record_cell V293_tick_pointer_cell V293_rdy_raw_cells].
    intros s H;clear -H;sep auto.
  - apply V293_tick_scan_head_store with(prefix:=[])(rest:=headcell::nil)(initial:=scan)(bh:=bh).
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

Theorem V293_tick_scan_branch : forall Spec sd li I r ri tid
  clock scan ptcb rows group now running head enabled ir si ci,
  NoAbs li -> (Int.unsigned(snd idle)+50<=Int.max_unsigned)%Z ->
  Forall V293_tick_binding_valid bindings -> NoDup(V293_tick_record_keys bindings idle) -> run<256 ->
  (forall st,st |= frame -> V293_tick_post_env ptcb rows group now running head bc br bg bn bu bh(getgenv st)(getlenv st)) ->
  ((CurTid ct ** frame) ==> CurLINV li tid) -> GoodFrm frame -> can_change_aop frame ->
  (gettopis si<=INUM)%nat ->
  InfRules Spec sd li I r ri
    (<||tailcode||> ** OS[ir,enabled,si,ci] ** V293_tick_scan_pre clock scan)
    (sifthen(V293_tick_eq(ecast(evar running)Tint32)1)
      (sseq(sassign(evar ptcb)(evar head))(swhile(V293_tick_guard ptcb)(V293_tick_iteration ptcb rows group))))
    (V293_tick_scan_result clock scan ir enabled si ci)tid.
Proof.
  intros Spec sd li I r ri tid clock scan ptcb rows group now running head enabled ir si ci
    NA IdleLimit Valid Unique Run Env Inv GF Free Bound.
  eapply V293_tick_known_ift_hoare with(flag:=Nat.eqb run 1).
  - intros st H.
    assert(Core:st |= V293_tick_scan_pre clock scan **
      (<||tailcode||> ** OS[ir,enabled,si,ci]))by(clear -H;sep auto).
    eapply V293_tick_scan_guard;[exact Run| |exact Core].
    intros st0 H0;exact(proj1(proj2(proj2(Env st0 H0)))).
  - destruct(Nat.eqb run 1)eqn:Running.
    + unfold tailcode,V293_tick_post_hook_core_tail,V293_tick_scan_result;rewrite Running.
      eapply seq_rule.
      * apply V293_tick_scan_head.
        -- intros st H. destruct(Env st H)as[Delay[Clock[RunningEnv Head]]].
           split;[exact(proj1 Delay)|exact Head].
        -- exact Inv.
      * apply V293_tick_chain_core_hoare;try assumption.
        -- unfold coreframe,V293_tick_post_hook_core_frame.
           intros st H;eapply V293_star_env_r;[ |exact H].
           intros st0 H0;exact(proj1(Env st0 H0)).
        -- unfold coreframe,V293_tick_post_hook_core_frame.
           intros st H;assert(K:st |= (CurTid ct ** frame) ** Atrue)by(clear -H;sep auto).
           eapply V293_CurLINV_extend with(extra:=Atrue).
           eapply astar_mono;[exact Inv|intros s Hs;exact Hs|exact K].
        -- unfold coreframe,V293_tick_post_hook_core_frame;split;[apply V293_tick_cells_frame|exact GF].
        -- unfold coreframe,V293_tick_post_hook_core_frame;split;
             [apply V293_tick_update_change;apply V293_owned_cells_good|exact Free].
    + unfold tailcode,V293_tick_post_hook_core_tail,V293_tick_scan_result;rewrite Running.
      intros st H;exact H.
Qed.

Theorem V293_tick_scan_hoare : forall Spec sd li I r ri tid
  clock scan ptcb rows group now running head enabled ir si ci,
  NoAbs li -> (Int.unsigned(snd idle)+50<=Int.max_unsigned)%Z ->
  Forall V293_tick_binding_valid bindings -> NoDup(V293_tick_record_keys bindings idle) -> run<256 ->
  (forall st,st |= frame -> V293_tick_post_env ptcb rows group now running head bc br bg bn bu bh(getgenv st)(getlenv st)) ->
  ((CurTid ct ** frame) ==> CurLINV li tid) -> GoodFrm frame -> can_change_aop frame ->
  (gettopis si<=INUM)%nat ->
  InfRules Spec sd li I r ri
    (<||code||> ** OS[ir,enabled,si,ci] ** V293_tick_scan_pre clock scan)
    (V293_tick_post_hook ptcb rows group now running head)
    (V293_tick_scan_result(Int.add clock Int.one)scan ir enabled si ci)tid.
Proof.
  intros Spec sd li I r ri tid clock scan ptcb rows group now running head enabled ir si ci
    NA IdleLimit Valid Unique Run Env Inv GF Free Bound.
  set(P:=V293_tick_scan_pre clock scan).
  set(Q:=V293_tick_scan_pre(Int.add clock Int.one)scan).
  set(branch:=sifthen(V293_tick_eq(ecast(evar running)Tint32)1)
    (sseq(sassign(evar ptcb)(evar head))(swhile(V293_tick_guard ptcb)(V293_tick_iteration ptcb rows group)))).
  set(target:=V293_tick_scan_result(Int.add clock Int.one)scan ir enabled si ci).
  assert(GP:GoodFrm P)by(apply V293_tick_scan_good;exact GF).
  assert(GQ:GoodFrm Q)by(apply V293_tick_scan_good;exact GF).
  assert(IQ:Q ==> CurLINV li tid).
  { unfold Q,V293_tick_scan_pre,V293_tick_scan_state,coreframe,V293_tick_post_hook_core_frame.
    intros st H;assert(K:st |= (CurTid ct ** frame) ** Atrue)by(clear -H;sep auto).
    eapply V293_CurLINV_extend with(extra:=Atrue).
    eapply astar_mono;[exact Inv|intros s Hs;exact Hs|exact K]. }
  assert(Branch:InfRules Spec sd li I r ri
    (<||tailcode||> ** OS[ir,enabled,si,ci] ** Q)branch target tid).
  { apply V293_tick_scan_branch with(now:=now);assumption. }
  assert(Work:forall extra tail out,can_change_aop extra ->
    InfRules Spec sd li I r ri(<||tailcode||> ** extra ** Q)tail out tid ->
    InfRules Spec sd li I r ri(<||code||> ** extra ** P)
      (sseq(sassign(evar now)(ebinop oplus(evar now)(econst32 Int.one)))tail)out tid).
  { intros extra tail out ExtraFree Tail.
    eapply seq_rule with(p':=<||tailcode||> ** extra ** Q);[ |exact Tail].
    apply V293_tick_scan_clock_write;try assumption.
    intros st H;exact(proj1(proj2(Env st H))). }
  change(InfRules Spec sd li I r ri(<||code||> ** OS[ir,enabled,si,ci] ** P)
    (sseq(sprim encrit)(sseq(sassign(evar now)(ebinop oplus(evar now)(econst32 Int.one)))
      (sseq(sprim excrit)branch)))target tid).
  destruct enabled.
  - eapply seq_rule.
    + eapply conseq_rule with
        (p:=<||code||> ** OS[ir,true,si,ci] ** ATopis(gettopis si) **
          [|(gettopis si<=INUM)%nat|] ** P)
        (q:=<||code||> ** OS[ir,false,si,true::ci] ** invlth_isr I 0(gettopis si) ** P).
      * intros st H;assert(IS:st |= Ais si ** Atrue)by(sep auto).
        pose proof(V293_time_topis si Atrue st IS)as Top.
        apply astar_l_atopis_elim in Top;destruct Top as[Top _].
        pose proof(@astar_l_atopis_intro st(gettopis si)_ H Top)as HT.
        clear H;rename HT into H;sep auto.
      * intros st H;exact H.
      * apply encrit1_rule;exact GP.
    + eapply conseq_rule with
        (p:=<||code||> ** (OS[ir,false,si,true::ci] ** invlth_isr I 0(gettopis si)) ** P)
        (q:=target);[ |intros st H;exact H|apply Work].
      * intros st H;sep auto.
      * split;[repeat split;exact Logic.I|apply V293_tick_post_hook_borrow_change].
      * eapply seq_rule with(p':=<||tailcode||> ** OS[ir,true,si,ci] ** Q);[ |exact Branch].
        eapply conseq_rule with
          (p:=<||tailcode||> ** OS[ir,false,si,true::ci] ** ATopis(gettopis si) **
            invlth_isr I 0(gettopis si) ** Q)
          (q:=<||tailcode||> ** OS[ir,true,si,ci] ** Q).
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

Theorem V293_tick_scan_semantics : forall Spec sd li I r ri tid
  clock scan ptcb rows group now running head enabled ir si ci,
  NoAbs li -> (Int.unsigned(snd idle)+50<=Int.max_unsigned)%Z ->
  Forall V293_tick_binding_valid bindings -> NoDup(V293_tick_record_keys bindings idle) -> run<256 ->
  (forall st,st |= frame -> V293_tick_post_env ptcb rows group now running head bc br bg bn bu bh(getgenv st)(getlenv st)) ->
  ((CurTid ct ** frame) ==> CurLINV li tid) -> GoodFrm frame -> can_change_aop frame ->
  (gettopis si<=INUM)%nat ->
  simulation.RuleSem Spec sd li I r ri
    (<||code||> ** OS[ir,enabled,si,ci] ** V293_tick_scan_pre clock scan)
    (V293_tick_post_hook ptcb rows group now running head)
    (V293_tick_scan_result(Int.add clock Int.one)scan ir enabled si ci)tid.
Proof. intros;apply RuleSound;apply V293_tick_scan_hoare;assumption. Qed.
End ScanSlot.

(* Preserve the SAME shared invariant while admitting genuine fresh locals. *)
Section ScanSwitchBoundary.
Variables (bindings:list(V293_tick_task*(taskstatus*val))) (idle:addrval) (message:val)
  (ct:tid) (es:EcbMod.map) (br bg bp bn bc bu bh:block) (run:nat) (frame:asrt).
Let tasks:=V293_tick_record_map false bindings idle message.
Let globals:=V293_tick_post_hook_core_globals bindings idle bu bh run.
Let coreframe:=V293_tick_post_hook_core_frame bindings idle bu bh run frame.
Let corepre:=V293_tick_scan_pre bindings idle message ct es br bg bp bn bc bu bh run frame.
Let coreresult:=V293_tick_scan_result bindings idle message ct es br bg bp bn bc bu bh run frame.

Definition V293_tick_scan_supplement scan :=
  Amapsto(bc,0%Z)(Tptr V293_tcb_type)true scan **
  (V293_owned_record_cells(V293_tick_chain_missing bindings idle) **
   (V293_owned_record_cells globals ** frame)).
Definition V293_tick_scan_switch_pre clock scan :=
  V293_tick_switch_view br bg bp bn ct tasks es clock ** V293_tick_scan_supplement scan.
Definition V293_tick_scan_switch_result scan ir si ci :=
  if Nat.eqb run 1 then
    EX actual:list(V293_tick_task*(taskstatus*val)),
      (<||END None||> ** OS[ir,false,si,ci] **
       (SWINV(V293_time_ready_inv br bg bp bn) **
        (V293_owned_record_cell(V293_tick_pointer_cell bc idle) **
         (V293_owned_record_cells(V293_tick_chain_residual actual idle) ** coreframe)))) **
      [|V293_tick_pend_choices bindings actual|]
  else <||END None||> ** OS[ir,false,si,ci] **
    (SWINV(V293_time_ready_inv br bg bp bn) ** V293_tick_scan_supplement scan).

Lemma V293_tick_scan_switch_entry : forall clock scan ir si ci aop,
  <||aop||> ** OS[ir,false,si,ci] ** V293_tick_scan_switch_pre clock scan ==>
  <||aop||> ** OS[ir,false,si,ci] ** corepre clock scan.
Proof.
  intros clock scan ir si ci aop s Held.
  assert(Open:s |=
    (V293_shared_flags ** (((CurTid ct ** V293_shared_fields ct tasks es clock) **
       V293_ready_payload br bg bp tasks) ** PV(bn,Int.zero)@Tint32|->Vint32 clock)) **
    (V293_tick_scan_supplement scan ** (<||aop||> ** OS[ir,false,si,ci]))).
  { eapply astar_mono;[apply V293_tick_switch_open|intros st H;exact H| ].
    unfold V293_tick_scan_switch_pre in Held;clear -Held;sep auto. }
  unfold corepre,V293_tick_scan_pre,V293_tick_scan_state,
    V293_tick_scan_supplement,V293_tick_post_hook_core_frame,coreframe,globals,
    V293_shared_flags,tasks,isrclr in *.
  clear Held;sep normal in Open;sep destruct Open.
  (* Modal flags can be discarded; no physical or abstract resource is lost. *)
  sep auto.
  destruct Open as[Open _];sep auto.
Qed.

Lemma V293_tick_scan_switch_return : forall clock scan ir si ci,
  (forall i,ir i=false) ->
  coreresult clock scan ir false si ci ==> V293_tick_scan_switch_result scan ir si ci.
Proof.
  intros clock scan ir si ci Clear s Held.
  unfold coreresult,V293_tick_scan_result,V293_tick_scan_switch_result in *.
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
      (V293_time_ready_core br bg bp bn ** (V293_tick_scan_supplement scan ** <||END None||>))).
    { unfold corepre,V293_tick_scan_pre,V293_tick_scan_state,
        V293_tick_post_hook_core_frame,V293_tick_scan_supplement,globals,
        V293_time_ready_core,V293_time_ready_fields in Held |- *.
      clear -Held;sep auto. }
    apply V293_tick_switch_close in Core;[ |exact Clear]. clear -Core;sep auto.
Qed.

Theorem V293_tick_scan_switch_hoare : forall Spec sd li r ri tid
  clock scan ptcb rows group now running head ir si ci,
  NoAbs li -> (Int.unsigned(snd idle)+50<=Int.max_unsigned)%Z ->
  Forall V293_tick_binding_valid bindings -> NoDup(V293_tick_record_keys bindings idle) -> run<256 ->
  (forall st,st |= frame -> V293_tick_post_env ptcb rows group now running head bc br bg bn bu bh(getgenv st)(getlenv st)) ->
  ((CurTid ct ** frame) ==> CurLINV li tid) -> GoodFrm frame -> can_change_aop frame ->
  (gettopis si<=INUM)%nat -> (forall i,ir i=false) ->
  InfRules Spec sd li (V293_time_ready_inv br bg bp bn) r ri
    (<||V293_tick_post_hook_core_code bindings run||> ** OS[ir,false,si,ci] ** V293_tick_scan_switch_pre clock scan)
    (V293_tick_post_hook ptcb rows group now running head)
    (V293_tick_scan_switch_result scan ir si ci)tid.
Proof.
  intros Spec sd li r ri tid clock scan ptcb rows group now running head ir si ci
    NA IdleLimit Valid Unique Run Env Inv GF Free Bound Clear.
  eapply conseq_rule with
    (p:=<||V293_tick_post_hook_core_code bindings run||> ** OS[ir,false,si,ci] ** corepre clock scan)
    (q:=coreresult(Int.add clock Int.one)scan ir false si ci).
  - apply V293_tick_scan_switch_entry.
  - apply V293_tick_scan_switch_return;exact Clear.
  - apply V293_tick_scan_hoare;assumption.
Qed.

Theorem V293_tick_scan_switch_semantics : forall Spec sd li r ri tid
  clock scan ptcb rows group now running head ir si ci,
  NoAbs li -> (Int.unsigned(snd idle)+50<=Int.max_unsigned)%Z ->
  Forall V293_tick_binding_valid bindings -> NoDup(V293_tick_record_keys bindings idle) -> run<256 ->
  (forall st,st |= frame -> V293_tick_post_env ptcb rows group now running head bc br bg bn bu bh(getgenv st)(getlenv st)) ->
  ((CurTid ct ** frame) ==> CurLINV li tid) -> GoodFrm frame -> can_change_aop frame ->
  (gettopis si<=INUM)%nat -> (forall i,ir i=false) ->
  simulation.RuleSem Spec sd li (V293_time_ready_inv br bg bp bn) r ri
    (<||V293_tick_post_hook_core_code bindings run||> ** OS[ir,false,si,ci] ** V293_tick_scan_switch_pre clock scan)
    (V293_tick_post_hook ptcb rows group now running head)
    (V293_tick_scan_switch_result scan ir si ci)tid.
Proof. intros;apply RuleSound;apply V293_tick_scan_switch_hoare;assumption. Qed.
End ScanSwitchBoundary.
