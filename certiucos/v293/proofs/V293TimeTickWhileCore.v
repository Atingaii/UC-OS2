(* The ORIGINAL complete while, followed by the EXISTING ordered abstract
   waiting-task chain. Exact shared core and residuals are returned.
   Entry still owns raw loop fields: no production IRQ borrowing is claimed. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickReadyUpdate.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBClear.
Require Import CertiOS.certiucos.v293.proofs.V293InitAllRecords.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickWhileShared.
Require Import CertiOS.certiucos.v293.proofs.V293TimeReadyShared.
Require Import CertiOS.certiucos.v293.proofs.V293TimeShared.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickWhileHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLosslessFields.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickReadyChain.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickRecordReassembly.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickWhileRecords.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickTaskBridge.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLoop.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickExpiry.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickDelayHoare.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFieldsHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBSuccessHoare.
Require Import CertiOS.certiucos.v293.proofs.V293NullBytes.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.code.V293OSTimeTick.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.soundness.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Coq.Sorting.Permutation Lia.
Import ListNotations.
Local Open Scope nat_scope.

Lemma V293_tick_chain_absinfer : forall bindings idle sd tasks R,
  Forall V293_tick_binding_valid bindings -> NoDup (V293_tick_record_keys bindings idle) ->
  (forall b, In b bindings -> get tasks (V293_tick_task_pointer (fst b))=
    Some (V293_tick_binding_value false b)) -> can_change_aop R ->
  absinfer sd (<||V293_tick_chain_code bindings||> ** (Aabsdata abstcblsid (abstcblist tasks) ** R))
    (<||END None||> ** (Aabsdata abstcblsid (abstcblist (V293_tick_bindings_run bindings tasks)) ** R)).
Proof.
  induction bindings as [ |[node [status msg]] rest IH];intros idle sd tasks R Valid Unique Inputs Free.
  - cbn [V293_tick_chain_code V293_tick_bindings_run]. apply absinfer_eq.
  - inversion Valid as [  |head tail Head Tail];subst head tail.
    change(NoDup(V293_tick_task_pointer node::V293_tick_record_keys rest idle))in Unique.
    inversion Unique as [  |key keys Fresh TailUnique];subst key keys.
    cbn [V293_tick_chain_code V293_tick_bindings_run fst snd].
    destruct status as [  |reason delay].
    + apply IH with(idle:=idle);try assumption. intros b Member. apply Inputs. right;exact Member.
    + destruct Head as [ NodeValid[P[Shape Delay]]]. cbn in Delay. subst delay.
      set (updated:=set tasks(V293_tick_task_pointer node)
        (V293_tick_binding_value true(node,(wait reason(Int.repr(V293_tick_delay_value node)),msg)))).
      eapply absinfer_trans with(q:=<||spec_seq(END None)(V293_tick_chain_code rest)||> **
        (Aabsdata abstcblsid(abstcblist updated) ** R)).
      * apply absinfer_seq;[cbn;tauto|cbn;tauto| ].
        unfold updated,V293_tick_binding_value,V293_tick_binding_status;cbn [fst snd].
        apply V293_tick_wait_absinfer.
        -- exact(Inputs _ (or_introl eq_refl)).
        -- exact(proj1(proj2 NodeValid)).
        -- exact Free.
      * eapply absinfer_trans with(q:=<||V293_tick_chain_code rest||> **
          (Aabsdata abstcblsid(abstcblist updated) ** R)).
        -- apply absinfer_seq_end;[cbn;tauto|cbn;tauto|intros st H;exact H].
        -- apply IH with(idle:=idle);try assumption.
           intros b Member. unfold updated. rewrite map_get_set'.
           ++ apply Inputs. right;exact Member.
           ++ intro Same. apply Fresh. unfold V293_tick_record_keys. apply in_or_app. left.
              apply in_map_iff. exists b. split;[congruence|exact Member].
Qed.

Lemma V293_tick_while_raw_change : forall cells R,
  can_change_aop R -> can_change_aop (V293_rdy_raw_cells cells R).
Proof.
  induction cells as [ |[[a tp]v]rest IH];intros R Free;cbn [V293_rdy_raw_cells can_change_aop].
  - exact Free.
  - split;[exact Logic.I|apply IH;exact Free].
Qed.

Lemma V293_tick_while_after_typed : forall bindings idle,
  Forall V293_tick_binding_valid bindings ->
  Forall (fun c=>let '(_,tp,v):=c in rule_type_val_match tp v=true)
    (V293_tick_chain_cells (map V293_tick_task_after (map fst bindings)) idle).
Proof.
  induction bindings as [ |b rest IH];intros idle Valid;cbn [map V293_tick_chain_cells].
  - constructor.
  - inversion Valid as [ |head tail Head Tail];subst head tail.
    apply Forall_app;split;[apply V293_tick_after_task_typed;destruct b as [t [status msg]];exact(proj1 Head)|apply IH;exact Tail].
Qed.

Section WhileCore.
Variables (bindings:list(V293_tick_task*(taskstatus*val))) (idle:addrval) (message:val)
  (ct:tid) (es:EcbMod.map) (n:int32) (br bg bp bn bc:block) (frame:asrt).
Let oldtasks:=V293_tick_record_map false bindings idle message.
Let newtasks:=V293_tick_record_map true bindings idle message.

Definition V293_tick_while_core_remainder tasks entries :=
  V293_owned_record_cells (concat(map V293_tick_binding_extra bindings)) **
  (V293_owned_record_cells (V293_tick_idle_extra idle message) **
  (V293_shared_fields ct tasks es n **
  (V293_owned_record_cells (V293_priority_cells bp 0%Z entries) **
  (CurTid ct ** (PV(bn,Int.zero)@Tint32|->Vint32 n ** frame))))).
Definition V293_tick_while_core_pre lo hi entries :=
  V293_rdy_raw_cells
    (V293_tick_while_cells bc [] (map fst bindings) idle bg br (V293_ready_group lo hi) lo hi)
    (V293_tick_while_core_remainder oldtasks entries).
Definition V293_tick_while_core_post := V293_time_ready_core br bg bp bn **
  (V293_owned_record_cell (V293_tick_pointer_cell bc idle) **
   (V293_owned_record_cells (V293_tick_chain_residual bindings idle) ** frame)).

Lemma V293_tick_while_core_raw_close : forall lo hi entries gf lof hif,
  Forall V293_tick_binding_valid bindings -> NoDup(V293_tick_record_keys bindings idle) ->
  V293_ready_rel lo hi entries oldtasks ->
  V293_tick_chain_bitmap(map fst bindings)(V293_ready_group lo hi)lo hi=(gf,(lof,hif)) ->
  V293_rdy_raw_cells
    (V293_tick_while_cells bc (V293_tick_chain_cells(map V293_tick_task_after(map fst bindings))idle)
      [] idle bg br gf lof hif) (V293_tick_while_core_remainder newtasks entries) ==>
    V293_tick_while_core_post.
Proof.
  intros lo hi entries gf lof hif Valid Unique Rel Bitmap s Raw.
  pose proof(V293_tick_record_chain_ready_rel bindings idle message lo hi entries Valid Unique Rel)as Ready.
  rewrite Bitmap in Ready. destruct Ready as [ Group NewRel].
  assert(G:gf<256)by(rewrite Group;unfold V293_ready_group;destruct(lof=?0);destruct(hif=?0);lia).
  assert(Typed:Forall(fun c=>let '(_,tp,v):=c in rule_type_val_match tp v=true)
    (V293_tick_while_cells bc (V293_tick_chain_cells(map V293_tick_task_after(map fst bindings))idle)
      [] idle bg br gf lof hif)).
  { unfold V293_tick_while_cells. cbn [V293_tick_head V293_tick_chain_cells app].
    constructor;[reflexivity| ]. apply Forall_app;split.
    - apply V293_tick_while_after_typed;exact Valid.
    - apply Forall_app;split.
      + apply V293_tick_bitmap_typed;[exact G|exact(proj1 NewRel)|exact(proj1(proj2 NewRel))].
      + constructor;[reflexivity|constructor]. }
  pose proof(V293_tick_raw_to_owned _ _ Typed s Raw)as Owned.
  unfold V293_tick_while_cells in Owned. cbn [V293_tick_head V293_tick_chain_cells app]in Owned.
  assert(Split:s |= V293_owned_record_cell(V293_tick_pointer_cell bc idle) **
    (V293_owned_record_cells(V293_tick_chain_cells(map V293_tick_task_after(map fst bindings))idle) **
    (V293_owned_record_cells(V293_tick_bitmap_cells bg br gf lof hif) **
    (V293_owned_record_cell(V293_tick_idle_cell idle) ** V293_tick_while_core_remainder newtasks entries)))).
  { cbn [V293_owned_record_cells] in Owned.
    assert(S1:s |= (V293_owned_record_cell(V293_tick_pointer_cell bc idle) **
      (V293_owned_record_cells(V293_tick_chain_cells(map V293_tick_task_after(map fst bindings))idle) **
       V293_owned_record_cells(V293_tick_bitmap_cells bg br gf lof hif++[V293_tick_idle_cell idle]))) **
       V293_tick_while_core_remainder newtasks entries).
    { eapply astar_mono;[ | intros st H;exact H|exact Owned].
      apply astar_mono;[intros st H;exact H| ].
      intros st H;exact(proj1(V293_tick_cells_append _ _ st) H). }
    assert(S2:s |= (V293_owned_record_cell(V293_tick_pointer_cell bc idle) **
      (V293_owned_record_cells(V293_tick_chain_cells(map V293_tick_task_after(map fst bindings))idle) **
       (V293_owned_record_cells(V293_tick_bitmap_cells bg br gf lof hif) **
        V293_owned_record_cells (V293_tick_idle_cell idle::nil)))) **
       V293_tick_while_core_remainder newtasks entries).
    { eapply astar_mono;[ | intros st H;exact H|exact S1].
      apply astar_mono;[intros st H;exact H| ].
      apply astar_mono;[intros st H;exact H| ].
      intros st H;exact(proj1(V293_tick_cells_append _ _ st) H). }
    cbn [V293_owned_record_cells] in S2. clear -S2;sep auto. }
  assert(Records:s |= V293_owned_task_records newtasks **
    (V293_owned_record_cells(V293_tick_chain_residual bindings idle) **
    (V293_owned_record_cell(V293_tick_pointer_cell bc idle) **
    (V293_owned_record_cells(V293_tick_bitmap_cells bg br gf lof hif) **
    (V293_shared_fields ct newtasks es n **
    (V293_owned_record_cells(V293_priority_cells bp 0%Z entries) **
    (CurTid ct ** (PV(bn,Int.zero)@Tint32|->Vint32 n ** frame)))))))).
  { apply V293_tick_chain_records_lossless;[exact Valid|exact Unique| ].
    unfold V293_tick_while_core_remainder in Split. clear -Split;sep auto. }
  unfold V293_tick_while_core_post,V293_time_ready_core,V293_time_ready_fields,
    V293_ready_payload,V293_ready_owned,V293_ready_cells.
  cbn [V293_tick_bitmap_cells V293_owned_record_cells]in Records.
  rewrite Group in Records. cbn [V293_owned_record_cells app].
  clear -Records NewRel;sep auto.
Qed.

Lemma V293_tick_while_core_finish : forall sd lo hi entries gf lof hif ir enabled si ci,
  Forall V293_tick_binding_valid bindings -> NoDup(V293_tick_record_keys bindings idle) ->
  V293_ready_rel lo hi entries oldtasks -> can_change_aop frame ->
  V293_tick_chain_bitmap(map fst bindings)(V293_ready_group lo hi)lo hi=(gf,(lof,hif)) ->
  absinfer sd
    (<||V293_tick_chain_code bindings||> ** OS[ir,enabled,si,ci] ** V293_rdy_raw_cells
      (V293_tick_while_cells bc (V293_tick_chain_cells(map V293_tick_task_after(map fst bindings))idle)
        [] idle bg br gf lof hif) (V293_tick_while_core_remainder oldtasks entries))
    (<||END None||> ** OS[ir,enabled,si,ci] ** V293_tick_while_core_post).
Proof.
  intros sd lo hi entries gf lof hif ir enabled si ci Valid Unique Rel Free Bitmap.
  set(cells:=V293_tick_while_cells bc (V293_tick_chain_cells(map V293_tick_task_after(map fst bindings))idle)
    [] idle bg br gf lof hif).
  set(other:=V293_owned_record_cells(concat(map V293_tick_binding_extra bindings)) **
    (V293_owned_record_cells(V293_tick_idle_extra idle message) **
    ((Aabsdata curtid(oscurt ct) ** (Aabsdata absecblsid(absecblist es) ** Aabsdata ostmid(ostm n))) **
    (V293_owned_record_cells(V293_priority_cells bp 0%Z entries) **
    (CurTid ct ** (PV(bn,Int.zero)@Tint32|->Vint32 n ** frame)))))).
  eapply absinfer_conseq with
    (p:=<||V293_tick_chain_code bindings||> ** (Aabsdata abstcblsid(abstcblist oldtasks) **
      (OS[ir,enabled,si,ci] ** V293_rdy_raw_cells cells other)))
    (q:=<||END None||> ** (Aabsdata abstcblsid(abstcblist newtasks) **
      (OS[ir,enabled,si,ci] ** V293_rdy_raw_cells cells other))).
  - intros s H.
    assert(K:s |= <||END None||> ** OS[ir,enabled,si,ci] **
      V293_rdy_raw_cells cells(V293_tick_while_core_remainder newtasks entries)).
    { assert(T:s |= <||END None||> ** (OS[ir,enabled,si,ci] **
        (Aabsdata abstcblsid(abstcblist newtasks) ** V293_rdy_raw_cells cells other)))
        by(clear -H;sep auto).
      eapply astar_mono;[intros st Hs;exact Hs| |exact T].
      apply astar_mono;[intros st Hs;exact Hs| ].
      intros st Hs. eapply V293_raw_cells_mono;[ |apply V293_raw_cells_unmove_frame;exact Hs].
      unfold other,V293_tick_while_core_remainder,V293_shared_fields. intros st0 H0;sep auto. }
    eapply astar_mono;[intros st Hs;exact Hs| |exact K].
    apply astar_mono;[intros st Hs;exact Hs| ].
    apply V293_tick_while_core_raw_close with(lo:=lo)(hi:=hi);assumption.
  - unfold newtasks. rewrite <-V293_tick_bindings_run_map by exact Unique.
    apply V293_tick_chain_absinfer with(idle:=idle);try assumption.
    + intros b Member;apply V293_tick_record_map_member;assumption.
    + cbn [can_change_aop]. split;[repeat split;exact Logic.I| ].
      apply V293_tick_while_raw_change. unfold other.
      cbn [can_change_aop]. repeat split;try exact Logic.I;try exact Free;
        apply V293_tick_update_change;apply V293_owned_cells_good.
  - intros s H.
    assert(K:s |= <||V293_tick_chain_code bindings||> ** OS[ir,enabled,si,ci] **
      (Aabsdata abstcblsid(abstcblist oldtasks) ** V293_rdy_raw_cells cells other)).
    { eapply astar_mono;[intros st Hs;exact Hs| |exact H].
      apply astar_mono;[intros st Hs;exact Hs| ].
      intros st Hs. apply V293_raw_cells_move_frame.
      eapply V293_raw_cells_mono;[ |exact Hs].
      unfold other,V293_tick_while_core_remainder,V293_shared_fields. intros st0 H0;sep auto. }
    clear -K;sep auto.
Qed.

Theorem V293_tick_while_core_hoare : forall Spec sd li I r ri tid
  ptcb rows group lo hi entries enabled ir si ci,
  NoAbs li -> (Int.unsigned(snd idle)+50<=Int.max_unsigned)%Z ->
  Forall V293_tick_binding_valid bindings -> NoDup(V293_tick_record_keys bindings idle) ->
  V293_ready_rel lo hi entries oldtasks ->
  (forall st,st |= frame -> V293_tick_delay_env ptcb rows group bc br bg(getgenv st)(getlenv st)) ->
  ((CurTid ct ** frame) ==> CurLINV li tid) -> GoodFrm frame -> can_change_aop frame ->
  (gettopis si<=INUM)%nat ->
  InfRules Spec sd li I r ri
    (<||V293_tick_chain_code bindings||> ** OS[ir,enabled,si,ci] ** V293_tick_while_core_pre lo hi entries)
    (swhile(V293_tick_guard ptcb)(V293_tick_iteration ptcb rows group))
    (<||END None||> ** OS[ir,enabled,si,ci] ** V293_tick_while_core_post)tid.
Proof.
  intros Spec sd li I r ri tid ptcb rows group lo hi entries enabled ir si ci
    NA IdleLimit Valid Unique Rel Env Inv GF Free Bound.
  destruct(V293_tick_chain_bitmap(map fst bindings)(V293_ready_group lo hi)lo hi)as [ gf[lof hif]]eqn:Bitmap.
  eapply abscsq_rule with
    (p:=<||V293_tick_chain_code bindings||> ** OS[ir,enabled,si,ci] ** V293_tick_while_core_pre lo hi entries)
    (q:=<||V293_tick_chain_code bindings||> ** OS[ir,enabled,si,ci] ** V293_rdy_raw_cells
      (V293_tick_while_cells bc (V293_tick_chain_cells(map V293_tick_task_after(map fst bindings))idle)
        [] idle bg br gf lof hif) (V293_tick_while_core_remainder oldtasks entries)).
  - exact NA.
  - apply absinfer_eq.
  - apply V293_tick_while_core_finish with(lo:=lo)(hi:=hi);assumption.
  - unfold V293_tick_while_core_pre.
    pose proof(V293_tick_while_hoare Spec sd li I r ri tid (V293_tick_chain_code bindings)
      (V293_tick_while_core_remainder oldtasks entries)ptcb rows group bc(map fst bindings)idle bg br
      (V293_ready_group lo hi)lo hi enabled ir si ci)as Rule.
    rewrite Bitmap in Rule. apply Rule.
    + exact IdleLimit.
    + rewrite Forall_map. eapply Forall_impl;[ | exact Valid]. intros [t [status msg]] H;exact(proj1 H).
    + unfold V293_ready_group;destruct(lo=?0);destruct(hi=?0);lia.
    + exact(proj1 Rel).
    + exact(proj1(proj2 Rel)).
    + unfold V293_tick_while_core_remainder. repeat apply V293_star_env_r. exact Env.
    + unfold V293_tick_while_core_remainder. intros st H.
      apply V293_CurLINV_extend with(extra:=Atrue).
      eapply astar_mono;[exact Inv|intros s Hs;exact Hs| ]. clear -H;sep auto.
    + unfold V293_tick_while_core_remainder,V293_shared_fields. cbn [GoodFrm].
      repeat split;try exact Logic.I;try exact GF;apply V293_tick_cells_frame.
    + exact Bound.
Qed.

Theorem V293_tick_while_core_semantics : forall Spec sd li I r ri tid
  ptcb rows group lo hi entries enabled ir si ci,
  NoAbs li -> (Int.unsigned(snd idle)+50<=Int.max_unsigned)%Z ->
  Forall V293_tick_binding_valid bindings -> NoDup(V293_tick_record_keys bindings idle) ->
  V293_ready_rel lo hi entries oldtasks ->
  (forall st,st |= frame -> V293_tick_delay_env ptcb rows group bc br bg(getgenv st)(getlenv st)) ->
  ((CurTid ct ** frame) ==> CurLINV li tid) -> GoodFrm frame -> can_change_aop frame ->
  (gettopis si<=INUM)%nat ->
  simulation.RuleSem Spec sd li I r ri
    (<||V293_tick_chain_code bindings||> ** OS[ir,enabled,si,ci] ** V293_tick_while_core_pre lo hi entries)
    (swhile(V293_tick_guard ptcb)(V293_tick_iteration ptcb rows group))
    (<||END None||> ** OS[ir,enabled,si,ci] ** V293_tick_while_core_post)tid.
Proof. intros;apply RuleSound;apply V293_tick_while_core_hoare;assumption. Qed.
End WhileCore.
