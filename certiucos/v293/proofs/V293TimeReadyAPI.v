(* Actual time APIs retain the existing ready/TCB/table invariant.
   Reuses the fixed V2.93.01 bodies and abstract actions; no replacement Inv. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeReadyShared.
Require Import CertiOS.certiucos.v293.proofs.V293TimeShared.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.framework.proof.step_prop.
Require Import CertiOS.certiucos.v293.proofs.V293TimeGetAPI.
Require Import CertiOS.certiucos.v293.proofs.V293TimeGetLink.
Require Import CertiOS.certiucos.v293.proofs.V293TimeSharedSet.
Require Import CertiOS.certiucos.v293.proofs.V293TimeNamesGood.
Require Import CertiOS.certiucos.v293.proofs.V293TimeSetAPI.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSVersionAPI.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.toptheorem.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Local Open Scope nat_scope.
Require Import CertiOS.certiucos.v293.code.V293OSVersion.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.certiucos.v293.proofs.V293ComponentLink.
Section ReadyAPI.
Variables br bg bp : block.
Local Lemma ready_action_free : forall P, GoodInvAsrt P -> can_change_aop P.
Proof. induction P;simpl;intuition eauto. Qed.

Lemma V293_time_ready_get_linearize : forall sd bn clock frame,
  can_change_aop frame ->
  absinfer sd
    (<||V293_time_get_action||> **
      ((V293_time_ready_fields br bg bp clock ** PV (bn,Int.zero) @ Tint32 |-> Vint32 clock) ** frame))
    (<||END (Some (Vint32 clock))||> ** (V293_time_ready_core br bg bp bn ** frame)).
Proof.
  intros sd bn clock frame Free.
  eapply absinfer_conseq with
    (p:=<||V293_time_get_action||> ** (Aabsdata ostmid (ostm clock) **
      ((EX t : tid, EX ts : TcbMod.map, EX es : EcbMod.map,
        CurTid t ** (Aabsdata curtid (oscurt t) **
          (Aabsdata abstcblsid (abstcblist ts) ** Aabsdata absecblsid (absecblist es))) **
        V293_ready_payload br bg bp ts) **
        (PV (bn,Int.zero) @ Tint32 |-> Vint32 clock ** frame))))
    (q:=<||END (Some (Vint32 clock))||> ** (Aabsdata ostmid (ostm clock) **
      ((EX t : tid, EX ts : TcbMod.map, EX es : EcbMod.map,
        CurTid t ** (Aabsdata curtid (oscurt t) **
          (Aabsdata abstcblsid (abstcblist ts) ** Aabsdata absecblsid (absecblist es))) **
        V293_ready_payload br bg bp ts) **
        (PV (bn,Int.zero) @ Tint32 |-> Vint32 clock ** frame)))).
  - unfold V293_time_ready_core,V293_time_ready_fields,V293_shared_fields.
    intros s H;sep auto.
  - apply V293_time_get_absinfer.
    split.
    + intros t ts es. split.
      * unfold CurTid,Agvarmapsto,Aptrmapsto. simpl;auto.
      * split;[simpl;auto | apply ready_action_free;apply V293_ready_payload_good].
    + simpl;auto.
  - unfold V293_time_ready_core,V293_time_ready_fields,V293_shared_fields.
    intros s H;sep auto.
Qed.

Theorem V293_time_ready_get_copy : forall Spec sd li r ri tid now ticks saved bn bt bs tmp save frame,
  NoAbs li -> can_change_aop frame -> (frame ==> CurLINV li tid) ->
  InfRules Spec sd li (V293_time_ready_inv br bg bp bn) r ri
    (<||V293_time_get_action||> ** (V293_time_ready_core br bg bp bn **
      V293_time_shared_locals now ticks saved bn bt bs tmp save frame))
    (sassign (evar ticks) (evar now))
    (EX clock : int32, <||END (Some (Vint32 clock))||> ** (V293_time_ready_core br bg bp bn **
      V293_time_shared_locals now ticks saved bn bt bs (Vint32 clock) save frame)) tid.
Proof.
  intros Spec sd li r ri tid now ticks saved bn bt bs tmp save frame NA Free Inv.
  eapply conseq_rule with
    (p:=EX clock : int32, <||V293_time_get_action||> **
      ((V293_time_ready_fields br bg bp clock ** PV (bn,Int.zero) @ Tint32 |-> Vint32 clock) **
        V293_time_shared_locals now ticks saved bn bt bs tmp save frame)).
  - unfold V293_time_ready_core. intros s H;sep auto.
  - intros s H;exact H.
  - apply ex_intro_rule. intro clock.
    eapply conseq_rule with
      (q:=<||END (Some (Vint32 clock))||> ** (V293_time_ready_core br bg bp bn **
        V293_time_shared_locals now ticks saved bn bt bs (Vint32 clock) save frame)).
    + intros s H;exact H.
    + intros s H;exists clock;exact H.
    + eapply abscsq_rule with
        (q:=<||V293_time_get_action||> **
          ((V293_time_ready_fields br bg bp clock ** PV (bn,Int.zero) @ Tint32 |-> Vint32 clock) **
            V293_time_shared_locals now ticks saved bn bt bs (Vint32 clock) save frame)).
      * exact NA.
      * apply absinfer_eq.
      * apply V293_time_ready_get_linearize.
        unfold V293_time_shared_locals,V293_time_binding,V293_time_cell,
          V293_counter_bindings,Aptrmapsto. simpl. repeat split;auto.
      * eapply conseq_rule with
          (p:=<||V293_time_get_action||> ** (V293_time_cell true ticks bt tmp **
            (V293_time_cell false now bn (Vint32 clock) ** (V293_time_ready_fields br bg bp clock **
              (V293_time_cell true saved bs save ** frame)))))
          (q:=<||V293_time_get_action||> ** (V293_time_cell true ticks bt (Vint32 clock) **
            (V293_time_cell false now bn (Vint32 clock) ** (V293_time_ready_fields br bg bp clock **
              (V293_time_cell true saved bs save ** frame))))).
        -- unfold V293_time_shared_locals,V293_time_cell. intros s H;sep auto.
        -- unfold V293_time_shared_locals,V293_time_cell. intros s H;sep auto.
        -- apply V293_time_copy. eapply V293_star_CurLINV_r.
           eapply V293_star_CurLINV_r;exact Inv.
Qed.

Theorem V293_time_ready_get_critical : forall Spec sd li r ri tid ir si ci
    now ticks saved bn bt bs tmp save frame,
  NoAbs li -> (forall i, ir i=false) -> (gettopis si <= INUM)%nat ->
  GoodFrm frame -> (frame ==> CurLINV li tid) ->
  InfRules Spec sd li (V293_time_ready_inv br bg bp bn) r ri
    (<||V293_time_get_action||> ** OS[ir,true,si,ci] **
      V293_time_shared_locals now ticks saved bn bt bs tmp save frame)
    (sseq (sprim encrit) (sseq (sassign (evar ticks) (evar now)) (sprim excrit)))
    (EX clock : int32, <||END (Some (Vint32 clock))||> ** OS[ir,true,si,ci] **
      V293_time_shared_locals now ticks saved bn bt bs (Vint32 clock) save frame) tid.
Proof.
  intros Spec sd li r ri tid ir si ci now ticks saved bn bt bs tmp save frame NA Clear Bound GF Inv.
  eapply seq_rule with (p':=<||V293_time_get_action||> ** OS[ir,false,si,true::ci] **
    invlth_isr (V293_time_ready_inv br bg bp bn) 0 (gettopis si) **
    V293_time_shared_locals now ticks saved bn bt bs tmp save frame).
  - eapply conseq_rule with
      (p:=<||V293_time_get_action||> ** OS[ir,true,si,ci] ** ATopis (gettopis si) **
        [| (gettopis si <= INUM)%nat |] ** V293_time_shared_locals now ticks saved bn bt bs tmp save frame).
    + intros s H. assert (S : s |= Ais si ** Atrue) by (sep auto).
      pose proof (V293_time_topis si Atrue s S) as Top.
      apply astar_l_atopis_elim in Top. destruct Top as [Top _].
      pose proof (@astar_l_atopis_intro s (gettopis si) _ H Top) as HT.
      clear H. rename HT into H. sep auto.
    + intros s H;exact H.
    + apply encrit1_rule. apply V293_time_locals_good;exact GF.
  - eapply seq_rule with (p':=EX clock : int32, <||END (Some (Vint32 clock))||> ** OS[ir,false,si,true::ci] **
      V293_time_ready_core br bg bp bn **
      V293_time_shared_locals now ticks saved bn bt bs (Vint32 clock) save frame).
    + eapply conseq_rule with
        (p:=<||V293_time_get_action||> ** (V293_time_ready_core br bg bp bn **
          V293_time_shared_locals now ticks saved bn bt bs tmp save (frame ** OS[ir,false,si,true::ci])))
        (q:=EX clock : int32, <||END (Some (Vint32 clock))||> ** (V293_time_ready_core br bg bp bn **
          V293_time_shared_locals now ticks saved bn bt bs (Vint32 clock) save (frame ** OS[ir,false,si,true::ci]))).
      * intros s H.
        assert (P : s |= (Aisr ir ** invlth_isr (V293_time_ready_inv br bg bp bn) 0 (gettopis si)) **
          (<||V293_time_get_action||> ** (Aie false ** (Ais si ** (Acs (true::ci) **
            V293_time_shared_locals now ticks saved bn bt bs tmp save frame))))) by (sep auto).
        eapply astar_mono in P;[ | apply V293_time_ready_irq_open_asrt;exact Clear | intros st H0;exact H0].
        clear H. unfold V293_time_shared_locals in *. sep auto.
      * unfold V293_time_shared_locals. intros s H;sep auto.
      * apply V293_time_ready_get_copy; [exact NA | | ].
        -- simpl. split; [ | repeat split].
           clear -GF. induction frame; simpl in *; intuition eauto.
        -- eapply V293_star_CurLINV_l;exact Inv.
    + eapply conseq_rule with
        (p:=EX clock : int32, <||END (Some (Vint32 clock))||> ** OS[ir,false,si,true::ci] **
          V293_time_ready_core br bg bp bn ** V293_time_shared_locals now ticks saved bn bt bs (Vint32 clock) save frame).
      * intros s H;exact H.
      * intros s H;exact H.
      * apply ex_intro_rule. intro clock.
        eapply conseq_rule with
          (p:=<||END (Some (Vint32 clock))||> ** OS[ir,false,si,true::ci] ** ATopis (gettopis si) **
            invlth_isr (V293_time_ready_inv br bg bp bn) 0 (gettopis si) **
            V293_time_shared_locals now ticks saved bn bt bs (Vint32 clock) save frame)
          (q:=<||END (Some (Vint32 clock))||> ** OS[ir,true,si,ci] **
            V293_time_shared_locals now ticks saved bn bt bs (Vint32 clock) save frame).
        -- intros s H.
           assert (P : s |= (Aisr ir ** V293_time_ready_core br bg bp bn) **
            (<||END (Some (Vint32 clock))||> ** (Aie false ** (Ais si ** (Acs (true::ci) **
              V293_time_shared_locals now ticks saved bn bt bs (Vint32 clock) save frame))))) by (sep auto).
           eapply astar_mono in P;[ | apply V293_time_ready_irq_close_asrt;exact Clear | intros st H0;exact H0].
           clear H. rename P into H.
           assert (S : s |= Ais si ** Atrue) by (sep auto).
           pose proof (V293_time_topis si Atrue s S) as Top.
           apply astar_l_atopis_elim in Top. destruct Top as [Top _].
           pose proof (@astar_l_atopis_intro s (gettopis si) _ H Top) as HT.
           clear H. rename HT into H. sep auto.
        -- intros s H;sep auto.
        -- apply excrit1_rule;[apply V293_time_locals_good;exact GF | apply V293_time_locals_inv;exact Inv].
Qed.

Theorem V293_OSTimeGet_ready_body : forall Spec sd li tid ir si ci
    now ticks saved bn bt bs tmp save frame,
  NoAbs li -> (forall i, ir i=false) -> (gettopis si <= INUM)%nat ->
  GoodFrm frame -> (frame ==> CurLINV li tid) ->
  InfRules Spec sd li (V293_time_ready_inv br bg bp bn)
    (fun result => EX clock : int32, [| result = Some (Vint32 clock) |] **
      (<||END (Some (Vint32 clock))||> ** OS[ir,true,si,ci] **
        V293_time_shared_locals now ticks saved bn bt bs (Vint32 clock) (Vint32 Int.zero) frame))
    Afalse
    (<||V293_time_get_action||> ** OS[ir,true,si,ci] **
      V293_time_shared_locals now ticks saved bn bt bs tmp save frame)
    (V293_TimeGet_body now ticks saved) Afalse tid.
Proof.
  intros Spec sd li tid ir si ci now ticks saved bn bt bs tmp save frame NA Clear Bound GF Inv.
  unfold V293_TimeGet_body.
  eapply seq_rule with (p':=<||V293_time_get_action||> ** OS[ir,true,si,ci] **
    V293_time_shared_locals now ticks saved bn bt bs tmp (Vint32 Int.zero) frame).
  - eapply conseq_rule;[ | | apply (V293_time_zero _ _ _ _ _ _ _ V293_time_get_action
      (V293_time_binding false now bn ** (V293_time_cell true ticks bt tmp **
        (frame ** OS[ir,true,si,ci]))) saved bs save)].
    + unfold V293_time_shared_locals. intros s H;sep auto.
    + unfold V293_time_shared_locals. intros s H;sep auto.
    + eapply V293_star_CurLINV_r. eapply V293_star_CurLINV_r.
      eapply V293_star_CurLINV_l;exact Inv.
  - eapply seq_rule with (p':=EX clock : int32, <||END (Some (Vint32 clock))||> ** OS[ir,true,si,ci] **
      V293_time_shared_locals now ticks saved bn bt bs (Vint32 clock) (Vint32 Int.zero) frame).
    + apply V293_time_ready_get_critical;assumption.
    + apply ex_intro_rule. intro clock.
      eapply rete_rule with (v:=Vint32 clock) (t:=Tint32).
      intros s LocalSnapshot. split.
      * exists clock. apply astar_l_apure_intro;[exact LocalSnapshot | reflexivity].
      * assert (C : s |= V293_time_cell true ticks bt (Vint32 clock) ** Atrue).
        { unfold V293_time_shared_locals in LocalSnapshot. clear -LocalSnapshot. sep auto. }
        destruct (V293_time_cell_read true ticks bt clock Atrue s C) as [Value Ty].
        split;[exact Value | split;[exact Ty | discriminate]].
Qed.

Theorem V293_TimeGet_ready_api_contract : forall P f Spec sd li lg tid vl pre post now ticks saved bn,
  ticks <> saved -> now <> ticks -> now <> saved ->
  GoodLInvAsrt li -> NoAbs li ->
  (forall t args, p_local li t args ==> Agvarenv now Tint32 (bn,0%Z) ** p_local li t args) ->
  P f=Some (V293_TimeGet_function now ticks saved) ->
  Some pre=BuildPreA' P f V293_TimeGet_api vl li tid lg ->
  Some post=BuildRetA' P f V293_TimeGet_api vl li tid lg ->
  InfRules Spec sd li (V293_time_ready_inv br bg bp bn) post Afalse pre
    (V293_TimeGet_body now ticks saved) Afalse tid.
Proof.
  intros P f Spec sd li lg tid vl pre post now ticks saved bn TS NT NS Good NA Globals Code Pre Post.
  unfold BuildPreA' in Pre. rewrite Code in Pre.
  cbn [V293_TimeGet_function] in Pre.
  destruct vl as [ | v vl].
  2:{ cbn [dl_vl_match] in Pre.
      assert (Nonempty : rev (v::vl) <> nil).
      { intro E. apply (f_equal (@rev val)) in E. rewrite rev_involutive in E. discriminate. }
      destruct (rev (v::vl));[contradiction | discriminate]. }
  assert (TSb : Zeq_bool ticks saved=false).
  { destruct (Zeq_bool ticks saved) eqn:E;[apply Zeq_bool_eq in E;contradiction | reflexivity]. }
  cbn [dl_vl_match inferules.dladd revlcons buildp good_decllist in_decllist] in Pre.
  rewrite TSb in Pre. cbn [V293_TimeGet_api fst] in Pre. inversion Pre;subst pre.
  unfold BuildRetA' in Post. rewrite Code in Post.
  cbn [V293_TimeGet_function inferules.dladd revlcons buildq good_decllist in_decllist] in Post.
  rewrite TSb in Post. cbn in Post. inversion Post;subst post.
  eapply conseq_rule;[apply (V293_time_get_api_entry now ticks saved bn li tid lg NT NS (Globals tid lg)) | intros s H;exact H | ].
  apply ex_intro_rule. intro bt. apply ex_intro_rule. intro bs.
  apply ex_intro_rule. intro tmp. apply ex_intro_rule. intro save.
  eapply r_conseq_rule.
  3:{ apply V293_OSTimeGet_ready_body;
    [exact NA | reflexivity | cbn;lia | apply V293_time_api_frame_good;exact Good | apply V293_time_api_frame_local]. }
  - intros result s [clock H]. eapply V293_time_get_api_return;exact H.
  - intros s H;exact H.
Qed.
Lemma V293_time_ready_set_close : forall sd bn old n frame,
  can_change_aop frame ->
  absinfer sd
    (<||V293_time_set_action n||> **
      ((V293_time_ready_fields br bg bp old ** PV (bn,Int.zero) @ Tint32 |-> Vint32 n) ** frame))
    (<||END None||> ** (V293_time_ready_core br bg bp bn ** frame)).
Proof.
  intros sd bn old n frame Free.
  eapply absinfer_conseq with
    (p:=<||V293_time_set_action n||> ** (Aabsdata ostmid (ostm old) **
      ((EX t : tid, EX ts : TcbMod.map, EX es : EcbMod.map,
        CurTid t ** (Aabsdata curtid (oscurt t) **
          (Aabsdata abstcblsid (abstcblist ts) ** Aabsdata absecblsid (absecblist es))) **
        V293_ready_payload br bg bp ts) **
        (PV (bn,Int.zero) @ Tint32 |-> Vint32 n ** frame))))
    (q:=<||END None||> ** (Aabsdata ostmid (ostm n) **
      ((EX t : tid, EX ts : TcbMod.map, EX es : EcbMod.map,
        CurTid t ** (Aabsdata curtid (oscurt t) **
          (Aabsdata abstcblsid (abstcblist ts) ** Aabsdata absecblsid (absecblist es))) **
        V293_ready_payload br bg bp ts) **
        (PV (bn,Int.zero) @ Tint32 |-> Vint32 n ** frame)))).
  - unfold V293_time_ready_core,V293_time_ready_fields,V293_shared_fields.
    intros s H;sep auto.
  - apply V293_time_set_absinfer.
    split.
    + intros t ts es. split.
      * unfold CurTid,Agvarmapsto,Aptrmapsto. simpl;auto.
      * split;[simpl;auto | apply ready_action_free;apply V293_ready_payload_good].
    + simpl;auto.
  - unfold V293_time_ready_fields,V293_shared_fields. intros s H;sep auto.
Qed.

Theorem V293_time_ready_set_copy : forall Spec sd li r ri tid now ticks saved bn bt bs n save frame,
  NoAbs li -> can_change_aop frame -> (frame ==> CurLINV li tid) ->
  InfRules Spec sd li (V293_time_ready_inv br bg bp bn) r ri
    (<||V293_time_set_action n||> ** (V293_time_ready_core br bg bp bn **
      V293_time_shared_locals now ticks saved bn bt bs (Vint32 n) save frame))
    (sassign (evar now) (evar ticks))
    (<||END None||> ** (V293_time_ready_core br bg bp bn **
      V293_time_shared_locals now ticks saved bn bt bs (Vint32 n) save frame)) tid.
Proof.
  intros Spec sd li r ri tid now ticks saved bn bt bs n save frame NA Free Inv.
  eapply conseq_rule with
    (p:=EX old : int32, <||V293_time_set_action n||> **
      ((V293_time_ready_fields br bg bp old ** PV (bn,Int.zero) @ Tint32 |-> Vint32 old) **
        V293_time_shared_locals now ticks saved bn bt bs (Vint32 n) save frame)).
  - unfold V293_time_ready_core. intros s H;sep auto.
  - intros s H;exact H.
  - apply ex_intro_rule. intro old.
    eapply abscsq_rule with
      (p:=<||V293_time_set_action n||> **
        ((V293_time_ready_fields br bg bp old ** PV (bn,Int.zero) @ Tint32 |-> Vint32 old) **
          V293_time_shared_locals now ticks saved bn bt bs (Vint32 n) save frame))
      (q:=<||V293_time_set_action n||> **
        ((V293_time_ready_fields br bg bp old ** PV (bn,Int.zero) @ Tint32 |-> Vint32 n) **
          V293_time_shared_locals now ticks saved bn bt bs (Vint32 n) save frame)).
    + exact NA.
    + apply absinfer_eq.
    + apply V293_time_ready_set_close.
      unfold V293_time_shared_locals,V293_time_binding,V293_time_cell,V293_counter_bindings,Aptrmapsto.
      simpl. repeat split;auto.
    + eapply conseq_rule with
        (p:=<||V293_time_set_action n||> **
          (V293_time_cell false now bn (Vint32 old) **
            (V293_time_cell true ticks bt (Vint32 n) **
              (V293_time_ready_fields br bg bp old ** (V293_time_cell true saved bs save ** frame)))))
        (q:=<||V293_time_set_action n||> **
          (V293_time_cell false now bn (Vint32 n) **
            (V293_time_cell true ticks bt (Vint32 n) **
              (V293_time_ready_fields br bg bp old ** (V293_time_cell true saved bs save ** frame))))).
      * unfold V293_time_shared_locals,V293_time_cell. intros s H;sep auto.
      * unfold V293_time_shared_locals,V293_time_cell. intros s H;sep auto.
      * apply V293_time_copy. eapply V293_star_CurLINV_r.
        eapply V293_star_CurLINV_r;exact Inv.
Qed.

Theorem V293_time_ready_set_critical : forall Spec sd li r ri tid ir si ci
    now ticks saved bn bt bs n save frame,
  NoAbs li -> (forall i, ir i=false) -> (gettopis si <= INUM)%nat ->
  GoodFrm frame -> (frame ==> CurLINV li tid) ->
  InfRules Spec sd li (V293_time_ready_inv br bg bp bn) r ri
    (<||V293_time_set_action n||> ** OS[ir,true,si,ci] **
      V293_time_shared_locals now ticks saved bn bt bs (Vint32 n) save frame)
    (sseq (sprim encrit) (sseq (sassign (evar now) (evar ticks)) (sprim excrit)))
    (<||END None||> ** OS[ir,true,si,ci] **
      V293_time_shared_locals now ticks saved bn bt bs (Vint32 n) save frame) tid.
Proof.
  intros Spec sd li r ri tid ir si ci now ticks saved bn bt bs n save frame NA Clear Bound GF Inv.
  eapply seq_rule with (p':=<||V293_time_set_action n||> ** OS[ir,false,si,true::ci] **
    invlth_isr (V293_time_ready_inv br bg bp bn) 0 (gettopis si) **
    V293_time_shared_locals now ticks saved bn bt bs (Vint32 n) save frame).
  - eapply conseq_rule with
      (p:=<||V293_time_set_action n||> ** OS[ir,true,si,ci] ** ATopis (gettopis si) **
        [| (gettopis si <= INUM)%nat |] **
          V293_time_shared_locals now ticks saved bn bt bs (Vint32 n) save frame).
    + intros s H. assert (S : s |= Ais si ** Atrue) by (sep auto).
      pose proof (V293_time_topis si Atrue s S) as Top.
      apply astar_l_atopis_elim in Top. destruct Top as [Top _].
      pose proof (@astar_l_atopis_intro s (gettopis si) _ H Top) as HT.
      clear H. rename HT into H. sep auto.
    + intros s H;exact H.
    + apply encrit1_rule. apply V293_time_locals_good;exact GF.
  - eapply seq_rule with (p':=<||END None||> ** OS[ir,false,si,true::ci] **
      V293_time_ready_core br bg bp bn **
      V293_time_shared_locals now ticks saved bn bt bs (Vint32 n) save frame).
    + eapply conseq_rule with
        (p:=<||V293_time_set_action n||> ** (V293_time_ready_core br bg bp bn **
          V293_time_shared_locals now ticks saved bn bt bs (Vint32 n) save
            (frame ** OS[ir,false,si,true::ci])))
        (q:=<||END None||> ** (V293_time_ready_core br bg bp bn **
          V293_time_shared_locals now ticks saved bn bt bs (Vint32 n) save
            (frame ** OS[ir,false,si,true::ci]))).
      * intros s H.
        assert (P : s |= (Aisr ir ** invlth_isr (V293_time_ready_inv br bg bp bn) 0 (gettopis si)) **
          (<||V293_time_set_action n||> ** (Aie false ** (Ais si ** (Acs (true::ci) **
            V293_time_shared_locals now ticks saved bn bt bs (Vint32 n) save frame))))) by (sep auto).
        eapply astar_mono in P;[ | apply V293_time_ready_irq_open_asrt;exact Clear | intros st H0;exact H0].
        clear H. unfold V293_time_shared_locals in *. sep auto.
      * unfold V293_time_shared_locals. intros s H;sep auto.
      * apply V293_time_ready_set_copy;[exact NA | | ].
        -- simpl. split;[ | repeat split].
           clear -GF. induction frame; simpl in *; intuition eauto.
        --
        eapply V293_star_CurLINV_l;exact Inv.
    + eapply conseq_rule with
        (p:=<||END None||> ** OS[ir,false,si,true::ci] ** ATopis (gettopis si) **
          invlth_isr (V293_time_ready_inv br bg bp bn) 0 (gettopis si) **
          V293_time_shared_locals now ticks saved bn bt bs (Vint32 n) save frame).
      * intros s H.
        assert (P : s |= (Aisr ir ** V293_time_ready_core br bg bp bn) **
          (<||END None||> ** (Aie false ** (Ais si ** (Acs (true::ci) **
            V293_time_shared_locals now ticks saved bn bt bs (Vint32 n) save frame))))) by (sep auto).
        eapply astar_mono in P;[ | apply V293_time_ready_irq_close_asrt;exact Clear | intros st H0;exact H0].
        clear H. rename P into H.
        assert (S : s |= Ais si ** Atrue) by (sep auto).
        pose proof (V293_time_topis si Atrue s S) as Top.
        apply astar_l_atopis_elim in Top. destruct Top as [Top _].
        pose proof (@astar_l_atopis_intro s (gettopis si) _ H Top) as HT.
        clear H. rename HT into H. sep auto.
      * intros s H;exact H.
      * apply excrit1_rule;[apply V293_time_locals_good;exact GF | apply V293_time_locals_inv;exact Inv].
Qed.

(* Stable full normalized setter body, with already allocated locals.
   No claim that the global clock stays n after interrupts are re-enabled. *)
Theorem V293_OSTimeSet_ready_body : forall Spec sd li tid ir si ci
    now ticks saved bn bt bs n save frame,
  NoAbs li -> (forall i, ir i=false) -> (gettopis si <= INUM)%nat ->
  GoodFrm frame -> (frame ==> CurLINV li tid) ->
  InfRules Spec sd li (V293_time_ready_inv br bg bp bn)
    (fun result => [| result = None |] **
      (<||END None||> ** OS[ir,true,si,ci] **
        V293_time_shared_locals now ticks saved bn bt bs (Vint32 n) (Vint32 Int.zero) frame))
    Afalse
    (<||V293_time_set_action n||> ** OS[ir,true,si,ci] **
      V293_time_shared_locals now ticks saved bn bt bs (Vint32 n) save frame)
    (V293_TimeSet_body now ticks saved) Afalse tid.
Proof.
  intros Spec sd li tid ir si ci now ticks saved bn bt bs n save frame NA Clear Bound GF Inv.
  unfold V293_TimeSet_body.
  eapply seq_rule with (p':=<||V293_time_set_action n||> ** OS[ir,true,si,ci] **
    V293_time_shared_locals now ticks saved bn bt bs (Vint32 n) (Vint32 Int.zero) frame).
  - eapply conseq_rule;[ | | apply (V293_time_zero _ _ _ _ _ _ _ (V293_time_set_action n)
      (V293_time_binding false now bn ** (V293_time_cell true ticks bt (Vint32 n) **
        (frame ** OS[ir,true,si,ci]))) saved bs save)].
    + unfold V293_time_shared_locals. intros s H;sep auto.
    + unfold V293_time_shared_locals. intros s H;sep auto.
    + eapply V293_star_CurLINV_r. eapply V293_star_CurLINV_r.
      eapply V293_star_CurLINV_l;exact Inv.
  - eapply seq_rule with (p':=<||END None||> ** OS[ir,true,si,ci] **
      V293_time_shared_locals now ticks saved bn bt bs (Vint32 n) (Vint32 Int.zero) frame).
    + apply V293_time_ready_set_critical;assumption.
    + apply ret_rule. intros s H. apply astar_l_apure_intro;[exact H | reflexivity].
Qed.

Theorem V293_TimeSet_ready_api_contract : forall P f Spec sd li lg tid vl pre post now ticks saved bn,
  ticks <> saved -> now <> ticks -> now <> saved ->
  GoodLInvAsrt li -> NoAbs li ->
  (forall t args, p_local li t args ==> Agvarenv now Tint32 (bn,0%Z) ** p_local li t args) ->
  P f=Some (V293_TimeSet_function now ticks saved) ->
  Some pre=BuildPreA' P f V293_TimeSet_api vl li tid lg ->
  Some post=BuildRetA' P f V293_TimeSet_api vl li tid lg ->
  InfRules Spec sd li (V293_time_ready_inv br bg bp bn) post Afalse pre
    (V293_TimeSet_body now ticks saved) Afalse tid.
Proof.
  intros P f Spec sd li lg tid vl pre post now ticks saved bn TS NT NS Good NA Globals Code Pre Post.
  unfold BuildPreA' in Pre. rewrite Code in Pre.
  cbn [V293_TimeSet_function] in Pre.
  destruct (dl_vl_match (dcons ticks Tint32 dnil) (rev vl)) eqn:Match;[ | discriminate].
  destruct (V293_time_api_args ticks vl Match) as [n E]. subst vl.
  assert (TSb : Zeq_bool ticks saved=false).
  { destruct (Zeq_bool ticks saved) eqn:E;[apply Zeq_bool_eq in E;contradiction | reflexivity]. }
  cbn [inferules.dladd revlcons buildp good_decllist in_decllist] in Pre. rewrite TSb in Pre.
  cbn [V293_TimeSet_api fst] in Pre. inversion Pre;subst pre.
  unfold BuildRetA' in Post. rewrite Code in Post.
  cbn [V293_TimeSet_function inferules.dladd revlcons buildq good_decllist in_decllist] in Post. rewrite TSb in Post.
  cbn in Post. inversion Post;subst post.
  eapply conseq_rule;[apply (V293_time_api_entry now ticks saved bn li tid lg n NT NS (Globals tid lg)) | intros s H;exact H | ].
  apply ex_intro_rule. intro bt. apply ex_intro_rule. intro bs. apply ex_intro_rule. intro save.
  eapply r_conseq_rule.
  3: { apply V293_OSTimeSet_ready_body;
    [exact NA | reflexivity | cbn;lia | apply V293_time_api_frame_good;exact Good | apply V293_time_api_frame_local]. }
  - intro result. apply V293_time_api_return.
  - intros s H;exact H.
Qed.

Theorem V293_time_ready_names_good : forall now bn,
  GoodI (V293_time_ready_inv br bg bp bn) V293_scheduler (V293_time_names_li now bn).
Proof.
  intros now bn. destruct (V293_time_ready_good br bg bp bn) as [Frame [Current [Switch Sched]]].
  split;[exact Frame | ]. split;[exact Current | ]. split;[ | exact Sched].
  intros o O op t b tp M' ct Hs Highest GE Store.
  destruct (Switch o O op t b tp M' ct Hs Highest GE Store) as [tls [Table [Live | Dead]]].
  - exists tls. split;[exact Table | ]. left;exact Live.
  - exists tls. split;[exact Table | ]. right. destruct Dead as [Absent Return].
    split;[exact Absent | ]. intros Mx Ox MM OO Local JM JO.
    assert (Empty : Mx=emp /\ Ox=emp).
    { specialize (Local op). destruct Local as [lg Local].
      apply V293_time_names_footprint in Local.
      destruct o as [[[[ge le] M] ir] aux]. exact Local. }
    destruct Empty as [EM EO]. subst Mx Ox.
    apply Return with (Mx:=emp) (Ox:=emp).
    + intro action. exists (nil:list logicvar).
      destruct o as [[[[ge le] M] ir] aux]. split;reflexivity.
    + exact JM.
    + exact JO.
Qed.

End ReadyAPI.

Theorem V293_ready_clock_WFAPI : forall br bg bp version settime gettime now ticks saved bn
    Spec sd li lg,
  ticks <> saved -> now <> ticks -> now <> saved ->
  GoodLInvAsrt li -> NoAbs li ->
  (forall t args, p_local li t args ==>
    Agvarenv now Tint32 (bn,0%Z) ** p_local li t args) ->
  WFAPI (V293_clock_api_unit version settime gettime now ticks saved)
    (V293_clock_api_spec version settime gettime) li Spec sd
    (V293_time_ready_inv br bg bp bn) lg.
Proof.
  intros br bg bp version settime gettime now ticks saved bn Spec sd li lg TS NT NS Good NA Names.
  split; [apply V293_clock_api_domains | ].
  intros f ab vl pre post ft tid API Pre Post.
  unfold V293_clock_api_spec in API.
  destruct (Z.eq_dec f version) as [Version | NotVersion].
  - inversion API; subst ab ft.
    assert (Code : V293_clock_api_unit version settime gettime now ticks saved f =
      Some V293_OSVersion_function).
    { unfold V293_clock_api_unit, V293_component_api_unit, pumerge, V293_OSVersion_api_unit.
      destruct (Z.eq_dec f version); [reflexivity | contradiction]. }
    exists Tint16. exists dnil. exists dnil. exists V293_OSVersion_body.
    split; [exact Code | ]. eapply V293_OSVersion_api_contract; eassumption.
  - destruct (Z.eq_dec f settime) as [SetTime | NotSet].
    + inversion API; subst ab ft.
      assert (Code : V293_clock_api_unit version settime gettime now ticks saved f =
        Some (V293_TimeSet_function now ticks saved)).
      { unfold V293_clock_api_unit, V293_component_api_unit, pumerge,
          V293_OSVersion_api_unit, V293_TimeSet_api_unit.
        destruct (Z.eq_dec f version), (Z.eq_dec f settime);
          try contradiction; reflexivity. }
      exists Tvoid. exists (dcons ticks Tint32 dnil). exists (dcons saved Tint32 dnil).
      exists (V293_TimeSet_body now ticks saved). split; [exact Code | ].
      eapply V293_TimeSet_ready_api_contract; eassumption.
    + destruct (Z.eq_dec f gettime) as [GetTime | Missing]; [ | discriminate].
      inversion API; subst ab ft.
      assert (Code : V293_clock_api_unit version settime gettime now ticks saved f =
        Some (V293_TimeGet_function now ticks saved)).
      { unfold V293_clock_api_unit, V293_component_api_unit, pumerge,
          V293_OSVersion_api_unit, V293_TimeSet_api_unit, V293_TimeGet_api_unit.
        destruct (Z.eq_dec f version), (Z.eq_dec f settime), (Z.eq_dec f gettime);
          try contradiction; reflexivity. }
      exists Tint32. exists dnil. exists (dcons ticks Tint32 (dcons saved Tint32 dnil)).
      exists (V293_TimeGet_body now ticks saved). split; [exact Code | ].
      eapply V293_TimeGet_ready_api_contract; eassumption.
Qed.

(* Same three API bodies, internal Spec, scheduler and name-local resource.
   This partial component is not a full kernel installation or initialization. *)
Theorem V293_ready_clock_components_checked : forall version settime gettime sched
    now ticks saved bn unmap group rows high y bt bg br bp bh lg,
  version <> settime -> gettime <> version -> gettime <> settime ->
  sched <> version -> sched <> settime -> sched <> gettime ->
  ticks <> saved -> now <> ticks -> now <> saved ->
  unmap <> y -> group <> y -> rows <> y -> high <> y ->
  let li := V293_time_names_li now bn in
  let Spec := V293_OSSchedNew_internal_spec sched unmap group rows high bt bg br bh
    li (V293_time_names_local_good now bn) in
  GoodI (V293_time_ready_inv br bg bp bn) V293_scheduler li /\
  WFAPI (V293_clock_api_unit version settime gettime now ticks saved)
    (V293_clock_api_spec version settime gettime) li Spec V293_scheduler
    (V293_time_ready_inv br bg bp bn) lg /\
  WFIFun (V293_OSSchedNew_internal_unit sched unmap group rows high y)
    Spec V293_scheduler (V293_time_ready_inv br bg bp bn) li /\
  no_fun_same (V293_clock_api_unit version settime gettime now ticks saved)
    (V293_OSSchedNew_internal_unit sched unmap group rows high y).
Proof.
  intros version settime gettime sched now ticks saved bn unmap group rows high y
    bt bg br bp bh lg VT GetVersion GetSet SV ST SG TS NT NS UY GY RY HY li Spec.
  split;[apply V293_time_ready_names_good | ]. split.
  - apply V293_ready_clock_WFAPI;try assumption.
    + apply V293_time_names_local_good.
    + apply V293_time_names_noabs.
    + apply V293_time_names_global.
  - split;[ | apply V293_clock_disjoint;assumption].
    destruct (V293_OSSchedNew_WFFunEnv sched unmap group rows high y bt bg br bh li
      (V293_time_names_local_good now bn) V293_scheduler
      (V293_time_ready_inv br bg bp bn) UY GY RY HY) as [Dom Bodies].
    split;[exact Dom | ]. intros f pre post t tl Lookup.
    destruct (Bodies f pre post t tl Lookup) as
      (d1 & d2 & body & Code & Types & Decls & Checked).
    exists d1. exists d2. exists body. auto.
Qed.
