(* Source-identical getter from V293TimeAccess; linearize while IRQ clock
   ownership is available, before excrit can allow another clock update. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeShared.
Require Import CertiOS.certiucos.v293.proofs.V293TimeSetAPI.
Require Import CertiOS.certiucos.v293.proofs.V293TimeSharedSet.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.step_prop.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Local Open Scope nat_scope.

Definition V293_time_get_step : osabstep := fun vl O result =>
  vl = nil /\ exists clock, get O ostmid = Some (ostm clock) /\
    result = (Some (Vint32 clock), O).
Definition V293_time_get_action := spec_prim nil V293_time_get_step.

Theorem V293_time_get_transition : forall sd O clock,
  get O ostmid = Some (ostm clock) ->
  spec_step sd V293_time_get_action O (END (Some (Vint32 clock))) O.
Proof.
  intros sd O clock Time. unfold V293_time_get_action.
  eapply spec_prim_step with (O:=O) (O':=O) (Of:=emp).
  - split; [reflexivity | exists clock;auto].
  - split; [intro x;tauto | ].
    intros tls Tasks. exists tls. split; [exact Tasks | intro t;tauto].
  - unfold tidsame;reflexivity.
  - apply map_join_emp.
  - apply map_join_emp.
Qed.

(* The clock slot is read, not updated; the abstract step keeps ALL O. *)
Theorem V293_time_get_absinfer : forall sd clock R,
  can_change_aop R ->
  absinfer sd
    (<||V293_time_get_action||> ** (Aabsdata ostmid (ostm clock) ** R))
    (<||END (Some (Vint32 clock))||> ** (Aabsdata ostmid (ostm clock) ** R)).
Proof.
  intros sd clock R Free. unfold V293_time_get_action.
  apply absinfer_prim; [simpl;auto | simpl;auto | ].
  intros s O op H. destruct s as [[[[ge le] M] ir] aux].
  apply astar_l_aop'_elim in H. destruct H as [Action H].
  change (op = spec_prim nil V293_time_get_step) in Action. subst op.
  assert (Time : get O ostmid = Some (ostm clock)).
  { change (get (getabst (ge,le,M,ir,aux,O,
      spec_prim nil V293_time_get_step)) ostmid = Some (ostm clock)).
    eapply V293_star_abst_get_l; [apply V293_shared_abs_get | exact H]. }
  exists O. exists (END (Some (Vint32 clock))). split.
  - eapply spec_stepS; [apply V293_time_get_transition;exact Time | apply spec_stepO].
  - apply astar_l_aop'_intro; [ | reflexivity].
    eapply change_aop_rule; [exact H | simpl;auto].
Qed.

Lemma V293_time_get_linearize : forall sd bn clock frame,
  can_change_aop frame ->
  absinfer sd
    (<||V293_time_get_action||> **
      ((V293_time_shared_fields clock ** PV (bn,Int.zero) @ Tint32 |-> Vint32 clock) ** frame))
    (<||END (Some (Vint32 clock))||> ** (V293_time_shared_core bn ** frame)).
Proof.
  intros sd bn clock frame Free.
  eapply absinfer_conseq with
    (p:=<||V293_time_get_action||> ** (Aabsdata ostmid (ostm clock) **
      ((EX t : tid, EX ts : TcbMod.map, EX es : EcbMod.map,
        CurTid t ** (Aabsdata curtid (oscurt t) **
          (Aabsdata abstcblsid (abstcblist ts) ** Aabsdata absecblsid (absecblist es)))) **
        (PV (bn,Int.zero) @ Tint32 |-> Vint32 clock ** frame))))
    (q:=<||END (Some (Vint32 clock))||> ** (Aabsdata ostmid (ostm clock) **
      ((EX t : tid, EX ts : TcbMod.map, EX es : EcbMod.map,
        CurTid t ** (Aabsdata curtid (oscurt t) **
          (Aabsdata abstcblsid (abstcblist ts) ** Aabsdata absecblsid (absecblist es)))) **
        (PV (bn,Int.zero) @ Tint32 |-> Vint32 clock ** frame)))).
  - unfold V293_time_shared_core,V293_time_shared_fields,V293_shared_fields.
    intros s H;sep auto.
  - apply V293_time_get_absinfer.
    unfold CurTid,Agvarmapsto,Aptrmapsto. simpl. repeat split;intros;auto.
  - unfold V293_time_shared_core,V293_time_shared_fields,V293_shared_fields.
    intros s H;sep auto.
Qed.

Theorem V293_time_get_copy : forall Spec sd li r ri tid now ticks saved bn bt bs tmp save frame,
  NoAbs li -> can_change_aop frame -> (frame ==> CurLINV li tid) ->
  InfRules Spec sd li (V293_time_shared_inv bn) r ri
    (<||V293_time_get_action||> ** (V293_time_shared_core bn **
      V293_time_shared_locals now ticks saved bn bt bs tmp save frame))
    (sassign (evar ticks) (evar now))
    (EX clock : int32, <||END (Some (Vint32 clock))||> ** (V293_time_shared_core bn **
      V293_time_shared_locals now ticks saved bn bt bs (Vint32 clock) save frame)) tid.
Proof.
  intros Spec sd li r ri tid now ticks saved bn bt bs tmp save frame NA Free Inv.
  eapply conseq_rule with
    (p:=EX clock : int32, <||V293_time_get_action||> **
      ((V293_time_shared_fields clock ** PV (bn,Int.zero) @ Tint32 |-> Vint32 clock) **
        V293_time_shared_locals now ticks saved bn bt bs tmp save frame)).
  - unfold V293_time_shared_core. intros s H;sep auto.
  - intros s H;exact H.
  - apply ex_intro_rule. intro clock.
    eapply conseq_rule with
      (q:=<||END (Some (Vint32 clock))||> ** (V293_time_shared_core bn **
        V293_time_shared_locals now ticks saved bn bt bs (Vint32 clock) save frame)).
    + intros s H;exact H.
    + intros s H;exists clock;exact H.
    + eapply abscsq_rule with
        (q:=<||V293_time_get_action||> **
          ((V293_time_shared_fields clock ** PV (bn,Int.zero) @ Tint32 |-> Vint32 clock) **
            V293_time_shared_locals now ticks saved bn bt bs (Vint32 clock) save frame)).
      * exact NA.
      * apply absinfer_eq.
      * apply V293_time_get_linearize.
        unfold V293_time_shared_locals,V293_time_binding,V293_time_cell,
          V293_counter_bindings,Aptrmapsto. simpl. repeat split;auto.
      * eapply conseq_rule with
          (p:=<||V293_time_get_action||> ** (V293_time_cell true ticks bt tmp **
            (V293_time_cell false now bn (Vint32 clock) ** (V293_time_shared_fields clock **
              (V293_time_cell true saved bs save ** frame)))))
          (q:=<||V293_time_get_action||> ** (V293_time_cell true ticks bt (Vint32 clock) **
            (V293_time_cell false now bn (Vint32 clock) ** (V293_time_shared_fields clock **
              (V293_time_cell true saved bs save ** frame))))).
        -- unfold V293_time_shared_locals,V293_time_cell. intros s H;sep auto.
        -- unfold V293_time_shared_locals,V293_time_cell. intros s H;sep auto.
        -- apply V293_time_copy. eapply V293_star_CurLINV_r.
           eapply V293_star_CurLINV_r;exact Inv.
Qed.

Theorem V293_time_get_critical : forall Spec sd li r ri tid ir si ci
    now ticks saved bn bt bs tmp save frame,
  NoAbs li -> (forall i, ir i=false) -> (gettopis si <= INUM)%nat ->
  GoodFrm frame -> (frame ==> CurLINV li tid) ->
  InfRules Spec sd li (V293_time_shared_inv bn) r ri
    (<||V293_time_get_action||> ** OS[ir,true,si,ci] **
      V293_time_shared_locals now ticks saved bn bt bs tmp save frame)
    (sseq (sprim encrit) (sseq (sassign (evar ticks) (evar now)) (sprim excrit)))
    (EX clock : int32, <||END (Some (Vint32 clock))||> ** OS[ir,true,si,ci] **
      V293_time_shared_locals now ticks saved bn bt bs (Vint32 clock) save frame) tid.
Proof.
  intros Spec sd li r ri tid ir si ci now ticks saved bn bt bs tmp save frame NA Clear Bound GF Inv.
  eapply seq_rule with (p':=<||V293_time_get_action||> ** OS[ir,false,si,true::ci] **
    invlth_isr (V293_time_shared_inv bn) 0 (gettopis si) **
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
      V293_time_shared_core bn **
      V293_time_shared_locals now ticks saved bn bt bs (Vint32 clock) save frame).
    + eapply conseq_rule with
        (p:=<||V293_time_get_action||> ** (V293_time_shared_core bn **
          V293_time_shared_locals now ticks saved bn bt bs tmp save (frame ** OS[ir,false,si,true::ci])))
        (q:=EX clock : int32, <||END (Some (Vint32 clock))||> ** (V293_time_shared_core bn **
          V293_time_shared_locals now ticks saved bn bt bs (Vint32 clock) save (frame ** OS[ir,false,si,true::ci]))).
      * intros s H.
        assert (P : s |= (Aisr ir ** invlth_isr (V293_time_shared_inv bn) 0 (gettopis si)) **
          (<||V293_time_get_action||> ** (Aie false ** (Ais si ** (Acs (true::ci) **
            V293_time_shared_locals now ticks saved bn bt bs tmp save frame))))) by (sep auto).
        eapply astar_mono in P;[ | apply V293_time_irq_open_asrt;exact Clear | intros st H0;exact H0].
        clear H. unfold V293_time_shared_locals in *. sep auto.
      * unfold V293_time_shared_locals. intros s H;sep auto.
      * apply V293_time_get_copy; [exact NA | | ].
        -- simpl. split; [ | repeat split].
           clear -GF. induction frame; simpl in *; intuition eauto.
        -- eapply V293_star_CurLINV_l;exact Inv.
    + eapply conseq_rule with
        (p:=EX clock : int32, <||END (Some (Vint32 clock))||> ** OS[ir,false,si,true::ci] **
          V293_time_shared_core bn ** V293_time_shared_locals now ticks saved bn bt bs (Vint32 clock) save frame).
      * intros s H;exact H.
      * intros s H;exact H.
      * apply ex_intro_rule. intro clock.
        eapply conseq_rule with
          (p:=<||END (Some (Vint32 clock))||> ** OS[ir,false,si,true::ci] ** ATopis (gettopis si) **
            invlth_isr (V293_time_shared_inv bn) 0 (gettopis si) **
            V293_time_shared_locals now ticks saved bn bt bs (Vint32 clock) save frame)
          (q:=<||END (Some (Vint32 clock))||> ** OS[ir,true,si,ci] **
            V293_time_shared_locals now ticks saved bn bt bs (Vint32 clock) save frame).
        -- intros s H.
           assert (P : s |= (Aisr ir ** V293_time_shared_core bn) **
            (<||END (Some (Vint32 clock))||> ** (Aie false ** (Ais si ** (Acs (true::ci) **
              V293_time_shared_locals now ticks saved bn bt bs (Vint32 clock) save frame))))) by (sep auto).
           eapply astar_mono in P;[ | apply V293_time_irq_close_asrt;exact Clear | intros st H0;exact H0].
           clear H. rename P into H.
           assert (S : s |= Ais si ** Atrue) by (sep auto).
           pose proof (V293_time_topis si Atrue s S) as Top.
           apply astar_l_atopis_elim in Top. destruct Top as [Top _].
           pose proof (@astar_l_atopis_intro s (gettopis si) _ H Top) as HT.
           clear H. rename HT into H. sep auto.
        -- intros s H;sep auto.
        -- apply excrit1_rule;[apply V293_time_locals_good;exact GF | apply V293_time_locals_inv;exact Inv].
Qed.

Theorem V293_OSTimeGet_refined_body : forall Spec sd li tid ir si ci
    now ticks saved bn bt bs tmp save frame,
  NoAbs li -> (forall i, ir i=false) -> (gettopis si <= INUM)%nat ->
  GoodFrm frame -> (frame ==> CurLINV li tid) ->
  InfRules Spec sd li (V293_time_shared_inv bn)
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
    + apply V293_time_get_critical;assumption.
    + apply ex_intro_rule. intro clock.
      eapply rete_rule with (v:=Vint32 clock) (t:=Tint32).
      intros s LocalSnapshot. split.
      * exists clock. apply astar_l_apure_intro;[exact LocalSnapshot | reflexivity].
      * assert (C : s |= V293_time_cell true ticks bt (Vint32 clock) ** Atrue).
        { unfold V293_time_shared_locals in LocalSnapshot. clear -LocalSnapshot. sep auto. }
        destruct (V293_time_cell_read true ticks bt clock Atrue s C) as [Value Ty].
        split;[exact Value | split;[exact Ty | discriminate]].
Qed.

Definition V293_TimeGet_function now ticks saved : function :=
  (Tint32,dnil,dcons ticks Tint32 (dcons saved Tint32 dnil),
    V293_TimeGet_body now ticks saved).
Definition V293_TimeGet_api : osapi :=
  (fun _ => V293_time_get_action,(Tint32,nil)).
Definition V293_TimeGet_api_unit (fget : fid) now ticks saved : progunit :=
  fun f => if Z.eq_dec f fget then Some (V293_TimeGet_function now ticks saved) else None.

Lemma V293_time_get_api_entry : forall now ticks saved bn li tid lg,
  now <> ticks -> now <> saved ->
  (p_local li tid lg ==> Agvarenv now Tint32 (bn,0%Z) ** p_local li tid lg) ->
  ((<||V293_time_get_action||> ** p_local li tid lg **
      ((EX v : val, LV ticks @ Tint32 |-> v) ** ((EX v : val, LV saved @ Tint32 |-> v) ** Aemp)) **
      Aie true ** Ais nil ** Acs nil ** Aisr empisr) ** V293_time_api_domain ticks saved) ==>
  EX bt : block, EX bs : block, EX tmp : val, EX save : val,
    <||V293_time_get_action||> ** OS[empisr,true,nil,nil] **
      V293_time_shared_locals now ticks saved bn bt bs tmp save
        (V293_time_api_frame li tid lg ticks saved).
Proof.
  intros now ticks saved bn li tid lg NT NS Globals s H.
  assert (Split : s |= (p_local li tid lg ** V293_time_api_domain ticks saved) **
    (<||V293_time_get_action||> **
      ((EX v : val, LV ticks @ Tint32 |-> v) ** ((EX v : val, LV saved @ Tint32 |-> v) ** Aemp)) **
      Aie true ** Ais nil ** Acs nil ** Aisr empisr)) by (sep auto).
  clear H.
  eapply astar_mono in Split.
  2: { apply astar_mono;[exact Globals | intros st H;exact H]. }
  2: { intros st H;exact H. }
  assert (Names : s |= (Agvarenv now Tint32 (bn,0%Z) ** V293_time_api_domain ticks saved) **
    (p_local li tid lg ** (<||V293_time_get_action||> **
      ((EX v : val, LV ticks @ Tint32 |-> v) ** ((EX v : val, LV saved @ Tint32 |-> v) ** Aemp)) **
      Aie true ** Ais nil ** Acs nil ** Aisr empisr))) by (sep auto).
  clear Split.
  eapply astar_mono in Names;[ | apply V293_time_api_bind;assumption | intros st H;exact H].
  unfold Alvarmapsto,Alvarenv' in Names.
  unfold V293_time_shared_locals,V293_time_cell,V293_time_api_frame.
  cbn [V293_time_binding].
  sep normal in Names. sep destruct Names.
  exists x0. exists x2. exists x. exists x1. sep auto.
Qed.

Lemma V293_time_get_api_return : forall now ticks saved bn bt bs li tid lg n result,
  [| result=Some (Vint32 n) |] ** (<||END (Some (Vint32 n))||> ** OS[empisr,true,nil,nil] **
    V293_time_shared_locals now ticks saved bn bt bs (Vint32 n) (Vint32 Int.zero)
      (V293_time_api_frame li tid lg ticks saved)) ==>
  ((<||spec_done result||> ** p_local li tid lg **
    ((EX v : val, LV ticks @ Tint32 |-> v) ** ((EX v : val, LV saved @ Tint32 |-> v) ** Aemp)) **
    Aie true ** Ais nil ** Acs nil ** Aisr empisr) ** V293_time_api_domain ticks saved).
Proof.
  intros now ticks saved bn bt bs li tid lg n result s H.
  apply astar_l_apure_elim in H. destruct H as [E H]. subst result.
  unfold V293_time_shared_locals,V293_time_api_frame in H.
  (* Name-only resource is duplicable/erasable, never a discarded clock byte. *)
  assert (Pack : s |= V293_time_binding false now bn **
    ((<||END (Some (Vint32 n))||> ** p_local li tid lg **
      (V293_time_cell true ticks bt (Vint32 n) **
        (V293_time_cell true saved bs (Vint32 Int.zero) ** Aemp)) **
      Aie true ** Ais nil ** Acs nil ** Aisr empisr) ** V293_time_api_domain ticks saved)) by (sep auto).
  clear H. destruct s as [[[[[[ge le] M] ir] aux] O] op]. apply sat_split in Pack.
  destruct Pack as (m1 & m2 & o1 & o2 & JM & JO & Name & Rest).
  destruct Name as [[b [GE [Eq [EM EO]]]] _].
  change (m1=emp) in EM. change (o1=emp) in EO. subst m1 o1.
  apply map_join_comm in JM. apply map_join_emp' in JM.
  apply map_join_comm in JO. apply map_join_emp' in JO. subst m2 o2.
  assert (Cells : (ge,le,M,ir,aux,O,op) |=
    (V293_time_cell true ticks bt (Vint32 n) ** V293_time_cell true saved bs (Vint32 Int.zero)) **
      (<||END (Some (Vint32 n))||> ** p_local li tid lg ** Aie true ** Ais nil ** Acs nil ** Aisr empisr **
        V293_time_api_domain ticks saved)) by (sep auto).
  clear Rest. eapply astar_mono in Cells.
  2: { apply astar_mono;apply V293_time_api_release_cell. }
  2: { intros st H;exact H. }
  sep auto.
Qed.

(* Stable API contract: actual builders, no expected clock at entry, no
   abstract-update premise and no body-correctness premise. *)
Theorem V293_TimeGet_api_contract : forall P f Spec sd li lg tid vl pre post now ticks saved bn,
  ticks <> saved -> now <> ticks -> now <> saved ->
  GoodLInvAsrt li -> NoAbs li ->
  (forall t args, p_local li t args ==> Agvarenv now Tint32 (bn,0%Z) ** p_local li t args) ->
  P f=Some (V293_TimeGet_function now ticks saved) ->
  Some pre=BuildPreA' P f V293_TimeGet_api vl li tid lg ->
  Some post=BuildRetA' P f V293_TimeGet_api vl li tid lg ->
  InfRules Spec sd li (V293_time_shared_inv bn) post Afalse pre
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
  cbn [dl_vl_match dladd revlcons buildp good_decllist in_decllist] in Pre.
  rewrite TSb in Pre. cbn [V293_TimeGet_api fst] in Pre. inversion Pre;subst pre.
  unfold BuildRetA' in Post. rewrite Code in Post.
  cbn [V293_TimeGet_function dladd revlcons buildq good_decllist in_decllist] in Post.
  rewrite TSb in Post. cbn in Post. inversion Post;subst post.
  eapply conseq_rule;[apply (V293_time_get_api_entry now ticks saved bn li tid lg NT NS (Globals tid lg)) | intros s H;exact H | ].
  apply ex_intro_rule. intro bt. apply ex_intro_rule. intro bs.
  apply ex_intro_rule. intro tmp. apply ex_intro_rule. intro save.
  eapply r_conseq_rule.
  3:{ apply V293_OSTimeGet_refined_body;
    [exact NA | reflexivity | cbn;lia | apply V293_time_api_frame_good;exact Good | apply V293_time_api_frame_local]. }
  - intros result s [clock H]. eapply V293_time_get_api_return;exact H.
  - intros s H;exact H.
Qed.
