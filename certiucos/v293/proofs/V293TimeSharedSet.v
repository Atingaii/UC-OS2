(* Shared OSTimeSet: abstract time changes only through spec_prim_step.
   Same normalized C body and same IRQ invariant as the shared getter. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeShared.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.step_prop.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List.
Local Open Scope nat_scope.

Definition V293_time_set_step : osabstep := fun vl O result =>
  exists old, exists n, vl = (Vint32 n :: nil) /\
    get O ostmid = Some (ostm old) /\
    result = (None, set O ostmid (ostm n)).
Definition V293_time_set_action n := spec_prim (Vint32 n :: nil) V293_time_set_step.

Lemma V293_time_set_transition : forall sd O old n,
  get O ostmid = Some (ostm old) ->
  spec_step sd (V293_time_set_action n) O (END None) (set O ostmid (ostm n)).
Proof.
  intros sd O old n Time. unfold V293_time_set_action.
  eapply spec_prim_step with (O:=O) (O':=set O ostmid (ostm n)) (Of:=emp).
  - exists old. exists n. repeat split;auto.
  - apply eqdomO_set2 with (x:=ostm old);[exact Time | discriminate].
  - unfold tidsame. rewrite map_get_set';[reflexivity | discriminate].
  - apply map_join_emp.
  - apply map_join_emp.
Qed.

(* R may contain arbitrary physical resources and other abstract slots.
   This is a derived framework abstraction rule, not an update oracle. *)
Theorem V293_time_set_absinfer : forall sd old n R,
  can_change_aop R ->
  absinfer sd
    (<||V293_time_set_action n||> ** (Aabsdata ostmid (ostm old) ** R))
    (<||END None||> ** (Aabsdata ostmid (ostm n) ** R)).
Proof.
  intros sd old n R Free. unfold V293_time_set_action.
  apply absinfer_prim;[simpl;auto | simpl;auto | ].
  intros s O op H. destruct s as [[[[ge le] M] ir] aux].
  assert (Action : op = spec_prim (Vint32 n :: nil) V293_time_set_step).
  { apply astar_l_aop'_elim in H. exact (proj1 H). }
  subst op. apply astar_l_aop'_elim in H. destruct H as [_ H].
  assert (Time : get O ostmid = Some (ostm old)).
  { change (get (getabst (ge,le,M,ir,aux,O,
      spec_prim (Vint32 n :: nil) V293_time_set_step)) ostmid = Some (ostm old)).
    eapply V293_star_abst_get_l;[apply V293_shared_abs_get | exact H]. }
  exists (set O ostmid (ostm n)). exists (END None). split.
  - eapply spec_stepS;[apply V293_time_set_transition with (old:=old);exact Time | apply spec_stepO].
  - apply astar_l_aop'_intro;[ | reflexivity].
    eapply change_aop_rule;[eapply V293_shared_replace_slot;exact H | simpl;auto].
Qed.

(* After the physical write the two times differ temporarily. Only this
   legal abstract action makes the original shared core closable again. *)
Lemma V293_time_set_close : forall sd bn old n frame,
  can_change_aop frame ->
  absinfer sd
    (<||V293_time_set_action n||> **
      ((V293_time_shared_fields old ** PV (bn,Int.zero) @ Tint32 |-> Vint32 n) ** frame))
    (<||END None||> ** (V293_time_shared_core bn ** frame)).
Proof.
  intros sd bn old n frame Free.
  eapply absinfer_conseq with
    (p:=<||V293_time_set_action n||> ** (Aabsdata ostmid (ostm old) **
      ((EX t : tid, EX ts : TcbMod.map, EX es : EcbMod.map,
        CurTid t ** (Aabsdata curtid (oscurt t) **
          (Aabsdata abstcblsid (abstcblist ts) ** Aabsdata absecblsid (absecblist es)))) **
        (PV (bn,Int.zero) @ Tint32 |-> Vint32 n ** frame))))
    (q:=<||END None||> ** (Aabsdata ostmid (ostm n) **
      ((EX t : tid, EX ts : TcbMod.map, EX es : EcbMod.map,
        CurTid t ** (Aabsdata curtid (oscurt t) **
          (Aabsdata abstcblsid (abstcblist ts) ** Aabsdata absecblsid (absecblist es)))) **
        (PV (bn,Int.zero) @ Tint32 |-> Vint32 n ** frame)))).
  - unfold V293_time_shared_core,V293_time_shared_fields,V293_shared_fields.
    intros s H;sep auto.
  - apply V293_time_set_absinfer.
    unfold CurTid,Agvarmapsto,Aptrmapsto. simpl. repeat split;intros;auto.
  - unfold V293_time_shared_fields,V293_shared_fields. intros s H;sep auto.
Qed.

Theorem V293_time_shared_set_copy : forall Spec sd li r ri tid now ticks saved bn bt bs n save frame,
  NoAbs li -> can_change_aop frame -> (frame ==> CurLINV li tid) ->
  InfRules Spec sd li (V293_time_shared_inv bn) r ri
    (<||V293_time_set_action n||> ** (V293_time_shared_core bn **
      V293_time_shared_locals now ticks saved bn bt bs (Vint32 n) save frame))
    (sassign (evar now) (evar ticks))
    (<||END None||> ** (V293_time_shared_core bn **
      V293_time_shared_locals now ticks saved bn bt bs (Vint32 n) save frame)) tid.
Proof.
  intros Spec sd li r ri tid now ticks saved bn bt bs n save frame NA Free Inv.
  eapply conseq_rule with
    (p:=EX old : int32, <||V293_time_set_action n||> **
      ((V293_time_shared_fields old ** PV (bn,Int.zero) @ Tint32 |-> Vint32 old) **
        V293_time_shared_locals now ticks saved bn bt bs (Vint32 n) save frame)).
  - unfold V293_time_shared_core. intros s H;sep auto.
  - intros s H;exact H.
  - apply ex_intro_rule. intro old.
    eapply abscsq_rule with
      (p:=<||V293_time_set_action n||> **
        ((V293_time_shared_fields old ** PV (bn,Int.zero) @ Tint32 |-> Vint32 old) **
          V293_time_shared_locals now ticks saved bn bt bs (Vint32 n) save frame))
      (q:=<||V293_time_set_action n||> **
        ((V293_time_shared_fields old ** PV (bn,Int.zero) @ Tint32 |-> Vint32 n) **
          V293_time_shared_locals now ticks saved bn bt bs (Vint32 n) save frame)).
    + exact NA.
    + apply absinfer_eq.
    + apply V293_time_set_close.
      unfold V293_time_shared_locals,V293_time_binding,V293_time_cell,V293_counter_bindings,Aptrmapsto.
      simpl. repeat split;auto.
    + eapply conseq_rule with
        (p:=<||V293_time_set_action n||> **
          (V293_time_cell false now bn (Vint32 old) **
            (V293_time_cell true ticks bt (Vint32 n) **
              (V293_time_shared_fields old ** (V293_time_cell true saved bs save ** frame)))))
        (q:=<||V293_time_set_action n||> **
          (V293_time_cell false now bn (Vint32 n) **
            (V293_time_cell true ticks bt (Vint32 n) **
              (V293_time_shared_fields old ** (V293_time_cell true saved bs save ** frame))))).
      * unfold V293_time_shared_locals,V293_time_cell. intros s H;sep auto.
      * unfold V293_time_shared_locals,V293_time_cell. intros s H;sep auto.
      * apply V293_time_copy. eapply V293_star_CurLINV_r.
        eapply V293_star_CurLINV_r;exact Inv.
Qed.

Theorem V293_time_shared_critical_set : forall Spec sd li r ri tid ir si ci
    now ticks saved bn bt bs n save frame,
  NoAbs li -> (forall i, ir i=false) -> (gettopis si <= INUM)%nat ->
  GoodFrm frame -> (frame ==> CurLINV li tid) ->
  InfRules Spec sd li (V293_time_shared_inv bn) r ri
    (<||V293_time_set_action n||> ** OS[ir,true,si,ci] **
      V293_time_shared_locals now ticks saved bn bt bs (Vint32 n) save frame)
    (sseq (sprim encrit) (sseq (sassign (evar now) (evar ticks)) (sprim excrit)))
    (<||END None||> ** OS[ir,true,si,ci] **
      V293_time_shared_locals now ticks saved bn bt bs (Vint32 n) save frame) tid.
Proof.
  intros Spec sd li r ri tid ir si ci now ticks saved bn bt bs n save frame NA Clear Bound GF Inv.
  eapply seq_rule with (p':=<||V293_time_set_action n||> ** OS[ir,false,si,true::ci] **
    invlth_isr (V293_time_shared_inv bn) 0 (gettopis si) **
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
      V293_time_shared_core bn **
      V293_time_shared_locals now ticks saved bn bt bs (Vint32 n) save frame).
    + eapply conseq_rule with
        (p:=<||V293_time_set_action n||> ** (V293_time_shared_core bn **
          V293_time_shared_locals now ticks saved bn bt bs (Vint32 n) save
            (frame ** OS[ir,false,si,true::ci])))
        (q:=<||END None||> ** (V293_time_shared_core bn **
          V293_time_shared_locals now ticks saved bn bt bs (Vint32 n) save
            (frame ** OS[ir,false,si,true::ci]))).
      * intros s H.
        assert (P : s |= (Aisr ir ** invlth_isr (V293_time_shared_inv bn) 0 (gettopis si)) **
          (<||V293_time_set_action n||> ** (Aie false ** (Ais si ** (Acs (true::ci) **
            V293_time_shared_locals now ticks saved bn bt bs (Vint32 n) save frame))))) by (sep auto).
        eapply astar_mono in P;[ | apply V293_time_irq_open_asrt;exact Clear | intros st H0;exact H0].
        clear H. unfold V293_time_shared_locals in *. sep auto.
      * unfold V293_time_shared_locals. intros s H;sep auto.
      * apply V293_time_shared_set_copy;[exact NA | | ].
        -- simpl. split;[ | repeat split].
           clear -GF. induction frame; simpl in *; intuition eauto.
        --
        eapply V293_star_CurLINV_l;exact Inv.
    + eapply conseq_rule with
        (p:=<||END None||> ** OS[ir,false,si,true::ci] ** ATopis (gettopis si) **
          invlth_isr (V293_time_shared_inv bn) 0 (gettopis si) **
          V293_time_shared_locals now ticks saved bn bt bs (Vint32 n) save frame).
      * intros s H.
        assert (P : s |= (Aisr ir ** V293_time_shared_core bn) **
          (<||END None||> ** (Aie false ** (Ais si ** (Acs (true::ci) **
            V293_time_shared_locals now ticks saved bn bt bs (Vint32 n) save frame))))) by (sep auto).
        eapply astar_mono in P;[ | apply V293_time_irq_close_asrt;exact Clear | intros st H0;exact H0].
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
Theorem V293_OSTimeSet_shared_body : forall Spec sd li tid ir si ci
    now ticks saved bn bt bs n save frame,
  NoAbs li -> (forall i, ir i=false) -> (gettopis si <= INUM)%nat ->
  GoodFrm frame -> (frame ==> CurLINV li tid) ->
  InfRules Spec sd li (V293_time_shared_inv bn)
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
    + apply V293_time_shared_critical_set;assumption.
    + apply ret_rule. intros s H. apply astar_l_apure_intro;[exact H | reflexivity].
Qed.

Print Assumptions V293_time_set_transition.
Print Assumptions V293_time_set_absinfer.
Print Assumptions V293_time_shared_set_copy.
Print Assumptions V293_OSTimeSet_shared_body.
