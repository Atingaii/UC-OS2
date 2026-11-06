(* The actual OSTime++ shares the getter/setter clock invariant.
   Only the clock prefix and stopped post-hook branch are refined here;
   running-task updates and the CPU hook are separate obligations. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeSharedSet.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickSuffix.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.
Require Import CertiOS.certiucos.v293.proofs.V293TimeShared.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.code.V293OSTimeTick.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.step_prop.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Local Open Scope nat_scope.

Definition V293_tick_clock_step : osabstep := fun vl O result =>
  vl = nil /\ exists clock, get O ostmid = Some (ostm clock) /\
    result = (None, set O ostmid (ostm (Int.add clock Int.one))).
Definition V293_tick_clock_action := spec_prim nil V293_tick_clock_step.

Theorem V293_tick_clock_transition : forall sd O clock,
  get O ostmid = Some (ostm clock) ->
  spec_step sd V293_tick_clock_action O (END None)
    (set O ostmid (ostm (Int.add clock Int.one))).
Proof.
  intros sd O clock Time. unfold V293_tick_clock_action.
  eapply spec_prim_step with (O:=O)
    (O':=set O ostmid (ostm (Int.add clock Int.one))) (Of:=emp).
  - split; [reflexivity | exists clock;auto].
  - apply eqdomO_set2 with (x:=ostm clock);[exact Time | discriminate].
  - unfold tidsame. rewrite map_get_set';[reflexivity | discriminate].
  - apply map_join_emp.
  - apply map_join_emp.
Qed.

Theorem V293_tick_clock_absinfer : forall sd clock R,
  can_change_aop R ->
  absinfer sd
    (<||V293_tick_clock_action||> ** (Aabsdata ostmid (ostm clock) ** R))
    (<||END None||> ** (Aabsdata ostmid (ostm (Int.add clock Int.one)) ** R)).
Proof.
  intros sd clock R Free. unfold V293_tick_clock_action.
  apply absinfer_prim;[simpl;auto | simpl;auto | ].
  intros s O op H. destruct s as [[[[ge le] M] ir] aux].
  apply astar_l_aop'_elim in H. destruct H as [Action H].
  change (op=spec_prim nil V293_tick_clock_step) in Action. subst op.
  assert (Time : get O ostmid = Some (ostm clock)).
  { change (get (getabst (ge,le,M,ir,aux,O,spec_prim nil V293_tick_clock_step)) ostmid = Some (ostm clock)).
    eapply V293_star_abst_get_l;[apply V293_shared_abs_get | exact H]. }
  exists (set O ostmid (ostm (Int.add clock Int.one))). exists (END None). split.
  - eapply spec_stepS;[apply V293_tick_clock_transition;exact Time | apply spec_stepO].
  - apply astar_l_aop'_intro;[ | reflexivity].
    eapply change_aop_rule;[eapply V293_shared_replace_slot;exact H | simpl;auto].
Qed.

Lemma V293_tick_clock_close : forall sd bn clock frame,
  can_change_aop frame ->
  absinfer sd
    (<||V293_tick_clock_action||> **
      ((V293_time_shared_fields clock **
        PV (bn,Int.zero) @ Tint32 |-> Vint32 (Int.add clock Int.one)) ** frame))
    (<||END None||> ** (V293_time_shared_core bn ** frame)).
Proof.
  intros sd bn clock frame Free.
  eapply absinfer_conseq with
    (p:=<||V293_tick_clock_action||> ** (Aabsdata ostmid (ostm clock) **
      ((EX t : tid, EX ts : TcbMod.map, EX es : EcbMod.map,
        CurTid t ** (Aabsdata curtid (oscurt t) **
          (Aabsdata abstcblsid (abstcblist ts) ** Aabsdata absecblsid (absecblist es)))) **
        (PV (bn,Int.zero) @ Tint32 |-> Vint32 (Int.add clock Int.one) ** frame))))
    (q:=<||END None||> ** (Aabsdata ostmid (ostm (Int.add clock Int.one)) **
      ((EX t : tid, EX ts : TcbMod.map, EX es : EcbMod.map,
        CurTid t ** (Aabsdata curtid (oscurt t) **
          (Aabsdata abstcblsid (abstcblist ts) ** Aabsdata absecblsid (absecblist es)))) **
        (PV (bn,Int.zero) @ Tint32 |-> Vint32 (Int.add clock Int.one) ** frame)))).
  - unfold V293_time_shared_core,V293_time_shared_fields,V293_shared_fields.
    intros s H;sep auto.
  - apply V293_tick_clock_absinfer.
    unfold CurTid,Agvarmapsto,Aptrmapsto. simpl. repeat split;intros;auto.
  - unfold V293_time_shared_fields,V293_shared_fields. intros s H;sep auto.
Qed.

(* Reuse the already proved unsigned increment rule, on the exact expression
   in the frozen tick AST, rather than assume evaluation or store success. *)
Theorem V293_tick_clock_write : forall Spec sd li r ri tid now bn frame,
  NoAbs li -> can_change_aop frame -> (frame ==> CurLINV li tid) ->
  InfRules Spec sd li (V293_time_shared_inv bn) r ri
    (<||V293_tick_clock_action||> ** (V293_time_shared_core bn **
      (V293_time_binding false now bn ** frame)))
    (sassign (evar now) (ebinop oplus (evar now) (econst32 Int.one)))
    (<||END None||> ** (V293_time_shared_core bn **
      (V293_time_binding false now bn ** frame))) tid.
Proof.
  intros Spec sd li r ri tid now bn frame NA Free Inv.
  eapply conseq_rule with
    (p:=EX clock : int32, <||V293_tick_clock_action||> **
      ((V293_time_shared_fields clock ** PV (bn,Int.zero) @ Tint32 |-> Vint32 clock) **
        (V293_time_binding false now bn ** frame))).
  - unfold V293_time_shared_core. intros s H;sep auto.
  - intros s H;exact H.
  - apply ex_intro_rule. intro clock.
    eapply abscsq_rule with
      (p:=<||V293_tick_clock_action||> **
        ((V293_time_shared_fields clock ** PV (bn,Int.zero) @ Tint32 |-> Vint32 clock) **
          (V293_time_binding false now bn ** frame)))
      (q:=<||V293_tick_clock_action||> **
        ((V293_time_shared_fields clock ** PV (bn,Int.zero) @ Tint32 |-> Vint32 (Int.add clock Int.one)) **
          (V293_time_binding false now bn ** frame))).
    + exact NA.
    + apply absinfer_eq.
    + apply V293_tick_clock_close.
      cbn [V293_time_binding V293_counter_bindings Aptrmapsto]. simpl. auto.
    + eapply conseq_rule with
        (p:=<||V293_tick_clock_action||> **
          ((V293_time_shared_fields clock ** frame) ** V293_counter_cell now bn clock))
        (q:=<||V293_tick_clock_action||> **
          ((V293_time_shared_fields clock ** frame) ** V293_counter_cell now bn (Int.add clock Int.one))).
      * unfold V293_time_binding,V293_counter_cell. intros s H;sep auto.
      * unfold V293_time_binding,V293_counter_cell. intros s H;sep auto.
      * apply V293_OSSched_counter_increment. eapply V293_star_CurLINV_r;exact Inv.
Qed.

(* This form preserves the original right-associated AST, including its tail.
   Tail is a separate continuation proof, never an assumed clock body. *)
Theorem V293_tick_clock_with_tail : forall Spec sd li r ri tid ir si ci now bn frame tail q,
  NoAbs li -> (forall i, ir i=false) -> (gettopis si <= INUM)%nat ->
  GoodFrm frame -> (frame ==> CurLINV li tid) ->
  InfRules Spec sd li (V293_time_shared_inv bn) r ri
    (<||END None||> ** OS[ir,true,si,ci] ** (V293_time_binding false now bn ** frame)) tail q tid ->
  InfRules Spec sd li (V293_time_shared_inv bn) r ri
    (<||V293_tick_clock_action||> ** OS[ir,true,si,ci] ** (V293_time_binding false now bn ** frame))
    (sseq (sprim encrit)
      (sseq (sassign (evar now) (ebinop oplus (evar now) (econst32 Int.one)))
        (sseq (sprim excrit) tail))) q tid.
Proof.
  intros Spec sd li r ri tid ir si ci now bn frame tail q NA Clear Bound GF Inv Tail.
  assert (GP : GoodFrm (V293_time_binding false now bn ** frame)).
  { cbn [V293_time_binding V293_counter_bindings Aptrmapsto GoodFrm];tauto. }
  eapply seq_rule with (p':=<||V293_tick_clock_action||> ** OS[ir,false,si,true::ci] **
    invlth_isr (V293_time_shared_inv bn) 0 (gettopis si) ** (V293_time_binding false now bn ** frame)).
  - eapply conseq_rule with
      (p:=<||V293_tick_clock_action||> ** OS[ir,true,si,ci] ** ATopis (gettopis si) **
        [| (gettopis si <= INUM)%nat |] ** (V293_time_binding false now bn ** frame)).
    + intros s H. assert (S : s |= Ais si ** Atrue) by (sep auto).
      pose proof (V293_time_topis si Atrue s S) as Top.
      apply astar_l_atopis_elim in Top. destruct Top as [Top _].
      pose proof (@astar_l_atopis_intro s (gettopis si) _ H Top) as HT.
      clear H. rename HT into H. sep auto.
    + intros s H;exact H.
    + apply encrit1_rule;exact GP.
  - eapply seq_rule with (p':=<||END None||> ** OS[ir,false,si,true::ci] **
      V293_time_shared_core bn ** (V293_time_binding false now bn ** frame)).
    + eapply conseq_rule with
        (p:=<||V293_tick_clock_action||> ** (V293_time_shared_core bn **
          (V293_time_binding false now bn ** (frame ** OS[ir,false,si,true::ci]))))
        (q:=<||END None||> ** (V293_time_shared_core bn **
          (V293_time_binding false now bn ** (frame ** OS[ir,false,si,true::ci])))).
      * intros s H.
        assert (P : s |= (Aisr ir ** invlth_isr (V293_time_shared_inv bn) 0 (gettopis si)) **
          (<||V293_tick_clock_action||> ** (Aie false ** (Ais si ** (Acs (true::ci) **
            (V293_time_binding false now bn ** frame)))))) by (sep auto).
        eapply astar_mono in P;[ | apply V293_time_irq_open_asrt;exact Clear | intros st H0;exact H0].
        clear H. sep auto.
      * intros s H;sep auto.
      * apply V293_tick_clock_write;[exact NA | | ].
        -- simpl. split;[ | repeat split].
           clear -GF. induction frame;simpl in *;intuition eauto.
        -- eapply V293_star_CurLINV_l;exact Inv.
    + eapply seq_rule;[ | exact Tail].
      eapply conseq_rule with
        (p:=<||END None||> ** OS[ir,false,si,true::ci] ** ATopis (gettopis si) **
          invlth_isr (V293_time_shared_inv bn) 0 (gettopis si) ** (V293_time_binding false now bn ** frame)).
      * intros s H.
        assert (P : s |= (Aisr ir ** V293_time_shared_core bn) **
          (<||END None||> ** (Aie false ** (Ais si ** (Acs (true::ci) **
            (V293_time_binding false now bn ** frame)))))) by (sep auto).
        eapply astar_mono in P;[ | apply V293_time_irq_close_asrt;exact Clear | intros st H0;exact H0].
        clear H. rename P into H.
        assert (S : s |= Ais si ** Atrue) by (sep auto).
        pose proof (V293_time_topis si Atrue s S) as Top.
        apply astar_l_atopis_elim in Top. destruct Top as [Top _].
        pose proof (@astar_l_atopis_intro s (gettopis si) _ H Top) as HT.
        clear H. rename HT into H. sep auto.
      * intros s H;exact H.
      * apply excrit1_rule;[exact GP | eapply V293_star_CurLINV_r;exact Inv].
Qed.

(* No clear-ISR hypothesis when the clock core is explicitly held already.
   This is NOT an ISR entry rule: the caller must actually supply that core. *)
Theorem V293_tick_clock_disabled : forall Spec sd li r ri tid ir si ci now bn frame,
  NoAbs li -> GoodFrm frame -> (frame ==> CurLINV li tid) ->
  InfRules Spec sd li (V293_time_shared_inv bn) r ri
    (<||V293_tick_clock_action||> ** OS[ir,false,si,ci] **
      (V293_time_shared_core bn ** (V293_time_binding false now bn ** frame)))
    (sseq (sprim encrit)
      (sseq (sassign (evar now) (ebinop oplus (evar now) (econst32 Int.one))) (sprim excrit)))
    (<||END None||> ** OS[ir,false,si,ci] **
      (V293_time_shared_core bn ** (V293_time_binding false now bn ** frame))) tid.
Proof.
  intros Spec sd li r ri tid ir si ci now bn frame NA GF Inv.
  eapply seq_rule.
  - apply encrit2_rule.
    unfold V293_time_shared_core,V293_time_shared_fields,CurTid,Agvarmapsto,
      Aptrmapsto,V293_shared_fields,V293_time_binding,V293_counter_bindings.
    simpl. repeat split;auto.
  - eapply seq_rule with (p':=<||END None||> ** OS[ir,false,si,false::ci] **
      (V293_time_shared_core bn ** (V293_time_binding false now bn ** frame))).
    + eapply conseq_rule with
        (p:=<||V293_tick_clock_action||> ** (V293_time_shared_core bn **
          (V293_time_binding false now bn ** (frame ** OS[ir,false,si,false::ci]))))
        (q:=<||END None||> ** (V293_time_shared_core bn **
          (V293_time_binding false now bn ** (frame ** OS[ir,false,si,false::ci])))).
      * intros s H;sep auto.
      * intros s H;sep auto.
      * apply V293_tick_clock_write;[exact NA | | ].
        -- simpl. split;[ | repeat split].
           clear -GF. induction frame;simpl in *;intuition eauto.
        -- eapply V293_star_CurLINV_l;exact Inv.
    + apply excrit2_rule.
      unfold V293_time_shared_core,V293_time_shared_fields,CurTid,Agvarmapsto,
        Aptrmapsto,V293_shared_fields,V293_time_binding,V293_counter_bindings.
      simpl. repeat split;auto.
Qed.

Lemma V293_tick_running_eval : forall running bu run rest s,
  run<256 -> s |= V293_guard_cell running bu run ** rest ->
  evalval (V293_tick_eq (ecast (evar running) Tint32) 1) (getsmem s) =
    Some (Vint32 (if Nat.eqb run 1 then Int.one else Int.zero)) /\
  evaltype (V293_tick_eq (ecast (evar running) Tint32) 1) (getsmem s) = Some Tint32.
Proof.
  intros running bu run rest s Range Owned.
  destruct (V293_current_variable running bu run rest s Range Owned) as [Value Ty].
  unfold V293_tick_eq. cbn [evalval evaltype] in Value,Ty |- *. rewrite Value,Ty.
  destruct (getsmem s) as [[ge le] M].
  cbn [bop_eval val_eq bop_type cmp_int_type V293_byteval].
  change ((if Int.eq (Int.repr (Z.of_nat run)) (Int.repr (Z.of_nat 1))
    then Some (Vint32 Int.one) else Some (Vint32 Int.zero)) =
    Some (Vint32 (if Nat.eqb run 1 then Int.one else Int.zero)) /\
    Some Tint32 = Some Tint32).
  rewrite (V293_byte_eq run 1 Range ltac:(lia)). destruct (Nat.eqb run 1);split;reflexivity.
Qed.

Theorem V293_tick_stopped_branch : forall Spec sd li I r ri tid p running bu run rest body,
  run<256 -> run<>1 -> (p ==> V293_guard_cell running bu run ** rest) ->
  InfRules Spec sd li I r ri p
    (sifthen (V293_tick_eq (ecast (evar running) Tint32) 1) body) p tid.
Proof.
  intros Spec sd li I r ri tid p running bu run rest body Range Stopped Owned.
  assert (No : Nat.eqb run 1=false) by (apply Nat.eqb_neq;exact Stopped).
  eapply ift_rule with (tp:=Tint32).
  - intros s H. destruct (V293_tick_running_eval running bu run rest s Range (Owned s H)) as [V T].
    exists (Vint32 (if Nat.eqb run 1 then Int.one else Int.zero)).
    split;[exact V | split;[exact T | discriminate]].
  - intros s [H _];exact H.
  - eapply conseq_rule with (p:=Afalse).
    + intros s [H [v [V True]]].
      destruct (V293_tick_running_eval running bu run rest s Range (Owned s H)) as [E _].
      rewrite No in E. rewrite E in V. inversion V;subst v. vm_compute in True;discriminate.
    + intros s H;exact H.
    + apply pfalse_rule.
Qed.

(* Stable exact post-hook suffix, not a modified clock-only tick function.
   The unexecuted branch remains the frozen original list walk. *)
Theorem V293_tick_stopped_shared_suffix : forall Spec sd li r ri tid ir si ci
    ptcb rows group now running head bn bu run frame,
  NoAbs li -> (forall i, ir i=false) -> (gettopis si <= INUM)%nat ->
  run<256 -> run<>1 -> GoodFrm frame -> (frame ==> CurLINV li tid) ->
  InfRules Spec sd li (V293_time_shared_inv bn) r ri
    (<||V293_tick_clock_action||> ** OS[ir,true,si,ci] **
      (V293_time_binding false now bn ** (V293_guard_cell running bu run ** frame)))
    (V293_tick_post_hook ptcb rows group now running head)
    (<||END None||> ** OS[ir,true,si,ci] **
      (V293_time_binding false now bn ** (V293_guard_cell running bu run ** frame))) tid.
Proof.
  intros Spec sd li r ri tid ir si ci ptcb rows group now running head bn bu run frame
    NA Clear Bound Range Stopped GF Inv.
  unfold V293_tick_post_hook. apply V293_tick_clock_with_tail.
  - exact NA.
  - exact Clear.
  - exact Bound.
  - simpl. repeat split; try apply V293_guard_cell_good; assumption.
  - eapply V293_star_CurLINV_r;exact Inv.
  - eapply V293_tick_stopped_branch with (bu:=bu) (run:=run).
    + exact Range.
    + exact Stopped.
    + intros s H;sep auto.
Qed.
