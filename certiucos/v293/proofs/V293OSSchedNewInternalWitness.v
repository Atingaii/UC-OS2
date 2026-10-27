(* Concrete builder precondition witness. The empty local invariant is only
   a satisfiability fixture; the stable component theorem remains parametric. *)
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import Coq.Lists.List Lia.
Local Open Scope nat_scope.

Lemma V293_witness_local_domain :
  eq_dom_env V293_witness_le (cons (104%Z, Tint8) nil).
Proof.
  unfold eq_dom_env, V293_witness_le. intros x t.
  destruct (Z.eq_dec 104%Z x) as [E | E].
  - subst x. rewrite map_get_set. simpl. split.
    + intros [H | H]; [inversion H; subst; eexists; reflexivity | contradiction].
    + intros [b H]. inversion H; subst. left; reflexivity.
  - rewrite map_get_set' by exact E. rewrite map_emp_get. simpl. split.
    + intros [H | H]; [inversion H; congruence | contradiction].
    + intros [b H]; discriminate.
Qed.

Lemma V293_witness_internal_frame :
  V293_wstate V293_witness_ge V293_witness_le emp |=
    Aie false ** V293_sched_local_domain 104%Z.
Proof.
  apply astar_l_aie_intro; [ | reflexivity].
  apply adomlenv_intro; [split; reflexivity | apply V293_witness_local_domain].
Qed.

Lemma V293_witness_internal_body_state :
  V293_wstate V293_witness_ge V293_witness_le V293_witness_memory |=
    <||spec_done None||> ** V293_sched_state
      (V293_sched_common 100%Z 101%Z 102%Z 103%Z 104%Z
        1%positive 2%positive 3%positive 4%positive 5%positive 0 16 2
        V293_witness_li (7%positive, Int.zero) (Aie false ** V293_sched_local_domain 104%Z))
      5%positive 4%positive (V293_byteval 0) (V293_byteval 0).
Proof.
  eapply V293_wstate_star with (m1 := emp) (m2 := V293_witness_memory).
  - apply map_join_comm. apply map_join_emp.
  - split; [reflexivity | split; reflexivity].
  - eapply V293_wstate_star.
    + unfold V293_witness_memory. V293_single_join 4%positive.
    + eapply V293_wstate_star.
      * V293_single_join 5%positive.
      * eapply V293_wstate_star.
        -- V293_single_join 6%positive.
        -- eapply V293_wstate_star with (m1 := emp) (m2 := V293_witness_inputs).
           ++ apply map_join_comm. apply map_join_emp.
           ++ apply V293_witness_bindings_sat.
           ++ apply V293_witness_inputs_sat.
        -- eapply V293_wstate_star with (m1 := V293_witness_current) (m2 := emp).
           ++ apply map_join_emp.
           ++ apply V293_witness_current_sat.
           ++ apply V293_witness_internal_frame.
      * split; [apply V293_encoded_memory_mapsto | reflexivity].
    + split; [apply V293_encoded_memory_mapsto | reflexivity].
Qed.

Definition V293_sched_fixture_lg : list logicvar :=
  cons (logic_lv (cons (Vint32 (Int.repr 0)) (cons (Vint32 (Int.repr 16)) nil)))
    (cons (logic_code (spec_done None)) nil).

Lemma V293_sched_insert_bounds : forall unmap group rows high bt bg br bh lo hi li tid aop hold,
  lo < 256 /\ hi < 256 /\ (exists p, V293_bitmap_ready lo hi p) ->
  <||aop||> ** V293_sched_internal_resource unmap group rows high bt bg br bh lo hi li tid hold ==>
  V293_sched_internal_pre unmap group rows high bt bg br bh lo hi li tid aop.
Proof.
  intros unmap group rows high bt bg br bh lo hi li tid aop hold Hb s Hs.
  exists hold. apply astar_comm. apply astar_l_apure_intro; assumption.
Qed.

Theorem V293_OSSchedNew_internal_precondition_witness : exists pre post s,
  Some pre = BuildPreI (V293_OSSchedNew_internal_unit 200%Z 100%Z 101%Z 102%Z 103%Z 104%Z)
    200%Z nil V293_sched_fixture_lg
    (V293_sched_fpre 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive
      V293_witness_li V293_witness_li_good) (7%positive, Int.zero) /\
  Some post = BuildRetI (V293_OSSchedNew_internal_unit 200%Z 100%Z 101%Z 102%Z 103%Z 104%Z)
    200%Z nil V293_sched_fixture_lg
    (V293_sched_fpost 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive
      V293_witness_li V293_witness_li_good) (7%positive, Int.zero) /\
  s |= pre.
Proof.
  eexists. eexists. exists (V293_wstate V293_witness_ge V293_witness_le V293_witness_memory).
  split; [reflexivity | ]. split; [reflexivity | ].
  change (V293_wstate V293_witness_ge V293_witness_le V293_witness_memory |=
    ((EX v : val, LV 104%Z @ Tint8 |-> v) ** Aemp) **
    V293_sched_internal_pre 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive
      0 16 V293_witness_li (7%positive, Int.zero) (spec_done None) ** V293_sched_local_domain 104%Z).
  pose proof V293_witness_internal_body_state as Hs.
  change (V293_wstate V293_witness_ge V293_witness_le V293_witness_memory |=
    <||spec_done None||> ** V293_sched_state
      (V293_sched_common 100%Z 101%Z 102%Z 103%Z 104%Z 1%positive 2%positive 3%positive 4%positive
        5%positive 0 16 (V293_ready_group 0 16) V293_witness_li (7%positive, Int.zero)
        (Aie false ** V293_sched_local_domain 104%Z)) 5%positive 4%positive
        (V293_byteval 0) (V293_byteval 0)) in Hs.
  apply V293_sched_return_resource in Hs.
  eapply astar_mono in Hs.
  2: { intros s0 H0; exact H0. }
  2: { apply astar_mono; [ | intros s0 H0; exact H0].
       apply V293_sched_insert_bounds.
       split; [lia | ]. split; [lia | ]. exists 12. vm_compute; intuition lia. }
  exact Hs.
Qed.
