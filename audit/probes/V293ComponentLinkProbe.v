(* Independent nonempty bindings and a SATISFIABLE actual internal builder,
   using the SAME name-local invariant as the linked API component. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.toptheorem.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.certiucos.v293.proofs.V293ComponentLink.
Require Import CertiOS.certiucos.v293.proofs.V293TimeNamesGood.
Require Import CertiOS.certiucos.v293.proofs.V293TimeShared.
Require Import CertiOS.certiucos.v293.proofs.V293TimeSetAPI.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternalWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.certiucos.v293.code.V293OSVersion.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Local Open Scope nat_scope.

Definition LinkLI := V293_time_names_li 1001%Z 80%positive.
Definition LinkSpec := V293_OSSchedNew_internal_spec 200%Z 100%Z 101%Z 102%Z 103%Z
  1%positive 2%positive 3%positive 4%positive LinkLI
  (V293_time_names_local_good 1001%Z 80%positive).
Definition LinkAPI := V293_component_api_unit 201%Z 202%Z 1001%Z 1002%Z 1003%Z.
Definition LinkInternal := V293_OSSchedNew_internal_unit 200%Z 100%Z 101%Z 102%Z 103%Z 104%Z.
Definition LinkGE := set V293_witness_ge 1001%Z (80%positive,Tint32).

Theorem checked_linked_component :
  GoodI (V293_time_shared_inv 80%positive) V293_scheduler LinkLI /\
  WFAPI LinkAPI (V293_component_api_spec 201%Z 202%Z) LinkLI LinkSpec
    V293_scheduler (V293_time_shared_inv 80%positive) nil /\
  WFIFun LinkInternal LinkSpec V293_scheduler (V293_time_shared_inv 80%positive) LinkLI /\
  no_fun_same LinkAPI LinkInternal.
Proof. apply V293_components_checked; discriminate. Qed.

Theorem checked_three_actual_bindings :
  let P := pumerge LinkAPI LinkInternal in
  P 201%Z = Some (Tint16,dnil,dnil,V293_OSVersion_body) /\
  P 202%Z = Some (V293_TimeSet_function 1001%Z 1002%Z 1003%Z) /\
  P 200%Z = Some (Tvoid,dnil,dcons 104%Z Tint8 dnil,
    V293_OSSchedNew_body 100%Z 101%Z 102%Z 103%Z 104%Z).
Proof. apply V293_component_linked_entries; discriminate. Qed.

Theorem checked_collision_actual_shadow :
  let Bad := pumerge LinkAPI
    (V293_OSSchedNew_internal_unit 201%Z 100%Z 101%Z 102%Z 103%Z 104%Z) in
  Bad 201%Z = Some V293_OSVersion_function /\
  Bad 201%Z <> Some (V293_OSSchedNew_function 100%Z 101%Z 102%Z 103%Z 104%Z).
Proof. apply V293_component_collision_shadows_internal. Qed.

Lemma LinkInputs : V293_wstate LinkGE V293_witness_le V293_witness_inputs |=
  V293_sched_inputs 1%positive 2%positive 3%positive 0 16 2.
Proof.
  eapply V293_wstate_star; [V293_witness_join | apply V293_read_bytes_witness | ].
  eapply V293_wstate_star.
  - apply map_join_merge. apply map_disjoint. intros [b i].
    destruct (Pos.eq_dec b 3%positive); [subst b; right; left | left]; V293_outside.
  - apply V293_read_bytes_witness.
  - split; [apply V293_encoded_memory_mapsto | reflexivity].
Qed.

Lemma LinkCurrent : V293_wstate LinkGE V293_witness_le V293_witness_current |=
  CurLINV LinkLI (7%positive,Int.zero).
Proof.
  exists (nil:list logicvar).
  eapply V293_wstate_star with (m1:=V293_witness_current) (m2:=emp).
  - apply map_join_emp.
  - exists Tvoid. exists 6%positive.
    eapply V293_wstate_star with (m1:=emp) (m2:=V293_witness_current).
    + apply map_join_comm;apply map_join_emp.
    + exists 6%positive. split; [vm_compute;reflexivity | repeat split;reflexivity].
    + split; [apply V293_encoded_memory_mapsto | reflexivity].
  - eapply V293_wstate_star with (m1:=emp) (m2:=emp).
    + apply map_join_emp.
    + unfold LINV,LinkLI,V293_time_names_li.
      eapply V293_wstate_star with (m1:=emp) (m2:=emp).
      * apply map_join_emp.
      * exists 80%positive. vm_compute;repeat split;reflexivity.
      * split; [apply V293_time_names_local_good | repeat split;reflexivity].
    + exact I.
Qed.

Lemma LinkBindings : V293_wstate LinkGE V293_witness_le emp |=
  V293_sched_bindings 100%Z 101%Z 102%Z 103%Z 104%Z
    1%positive 2%positive 3%positive 4%positive 5%positive.
Proof.
  unfold V293_sched_bindings. repeat split.
  - exists 1%positive. vm_compute;repeat split;reflexivity.
  - exists 2%positive. vm_compute;repeat split;reflexivity.
  - exists 3%positive. vm_compute;repeat split;reflexivity.
  - exists 4%positive. vm_compute;repeat split;reflexivity.
  - exists 5%positive. vm_compute;repeat split;reflexivity.
  - intros [v H]. vm_compute in H;discriminate.
  - intros [v H]. vm_compute in H;discriminate.
  - intros [v H]. vm_compute in H;discriminate.
  - intros [v H]. vm_compute in H;discriminate.
Qed.

Lemma LinkBodyState : V293_wstate LinkGE V293_witness_le V293_witness_memory |=
  <||spec_done None||> ** V293_sched_state
    (V293_sched_common 100%Z 101%Z 102%Z 103%Z 104%Z
      1%positive 2%positive 3%positive 4%positive 5%positive 0 16 2
      LinkLI (7%positive,Int.zero) (Aie false ** V293_sched_local_domain 104%Z))
    5%positive 4%positive (V293_byteval 0) (V293_byteval 0).
Proof.
  eapply V293_wstate_star with (m1:=emp) (m2:=V293_witness_memory).
  - apply map_join_comm;apply map_join_emp.
  - split; [reflexivity | repeat split;reflexivity].
  - eapply V293_wstate_star.
    + unfold V293_witness_memory. V293_single_join 4%positive.
    + eapply V293_wstate_star.
      * V293_single_join 5%positive.
      * eapply V293_wstate_star.
        -- V293_single_join 6%positive.
        -- eapply V293_wstate_star with (m1:=emp) (m2:=V293_witness_inputs).
           ++ apply map_join_comm;apply map_join_emp.
           ++ exact LinkBindings.
           ++ exact LinkInputs.
        -- eapply V293_wstate_star with (m1:=V293_witness_current) (m2:=emp).
           ++ apply map_join_emp.
           ++ exact LinkCurrent.
           ++ apply astar_l_aie_intro; [ | reflexivity].
              apply adomlenv_intro; [repeat split;reflexivity | apply V293_witness_local_domain].
      * split; [apply V293_encoded_memory_mapsto | reflexivity].
    + split; [apply V293_encoded_memory_mapsto | reflexivity].
Qed.

(* The builder has a satisfying state with the very same LinkLI/LinkSpec.
   This is a spatial witness, NOT initialization reachability or sat(INV). *)
Theorem checked_linked_internal_entry_nonvacuous : exists fp fq pre post s,
  LinkSpec 200%Z = Some (fp,fq,(Tvoid,nil)) /\
  Some pre = BuildPreI LinkInternal 200%Z nil V293_sched_fixture_lg fp (7%positive,Int.zero) /\
  Some post = BuildRetI LinkInternal 200%Z nil V293_sched_fixture_lg fq (7%positive,Int.zero) /\
  s |= pre.
Proof.
  eexists. eexists. eexists. eexists.
  exists (V293_wstate LinkGE V293_witness_le V293_witness_memory).
  split; [reflexivity | ]. split; [reflexivity | ]. split; [reflexivity | ].
  change (V293_wstate LinkGE V293_witness_le V293_witness_memory |=
    ((EX v:val, LV 104%Z @ Tint8 |-> v) ** Aemp) **
    V293_sched_internal_pre 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive
      0 16 LinkLI (7%positive,Int.zero) (spec_done None) ** V293_sched_local_domain 104%Z).
  pose proof LinkBodyState as H.
  change (V293_wstate LinkGE V293_witness_le V293_witness_memory |=
    <||spec_done None||> ** V293_sched_state
      (V293_sched_common 100%Z 101%Z 102%Z 103%Z 104%Z
        1%positive 2%positive 3%positive 4%positive 5%positive 0 16
        (V293_ready_group 0 16) LinkLI (7%positive,Int.zero)
        (Aie false ** V293_sched_local_domain 104%Z))
      5%positive 4%positive (V293_byteval 0) (V293_byteval 0)) in H.
  apply V293_sched_return_resource in H.
  eapply astar_mono in H.
  2:{ intros st HS;exact HS. }
  2:{ apply astar_mono; [ | intros st HS;exact HS].
      apply V293_sched_insert_bounds. split; [lia | ]. split; [lia | ].
      exists 12. vm_compute;intuition lia. }
  exact H.
Qed.
