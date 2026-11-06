(* Same-state pending increment/switch fixture, not initialization or reachability.
   This fixture instantiates an empty extra-cell list, not all kernel globals. *)
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStorageTail.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitchWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChangeWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitch.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchState.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293SharedStateWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrentWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.sep_combine_lemmas.
Require Import Coq.Lists.List Lia.
Local Open Scope nat_scope.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitHandoffHoare.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStorageWitness.
Require Import CertiOS.audit.probes.V293OSIntExitBoundarySwitchProbe.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBoundarySwitch.
Import ListNotations.
(* Independent full-write cache cells; current task is waiting, next is ready.
   The earlier BX copy-deletion executions are a separate fixture, not this
   resource witness nor a resumption execution. *)
Definition FHge := set(set V293_storage_fixture_ge 112%Z(4%positive,Tint8))113%Z(5%positive,Tint8).
Definition FHbyte b n := V293_encoded_memory b 0 true(encode_val Tint8(V293_byteval n)).
Definition FHbytes := merge(FHbyte 4%positive 12)(FHbyte 5%positive 4).
Definition FHextra c := merge(V293_counter_memory 3%positive c)FHbytes.
Definition FHextra_owned c := V293_counter_cell 111%Z 3%positive c **
 (V293_handoff_byte 112%Z 4%positive 12 ** V293_handoff_byte 113%Z 5%positive 4).
Ltac FHoutside := unfold FHextra,FHbytes,FHbyte,V293_counter_memory,
 V293_switch_fixture_mem,V293_switch_fixture_target,V293_shared_fixture_mem;
 repeat rewrite map_merge_semp by reflexivity;
 repeat rewrite V293_encoded_memory_outside by(left;congruence);reflexivity.
Lemma FHbyte_owned : forall x b n,
 get FHge x=Some(b,Tint8) ->
 V293_target_wstate FHge emp(FHbyte b n)emp |= V293_handoff_byte x b n.
Proof.
 intros x b n G;unfold V293_handoff_byte,V293_handoff_binding.
 eapply V293_target_wstate_star with(m1:=emp)(o1:=emp)(o2:=emp).
 - apply map_join_comm;apply map_join_emp.
 - apply map_join_emp.
 - split;[exists b;split;[exact G|repeat split;reflexivity]| ].
   split;[intros[v E];discriminate|repeat split;reflexivity].
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Lemma FHextra_witness : forall c,
 V293_target_wstate FHge emp(FHextra c)emp |=FHextra_owned c.
Proof.
 intros c;unfold FHextra_owned,FHextra.
 eapply V293_target_wstate_star with(o1:=emp)(o2:=emp).
 - apply map_join_merge;apply map_disjoint;intros[b i].
   destruct(Pos.eq_dec b 3%positive)as[E|E].
   + subst b;right;left;FHoutside.
   + left;apply V293_encoded_memory_outside;left;exact E.
 - apply map_join_emp.
 - apply V293_counter_cell_witness;vm_compute;reflexivity.
 - eapply V293_target_wstate_star with(o1:=emp)(o2:=emp).
   + apply map_join_merge;apply map_disjoint;intros[b i].
     destruct(Pos.eq_dec b 4%positive)as[E|E].
     * subst b;right;left;apply V293_encoded_memory_outside;left;discriminate.
     * left;apply V293_encoded_memory_outside;left;exact E.
   + apply map_join_emp.
   + apply FHbyte_owned;vm_compute;reflexivity.
   + apply FHbyte_owned;vm_compute;reflexivity.
Qed.
Lemma FHpointer : forall var block t,
  get FHge var = Some (block, Tptr Tvoid) ->
  V293_target_wstate FHge emp
    (V293_encoded_memory block 0 true (encode_val (Tptr Tvoid) (Vptr t))) emp |=
    GV var @ (Tptr Tvoid) |-> (Vptr t).
Proof.
  intros var block t HG. exists block. eapply V293_target_wstate_star with
    (m1 := emp) (o1 := emp) (o2 := emp).
  - apply map_join_comm. apply map_join_emp.
  - apply map_join_emp.
  - exists block. split; [exact HG | ]. repeat split; reflexivity.
  - split; [apply V293_encoded_memory_mapsto | reflexivity].
Qed.
Lemma FHspatial : forall tasks events now next,
  V293_target_wstate FHge emp (V293_switch_fixture_mem next)
    (V293_shared_fixture_abs V293_idle_tid tasks events now) |=
    V293_shared_flags **
      ((GV OSTCBCur @ (Tptr Tvoid) |-> (Vptr V293_idle_tid)) **
        (V293_shared_fields V293_idle_tid tasks events now **
          (GV 107%Z @ (Tptr Tvoid) |-> (Vptr next)))) ** (Ais nil ** Acs nil).
Proof.
  intros tasks events now next.
  assert (HF : V293_target_wstate FHge emp emp emp |=
    V293_shared_flags ** (Ais nil ** Acs nil)).
  { unfold V293_shared_flags.
    repeat (eapply V293_target_wstate_star with (m1 := emp) (m2 := emp) (o1 := emp) (o2 := emp);
      [apply map_join_emp | apply map_join_emp | | ]).
    - exists (fun _ : hid => false). split; repeat split; reflexivity.
    - repeat split; reflexivity.
    - exists INUM. repeat split; reflexivity.
    - repeat split; reflexivity.
    - repeat split; reflexivity. }
  assert (HA : V293_target_wstate FHge emp emp
    (V293_shared_fixture_abs V293_idle_tid tasks events now) |=
    V293_shared_fields V293_idle_tid tasks events now).
  { unfold V293_shared_fields, V293_shared_fixture_abs.
    repeat (eapply V293_target_wstate_star; [apply map_join_emp | apply map_join_merge;
      apply map_disjoint; intros key; destruct key; simpl; auto | split; reflexivity | ]).
    split; reflexivity. }
  assert (HP : V293_target_wstate FHge emp (V293_switch_fixture_mem next) emp |=
    (GV OSTCBCur @ (Tptr Tvoid) |-> (Vptr V293_idle_tid)) **
    (GV 107%Z @ (Tptr Tvoid) |-> (Vptr next))).
  { eapply V293_target_wstate_star.
    - apply map_join_merge. apply map_disjoint. intros [b i].
      destruct (Pos.eq_dec b 1%positive) as [E | E].
      + subst b. right; left. apply V293_encoded_memory_outside. left; discriminate.
      + left. apply V293_encoded_memory_outside. left; exact E.
    - apply map_join_emp.
    - apply FHpointer. vm_compute; reflexivity.
    - apply FHpointer. vm_compute; reflexivity. }
  assert (HK : V293_target_wstate FHge emp (V293_switch_fixture_mem next)
    (V293_shared_fixture_abs V293_idle_tid tasks events now) |=
    (((GV OSTCBCur @ (Tptr Tvoid) |-> (Vptr V293_idle_tid)) **
      (GV 107%Z @ (Tptr Tvoid) |-> (Vptr next))) ** V293_shared_fields V293_idle_tid tasks events now) **
      (V293_shared_flags ** (Ais nil ** Acs nil))).
  { eapply V293_target_wstate_star with (m2 := emp) (o2 := emp).
    - apply map_join_emp.
    - apply map_join_emp.
    - eapply V293_target_wstate_star with (m2 := emp) (o1 := emp).
      + apply map_join_emp.
      + apply map_join_comm. apply map_join_emp.
      + exact HP.
      + exact HA.
    - exact HF. }
  clear HF HA HP. sep auto.
Qed.

Theorem FHentry_nonempty : forall different c events now aop,
  exists s,
    indom (V293_current_mode_tasks different) V293_idle_tid /\
    V293_highest_ready (V293_current_mode_tasks different) (V293_switch_target different) /\
    s |= V293_exit_handoff_tail 112%Z 113%Z 111%Z 107%Z 4%positive 5%positive 3%positive Tvoid nil V293_idle_tid
      (V293_current_mode_tasks different) events now (V293_switch_target different)
      aop nil nil Aemp 12 4 c.
Proof.
  intros different c events now aop.
  set (M := merge (V293_switch_fixture_mem (V293_switch_target different))
    (FHextra c)).
  set (O := V293_shared_fixture_abs V293_idle_tid (V293_current_mode_tasks different) events now).
  set (s := ((FHge, emp, M, (fun _ : hid => false),
    (false, nil, nil), O, (sched;;aop)) : RstateOP)).
  exists s.
  destruct (V293_pending_switch_precondition_witness different events now aop)
    as [unused [Hmem [Hhighest _]]].
  split; [exact Hmem | ]. split; [exact Hhighest | ].
  assert (HS : V293_target_wstate FHge emp M O |=
    (V293_shared_flags **
      ((GV OSTCBCur @ (Tptr Tvoid) |-> (Vptr V293_idle_tid)) **
        (V293_shared_fields V293_idle_tid (V293_current_mode_tasks different) events now **
          (GV 107%Z @ (Tptr Tvoid) |-> (Vptr (V293_switch_target different))))) **
      (Ais nil ** Acs nil)) ** FHextra_owned c).
  { eapply V293_target_wstate_star with (o1 := O) (o2 := emp).
    - apply map_join_merge. apply map_disjoint. intros [b i].
      destruct(Pos.eq_dec b 1%positive)as[E|E].
      + subst b;right;left;FHoutside.
      + destruct(Pos.eq_dec b 2%positive)as[E2|E2].
        * subst b;right;left;FHoutside.
        * left;FHoutside.
    - apply map_join_emp.
    - apply FHspatial.
    - apply FHextra_witness. }
  assert (HC : can_change_aop
    ((V293_shared_flags **
      ((GV OSTCBCur @ (Tptr Tvoid) |-> (Vptr V293_idle_tid)) **
        (V293_shared_fields V293_idle_tid (V293_current_mode_tasks different) events now **
          (GV 107%Z @ (Tptr Tvoid) |-> (Vptr (V293_switch_target different))))) **
      (Ais nil ** Acs nil)) ** FHextra_owned c)).
  { unfold V293_shared_flags, V293_shared_fields, V293_counter_cell,
      V293_counter_bindings, FHextra_owned, V293_handoff_byte, V293_handoff_binding, Agvarmapsto, Aptrmapsto. simpl. repeat split; auto. }
  pose proof (@change_aop_rule _ _ _ (sched;;aop) _ HS HC) as HP.
  fold s in HP.
  assert (HK : s |= (CurTid V293_idle_tid ** CurTid V293_idle_tid) **
    ((V293_shared_flags ** (V293_shared_fields V293_idle_tid (V293_current_mode_tasks different) events now **
      (GV 107%Z @ (Tptr Tvoid) |-> (Vptr (V293_switch_target different))))) **
      ((Ais nil ** Acs nil) ** FHextra_owned c))).
  { eapply astar_mono with (P := GV OSTCBCur @ (Tptr Tvoid) |-> (Vptr V293_idle_tid)).
    - intros st H. apply GV_separate_rw in H. unfold CurTid. sep auto.
    - intros st H; exact H.
    - clear HS. sep auto. }
  unfold V293_exit_handoff_tail, V293_storage_open.
  cbn [V293_storage]. unfold FHextra_owned in HK.
  apply astar_l_aop'_intro with (aop := sched;;aop) in HK; [ | reflexivity].
  clear HP HS. sep auto.
Qed.

Theorem FHdifferent_max_nonempty : exists s,
 V293_switch_target true<>V293_idle_tid /\
 indom(V293_current_mode_tasks true)V293_idle_tid /\
 V293_highest_ready(V293_current_mode_tasks true)(V293_switch_target true) /\
 s |=V293_exit_handoff_tail 112%Z 113%Z 111%Z 107%Z 4%positive 5%positive 3%positive
 Tvoid nil V293_idle_tid(V293_current_mode_tasks true)emp Int.zero(V293_switch_target true)
 (spec_done None)nil nil Aemp 12 4(Int.repr Int.max_unsigned).
Proof.
 destruct(FHentry_nonempty true(Int.repr Int.max_unsigned)emp Int.zero(spec_done None))as[s[Member[Highest Held]]].
 exists s;split;[unfold V293_switch_target,V293_current_next,V293_idle_tid;congruence| ].
 repeat first[assumption|split].
Qed.
Lemma FHprivate_local : Aemp ==> LINV V293_shared_li V293_idle_tid nil ** Atrue.
Proof.
 intros s H;pose proof(V293_switch_local_empty V293_idle_tid nil s H)as L;sep auto.
Qed.
Theorem FHactual_changed_tail : forall Spec r ri c,
 InfRules Spec V293_scheduler V293_shared_li
 (V293_storage_inv (cons((3%positive,0%Z),Tint32)(cons((4%positive,0%Z),Tint8)(cons((5%positive,0%Z),Tint8)nil)))107%Z Tvoid)r ri
 (V293_exit_handoff_tail 112%Z 113%Z 111%Z 107%Z 4%positive 5%positive 3%positive
 Tvoid nil V293_idle_tid(V293_current_mode_tasks true)emp Int.zero(V293_switch_target true)
 (spec_done None)nil nil Aemp 12 4 c)
 (sseq(V293_OSSched_increment 111%Z)(sseq(sskip None)(V293_interrupt_handoff 112%Z 113%Z 107%Z)))
 (V293_exit_handoff_resumed 112%Z 113%Z 111%Z 107%Z 4%positive 5%positive 3%positive
 Tvoid nil V293_idle_tid(spec_done None)nil nil Aemp)V293_idle_tid.
Proof.
 intros Spec r ri c;apply V293_OSIntExit_changed_tail.
 - lia.
 - vm_compute;eexists;reflexivity.
 - exact(V293_shared_case_highest true).
 - exact I.
 - apply FHprivate_local.
Qed.
Lemma FHcopy_observable : forall nh nc c s,
 nc<256 ->
 s |=V293_exit_handoff_tail 112%Z 113%Z 111%Z 107%Z 4%positive 5%positive 3%positive
 Tvoid nil V293_idle_tid(V293_current_mode_tasks true)emp Int.zero(V293_switch_target true)
 (spec_done None)nil nil Aemp nh nc c ->
 evalval(evar 113%Z)(getsmem s)=Some(V293_byteval nc).
Proof.
 intros nh nc c s Bound Held.
 assert(B:s |=V293_handoff_byte 113%Z 5%positive nc ** Atrue).
 { unfold V293_exit_handoff_tail in Held;clear -Held;sep auto. }
 destruct(V293_handoff_byte_read 113%Z 5%positive nc Atrue s Bound B)as[Value Ty];exact Value.
Qed.
Lemma FHcounter_wrap : Int.add(Int.repr Int.max_unsigned)Int.one=Int.zero.
Proof. vm_compute;apply Int.mkint_eq;reflexivity. Qed.
(* Frozen single-factor full-switch deletion evidence: not an execution of FH. *)
Check BXcopy_ablation.
