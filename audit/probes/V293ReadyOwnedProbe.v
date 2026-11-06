(* Fixed literal contract.  It uses the earlier fixed program AST, not a
   program generated from the candidate.  This is not a second proof. *)
Require Import CertiOS.audit.probes.V293SuccessEntryWitnessProbe.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293SharedStateWitness.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope nat_scope.

Definition expected_owned_tasks : TcbMod.map :=
  set (V293_prefix_fixture_tasks true) (41%positive,Int.repr 8) (Int.repr 6,rdy,Vnull).
Definition expected_owned_entries :=
  update_nth_val 6 (update_nth_val 8 V293_prefix_fixture_entries Vnull)
    (Vptr (41%positive,Int.repr 8)).
Definition expected_ready_step (next : tid) (old new : nat) : osabstep :=
  fun args O result => args = nil /\ old < 13 /\ new < 12 /\
    exists tasks message,
      get O abstcblsid = Some (abstcblist tasks) /\
      get tasks next = Some (Int.repr (Z.of_nat old),rdy,message) /\
      (forall t status msg, get tasks t <> Some (Int.repr (Z.of_nat new),status,msg)) /\
      result = (Some (Vint32 Int.zero),set O abstcblsid
        (abstcblist (set tasks next (Int.repr (Z.of_nat new),rdy,message)))).
Definition expected_owned_post Mf O' OO' Of op ir enabled si ci events now :=
  join O' Of OO' /\
  expected_entry_trace false ir enabled si ci Mf /\
  V293_tcb_updated_loads Mf 41%positive 8%Z 6 /\
  V293_rekey_bitmap_loads Mf 30%positive 31%positive 80 0 1 /\
  V293_table_loads V293_tcb_type Mf 50%positive expected_owned_entries /\
  load (Tcom_ptr 411%Z) Mf (41%positive,36%Z) = Some Vnull /\
  (forall c ty k, In (c,ty) (getaddr V293_tcb_update_fixture_le) -> k < typelen ty ->
    get Mf (c,Z.of_nat k) = None) /\
  get O' abstcblsid = Some (abstcblist expected_owned_tasks) /\
  (expected_entry_ge,emp,Mf,ir,(enabled,si,ci),OO',op) |=
    V293_shared_fields (41%positive,Int.repr 8) expected_owned_tasks events now ** Atrue /\
  V293_bitmap_tasks 80 0 expected_owned_tasks /\
  V293_priority_table expected_owned_entries expected_owned_tasks /\
  V293_highest_ready expected_owned_tasks (60%positive,Int.zero).

Theorem expected_owned_contract : forall sc events now O Of OO op ir enabled si ci,
  (expected_entry_ge,V293_tcb_update_fixture_le,emp,ir,(enabled,si,ci),O,op) |=
    V293_shared_fields (41%positive,Int.repr 8) (V293_prefix_fixture_tasks true) events now ->
  join O Of OO ->
  exists Mf O' OO',
    spec_step sc (spec_prim nil (expected_ready_step (41%positive,Int.repr 8) 8 6)) OO
      (spec_done (Some (Vint32 Int.zero))) OO' /\
    expected_owned_post Mf O' OO' Of op ir enabled si ci events now.
Proof.
  intros sc events now O Of OO op ir enabled si ci Owned Frame.
  destruct (V293_critical_ready_owned_success sc events now O Of OO op ir enabled si ci Owned Frame)
    as (Mf & O' & OO' & Frame' & Step & Rest).
  exists Mf. exists O'. exists OO'. split; [exact Step | ].
  unfold expected_owned_post. split; assumption.
Qed.
Print Assumptions expected_owned_contract.

(* All owned-entry premises are actually discharged; no initialized-state
   or full ready-invariant validity is claimed for this fixture. *)
Theorem expected_owned_nonvacuity : forall sc events now op ir enabled si ci,
  exists Mf O' OO',
    spec_step sc (spec_prim nil (expected_ready_step (41%positive,Int.repr 8) 8 6))
      (V293_shared_fixture_abs (41%positive,Int.repr 8) (V293_prefix_fixture_tasks true) events now)
      (spec_done (Some (Vint32 Int.zero))) OO' /\
    expected_owned_post Mf O' OO' emp op ir enabled si ci events now.
Proof.
  intros sc events now op ir enabled si ci.
  eapply expected_owned_contract.
  - eapply V293_shared_fields_rebase. apply V293_shared_fixture_fields.
  - apply map_join_emp.
Qed.
Print Assumptions expected_owned_nonvacuity.

Theorem expected_stale_bitmap_rejection : ~ V293_bitmap_tasks 80 0 (V293_prefix_fixture_tasks true).
Proof. exact V293_ready_prio_stale_bitmap_rejected. Qed.
Print Assumptions expected_stale_bitmap_rejection.

Theorem expected_wrong_selection_rejection :
  ~ V293_highest_ready expected_owned_tasks (41%positive,Int.repr 8).
Proof. exact V293_ready_prio_moving_not_highest. Qed.
Print Assumptions expected_wrong_selection_rejection.
