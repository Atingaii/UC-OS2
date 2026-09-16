Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.

Inductive V293DeleteResult : Type :=
| V293DeleteOK
| V293DeleteLockedCurrent.

Record V293ExecutionState : Type := {
  v293_lock_nesting : nat;
  v293_current_live : bool;
  v293_current_on_free_list : bool
}.

Definition V293_execution_ownership_safe (s : V293ExecutionState) : Prop :=
  v293_current_live s = true -> v293_current_on_free_list s = false.

Definition V293_delete_current (s : V293ExecutionState)
  : V293DeleteResult * V293ExecutionState :=
  if Nat.eqb (v293_lock_nesting s) 0 then
    (V293DeleteOK,
     {| v293_lock_nesting := 0;
        v293_current_live := false;
        v293_current_on_free_list := true |})
  else
    (V293DeleteLockedCurrent, s).

Theorem V293_locked_current_delete_is_rejected :
  forall s,
    v293_lock_nesting s <> 0 ->
    fst (V293_delete_current s) = V293DeleteLockedCurrent.
Proof.
  intros s H.
  unfold V293_delete_current.
  destruct (Nat.eqb_spec (v293_lock_nesting s) 0).
  - contradiction.
  - reflexivity.
Qed.

Theorem V293_locked_current_delete_preserves_state :
  forall s,
    v293_lock_nesting s <> 0 ->
    snd (V293_delete_current s) = s.
Proof.
  intros s H.
  unfold V293_delete_current.
  destruct (Nat.eqb_spec (v293_lock_nesting s) 0).
  - contradiction.
  - reflexivity.
Qed.

Theorem V293_locked_current_delete_preserves_ownership :
  forall s,
    V293_execution_ownership_safe s ->
    v293_lock_nesting s <> 0 ->
    V293_execution_ownership_safe (snd (V293_delete_current s)).
Proof.
  intros s Hsafe Hlock.
  rewrite V293_locked_current_delete_preserves_state by exact Hlock.
  exact Hsafe.
Qed.
