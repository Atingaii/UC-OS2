Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Import ListNotations.

Fixpoint V293_effective_priority (base : nat) (held_pips : list nat) : nat :=
  match held_pips with
  | [] => base
  | p :: ps => Nat.min p (V293_effective_priority base ps)
  end.

Definition V293_restore_priority (base : nat) (remaining_pips : list nat) : nat :=
  V293_effective_priority base remaining_pips.

Theorem V293_restore_without_mutexes_is_base :
  forall base, V293_restore_priority base [] = base.
Proof. reflexivity. Qed.

Theorem V293_effective_priority_cons :
  forall base p ps,
    V293_effective_priority base (p :: ps) =
    Nat.min p (V293_effective_priority base ps).
Proof. reflexivity. Qed.

Theorem V293_restore_single_mutex :
  forall base pip, V293_restore_priority base [pip] = Nat.min pip base.
Proof. intros; reflexivity. Qed.
