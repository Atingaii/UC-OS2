Require Import Coq.Arith.Arith.
Require Import Lia.

Definition V293_OS_LOWEST_PRIO : nat := 12.
Definition V293_OS_MAX_EVENTS : nat := 2.
Definition V293_OS_MAX_TASKS : nat := 11.

Definition V293_native_pend_status : bool := true.
Definition V293_event_multi_enabled : bool := false.
Definition V293_timer_manager_enabled : bool := false.
Definition V293_task_registers_enabled : bool := false.

Lemma V293_priority_range_nonempty : 0 < V293_OS_LOWEST_PRIO.
Proof. unfold V293_OS_LOWEST_PRIO; lia. Qed.

Lemma V293_event_pool_nonempty : 0 < V293_OS_MAX_EVENTS.
Proof. unfold V293_OS_MAX_EVENTS; lia. Qed.
