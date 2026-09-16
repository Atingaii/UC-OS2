Require Import Coq.Bool.Bool.

Inductive V293PendResult : Type :=
| V293PendOK
| V293PendTimeout
| V293PendAbort.

Record V293PendState : Type := {
  v293_waiting : bool;
  v293_suspended : bool;
  v293_ready : bool;
  v293_pend_result : V293PendResult
}.

Definition V293_tick_timeout (s : V293PendState) : V293PendState :=
  {| v293_waiting := false;
     v293_suspended := v293_suspended s;
     v293_ready := negb (v293_suspended s);
     v293_pend_result := V293PendTimeout |}.

Definition V293_suspend (s : V293PendState) : V293PendState :=
  {| v293_waiting := v293_waiting s;
     v293_suspended := true;
     v293_ready := false;
     v293_pend_result := v293_pend_result s |}.

Definition V293_resume (s : V293PendState) : V293PendState :=
  {| v293_waiting := v293_waiting s;
     v293_suspended := false;
     v293_ready := negb (v293_waiting s);
     v293_pend_result := v293_pend_result s |}.

Theorem V293_timeout_suspend_resume_ready :
  forall s,
    v293_ready (V293_resume (V293_suspend (V293_tick_timeout s))) = true.
Proof. intros; reflexivity. Qed.

Theorem V293_timeout_suspend_resume_preserves_timeout :
  forall s,
    v293_pend_result (V293_resume (V293_suspend (V293_tick_timeout s))) =
    V293PendTimeout.
Proof. intros; reflexivity. Qed.

Theorem V293_timeout_clears_waiting :
  forall s, v293_waiting (V293_tick_timeout s) = false.
Proof. intros; reflexivity. Qed.
