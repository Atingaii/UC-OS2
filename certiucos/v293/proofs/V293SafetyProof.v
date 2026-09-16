Require Import CertiOS.certiucos.v293.spec.V293SafetySpec.

Theorem V293_timeout_suspend_resume_safety_proved :
  V293_timeout_suspend_resume_safety.
Proof.
  intros s; split.
  - apply V293_timeout_suspend_resume_ready.
  - apply V293_timeout_suspend_resume_preserves_timeout.
Qed.

Theorem V293_nested_mutex_restoration_safety_proved :
  V293_nested_mutex_restoration_safety.
Proof. intros; reflexivity. Qed.

Theorem V293_locked_self_delete_safety_proved :
  V293_locked_self_delete_safety.
Proof.
  intros s Hsafe Hlock; split.
  - apply V293_locked_current_delete_is_rejected; exact Hlock.
  - apply V293_locked_current_delete_preserves_ownership; assumption.
Qed.
