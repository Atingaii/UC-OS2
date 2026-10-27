(* Configured OS_Sched: != is normalized to logical negation of equality.
   The discarded-result unsigned postfix ++ is a single modular assignment.
   The actual switch and critical-section boundaries remain OPEN. *)
Require Import CertiOS.framework.model.memory CertiOS.framework.model.language.

Definition V293_OSSched_different (high current : var) : expr :=
  eunop oppsite (ebinop oeq (ecast (evar high) Tint32) (ecast (evar current) Tint32)).

Definition V293_OSSched_increment (counter : var) : stmts :=
  sassign (evar counter) (ebinop oplus (evar counter) (econst32 Int.one)).

Definition V293_OSSched_change (high current counter : var) (suffix : stmts) : stmts :=
  sifthen (V293_OSSched_different high current)
    (sseq (V293_OSSched_increment counter) suffix).
