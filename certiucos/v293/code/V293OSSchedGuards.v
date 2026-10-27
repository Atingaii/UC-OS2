(* The two configured guards of OS_Sched. The continuation is explicit:
   it still contains the priority comparison, counter and switch obligations.
   Critical-section entry/exit are not included here. *)
Require Import CertiOS.framework.model.memory CertiOS.framework.model.language.

Definition V293_OSSched_zero (x : var) : expr :=
  ebinop oeq (ecast (evar x) Tint32) (econst32 (Int.repr 0)).

Definition V293_OSSched_guards (interrupt lock : var) (body : stmts) : stmts :=
  sifthen (V293_OSSched_zero interrupt)
    (sifthen (V293_OSSched_zero lock) body).
