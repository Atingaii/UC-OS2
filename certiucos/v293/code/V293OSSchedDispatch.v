(* Only the first two statements of OS_Sched's unlocked branch.
   This is not a translation of its critical-section wrapper or context switch.
   The pointee type remains a linker parameter: no TCB field is dereferenced. *)
Require Import CertiOS.framework.model.memory CertiOS.framework.model.language.

Definition V293_OSSched_target_expr (table high : var) : expr :=
  earrayelem (evar table) (evar high).

Definition V293_OSSched_target_update (table high target : var) : stmts :=
  sassign (evar target) (V293_OSSched_target_expr table high).

Definition V293_OSSched_unlocked_prefix (sched_id table high target : var) : stmts :=
  sseq (scall sched_id nil) (V293_OSSched_target_update table high target).
