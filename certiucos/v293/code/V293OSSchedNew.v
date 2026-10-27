(* Checked translation of the configured static OS_SchedNew.
   Array decay and lvalue reads use CoqImp's native array/evar semantics.
   The promoted 32-bit operations and final byte narrowing remain explicit.
   Identifiers are linker parameters, not a completed global symbol table. *)
Require Import CertiOS.framework.model.memory CertiOS.framework.model.language.

Definition V293_OSSchedNew_row_expr (unmap group : var) : expr :=
  earrayelem (evar unmap) (evar group).

Definition V293_OSSchedNew_priority_expr (unmap rows y : var) : expr :=
  ecast
    (ebinop oplus
      (ebinop olshift (ecast (evar y) Tint32) (econst32 (Int.repr 3)))
      (ecast (earrayelem (evar unmap) (earrayelem (evar rows) (evar y))) Tint32))
    Tint8.

Definition V293_OSSchedNew_updates (unmap group rows high y : var) : stmts :=
  sseq (sassign (evar y) (V293_OSSchedNew_row_expr unmap group))
       (sassign (evar high) (V293_OSSchedNew_priority_expr unmap rows y)).

(* A C void function falling through its closing brace returns to its caller. *)
Definition V293_OSSchedNew_body (unmap group rows high y : var) : stmts :=
  sseq (V293_OSSchedNew_updates unmap group rows high y) sret.

Definition V293_OSSchedNew_function (unmap group rows high y : var) : function :=
  (Tvoid, dnil, dcons y Tint8 dnil, V293_OSSchedNew_body unmap group rows high y).
