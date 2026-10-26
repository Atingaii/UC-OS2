(* Generated from the frozen, configured Clang AST by check-v293-functions.py.
   The unsigned-int to unsigned-short return conversion is explicit. *)
Require Import CertiOS.framework.model.memory.
Require Import CertiOS.framework.model.language.

Definition V293_OSVersion_expr : expr :=
  ecast (econst32 (Int.repr 29300)) Tint16.

Definition V293_OSVersion_body : stmts := srete V293_OSVersion_expr.

Definition V293_OSVersion_function : function :=
  (Tint16, dnil, dnil, V293_OSVersion_body).
