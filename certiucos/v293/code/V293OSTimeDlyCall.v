(* Fixed configured OSTimeDly declaration, including the local initializer.
   Critical operations keep the existing accepted normalized interpretation. *)
Require Import CertiOS.certiucos.v293.code.V293OSTimeDly.
Require Import CertiOS.framework.model.memory CertiOS.framework.model.language.

Definition V293_dly_full_body current rows group y ticks nesting lock sched saved :=
 sseq (sassign (evar saved) (econst32 Int.zero))
       (V293_dly_body current rows group y ticks nesting lock sched).

Definition V293_dly_function current rows group y ticks nesting lock sched saved : function :=
 (Tvoid, dcons ticks Tint32 dnil,
  dcons y Tint8 (dcons saved Tint32 dnil),
  V293_dly_full_body current rows group y ticks nesting lock sched saved).
