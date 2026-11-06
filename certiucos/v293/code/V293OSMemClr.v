(* Fixed-source OS_MemClr. Postincrement elaboration stores at the old
   pointer before advancing it. Parameter cells and target bytes are separate.
   This is a manual source normalization, not a verified C frontend. *)
Require Import CertiOS.framework.include_frm.
Definition V293_clr_guard (size : var) :=
  ebinop olt (econst32 Int.zero) (ecast (evar size) Tint32).
Definition V293_clr_advance (dest : var) :=
  sassign (evar dest) (ebinop oplus (evar dest) (econst32 Int.one)).
Definition V293_clr_iteration (dest size : var) :=
  sseq (sassign (ederef (evar dest)) (ecast (econst32 Int.zero) Tint8))
    (sseq (V293_clr_advance dest)
      (sassign (evar size)
        (ecast (ebinop ominus (ecast (evar size) Tint32) (econst32 Int.one)) Tint16))).
Definition V293_clr_loop (dest size : var) :=
  swhile (V293_clr_guard size) (V293_clr_iteration dest size).
Definition V293_MemClr_function (dest size : var) : function :=
  (Tvoid,dcons dest (Tptr Tint8) (dcons size Tint16 dnil),dnil,
    sseq (V293_clr_loop dest size) sret).
