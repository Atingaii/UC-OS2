(* Exact configured for-loop is elaborated to native while, not unrolled.
   Fixed OS_LOWEST_PRIO=12 gives two rows. Identifiers are linker parameters. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Definition V293_rdy_zero := ecast (econst32 Int.zero) Tint8.
Definition V293_rdy_guard (i : var) :=
  ebinop olt (ecast (evar i) Tint32) (econst32 (Int.repr 2)).
Definition V293_rdy_increment (i : var) :=
  sassign (evar i) (ecast (ebinop oplus (ecast (evar i) Tint32) (econst32 Int.one)) Tint8).
Definition V293_rdy_loop (rows i : var) :=
  swhile (V293_rdy_guard i)
    (sseq (sassign (earrayelem (evar rows) (evar i)) V293_rdy_zero) (V293_rdy_increment i)).
Definition V293_InitRdyList_updates (group rows prio high top current i : var) :=
  sseq (sassign (evar group) V293_rdy_zero)
  (sseq (sassign (evar i) V293_rdy_zero)
  (sseq (V293_rdy_loop rows i)
  (sseq (sassign (evar prio) V293_rdy_zero)
  (sseq (sassign (evar high) V293_rdy_zero)
  (sseq (sassign (evar top) (ecast enull (Tptr V293_tcb_type)))
        (sassign (evar current) (ecast enull (Tptr V293_tcb_type)))))))).
Definition V293_InitRdyList_function (group rows prio high top current i : var) : function :=
  (Tvoid,dnil,dcons i Tint8 dnil,
   sseq (V293_InitRdyList_updates group rows prio high top current i) sret).
