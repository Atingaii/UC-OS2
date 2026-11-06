(* Configured OS_InitTCBList: source declarations in source order, full body,
   explicit sret for the C void fall-through. Identifier order is not C state. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.code.V293OSInitTCBList.
Definition V293_InitTCBList_function clear table priorities list_head free_head ix ix_next ptcb1 ptcb2 : function :=
  (Tvoid,dnil,
   dcons ix Tint8 (dcons ix_next Tint8
     (dcons ptcb1 (Tptr V293_tcb_type) (dcons ptcb2 (Tptr V293_tcb_type) dnil))),
   sseq (V293_init_tcb_body clear table priorities list_head free_head ix ix_next ptcb1 ptcb2) sret).
