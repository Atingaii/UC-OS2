(* Configured OS_InitTCBList os_core.c:1591--1617. For is elaborated to
   native while; no finite array of assignments replaces the source loop.
   The two sizeof expressions are folded using the fixed checked layout. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.code.V293OSInitTCBClear.
Definition V293_tcb_link_guard (ix : var) :=
  ebinop olt (ecast (evar ix) Tint32) (econst32 (Int.repr 12)).
Definition V293_tcb_link_inc (ix : var) :=
  ecast (ebinop oplus (ecast (evar ix) Tint32) (econst32 Int.one)) Tint8.
Definition V293_tcb_link_address (table ix : var) :=
  eaddrof (earrayelem (evar table) (evar ix)).
Definition V293_tcb_link_field (p : var) := efield (ederef (evar p)) 7%Z.
Definition V293_tcb_link_iteration (table ix ix_next ptcb1 ptcb2 : var) :=
  sseq (sassign (evar ix_next) (V293_tcb_link_inc ix))
  (sseq (sassign (evar ptcb1) (V293_tcb_link_address table ix))
  (sseq (sassign (evar ptcb2) (V293_tcb_link_address table ix_next))
  (sseq (sassign (V293_tcb_link_field ptcb1) (evar ptcb2))
        (sassign (evar ix) (V293_tcb_link_inc ix))))).
Definition V293_tcb_link_loop (table ix ix_next ptcb1 ptcb2 : var) :=
  swhile (V293_tcb_link_guard ix) (V293_tcb_link_iteration table ix ix_next ptcb1 ptcb2).
Definition V293_tcb_link_tail (table list_head free_head ix ptcb1 : var) :=
  sseq (sassign (evar ptcb1) (V293_tcb_link_address table ix))
  (sseq (sassign (V293_tcb_link_field ptcb1) (ecast enull (Tptr V293_tcb_type)))
  (sseq (sassign (evar list_head) (ecast enull (Tptr V293_tcb_type)))
        (sassign (evar free_head) (eaddrof (earrayelem (evar table) (econst32 Int.zero)))))).
Definition V293_init_tcb_links (table list_head free_head ix ix_next ptcb1 ptcb2 : var) :=
  sseq (sassign (evar ix) (ecast (econst32 Int.zero) Tint8))
  (sseq (V293_tcb_link_loop table ix ix_next ptcb1 ptcb2)
        (V293_tcb_link_tail table list_head free_head ix ptcb1)).
Definition V293_init_tcb_body (clear table priorities list_head free_head ix ix_next ptcb1 ptcb2 : var) :=
  sseq (V293_init_tcb_clear clear table priorities)
       (V293_init_tcb_links table list_head free_head ix ix_next ptcb1 ptcb2).
