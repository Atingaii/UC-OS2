(* First two statements of configured OS_InitTCBList (os_core.c:1591ff).
   sizeof is manually folded from the checked fixed analysis layout; this
   language has no sizeof constructor. No TCBNext initialization is included. *)
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.framework.include_frm.
Definition V293_tcb_table_type := Tarray V293_tcb_type 13.
Definition V293_tcb_prio_table_type := Tarray (Tptr V293_tcb_type) 13.
Definition V293_init_clear_address (table : var) : expr :=
  ecast (eaddrof (earrayelem (evar table) (econst32 Int.zero))) (Tptr Tint8).
Definition V293_init_clear_size (tp : type) : expr :=
  ecast (econst32 (Int.repr (Z.of_nat (typelen tp)))) Tint16.
Definition V293_init_tcb_clear (f table priorities : var) : stmts :=
  sseq (scall f (V293_init_clear_address table ::
    V293_init_clear_size V293_tcb_table_type :: nil))
    (scall f (V293_init_clear_address priorities ::
      V293_init_clear_size V293_tcb_prio_table_type :: nil)).
