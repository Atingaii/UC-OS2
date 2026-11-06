(* Configured os_flag.c:1142--1180, fixed source body SHA256
   5b8594c0edd6c5b4f91eb0e4c6225265da37f9b3c2034032c27102ce3479a62e.
   Five 12-byte OS_FLAG_GRP; 16-bit OS_FLAGS; padding is explicit.
   sizeof folds to 60; for translates to native while + increment.
   Manual source frontend, not a verified C translation. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSInitTCBClear.
Definition V293_flag_fields : decllist :=
  dcons 1%Z Tint8 (dcons (Z.neg 1) (Tarray Tint8 3)
   (dcons 2%Z (Tptr Tvoid) (dcons 3%Z Tint16
    (dcons (Z.neg 2) (Tarray Tint8 2) dnil)))).
Definition V293_flag_type : type := Tstruct 412%Z V293_flag_fields.
Definition V293_flag_table_type := Tarray V293_flag_type 5.
Definition V293_flag_link_guard (ix : var) :=
  ebinop olt (ecast (evar ix) Tint32) (econst32 (Int.repr 4)).
Definition V293_flag_link_inc (ix : var) :=
  ecast (ebinop oplus (ecast (evar ix) Tint32) (econst32 Int.one)) Tint16.
Definition V293_flag_link_address (table ix : var) :=
  eaddrof (earrayelem (evar table) (evar ix)).
Definition V293_flag_type_field (p : var) := efield (ederef (evar p)) 1%Z.
Definition V293_flag_ptr_field (p : var) := efield (ederef (evar p)) 2%Z.
Definition V293_flag_link_iteration (table ix ix_next pgrp1 pgrp2 : var) :=
  sseq (sassign (evar ix_next) (V293_flag_link_inc ix))
  (sseq (sassign (evar pgrp1) (V293_flag_link_address table ix))
  (sseq (sassign (evar pgrp2) (V293_flag_link_address table ix_next))
  (sseq (sassign (V293_flag_type_field pgrp1) (ecast (econst32 Int.zero) Tint8))
  (sseq (sassign (V293_flag_ptr_field pgrp1) (ecast (evar pgrp2) (Tptr Tvoid)))
        (sassign (evar ix) (V293_flag_link_inc ix)))))).
Definition V293_flag_link_loop (table ix ix_next pgrp1 pgrp2 : var) :=
  swhile (V293_flag_link_guard ix) (V293_flag_link_iteration table ix ix_next pgrp1 pgrp2).
Definition V293_flag_link_tail (table free_head ix pgrp1 : var) :=
  sseq (sassign (evar pgrp1) (V293_flag_link_address table ix))
  (sseq (sassign (V293_flag_type_field pgrp1) (ecast (econst32 Int.zero) Tint8))
  (sseq (sassign (V293_flag_ptr_field pgrp1) (ecast enull (Tptr Tvoid)))
        (sassign (evar free_head) (eaddrof (earrayelem (evar table) (econst32 Int.zero)))))).
Definition V293_init_flag_links (table free_head ix ix_next pgrp1 pgrp2 : var) :=
  sseq (sassign (evar ix) (ecast (econst32 Int.zero) Tint16))
  (sseq (V293_flag_link_loop table ix ix_next pgrp1 pgrp2)
        (V293_flag_link_tail table free_head ix pgrp1)).
Definition V293_init_flag_body (clear table free_head ix ix_next pgrp1 pgrp2 : var) :=
  sseq (scall clear (V293_init_clear_address table ::
    V293_init_clear_size V293_flag_table_type :: nil))
       (V293_init_flag_links table free_head ix ix_next pgrp1 pgrp2).
Definition V293_FlagInit_function (clear table free_head ix ix_next pgrp1 pgrp2 : var) : function :=
  (Tvoid,dnil,
   dcons ix Tint16 (dcons ix_next Tint16
    (dcons pgrp1 (Tptr V293_flag_type) (dcons pgrp2 (Tptr V293_flag_type) dnil))),
   sseq (V293_init_flag_body clear table free_head ix ix_next pgrp1 pgrp2) sret).
