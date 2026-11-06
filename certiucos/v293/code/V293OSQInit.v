(* Configured os_q.c:936--962, body SHA256
   1c7141f5cfdd50134cb33e3f4b1d4d3ddcd75d8c0effe2cfdbab933d513196e6.
   Four 24-byte OS_Q objects. Recursive OSQPtr uses composite tag 414.
   Manual source frontend; sizeof=96; for lowers to native while. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSInitTCBClear.
Definition V293_q_fields : decllist :=
  dcons 1%Z (Tcom_ptr 414%Z)
  (dcons 2%Z (Tptr (Tptr Tvoid)) (dcons 3%Z (Tptr (Tptr Tvoid))
   (dcons 4%Z (Tptr (Tptr Tvoid)) (dcons 5%Z (Tptr (Tptr Tvoid))
    (dcons 6%Z Tint16 (dcons 7%Z Tint16 dnil)))))).
Definition V293_q_type : type := Tstruct 414%Z V293_q_fields.
Definition V293_q_table_type := Tarray V293_q_type 4.
Definition V293_q_link_guard (ix : var) :=
  ebinop olt (ecast (evar ix) Tint32) (econst32 (Int.repr 3)).
Definition V293_q_link_inc (ix : var) :=
  ecast (ebinop oplus (ecast (evar ix) Tint32) (econst32 Int.one)) Tint16.
Definition V293_q_link_address (table ix : var) :=
  eaddrof (earrayelem (evar table) (evar ix)).
Definition V293_q_ptr_field (p : var) := efield (ederef (evar p)) 1%Z.
Definition V293_q_link_iteration (table ix ix_next pq1 pq2 : var) :=
  sseq (sassign (evar ix_next) (V293_q_link_inc ix))
  (sseq (sassign (evar pq1) (V293_q_link_address table ix))
  (sseq (sassign (evar pq2) (V293_q_link_address table ix_next))
  (sseq (sassign (V293_q_ptr_field pq1) (evar pq2))
        (sassign (evar ix) (V293_q_link_inc ix))))).
Definition V293_q_link_loop (table ix ix_next pq1 pq2 : var) :=
  swhile (V293_q_link_guard ix) (V293_q_link_iteration table ix ix_next pq1 pq2).
Definition V293_q_link_tail (table free_head ix pq1 : var) :=
  sseq (sassign (evar pq1) (V293_q_link_address table ix))
  (sseq (sassign (V293_q_ptr_field pq1) (ecast enull (Tptr V293_q_type)))
        (sassign (evar free_head) (eaddrof (earrayelem (evar table) (econst32 Int.zero))))).
Definition V293_init_q_links (table free_head ix ix_next pq1 pq2 : var) :=
  sseq (sassign (evar ix) (ecast (econst32 Int.zero) Tint16))
  (sseq (V293_q_link_loop table ix ix_next pq1 pq2)
        (V293_q_link_tail table free_head ix pq1)).
Definition V293_init_q_body (clear table free_head ix ix_next pq1 pq2 : var) :=
  sseq (scall clear (V293_init_clear_address table ::
    V293_init_clear_size V293_q_table_type :: nil))
       (V293_init_q_links table free_head ix ix_next pq1 pq2).
Definition V293_QInit_function (clear table free_head ix ix_next pq1 pq2 : var) : function :=
  (Tvoid,dnil,
   dcons ix Tint16 (dcons ix_next Tint16
    (dcons pq1 (Tptr V293_q_type) (dcons pq2 (Tptr V293_q_type) dnil))),
   sseq (V293_init_q_body clear table free_head ix ix_next pq1 pq2) sret).
