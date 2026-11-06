(* Configured os_mem.c:456--487; fixed body SHA256
   69ae7854109e60bdc76cade4c510ba64a83d67761a66318349aaf0e2317c2cd5.
   Five 20-byte OS_MEM objects; only pmem then i are local variables.
   Manual source frontend: sizeof=100; for lowers to native while. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSInitTCBClear.
Definition V293_mem_fields : decllist :=
  dcons 1%Z (Tptr Tvoid) (dcons 2%Z (Tptr Tvoid)
   (dcons 3%Z Tint32 (dcons 4%Z Tint32 (dcons 5%Z Tint32 dnil)))).
Definition V293_mem_type : type := Tstruct 413%Z V293_mem_fields.
Definition V293_mem_table_type := Tarray V293_mem_type 5.
Definition V293_mem_link_guard (ix : var) :=
  ebinop olt (ecast (evar ix) Tint32) (econst32 (Int.repr 4)).
Definition V293_mem_link_inc (ix : var) :=
  ecast (ebinop oplus (ecast (evar ix) Tint32) (econst32 Int.one)) Tint16.
Definition V293_mem_link_address (table ix : var) :=
  eaddrof (earrayelem (evar table) (evar ix)).
Definition V293_mem_link_next (table ix : var) :=
  ecast (eaddrof (earrayelem (evar table)
    (ebinop oplus (ecast (evar ix) Tint32) (econst32 Int.one)))) (Tptr Tvoid).
Definition V293_mem_ptr_field (pmem : var) := efield (ederef (evar pmem)) 2%Z.
Definition V293_mem_link_iteration (table pmem ix : var) :=
  sseq (sassign (evar pmem) (V293_mem_link_address table ix))
  (sseq (sassign (V293_mem_ptr_field pmem) (V293_mem_link_next table ix))
        (sassign (evar ix) (V293_mem_link_inc ix))).
Definition V293_mem_link_loop (table pmem ix : var) :=
  swhile (V293_mem_link_guard ix) (V293_mem_link_iteration table pmem ix).
Definition V293_mem_link_tail (table free_head pmem ix : var) :=
  sseq (sassign (evar pmem) (V293_mem_link_address table ix))
  (sseq (sassign (V293_mem_ptr_field pmem) (ecast enull (Tptr Tvoid)))
        (sassign (evar free_head) (eaddrof (earrayelem (evar table) (econst32 Int.zero))))).
Definition V293_init_mem_links (table free_head pmem ix : var) :=
  sseq (sassign (evar ix) (ecast (econst32 Int.zero) Tint16))
  (sseq (V293_mem_link_loop table pmem ix) (V293_mem_link_tail table free_head pmem ix)).
Definition V293_init_mem_body (clear table free_head pmem ix : var) :=
  sseq (scall clear (V293_init_clear_address table ::
    V293_init_clear_size V293_mem_table_type :: nil))
       (V293_init_mem_links table free_head pmem ix).
Definition V293_MemInit_function (clear table free_head pmem ix : var) : function :=
  (Tvoid,dnil,dcons pmem (Tptr V293_mem_type) (dcons ix Tint16 dnil),
   sseq (V293_init_mem_body clear table free_head pmem ix) sret).
