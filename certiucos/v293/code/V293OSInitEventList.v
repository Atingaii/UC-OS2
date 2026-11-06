(* Configured os_core.c:1336--1373, source body hash
   230bd821cc790a82385212f2bde26fb379626776971cc295ee8d39a3e2ebc796.
   Two events, 16-byte analysis layout; sizeof folds to 32. The for is a
   native while with its increment at the end, not a replacement write list.
   OSEventPtr is void*: implicit pointer conversion is explicit below;
   the composite C pointer casts of zero normalize to void-pointer NULL. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.code.V293OSInitTCBClear.
Definition V293_event_table_type := Tarray V293_event_type 2.
Definition V293_event_link_guard (ix : var) :=
  ebinop olt (ecast (evar ix) Tint32) (econst32 Int.one).
Definition V293_event_link_inc (ix : var) :=
  ecast (ebinop oplus (ecast (evar ix) Tint32) (econst32 Int.one)) Tint16.
Definition V293_event_link_address (table ix : var) :=
  eaddrof (earrayelem (evar table) (evar ix)).
Definition V293_event_type_field (p : var) := efield (ederef (evar p)) 1%Z.
Definition V293_event_ptr_field (p : var) := efield (ederef (evar p)) 2%Z.
Definition V293_event_link_iteration (table ix ix_next pevent1 pevent2 : var) :=
  sseq (sassign (evar ix_next) (V293_event_link_inc ix))
  (sseq (sassign (evar pevent1) (V293_event_link_address table ix))
  (sseq (sassign (evar pevent2) (V293_event_link_address table ix_next))
  (sseq (sassign (V293_event_type_field pevent1) (ecast (econst32 Int.zero) Tint8))
  (sseq (sassign (V293_event_ptr_field pevent1) (ecast (evar pevent2) (Tptr Tvoid)))
        (sassign (evar ix) (V293_event_link_inc ix)))))).
Definition V293_event_link_loop (table ix ix_next pevent1 pevent2 : var) :=
  swhile (V293_event_link_guard ix) (V293_event_link_iteration table ix ix_next pevent1 pevent2).
Definition V293_event_link_tail (table free_head ix pevent1 : var) :=
  sseq (sassign (evar pevent1) (V293_event_link_address table ix))
  (sseq (sassign (V293_event_type_field pevent1) (ecast (econst32 Int.zero) Tint8))
  (sseq (sassign (V293_event_ptr_field pevent1) (ecast enull (Tptr Tvoid)))
        (sassign (evar free_head) (eaddrof (earrayelem (evar table) (econst32 Int.zero)))))).
Definition V293_init_event_links (table free_head ix ix_next pevent1 pevent2 : var) :=
  sseq (sassign (evar ix) (ecast (econst32 Int.zero) Tint16))
  (sseq (V293_event_link_loop table ix ix_next pevent1 pevent2)
        (V293_event_link_tail table free_head ix pevent1)).
Definition V293_init_event_body (clear table free_head ix ix_next pevent1 pevent2 : var) :=
  sseq (scall clear (V293_init_clear_address table ::
    V293_init_clear_size V293_event_table_type :: nil))
       (V293_init_event_links table free_head ix ix_next pevent1 pevent2).
Definition V293_InitEventList_function (clear table free_head ix ix_next pevent1 pevent2 : var) : function :=
  (Tvoid,dnil,
   dcons ix Tint16 (dcons ix_next Tint16
    (dcons pevent1 (Tptr V293_event_type) (dcons pevent2 (Tptr V293_event_type) dnil))),
   sseq (V293_init_event_body clear table free_head ix ix_next pevent1 pevent2) sret).
