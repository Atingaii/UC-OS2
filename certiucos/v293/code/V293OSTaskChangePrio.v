(* Frozen OSTaskChangePrio, os_task.c:119-120, ONLY the two table writes.
   The C null pointer cast is represented by the language's typed-assignment null.
   No TCB dereference or preceding/following API statement is translated here.
   The 13-entry table and 4-byte pointers are the fixed analysis profile. *)
Require Import CertiOS.framework.model.memory CertiOS.framework.model.language.

Definition V293_task_prio_rekey (table oldprio newprio ptcb : var) : stmts :=
  sseq (sassign (earrayelem (evar table) (evar oldprio)) enull)
       (sassign (earrayelem (evar table) (evar newprio)) (evar ptcb)).

(* Normalized RHSs of the byte compound assignments in os_task.c:125/130.
   Integer promotions, C's explicit complement-to-OS_PRIO cast, and the
   final compound-assignment byte conversion remain explicit.  The mask
   operand is the earlier computed bitx_old/bitx_new, not its bit index. *)
Definition V293_task_prio_clear_expr (row mask : expr) : expr :=
  ecast (ebinop obitand (ecast row Tint32)
    (ecast (ecast (eunop negation (ecast mask Tint32)) Tint8) Tint32)) Tint8.
Definition V293_task_prio_set_expr (row mask : expr) : expr :=
  ecast (ebinop obitor (ecast row Tint32) (ecast mask Tint32)) Tint8.

(* Exact statement order INSIDE the ready THEN branch, os_task.c:125-130.
   The three preceding TCB reads and the outer ready test are not included.
   The configured OS_TRACE_TASK_READY macro expands to no statements. *)
Definition V293_task_prio_ready_then
    (rows group yold ynew xold xnew byold bynew : var) : stmts :=
  let oldrow := earrayelem (evar rows) (evar yold) in
  let newrow := earrayelem (evar rows) (evar ynew) in
  sseq (sassign oldrow (V293_task_prio_clear_expr oldrow (evar xold)))
    (sseq (sifthen (ebinop oeq (ecast oldrow Tint32) (econst32 Int.zero))
      (sassign (evar group) (V293_task_prio_clear_expr (evar group) (evar byold))))
      (sseq (sassign (evar group) (V293_task_prio_set_expr (evar group) (evar bynew)))
        (sassign newrow (V293_task_prio_set_expr newrow (evar xnew))))).

(* Complete configured OS_TCB field order. Tags 410/411/412 name os_tcb,
   os_event and os_flag_node. The analysis profile has 16-bit OS_FLAGS,
   hence TWO bytes of source-layout padding before OSTCBDly. The synthetic
   field -1 has no C lvalue counterpart. No optional field is silently dropped. *)
Definition V293_tcb_fields : decllist :=
  dcons 1%Z (Tptr Tint32) (* OSTCBStkPtr *)
  (dcons 2%Z (Tptr Tvoid) (* OSTCBExtPtr *)
  (dcons 3%Z (Tptr Tint32) (* OSTCBStkBottom *)
  (dcons 4%Z Tint32 (* OSTCBStkSize *)
  (dcons 5%Z Tint16 (* OSTCBOpt *)
  (dcons 6%Z Tint16 (* OSTCBId *)
  (dcons 7%Z (Tcom_ptr 410%Z) (* OSTCBNext *)
  (dcons 8%Z (Tcom_ptr 410%Z) (* OSTCBPrev *)
  (dcons 9%Z (Tcom_ptr 411%Z) (* OSTCBEventPtr *)
  (dcons 10%Z (Tptr Tvoid) (* OSTCBMsg *)
  (dcons 11%Z (Tcom_ptr 412%Z) (* OSTCBFlagNode *)
  (dcons 12%Z Tint16 (* OSTCBFlagsRdy *)
  (dcons (-1)%Z (Tarray Tint8 2) (* source layout padding *)
  (dcons 13%Z Tint32 (* OSTCBDly *)
  (dcons 14%Z Tint8 (* OSTCBStat *)
  (dcons 15%Z Tint8 (* OSTCBStatPend *)
  (dcons 16%Z Tint8 (* OSTCBPrio *)
  (dcons 17%Z Tint8 (* OSTCBX *)
  (dcons 18%Z Tint8 (* OSTCBY *)
  (dcons 19%Z Tint8 (* OSTCBBitX *)
  (dcons 20%Z Tint8 (* OSTCBBitY *)
  (dcons 21%Z Tint8 dnil))))))))))))))))))))).
Definition V293_tcb_type : type := Tstruct 410%Z V293_tcb_fields.

(* The actual three statements between the priority-table writes and the
   outer ready condition, os_task.c:121-123. BitY is read before BitX. *)
Definition V293_task_prio_read_old (ptcb yold byold xold : var) : stmts :=
  sseq (sassign (evar yold) (efield (ederef (evar ptcb)) 18%Z))
    (sseq (sassign (evar byold) (efield (ederef (evar ptcb)) 20%Z))
          (sassign (evar xold) (efield (ederef (evar ptcb)) 19%Z))).

(* os_task.c:124. The language has no != constructor: !(a == 0)
   preserves C's truth value. Both byte operands are promoted before &.
   Equality with zero is unaffected by the unsigned type of literal 0u. *)
Definition V293_task_prio_ready_test (rows yold xold : var) : expr :=
  eunop oppsite (ebinop oeq
    (ebinop obitand (ecast (earrayelem (evar rows) (evar yold)) Tint32)
      (ecast (evar xold) Tint32)) (econst32 Int.zero)).

(* Only the ready if. The following independent event-pointer statements
   (starting at line 135) are NOT translated by this ready-only fragment. *)
Definition V293_task_prio_ready_branch
    (rows group yold ynew xold xnew byold bynew : var) : stmts :=
  sifthen (V293_task_prio_ready_test rows yold xold)
    (V293_task_prio_ready_then rows group yold ynew xold xnew byold bynew).

Definition V293_task_prio_read_ready
    (ptcb rows group yold ynew xold xnew byold bynew : var) : stmts :=
  sseq (V293_task_prio_read_old ptcb yold byold xold)
    (V293_task_prio_ready_branch rows group yold ynew xold xnew byold bynew).

(* Continuous frozen source 119-130: table writes, the three TCB reads,
   then the ready if. Independent event handling and TCB updates follow. *)
Definition V293_task_prio_prefix
    (table oldprio newprio ptcb rows group yo yn xo xn byo byn : var) : stmts :=
  sseq (V293_task_prio_rekey table oldprio newprio ptcb)
    (V293_task_prio_read_ready ptcb rows group yo yn xo xn byo byn).

(* Configured os_event, actual five fields; explicit analysis-layout padding.
   Field tags 1..5 follow C order. Synthetic -1/-2 have no C lvalue. *)
Definition V293_event_fields : decllist :=
  dcons 1%Z Tint8 (dcons (-1)%Z (Tarray Tint8 3)
  (dcons 2%Z (Tptr Tvoid) (dcons 3%Z Tint16
  (dcons 4%Z Tint8 (dcons 5%Z (Tarray Tint8 2)
  (dcons (-2)%Z (Tarray Tint8 3) dnil)))))).
Definition V293_event_type : type := Tstruct 411%Z V293_event_fields.

(* Actual independent event THEN, os_task.c:137-142; field lvalues are NOT
   aliases for global ready tables. Non-null body execution remains open. *)
Definition V293_task_prio_event_then (pevent yo yn xo xn byo byn : var) : stmts :=
  let rows := efield (ederef (evar pevent)) 5%Z in
  let group := efield (ederef (evar pevent)) 4%Z in
  let oldrow := earrayelem rows (evar yo) in
  let newrow := earrayelem rows (evar yn) in
  sseq (sassign oldrow (V293_task_prio_clear_expr oldrow (evar xo)))
    (sseq (sifthen (ebinop oeq (ecast oldrow Tint32) (econst32 Int.zero))
      (sassign group (V293_task_prio_clear_expr group (evar byo))))
      (sseq (sassign group (V293_task_prio_set_expr group (evar byn)))
        (sassign newrow (V293_task_prio_set_expr newrow (evar xn))))).
Definition V293_task_prio_event_read (ptcb pevent : var) : stmts :=
  sassign (evar pevent) (efield (ederef (evar ptcb)) 9%Z).
(* !(pevent == null), retaining the C cast's pointer type explicitly. *)
Definition V293_task_prio_event_test (pevent : var) : expr :=
  eunop oppsite (ebinop oeq (evar pevent) (ecast enull (Tptr V293_event_type))).
Definition V293_task_prio_event (ptcb pevent yo yn xo xn byo byn : var) : stmts :=
  sseq (V293_task_prio_event_read ptcb pevent)
    (sifthen (V293_task_prio_event_test pevent)
      (V293_task_prio_event_then pevent yo yn xo xn byo byn)).
Definition V293_task_prio_prefix_event
    (table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent : var) : stmts :=
  sseq (V293_task_prio_prefix table oldprio newprio ptcb rows group yo yn xo xn byo byn)
    (V293_task_prio_event ptcb pevent yo yn xo xn byo byn).

(* Configured os_task.c:162-166. xi is x_new (the bit INDEX), whereas
   xn is bitx_new (the bit MASK) used by the earlier bitmap statements.
   The configured Multi-Pend block between 143 and 162 is absent. *)
Definition V293_task_prio_tcb_update (ptcb newprio yn xi byn xn : var) : stmts :=
  sseq (sassign (efield (ederef (evar ptcb)) 16%Z) (evar newprio))
    (sseq (sassign (efield (ederef (evar ptcb)) 18%Z) (evar yn))
      (sseq (sassign (efield (ederef (evar ptcb)) 17%Z) (evar xi))
        (sseq (sassign (efield (ederef (evar ptcb)) 20%Z) (evar byn))
              (sassign (efield (ederef (evar ptcb)) 19%Z) (evar xn))))).

Definition V293_task_prio_prefix_event_update
    (table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent xi : var) : stmts :=
  sseq (V293_task_prio_prefix_event table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent)
    (V293_task_prio_tcb_update ptcb newprio yn xi byn xn).

(* Configured os_task.c:110/111/116/117. Fixed 32-bit analysis types:
   promoted nonnegative newprio >> 3u, unsigned &, unsigned-long 1uL <<
   promoted byte coordinate, and explicit byte conversions. *)
Definition V293_task_prio_y_expr (newprio : var) : expr :=
  ecast (ebinop orshift (ecast (evar newprio) Tint32)
    (econst32 (Int.repr 3))) Tint8.
Definition V293_task_prio_x_expr (newprio : var) : expr :=
  ecast (ebinop obitand (ecast (evar newprio) Tint32)
    (econst32 (Int.repr 7))) Tint8.
Definition V293_task_prio_mask_expr (coord : var) : expr :=
  ecast (ebinop olshift (econst32 Int.one) (ecast (evar coord) Tint32)) Tint8.
Definition V293_task_prio_coordinates (newprio yn xi byn xn : var) : stmts :=
  sseq (sassign (evar yn) (V293_task_prio_y_expr newprio))
    (sseq (sassign (evar xi) (V293_task_prio_x_expr newprio))
      (sseq (sassign (evar byn) (V293_task_prio_mask_expr yn))
            (sassign (evar xn) (V293_task_prio_mask_expr xi)))).
Definition V293_task_prio_coordinates_update
    (table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent xi : var) : stmts :=
  sseq (V293_task_prio_coordinates newprio yn xi byn xn)
    (V293_task_prio_prefix_event_update table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent xi).

(* Configured os_task.c:83--90. >= and != are normalized using ! and
   the language's < / == operators. The byte arguments are promoted. *)
Definition V293_task_prio_ge_limit (prio : var) : expr :=
  eunop oppsite (ebinop olt (ecast (evar prio) Tint32) (econst32 (Int.repr 12))).
Definition V293_task_prio_is_self (oldprio : var) : expr :=
  ebinop oeq (ecast (evar oldprio) Tint32) (econst32 (Int.repr 255)).
Definition V293_task_prio_argument_guards (oldprio newprio : var) : stmts :=
  sseq (sifthen (V293_task_prio_ge_limit oldprio)
    (sifthen (eunop oppsite (V293_task_prio_is_self oldprio))
      (srete (econst32 (Int.repr 42)))))
    (sifthen (V293_task_prio_ge_limit newprio)
      (srete (econst32 (Int.repr 42)))).

(* Configured os_task.c:93--104, starting AFTER critical entry. The real
   error branches retain ExitCritical(&cpu_sr) and their distinct error codes.
   Line 105's integer-to-pointer RESERVED guard is NOT modeled here. *)
Definition V293_task_prio_null_test (e : expr) : expr :=
  ebinop oeq e (ecast enull (Tptr V293_tcb_type)).
Definition V293_task_prio_self_read (oldprio current : var) : stmts :=
  sifthen (V293_task_prio_is_self oldprio)
    (sassign (evar oldprio) (efield (ederef (evar current)) 16%Z)).
Definition V293_task_prio_lookup (table oldprio ptcb : var) : stmts :=
  sassign (evar ptcb) (earrayelem (evar table) (evar oldprio)).
Definition V293_task_prio_entry_lookup
    (table oldprio newprio ptcb current cpu_sr : var) (exit_id : fid) : stmts :=
  sseq (sifthen (eunop oppsite (V293_task_prio_null_test
    (earrayelem (evar table) (evar newprio))))
    (sseq (scall exit_id (eaddrof (evar cpu_sr) :: nil)) (srete (econst32 (Int.repr 40)))))
    (sseq (V293_task_prio_self_read oldprio current)
      (sseq (V293_task_prio_lookup table oldprio ptcb)
        (sifthen (V293_task_prio_null_test (evar ptcb))
          (sseq (scall exit_id (eaddrof (evar cpu_sr) :: nil)) (srete (econst32 (Int.repr 41))))))).

(* OS_TCB_RESERVED, the C pointer cast of integer 1, is a non-dereferenced token.
   Lower the macro to a STATIC symbolic address, not a memory read or NULL.
   The symbol has no source-C storage object. Its global binding, absence of
   local shadowing, and separation from real TCB pointers remain explicit
   representation obligations. This is not a numerical integer-pointer cast. *)
Definition V293_task_prio_reserved_expr (reserved : var) : expr :=
  ecast (eaddrof (evar reserved)) (Tptr V293_tcb_type).
Definition V293_task_prio_reserved_test (ptcb reserved : var) : expr :=
  ebinop oeq (evar ptcb) (V293_task_prio_reserved_expr reserved).
Definition V293_task_prio_reserved_error (cpu_sr : var) (exit_id : fid) : stmts :=
  sseq (scall exit_id (eaddrof (evar cpu_sr) :: nil)) (srete (econst32 (Int.repr 67))).
Definition V293_task_prio_reserved_guard
    (ptcb reserved cpu_sr : var) (exit_id : fid) : stmts :=
  sifthen (V293_task_prio_reserved_test ptcb reserved)
    (V293_task_prio_reserved_error cpu_sr exit_id).
Definition V293_task_prio_entry_reserved
    (table oldprio newprio ptcb current reserved cpu_sr : var) (exit_id : fid) : stmts :=
  sseq (V293_task_prio_entry_lookup table oldprio newprio ptcb current cpu_sr exit_id)
    (V293_task_prio_reserved_guard ptcb reserved cpu_sr exit_id).

(* Continuous successful 93--166 segment; critical/error/return linking stays open. *)
Definition V293_task_prio_entry_update
    (table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent xi
     current reserved cpu_sr : var) (exit_id : fid) : stmts :=
  sseq (V293_task_prio_entry_reserved table oldprio newprio ptcb current reserved cpu_sr exit_id)
    (V293_task_prio_coordinates_update table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent xi).

