(* Fixed configured os_core.c:937-1008. Source/body identity is recorded in
   audit/logs/stage28-time-tick/protocol.json BEFORE this translation.
   These are executable statements, not a verified C frontend or a linked
   function definition. Local declarations/allocation and implicit void return
   are not represented by the body below. CPU hook is retained, not erased. *)
Require Import CertiOS.framework.model.memory CertiOS.framework.model.language.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.

Definition V293_tick_field (ptcb : var) (field : ident) : expr :=
  efield (ederef (evar ptcb)) field.
Definition V293_tick_eq (e : expr) (n : Z) : expr :=
  ebinop oeq e (econst32 (Int.repr n)).
Definition V293_tick_ne (e : expr) (n : Z) : expr :=
  eunop oppsite (V293_tick_eq e n).

(* 990-1001. PEND_ANY = 1|2|4|16|32 = 55; suspend bit = 8.
   The pending-result byte is independent of OSTCBStat. Integer promotions,
   complement narrowing and compound-assignment conversion remain explicit. *)
Definition V293_tick_expiry (ptcb rows group : var) : stmts :=
  let stat := V293_tick_field ptcb 14%Z in
  let pend := V293_tick_field ptcb 15%Z in
  let mask := ebinop obitand (ecast stat Tint32) (econst32 (Int.repr 55)) in
  let row := earrayelem (evar rows) (V293_tick_field ptcb 18%Z) in
  sseq
    (sif (V293_tick_ne mask 0)
      (sseq (sassign stat (V293_task_prio_clear_expr stat (econst32 (Int.repr 55))))
            (sassign pend (ecast (econst32 Int.one) Tint8)))
      (sassign pend (ecast (econst32 Int.zero) Tint8)))
    (sifthen (V293_tick_eq
      (ebinop obitand (ecast stat Tint32) (econst32 (Int.repr 8))) 0)
      (sseq (sassign (evar group)
         (V293_task_prio_set_expr (evar group) (V293_tick_field ptcb 20%Z)))
        (sassign row (V293_task_prio_set_expr row (V293_tick_field ptcb 19%Z))))).

(* 986-1002. Unsigned 32-bit decrement, with the subsequent load kept. *)
Definition V293_tick_delay (ptcb rows group : var) : stmts :=
  let delay := V293_tick_field ptcb 13%Z in
  sifthen (V293_tick_ne delay 0)
    (sseq (sassign delay (ebinop ominus delay (econst32 Int.one)))
      (sifthen (V293_tick_eq delay 0) (V293_tick_expiry ptcb rows group))).
Definition V293_tick_advance (ptcb : var) : stmts :=
  sassign (evar ptcb) (V293_tick_field ptcb 7%Z).
Definition V293_tick_guard (ptcb : var) : expr :=
  V293_tick_ne (ecast (V293_tick_field ptcb 16%Z) Tint32) 12.

(* Keep the Next assignment BEFORE exit, as in lines 1004-1005. *)
Definition V293_tick_raw_iteration (ptcb rows group saved : var) (enter exit : fid) : stmts :=
  sseq (scall enter (eaddrof (evar saved) :: nil))
    (sseq (V293_tick_delay ptcb rows group)
      (sseq (V293_tick_advance ptcb) (scall exit (eaddrof (evar saved) :: nil)))).
Definition V293_tick_iteration (ptcb rows group : var) : stmts :=
  sseq (sprim encrit)
    (sseq (V293_tick_delay ptcb rows group)
      (sseq (V293_tick_advance ptcb) (sprim excrit))).

(* Complete configured executable body including initialized cpu_sr, CPU hook,
   increment BEFORE OSRunning test, and the whole while. No proof of all these
   statements is claimed by the zero-delay iteration contract. *)
Definition V293_tick_raw_body
    (ptcb rows group saved now running head : var) (hook enter exit : fid) : stmts :=
  sseq (sassign (evar saved) (econst32 Int.zero))
    (sseq (scall hook nil)
      (sseq (scall enter (eaddrof (evar saved) :: nil))
        (sseq (sassign (evar now) (ebinop oplus (evar now) (econst32 Int.one)))
          (sseq (scall exit (eaddrof (evar saved) :: nil))
            (sifthen (V293_tick_eq (ecast (evar running) Tint32) 1)
              (sseq (sassign (evar ptcb) (evar head))
                (swhile (V293_tick_guard ptcb)
                  (V293_tick_raw_iteration ptcb rows group saved enter exit)))))))).

Definition V293_tick_body
    (ptcb rows group saved now running head : var) (hook : fid) : stmts :=
  sseq (sassign (evar saved) (econst32 Int.zero))
    (sseq (scall hook nil)
      (sseq (sprim encrit)
        (sseq (sassign (evar now) (ebinop oplus (evar now) (econst32 Int.one)))
          (sseq (sprim excrit)
            (sifthen (V293_tick_eq (ecast (evar running) Tint32) 1)
              (sseq (sassign (evar ptcb) (evar head))
                (swhile (V293_tick_guard ptcb)
                  (V293_tick_iteration ptcb rows group)))))))).
