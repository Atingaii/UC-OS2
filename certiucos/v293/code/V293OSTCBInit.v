(* Fixed configured OS_TCBInit, os_core.c:2049..2101: only the continuous
   eighteen field writes, after free-list pop/critical exit and BEFORE
   OSTCBInitHook. No hook, publication, ready-list insertion or return is hidden.
   Null casts use typed-assignment null; integer conversions remain explicit. *)
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.framework.model.memory.
Require Import CertiOS.framework.model.language.
Definition V293_tcb_init_mask_expr (ptcb : var) (tag : ident) : expr :=
  ecast (ebinop olshift (econst32 Int.one)
    (ecast (efield (ederef (evar ptcb)) tag) Tint32)) Tint8.
Definition V293_TCBInit_fields
    (ptcb prio ptos pbos id stk_size pext opt : var) : stmts :=
  sseq (sassign (efield (ederef (evar ptcb)) 1%Z) (evar ptos))
    (sseq (sassign (efield (ederef (evar ptcb)) 16%Z) (evar prio))
    (sseq (sassign (efield (ederef (evar ptcb)) 14%Z) (ecast (econst32 Int.zero) Tint8))
    (sseq (sassign (efield (ederef (evar ptcb)) 15%Z) (ecast (econst32 Int.zero) Tint8))
    (sseq (sassign (efield (ederef (evar ptcb)) 13%Z) (econst32 Int.zero))
    (sseq (sassign (efield (ederef (evar ptcb)) 2%Z) (evar pext))
    (sseq (sassign (efield (ederef (evar ptcb)) 4%Z) (evar stk_size))
    (sseq (sassign (efield (ederef (evar ptcb)) 3%Z) (evar pbos))
    (sseq (sassign (efield (ederef (evar ptcb)) 5%Z) (evar opt))
    (sseq (sassign (efield (ederef (evar ptcb)) 6%Z) (evar id))
    (sseq (sassign (efield (ederef (evar ptcb)) 21%Z) (ecast (econst32 Int.zero) Tint8))
    (sseq (sassign (efield (ederef (evar ptcb)) 18%Z) (V293_task_prio_y_expr prio))
    (sseq (sassign (efield (ederef (evar ptcb)) 17%Z) (V293_task_prio_x_expr prio))
    (sseq (sassign (efield (ederef (evar ptcb)) 20%Z) (V293_tcb_init_mask_expr ptcb 18%Z))
    (sseq (sassign (efield (ederef (evar ptcb)) 19%Z) (V293_tcb_init_mask_expr ptcb 17%Z))
    (sseq (sassign (efield (ederef (evar ptcb)) 9%Z) (enull))
    (sseq (sassign (efield (ederef (evar ptcb)) 11%Z) (enull))
    ((sassign (efield (ederef (evar ptcb)) 10%Z) (enull))))))))))))))))))).
