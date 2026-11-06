(* Configured OSTaskCreateExt through the stack-initializer callsite.
   Manual frontend: ADR0004 maps RESERVED to the SAME static symbol used by
   priority-change; ADR0005 maps enter/exit markers, erasing CPU_SR byte effects.
   All three guards/error statements retained. The suffix after the stack call
   is deliberately unmodeled. No function-pointer type/port implementation is
   supplied and no complete function/call-allocation claim is made. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Definition V293_TaskCreateExt_occupied :=
 sseq (sprim excrit) (srete(econst32(Int.repr 40))).
Definition V293_TaskCreateExt_irq_error :=
 sseq (sprim excrit) (srete(econst32(Int.repr 60))).
Definition V293_TaskCreateExt_prefix table prio nesting cpu reserved suffix :=
 sseq (sassign (evar cpu) (econst32 Int.zero))
 (sseq (sifthen (ebinop olt (econst32(Int.repr 12)) (ecast(evar prio) Tint32))
   (srete(econst32(Int.repr 42))))
 (sseq (sprim encrit)
 (sseq (sifthen (ebinop olt (econst32 Int.zero) (ecast(evar nesting) Tint32))
   V293_TaskCreateExt_irq_error)
 (sseq (sifthen (ebinop oeq (earrayelem(evar table)(evar prio))
    (ecast enull (Tptr V293_tcb_type)))
   (sseq (sassign (earrayelem(evar table)(evar prio))
     (V293_task_prio_reserved_expr reserved))
    (sseq (sprim excrit) suffix)))
   V293_TaskCreateExt_occupied)))).
Definition V293_TaskCreateExt_stack_call psp hook task arg top opt :=
 scalle (evar psp) hook (evar task::evar arg::evar top::evar opt::nil).
