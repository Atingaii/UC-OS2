(* Manual source mapping of configured OS_TCBInit before OSTCBInitHook.
   ADR0005: enter/exit are normalized critical MACRO MARKERS, not executions
   of missing port bodies; CPU_SR bytes erased. Starts after local init.
   The caller supplies the UNEXECUTED real success suffix (Hook onward).
   The source's trailing exit/return66 remains in the continuation. *)
Require Import CertiOS.certiucos.v293.code.V293OSTCBInit.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Definition V293_TCBInit_empty := sseq (sprim excrit) (srete (econst32 (Int.repr 66))).
Definition V293_TCBInit_pop free ptcb :=
  sassign (evar free) (efield (ederef (evar ptcb)) 7%Z).
Definition V293_TCBInit_prefix free ptcb prio ptos pbos id stk_size pext opt suffix :=
  sseq (sprim encrit)
    (sseq (sassign (evar ptcb) (evar free))
      (sseq (sifthen (eunop oppsite (V293_task_prio_null_test (evar ptcb)))
        (sseq (V293_TCBInit_pop free ptcb)
          (sseq (sprim excrit)
            (sseq (V293_TCBInit_fields ptcb prio ptos pbos id stk_size pext opt) suffix))))
        V293_TCBInit_empty)).
