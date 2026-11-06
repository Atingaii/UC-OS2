(* Exact configured suffix after err=OS_TCBInit(...), manually alpha-renamed.
   Empty successful statement and failure rollback are retained. Critical
   macros follow ADR0005; no scheduler body or port implementation is supplied. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtPrefix.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtCalls.
Definition V293_TaskCreateExt_rollback table prio :=
 sseq (sprim encrit)
 (sseq (sassign (earrayelem(evar table)(evar prio))
   (ecast enull (Tptr V293_tcb_type))) (sprim excrit)).
Definition V293_TaskCreateExt_suffix table prio err running sched :=
 sseq (sif (ebinop oeq (evar err) (econst32 Int.zero))
   (sseq (sskip None)
    (sifthen (ebinop oeq (evar running) (econst32 Int.one)) (scall sched nil)))
   (V293_TaskCreateExt_rollback table prio))
  (srete (evar err)).
Definition V293_TaskCreateExt_body table prio nesting cpu reserved
 psp hook task arg top opt err tcb bottom identity size ext running sched :=
 V293_TaskCreateExt_prefix table prio nesting cpu reserved
 (V293_TaskCreateExt_calls psp hook task arg top opt err tcb prio bottom identity size ext
  (V293_TaskCreateExt_suffix table prio err running sched)).
