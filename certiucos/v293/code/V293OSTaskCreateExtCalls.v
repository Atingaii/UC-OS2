(* Exact next source call, manually alpha-renamed. The creation suffix after
   this call is still parameterized; no Hook body is supplied. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtPrefix.
Require Import Coq.Lists.List.
Import ListNotations.
Definition V293_TaskCreateExt_TCB_call err tcb prio psp bottom identity size ext opt :=
 scalle (evar err) tcb [evar prio;evar psp;evar bottom;evar identity;evar size;evar ext;evar opt].
Definition V293_TaskCreateExt_calls psp hook task arg top opt err tcb prio bottom identity size ext rest :=
 sseq (V293_TaskCreateExt_stack_call psp hook task arg top opt)
 (sseq (V293_TaskCreateExt_TCB_call err tcb prio psp bottom identity size ext opt) rest).
Definition V293_create_stack_cont psp err tcb prio bottom identity size ext opt rest ks :=
 kassignr (evar psp) (Tptr Tint32)
 (kseq (sseq (V293_TaskCreateExt_TCB_call err tcb prio psp bottom identity size ext opt) rest)
 (kseq V293_TaskCreateExt_occupied ks)).
Definition V293_create_TCB_cont err rest ks :=
 kassignr (evar err) Tint8 (kseq rest (kseq V293_TaskCreateExt_occupied ks)).
