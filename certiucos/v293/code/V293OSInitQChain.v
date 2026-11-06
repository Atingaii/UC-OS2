(* Contiguous OSInit calls at positions 1--7 (zero-based), after BeginHook.
   Manual grouping; no claim of verified C frontend or full OSInit. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSInitMemChain.
Definition V293_init_seven_calls misc ready tcbs events flags mems queues :=
  sseq (V293_init_six_calls misc ready tcbs events flags mems) (scall queues nil).
