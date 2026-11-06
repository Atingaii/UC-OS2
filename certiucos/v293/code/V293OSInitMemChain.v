(* Contiguous OSInit statements 2--7, after unresolved BeginHook.
   Manual grouping only, not a verified C frontend. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSInitFlagChain.
Definition V293_init_six_calls misc ready tcbs events flags mems :=
  sseq (V293_init_five_calls misc ready tcbs events flags) (scall mems nil).
