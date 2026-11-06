(* Contiguous OSInit statements 2--6, after unresolved BeginHook.
   Manual grouping only, not a verified C frontend. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSInitEventChain.
Definition V293_init_five_calls misc ready tcbs events flags :=
  sseq (V293_init_four_calls misc ready tcbs events) (scall flags nil).
