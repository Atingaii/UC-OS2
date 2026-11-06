(* Contiguous OSInit statements 2--5, after the unresolved BeginHook.
   Grouping the first three calls changes no C statement or call order;
   this is a manual frontend normalization, not a verified translation. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSInitChain.
Definition V293_init_four_calls misc ready tcbs events :=
  sseq (V293_init_three_calls misc ready tcbs) (scall events nil).
