(* Contiguous three-call slice of configured OSInit AFTER OSInitHookBegin.
   The port hook is not removed or assumed to be an empty function. *)
Require Import CertiOS.framework.include_frm.
Definition V293_init_three_calls misc ready tcbs :=
  sseq (scall misc nil) (sseq (scall ready nil) (scall tcbs nil)).
