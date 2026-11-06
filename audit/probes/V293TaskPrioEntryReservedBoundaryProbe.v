(* Concrete framework limitation, not a claim that source line 105 is skip. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Theorem reserved_integer_pointer_cast_not_typed : forall ge le M,
  evaltype (ecast (econst32 Int.one) (Tptr V293_tcb_type)) (ge,le,M) = None.
Proof. intros; reflexivity. Qed.
Print Assumptions reserved_integer_pointer_cast_not_typed.
