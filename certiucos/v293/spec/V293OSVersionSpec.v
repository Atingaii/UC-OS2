Require Import CertiOS.framework.include_frm.

(* Independent API contract: the locked header defines OS_VERSION as 29300u,
   despite the upstream release being named V2.93.01. *)
Definition V293_OSVersion_result : val := Vint32 (Int.repr 29300).

Definition V293_OSVersion_post (frame : asrt) : retasrt :=
  fun result => [| result = Some V293_OSVersion_result |] ** frame.
