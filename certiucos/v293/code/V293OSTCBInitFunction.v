(* Full configured function syntax, manual alpha-renaming and ADR0005 critical
   macro mapping. CPU_SR explicit initialization retained; token effects erased.
   Both hooks stay actual calls. No port/hook implementation is supplied. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitPrefix.
Require Import CertiOS.certiucos.v293.code.V293OSTCBPublish.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Import ListNotations.
Definition V293_TCBInit_parameters :=
 dcons 101%Z Tint8 (dcons 102%Z (Tptr Tint32) (dcons 103%Z (Tptr Tint32)
 (dcons 104%Z Tint16 (dcons 105%Z Tint32 (dcons 106%Z (Tptr Tvoid)
 (dcons 107%Z Tint16 dnil)))))).
Definition V293_TCBInit_locals :=
 dcons 108%Z (Tptr V293_tcb_type) (dcons 109%Z Tint32 dnil).
Definition V293_TCBInit_success_suffix hook_init hook_create :=
 sseq (scall hook_init (evar 108%Z::nil))
  (sseq (sprim encrit)
   (sseq (sassign (earrayelem (evar 92%Z) (evar 101%Z)) (evar 108%Z))
    (sseq (sprim excrit)
     (sseq (scall hook_create (evar 108%Z::nil))
       (V293_TCB_publish 108%Z 93%Z 94%Z 95%Z 96%Z))))).
Definition V293_TCBInit_function_body hook_init hook_create :=
 sseq (sassign (evar 109%Z) (econst32 Int.zero))
 (V293_TCBInit_prefix 91%Z 108%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z
   (V293_TCBInit_success_suffix hook_init hook_create)).
Definition V293_TCBInit_function hook_init hook_create : function :=
 (Tint8,V293_TCBInit_parameters,V293_TCBInit_locals,
  V293_TCBInit_function_body hook_init hook_create).
Definition V293_TCBInit_argument_types : typelist :=
 [Tint16;Tptr Tvoid;Tint32;Tint16;Tptr Tint32;Tptr Tint32;Tint8].
