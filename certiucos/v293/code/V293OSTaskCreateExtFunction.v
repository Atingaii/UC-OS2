(* Exact configured nine-parameter/three-local function record. Manual frontend
   ADR0004/5/7, including uint32 task selector; not a machine ABI claim. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtSuffix.
Require Import Coq.Lists.List.
Import ListNotations.
Definition V293_CreateExt_parameters := dcons 201%Z Tint32 (dcons 202%Z (Tptr Tvoid) (dcons 203%Z (Tptr Tint32) (dcons 101%Z Tint8 (dcons 206%Z Tint16 (dcons 205%Z (Tptr Tint32) (dcons 207%Z Tint32 (dcons 208%Z (Tptr Tvoid) (dcons 204%Z Tint16 (dnil))))))))).
Definition V293_CreateExt_locals := dcons 108%Z (Tptr Tint32) (dcons 209%Z Tint8 (dcons 109%Z Tint32 (dnil))).
Definition V293_CreateExt_body table nesting reserved running sched hook tcb :=
 V293_TaskCreateExt_body table 101%Z nesting 109%Z reserved 108%Z hook 201%Z 202%Z 203%Z 204%Z 209%Z tcb 205%Z 206%Z 207%Z 208%Z running sched.
Definition V293_CreateExt_function table nesting reserved running sched hook tcb :=
 (Tint8,V293_CreateExt_parameters,V293_CreateExt_locals,V293_CreateExt_body table nesting reserved running sched hook tcb).
Definition V293_CreateExt_argument_types := [Tint16;(Tptr Tvoid);Tint32;(Tptr Tint32);Tint16;Tint8;(Tptr Tint32);(Tptr Tvoid);Tint32].
