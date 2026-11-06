(* Complete configured OS_InitMisc, fixed V2.93.01.
   Ten unsigned global zero writes; explicit narrowing casts, implicit void
   return elaborated as sret. Manual frontend; volatile ordering retained. *)
Require Import CertiOS.framework.include_frm.
Require Import Coq.Lists.List.
Import ListNotations.
Definition V293_init_zero x tp :=
  sassign (evar x) (ecast (econst32 Int.zero) tp).
Fixpoint V293_init_zero_sequence (fields : list (var * type)) : stmts :=
  match fields with
  | [] => sskip None
  | (x,tp)::tail => sseq (V293_init_zero x tp) (V293_init_zero_sequence tail)
  end.
Definition V293_InitMisc_fields (time interrupt lock tasks running switches idle idle_run idle_max stat_ready : var) : list (var * type) :=
  [(time, Tint32); (interrupt, Tint8); (lock, Tint8); (tasks, Tint8);
   (running, Tint8); (switches, Tint32); (idle, Tint32);
   (idle_run, Tint32); (idle_max, Tint32); (stat_ready, Tint8)].
Definition V293_InitMisc_updates time interrupt lock tasks running switches idle idle_run idle_max stat_ready : stmts :=
  V293_init_zero_sequence (V293_InitMisc_fields time interrupt lock tasks running switches idle idle_run idle_max stat_ready).
Definition V293_InitMisc_function time interrupt lock tasks running switches idle idle_run idle_max stat_ready : function :=
  (Tvoid, dnil, dnil, sseq (V293_InitMisc_updates time interrupt lock tasks running switches idle idle_run idle_max stat_ready) sret).
