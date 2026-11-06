(* Configured OSTimeDly, fixed V2.93.01 Source/os_time.c:53-81.
   See stage316 source identity. Only the critical blocking updates below are
   presently proved; guard/call/return ASTs are not whole-function proof credit.
   V293_dly_body starts after the configured cpu_sr=0 local initializer;
   encrit/excrit are the accepted normalized critical-section boundary. *)
Require Import CertiOS.framework.model.memory CertiOS.framework.model.language.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.

Definition V293_dly_field current tag := efield (ederef (evar current)) tag.
Definition V293_dly_row rows y := earrayelem (evar rows) (evar y).
Definition V293_dly_clear_row current rows y :=
 sassign (V293_dly_row rows y)
  (V293_task_prio_clear_expr (V293_dly_row rows y) (V293_dly_field current 19%Z)).
Definition V293_dly_clear_group current group :=
 sassign (evar group) (V293_task_prio_clear_expr (evar group) (V293_dly_field current 20%Z)).
Definition V293_dly_group_if current rows group y :=
 sifthen (ebinop oeq (ecast (V293_dly_row rows y) Tint32) (econst32 Int.zero))
  (V293_dly_clear_group current group).
(* Sequence grouping does not insert or remove any configured C statement. *)
Definition V293_dly_before_delay current rows group y :=
 sseq (sassign (evar y) (V293_dly_field current 18%Z))
 (sseq (V293_dly_clear_row current rows y)
 (sseq (sskip None) (* empty OS_TRACE_TASK_SUSPENDED expansion *)
       (V293_dly_group_if current rows group y))).
Definition V293_dly_updates current rows group y ticks :=
 sseq (V293_dly_before_delay current rows group y)
 (sseq (sassign (V293_dly_field current 13%Z) (evar ticks))
       (sskip None)). (* empty OS_TRACE_TASK_DLY expansion *)
Definition V293_dly_positive current rows group y ticks sched :=
 sseq (sprim encrit)
  (sseq (V293_dly_updates current rows group y ticks)
   (sseq (sprim excrit) (scall sched nil))).
Definition V293_dly_body current rows group y ticks nesting lock sched :=
 sseq (sifthen (ebinop olt (econst32 Int.zero) (ecast (evar nesting) Tint32)) sret)
 (sseq (sifthen (ebinop olt (econst32 Int.zero) (ecast (evar lock) Tint32)) sret)
 (sseq (sifthen (ebinop olt (econst32 Int.zero) (evar ticks))
  (V293_dly_positive current rows group y ticks sched)) sret)).
