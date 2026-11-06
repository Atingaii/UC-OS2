(* Fixed configured os_core.c:693-736, source identity checked before modeling.
   Empty trace statements remain explicit. CPU calls are not primitives or
   empty implementations. The function includes the saved-status local slot. *)
Require Import CertiOS.framework.model.memory CertiOS.framework.model.language.
Require Import CertiOS.certiucos.v293.code.V293OSIntEnter.
Require Import CertiOS.certiucos.v293.code.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.code.V293OSSchedDispatch.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Definition V293_OSIntExit_positive (nesting : var) :=
 ebinop olt (econst32 Int.zero) (ecast (evar nesting) Tint32).
Definition V293_OSIntExit_previous (nesting : var) :=
 ecast (ebinop ominus (ecast (evar nesting) Tint32) (econst32 Int.one)) Tint8.
Definition V293_OSIntExit_decrement (nesting : var) :=
 sifthen (V293_OSIntExit_positive nesting)
   (sassign (evar nesting) (V293_OSIntExit_previous nesting)).
Definition V293_OSIntExit_guards (nesting lock : var) (dispatch : stmts) :=
 sif (V293_OSSched_zero nesting)
   (sif (V293_OSSched_zero lock) dispatch (sskip None)) (sskip None).
Definition V293_OSIntExit_nesting_dispatch nesting lock dispatch :=
 sseq (V293_OSIntExit_decrement nesting) (V293_OSIntExit_guards nesting lock dispatch).
Definition V293_OSIntExit_dispatch (table high target current counter : var)
 (sched_id int_switch : fid) :=
 sseq (V293_OSSched_unlocked_prefix sched_id table high target)
   (sif (V293_OSSched_different high current)
     (sseq (V293_OSSched_increment counter)
       (sseq (sskip None) (scall int_switch nil))) (sskip None)).
Definition V293_OSIntExit_body (running nesting lock saved table high target current counter : var)
 (sched_id enter exit int_switch : fid) :=
 sseq (sassign (evar saved) (econst32 Int.zero))
   (sseq (sifthen (V293_OSIntEnter_running running)
     (sseq (scall enter (eaddrof (evar saved)::nil))
       (sseq (V293_OSIntExit_nesting_dispatch nesting lock
         (V293_OSIntExit_dispatch table high target current counter sched_id int_switch))
         (scall exit (eaddrof (evar saved)::nil))))) sret).
Definition V293_OSIntExit_function running nesting lock saved table high target current counter
 sched_id enter exit int_switch : function :=
 (Tvoid,dnil,dcons saved Tint32 dnil,
   V293_OSIntExit_body running nesting lock saved table high target current counter
     sched_id enter exit int_switch).
