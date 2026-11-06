(* Fixed-profile os_core.c:663-671. The trace macro expands to an empty
   statement. Integer promotion and the final byte conversion are explicit. *)
Require Import CertiOS.framework.model.memory CertiOS.framework.model.language.
Definition V293_OSIntEnter_running (running : var) :=
 ebinop oeq (ecast (evar running) Tint32) (econst32 Int.one).
Definition V293_OSIntEnter_room (nesting : var) :=
 ebinop olt (ecast (evar nesting) Tint32) (econst32 (Int.repr 255)).
Definition V293_OSIntEnter_next (nesting : var) :=
 ecast (ebinop oplus (ecast (evar nesting) Tint32) (econst32 Int.one)) Tint8.
Definition V293_OSIntEnter_updates (running nesting : var) :=
 sifthen (V293_OSIntEnter_running running)
   (sseq (sifthen (V293_OSIntEnter_room nesting)
      (sassign (evar nesting) (V293_OSIntEnter_next nesting))) (sskip None)).
Definition V293_OSIntEnter_body (running nesting : var) :=
 sseq (V293_OSIntEnter_updates running nesting) sret.
Definition V293_OSIntEnter_function (running nesting : var) : function :=
 (Tvoid,dnil,dnil,V293_OSIntEnter_body running nesting).
