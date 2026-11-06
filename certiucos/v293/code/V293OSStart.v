(* Manually alpha-renamed fixed configured OSStart; implicit void fall-through
   is explicit sret. OSStartHighRdy remains a genuine port call, not a no-op. *)
Require Import CertiOS.framework.include_frm.
Definition V293_OSStart_guard running :=
  ebinop oeq (evar running) (econst32 Int.zero).
Definition V293_OSStart_dispatch prio high table top current port :=
  sseq (sassign (evar prio) (evar high))
   (sseq (sassign (evar top) (earrayelem (evar table) (evar high)))
    (sseq (sassign (evar current) (evar top)) (scall port nil))).
Definition V293_OSStart_branch sched prio high table top current port :=
  sseq (scall sched nil) (V293_OSStart_dispatch prio high table top current port).
Definition V293_OSStart_body running sched prio high table top current port :=
  sseq (sifthen (V293_OSStart_guard running)
    (V293_OSStart_branch sched prio high table top current port)) sret.
Definition V293_OSStart_function running sched prio high table top current port : function :=
  (Tvoid,dnil,dnil,V293_OSStart_body running sched prio high table top current port).
