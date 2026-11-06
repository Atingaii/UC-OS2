(* Configured OS_TCBInit, AFTER OSTaskCreateHook; priority table publication
   and both hook calls precede this block and are NOT erased or executed here.
   Manual ADR0005 critical-macro normalization; stop before return0. *)
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.framework.include_frm.
Definition V293_pub_field pointer tag := efield (ederef pointer) tag.
Definition V293_TCB_publish_body ptcb head group rows counter :=
  sseq (sassign (V293_pub_field (evar ptcb) 7%Z) (evar head))
   (sseq (sassign (V293_pub_field (evar ptcb) 8%Z) enull)
    (sseq (sifthen (eunop oppsite (V293_task_prio_null_test (evar head)))
       (sassign (V293_pub_field (evar head) 8%Z) (evar ptcb)))
     (sseq (sassign (evar head) (evar ptcb))
      (sseq (sassign (evar group) (V293_task_prio_set_expr (evar group) (V293_pub_field (evar ptcb) 20%Z)))
       (sseq (sassign (earrayelem (evar rows) (V293_pub_field (evar ptcb) 18%Z))
          (V293_task_prio_set_expr (earrayelem (evar rows) (V293_pub_field (evar ptcb) 18%Z))
            (V293_pub_field (evar ptcb) 19%Z)))
        (sseq (sassign (evar counter) (ecast (ebinop oplus (ecast (evar counter) Tint32) (econst32 Int.one)) Tint8))
          (sskip None))))))).
Definition V293_TCB_publish ptcb head group rows counter :=
  sseq (sprim encrit)
    (sseq (V293_TCB_publish_body ptcb head group rows counter)
      (sseq (sprim excrit) (srete (econst32 Int.zero)))).
