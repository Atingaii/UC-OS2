(* The existing closed physical storage fixture is lent to the new exact
   prefix. Both task modes coexist with full arrays and unique shared slots.
   No initialization or complete interrupt execution is claimed. *)
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedExactPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedExactLocal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStoragePrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStoragePrefixWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStorageTail.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrentWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrent.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCritical.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedShared.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitch.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.code.V293OSSchedDispatch.
Require Import CertiOS.framework.include_frm.
Require Import Coq.Lists.List Lia.
Local Open Scope nat_scope.

Definition SPprogram := V293_OSSchedNew_internal_unit 200%Z 100%Z 101%Z 102%Z 103%Z 104%Z.
Definition SPspec := V293_sched_exact_spec 200%Z 100%Z 101%Z 102%Z 103%Z
  1%positive 2%positive 3%positive 4%positive V293_shared_li V293_opened_inv V293_switch_li_good.
Definition SPentry different events now aop :=
 V293_storage_prefix_entry 100%Z 101%Z 102%Z 103%Z 106%Z 107%Z
 1%positive 2%positive 3%positive 4%positive 8%positive 10%positive Tvoid 0 16
 (V293_current_mode_entries different) nil V293_idle_tid
 (V293_current_mode_tasks different) events now aop nil nil Aemp V293_idle_tid (V293_byteval 0).
Definition SPborrowed different events now aop :=
 V293_exact_storage_prefix_borrowed 100%Z 101%Z 102%Z 103%Z 106%Z 107%Z
 1%positive 2%positive 3%positive 4%positive 8%positive 10%positive Tvoid 0 16
 (V293_current_mode_entries different) Aemp V293_idle_tid
 (V293_current_mode_tasks different) events now aop nil nil Aemp (Vptr V293_idle_tid).
(* A literal output interface, not extracted by printing a candidate type. *)
Definition SPreturned different events now aop :=
 EX next:Modules.tid, [|V293_highest_ready(V293_current_mode_tasks different) next|] **
 ((<||aop||> **
   (((V293_storage_open 107%Z Tvoid V293_idle_tid (V293_current_mode_tasks different) events now next **
     (V293_inputs_full 1%positive 2%positive 3%positive 0 16 **
       (Amapsto(4%positive,0%Z) Tint8 true (V293_byteval 12) **
         (V293_array true 8%positive 0 4(Tptr Tvoid)(V293_current_mode_entries different) ** Aemp)))) **
      p_local V293_shared_li V293_idle_tid nil) ** (Ais nil ** Acs nil))) **
   ((V293_sched_globals 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive **
     V293_prefix_bindings 106%Z 103%Z 107%Z Tvoid 8%positive 10%positive) ** Aemp)).

Theorem SPenvironment : forall sd RI,
 WFFunEnv SPprogram SPspec sd V293_shared_li RI.
Proof. intros;apply V293_OSSchedNew_exact_WFFunEnv;discriminate. Qed.

Theorem SPnonempty : forall different events now aop,
 exists s,
 V293_bitmap_tasks 0 16(V293_current_mode_tasks different) /\
 V293_priority_table(V293_current_mode_entries different)(V293_current_mode_tasks different) /\
 (s |=SPentry different events now aop) /\ (s |=SPborrowed different events now aop).
Proof.
 intros different events now aop.
 destruct(V293_storage_closed_prefix_entry_witness different events now aop)
 as(s & Hb & Ht & Hcur & Hptr & Hs).
 exists s;split;[exact Hb|split;[exact Ht|split;[exact Hs| ]]].
 unfold SPborrowed;apply V293_exact_storage_prefix_lend with(rest:=nil)(old:=V293_idle_tid)(hv:=V293_byteval 0);
 try lia;[exists 12;vm_compute;intuition lia|exact Hs].
Qed.

Theorem SPactual_prefix : forall different events now aop RI r ri,
 InfRules SPspec V293_scheduler V293_shared_li RI r ri
 (SPentry different events now aop)
 (sseq(scall 200%Z nil)(sassign(evar 107%Z)(earrayelem(evar 106%Z)(evar 103%Z))))
 (SPreturned different events now aop) V293_idle_tid.
Proof.
 intros different events now aop RI r ri.
 destruct(V293_current_mode_relations different)as[Hb[Ht Hcur]].
 unfold SPentry,SPreturned.
 change(InfRules SPspec V293_scheduler V293_shared_li RI r ri
 (V293_retained_storage_prefix_entry 100%Z 101%Z 102%Z 103%Z 106%Z 107%Z
 1%positive 2%positive 3%positive 4%positive 8%positive 10%positive Tvoid 0 16
 (V293_current_mode_entries different) nil Aemp V293_idle_tid
 (V293_current_mode_tasks different) events now aop nil nil Aemp V293_idle_tid(V293_byteval 0))
 (V293_OSSched_unlocked_prefix 200%Z 106%Z 103%Z 107%Z)
 (V293_exact_storage_prefix_returned 100%Z 101%Z 102%Z 103%Z 106%Z 107%Z
 1%positive 2%positive 3%positive 4%positive 8%positive 10%positive Tvoid 0 16
 (V293_current_mode_entries different) Aemp V293_idle_tid
 (V293_current_mode_tasks different) events now aop nil nil Aemp) V293_idle_tid).
 apply V293_OSSched_exact_storage_closed_prefix;try lia;try exact I;try assumption.
 - exists 12;vm_compute;intuition lia.
 - reflexivity.
Qed.
