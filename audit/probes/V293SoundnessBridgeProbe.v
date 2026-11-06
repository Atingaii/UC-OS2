(* A nonempty shared/local entry for the universal task relation.
   No boot reachability or interrupt-body correctness is claimed. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeSourceTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293TimeSourceAPI.
Require Import CertiOS.certiucos.v293.proofs.V293TimeReadyAPI.
Require Import CertiOS.certiucos.v293.proofs.V293TimeReadyShared.
Require Import CertiOS.certiucos.v293.proofs.V293TimeReadyEntry.
Require Import CertiOS.certiucos.v293.proofs.V293TimeNamesGood.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.audit.probes.V293TimeReadyEntryProbe.
Require Import CertiOS.audit.probes.V293TimeReadySharedProbe.
Require Import CertiOS.audit.probes.V293TimeReadyAPIProbe.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.soundness.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.simulation.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.framework.proof.oscorrectness.
Require Import CertiOS.framework.proof.toptheorem.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List.


Require Import CertiOS.audit.probes.V293TimeSourceTaskSimProbe.
Require Import CertiOS.certiucos.v293.proofs.V293CallSoundness.
Require Import CertiOS.certiucos.v293.proofs.V293Soundness.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTaskSimulation.

Theorem V293_internal_sim_checked :
  WFFuncsSim RAinternal RAspec V293_scheduler RAli TSinv.
Proof.
  apply V293_WFFunEnv_imply_WFFuncsSim.
  apply V293_OSSchedNew_WFFunEnv;discriminate.
Qed.

Theorem V293_get_set_sim_checked : forall ip intspec t clock n,
  no_call_api_ipu ip TSapi -> EqDomInt ip intspec ->
  exists Ml Ms Ol Os,
    join Ml Ms (TRmemory t clock) /\ join Ol Os (TRabstract t clock) /\
    InitTaskSt RAli t (TSstate JGE Ml,Ol) /\
    satp (TSstate JGE Ms) Os (INV TSinv) /\
    TaskSim (TSpc n,(TSapi,RAinternal,ip)) (nilcont(TSclientbody n))
      (TSstate JGE Ml) (TSpc n,(TSaspec,intspec,V293_scheduler))
      (nilcont(TSclientbody n)) Ol RAli TSinv (InitTaskSt RAli t) t.
Proof.
  intros ip intspec t clock n Calls Dom.
  destruct (TSnonempty_joint_entry t clock) as (Ml&Ms&Ol&Os&JM&JO&Entry&Inv).
  destruct (TSstructure n) as [Sep [IC [Syn [Client Stmt]]]].
  exists Ml. exists Ms. exists Ol. exists Os.
  split;[exact JM | ]. split;[exact JO | ]. split;[exact Entry | ]. split;[exact Inv | ].
  eapply V293_time_source_tasksim_sound with (Spec:=RAspec);try discriminate;
    try eassumption;exact V293_internal_sim_checked.
Qed.

Require Import CertiOS.framework.proof.fcallsound.
Require Import CertiOS.framework.proof.rulesound.
Require Import CertiOS.framework.proof.lemmasfortoptheo.

(* Exact old propositions are reused, not weaker replacements. *)
Theorem Contract_1 : ltac:(let T := type of call_ignore_exprlist_sim in exact T).
Proof. exact V293_call_ignore_exprlist_sim. Qed.

Theorem Contract_2 : ltac:(let T := type of call_rule_sound in exact T).
Proof. exact V293_call_rule_sound. Qed.

Theorem Contract_3 : ltac:(let T := type of calle_rule_sound in exact T).
Proof. exact V293_calle_rule_sound. Qed.

Theorem Contract_4 : ltac:(let T := type of calle_rule_lvar_sound in exact T).
Proof. exact V293_calle_rule_lvar_sound. Qed.

Theorem Contract_5 : ltac:(let T := type of RuleSound in exact T).
Proof. exact V293_rule_sound. Qed.

Theorem Contract_6 : ltac:(let T := type of WFFunEnv_imply_WFFuncsSim in exact T).
Proof. exact V293_WFFunEnv_imply_WFFuncsSim. Qed.

Theorem Contract_7 : ltac:(let T := type of ApiMethSim in exact T).
Proof. exact V293_ApiMethSim. Qed.

Theorem Contract_8 : ltac:(let T := type of V293_source_time_ready_method in exact T).
Proof. exact V293_time_source_method_sound. Qed.

Theorem Contract_9 : ltac:(let T := type of V293_source_time_ready_tasksim in exact T).
Proof. exact V293_time_source_tasksim_sound. Qed.

Theorem Contract_10 : ltac:(let T := type of TSinternal_checked in exact T).
Proof. exact V293_internal_sim_checked. Qed.

Theorem Contract_11 : ltac:(let T := type of TSget_set_client in exact T).
Proof. exact V293_get_set_sim_checked. Qed.

