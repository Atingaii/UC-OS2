(* Exact type checks: no concrete initializer or ISR is supplied here. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.oscorrectness.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.lemmasfortoptheo.
Require Import CertiOS.framework.proof.toptheorem.
Require Import CertiOS.certiucos.v293.proofs.V293InitializationPartition.
Require Import CertiOS.certiucos.v293.proofs.V293GlobalSoundness.

Theorem Contract_1 : ltac:(let T := type of init_partmo' in exact T).
Proof. exact V293_init_partmo'. Qed.

Theorem Contract_2 : ltac:(let T := type of init_partmo in exact T).
Proof. exact V293_init_partmo. Qed.

Theorem Contract_3 : ltac:(let T := type of IntMethSim in exact T).
Proof. exact V293_IntMethSim. Qed.

Theorem Contract_4 : ltac:(let T := type of toptheorem' in exact T).
Proof. exact V293_toptheorem'. Qed.

Theorem Contract_5 : ltac:(let T := type of toptheorem in exact T).
Proof. exact V293_toptheorem. Qed.

Theorem Contract_6 : ltac:(let T := type of verified_os' in exact T).
Proof. exact V293_verified_os'. Qed.

Theorem Contract_7 : ltac:(let T := type of Soundness in exact T).
Proof. exact V293_Soundness. Qed.


Require Import CertiOS.certiucos.v293.proofs.V293TraceRefinement.
Theorem Contract_progsim_imply_eref_aux : ltac:(let T := type of progsim_imply_eref_aux in exact T).
Proof. exact V293_progsim_imply_eref_aux. Qed.
Theorem Contract_progsim_imply_eref : ltac:(let T := type of progsim_imply_eref in exact T).
Proof. exact V293_progsim_imply_eref. Qed.
