(* Independent three-byte return anchor. Not reachable-body/Hook evidence. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtSuffix.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateSuffix.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope Z_scope.
Definition AnchorGE : env := set emp 99%Z (33%positive,Tint8).
Definition AnchorLE : env := set emp 209%Z (32%positive,Tint8).
Definition AnchorBase := V293_write_byte (V293_write_byte emp 31%positive 77) 32%positive 0.
Definition AnchorMemory(active:bool) := V293_write_byte AnchorBase 33%positive (if active then 1 else 0).
Definition AnchorStart := (curs(sskip None),(kenil,kseq (V293_TaskCreateExt_suffix 92%Z 101%Z 209%Z 99%Z 904%Z) kstop)).
Lemma AnchorReads : forall active,
 load Tint8 (AnchorMemory active) (32%positive,0)=Some(Vint32 Int.zero) /\
 load Tint8 (AnchorMemory active) (33%positive,0)=Some(Vint32(if active then Int.one else Int.zero)) /\
 load Tint8 (AnchorMemory active) (31%positive,0)=Some(V293_byteval 77).
Proof.
 intro active. unfold AnchorMemory,AnchorBase. split.
 - rewrite V293_write_byte_other_load by discriminate. apply (V293_write_byte_load _ _ 0);lia.
 - split.
   + destruct active;apply (V293_write_byte_load _ _);lia.
   + rewrite V293_write_byte_other_load by discriminate.
     rewrite V293_write_byte_other_load by discriminate. apply V293_write_byte_load;lia.
Qed.
Theorem AnchorExecution : forall P active,
 cstepstar P AnchorStart (AnchorGE,AnchorLE,AnchorMemory active)
 (if active then (curs(sfexec 904%Z nil nil),(kenil,kseq(srete(evar 209%Z)) kstop))
 else (curs(sskip(Some(Vint32 Int.zero))),(kenil,kret kstop)))
 (AnchorGE,AnchorLE,AnchorMemory active).
Proof.
 intros P active. destruct (AnchorReads active) as (Err&Running&Caller).
 apply (V293_OSTaskCreateExt_success_suffix P kstop AnchorGE AnchorLE (AnchorMemory active)
 92%Z 101%Z 209%Z 99%Z 904%Z 32%positive 33%positive active);try reflexivity;assumption.
Qed.
Theorem DispatchOnlyRunningByteChanges : forall a,
 a<>(33%positive,0) -> get (AnchorMemory true) a=get (AnchorMemory false) a.
Proof.
 intros [b i] Different. unfold AnchorMemory,V293_write_byte.
 rewrite !map_get_set' by congruence. reflexivity.
Qed.
Theorem DispatchDecisionChanges : forall P,
 cstepstar P AnchorStart (AnchorGE,AnchorLE,AnchorMemory false)
 (curs(sskip(Some(Vint32 Int.zero))),(kenil,kret kstop)) (AnchorGE,AnchorLE,AnchorMemory false) /\
 cstepstar P AnchorStart (AnchorGE,AnchorLE,AnchorMemory true)
 (curs(sfexec 904%Z nil nil),(kenil,kseq(srete(evar 209%Z)) kstop)) (AnchorGE,AnchorLE,AnchorMemory true) /\
 load Tint8 (AnchorMemory false) (32%positive,0)=Some(Vint32 Int.zero) /\
 load Tint8 (AnchorMemory true) (32%positive,0)=Some(Vint32 Int.zero) /\
 load Tint8 (AnchorMemory false) (31%positive,0)=Some(V293_byteval 77) /\
 load Tint8 (AnchorMemory true) (31%positive,0)=Some(V293_byteval 77).
Proof.
 intro P. destruct(AnchorReads false) as (E0&R0&C0). destruct(AnchorReads true) as (E1&R1&C1).
 split;[exact(AnchorExecution P false)| ]. split;[exact(AnchorExecution P true)| ]. repeat split;assumption.
Qed.
Print Assumptions AnchorExecution.
Print Assumptions DispatchOnlyRunningByteChanges.
Print Assumptions DispatchDecisionChanges.
