(* Only return dispatch is tested here, not body reachability or Hooks. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateReturn.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope Z_scope.
Definition ReturnGE : env := emp.
Definition ReturnLE : env := set emp 209%Z (32%positive,Tint8).
Definition ReturnCaller : env := set emp 777%Z (31%positive,Tint8).
Definition ReturnMemory := V293_write_byte (V293_write_byte emp 31%positive 77) 32%positive 0.
Definition ReturnK (present:bool) := if present then kcall 905%Z (sskip None) ReturnCaller kstop else kstop.
Definition ReturnStart(present:bool) := (curs(sskip(Some(Vint32 Int.zero))),(kenil,kret(ReturnK present))).
Theorem ReturnPresent : forall P, exists Mr,
 cstepstar P (ReturnStart true) (ReturnGE,ReturnLE,ReturnMemory)
 (curs(sskip(Some(Vint32 Int.zero))),(kenil,kstop)) (ReturnGE,ReturnCaller,Mr) /\
 get Mr (32%positive,0)=None /\
 load Tint8 Mr (31%positive,0)=Some(V293_byteval 77).
Proof.
 intro P. destruct(V293_create_value_return P (ReturnK true) ReturnGE ReturnLE
 ReturnCaller ReturnMemory 905%Z (sskip None) kstop (Vint32 Int.zero))
 as (Mr&Exec&Outside&Removed).
 - reflexivity.
 - cbn;repeat constructor;cbn;tauto.
 - intros b tp Member. cbn in Member. destruct Member as [E|Member];[inversion E;subst|contradiction].
   intros k K. cbn in K. assert(k=0%nat) by lia. subst k.
   unfold ReturnMemory,V293_write_byte. eexists. apply map_get_set.
 - exists Mr. split;[exact Exec| ]. split.
   + exact(Removed 32%positive Tint8 0%nat (or_introl eq_refl) ltac:(cbn;lia)).
   + transitivity (load Tint8 ReturnMemory (31%positive,0));[apply V293_load_block_frame;intro i;apply Outside;change (~In 31%positive [32%positive]);cbn;intuition congruence| ].
     unfold ReturnMemory. rewrite V293_write_byte_other_load by discriminate.
     apply V293_write_byte_load;lia.
Qed.
Theorem ReturnAbsent : forall P, ~ exists C' m',
 cstep P (ReturnStart false) (ReturnGE,ReturnLE,ReturnMemory) C' m'.
Proof.
 intros P (C'&m'&Step). unfold ReturnStart,ReturnK in Step. inversion Step;subst;try discriminate.
 all: match goal with E : (curs(sskip(Some _)),_) = (_,_) |- _ => inversion E;subst;clear E end.
 - match goal with H : estep _ _ _ _ _ _ |- _ => inversion H end.
 - match goal with H : sstep _ _ _ _ _ _ _ |- _ => inversion H;subst;cbn in *;congruence end.
Qed.
Print Assumptions ReturnPresent.
Print Assumptions ReturnAbsent.
