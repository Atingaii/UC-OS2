(* Nonempty callers of the same generated two-function unit. The input owns
   real ready records; no successful execution is an input hypothesis. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeSourceReadyCall.
Require Import CertiOS.certiucos.v293.proofs.V293TimeSourceAPI.
Require Import CertiOS.certiucos.v293.code.V293TimeSource.
Require Import CertiOS.certiucos.v293.proofs.V293TimeReadyShared.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAPICall.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAPILifecycle.
Require Import CertiOS.certiucos.v293.proofs.V293TimeShared.
Require Import CertiOS.certiucos.v293.proofs.V293TimeGetAPI.
Require Import CertiOS.certiucos.v293.proofs.V293TimeSetAPI.
Require Import CertiOS.certiucos.v293.proofs.V293TimeSharedSet.
Require Import CertiOS.certiucos.v293.proofs.V293TimeGetAPI.
Require Import CertiOS.certiucos.v293.proofs.V293TimeSetAPI.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TimeNamesGood.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.audit.probes.V293TimeReadyEntryProbe.
Require Import CertiOS.audit.probes.V293TimeReadySharedProbe.
Require Import CertiOS.audit.probes.V293TimeAPICallProbe.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.memory_prop.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.framework.proof.lmachLib.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope nat_scope.

Definition SRprogram := V293_source_time_program 203%Z 202%Z 1001%Z 1002%Z 1003%Z.
Definition SRcore := V293_time_ready_core 80%positive 81%positive 82%positive 150%positive.
Definition SRstate caller enabled M O op : RstateOP :=
  (JGE,caller,M,empisr,(enabled,[],[]),O,op).
Definition SRget caller ks ct clock enabled Mf :=
  V293_local_steps SRprogram (curs(scall 203%Z []),(kenil,ks))
    ((JGE,caller,TRmemory ct clock),empisr,(enabled,[],[]))
    (curs(sskip(Some(Vint32 clock))),(kenil,ks)) ((JGE,caller,Mf),empisr,(enabled,[],[])).
Definition SRset caller ks ct clock enabled n Mf :=
  V293_local_steps SRprogram (curs(scall 202%Z [econst32 n]),(kenil,ks))
    ((JGE,caller,TRmemory ct clock),empisr,(enabled,[],[]))
    (curs(sskip None),(kenil,ks)) ((JGE,caller,Mf),empisr,(enabled,[],[])).

Lemma SRinput : forall caller enabled ct clock op,
  SRstate caller enabled(TRmemory ct clock)(TRabstract ct clock)op |= SRcore ** CurTid ct.
Proof.
  intros. unfold SRstate,SRcore.
  eapply V293_source_time_entry_core;exact(Jcore_and_current ct clock op).
Qed.
Lemma SRset_map : forall ct clock n,
  set(TRabstract ct clock)ostmid(ostm n)=TRabstract ct n.
Proof.
  intros. apply OSAbstMod.extensionality. intro id.
  change(get(set(TRabstract ct clock)ostmid(ostm n))id=get(TRabstract ct n)id).
  unfold TRabstract. destruct id;repeat rewrite map_get_set' by discriminate;
    repeat rewrite map_get_set;reflexivity.
Qed.
Lemma SRslot : forall ct clock, get(TRabstract ct clock)ostmid=Some(ostm clock).
Proof. intros. unfold TRabstract. apply map_get_set. Qed.
Lemma SRclock : forall caller enabled M ct clock op R,
  SRstate caller enabled M(TRabstract ct clock)op |= SRcore ** R ->
  load Tint32 M(150%positive,0%Z)=Some(Vint32 clock).
Proof.
  intros. eapply V293_source_time_clock_owned;[apply SRslot | exact H].
Qed.
Lemma SRremoved : forall Mc Mf,
  freels(getaddr(V293_time_call_locals 1002%Z 1003%Z 160%positive 161%positive))Mc Mf ->
  forall k,k<4 -> get Mf(160%positive,Z.of_nat k)=None /\ get Mf(161%positive,Z.of_nat k)=None.
Proof.
  intros Mc Mf Fs k K.
  change(freels((160%positive,Tint32)::(161%positive,Tint32)::nil)Mc Mf)in Fs.
  inversion Fs as [ | b1 t1 ls1 M0 M1 M2 F1 Fs1];subst.
  inversion Fs1 as [ | b2 t2 ls2 M3 M4 M5 F2 Fs2];subst.
  inversion Fs2;subst. unfold free in F1,F2. split.
  - erewrite V293_freeb_outside;[ | exact F2 | left;discriminate].
    replace(Z.of_nat k)with(0+Z.of_nat k)%Z by reflexivity.
    eapply V293_freeb_removed;[exact F1 | exact K].
  - replace(Z.of_nat k)with(0+Z.of_nat k)%Z by reflexivity.
    eapply V293_freeb_removed;[exact F2 | exact K].
Qed.

Theorem SRget_nonempty_both_IE : forall caller ks ct clock enabled,
  exists Mc Mf,
    SRget caller ks ct clock enabled Mf /\
    spec_step V293_scheduler V293_time_get_action(TRabstract ct clock)
      (END(Some(Vint32 clock)))(TRabstract ct clock) /\
    SRstate caller enabled Mf(TRabstract ct clock)(END(Some(Vint32 clock))) |= SRcore ** CurTid ct /\
    load Tint32 Mf(150%positive,0%Z)=Some(Vint32 clock) /\
    (forall k,k<4 -> get Mf(160%positive,Z.of_nat k)=None /\ get Mf(161%positive,Z.of_nat k)=None) /\
    freels(getaddr(V293_time_call_locals 1002%Z 1003%Z 160%positive 161%positive))Mc Mf.
Proof.
  intros caller ks ct clock enabled.
  assert(Code:SRprogram 203%Z=Some(V293_source_OSTimeGet_function 1001%Z 1002%Z 1003%Z)).
  { exact(proj1(V293_source_time_entries 203%Z 202%Z 1001%Z 1002%Z 1003%Z ltac:(discriminate))). }
  destruct(V293_source_time_get_ready_call 80%positive 81%positive 82%positive 150%positive ct
    SRprogram V293_scheduler ks JGE caller(TRmemory ct clock)empisr enabled [] [](TRabstract ct clock)
    203%Z 1001%Z 1002%Z 1003%Z 160%positive 161%positive clock Code
    ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)ltac:(reflexivity)
    (Cfresh ct clock _ (or_introl eq_refl))(Cfresh ct clock _ (or_intror eq_refl))
    ltac:(discriminate)(SRslot ct clock)(SRinput caller enabled ct clock V293_time_get_action))
    as(Mc&Mf&Exec&Prefix&Suffix&Step&Closed&Final&Freed).
  exists Mc. exists Mf. split;[exact Exec | ]. split;[exact Step | ]. split;[exact Final | ].
  split;[eapply SRclock;exact Final | ]. split;[eapply SRremoved;exact Freed | exact Freed].
Qed.

Theorem SRset_nonempty_both_IE : forall caller ks ct clock enabled n,
  exists Mc Mf,
    SRset caller ks ct clock enabled n Mf /\
    spec_step V293_scheduler(V293_time_set_action n)(TRabstract ct clock)(END None)(TRabstract ct n) /\
    SRstate caller enabled Mf(TRabstract ct n)(END None) |= SRcore ** CurTid ct /\
    load Tint32 Mf(150%positive,0%Z)=Some(Vint32 n) /\
    (forall k,k<4 -> get Mf(160%positive,Z.of_nat k)=None /\ get Mf(161%positive,Z.of_nat k)=None) /\
    freels(getaddr(V293_time_call_locals 1002%Z 1003%Z 160%positive 161%positive))Mc Mf.
Proof.
  intros caller ks ct clock enabled n.
  assert(Code:SRprogram 202%Z=Some(V293_source_OSTimeSet_function 1001%Z 1002%Z 1003%Z)).
  { exact(proj1(proj2(V293_source_time_entries 203%Z 202%Z 1001%Z 1002%Z 1003%Z ltac:(discriminate)))). }
  destruct(V293_source_time_set_ready_call 80%positive 81%positive 82%positive 150%positive ct
    SRprogram V293_scheduler ks JGE caller(TRmemory ct clock)empisr enabled [] [](TRabstract ct clock)
    202%Z 1001%Z 1002%Z 1003%Z 160%positive 161%positive clock n Code
    ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)ltac:(reflexivity)
    (Cfresh ct clock _ (or_introl eq_refl))(Cfresh ct clock _ (or_intror eq_refl))
    ltac:(discriminate)(SRslot ct clock)(SRinput caller enabled ct clock(V293_time_set_action n)))
    as(Mc&Mf&Exec&Prefix&Suffix&Step&Closed&Final&Freed).
  rewrite SRset_map in Step,Closed,Final.
  exists Mc. exists Mf. split;[exact Exec | ]. split;[exact Step | ]. split;[exact Final | ].
  split;[eapply SRclock;exact Final | ]. split;[eapply SRremoved;exact Freed | exact Freed].
Qed.

(* The same actual return heap and operation endpoint; only the abstract clock
   slot is held at its old value. No syntactic, argument or link rejection. *)
Theorem SRset_stale_abstract_control : forall caller ks ct clock enabled n,
  n<>clock -> exists Mc Mf,
    SRset caller ks ct clock enabled n Mf /\
    spec_step V293_scheduler(V293_time_set_action n)(TRabstract ct clock)(END None)(TRabstract ct n) /\
    load Tint32 Mf(150%positive,0%Z)=Some(Vint32 n) /\
    SRstate caller enabled Mf(TRabstract ct n)(END None) |= SRcore ** CurTid ct /\
    ~ SRstate caller enabled Mf(TRabstract ct clock)(END None) |= SRcore ** CurTid ct /\
    (forall k,k<4 -> get Mf(160%positive,Z.of_nat k)=None /\ get Mf(161%positive,Z.of_nat k)=None) /\
    freels(getaddr(V293_time_call_locals 1002%Z 1003%Z 160%positive 161%positive))Mc Mf.
Proof.
  intros caller ks ct clock enabled n Different.
  destruct(SRset_nonempty_both_IE caller ks ct clock enabled n)
    as(Mc&Mf&Exec&Step&Final&Load&Removed&Freed).
  exists Mc. exists Mf. split;[exact Exec | ]. split;[exact Step | ]. split;[exact Load | ].
  split;[exact Final | ]. split.
  - intro Wrong. pose proof(SRclock caller enabled Mf ct clock(END None)(CurTid ct)Wrong)as Old.
    congruence.
  - split;assumption.
Qed.

Theorem SRsource_ready_component : forall Spec lg,
  GoodI (V293_time_ready_inv 80%positive 81%positive 82%positive 150%positive)
    V293_scheduler(V293_time_names_li 1001%Z 150%positive) /\
  APIRule SRprogram(V293_source_time_spec 203%Z 202%Z)Spec V293_scheduler
    (V293_time_names_li 1001%Z 150%positive)
    (V293_time_ready_inv 80%positive 81%positive 82%positive 150%positive)lg.
Proof. intros. apply V293_source_time_ready_coherent;discriminate. Qed.
