Require Import CertiOS.certiucos.v293.proofs.V293TimeSourceAPI.
Require Import CertiOS.certiucos.v293.proofs.V293TimeSourceReadyCall.
Require Import CertiOS.certiucos.v293.proofs.V293ReadySwitchStep.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAPICall.
Require Import CertiOS.certiucos.v293.proofs.V293TimeShared.
Require Import CertiOS.certiucos.v293.proofs.V293TimeSharedSet.
Require Import CertiOS.certiucos.v293.proofs.V293TimeGetAPI.
Require Import CertiOS.certiucos.v293.proofs.V293TimeSetAPI.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.
Require Import CertiOS.certiucos.v293.code.V293TimeSource.
Require Import CertiOS.certiucos.v293.proofs.V293TimeReadyShared.
Require Import CertiOS.certiucos.v293.proofs.V293TimeReadyEntry.
Require Import Coq.Lists.List.
(* Independent literal ready/table resources; not boot reachability. *)
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293SharedStateWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrent.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.framework.proof.memory_prop.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.audit.probes.V293TaskRecordInvariantProbe.
Import ListNotations.
Local Open Scope nat_scope.

Require Import CertiOS.certiucos.v293.proofs.V293TimeReadyGlobalCall.
Require Import CertiOS.audit.probes.V293TimeSourceReadyCallProbe.

Require Import CertiOS.audit.probes.V293TimeReadyGlobalCallProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TimeContinuousGlobal.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyGlobalTrace.

(* Nonempty literal tasks are reused without changing their priority-table
   alias. This is an actual finite global trace, not initialization reachability. *)
Definition CGtrace pc ip cst selected clock enabled f args result Mf :=
  V293_global_steps(pc,(SRprogram,(fun _ => None),ip))cst
    (Gtasks f args kstop,(GGE,Gles selected,GTRmemory OwnershipWaiting clock,empisr,Gaux enabled),OwnershipWaiting)
    (set(set(Gtasks f args kstop)OwnershipWaiting(SKIP,(kenil,kstop)))OwnershipReady
      (curs(sskip result),(kenil,kstop)),(GGE,Gles selected,Mf,empisr,Gaux enabled),OwnershipReady).

Theorem CGget_nonempty_both_IE : forall pc ip cge cles CM cle selected clock enabled,
  get cles OwnershipReady=Some cle ->
  exists Ms Mc Mf,
    Gswitch pc ip (cge,cles,CM) kstop selected clock enabled 203%Z [] Ms /\
    CGtrace pc ip(cge,cles,CM)selected clock enabled 203%Z [] (Some(Vint32 clock)) Mf /\
    spec_step V293_scheduler V293_time_get_action(Gafter clock)(END(Some(Vint32 clock)))(Gafter clock) /\
    Gstate selected enabled Mf(Gafter clock)(END(Some(Vint32 clock))) |= SRcore ** CurTid OwnershipReady /\
    load Tint32 Mf(150%positive,0%Z)=Some(Vint32 clock) /\
    (forall k,k<4 ->get Mf(160%positive,Z.of_nat k)=None /\get Mf(161%positive,Z.of_nat k)=None) /\
    freels(getaddr(V293_time_call_locals 1002%Z 1003%Z 160%positive 161%positive))Mc Mf.
Proof.
  intros pc ip cge cles CM cle selected clock enabled Client.
  assert(Code:SRprogram 203%Z=Some(V293_source_OSTimeGet_function 1001%Z 1002%Z 1003%Z)).
  { exact(proj1(V293_source_time_entries 203%Z 202%Z 1001%Z 1002%Z 1003%Z ltac:(discriminate))). }
  destruct(V293_time_switch_global_get 80%positive 81%positive 82%positive 150%positive
    pc SRprogram(fun _ => None)ip(Gtasks 203%Z [] kstop)cge cles CM cle kstop OwnershipWaiting OwnershipReady
    1040%Z 82%positive 1%positive GGE emp selected(Gles selected)(GTRmemory OwnershipWaiting clock)
    empisr(false,[],[])enabled [] [](Gaux enabled)(GTRabstract OwnershipWaiting clock)Tvoid
    V293_scheduler 203%Z 1001%Z 1002%Z 1003%Z 160%positive 161%positive clock
    Client Code ltac:(discriminate)eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl(Gtarget clock)eq_refl
    ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)eq_refl
    (Gfresh clock _ (or_introl eq_refl))(Gfresh clock _ (or_intror eq_refl))
    ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)(Gslot clock)(Ginput clock V293_time_get_action))
    as(Ms&Mc&Mf&Switch&Exec&Store&Step&Final&Freed).
  exists Ms. exists Mc. exists Mf. split;[exact Switch | ]. split;[exact Exec | ].
  split;[exact Step | ]. split;[exact Final | ]. split.
  - eapply V293_source_time_clock_owned;[ | exact Final].
    unfold Gafter;rewrite map_get_set' by discriminate;apply Gslot.
  - split;[eapply SRremoved;exact Freed | exact Freed].
Qed.

Theorem CGset_nonempty_both_IE : forall pc ip cge cles CM cle selected clock enabled n,
  get cles OwnershipReady=Some cle ->
  exists Ms Mc Mf,
    Gswitch pc ip (cge,cles,CM) kstop selected clock enabled 202%Z [econst32 n] Ms /\
    CGtrace pc ip(cge,cles,CM)selected clock enabled 202%Z [econst32 n] None Mf /\
    spec_step V293_scheduler(V293_time_set_action n)(Gafter clock)(END None)(set(Gafter clock)ostmid(ostm n)) /\
    Gstate selected enabled Mf(set(Gafter clock)ostmid(ostm n))(END None) |= SRcore ** CurTid OwnershipReady /\
    load Tint32 Mf(150%positive,0%Z)=Some(Vint32 n) /\
    (forall k,k<4 ->get Mf(160%positive,Z.of_nat k)=None /\get Mf(161%positive,Z.of_nat k)=None) /\
    freels(getaddr(V293_time_call_locals 1002%Z 1003%Z 160%positive 161%positive))Mc Mf.
Proof.
  intros pc ip cge cles CM cle selected clock enabled n Client.
  assert(Code:SRprogram 202%Z=Some(V293_source_OSTimeSet_function 1001%Z 1002%Z 1003%Z)).
  { exact(proj1(proj2(V293_source_time_entries 203%Z 202%Z 1001%Z 1002%Z 1003%Z ltac:(discriminate)))). }
  destruct(V293_time_switch_global_set 80%positive 81%positive 82%positive 150%positive
    pc SRprogram(fun _ => None)ip(Gtasks 202%Z [econst32 n] kstop)cge cles CM cle kstop OwnershipWaiting OwnershipReady
    1040%Z 82%positive 1%positive GGE emp selected(Gles selected)(GTRmemory OwnershipWaiting clock)
    empisr(false,[],[])enabled [] [](Gaux enabled)(GTRabstract OwnershipWaiting clock)Tvoid
    V293_scheduler 202%Z 1001%Z 1002%Z 1003%Z 160%positive 161%positive clock n
    Client Code ltac:(discriminate)eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl(Gtarget clock)eq_refl
    ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)eq_refl
    (Gfresh clock _ (or_introl eq_refl))(Gfresh clock _ (or_intror eq_refl))
    ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)(Gslot clock)(Ginput clock(V293_time_set_action n)))
    as(Ms&Mc&Mf&Switch&Exec&Store&Step&Final&Freed).
  exists Ms. exists Mc. exists Mf. split;[exact Switch | ]. split;[exact Exec | ].
  split;[exact Step | ]. split;[exact Final | ]. split.
  - eapply V293_source_time_clock_owned;[apply map_get_set | exact Final].
  - split;[eapply SRremoved;exact Freed | exact Freed].
Qed.

Corollary CGget_set_client_witness : forall pc ip cge CM selected clock enabled n,
  (exists Mf,CGtrace pc ip(cge,sig OwnershipReady (emp:env),CM)selected clock enabled
    203%Z [] (Some(Vint32 clock))Mf) /\
  (exists Mf,CGtrace pc ip(cge,sig OwnershipReady (emp:env),CM)selected clock enabled
    202%Z [econst32 n] None Mf).
Proof.
  intros. split.
  - destruct(CGget_nonempty_both_IE pc ip cge(sig OwnershipReady(emp:env))CM emp
      selected clock enabled ltac:(apply map_get_sig))as(Ms&Mc&Mf&Switch&Trace&Rest).
    exists Mf;exact Trace.
  - destruct(CGset_nonempty_both_IE pc ip cge(sig OwnershipReady(emp:env))CM emp
      selected clock enabled n ltac:(apply map_get_sig))as(Ms&Mc&Mf&Switch&Trace&Rest).
    exists Mf;exact Trace.
Qed.

Lemma CGswitch_arbitrary_client : forall pc ip cst selected clock enabled f args,
  exists Ms,
    Gswitch pc ip cst kstop selected clock enabled f args Ms /\
    store(Tptr Tvoid)(GTRmemory OwnershipWaiting clock)(1%positive,0%Z)(Vptr OwnershipReady)=Some Ms.
Proof.
  intros pc ip cst selected clock enabled f args.
  destruct(V293_time_ready_global_switch 80%positive 81%positive 82%positive 150%positive
    pc SRprogram(fun _ => None)ip(Gtasks f args kstop)cst kstop OwnershipWaiting OwnershipReady
    1040%Z 82%positive 1%positive GGE emp selected(Gles selected)(GTRmemory OwnershipWaiting clock)
    empisr(false,[],[])(enabled,[],[])(Gaux enabled)(GTRabstract OwnershipWaiting clock)
    V293_time_get_action Tvoid eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl(Gtarget clock)eq_refl
    (Ginput clock V293_time_get_action))as(Ms&Switch&Store&Rest).
  exists Ms;auto.
Qed.

(* Only one client map binding is removed. The task switch still succeeds
   with identical OS memory, task code, contexts and interrupt flags.
   This is early call-boundary rejection, not a downstream body experiment. *)
Theorem CGmissing_client_single_factor : forall pc ip cge cles CM cle selected clock enabled f args,
  get cles OwnershipReady=Some cle ->
  exists Ms,
    Gswitch pc ip(cge,cles,CM)kstop selected clock enabled f args Ms /\
    Gswitch pc ip(cge,del cles OwnershipReady,CM)kstop selected clock enabled f args Ms /\
    get(del cles OwnershipReady)OwnershipReady=None /\
    (forall t,t<>OwnershipReady ->get(del cles OwnershipReady)t=get cles t) /\
    (forall tst C' cst' tst',
      ~ltstep(pc,(SRprogram,(fun _ => None),ip))OwnershipReady
        (curs(scall f args),(kenil,kstop))(cge,del cles OwnershipReady,CM)tst C' cst' tst').
Proof.
  intros pc ip cge cles CM cle selected clock enabled f args Client.
  destruct(CGswitch_arbitrary_client pc ip(cge,cles,CM)selected clock enabled f args)
    as(Ms&Good&Store).
  destruct(CGswitch_arbitrary_client pc ip(cge,del cles OwnershipReady,CM)selected clock enabled f args)
    as(Ms'&Bad&Store').
  rewrite Store in Store';inversion Store';subst Ms'.
  assert(Missing:get(del cles OwnershipReady)OwnershipReady=None).
  { rewrite map_del_sem;destruct(map_dec_a OwnershipReady OwnershipReady);congruence. }
  exists Ms;split;[exact Good | ];split;[exact Bad | ];split;[exact Missing | ];split.
  - intros t Apart;rewrite map_del_sem;destruct(map_dec_a OwnershipReady t);congruence.
  - intros;eapply V293_time_missing_client_binding;exact Missing.
Qed.
