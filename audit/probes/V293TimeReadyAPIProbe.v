(* Component and independent old physical witnesses. Fixture transport below
   is not a complete API trace, initialization, or interrupt installation. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeReadyAPI.
Require Import CertiOS.certiucos.v293.proofs.V293TimeReadyShared.
Require Import CertiOS.certiucos.v293.proofs.V293TimeGetAPI.
Require Import CertiOS.certiucos.v293.proofs.V293TimeGetLink.
Require Import CertiOS.certiucos.v293.proofs.V293TimeSetAPI.
Require Import CertiOS.certiucos.v293.proofs.V293TimeSharedSet.
Require Import CertiOS.certiucos.v293.proofs.V293TimeNamesGood.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.code.V293OSVersion.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.audit.probes.V293TimeReadySharedProbe.
Require Import CertiOS.audit.probes.V293TimeGetAPIProbe.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.audit.probes.V293ReadyTaskInvariantProbe.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.toptheorem.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition RAapi := V293_clock_api_unit 201%Z 202%Z 203%Z 1001%Z 1002%Z 1003%Z.
Definition RAli := V293_time_names_li 1001%Z 150%positive.
Definition RAspec := V293_OSSchedNew_internal_spec 200%Z 100%Z 101%Z 102%Z 103%Z
  70%positive 81%positive 80%positive 90%positive RAli
  (V293_time_names_local_good 1001%Z 150%positive).
Definition RAinternal := V293_OSSchedNew_internal_unit 200%Z 100%Z 101%Z 102%Z 103%Z 104%Z.

Theorem RAcommon_component : forall lg,
  GoodI TRinv V293_scheduler RAli /\
  WFAPI RAapi (V293_clock_api_spec 201%Z 202%Z 203%Z) RAli RAspec
    V293_scheduler TRinv lg /\
  WFIFun RAinternal RAspec V293_scheduler TRinv RAli /\
  no_fun_same RAapi RAinternal.
Proof. intros. apply V293_ready_clock_components_checked;discriminate. Qed.

Theorem RAactual_entries :
  let P := pumerge RAapi RAinternal in
  P 201%Z=Some V293_OSVersion_function /\
  P 202%Z=Some (V293_TimeSet_function 1001%Z 1002%Z 1003%Z) /\
  P 203%Z=Some (V293_TimeGet_function 1001%Z 1002%Z 1003%Z) /\
  P 200%Z=Some (V293_OSSchedNew_function 100%Z 101%Z 102%Z 103%Z 104%Z).
Proof. apply V293_clock_linked_entries;discriminate. Qed.

Theorem RAget_builders : forall t lg,
  exists pre post,
    Some pre=BuildPreA' RAapi 203%Z V293_TimeGet_api [] RAli t lg /\
    Some post=BuildRetA' RAapi 203%Z V293_TimeGet_api [] RAli t lg /\
    InfRules RAspec V293_scheduler RAli TRinv post Afalse pre
      (V293_TimeGet_body 1001%Z 1002%Z 1003%Z) Afalse t.
Proof.
  intros. eexists. eexists. split;[reflexivity | ]. split;[reflexivity | ].
  eapply V293_TimeGet_ready_api_contract with (P:=RAapi)(f:=203%Z)(vl:=nil)(lg:=lg);try discriminate.
  - apply V293_time_names_local_good.
  - apply V293_time_names_noabs.
  - apply V293_time_names_global.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.
Theorem RAset_builders : forall t lg n,
  exists pre post,
    Some pre=BuildPreA' RAapi 202%Z V293_TimeSet_api [Vint32 n] RAli t lg /\
    Some post=BuildRetA' RAapi 202%Z V293_TimeSet_api [Vint32 n] RAli t lg /\
    InfRules RAspec V293_scheduler RAli TRinv post Afalse pre
      (V293_TimeSet_body 1001%Z 1002%Z 1003%Z) Afalse t.
Proof.
  intros. eexists. eexists. split;[reflexivity | ]. split;[reflexivity | ].
  eapply V293_TimeSet_ready_api_contract with (P:=RAapi)(f:=202%Z)(vl:=[Vint32 n])(lg:=lg);try discriminate.
  - apply V293_time_names_local_good.
  - apply V293_time_names_noabs.
  - apply V293_time_names_global.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.
Theorem RAargument_controls : forall t lg,
  BuildPreA' RAapi 203%Z V293_TimeGet_api [Vint32 Int.zero] RAli t lg=None /\
  BuildPreA' RAapi 202%Z V293_TimeSet_api [] RAli t lg=None /\
  BuildPreA' RAapi 202%Z V293_TimeSet_api [Vnull] RAli t lg=None.
Proof. intros. repeat split;reflexivity. Qed.

(* Independent nonempty strong resource; does not invoke the new API proofs.
   The old ready fixture already owns actual TCB, table, bitmap and clock bytes. *)
Theorem RAcore_nonempty : forall ct n,
  TRstate ct n (TRmemory ct n) |=
    V293_time_ready_core 80%positive 81%positive 82%positive 150%positive ** Atrue.
Proof.
  intros. eapply V293_time_ready_switch_core_frame with (t:=ct). apply TRliteral_spatial.
Qed.
Theorem RAclock_control : forall ct n bad,
  bad<>n ->
  TRstate ct n (TRmemory ct n) |=
    V293_time_ready_core 80%positive 81%positive 82%positive 150%positive ** Atrue /\
  V293_ready_loads (TRmemory ct bad) 80%positive 81%positive 82%positive 16 0 RTentries /\
  ~ TRstate ct n (TRmemory ct bad) |=
    V293_time_ready_core 80%positive 81%positive 82%positive 150%positive ** Atrue.
Proof.
  intros ct n bad Different. split;[apply RAcore_nonempty | ].
  split;[apply TRready_loads | ]. intro Held.
  destruct (V293_time_ready_clock_agreement _ _ _ _ _ _ Held) as [v [Time Physical]].
  change (get (TRabstract ct n) ostmid=Some(ostm v)) in Time.
  unfold TRabstract in Time. rewrite map_get_set in Time.
  change (load Tint32 (TRmemory ct bad) (150%positive,0%Z)=Some(Vint32 v)) in Physical.
  pose proof (TRclock_load ct bad). assert (v=n) by congruence. congruence.
Qed.

(* Ready rejection is independent of clock rejection: clock stays exactly n,
   both bitmaps have the same group and are nonempty. Reuses the frozen store. *)
Theorem RAready_control : forall ct n, exists Mf,
  TRstate ct n (TRmemory ct n) |= SWINVt TRinv ct /\
  store Tint8 (TRmemory ct n) (80%positive,0%Z) (V293_byteval 32)=Some Mf /\
  (forall a, a<>(80%positive,0%Z) -> get Mf a=get (TRmemory ct n) a) /\
  load Tint8 Mf (80%positive,0%Z)=Some(V293_byteval 32) /\
  load Tint32 Mf (150%positive,0%Z)=Some(Vint32 n) /\
  V293_bitmap_ready 32 0 5 /\
  V293_ready_group 32 0=V293_ready_group 16 0 /\
  ~ TRstate ct n Mf |= SWINVt TRinv ct.
Proof. apply TRready_ablation. Qed.

Theorem RAget_exact_on_ready_heap : forall sd ct n result O',
  spec_step sd V293_time_get_action (TRabstract ct n) (END result) O' ->
  result=Some(Vint32 n) /\ O'=TRabstract ct n.
Proof.
  intros. eapply checked_get_read_result_exact;[ | exact H].
  unfold TRabstract. apply map_get_set.
Qed.
Theorem RAget_positive : forall sd ct n,
  spec_step sd V293_time_get_action (TRabstract ct n)
    (END (Some(Vint32 n))) (TRabstract ct n) /\
  load Tint32 (TRmemory ct n) (150%positive,0%Z)=Some(Vint32 n) /\
  V293_ready_loads (TRmemory ct n) 80%positive 81%positive 82%positive 16 0 RTentries.
Proof.
  intros. split.
  - apply V293_time_get_transition. unfold TRabstract. apply map_get_set.
  - split;[apply TRclock_load | apply TRready_loads].
Qed.
Theorem RAget_wrong_return : forall sd ct,
  ~spec_step sd V293_time_get_action (TRabstract ct (Int.repr 37))
    (END(Some(Vint32(Int.repr 38)))) (TRabstract ct (Int.repr 37)).
Proof.
  intros sd ct H. apply RAget_exact_on_ready_heap in H. destruct H as [Wrong _].
  vm_compute in Wrong. discriminate.
Qed.
(* This is an abstract action, NOT a physical setter execution. *)
Theorem RAset_preserves_nonclock_slots : forall sd ct old n,
  spec_step sd (V293_time_set_action n) (TRabstract ct old)
    (END None) (set (TRabstract ct old) ostmid (ostm n)) /\
  (forall key, key<>ostmid ->
    get (set (TRabstract ct old) ostmid (ostm n)) key=get (TRabstract ct old) key).
Proof.
  intros. split.
  - eapply V293_time_set_transition. unfold TRabstract. apply map_get_set.
  - intros. apply map_get_set'. congruence.
Qed.
