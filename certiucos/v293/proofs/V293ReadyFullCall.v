(* Real scheduler call boundaries. No pre-allocated CPU_SR is assumed.
   Existence of a body trace is a seam, instantiated independently below;
   this file alone is not WFIFun or an all-interleavings function proof. *)
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCriticalGlobal.
Require Import CertiOS.certiucos.v293.proofs.V293ReadySchedCall.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.certiucos.v293.code.V293OSSchedDispatch.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.framework.proof.memory_prop.
Require Import CertiOS.framework.proof.join_prop.
Require Import CertiOS.tactics.basetac.join_lib.
Require Import CertiOS.framework.proof.step_prop.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyGlobalTrace.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition V293_cpu_lenv saved b : env := set emp saved (b,Tint32).

Lemma V293_cpu_layout : forall saved b,
  getaddr (V293_cpu_lenv saved b)=[(b,Tint32)].
Proof.
  intros. unfold V293_cpu_lenv.
  change (getaddr (EnvMod.set EnvMod.emp saved (b,Tint32))=[(b,Tint32)]).
  reflexivity.
Qed.

(* This is the genuine sfexec boundary, before allocating any local byte. *)
Theorem V293_sched_call_enter : forall P ks ge caller M ir aux
    f saved interrupt lock schednew table high target current counter b,
  P f=Some (V293_OSSched_success_function saved interrupt lock schednew table high target current counter) ->
  fresh M b ->
  exists Ms,
    store Tint32 (allocb M b 0%Z 4) (b,0%Z) (Vint32 Int.zero)=Some Ms /\
    V293_bytes_writable Ms b 0%Z 4 /\
    free Tint32 b Ms=Some M /\
    (forall c i, c<>b -> get Ms (c,i)=get M (c,i)) /\
    V293_local_steps P (curs (sfexec f nil nil),(kenil,ks)) ((ge,caller,M),ir,aux)
      (curs (V293_sched_control interrupt lock
        (sseq (V293_OSSched_unlocked_prefix schednew table high target)
          (V293_OSSched_change high current counter (sprim (switch target))))),
        (kenil,kcall f (V293_OSSched_success_body saved interrupt lock schednew table high target current counter) caller ks))
      ((ge,V293_cpu_lenv saved b,Ms),ir,aux).
Proof.
  intros P ks ge caller M ir aux f saved interrupt lock schednew table high target current counter b Program Fresh.
  destruct (V293_success_scheduler_storage M b Fresh) as (Ms&Init&Writable&Free&Frame).
  exists Ms. split;[exact Init| ]. split;[exact Writable| ]. split;[exact Free| ]. split;[exact Frame| ].
  eapply V293_local_cons.
  { apply ostc_step. eapply stmt_step;[reflexivity| ].
    eapply sfexec_step with (d1:=dnil) (d2:=dcons saved Tint32 dnil);
      [reflexivity|reflexivity|exact Program|exact I|reflexivity]. }
  eapply V293_local_cons.
  { apply ostc_step. eapply stmt_step;[reflexivity| ]. eapply salloclv_step;
      [reflexivity|reflexivity| ].
    exists b. split;[exact Fresh| ]. split;[reflexivity| ]. split.
    - intros [v E]. rewrite map_emp_get in E. discriminate.
    - reflexivity. }
  eapply V293_local_cons. { apply ostc_step. eapply stmt_step;[reflexivity|apply sallocend_step]. }
  rewrite V293_sched_control_exact.
  eapply V293_local_cons. { apply ostc_step. eapply stmt_step;[reflexivity|apply sseq_step]. }
  eapply V293_local_trans.
  { apply V293_csteps_local. eapply V293_success_assign_zero;
      [unfold V293_cpu_lenv;apply map_get_set|exact Init]. }
  eapply V293_local_cons. { apply ostc_step. eapply stmt_step;[reflexivity|apply sskip_step]. }
  apply V293_local_refl.
Qed.

(* The fresh object is owned, so a ready-tail frame can carry it until return. *)
Lemma V293_cpu_initialized_frame : forall ge le M ir aux O op b Ms R,
  fresh M b -> (ge,le,M,ir,aux,O,op) |= R ->
  store Tint32 (allocb M b 0%Z 4) (b,0%Z) (Vint32 Int.zero)=Some Ms ->
  (ge,le,Ms,ir,aux,O,op) |= Amapsto (b,0%Z) Tint32 true (Vint32 Int.zero) ** R.
Proof.
  intros ge le M ir aux O op b Ms R Fresh Held Store.
  pose proof (V293_tick_allocate_frame ge le M ir aux O op b Tint32 R Fresh Held) as Raw.
  destruct (V293_tick_raw_slot_update (b,0%Z) Tint32 Vundef (Vint32 Int.zero)
    R ge le (allocb M b 0%Z 4) ir aux O op eq_refl Raw) as (Ms'&Store'&After).
  assert (Ms'=Ms) by congruence. subst Ms'. unfold V293_owned_record_cell in After. sep auto.
Qed.

(* Reconstructing a released fixture is a checked allocation/store, not a
   memory oracle. The caller must establish that the entire block is fresh. *)
Lemma V293_cpu_recreate : forall ge le M ir aux O op b R Mbase,
  (ge,le,M,ir,aux,O,op) |= Amapsto (b,0%Z) Tint32 true (Vint32 Int.zero) ** R ->
  free Tint32 b M=Some Mbase -> fresh Mbase b ->
  store Tint32 (allocb Mbase b 0%Z 4) (b,0%Z) (Vint32 Int.zero)=Some M.
Proof.
  intros ge le M ir aux O op b R Mbase Held Free Fresh.
  apply sat_split in Held. destruct Held as (local&rest&ol&orest&JM&JO&[Slot Empty]&Rest).
  assert (Back : free Tint32 b M=Some rest).
  { destruct Slot as (bytes&Encoding&Points). unfold free.
    rewrite <- (encode_val_length Tint32 (Vint32 Int.zero)),Encoding.
    apply free_locality2' with (M1:=local);assumption. }
  assert (Mbase=rest) by congruence. subst rest.
  destruct (V293_success_scheduler_storage Mbase b Fresh) as (Ms&Store&W&F&Frame).
  pose proof (join_mapstoval_store_allocb Mbase b Tint32 (Vint32 Int.zero) local Ms Fresh Slot Store) as Joined.
  assert (Ms=M) by (eapply join_unique;[exact Joined|apply map_join_comm;exact JM]).
  subst Ms. exact Store.
Qed.

Lemma V293_cpu_release : forall ge le M ir aux O op b v R,
  (ge,le,M,ir,aux,O,op) |= Amapsto (b,0%Z) Tint32 true v ** R ->
  exists Mf, free Tint32 b M=Some Mf /\
    (ge,le,Mf,ir,aux,O,op) |= R /\
    (forall i, (0<=i<4)%Z -> get Mf (b,i)=None) /\
    (forall c i, c<>b -> get Mf (c,i)=get M (c,i)).
Proof.
  intros ge le M ir aux O op b v R Held.
  apply sat_split in Held. destruct Held as (local&rest&ol&orest&JM&JO&[Slot Empty]&Rest).
  change (ol=emp) in Empty. subst ol. apply map_join_comm in JO. apply map_join_emp' in JO. subst orest.
  destruct Slot as (bytes&Encoding&Points).
  assert (Free : free Tint32 b M=Some rest).
  { unfold free. rewrite <- (encode_val_length Tint32 v),Encoding.
    apply free_locality2' with (M1:=local);assumption. }
  exists rest. split;[exact Free| ]. split;[exact Rest| ]. split.
  - intros i Range. replace i with (0+Z.of_nat (Z.to_nat i))%Z by (rewrite Z2Nat.id;lia).
    eapply V293_freeb_removed;[exact Free|cbn;lia].
  - intros. eapply V293_freeb_outside;[exact Free|left;exact H].
Qed.

Theorem V293_sched_call_return : forall P ks ge caller M Mf ir aux f body saved b,
  free Tint32 b M=Some Mf ->
  V293_local_steps P (curs sret,(kenil,kcall f body caller ks))
    ((ge,V293_cpu_lenv saved b,M),ir,aux)
    (SKIP,(kenil,ks)) ((ge,caller,Mf),ir,aux).
Proof.
  intros. eapply V293_local_cons.
  { apply ostc_step. eapply stmt_step;[reflexivity| ]. eapply sret_step with (al:=[(b,Tint32)]);
      [reflexivity|reflexivity|apply V293_cpu_layout]. }
  eapply V293_local_cons.
  { apply ostc_step. eapply stmt_step;[reflexivity| ]. eapply sfree_step;[reflexivity|reflexivity|exact H]. }
  eapply V293_local_cons.
  { apply ostc_step. eapply stmt_step;[reflexivity| ]. eapply sfreeend_step;reflexivity. }
  apply V293_local_refl.
Qed.

(* Continuation locality for the existing closure, not a new execution rule. *)
Lemma V293_local_steps_enclose : forall po pi C st Cf stf,
  V293_local_steps (pumerge po pi) C st Cf stf -> forall outer,
  V293_local_steps (pumerge po pi) (V293_enclose C outer) st
    (V293_enclose Cf outer) stf.
Proof.
  intros po pi C st Cf stf Trace. unfold V293_local_steps in Trace.
  remember (C,st) as initial eqn:Initial in Trace.
  remember (Cf,stf) as final eqn:Final in Trace.
  revert C st Cf stf Initial Final.
  induction Trace as [x | x y z Step Rest IH];
    intros C st Cf stf Initial Final; subst x.
  - inversion Final;subst. intros. apply V293_local_refl.
  - destruct y as [Cmid stmid]. destruct z as [Clast stlast].
    inversion Final;subst Clast stlast. intro outer.
    eapply V293_local_cons with (C1:=V293_enclose Cmid outer) (st1:=stmid).
    + destruct C as [c [ke ks]],Cmid as [c' [ke' ks']].
      exact (loststep_cont_locality c ke ks st stmid c' ke' ks' po pi outer Step).
    + eapply IH;reflexivity.
Qed.
