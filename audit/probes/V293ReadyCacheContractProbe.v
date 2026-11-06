(* Contract tests, not an installed external port or initialization reachability. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrent.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCacheContract.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyGlobalTrace.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293LocalGlobalTrace.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.audit.probes.V293TaskRecordInvariantProbe.
Require Import CertiOS.audit.probes.V293ReadyTaskInvariantProbe.
Require Import CertiOS.audit.probes.V293ReadySchedCallProbe.
Require Import CertiOS.audit.probes.V293ReadyGlobalTraceProbe.
Require Import CertiOS.audit.probes.V293ReadySourceTailProbe.
Require Import CertiOS.audit.probes.V293ReadyCriticalGlobalProbe.
Require Import CertiOS.audit.probes.V293ReadyFullCallProbe.
Require Import CertiOS.audit.probes.V293ReadyCallGlobalProbe.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Lemma SCready_priority : V293_current_task OwnershipTasks OwnershipReady 4.
Proof. split;[lia| ]. exists rdy. exists Vnull. vm_compute;reflexivity. Qed.

(* A counterexample on the already checked, complete source-call prefix. *)
Theorem SCcall_gap : forall enabled ci ip cst, exists Mbase Mf,
  V293_global_steps (RCprogram,(CGpo,CGempty,ip)) cst
    (FGat OwnershipWaiting (curs (sfexec 113%Z nil nil),(kenil,kstop)) RTle Mbase (enabled,nil,ci))
    (set FCswitch_tasks OwnershipWaiting (SKIP,(kenil,FCpending)),
      (CGge,CGswitch_envs,Mf,(fun _=>false),CGswitch_aux enabled ci),OwnershipReady) /\
  load (Tptr V293_tcb_type) Mf (1%positive,0%Z)=Some (Vptr OwnershipReady) /\
  load Tint8 Mf (94%positive,0%Z)=Some (V293_byteval 6) /\
  ~V293_cache_current OwnershipTasks OwnershipReady Mf 94%positive.
Proof.
  intros enabled ci ip cst.
  destruct (FGswitch enabled ci ip cst)
    as (Mbase&Mtail&Mf&Fresh&Back&Trace&Store&Current&Counter&Cache&CPU&Aux&Other).
  exists Mbase. exists Mf. split;[exact Trace| ]. split;[exact Current| ]. split;[exact Cache| ].
  exact (V293_cache_current_mismatch _ _ _ _ 6 4 ltac:(lia) SCready_priority Cache ltac:(lia)).
Qed.

Definition SCframe :=
  V293_owned_record_cell ((91%positive,0%Z),Tint8,V293_byteval 4) **
  (V293_owned_record_cell ((95%positive,0%Z),Tint32,Vint32 Int.zero) **
   (V293_owned_record_cell ((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady) ** CGframe 0 0)).

(* This store+switch is a contract sufficiency test, NOT a port implementation.
   The unchanged control and omitted-write control both execute pswitch_step. *)
Theorem SCwrite_switch_ablation : forall enabled ci ip cst, exists Mtail Mw Mpositive Mnegative,
  V293_local_steps CGprogram (curs CGcontrol,(kenil,kstop))
    ((CGge,CGle,CGmemory OwnershipWaiting true 0 0),(fun _=>false),(enabled,nil,ci))
    (curs (sprim (switch 106%Z)),(kenil,CGpending))
    ((CGge,CGle,Mtail),(fun _=>false),(false,nil,enabled::ci)) /\
  store Tint8 Mtail (94%positive,0%Z) (V293_byteval 4)=Some Mw /\
  lpstep (RCprogram,(CGpo,CGempty,ip)) FCswitch_tasks cst
    (CGge,CGswitch_envs,Mw,(fun _=>false),CGswitch_aux enabled ci) OwnershipWaiting
    (set FCswitch_tasks OwnershipWaiting (SKIP,(kenil,FCpending))) cst
    (CGge,CGswitch_envs,Mpositive,(fun _=>false),CGswitch_aux enabled ci) OwnershipReady /\
  lpstep (RCprogram,(CGpo,CGempty,ip)) FCswitch_tasks cst
    (CGge,CGswitch_envs,Mtail,(fun _=>false),CGswitch_aux enabled ci) OwnershipWaiting
    (set FCswitch_tasks OwnershipWaiting (SKIP,(kenil,FCpending))) cst
    (CGge,CGswitch_envs,Mnegative,(fun _=>false),CGswitch_aux enabled ci) OwnershipReady /\
  load (Tptr V293_tcb_type) Mpositive (1%positive,0%Z)=Some (Vptr OwnershipReady) /\
  load (Tptr V293_tcb_type) Mnegative (1%positive,0%Z)=Some (Vptr OwnershipReady) /\
  V293_cache_current OwnershipTasks OwnershipReady Mpositive 94%positive /\
  ~V293_cache_current OwnershipTasks OwnershipReady Mnegative 94%positive /\
  load Tint8 Mpositive (94%positive,0%Z)=Some (V293_byteval 4) /\
  load Tint8 Mnegative (94%positive,0%Z)=Some (V293_byteval 6) /\
  (forall c i, c<>94%positive \/ i<>0%Z -> get Mw (c,i)=get Mtail (c,i)) /\
  (forall c i, c<>94%positive \/ i<>0%Z -> get Mpositive (c,i)=get Mnegative (c,i)).
Proof.
  intros enabled ci ip cst.
  destruct (CGlocal_ready true enabled ci) as (Mtail & Prefix & Before & Target & Counter & Cache).
  assert (Held : (CGge,CGle,Mtail,(fun _=>false),(false,nil,enabled::ci),
    RIabstract OwnershipWaiting,spec_done None) |=
    SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) OwnershipWaiting **
      (V293_owned_record_cell ((94%positive,0%Z),Tint8,V293_byteval 6) ** SCframe)).
  { unfold CGstate,GScurrent,CGpost,STcache in Before. unfold SCframe. sep auto. }
  destruct (V293_ready_switch_cache 80%positive 81%positive 82%positive RCprogram CGpo CGempty ip
    FCswitch_tasks cst FCpending OwnershipWaiting OwnershipReady 106%Z 93%positive 1%positive 94%positive
    CGge CGle CGswitch_envs Mtail (fun _=>false) (false,nil,enabled::ci) (CGswitch_aux enabled ci)
    (RIabstract OwnershipWaiting) (spec_done None) SCframe V293_tcb_type OwnershipTasks 6 4
    (map_get_set _ _ _) (map_get_set _ _ _) (map_get_set _ _ _) eq_refl Target eq_refl
    ltac:(lia) eq_refl SCready_priority Held)
    as (Mn & Negative & NS & NA & NC & NCache & NIff & NMap & NF).
  destruct (V293_ready_cache_write 80%positive 81%positive 82%positive OwnershipWaiting SCframe
    CGge CGle Mtail (fun _=>false) (false,nil,enabled::ci) (RIabstract OwnershipWaiting)
    (spec_done None) 94%positive (V293_byteval 6) 4 ltac:(lia) Held)
    as (Mw & Write & Written & NewCache & WF).
  assert (TargetW : load (Tptr V293_tcb_type) Mw (93%positive,0%Z)=Some (Vptr OwnershipReady)).
  { rewrite (V293_load_block_frame _ Mtail Mw 93%positive 0%Z
      ltac:(intro;apply WF;left;discriminate)). exact Target. }
  destruct (V293_ready_switch_cache 80%positive 81%positive 82%positive RCprogram CGpo CGempty ip
    FCswitch_tasks cst FCpending OwnershipWaiting OwnershipReady 106%Z 93%positive 1%positive 94%positive
    CGge CGle CGswitch_envs Mw (fun _=>false) (false,nil,enabled::ci) (CGswitch_aux enabled ci)
    (RIabstract OwnershipWaiting) (spec_done None) SCframe V293_tcb_type OwnershipTasks 4 4
    (map_get_set _ _ _) (map_get_set _ _ _) (map_get_set _ _ _) eq_refl TargetW eq_refl
    ltac:(lia) eq_refl SCready_priority Written)
    as (Mp & Positive & PS & PA & PC & PCache & PIff & PMap & PF).
  assert (SameCurrent : forall i, (0<=i<4)%Z -> get Mp (1%positive,i)=get Mn (1%positive,i)).
  { intros i Bound.
    pose proof (V293_storebytes_nth _ _ _ _ _ (Z.to_nat i) PS ltac:(rewrite encode_val_length;cbn [typelen];lia)) as PByte.
    pose proof (V293_storebytes_nth _ _ _ _ _ (Z.to_nat i) NS ltac:(rewrite encode_val_length;cbn [typelen];lia)) as NByte.
    replace (0+Z.of_nat (Z.to_nat i))%Z with i in PByte,NByte by lia.
    exact (eq_trans PByte (eq_sym NByte)). }
  exists Mtail. exists Mw. exists Mp. exists Mn.
  split;[exact Prefix| ]. split;[exact Write| ]. split;[exact Positive| ]. split;[exact Negative| ].
  split;[exact PC| ]. split;[exact NC| ]. split;[apply (proj2 PIff);reflexivity| ].
  split;[intro Bad;apply (proj1 NIff) in Bad;lia| ].
  split;[exact PCache| ]. split;[exact NCache| ]. split;[exact WF| ].
  intros c i Away. destruct (Pos.eq_dec c 1%positive) as [E|N].
  - subst c. destruct (Z_lt_dec i 0) as [L|L].
    + rewrite PF by (right;left;exact L). rewrite NF by (right;left;exact L). apply WF. left;discriminate.
    + destruct (Z_le_dec 4 i) as [U|U].
      * rewrite PF by (right;right;exact U). rewrite NF by (right;right;exact U). apply WF. left;discriminate.
      * apply SameCurrent;lia.
  - rewrite PF by (left;exact N). rewrite NF by (left;exact N). apply WF. exact Away.
Qed.
