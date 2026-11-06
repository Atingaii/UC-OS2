(* Joint actual bytes and the exact original priority branch. Fixtures are
   not initialization reachability or a global cache-coherence invariant. *)
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
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTargetHandoff.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchState.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.audit.probes.V293ReadyTaskInvariantProbe.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.certiucos.v293.code.V293OSSchedDispatch.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.audit.probes.V293ReadyTargetHandoffProbe.
Require Import CertiOS.certiucos.v293.proofs.V293ReadySchedCall.
Require Import CertiOS.audit.probes.V293ReadySchedCallProbe.
Require Import CertiOS.certiucos.v293.proofs.V293ReadySwitchStep.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPointerCompare.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickCountdown.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.audit.probes.V293ReadySwitchStepProbe.
Require Import CertiOS.certiucos.v293.proofs.V293ReadySourceTail.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyGlobalTrace.
Require Import CertiOS.audit.probes.V293ReadySourceTailProbe.
Require Import CertiOS.framework.proof.auxdef.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Operators_Properties.
Import ListNotations.
Local Open Scope nat_scope.
Require Import CertiOS.audit.probes.V293ReadyGlobalTraceProbe.
Require Import CertiOS.certiucos.v293.proofs.V293LocalGlobalTrace.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCriticalGlobal.
Require Import CertiOS.certiucos.v293.code.V293OSSchedGuards.
Import ListNotations.
Local Open Scope list_scope.

Require Import CertiOS.audit.probes.V293ReadyCriticalGlobalProbe.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyFullCall.
Import ListNotations.
Local Open Scope list_scope.
Require Import CertiOS.audit.probes.V293ReadyFullCallProbe.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCallGlobal.
Import ListNotations.
Local Open Scope list_scope.

Definition FGat ct C le M au := V293_local_global_at GSbase GSenvs
  (RSaux ct) ct C ((CGge,le,M),(fun _=>false),au).

Theorem FGenter : forall ct different ni nl enabled ci ip cst,
  ni<256 -> nl<256 -> exists Mbase,
  fresh Mbase 98%positive /\
  free Tint32 98%positive (CGmemory ct different ni nl)=Some Mbase /\
  V293_global_steps (RCprogram,(CGpo,CGempty,ip)) cst
    (FGat ct (curs (sfexec 113%Z nil nil),(kenil,kstop)) RTle Mbase (enabled,nil,ci))
    (FGat ct (curs CGcontrol,(kenil,FCouter)) CGle (CGmemory ct different ni nl) (enabled,nil,ci)).
Proof.
  intros ct different ni nl enabled ci ip cst Ni Nl.
  destruct (FCcaller ct different ni nl Ni Nl) as (Mbase&Back&Fresh&Init&Outside).
  exists Mbase. split;[exact Fresh| ]. split;[exact Back| ].
  unfold FGat. rewrite <- FCenv.
  exact (V293_sched_global_enter RCprogram CGpo CGempty ip GSbase GSenvs (RSaux ct) ct cst
    CGge RTle Mbase (fun _=>false) (enabled,nil,ci) kstop
    113%Z 120%Z 110%Z 111%Z 107%Z 105%Z 103%Z 106%Z 108%Z 109%Z
    98%positive (CGmemory ct different ni nl) eq_refl Fresh Init I).
Qed.

(* Exact no-switch path, stopping at the last administrative return step. *)
Theorem FGno_switch_free : forall enabled ci ip cst, exists Mbase Mtail Mf,
  fresh Mbase 98%positive /\
  free Tint32 98%positive (CGmemory OwnershipReady false 0 0)=Some Mbase /\
  V293_global_steps (RCprogram,(CGpo,CGempty,ip)) cst
    (FGat OwnershipReady (curs (sfexec 113%Z nil nil),(kenil,kstop)) RTle Mbase (enabled,nil,ci))
    (FGat OwnershipReady (curs (sfree nil None),(kenil,FCouter)) CGle Mf (enabled,nil,ci)) /\
  free Tint32 98%positive Mtail=Some Mf /\
  (forall i, (0<=i<4)%Z -> get Mf (98%positive,i)=None) /\
  (forall b i, b<>98%positive -> get Mf (b,i)=get Mtail (b,i)) /\
  load (Tptr V293_tcb_type) Mf (93%positive,0%Z)=Some (Vptr OwnershipReady) /\
  load Tint32 Mf (95%positive,0%Z)=Some (Vint32 Int.mone) /\
  load Tint8 Mf (94%positive,0%Z)=Some (V293_byteval 4).
Proof.
  intros enabled ci ip cst.
  destruct (FGenter OwnershipReady false 0 0 enabled ci ip cst ltac:(lia) ltac:(lia))
    as (Mbase&Fresh&Back&Enter).
  destruct (CGlocal_ready false enabled ci) as (Mtail&Body&After&Target&Counter&Cache).
  pose proof (FCcpu_after _ _ _ _ After) as Owned.
  destruct (V293_cpu_release CGge CGle Mtail (fun _=>false) (false,nil,enabled::ci)
    (RIabstract OwnershipReady) (spec_done None) 98%positive (Vint32 Int.zero) Atrue Owned)
    as (Mf&Free&Rest&Removed&Frame).
  assert (BodyReturn : V293_local_steps CGprogram (curs CGcontrol,(kenil,kstop))
    ((CGge,CGle,CGmemory OwnershipReady false 0 0),(fun _=>false),(enabled,nil,ci))
    (curs sret,(kenil,kstop)) ((CGge,CGle,Mtail),(fun _=>false),(enabled,nil,ci))).
  { eapply V293_local_trans;[exact Body|apply V293_sched_control_exit]. }
  exists Mbase. exists Mtail. exists Mf. split;[exact Fresh| ]. split;[exact Back| ]. split.
  - eapply V293_global_trans;[exact Enter| ].
    eapply V293_global_trans.
    + exact (V293_local_steps_global RCprogram CGpo CGempty ip _ _ _ _ BodyReturn
        113%Z CGbody RTle kstop Tvoid dnil (dcons 120%Z Tint32 dnil)
        GSbase GSenvs (RSaux OwnershipReady) OwnershipReady cst eq_refl I).
    + unfold FGat. rewrite <- FCenv.
      exact (V293_sched_global_free RCprogram CGpo CGempty ip GSbase GSenvs
        (RSaux OwnershipReady) OwnershipReady cst CGge RTle Mtail Mf (fun _=>false)
        (enabled,nil,ci) kstop 113%Z CGbody Tvoid dnil (dcons 120%Z Tint32 dnil)
        120%Z 98%positive eq_refl Free).
  - split;[exact Free| ]. split;[exact Removed| ]. split;[exact Frame| ]. split;[ |split].
    + rewrite (V293_load_block_frame _ Mtail Mf 93%positive 0%Z ltac:(intro;apply Frame;discriminate)). exact Target.
    + rewrite (V293_load_block_frame _ Mtail Mf 95%positive 0%Z ltac:(intro;apply Frame;discriminate)). exact Counter.
    + rewrite (V293_load_block_frame _ Mtail Mf 94%positive 0%Z ltac:(intro;apply Frame;discriminate)). exact Cache.
Qed.

Theorem FGno_switch : forall enabled ci ip cst, exists Mbase Mf,
  fresh Mbase 98%positive /\
  free Tint32 98%positive (CGmemory OwnershipReady false 0 0)=Some Mbase /\
  V293_global_steps (RCprogram,(CGpo,CGempty,ip)) cst
    (FGat OwnershipReady (curs (sfexec 113%Z nil nil),(kenil,kstop)) RTle Mbase (enabled,nil,ci))
    (FGat OwnershipReady (SKIP,(kenil,kstop)) RTle Mf (enabled,nil,ci)) /\
  (forall i, (0<=i<4)%Z -> get Mf (98%positive,i)=None) /\
  load (Tptr V293_tcb_type) Mf (93%positive,0%Z)=Some (Vptr OwnershipReady) /\
  load Tint32 Mf (95%positive,0%Z)=Some (Vint32 Int.mone) /\
  load Tint8 Mf (94%positive,0%Z)=Some (V293_byteval 4).
Proof.
  intros enabled ci ip cst.
  destruct (FGno_switch_free enabled ci ip cst)
    as (Mbase&Mtail&Mf&Fresh&Back&Prefix&Free&Removed&Frame&Target&Counter&Cache).
  exists Mbase. exists Mf. split;[exact Fresh| ]. split;[exact Back| ]. split.
  - eapply V293_global_trans;[exact Prefix| ].
    exact (V293_sched_global_restore RCprogram CGpo CGempty ip GSbase GSenvs
      (RSaux OwnershipReady) OwnershipReady cst CGge CGle Mf (fun _=>false)
      (enabled,nil,ci) kstop 113%Z CGbody RTle Tvoid dnil (dcons 120%Z Tint32 dnil) eq_refl).
  - split;[exact Removed| ]. split;[exact Target| ]. split;assumption.
Qed.

Theorem FGblocked : forall ct different ni nl enabled ci ip cst,
  ni<256 -> nl<256 -> (Nat.eqb ni 0 && Nat.eqb nl 0)=false -> exists Mbase,
  fresh Mbase 98%positive /\
  free Tint32 98%positive (CGmemory ct different ni nl)=Some Mbase /\
  V293_global_steps (RCprogram,(CGpo,CGempty,ip)) cst
    (FGat ct (curs (sfexec 113%Z nil nil),(kenil,kstop)) RTle Mbase (enabled,nil,ci))
    (FGat ct (SKIP,(kenil,kstop)) RTle Mbase (enabled,nil,ci)).
Proof.
  intros ct different ni nl enabled ci ip cst Ni Nl Blocked.
  destruct (FGenter ct different ni nl enabled ci ip cst Ni Nl) as (Mbase&Fresh&Free&Enter).
  exists Mbase. split;[exact Fresh| ]. split;[exact Free| ].
  eapply V293_global_trans;[exact Enter| ].
  eapply V293_global_trans.
  - exact (V293_local_steps_global RCprogram CGpo CGempty ip _ _ _ _
      (CGlocal_blocked ct different ni nl enabled ci Ni Nl Blocked)
      113%Z CGbody RTle kstop Tvoid dnil (dcons 120%Z Tint32 dnil)
      GSbase GSenvs (RSaux ct) ct cst eq_refl I).
  - unfold FGat. rewrite <- FCenv.
    exact (V293_sched_global_return RCprogram CGpo CGempty ip GSbase GSenvs (RSaux ct) ct cst
      CGge RTle (CGmemory ct different ni nl) Mbase (fun _=>false) (enabled,nil,ci)
      kstop 113%Z CGbody Tvoid dnil (dcons 120%Z Tint32 dnil) 120%Z 98%positive eq_refl Free).
Qed.

Theorem FGswitch : forall enabled ci ip cst, exists Mbase Mtail Mf,
  fresh Mbase 98%positive /\
  free Tint32 98%positive (CGmemory OwnershipWaiting true 0 0)=Some Mbase /\
  V293_global_steps (RCprogram,(CGpo,CGempty,ip)) cst
    (FGat OwnershipWaiting (curs (sfexec 113%Z nil nil),(kenil,kstop)) RTle Mbase (enabled,nil,ci))
    (set FCswitch_tasks OwnershipWaiting (SKIP,(kenil,FCpending)),
      (CGge,CGswitch_envs,Mf,(fun _=>false),CGswitch_aux enabled ci),OwnershipReady) /\
  store (Tptr V293_tcb_type) Mtail (1%positive,0%Z) (Vptr OwnershipReady)=Some Mf /\
  load (Tptr V293_tcb_type) Mf (1%positive,0%Z)=Some (Vptr OwnershipReady) /\
  load Tint32 Mf (95%positive,0%Z)=Some (Vint32 Int.zero) /\
  load Tint8 Mf (94%positive,0%Z)=Some (V293_byteval 6) /\
  (CGge,CGle,Mf,(fun _=>false),(false,nil,enabled::ci),
    set (RIabstract OwnershipWaiting) curtid (oscurt OwnershipReady),spec_done None) |=
    Amapsto (98%positive,0%Z) Tint32 true (Vint32 Int.zero) ** Atrue /\
  get (CGswitch_aux enabled ci) OwnershipWaiting=Some (false,nil,enabled::ci) /\
  get (CGswitch_aux enabled ci) OwnershipReady=Some (false,nil,nil).
Proof.
  intros enabled ci ip cst.
  destruct (FGenter OwnershipWaiting true 0 0 enabled ci ip cst ltac:(lia) ltac:(lia))
    as (Mbase&Fresh&Back&Enter).
  destruct (CGlocal_ready true enabled ci) as (Mtail&Body&Before&Target&Counter&Cache).
  destruct (V293_ready_switch_step 80%positive 81%positive 82%positive RCprogram CGpo CGempty ip
    FCswitch_tasks cst FCpending OwnershipWaiting OwnershipReady
    106%Z 93%positive 1%positive CGge CGle CGswitch_envs Mtail (fun _=>false)
    (false,nil,enabled::ci) (CGswitch_aux enabled ci) (RIabstract OwnershipWaiting)
    (spec_done None) (CGpost true 0 0) V293_tcb_type
    (map_get_set _ _ _) (map_get_set _ _ _) (map_get_set _ _ _) eq_refl Target eq_refl Before)
    as (Mf&Step&Store&After&Current&Skipped&Other&Outside).
  exists Mbase. exists Mtail. exists Mf. split;[exact Fresh| ]. split;[exact Back| ]. split.
  - eapply V293_global_trans;[exact Enter| ].
    eapply V293_global_trans.
    + exact (V293_local_steps_global RCprogram CGpo CGempty ip _ _ _ _ Body
        113%Z CGbody RTle kstop Tvoid dnil (dcons 120%Z Tint32 dnil)
        GSbase GSenvs (RSaux OwnershipWaiting) OwnershipWaiting cst eq_refl I).
    + unfold V293_global_steps.
      eapply Relation_Operators.rt1n_trans with
        (y:=(set FCswitch_tasks OwnershipWaiting (SKIP,(kenil,FCpending)),
          (CGge,CGswitch_envs,Mf,(fun _=>false),CGswitch_aux enabled ci),OwnershipReady));
        [exact Step|apply Relation_Operators.rt1n_refl].
  - split;[exact Store| ]. split;[exact Current| ]. split.
    + rewrite (V293_load_block_frame _ Mtail Mf 95%positive 0%Z
        ltac:(intro;apply Outside;left;discriminate)). exact Counter.
    + split.
      * rewrite (V293_load_block_frame _ Mtail Mf 94%positive 0%Z
          ltac:(intro;apply Outside;left;discriminate)). exact Cache.
      * split.
        -- unfold CGpost,CGframe in After. cbn [CGextra V293_owned_record_cells] in After.
           unfold V293_owned_record_cell in After. sep auto.
        -- split;[apply map_get_set| ]. unfold CGswitch_aux.
           rewrite map_get_set' by (vm_compute;discriminate). reflexivity.
Qed.

(* Only the saved caller environment in the final frame is changed. Both
   suffixes use original global sfreeend and the SAME already-freed heap. *)
Theorem FGrestore_ablation : forall enabled ci ip cst, exists Mbase Mf,
  V293_global_steps (RCprogram,(CGpo,CGempty,ip)) cst
    (FGat OwnershipReady (curs (sfexec 113%Z nil nil),(kenil,kstop)) RTle Mbase (enabled,nil,ci))
    (FGat OwnershipReady (curs (sfree nil None),(kenil,FCouter)) CGle Mf (enabled,nil,ci)) /\
  V293_global_steps (RCprogram,(CGpo,CGempty,ip)) cst
    (FGat OwnershipReady (curs (sfree nil None),(kenil,FCouter)) CGle Mf (enabled,nil,ci))
    (FGat OwnershipReady (SKIP,(kenil,kstop)) RTle Mf (enabled,nil,ci)) /\
  V293_global_steps (RCprogram,(CGpo,CGempty,ip)) cst
    (FGat OwnershipReady (curs (sfree nil None),(kenil,kcall 113%Z CGbody CGle kstop)) CGle Mf (enabled,nil,ci))
    (FGat OwnershipReady (SKIP,(kenil,kstop)) CGle Mf (enabled,nil,ci)) /\
  (forall i, (0<=i<4)%Z -> get Mf (98%positive,i)=None) /\
  get RTle 104%Z=Some (90%positive,Tint8) /\ get CGle 104%Z=None /\ RTle<>CGle.
Proof.
  intros enabled ci ip cst.
  destruct (FGno_switch_free enabled ci ip cst)
    as (Mbase&Mtail&Mf&Fresh&Back&Prefix&Free&Removed&Frame&Target&Counter&Cache).
  exists Mbase. exists Mf. split;[exact Prefix| ]. split.
  - exact (V293_sched_global_restore RCprogram CGpo CGempty ip GSbase GSenvs
      (RSaux OwnershipReady) OwnershipReady cst CGge CGle Mf (fun _=>false)
      (enabled,nil,ci) kstop 113%Z CGbody RTle Tvoid dnil (dcons 120%Z Tint32 dnil) eq_refl).
  - split.
    + exact (V293_sched_global_restore RCprogram CGpo CGempty ip GSbase GSenvs
        (RSaux OwnershipReady) OwnershipReady cst CGge CGle Mf (fun _=>false)
        (enabled,nil,ci) kstop 113%Z CGbody CGle Tvoid dnil (dcons 120%Z Tint32 dnil) eq_refl).
    + split;[exact Removed| ]. split;[reflexivity| ]. split;[reflexivity| ].
      intro Same. pose proof (f_equal (fun e:env=>get e 104%Z) Same) as Bad.
      change (Some (90%positive,Tint8)=None) in Bad. discriminate.
Qed.
