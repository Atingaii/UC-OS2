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

Definition FCouter := kcall 113%Z CGbody RTle kstop.
Definition FCpending := kseq (sseq (sprim excrit) sret) FCouter.

Lemma FCcpu_entry : forall ct different ni nl ci, ni<256 -> nl<256 ->
  CGstate ct (CGmemory ct different ni nl) ci |=
    Amapsto (98%positive,0%Z) Tint32 true (Vint32 Int.zero) ** Atrue.
Proof.
  intros. pose proof (CGentry ct different ni nl ci H H0) as Held.
  unfold CGframe in Held. cbn [CGextra V293_owned_record_cells] in Held.
  unfold V293_owned_record_cell in Held. sep auto.
Qed.

Lemma FCcpu_outside : forall ct different ni nl i, (i<0 \/ 4<=i)%Z ->
  get (CGmemory ct different ni nl) (98%positive,i)=None.
Proof.
  intros ct different ni nl i Outside.
  unfold CGmemory,CGwith. rewrite !map_merge_semp by reflexivity.
  rewrite RToutside by discriminate.
  unfold CGoutputs,CGcells,STcells,CGextra.
  cbn [OwnershipCellsMemory app OwnershipCellMemory].
  rewrite !map_merge_semp by reflexivity.
  repeat rewrite V293_encoded_memory_outside by (left;discriminate).
  rewrite V293_encoded_memory_outside by (cbn;tauto).
  rewrite map_emp_get. unfold RTdecoder,V293_nat_memory.
  rewrite V293_encoded_memory_outside by (left;discriminate). reflexivity.
Qed.

(* The caller memory is obtained by a checked free. Entire-block freshness
   plus reconstruction proves the actual entry allocation yields this fixture. *)
Theorem FCcaller : forall ct different ni nl, ni<256 -> nl<256 -> exists Mbase,
  free Tint32 98%positive (CGmemory ct different ni nl)=Some Mbase /\
  fresh Mbase 98%positive /\
  store Tint32 (allocb Mbase 98%positive 0%Z 4) (98%positive,0%Z)
    (Vint32 Int.zero)=Some (CGmemory ct different ni nl) /\
  (forall b i, b<>98%positive -> get Mbase (b,i)=get (CGmemory ct different ni nl) (b,i)).
Proof.
  intros ct different ni nl Ni Nl.
  pose proof (FCcpu_entry ct different ni nl nil Ni Nl) as Owned.
  destruct (V293_cpu_release CGge CGle (CGmemory ct different ni nl) (fun _=>false)
    (false,nil,nil) (RIabstract ct) (spec_done None) 98%positive (Vint32 Int.zero) Atrue Owned)
    as (Mbase & Free & Rest & Removed & Frame).
  assert (Fresh : fresh Mbase 98%positive).
  { intros b i E [v Read]. subst b.
    destruct (Z_lt_ge_dec i 0) as [Neg|Nonneg].
    - assert (Outside : get Mbase (98%positive,i)=get (CGmemory ct different ni nl) (98%positive,i)).
      { eapply V293_freeb_outside;[exact Free|right;left;exact Neg]. }
      assert (Missing : get Mbase (98%positive,i)=None).
      { transitivity (get (CGmemory ct different ni nl) (98%positive,i));[exact Outside|apply FCcpu_outside;left;exact Neg]. }
      pose proof (eq_trans (eq_sym Missing) Read) as Bad. discriminate Bad.
    - destruct (Z_lt_ge_dec i 4) as [Within|Above].
      + pose proof (eq_trans (eq_sym (Removed i ltac:(lia))) Read) as Bad. discriminate Bad.
      + assert (Outside : get Mbase (98%positive,i)=get (CGmemory ct different ni nl) (98%positive,i)).
        { eapply V293_freeb_outside;[exact Free|right;right;cbn;lia]. }
        assert (Missing : get Mbase (98%positive,i)=None).
        { transitivity (get (CGmemory ct different ni nl) (98%positive,i));[exact Outside|apply FCcpu_outside;right;lia]. }
        pose proof (eq_trans (eq_sym Missing) Read) as Bad. discriminate Bad. }
  exists Mbase. split;[exact Free| ]. split;[exact Fresh| ]. split;[ |exact Frame].
  eapply V293_cpu_recreate; eauto.
Qed.

Lemma FCenv : V293_cpu_lenv 120%Z 98%positive=CGle.
Proof. unfold V293_cpu_lenv,CGle. apply map_set_emp. Qed.

Theorem FCenter : forall ct different ni nl enabled ci,
  ni<256 -> nl<256 -> exists Mbase,
  fresh Mbase 98%positive /\
  free Tint32 98%positive (CGmemory ct different ni nl)=Some Mbase /\
  V293_local_steps CGprogram (curs (scall 113%Z nil),(kenil,kstop))
    ((CGge,RTle,Mbase),(fun _=>false),(enabled,nil,ci))
    (curs CGcontrol,(kenil,FCouter))
    ((CGge,CGle,CGmemory ct different ni nl),(fun _=>false),(enabled,nil,ci)).
Proof.
  intros ct different ni nl enabled ci Ni Nl.
  destruct (FCcaller ct different ni nl Ni Nl) as (Mbase&Free&Fresh&Rebuild&Frame).
  destruct (V293_sched_call_enter CGprogram kstop CGge RTle Mbase (fun _=>false)
    (enabled,nil,ci) 113%Z 120%Z 110%Z 111%Z 107%Z 105%Z 103%Z 106%Z 108%Z 109%Z
    98%positive eq_refl Fresh) as (Ms&Init&Writable&Back&Outside&Enter).
  pose proof (eq_trans (eq_sym Init) Rebuild) as Same. inversion Same;subst Ms.
  exists Mbase. split;[exact Fresh| ]. split;[exact Free| ].
  eapply V293_local_cons.
  { apply ostc_step. eapply stmt_step;[reflexivity|apply snpcall_step]. }
  rewrite FCenv in Enter. exact Enter.
Qed.

Theorem FCblocked_return : forall ct different ni nl enabled ci,
  ni<256 -> nl<256 -> (Nat.eqb ni 0 && Nat.eqb nl 0)=false -> exists Mbase,
  free Tint32 98%positive (CGmemory ct different ni nl)=Some Mbase /\
  fresh Mbase 98%positive /\
  V293_local_steps CGprogram (curs (scall 113%Z nil),(kenil,kstop))
    ((CGge,RTle,Mbase),(fun _=>false),(enabled,nil,ci))
    (SKIP,(kenil,kstop)) ((CGge,RTle,Mbase),(fun _=>false),(enabled,nil,ci)).
Proof.
  intros ct different ni nl enabled ci Ni Nl Blocked.
  destruct (FCenter ct different ni nl enabled ci Ni Nl) as (Mbase&Fresh&Free&Enter).
  exists Mbase. split;[exact Free| ]. split;[exact Fresh| ].
  eapply V293_local_trans;[exact Enter| ].
  pose proof (V293_local_steps_enclose CGpo CGempty _ _ _ _
    (CGlocal_blocked ct different ni nl enabled ci Ni Nl Blocked) FCouter) as Body.
  eapply V293_local_trans;[exact Body| ].
  rewrite <- FCenv. exact (V293_sched_call_return CGprogram kstop CGge RTle _ _ (fun _=>false)
    (enabled,nil,ci) 113%Z CGbody 120%Z 98%positive Free).
Qed.

Lemma FCcpu_after : forall ct different M ci,
  CGstate ct M ci |= SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) ct ** CGpost different 0 0 ->
  CGstate ct M ci |= Amapsto (98%positive,0%Z) Tint32 true (Vint32 Int.zero) ** Atrue.
Proof.
  intros ct different M ci Held. unfold CGpost,CGframe in Held.
  cbn [CGextra V293_owned_record_cells] in Held.
  unfold V293_owned_record_cell in Held. sep auto.
Qed.

Theorem FCno_switch_return : forall enabled ci, exists Mbase Mtail Mf,
  fresh Mbase 98%positive /\
  V293_local_steps CGprogram (curs (scall 113%Z nil),(kenil,kstop))
    ((CGge,RTle,Mbase),(fun _=>false),(enabled,nil,ci))
    (SKIP,(kenil,kstop)) ((CGge,RTle,Mf),(fun _=>false),(enabled,nil,ci)) /\
  free Tint32 98%positive Mtail=Some Mf /\
  (forall i, (0<=i<4)%Z -> get Mf (98%positive,i)=None) /\
  (forall b i, b<>98%positive -> get Mf (b,i)=get Mtail (b,i)) /\
  load (Tptr V293_tcb_type) Mf (93%positive,0%Z)=Some (Vptr OwnershipReady) /\
  load Tint32 Mf (95%positive,0%Z)=Some (Vint32 Int.mone) /\
  load Tint8 Mf (94%positive,0%Z)=Some (V293_byteval 4).
Proof.
  intros enabled ci.
  destruct (FCenter OwnershipReady false 0 0 enabled ci ltac:(lia) ltac:(lia))
    as (Mbase&Fresh&Back&Enter).
  destruct (CGlocal_ready false enabled ci) as (Mtail&Body&After&Target&Counter&Cache).
  pose proof (FCcpu_after _ _ _ _ After) as Owned.
  destruct (V293_cpu_release CGge CGle Mtail (fun _=>false)
    (false,nil,enabled::ci) (RIabstract OwnershipReady) (spec_done None)
    98%positive (Vint32 Int.zero) Atrue Owned) as (Mf&Free&Rest&Removed&Frame).
  exists Mbase. exists Mtail. exists Mf. split;[exact Fresh| ]. split.
  - eapply V293_local_trans;[exact Enter| ].
    pose proof (V293_local_steps_enclose CGpo CGempty _ _ _ _ Body FCouter) as Framed.
    eapply V293_local_trans;[exact Framed| ].
    eapply V293_local_trans;[apply V293_sched_control_exit| ].
    rewrite <- FCenv. exact (V293_sched_call_return CGprogram kstop CGge RTle _ _ (fun _=>false)
      (enabled,nil,ci) 113%Z CGbody 120%Z 98%positive Free).
  - split;[exact Free| ]. split;[exact Removed| ]. split;[exact Frame| ].
    split;[ |split].
    + rewrite (V293_load_block_frame _ Mtail Mf 93%positive 0%Z ltac:(intro;apply Frame;discriminate)). exact Target.
    + rewrite (V293_load_block_frame _ Mtail Mf 95%positive 0%Z ltac:(intro;apply Frame;discriminate)). exact Counter.
    + rewrite (V293_load_block_frame _ Mtail Mf 94%positive 0%Z ltac:(intro;apply Frame;discriminate)). exact Cache.
Qed.

Theorem FCready_to_switch : forall enabled ci, exists Mbase Mtail,
  fresh Mbase 98%positive /\
  free Tint32 98%positive (CGmemory OwnershipWaiting true 0 0)=Some Mbase /\
  V293_local_steps CGprogram (curs (scall 113%Z nil),(kenil,kstop))
    ((CGge,RTle,Mbase),(fun _=>false),(enabled,nil,ci))
    (curs (sprim (switch 106%Z)),(kenil,FCpending))
    ((CGge,CGle,Mtail),(fun _=>false),(false,nil,enabled::ci)) /\
  CGstate OwnershipWaiting Mtail (enabled::ci) |=
    SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) OwnershipWaiting ** CGpost true 0 0 /\
  load (Tptr V293_tcb_type) Mtail (93%positive,0%Z)=Some (Vptr OwnershipReady) /\
  load Tint32 Mtail (95%positive,0%Z)=Some (Vint32 Int.zero) /\
  load Tint8 Mtail (94%positive,0%Z)=Some (V293_byteval 6).
Proof.
  intros enabled ci.
  destruct (FCenter OwnershipWaiting true 0 0 enabled ci ltac:(lia) ltac:(lia))
    as (Mbase&Fresh&Back&Enter).
  destruct (CGlocal_ready true enabled ci) as (Mtail&Body&After&Target&Counter&Cache).
  exists Mbase. exists Mtail. split;[exact Fresh| ]. split;[exact Back| ]. split.
  - eapply V293_local_trans;[exact Enter| ].
    exact (V293_local_steps_enclose CGpo CGempty _ _ _ _ Body FCouter).
  - split;[exact After| ]. split;[exact Target| ]. split;assumption.
Qed.

Definition FCswitch_tasks : tasks := set GSbase OwnershipWaiting
  (curs (sprim (switch 106%Z)),(kenil,FCpending)).

(* The prefix is local loststep closure; the final step is original lpstep.
   They share exactly Mtail. No global classification of the full call is claimed. *)
Theorem FCswitch_after_call : forall enabled ci ip cst, exists Mbase Mtail Mf,
  fresh Mbase 98%positive /\
  V293_local_steps CGprogram (curs (scall 113%Z nil),(kenil,kstop))
    ((CGge,RTle,Mbase),(fun _=>false),(enabled,nil,ci))
    (curs (sprim (switch 106%Z)),(kenil,FCpending))
    ((CGge,CGle,Mtail),(fun _=>false),(false,nil,enabled::ci)) /\
  lpstep (RCprogram,(CGpo,CGempty,ip)) FCswitch_tasks cst
    (CGge,CGswitch_envs,Mtail,(fun _=>false),CGswitch_aux enabled ci) OwnershipWaiting
    (set FCswitch_tasks OwnershipWaiting (SKIP,(kenil,FCpending))) cst
    (CGge,CGswitch_envs,Mf,(fun _=>false),CGswitch_aux enabled ci) OwnershipReady /\
  load (Tptr V293_tcb_type) Mf (1%positive,0%Z)=Some (Vptr OwnershipReady) /\
  (CGge,CGle,Mf,(fun _=>false),(false,nil,enabled::ci),
    set (RIabstract OwnershipWaiting) curtid (oscurt OwnershipReady),spec_done None) |=
    Amapsto (98%positive,0%Z) Tint32 true (Vint32 Int.zero) ** Atrue /\
  get (CGswitch_aux enabled ci) OwnershipWaiting=Some (false,nil,enabled::ci) /\
  get (CGswitch_aux enabled ci) OwnershipReady=Some (false,nil,nil).
Proof.
  intros enabled ci ip cst.
  destruct (FCready_to_switch enabled ci) as (Mbase&Mtail&Fresh&Back&Trace&Before&Target&Counter&Cache).
  destruct (V293_ready_switch_step 80%positive 81%positive 82%positive RCprogram CGpo CGempty ip
    FCswitch_tasks cst FCpending OwnershipWaiting OwnershipReady
    106%Z 93%positive 1%positive CGge CGle CGswitch_envs Mtail (fun _=>false)
    (false,nil,enabled::ci) (CGswitch_aux enabled ci) (RIabstract OwnershipWaiting)
    (spec_done None) (CGpost true 0 0) V293_tcb_type
    (map_get_set _ _ _) (map_get_set _ _ _) (map_get_set _ _ _) eq_refl Target eq_refl Before)
    as (Mf&Step&Store&After&Current&Skipped&Other&Outside).
  exists Mbase. exists Mtail. exists Mf.
  split;[exact Fresh| ]. split;[exact Trace| ]. split;[exact Step| ]. split;[exact Current| ]. split.
  - unfold CGpost,CGframe in After. cbn [CGextra V293_owned_record_cells] in After.
    unfold V293_owned_record_cell in After. sep auto.
  - split;[apply map_get_set| ]. unfold CGswitch_aux.
    rewrite map_get_set' by (vm_compute;discriminate). reflexivity.
Qed.

(* Single administrative-release fault: replace the one-object free list by
   the empty list at the same boundary, without changing any memory or aux. *)
Theorem FCfree_ablation : forall enabled ci, exists Mbase Mtail Mf,
  V293_local_steps CGprogram (curs (scall 113%Z nil),(kenil,kstop))
    ((CGge,RTle,Mbase),(fun _=>false),(enabled,nil,ci))
    (curs (sfree ((98%positive,Tint32)::nil) None),(kenil,FCouter))
    ((CGge,CGle,Mtail),(fun _=>false),(enabled,nil,ci)) /\
  V293_local_steps CGprogram (curs (sfree ((98%positive,Tint32)::nil) None),(kenil,FCouter))
    ((CGge,CGle,Mtail),(fun _=>false),(enabled,nil,ci))
    (SKIP,(kenil,kstop)) ((CGge,RTle,Mf),(fun _=>false),(enabled,nil,ci)) /\
  V293_local_steps CGprogram (curs (sfree nil None),(kenil,FCouter))
    ((CGge,CGle,Mtail),(fun _=>false),(enabled,nil,ci))
    (SKIP,(kenil,kstop)) ((CGge,RTle,Mtail),(fun _=>false),(enabled,nil,ci)) /\
  (forall i, (0<=i<4)%Z -> get Mf (98%positive,i)=None) /\
  load Tint32 Mtail (98%positive,0%Z)=Some (Vint32 Int.zero) /\
  (forall b i, b<>98%positive -> get Mf (b,i)=get Mtail (b,i)).
Proof.
  intros enabled ci.
  destruct (FCenter OwnershipReady false 0 0 enabled ci ltac:(lia) ltac:(lia))
    as (Mbase&Fresh&Back&Enter).
  destruct (CGlocal_ready false enabled ci) as (Mtail&Body&After&Target&Counter&Cache).
  pose proof (FCcpu_after _ _ _ _ After) as Owned.
  destruct (V293_cpu_release CGge CGle Mtail (fun _=>false)
    (false,nil,enabled::ci) (RIabstract OwnershipReady) (spec_done None)
    98%positive (Vint32 Int.zero) Atrue Owned) as (Mf&Free&Rest&Removed&Frame).
  exists Mbase. exists Mtail. exists Mf. split.
  - eapply V293_local_trans;[exact Enter| ].
    eapply V293_local_trans;[exact (V293_local_steps_enclose CGpo CGempty _ _ _ _ Body FCouter)| ].
    eapply V293_local_trans;[apply V293_sched_control_exit| ].
    eapply V293_local_cons;[ |apply V293_local_refl].
    apply ostc_step. eapply stmt_step;[reflexivity| ].
    eapply sret_step;[reflexivity|reflexivity| ]. rewrite <- FCenv. apply V293_cpu_layout.
  - split.
    + eapply V293_local_cons.
      { apply ostc_step. eapply stmt_step;[reflexivity| ].
        eapply sfree_step;[reflexivity|reflexivity|exact Free]. }
      eapply V293_local_cons;[ |apply V293_local_refl].
      apply ostc_step. eapply stmt_step;[reflexivity| ]. eapply sfreeend_step;reflexivity.
    + split.
      * eapply V293_local_cons;[ |apply V293_local_refl].
        apply ostc_step. eapply stmt_step;[reflexivity| ]. eapply sfreeend_step;reflexivity.
      * split;[exact Removed| ]. split;[ |exact Frame].
        change (load Tint32 (getmem (CGstate OwnershipReady Mtail (enabled::ci)))
          (98%positive,0%Z)=Some (Vint32 Int.zero)).
        eapply V293_record_star_load_r;[ |exact After].
        unfold CGpost. do 4 eapply V293_record_star_load_r.
        unfold CGframe. eapply V293_record_star_load_l.
        cbn [CGextra V293_owned_record_cells]. do 2 eapply V293_record_star_load_r.
        eapply V293_record_star_load_l. apply V293_owned_record_cell_load.
Qed.
