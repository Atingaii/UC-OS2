(* The Ready continuation is an explicitly installed environment fixture,
   NOT OS_Sched selecting or waking the blocked Waiting task. No source edit. *)
Require Import CertiOS.audit.probes.V293ReadySwitchStepProbe.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.audit.probes.V293ReadyCallGlobalProbe.
Require Import CertiOS.audit.probes.V293ReadyCriticalGlobalProbe.
Require Import CertiOS.audit.probes.V293ReadyFullCallProbe.
Require Import CertiOS.audit.probes.V293ReadyGlobalTraceProbe.
Require Import CertiOS.audit.probes.V293ReadySourceTailProbe.
Require Import CertiOS.audit.probes.V293ReadySchedCallProbe.
Require Import CertiOS.audit.probes.V293ReadyTaskInvariantProbe.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.audit.probes.V293TaskRecordInvariantProbe.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyResumption.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCallGlobal.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyFullCall.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293ReadySwitchStep.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchState.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293LocalGlobalTrace.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyGlobalTrace.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.code.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.code.V293OSSchedDispatch.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.framework.proof.join_prop.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Require Import Coq.Relations.Relation_Operators.
Import ListNotations.
Local Open Scope nat_scope.

Definition RPassign := sassign (evar 106%Z)
  (earrayelem (evar 105%Z) (econst32 (Int.repr 6))).
Definition RPcontext := sseq RPassign (sprim (switch 106%Z)).
Definition RPbase : tasks := sig OwnershipReady (curs RPcontext,(kenil,FCouter)).
Definition RPat ct C le M au := V293_local_global_at RPbase GSenvs
  (RSaux OwnershipWaiting) ct C ((CGge,le,M),(fun _=>false),au).
Definition RPsw := set RPbase OwnershipWaiting (curs (sprim (switch 106%Z)),(kenil,FCpending)).
Definition RPafter := set RPsw OwnershipWaiting (SKIP,(kenil,FCpending)).

Lemma RPentry : forall enabled ci ip cst, exists Mbase Mfirst,
  fresh Mbase 98%positive /\
  free Tint32 98%positive (CGmemory OwnershipWaiting true 0 0)=Some Mbase /\
  V293_global_steps (RCprogram,(CGpo,CGempty,ip)) cst
    (RPat OwnershipWaiting (curs (sfexec 113%Z nil nil),(kenil,kstop)) RTle Mbase (enabled,nil,ci))
    (RPafter,(CGge,CGswitch_envs,Mfirst,(fun _=>false),CGswitch_aux enabled ci),OwnershipReady) /\
  (CGge,CGle,Mfirst,(fun _=>false),(false,nil,enabled::ci),
    set (RIabstract OwnershipWaiting) curtid (oscurt OwnershipReady),spec_done None) |=
    SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) OwnershipReady ** CGpost true 0 0 /\
  load Tint8 Mfirst (94%positive,0%Z)=Some (V293_byteval 6).
Proof.
  intros enabled ci ip cst.
  destruct (FCcaller OwnershipWaiting true 0 0 ltac:(lia) ltac:(lia))
    as (Mbase&Back&Fresh&Init&Outside).
  assert (Enter : V293_global_steps (RCprogram,(CGpo,CGempty,ip)) cst
    (RPat OwnershipWaiting (curs (sfexec 113%Z nil nil),(kenil,kstop)) RTle Mbase (enabled,nil,ci))
    (RPat OwnershipWaiting (curs CGcontrol,(kenil,FCouter)) CGle
      (CGmemory OwnershipWaiting true 0 0) (enabled,nil,ci))).
  { unfold RPat. rewrite <- FCenv.
    exact (V293_sched_global_enter RCprogram CGpo CGempty ip RPbase GSenvs
      (RSaux OwnershipWaiting) OwnershipWaiting cst CGge RTle Mbase (fun _=>false)
      (enabled,nil,ci) kstop 113%Z 120%Z 110%Z 111%Z 107%Z 105%Z 103%Z 106%Z 108%Z 109%Z
      98%positive (CGmemory OwnershipWaiting true 0 0) eq_refl Fresh Init I). }
  destruct (CGlocal_ready true enabled ci) as (Mtail&Body&Before&Target&Counter&Cache).
  destruct (V293_ready_switch_step 80%positive 81%positive 82%positive RCprogram CGpo CGempty ip
    RPsw cst FCpending OwnershipWaiting OwnershipReady
    106%Z 93%positive 1%positive CGge CGle CGswitch_envs Mtail (fun _=>false)
    (false,nil,enabled::ci) (CGswitch_aux enabled ci) (RIabstract OwnershipWaiting)
    (spec_done None) (CGpost true 0 0) V293_tcb_type
    (map_get_set _ _ _) (map_get_set _ _ _) (map_get_set _ _ _) eq_refl Target eq_refl Before)
    as (Mfirst&Step&Store&After&Current&Skipped&Other&Frame).
  exists Mbase. exists Mfirst. split;[exact Fresh| ]. split;[exact Back| ]. split.
  - eapply V293_global_trans;[exact Enter| ]. eapply V293_global_trans.
    + exact (V293_local_steps_global RCprogram CGpo CGempty ip _ _ _ _ Body
        113%Z CGbody RTle kstop Tvoid dnil (dcons 120%Z Tint32 dnil)
        RPbase GSenvs (RSaux OwnershipWaiting) OwnershipWaiting cst eq_refl I).
    + unfold V293_global_steps. eapply rt1n_trans with
        (y:=(RPafter,(CGge,CGswitch_envs,Mfirst,(fun _=>false),CGswitch_aux enabled ci),OwnershipReady));
        [exact Step|apply rt1n_refl].
  - split;[exact After| ].
    rewrite (V293_load_block_frame _ Mtail Mfirst 94%positive 0%Z
      ltac:(intro;apply Frame;left;discriminate)). exact Cache.
Qed.

Lemma RPtable_waiting : forall enabled ci M,
  (CGge,CGle,M,(fun _=>false),(false,nil,enabled::ci),
    set (RIabstract OwnershipWaiting) curtid (oscurt OwnershipReady),spec_done None) |=
    SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) OwnershipReady ** CGpost true 0 0 ->
  load (Tptr V293_tcb_type) M (82%positive,24%Z)=Some (Vptr OwnershipWaiting).
Proof.
  intros enabled ci M Held.
  destruct (V293_ready_switch_sound 80%positive 81%positive 82%positive _ _ _ Held)
    as (tasks&lo&hi&entries&Map&Records&Rel&Loads).
  change (get (set (RIabstract OwnershipWaiting) curtid (oscurt OwnershipReady)) abstcblsid=
    Some (abstcblist tasks)) in Map.
  rewrite map_get_set' in Map by discriminate.
  change (Some (abstcblist OwnershipTasks)=Some (abstcblist tasks)) in Map.
  inversion Map;subst tasks.
  destruct Rel as (Lo&Hi&Nonempty&Bitmap&Len&Table).
  destruct (Table OwnershipWaiting (Int.repr 6)
    (wait (os_stat_sem (72%positive,Int.repr 5)) Int.one) (Vptr (120%positive,Int.repr 7)) eq_refl)
    as (p&Bound&Prio&Entry).
  assert (p=6) by (symmetry;apply V293_priority_repr_injective;[lia|exact Bound|exact Prio]). subst p.
  destruct Loads as (Low&High&Group&TableLoads).
  specialize (TableLoads 6 ltac:(lia)). cbn [getmem] in TableLoads.
  rewrite Entry in TableLoads. exact TableLoads.
Qed.

Lemma RPcells : forall enabled ci M,
  (CGge,CGle,M,(fun _=>false),(false,nil,enabled::ci),
    set (RIabstract OwnershipWaiting) curtid (oscurt OwnershipReady),spec_done None) |=
    SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) OwnershipReady ** CGpost true 0 0 ->
  (CGge,CGle,M,(fun _=>false),(false,nil,enabled::ci),
    set (RIabstract OwnershipWaiting) curtid (oscurt OwnershipReady),spec_done None) |=
    V293_owned_record_cell ((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady) **
    (V293_owned_record_cell ((1%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady) **
      (Amapsto (98%positive,0%Z) Tint32 true (Vint32 Int.zero) ** Atrue)).
Proof.
  intros enabled ci M Held.
  assert (Open : (CGge,CGle,M,(fun _=>false),(false,nil,enabled::ci),
    set (RIabstract OwnershipWaiting) curtid (oscurt OwnershipReady),spec_done None) |=
    (V293_shared_flags ** V293_ready_full 80%positive 81%positive 82%positive OwnershipReady) ** CGpost true 0 0).
  { eapply astar_mono;[apply V293_ready_switch_full|intros s H;exact H|exact Held]. }
  unfold V293_ready_full in Open. sep normal in Open. sep destruct Open.
  assert (Named : (CGge,CGle,M,(fun _=>false),(false,nil,enabled::ci),
    set (RIabstract OwnershipWaiting) curtid (oscurt OwnershipReady),spec_done None) |=
    (GV OSTCBCur @ (Tptr x2) |-> (Vptr OwnershipReady)) ** Atrue) by (sep auto).
  apply sat_split in Named. destruct Named as (ma&mb&oa&ob&JM&JO&Cell&Rest).
  destruct (V293_dispatch_named_cell_parts _ _ _ _ _ _ _ _ _ _ Cell) as (bc&GE&HC&HE).
  change (get CGge OSTCBCur=Some (bc,Tptr x2)) in GE.
  change (Some (1%positive,Tptr V293_tcb_type)=Some (bc,Tptr x2)) in GE.
  inversion GE;subst bc x2.
  unfold CGpost,CGframe in Open. cbn [CGextra V293_owned_record_cells] in Open.
  unfold Agvarmapsto in Open. sep normal in Open. sep destruct Open.
  unfold Agvarenv',Aptrmapsto in Open. cbn [addrval_to_addr] in Open.
  assert (Address : (CGge,CGle,M,(fun _=>false),(false,nil,enabled::ci),
    set (RIabstract OwnershipWaiting) curtid (oscurt OwnershipReady),spec_done None) |=
    Agvarenv OSTCBCur (Tptr V293_tcb_type) (x2,0%Z) ** Atrue) by (sep auto).
  apply sat_split in Address. destruct Address as (m1&m2&o1&o2&J1&J2&[b0 [G [E0 Other]]]&Other2).
  change (Some (1%positive,Tptr V293_tcb_type)=Some (b0,Tptr V293_tcb_type)) in G.
  inversion G;subst b0.
  inversion E0;subst x2.
  unfold V293_owned_record_cell in *. sep auto.
Qed.

Lemma RPprepare : forall enabled ci ip cst M,
  (CGge,CGle,M,(fun _=>false),(false,nil,enabled::ci),
    set (RIabstract OwnershipWaiting) curtid (oscurt OwnershipReady),spec_done None) |=
    SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) OwnershipReady ** CGpost true 0 0 ->
  exists Mb,
    V293_global_steps (RCprogram,(CGpo,CGempty,ip)) cst
      (RPafter,(CGge,CGswitch_envs,M,(fun _=>false),CGswitch_aux enabled ci),OwnershipReady)
      (set RPafter OwnershipReady (curs (sprim (switch 106%Z)),(kenil,FCouter)),
        (CGge,CGswitch_envs,Mb,(fun _=>false),CGswitch_aux enabled ci),OwnershipReady) /\
    load (Tptr V293_tcb_type) Mb (93%positive,0%Z)=Some (Vptr OwnershipWaiting) /\
    (CGge,CGle,Mb,(fun _=>false),(false,nil,enabled::ci),
      set (RIabstract OwnershipWaiting) curtid (oscurt OwnershipReady),spec_done None) |=
      V293_owned_record_cell ((1%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady) **
        (Amapsto (98%positive,0%Z) Tint32 true (Vint32 Int.zero) ** Atrue) /\
    (forall b i, b<>93%positive -> get Mb (b,i)=get M (b,i)).
Proof.
  intros enabled ci ip cst M Held.
  pose proof (RPtable_waiting _ _ _ Held) as Read.
  pose proof (RPcells _ _ _ Held) as Owned.
  destruct (V293_owned_record_cell_update _ (Tptr V293_tcb_type) _ (Vptr OwnershipWaiting)
    _ _ _ _ _ _ _ _ eq_refl Owned) as (Mb&Store&Stored).
  assert (EnvLocal : V293_local_steps CGprogram (curs RPcontext,(kenil,kstop))
      ((CGge,emp,M),(fun _=>false),(false,nil,nil))
      (curs (sprim (switch 106%Z)),(kenil,kstop))
      ((CGge,emp,Mb),(fun _=>false),(false,nil,nil))).
  { eapply V293_local_cons.
    - apply ostc_step. eapply stmt_step;[reflexivity|apply sseq_step].
    - eapply V293_local_trans.
      + apply V293_csteps_local. unfold RPassign.
        eapply V293_assign_pointer_execution with (tp:=V293_tcb_type) (tr:=Tptr V293_tcb_type)
          (b:=93%positive) (off:=0%Z) (value:=Vptr OwnershipWaiting).
        * reflexivity.
        * reflexivity.
        * apply eq_vptr. eauto.
        * reflexivity.
        * change (load (Tptr V293_tcb_type) M (82%positive,24%Z)=Some (Vptr OwnershipWaiting)). exact Read.
        * change (0<=0<=4294967295)%Z. lia.
        * exact Store.
      + eapply V293_local_cons.
        * apply ostc_step. eapply stmt_step;[reflexivity|apply sskip_step].
        * apply V293_local_refl. }
  pose proof (V293_local_steps_global RCprogram CGpo CGempty ip _ _ _ _ EnvLocal
    113%Z CGbody RTle kstop Tvoid dnil (dcons 120%Z Tint32 dnil)
    RPafter CGswitch_envs (CGswitch_aux enabled ci) OwnershipReady cst eq_refl I) as Trace.
  assert (TC : set RPafter OwnershipReady (curs RPcontext,(kenil,FCouter))=RPafter).
  { apply TasksMod.get_set_same.
    change (get RPafter OwnershipReady=Some (curs RPcontext,(kenil,FCouter))).
    unfold RPafter,RPsw,RPbase.
    rewrite !map_get_set' by (vm_compute;discriminate). apply map_get_sig. }
  assert (LC : set CGswitch_envs OwnershipReady emp=CGswitch_envs).
  { apply CltEnvMod.get_set_same.
    change (get CGswitch_envs OwnershipReady=Some emp). unfold CGswitch_envs,GSenvs.
    rewrite map_get_set' by (vm_compute;discriminate). apply map_get_sig. }
  assert (AC : set (CGswitch_aux enabled ci) OwnershipReady (false,nil,nil)=CGswitch_aux enabled ci).
  { apply TaskLStMod.get_set_same.
    change (get (CGswitch_aux enabled ci) OwnershipReady=Some (false,nil,nil)).
    unfold CGswitch_aux,RSaux.
    rewrite map_get_set' by (vm_compute;discriminate). reflexivity. }
  change (V293_global_steps (RCprogram,(CGpo,CGempty,ip)) cst
    (set RPafter OwnershipReady (curs RPcontext,(kenil,FCouter)),
      (CGge,set CGswitch_envs OwnershipReady emp,M,(fun _=>false),
        set (CGswitch_aux enabled ci) OwnershipReady (false,nil,nil)),OwnershipReady)
    (set RPafter OwnershipReady (curs (sprim (switch 106%Z)),(kenil,FCouter)),
      (CGge,set CGswitch_envs OwnershipReady emp,Mb,(fun _=>false),
        set (CGswitch_aux enabled ci) OwnershipReady (false,nil,nil)),OwnershipReady)) in Trace.
  rewrite TC,LC,AC in Trace.
  exists Mb. split;[exact Trace| ]. split.
  - eapply V293_store_readback;[reflexivity|exact Store].
  - split;[sep auto| ]. intros b i Outside.
    eapply V293_storebytes_outside;[exact Store|left;exact Outside].
Qed.

Definition RPback := set RPafter OwnershipReady (curs (sprim (switch 106%Z)),(kenil,FCouter)).
Definition RPdone := set (set RPback OwnershipReady (SKIP,(kenil,FCouter)))
  OwnershipWaiting (SKIP,(kenil,kstop)).

(* Same physical heaps at every join: actual sfexec -> first switch ->
   explicit environment table read/target assignment -> switch back -> return.
   Waiting is still abstractly blocked: this is NOT scheduler selection. *)
Theorem RProundtrip : forall enabled ci ip cst, exists Mbase Mfirst Mb Ms Mf,
  fresh Mbase 98%positive /\
  free Tint32 98%positive (CGmemory OwnershipWaiting true 0 0)=Some Mbase /\
  V293_global_steps (RCprogram,(CGpo,CGempty,ip)) cst
    (RPat OwnershipWaiting (curs (sfexec 113%Z nil nil),(kenil,kstop)) RTle Mbase (enabled,nil,ci))
    (RPafter,(CGge,CGswitch_envs,Mfirst,(fun _=>false),CGswitch_aux enabled ci),OwnershipReady) /\
  V293_global_steps (RCprogram,(CGpo,CGempty,ip)) cst
    (RPafter,(CGge,CGswitch_envs,Mfirst,(fun _=>false),CGswitch_aux enabled ci),OwnershipReady)
    (RPback,(CGge,CGswitch_envs,Mb,(fun _=>false),CGswitch_aux enabled ci),OwnershipReady) /\
  V293_global_steps (RCprogram,(CGpo,CGempty,ip)) cst
    (RPat OwnershipWaiting (curs (sfexec 113%Z nil nil),(kenil,kstop)) RTle Mbase (enabled,nil,ci))
    (RPdone,(CGge,set CGswitch_envs OwnershipWaiting RTle,Mf,(fun _=>false),
      set (CGswitch_aux enabled ci) OwnershipWaiting (enabled,nil,ci)),OwnershipWaiting) /\
  store (Tptr V293_tcb_type) Mb (1%positive,0%Z) (Vptr OwnershipWaiting)=Some Ms /\
  free Tint32 98%positive Ms=Some Mf /\
  (forall i, (0<=i<4)%Z -> get Mf (98%positive,i)=None) /\
  load (Tptr V293_tcb_type) Mf (1%positive,0%Z)=Some (Vptr OwnershipWaiting) /\
  load Tint8 Mf (94%positive,0%Z)=Some (V293_byteval 6) /\
  (forall b i, b<>93%positive -> b<>1%positive -> b<>98%positive -> get Mf (b,i)=get Mfirst (b,i)) /\
  get (set CGswitch_envs OwnershipWaiting RTle) OwnershipReady=Some emp /\
  get (set (CGswitch_aux enabled ci) OwnershipWaiting (enabled,nil,ci)) OwnershipReady=Some (false,nil,nil).
Proof.
  intros enabled ci ip cst.
  destruct (RPentry enabled ci ip cst) as (Mbase&Mfirst&Fresh&Back&Prefix&After&Cache).
  destruct (RPprepare enabled ci ip cst Mfirst After) as (Mb&Prepare&Target&Owned&TargetFrame).
  assert (RunLocal : get CGswitch_envs OwnershipReady=Some emp).
  { unfold CGswitch_envs,GSenvs. rewrite map_get_set' by (vm_compute;discriminate). apply map_get_sig. }
  assert (RunAux : get (CGswitch_aux enabled ci) OwnershipReady=Some (false,nil,nil)).
  { unfold CGswitch_aux,RSaux. rewrite map_get_set' by (vm_compute;discriminate). reflexivity. }
  assert (Suspended : get RPback OwnershipWaiting=Some (SKIP,(kenil,FCpending))).
  { unfold RPback,RPafter. rewrite map_get_set' by (vm_compute;discriminate). apply map_get_set. }
  assert (Local : get CGswitch_envs OwnershipWaiting=Some (V293_cpu_lenv 120%Z 98%positive)).
  { rewrite FCenv. apply map_get_set. }
  assert (Held : (CGge,V293_cpu_lenv 120%Z 98%positive,Mb,(fun _=>false),
    (false,nil,enabled::ci),set (RIabstract OwnershipWaiting) curtid (oscurt OwnershipReady),spec_done None) |=
    V293_owned_record_cell ((1%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady) **
      (Amapsto (98%positive,0%Z) Tint32 true (Vint32 Int.zero) ** Atrue)).
  { rewrite FCenv. exact Owned. }
  destruct (V293_sched_switch_resume_return RCprogram CGpo CGempty ip RPback CGswitch_envs
    (CGswitch_aux enabled ci) OwnershipReady OwnershipWaiting cst CGge Mb (fun _=>false)
    emp (false,nil,nil) FCouter 106%Z 93%positive 1%positive V293_tcb_type
    false enabled nil ci (set (RIabstract OwnershipWaiting) curtid (oscurt OwnershipReady))
    (spec_done None) Atrue 113%Z CGbody RTle kstop Tvoid dnil (dcons 120%Z Tint32 dnil)
    120%Z 98%positive (Vint32 Int.zero) ltac:(vm_compute;discriminate) eq_refl I
    (map_get_set _ _ _) RunLocal RunAux Suspended Local (map_get_set _ _ _) eq_refl Target eq_refl Held)
    as (Ms&Mf&Step&Resume&Store&Free&Rest&Removed&Frame).
  assert (Whole : V293_global_steps (RCprogram,(CGpo,CGempty,ip)) cst
    (RPat OwnershipWaiting (curs (sfexec 113%Z nil nil),(kenil,kstop)) RTle Mbase (enabled,nil,ci))
    (RPdone,(CGge,set CGswitch_envs OwnershipWaiting RTle,Mf,(fun _=>false),
      set (CGswitch_aux enabled ci) OwnershipWaiting (enabled,nil,ci)),OwnershipWaiting)).
  { eapply V293_global_trans;[exact Prefix| ]. eapply V293_global_trans;[exact Prepare|exact Resume]. }
  exists Mbase. exists Mfirst. exists Mb. exists Ms. exists Mf.
  split;[exact Fresh| ]. split;[exact Back| ]. split;[exact Prefix| ]. split;[exact Prepare| ].
  split;[exact Whole| ]. split;[exact Store| ]. split;[exact Free| ]. split;[exact Removed| ]. split.
  - change (load (Tptr V293_tcb_type)
      (getmem (CGge,RTle,Mf,(fun _=>false),(enabled,nil,ci),
        set (RIabstract OwnershipWaiting) curtid (oscurt OwnershipReady),spec_done None))
      (1%positive,0%Z)=Some (Vptr OwnershipWaiting)).
    eapply V293_record_star_load_l;[apply V293_owned_record_cell_load|exact Rest].
  - assert (Outside : forall b i, b<>93%positive -> b<>1%positive -> b<>98%positive ->
      get Mf (b,i)=get Mfirst (b,i)).
    { intros b i N93 N1 N98. rewrite Frame by assumption. apply TargetFrame;exact N93. }
    split.
    + rewrite (V293_load_block_frame _ Mfirst Mf 94%positive 0%Z
        ltac:(intro;apply Outside;discriminate)). exact Cache.
    + split;[exact Outside| ]. split;rewrite map_get_set' by (vm_compute;discriminate);assumption.
Qed.
