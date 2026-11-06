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
Import ListNotations.
Local Open Scope nat_scope.
Definition STge : env := set (set RSge 108%Z (94%positive,Tint8)) 109%Z (95%positive,Tint32).
Definition STcache (different : bool) := if different then 6 else 4.
Definition STcells different : list V293_record_cell :=
  [((90%positive,0%Z),Tint8,V293_byteval 99);
   ((91%positive,0%Z),Tint8,V293_byteval 88);
   ((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipWaiting);
   ((94%positive,0%Z),Tint8,V293_byteval (STcache different));
   ((95%positive,0%Z),Tint32,Vint32 Int.mone)].
Definition SToutputs different := OwnershipCellsMemory (STcells different).
Definition STwith ct different := merge (RTfull ct) (SToutputs different).
Definition STmemory ct different := merge (STwith ct different) RTdecoder.
Definition STstate ct M := V293_target_wstate STge RTle M (RIabstract ct).
Definition STbody := sseq (V293_OSSched_unlocked_prefix 107%Z 105%Z 103%Z 106%Z)
  (V293_OSSched_change 103%Z 108%Z 109%Z (sprim (switch 106%Z))).

Lemma SToutputs_join : forall ct different,
  join (RTfull ct) (SToutputs different) (STwith ct different).
Proof.
  intros ct different. apply map_join_merge;apply map_disjoint;intros [b i].
  destruct (Pos.eq_dec b 90%positive) as [E|N90]; [subst b;left;apply RToutside;discriminate | ].
  destruct (Pos.eq_dec b 91%positive) as [E|N91]; [subst b;left;apply RToutside;discriminate | ].
  destruct (Pos.eq_dec b 93%positive) as [E|N93]; [subst b;left;apply RToutside;discriminate | ].
  destruct (Pos.eq_dec b 94%positive) as [E|N94]; [subst b;left;apply RToutside;discriminate | ].
  destruct (Pos.eq_dec b 95%positive) as [E|N95]; [subst b;left;apply RToutside;discriminate | ].
  right;left. unfold SToutputs. apply OwnershipCellsOutside.
  intro H;destruct different;vm_compute in H;intuition congruence.
Qed.
Lemma STdecoder_join : forall ct different,
  join (STwith ct different) RTdecoder (STmemory ct different).
Proof.
  intros ct different. apply map_join_merge;apply map_disjoint;intros [b i].
  destruct (Pos.eq_dec b 92%positive) as [E|N92].
  - subst b. left. unfold STwith;rewrite map_merge_semp by reflexivity.
    rewrite RToutside by discriminate. unfold SToutputs.
    rewrite OwnershipCellsOutside by (intro H;destruct different;vm_compute in H;intuition congruence).
    reflexivity.
  - right;left. apply V293_encoded_memory_outside. left;exact N92.
Qed.
Lemma STentry : forall ct different, STstate ct (STmemory ct different) |=
  SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) ct **
    (V293_owned_record_cell ((91%positive,0%Z),Tint8,V293_byteval 88) **
     (V293_owned_record_cell ((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipWaiting) **
      (V293_owned_record_cell ((94%positive,0%Z),Tint8,V293_byteval (STcache different)) **
       (V293_owned_record_cell ((95%positive,0%Z),Tint32,Vint32 Int.mone) ** RCframe)))).
Proof.
  intros ct different.
  assert (Outputs : V293_target_wstate STge RTle (SToutputs different) emp |=
    V293_owned_record_cells (STcells different)).
  { apply OwnershipCellsSpatial.
    - destruct different;vm_compute;repeat split;intros;intuition congruence.
    - destruct different;repeat constructor;vm_compute;reflexivity. }
  assert (Core : V293_target_wstate STge RTle (STwith ct different) (RIabstract ct) |=
    SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) ct **
    V293_owned_record_cells (STcells different)).
  { eapply V293_target_wstate_star with (m1:=RTfull ct) (m2:=SToutputs different)
      (o1:=RIabstract ct) (o2:=emp).
    - apply SToutputs_join.
    - apply map_join_emp.
    - apply RSenv_spatial with (tp:=V293_tcb_type). vm_compute;reflexivity.
    - exact Outputs. }
  assert (Both : STstate ct (STmemory ct different) |=
    (SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) ct **
      V293_owned_record_cells (STcells different)) ** V293_read_bytes 92%positive 0%Z V293_ready_table).
  { eapply V293_target_wstate_star with (m1:=STwith ct different) (m2:=RTdecoder)
      (o1:=RIabstract ct) (o2:=emp).
    - apply STdecoder_join.
    - apply map_join_emp.
    - exact Core.
    - apply V293_read_bytes_witness. }
  cbn [STcells V293_owned_record_cells] in Both. unfold RCframe. clear Core Outputs. sep auto.
Qed.
Lemma STlookup : forall ct different n, n<256 ->
  load Tint8 (STmemory ct different) (92%positive,Z.of_nat n)=Some (V293_byteval (V293_ready_lookup n)).
Proof.
  intros ct different n Bound. eapply load_mem_mono with (M:=RTdecoder).
  - assert (RowBound : nth n V293_ready_table 0<256).
    { change (V293_ready_lookup n<256). pose proof (proj1 (V293_ready_row_spec n Bound)). lia. }
    replace (Z.of_nat n) with (0+Z.of_nat n)%Z by lia.
    apply (V293_read_bytes_load V293_ready_table 92%positive 0%Z n Bound RowBound
      (V293_wstate emp emp RTdecoder)). apply V293_read_bytes_witness.
  - exists (STwith ct different). apply map_join_comm;apply STdecoder_join.
Qed.

(* Exact source branch on both byte values, including UINT32_MAX -> zero.
   Current, TCB records, ready bytes and the initial target are otherwise the
   same for the two branches. No cache/task coherence is assumed here. *)
Theorem STjoint_source_tail : forall ct different ks, exists Mtarget Mtail,
  cstepstar RCprogram (curs STbody,(kenil,ks)) (STge,RTle,STmemory ct different)
    ((if different then curs (sprim (switch 106%Z)) else SKIP),(kenil,ks)) (STge,RTle,Mtail) /\
  (if different then store Tint32 Mtarget (95%positive,0%Z) (Vint32 Int.zero)=Some Mtail else Mtail=Mtarget) /\
  STstate ct Mtail |= SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) ct **
    (V293_owned_record_cell ((91%positive,0%Z),Tint8,V293_byteval 4) **
     (V293_owned_record_cell ((94%positive,0%Z),Tint8,V293_byteval (STcache different)) **
      (V293_owned_record_cell ((95%positive,0%Z),Tint32,Vint32 (if different then Int.zero else Int.mone)) **
       (V293_owned_record_cell ((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady) ** RCframe)))) /\
  load (Tptr V293_tcb_type) Mtail (93%positive,0%Z)=Some (Vptr OwnershipReady) /\
  load Tint32 Mtail (95%positive,0%Z)=Some (Vint32 (if different then Int.zero else Int.mone)) /\
  load Tint8 Mtail (94%positive,0%Z)=Some (V293_byteval (STcache different)) /\
  (forall b i, b<>95%positive \/ (i<0)%Z \/ (4<=i)%Z -> get Mtail (b,i)=get Mtarget (b,i)).
Proof.
  intros ct different ks.
  destruct (V293_ready_source_dispatch 80%positive 81%positive 82%positive RCprogram ks STge RTle
    (STmemory ct different) (fun _=>false) (false,nil,nil) (RIabstract ct) (spec_done None) ct RCframe
    107%Z 100%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 108%Z 109%Z
    92%positive 91%positive 93%positive 94%positive 95%positive (STcache different) Int.mone
    (V293_byteval 88) (Vptr OwnershipWaiting)
    ltac:(vm_compute;reflexivity)
    ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
    ltac:(discriminate) ltac:(discriminate)
    eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
    eq_refl eq_refl eq_refl eq_refl ltac:(destruct different;cbn [STcache];lia)
    RCframe_good (STlookup ct different) (STentry ct different))
    as (tasks & lo & hi & entries & next & message & Mtarget & Mtail & Map & Rel & Task & Exec & Store & After & Target & Counter & Cache & Outside).
  pose proof (RIfixed_tasks ct). assert (tasks=OwnershipTasks) by congruence. subst tasks.
  assert (Range : V293_ready_select lo hi (V293_ready_group lo hi)<13).
  { destruct Rel as [Lo [Hi [Nonempty [Bitmap Table]]]].
    apply V293_ready_selection_range;assumption || reflexivity. }
  destruct (RTonly_ready _ _ _ Range Task) as (Selected & Next & Message). subst next message.
  rewrite Selected in Exec,Store,After,Counter.
  assert (Wrap : Int.add Int.mone Int.one=Int.zero) by (vm_compute;apply Int.mkint_eq;reflexivity).
  rewrite Wrap in Store,After,Counter.
  exists Mtarget. exists Mtail. destruct different;cbn [STcache] in *;
    repeat first [assumption | split].
Qed.

(* Prospective single-factor guard control: exactly one cache byte changes.
   This control need not preserve cache/task coherence; that is checked
   separately rather than smuggled into the invariant. *)
Theorem STcache_only_control : forall ct a, a<>(94%positive,0%Z) ->
  get (STmemory ct true) a=get (STmemory ct false) a.
Proof.
  intros ct [b i] Apart.
  assert (Outside : b<>94%positive \/ (i<0)%Z \/ (1<=i)%Z).
  { destruct (Pos.eq_dec b 94%positive) as [E|N]; [subst b;right | left;exact N].
    assert (i<>0%Z) by (intro E;apply Apart;congruence). lia. }
  assert (Leaf : get (OwnershipCellMemory ((94%positive,0%Z),Tint8,V293_byteval 6)) (b,i)=
    get (OwnershipCellMemory ((94%positive,0%Z),Tint8,V293_byteval 4)) (b,i)).
  { unfold OwnershipCellMemory.
    rewrite !V293_encoded_memory_outside; [reflexivity | exact Outside | exact Outside]. }
  unfold STmemory,STwith,SToutputs,STcells.
  cbn [OwnershipCellsMemory STcache]. rewrite !map_merge_semp by reflexivity.
  rewrite Leaf. reflexivity.
Qed.
Theorem STcoherent_current : forall (different : bool),
  V293_current_task OwnershipTasks (if different then OwnershipWaiting else OwnershipReady) (STcache different).
Proof.
  destruct different;split; [cbn [STcache];lia | | cbn [STcache];lia | ].
  - exists (wait (os_stat_sem (72%positive,Int.repr 5)) Int.one).
    exists (Vptr (120%positive,Int.repr 7)). vm_compute;reflexivity.
  - exists rdy. exists Vnull. vm_compute;reflexivity.
Qed.

Definition STpostframe different : asrt :=
  V293_owned_record_cell ((91%positive,0%Z),Tint8,V293_byteval 4) **
   (V293_owned_record_cell ((94%positive,0%Z),Tint8,V293_byteval (STcache different)) **
    (V293_owned_record_cell ((95%positive,0%Z),Tint32,Vint32 (if different then Int.zero else Int.mone)) **
     (V293_owned_record_cell ((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady) ** RCframe))).

(* Same endpoint CODE and MEMORY feed the real switch. There is no premise
   allowing an unrelated switch code to be supplied after a SKIP endpoint.
   This is still a cstepstar + lpstep mixed trace, not a global lpstep closure. *)
Theorem STjoint_source_switch : forall ks po pi ip cst, exists Mtail Mf,
  cstepstar RCprogram (curs STbody,(kenil,ks)) (STge,RTle,STmemory OwnershipWaiting true)
    (curs (sprim (switch 106%Z)),(kenil,ks)) (STge,RTle,Mtail) /\
  lpstep (RCprogram,(po,pi,ip)) (RStasks OwnershipWaiting ks) cst
    (STge,RSles OwnershipWaiting,Mtail,(fun _=>false),RSaux OwnershipWaiting) OwnershipWaiting
    (set (RStasks OwnershipWaiting ks) OwnershipWaiting (SKIP,(kenil,ks))) cst
    (STge,RSles OwnershipWaiting,Mf,(fun _=>false),RSaux OwnershipWaiting) OwnershipReady /\
  (STge,RTle,Mf,(fun _=>false),(false,nil,nil),set (RIabstract OwnershipWaiting) curtid (oscurt OwnershipReady),spec_done None) |=
    SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) OwnershipReady ** STpostframe true /\
  load (Tptr V293_tcb_type) Mf (1%positive,0%Z)=Some (Vptr OwnershipReady) /\
  load Tint32 Mf (95%positive,0%Z)=Some (Vint32 Int.zero) /\
  load Tint8 Mf (94%positive,0%Z)=Some (V293_byteval 6) /\
  load Tint8 Mf (94%positive,0%Z)<>Some (V293_byteval 4) /\
  V293_current_task OwnershipTasks OwnershipWaiting 6 /\
  ~ V293_current_task OwnershipTasks OwnershipReady 6 /\
  (forall b i, b<>1%positive \/ (i<0)%Z \/ (4<=i)%Z -> get Mf (b,i)=get Mtail (b,i)).
Proof.
  intros ks po pi ip cst.
  destruct (STjoint_source_tail OwnershipWaiting true ks)
    as (Mtarget & Mtail & Exec & Store & Before & Target & Counter & Cache & OutsideCounter).
  change (STstate OwnershipWaiting Mtail |=
    SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) OwnershipWaiting ** STpostframe true) in Before.
  destruct (V293_ready_switch_step 80%positive 81%positive 82%positive RCprogram po pi ip
    (RStasks OwnershipWaiting ks) cst ks OwnershipWaiting OwnershipReady 106%Z 93%positive 1%positive
    STge RTle (RSles OwnershipWaiting) Mtail (fun _=>false) (false,nil,nil) (RSaux OwnershipWaiting)
    (RIabstract OwnershipWaiting) (spec_done None) (STpostframe true) V293_tcb_type
    (map_get_set _ _ _) (map_get_set _ _ _) (map_get_set _ _ _) eq_refl Target eq_refl Before)
    as (Mf & Step & CurrentStore & After & CurrentLoad & SkippedCode & Other & OutsideCurrent).
  assert (CounterFinal : load Tint32 Mf (95%positive,0%Z)=Some (Vint32 Int.zero)).
  { change (load Tint32 (getmem (STge,RTle,Mf,(fun _=>false),(false,nil,nil),
      set (RIabstract OwnershipWaiting) curtid (oscurt OwnershipReady),spec_done None)) (95%positive,0%Z)=Some (Vint32 Int.zero)).
    eapply V293_record_star_load_r; [ | exact After].
    unfold STpostframe. do 2 eapply V293_record_star_load_r.
    eapply V293_record_star_load_l. apply V293_owned_record_cell_load. }
  assert (CacheFinal : load Tint8 Mf (94%positive,0%Z)=Some (V293_byteval 6)).
  { change (load Tint8 (getmem (STge,RTle,Mf,(fun _=>false),(false,nil,nil),
      set (RIabstract OwnershipWaiting) curtid (oscurt OwnershipReady),spec_done None)) (94%positive,0%Z)=Some (V293_byteval 6)).
    eapply V293_record_star_load_r; [ | exact After].
    unfold STpostframe. eapply V293_record_star_load_r.
    eapply V293_record_star_load_l. apply V293_owned_record_cell_load. }
  assert (NotNext : ~ V293_current_task OwnershipTasks OwnershipReady 6).
  { intros [Range [status [message Task]]].
    change (Some (Int.repr 4,rdy,Vnull)=Some (Int.repr 6,status,message)) in Task.
    vm_compute in Task. discriminate. }
  exists Mtail. exists Mf.
  split; [exact Exec | ]. split; [exact Step | ]. split; [exact After | ].
  split; [exact CurrentLoad | ]. split; [exact CounterFinal | ]. split; [exact CacheFinal | ].
  split; [rewrite CacheFinal;vm_compute;discriminate | ].
  split; [exact (STcoherent_current true) | ]. split;assumption.
Qed.

Theorem STjoint_no_switch : forall ks, exists M,
  cstepstar RCprogram (curs STbody,(kenil,ks)) (STge,RTle,STmemory OwnershipReady false)
    (SKIP,(kenil,ks)) (STge,RTle,M) /\
  STstate OwnershipReady M |= SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) OwnershipReady ** STpostframe false /\
  load Tint32 M (95%positive,0%Z)=Some (Vint32 Int.mone) /\
  load Tint8 M (94%positive,0%Z)=Some (V293_byteval 4) /\
  V293_current_task OwnershipTasks OwnershipReady 4.
Proof.
  intros ks. destruct (STjoint_source_tail OwnershipReady false ks)
    as (Mtarget & M & Exec & Store & After & Target & Counter & Cache & Outside).
  exists M. split; [exact Exec | ]. split; [exact After | ].
  split; [exact Counter | ]. split; [exact Cache | exact (STcoherent_current false)].
Qed.
