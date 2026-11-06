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
(* Function 112 is explicitly a FRAGMENT fixture, not full OS_Sched.
   Its body is the exact source fragment; no fabricated interrupt context. *)
Definition GSpo : progunit := fun f =>
  if Z.eq_dec f 112%Z then Some (Tvoid,dnil,dnil,STbody) else RCprogram f.
Definition GSempty : progunit := fun _ => None.
Definition GSprogram := pumerge GSpo GSempty.
Definition GSouter := kcall 112%Z STbody RTle kstop.
Definition GSbase : tasks := sig OwnershipReady (SKIP,(kenil,kstop)).
Definition GSenvs : cltenvs := sig OwnershipReady emp.
Definition GScurrent (different:bool) := if different then OwnershipWaiting else OwnershipReady.
Definition GSat different C M := V293_global_at GSbase GSenvs (GScurrent different)
  (fun _=>false) (RSaux (GScurrent different)) C (STge,RTle,M).

Theorem GSsource_tail : forall ct different ks, exists Mtarget Mtail,
  cstepstar GSprogram (curs STbody,(kenil,ks)) (STge,RTle,STmemory ct different)
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
  destruct (V293_ready_source_dispatch 80%positive 81%positive 82%positive GSprogram ks STge RTle
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


Theorem GSglobal_source : forall different ip cst, exists Mtail,
  V293_global_steps (RCprogram,(GSpo,GSempty,ip)) cst
    (GSat different (curs STbody,(kenil,GSouter)) (STmemory (GScurrent different) different))
    (GSat different ((if different then curs (sprim (switch 106%Z)) else SKIP),(kenil,GSouter)) Mtail) /\
  STstate (GScurrent different) Mtail |=
    SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) (GScurrent different) ** STpostframe different /\
  load (Tptr V293_tcb_type) Mtail (93%positive,0%Z)=Some (Vptr OwnershipReady) /\
  load Tint32 Mtail (95%positive,0%Z)=Some (Vint32 (if different then Int.zero else Int.mone)) /\
  load Tint8 Mtail (94%positive,0%Z)=Some (V293_byteval (STcache different)).
Proof.
  intros different ip cst.
  destruct (GSsource_tail (GScurrent different) different kstop)
    as (Mtarget & Mtail & Exec & Store & Before & Target & Counter & Cache & Outside).
  exists Mtail. split.
  - exact (V293_csteps_global RCprogram GSpo GSempty ip _ _ _ _ Exec
      112%Z STbody RTle kstop Tvoid dnil dnil GSbase GSenvs (GScurrent different)
      (fun _=>false) (RSaux (GScurrent different)) (false,nil,nil) cst
      eq_refl (map_get_set _ _ _) I).
  - split; [exact Before | ]. split; [exact Target | ]. split;assumption.
Qed.

Theorem GSglobal_switch : forall ip cst, exists Mf,
  V293_global_steps (RCprogram,(GSpo,GSempty,ip)) cst
    (GSat true (curs STbody,(kenil,GSouter)) (STmemory OwnershipWaiting true))
    (set (RStasks OwnershipWaiting GSouter) OwnershipWaiting (SKIP,(kenil,GSouter)),
      (STge,RSles OwnershipWaiting,Mf,(fun _=>false),RSaux OwnershipWaiting),OwnershipReady) /\
  (STge,RTle,Mf,(fun _=>false),(false,nil,nil),
    set (RIabstract OwnershipWaiting) curtid (oscurt OwnershipReady),spec_done None) |=
    SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) OwnershipReady ** STpostframe true /\
  load (Tptr V293_tcb_type) Mf (1%positive,0%Z)=Some (Vptr OwnershipReady) /\
  load Tint32 Mf (95%positive,0%Z)=Some (Vint32 Int.zero) /\
  load Tint8 Mf (94%positive,0%Z)=Some (V293_byteval 6) /\
  ~ V293_current_task OwnershipTasks OwnershipReady 6 /\
  (forall other, other<>OwnershipWaiting ->
    get (set (RStasks OwnershipWaiting GSouter) OwnershipWaiting (SKIP,(kenil,GSouter))) other=
      get (RStasks OwnershipWaiting GSouter) other).
Proof.
  intros ip cst.
  destruct (GSglobal_source true ip cst) as (Mtail & Trace & Before & Target & Counter & Cache).
  destruct (V293_ready_switch_step 80%positive 81%positive 82%positive RCprogram GSpo GSempty ip
    (RStasks OwnershipWaiting GSouter) cst GSouter OwnershipWaiting OwnershipReady 106%Z 93%positive 1%positive
    STge RTle (RSles OwnershipWaiting) Mtail (fun _=>false) (false,nil,nil) (RSaux OwnershipWaiting)
    (RIabstract OwnershipWaiting) (spec_done None) (STpostframe true) V293_tcb_type
    (map_get_set _ _ _) (map_get_set _ _ _) (map_get_set _ _ _) eq_refl Target eq_refl Before)
    as (Mf & Step & Store & After & Current & Skipped & Other & Outside).
  exists Mf. split.
  - apply clos_rt_rt1n. eapply Relation_Operators.rt_trans.
    + apply clos_rt1n_rt. exact Trace.
    + apply Relation_Operators.rt_step. exact Step.
  - split; [exact After | ]. split; [exact Current | ].
    assert (CounterFinal : load Tint32 Mf (95%positive,0%Z)=Some (Vint32 Int.zero)).
    { change (load Tint32 (getmem (STge,RTle,Mf,(fun _=>false),(false,nil,nil),
        set (RIabstract OwnershipWaiting) curtid (oscurt OwnershipReady),spec_done None))
        (95%positive,0%Z)=Some (Vint32 Int.zero)).
      eapply V293_record_star_load_r; [ | exact After].
      unfold STpostframe. do 2 eapply V293_record_star_load_r.
      eapply V293_record_star_load_l. apply V293_owned_record_cell_load. }
    split; [exact CounterFinal | ].
    assert (CacheFinal : load Tint8 Mf (94%positive,0%Z)=Some (V293_byteval 6)).
    { change (load Tint8 (getmem (STge,RTle,Mf,(fun _=>false),(false,nil,nil),
        set (RIabstract OwnershipWaiting) curtid (oscurt OwnershipReady),spec_done None))
        (94%positive,0%Z)=Some (V293_byteval 6)).
      eapply V293_record_star_load_r; [ | exact After]. unfold STpostframe.
      eapply V293_record_star_load_r. eapply V293_record_star_load_l.
      apply V293_owned_record_cell_load. }
    split; [exact CacheFinal | ]. split.
    + intros [Range [status [message Task]]].
      change (Some (Int.repr 4,rdy,Vnull)=Some (Int.repr 6,status,message)) in Task.
      vm_compute in Task. discriminate.
    + exact Other.
Qed.

Theorem GSglobal_no_switch : forall ip cst, exists M,
  V293_global_steps (RCprogram,(GSpo,GSempty,ip)) cst
    (GSat false (curs STbody,(kenil,GSouter)) (STmemory OwnershipReady false))
    (GSat false (SKIP,(kenil,GSouter)) M) /\
  STstate OwnershipReady M |=
    SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) OwnershipReady ** STpostframe false /\
  load Tint32 M (95%positive,0%Z)=Some (Vint32 Int.mone) /\
  load Tint8 M (94%positive,0%Z)=Some (V293_byteval 4) /\
  V293_current_task OwnershipTasks OwnershipReady 4.
Proof.
  intros ip cst. destruct (GSglobal_source false ip cst)
    as (M & Trace & After & Target & Counter & Cache).
  exists M. split; [exact Trace | ]. split; [exact After | ].
  split; [exact Counter | ]. split; [exact Cache | exact (STcoherent_current false)].
Qed.

(* One-factor ablation: remove ONLY the enclosing 112 binding. The same
   body, memory, code and continuation remain; source execution still exists,
   but the initial InOS classification fails. This is not a stuckness claim. *)
Theorem GSbinding_only_control :
  (forall f, f<>112%Z -> GSpo f=RCprogram f) /\
  GSpo 112%Z=Some (Tvoid,dnil,dnil,STbody) /\ RCprogram 112%Z=None /\
  InOS (curs STbody,(kenil,GSouter)) GSprogram /\
  ~ InOS (curs STbody,(kenil,GSouter)) (pumerge RCprogram GSempty) /\
  (forall ct different, exists Mtail,
    cstepstar RCprogram (curs STbody,(kenil,GSouter)) (STge,RTle,STmemory ct different)
      ((if different then curs (sprim (switch 106%Z)) else SKIP),(kenil,GSouter)) (STge,RTle,Mtail)).
Proof.
  split.
  - intros f Ne. unfold GSpo. destruct (Z.eq_dec f 112%Z);congruence.
  - split; [reflexivity | ]. split; [reflexivity | ]. split.
    + exact (V293_enclosing_inos RCprogram GSpo GSempty (fun _=>None)
        112%Z STbody RTle kstop Tvoid dnil dnil (curs STbody,(kenil,kstop)) eq_refl I).
    + split.
      * intros (c & ke & ks & Eq & Cases). inversion Eq;subst c ke ks.
        destruct Cases as [(f & vl & fc & tl & Wrong & Bound) | [(f & le & ks & ty & da & db & body & body' & Call & Bound) | Interrupt]].
        -- discriminate Wrong.
        -- cbn [callcont GSouter] in Call. inversion Call;subst.
           vm_compute in Bound. discriminate.
        -- apply Interrupt. reflexivity.
      * intros ct different. destruct (STjoint_source_tail ct different GSouter)
          as (Mtarget & Mtail & Exec & Rest).
        exists Mtail. exact Exec.
Qed.
