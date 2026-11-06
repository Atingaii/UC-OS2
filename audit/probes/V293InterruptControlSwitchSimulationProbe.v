(* The existing normalized BXglobal true, with nonempty tasks and saved interrupt context. *)
(* Existing interrupt continuation in actual global maps; no port body. *)
(* Independent waiting-current resources and exact OSIntCtxSw call boundary. *)
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

Require Import CertiOS.certiucos.v293.proofs.V293ReadyTargetHandoff.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchState.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.audit.probes.V293ReadyTaskInvariantProbe.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.certiucos.v293.code.V293OSSchedDispatch.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Local Open Scope nat_scope.
Require Import CertiOS.audit.probes.V293ReadyTargetHandoffProbe.
Require Import CertiOS.certiucos.v293.proofs.V293ReadySchedCall.

Require Import CertiOS.audit.probes.V293ReadySchedCallProbe.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitDispatchExecution.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitExecution.
Require Import CertiOS.certiucos.v293.code.V293OSIntExit.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.code.V293OSSchedGuards.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Local Open Scope nat_scope.

Require Import CertiOS.audit.probes.V293OSIntExitDispatchExecutionProbe.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitDispatchCall.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitCallExecution.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCriticalGlobal.

Require Import CertiOS.audit.probes.V293OSIntExitDispatchCallProbe.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitSwitchEntry.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyFullCall.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPointerCompare.
Import ListNotations.
Require Import CertiOS.audit.probes.V293OSIntExitSwitchEntryProbe.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitInterruptGlobal.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyGlobalTrace.
Require Import CertiOS.certiucos.v293.proofs.V293LocalGlobalTrace.
Require Import CertiOS.tactics.basetac.join_lib.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import CertiOS.audit.probes.V293OSIntExitInterruptGlobalProbe.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBoundarySwitch.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCacheContract.

(* Same physical heap; align current/target pointee types for ORIGINAL pswitch. *)
Require Import CertiOS.audit.probes.V293OSIntExitBoundarySwitchProbe.
Require Import CertiOS.audit.probes.V293InterruptControlSchedulerProbe.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptControlSwitchSimulation.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptControlScheduler.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptFixedControlSpec.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptControlRetention.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptQuietBuilder.
Require Import CertiOS.certiucos.v293.proofs.V293SwitchProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCallGlobal.

Definition SMK:=snd(snd(BXend true)).
Definition SMT:tasks:=set(GXtasks CSready)SXct(curs(sprim(switch 106%Z)),(kenil,SMK)).
Definition SMTf:tasks:=set SMT SXct(BXend true).
Definition SML bs:=set(GXenvs SXcaller)SXct(V293_cpu_lenv 601%Z bs).
Definition SMA enabled ci:=set(GXaux enabled ci((true,nil,nil):localst))SXct(false,nil,enabled::ci).
Definition SMS bs M enabled ci:osstate:=(BXge,SML bs,M,(fun _=>false),SMA enabled ci).
Definition SMPh:hprog:=(GXempty,((fun _=>None),(fun _=>None),V293_scheduler)).
Definition SMrest bs:=
 V293_owned_record_cell((96%positive,0%Z),Tint8,V293_byteval 4) **
 (V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval 4) **
 (V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady) **
 (V293_owned_record_cell((97%positive,0%Z),Tint32,Vint32(Int.repr 20)) **
 (Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **SXframe)))).
Definition SMowned bs:=SWINVt(V293_ready_inv 80%positive 81%positive 82%positive)SXct **
 (V293_irq_controls 98%positive 94%positive 95%positive 1 0 0 **SMrest bs).
Definition SMsource cst enabled ci bs Ms:=
 V293_global_steps(BXglobal true)cst
 (GXtasks CSready,(BXge,GXenvs SXcaller,SXmemory 1 6,(fun _=>false),GXaux enabled ci(true,nil,nil)),SXct)
 (SMT,SMS bs Ms enabled ci,SXct).

(* No execution premise: full normalized call, then the real cache copy. *)
Lemma SMprepare : forall enabled ci cst,exists bs Ms,
 SMsource cst enabled ci bs Ms /\
 (BXge,V293_cpu_lenv 601%Z bs,Ms,(fun _=>false),(false,nil,enabled::ci),CSO,spec_done None)|=SMowned bs /\
 load(Tptr V293_tcb_type)Ms(93%positive,0%Z)=Some(Vptr OwnershipReady).
Proof.
 intros enabled ci cst.
 destruct(V293_exit_boundary_entry_global 80%positive 81%positive 82%positive
 (BXprogram true)kstop GXempty(BXprogram true)GXempty((fun _=>None):intunit)
 (GXtasks CSready)(GXenvs SXcaller)(GXaux enabled ci(true,nil,nil))cst
 (curs(scall 501%Z nil))kenil SXcaller BXge SXcaller(SXmemory 1 6)(fun _=>false)
 enabled nil ci(RIabstract SXct)(spec_done None)SXct SXframe OwnershipTasks 6
 300%Z 107%Z 100%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z
 108%Z 109%Z 113%Z 601%Z 110%Z 111%Z(BXcmd true)
 92%positive 91%positive 93%positive 94%positive 95%positive 98%positive 96%positive 97%positive
 (Int.repr 19)(V293_byteval 88)(Vptr OwnershipWaiting)
 (BXmerge true)(GXcode CSready)(GXenv SXcaller)(GXaux_current enabled ci(true,nil,nil))I
 eq_refl eq_refl ltac:(vm_compute;intuition congruence)
 ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)
 ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)
 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
 (RIfixed_tasks SXct)SXcurrent SXnot_highest SXframe_good(SXlookup 1 6)(BXindependent_entry ci))
 as(bs&next&nh&Me&Fresh&Different&PriorityDifferent&Highest&NextPriority&Exec&Post&Target&Counter&Cache&Alive&Frame).
 assert(Next:next=OwnershipReady).
 { destruct RTliteral_rel as(Lo&Hi&Nonempty&Bitmap&Table).
   eapply V293_highest_unique;[exact Table|exact Highest|exact FXhighest]. }
 subst next.
 assert(Priority:nh=4).
 { destruct NextPriority as[Bound[st[m Task]]].
   assert(Ready:get OwnershipTasks OwnershipReady=Some(Int.repr 4,rdy,Vnull))by reflexivity.
   unfold get,TcbMap in Task,Ready;rewrite Ready in Task.
   apply V293_priority_repr_injective;[exact Bound|lia| ].
   symmetry;exact(f_equal(fun x=>match x with Some(p,_,_)=>p |None=>Int.zero end)Task). }
 subst nh.
 set(rest:=V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((95%positive,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((98%positive,0%Z),Tint8,V293_byteval 1) **
 (V293_owned_record_cell((97%positive,0%Z),Tint32,Vint32(Int.repr 20)) **
 (Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **SXframe))))).
 assert(Reordered:(BXge,V293_cpu_lenv 601%Z bs,Me,(fun _=>false),(false,nil,enabled::ci),CSO,spec_done None)|=
 SWINVt(V293_ready_inv 80%positive 81%positive 82%positive)SXct **
 (V293_owned_record_cell((96%positive,0%Z),Tint8,V293_byteval 6) **
 (V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval 4) **
 (V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady) **rest)))).
 { unfold rest;clear -Post;sep auto. }
 set(inner:=kseq(sprim excrit)(kseq sret kstop)).
 destruct(V293_handoff_copy_execution 80%positive 81%positive 82%positive(BXprogram true)inner
 BXge(V293_cpu_lenv 601%Z bs)Me(fun _=>false)(false,nil,enabled::ci)CSO(spec_done None)SXct rest
 103%Z 110%Z 106%Z 91%positive 96%positive 93%positive 4 6 OwnershipReady
 ltac:(lia)ltac:(unfold V293_cpu_lenv;rewrite map_get_set' by discriminate;apply map_emp_get)
 ltac:(unfold V293_cpu_lenv;rewrite map_get_set' by discriminate;apply map_emp_get)
 eq_refl eq_refl Reordered)
 as(Ms&Copy&CopyStore&After&CopyFrame).
 assert(Owned:(BXge,V293_cpu_lenv 601%Z bs,Ms,(fun _=>false),(false,nil,enabled::ci),CSO,spec_done None)|=SMowned bs).
 { unfold SMowned,SMrest,V293_irq_controls,rest,V293_owned_record_cell in *;clear -After;sep auto;sep rearr in After with(6::4::5::1::2::3::nil);apply astar_r_aemp_intro in After;
 match type of After with ?st |= ?P ** Aemp =>
 assert(Added:st|=P ** Atrue) by
 (eapply astar_mono;[intros st0 Keep;exact Keep|intros st0 Empty;exact I|exact After]);
 clear After;rename Added into After end;
 sep normal in After;sep auto. }
 assert(Read:load(Tptr V293_tcb_type)Ms(93%positive,0%Z)=Some(Vptr OwnershipReady)).
 { eapply V293_record_star_load_l with(s:=(BXge,V293_cpu_lenv 601%Z bs,Ms,(fun _=>false),(false,nil,enabled::ci),CSO,spec_done None))
 (P:=V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady))(Q:=Atrue).
 - apply V293_owned_record_cell_load.
 - clear -After;sep auto. }
 rewrite BXmerge in Copy.
 pose proof(V293_csteps_global GXempty(BXprogram true)GXempty((fun _=>None):intunit)
 _ _ _ _ Copy 300%Z(BXbody true)SXcaller GXirq Tvoid dnil(dcons 601%Z Tint32 dnil)
 (GXtasks CSready)(GXenvs SXcaller)SXct(fun _=>false)
 (SMA enabled ci)(false,nil,enabled::ci)cst eq_refl(map_get_set _ _ _)I)as CopyGlobal.
 cbn[V293_global_at V293_enclose AddKsToTail]in CopyGlobal.
 exists bs;exists Ms;split;[ |split;assumption].
 unfold SMsource,SMS,SML,SMA,SMT.
 eapply V293_global_trans;[exact Exec|exact CopyGlobal].
Qed.

Theorem SMcompleted_match : forall enabled ci cst,exists bs Ms Mf,
 SMsource cst enabled ci bs Ms /\
 lpstep(BXglobal true)SMT cst(SMS bs Ms enabled ci)SXct SMTf cst(SMS bs Mf enabled ci)OwnershipReady /\
 hpstep SMPh CST cst CSO CSTnext cst CSnext /\
 V293_control_capture 98%positive 94%positive 95%positive
 (BXge,V293_cpu_lenv 601%Z bs,Mf,(fun _=>false),(false,nil,enabled::ci),CSnext,spec_done None)=Some(CSnext,CSc) /\
 load(Tptr V293_tcb_type)Mf(1%positive,0%Z)=Some(Vptr OwnershipReady) /\
 get CSnext curtid=Some(oscurt OwnershipReady) /\
 load Tint8 Mf(96%positive,0%Z)=Some(V293_byteval 4) /\
 (forall T' cst' S' t',lpstep(BXglobal true)SMT cst(SMS bs Ms enabled ci)SXct T' cst' S' t' ->
 T'=SMTf /\cst'=cst /\S'=SMS bs Mf enabled ci /\t'=OwnershipReady) /\
 ~lpstepabt(BXglobal true)SMT cst(SMS bs Ms enabled ci)SXct /\
 get SMTf OwnershipReady=Some CSready /\get CSTnext OwnershipReady=Some CSready /\
 get(SML bs)OwnershipReady=Some SXcaller /\
 @get tid localst ltaskstset TaskLStMap(SMA enabled ci)OwnershipReady=Some(true,nil,nil).
Proof.
 intros enabled ci cst.
 destruct(SMprepare enabled ci cst)as(bs&Ms&Exec&Owned&Read).
 destruct(V293_control_switch_forward 80%positive 81%positive 82%positive
 98%positive 94%positive 95%positive GXempty(BXprogram true)GXempty((fun _=>None):intunit)
 (fun _=>None)(fun _=>None)V293_scheduler SMT CST cst SXct OwnershipReady 106%Z SMK CSke CSks
 (spec_done None)BXge(V293_cpu_lenv 601%Z bs)(SML bs)Ms(fun _=>false)(SMA enabled ci)nil(enabled::ci)
 93%positive 1%positive V293_tcb_type CSO(spec_done None)(SMrest bs)1 0 0
 ltac:(lia)ltac:(lia)ltac:(lia)(map_get_set _ _ _)(map_get_set _ _ _)(map_get_set _ _ _)
 eq_refl Read eq_refl eq_refl CSchosen(map_get_set _ _ _)Owned)
 as(Mf&Low&Store&High&Event&After&Captured&Physical&Observed&All&Output&NoAbort&Frames).
 assert(Cache:load Tint8 Mf(96%positive,0%Z)=Some(V293_byteval 4)).
 { eapply V293_record_star_load_l with(s:=(BXge,V293_cpu_lenv 601%Z bs,Mf,(fun _=>false),(false,nil,enabled::ci),CSnext,spec_done None))
 (P:=V293_owned_record_cell((96%positive,0%Z),Tint8,V293_byteval 4))(Q:=Atrue).
 - apply V293_owned_record_cell_load.
 - unfold SMrest in After;clear -After;sep auto. }
 exists bs;exists Ms;exists Mf.
 repeat first[assumption|split].
Qed.

(* Both task entries are nonempty; the suspended caller and saved IE stack
   are retained at the very same cutpoint, rather than replaced by emp. *)
Lemma SMsaved_context : forall bs enabled ci,
 get SMTf SXct=Some(BXend true) /\
 get CSTnext OwnershipWaiting=Some CSafter /\
 get(SML bs)SXct=Some(V293_cpu_lenv 601%Z bs) /\
 @get tid localst ltaskstset TaskLStMap(SMA enabled ci)SXct=Some(false,nil,enabled::ci).
Proof.
 intros;repeat split;apply map_get_set.
Qed.
