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

Require Import CertiOS.audit.probes.V293OSIntExitBoundarySwitchProbe.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitResumedReturn.

Definition RXblock := 7000%positive.
Definition RXpending tail : code :=
 (SKIP,(kenil,kseq(sprim excrit)(kseq sret(kcall 300%Z(BXbody true)SXcaller tail)))).
Definition RXtasks tail := GXtasks(RXpending tail).
Definition RXenvs := GXenvs(V293_cpu_lenv 601%Z RXblock).
Definition RXaux enabled ci ne nci := GXaux enabled ci((false,nil,ne::nci):localst).
Lemma RXfresh : fresh(SXmemory 1 6)RXblock.
Proof.
 intros l i E[v Present];subst l.
 unfold SXmemory in Present;rewrite map_merge_semp in Present by reflexivity.
 rewrite SXold_outside in Present by discriminate.
 unfold SXextra,FXextra in Present;rewrite OwnershipCellsOutside in Present.
 - discriminate.
 - intro E;vm_compute in E;intuition congruence.
Qed.
Lemma RXframe_entry : forall ci M,
 store Tint32(allocb(SXmemory 1 6)RXblock 0%Z 4)(RXblock,0%Z)(Vint32 Int.zero)=Some M ->
 (BXge,SXcaller,M,(fun _=>false),(false,nil,ci),RIabstract SXct,spec_done None)|=
 SWINVt(V293_ready_inv 80%positive 81%positive 82%positive)SXct **
 (V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval 88) **
 (V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipWaiting) **
 (V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval 1) **
 (V293_owned_record_cell((95%positive,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((96%positive,0%Z),Tint8,V293_byteval 6) **
 (V293_owned_record_cell((98%positive,0%Z),Tint8,V293_byteval 1) **
 (V293_owned_record_cell((97%positive,0%Z),Tint32,Vint32(Int.repr 19)) **
 (Amapsto(RXblock,0%Z)Tint32 true(Vint32 Int.zero) **SXframe)))))))).
Proof.
 intros ci M Store.
 pose proof(V293_cpu_initialized_frame BXge SXcaller(SXmemory 1 6)(fun _=>false)
 (false,nil,ci)(RIabstract SXct)(spec_done None)RXblock M SXpre
 RXfresh(BXindependent_entry ci)Store)as Held.
 unfold SXpre,SXentry_frame in Held;sep auto.
Qed.
Lemma RXhighest : forall next,V293_highest_ready OwnershipTasks next ->next=OwnershipReady.
Proof.
 intros next Highest;destruct RTliteral_rel as(Lo&Hi&Nonempty&Bitmap&Table).
 eapply V293_highest_unique;[exact Table|exact Highest|exact FXhighest].
Qed.
Lemma RXpending_bindings : forall tail enabled ci ne nci next,
 V293_highest_ready OwnershipTasks next ->
 get(RXtasks tail)next=Some(RXpending tail) /\
 get RXenvs next=Some(V293_cpu_lenv 601%Z RXblock) /\
 get(RXaux enabled ci ne nci)next=Some(false,nil,ne::nci).
Proof.
 intros;apply RXhighest in H;subst next.
 unfold RXtasks,RXenvs,RXaux,GXtasks,GXenvs,GXaux.
 repeat split;rewrite map_get_set' by discriminate;apply map_get_set.
Qed.

(* Storage is constructed below; this lemma is reusable on that exact result. *)
Theorem RXcomplete_initialized : forall M enabled ci ne nci tail cst,
 store Tint32(allocb(SXmemory 1 6)RXblock 0%Z 4)(RXblock,0%Z)(Vint32 Int.zero)=Some M ->
 exists bs Msw Mret,fresh M bs /\
 V293_global_steps(BXglobal true)cst
 (RXtasks tail,(BXge,RXenvs,M,(fun _=>false),RXaux enabled ci ne nci),SXct)
 (set(set(RXtasks tail)SXct(BXend true))OwnershipReady(SKIP,(kenil,tail)),
 (BXge,set(set RXenvs SXct(V293_cpu_lenv 601%Z bs))OwnershipReady SXcaller,
 Mret,(fun _=>false),set(set(RXaux enabled ci ne nci)SXct(false,nil,enabled::ci))OwnershipReady(ne,nil,nci)),OwnershipReady) /\
 free Tint32 RXblock Msw=Some Mret /\
 (forall i,(0<=i<4)%Z ->get Mret(RXblock,i)=None) /\
 (forall b i,b<>RXblock ->get Mret(b,i)=get Msw(b,i)) /\
 load(Tptr V293_tcb_type)Mret(1%positive,0%Z)=Some(Vptr OwnershipReady) /\
 load Tint8 Mret(96%positive,0%Z)=Some(V293_byteval 4) /\
 load Tint32 Mret(97%positive,0%Z)=Some(Vint32(Int.repr 20)) /\
 (forall k,k<4 ->exists v,get Mret(bs,Z.of_nat k)=Some(true,v)) /\
 get(set(set(RXtasks tail)SXct(BXend true))OwnershipReady(SKIP,(kenil,tail)))SXct=Some(BXend true) /\
 get(set(set RXenvs SXct(V293_cpu_lenv 601%Z bs))OwnershipReady SXcaller)SXct=Some(V293_cpu_lenv 601%Z bs) /\
 get(set(set(RXaux enabled ci ne nci)SXct(false,nil,enabled::ci))OwnershipReady(ne,nil,nci))SXct=Some(false,nil,enabled::ci).
Proof.
 intros M enabled ci ne nci tail cst Store.
 destruct(V293_success_scheduler_storage(SXmemory 1 6)RXblock RXfresh)
 as(M'&Store'&Writable&FreeBack&Outside).
 change(store Tint32(allocb(SXmemory 1 6)RXblock 0%Z 4)(RXblock,0%Z)(Vint32 Int.zero)=Some M')in Store'.
 rewrite Store in Store';inversion Store';subst M'.
 assert(Lookup:forall n,n<256 ->load Tint8 M(92%positive,Z.of_nat n)=Some(V293_byteval(V293_ready_lookup n))).
 { intros n N;etransitivity;[apply V293_load_block_frame;intro i;apply Outside;discriminate|apply SXlookup;exact N]. }
 destruct(V293_OSIntExit_call_switch_resume 80%positive 81%positive 82%positive
 (BXprogram true)kstop GXempty(BXprogram true)GXempty((fun _=>None):intunit)
 (RXtasks tail)RXenvs(RXaux enabled ci ne nci)cst
 (curs(scall 501%Z nil))kenil SXcaller BXge SXcaller M(fun _=>false)
 enabled nil ci(RIabstract SXct)(spec_done None)SXct SXframe OwnershipTasks 6
 300%Z 107%Z 100%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z
 108%Z 109%Z 113%Z 601%Z 110%Z 111%Z
 92%positive 91%positive 93%positive 94%positive 95%positive 98%positive 96%positive 97%positive
 (Int.repr 19)(V293_byteval 88)(Vptr OwnershipWaiting)1%positive
 RXblock(Vint32 Int.zero)SXcaller tail false ne nil nci
 (BXmerge true)(GXcode(RXpending tail))(GXenv(V293_cpu_lenv 601%Z RXblock))
 (GXaux_current enabled ci((false,nil,ne::nci):localst))I
 eq_refl eq_refl ltac:(vm_compute;intuition congruence)
 ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)
 ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)
 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
 (map_get_set _ _ _)(BXdomain(RXpending tail)(V293_cpu_lenv 601%Z RXblock)((false,nil,ne::nci):localst)enabled ci)
 (RIfixed_tasks SXct)SXcurrent SXnot_highest SXframe_good
 ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)
 (RXpending_bindings tail enabled ci ne nci)Lookup(RXframe_entry ci M Store))
 as(bs&next&nh&Msw&Mret&Fresh&Different&PriorityDifferent&Highest&NextPriority&Exec&Free&Removed&Frame&Pointer&Cache&Counter&Alive&OldCode&OldEnv&OldAux).
 apply RXhighest in Highest;subst next.
 assert(Priority:nh=4).
 { destruct NextPriority as[Bound[st[m Task]]].
   assert(Ready:get OwnershipTasks OwnershipReady=Some(Int.repr 4,rdy,Vnull))by reflexivity.
   unfold get,TcbMap in Task,Ready;rewrite Ready in Task.
   apply V293_priority_repr_injective;[exact Bound|lia| ].
   symmetry;exact(f_equal(fun x=>match x with Some(p,_,_)=>p |None=>Int.zero end)Task). }
 subst nh;exists bs;exists Msw;exists Mret;repeat first[assumption|split].
Qed.

Definition RXreturned M enabled ci ne nci tail cst :=
 exists bs Msw Mret,fresh M bs /\
 V293_global_steps(BXglobal true)cst
 (RXtasks tail,(BXge,RXenvs,M,(fun _=>false),RXaux enabled ci ne nci),SXct)
 (set(set(RXtasks tail)SXct(BXend true))OwnershipReady(SKIP,(kenil,tail)),
 (BXge,set(set RXenvs SXct(V293_cpu_lenv 601%Z bs))OwnershipReady SXcaller,
 Mret,(fun _=>false),set(set(RXaux enabled ci ne nci)SXct(false,nil,enabled::ci))OwnershipReady(ne,nil,nci)),OwnershipReady) /\
 free Tint32 RXblock Msw=Some Mret /\
 (forall i,(0<=i<4)%Z ->get Mret(RXblock,i)=None) /\
 (forall b i,b<>RXblock ->get Mret(b,i)=get Msw(b,i)) /\
 load(Tptr V293_tcb_type)Mret(1%positive,0%Z)=Some(Vptr OwnershipReady) /\
 load Tint8 Mret(96%positive,0%Z)=Some(V293_byteval 4) /\
 load Tint32 Mret(97%positive,0%Z)=Some(Vint32(Int.repr 20)) /\
 (forall k,k<4 ->exists v,get Mret(bs,Z.of_nat k)=Some(true,v)) /\
 get(set(set(RXtasks tail)SXct(BXend true))OwnershipReady(SKIP,(kenil,tail)))SXct=Some(BXend true) /\
 get(set(set RXenvs SXct(V293_cpu_lenv 601%Z bs))OwnershipReady SXcaller)SXct=Some(V293_cpu_lenv 601%Z bs) /\
 get(set(set(RXaux enabled ci ne nci)SXct(false,nil,enabled::ci))OwnershipReady(ne,nil,nci))SXct=Some(false,nil,enabled::ci).

Theorem RXboth_initial_IE : forall ci ne nci tail cst,
 exists M,
 store Tint32(allocb(SXmemory 1 6)RXblock 0%Z 4)(RXblock,0%Z)(Vint32 Int.zero)=Some M /\
 free Tint32 RXblock M=Some(SXmemory 1 6) /\
 RXreturned M false ci ne nci tail cst /\ RXreturned M true ci ne nci tail cst.
Proof.
 intros;destruct(V293_success_scheduler_storage(SXmemory 1 6)RXblock RXfresh)
 as(M&Store&Writable&Free&Outside).
 exists M;split;[exact Store| ];split;[exact Free| ];split;
 apply RXcomplete_initialized;exact Store.
Qed.
Theorem RXboth_target_IE : forall enabled ci nci tail cst,
 exists M,RXreturned M enabled ci false nci tail cst /\ RXreturned M enabled ci true nci tail cst.
Proof.
 intros;destruct(V293_success_scheduler_storage(SXmemory 1 6)RXblock RXfresh)
 as(M&Store&Writable&Free&Outside).
 exists M;split;apply RXcomplete_initialized;exact Store.
Qed.
Lemma RXsaved : forall M ge le ir aux op,
 store Tint32(allocb(SXmemory 1 6)RXblock 0%Z 4)(RXblock,0%Z)(Vint32 Int.zero)=Some M ->
 (ge,le,M,ir,aux,RIabstract SXct,op)|=Amapsto(RXblock,0%Z)Tint32 true(Vint32 Int.zero) **Atrue.
Proof.
 intros M ge le ir aux op Store.
 pose proof(RXframe_entry nil M Store)as Entry.
 assert(Cell:(BXge,SXcaller,M,(fun _=>false),(false,nil,nil),RIabstract SXct,spec_done None)|=
 Amapsto(RXblock,0%Z)Tint32 true(Vint32 Int.zero) **Atrue)by(sep auto).
 eapply V293_saved_cell_context;exact Cell.
Qed.
Theorem RXstack_top_ablation : forall enabled ci tail cst,
 exists M Mf,
 free Tint32 RXblock M=Some Mf /\ Mf=SXmemory 1 6 /\
 V293_global_steps(BXglobal true)cst
 (RXtasks tail,(BXge,RXenvs,M,(fun _=>false),RXaux false nil enabled(negb enabled::ci)),OwnershipReady)
 (set(RXtasks tail)OwnershipReady(SKIP,(kenil,tail)),
 (BXge,set RXenvs OwnershipReady SXcaller,Mf,(fun _=>false),
 set(RXaux false nil enabled(negb enabled::ci))OwnershipReady(enabled,nil,negb enabled::ci)),OwnershipReady) /\
 V293_global_steps(BXglobal true)cst
 (RXtasks tail,(BXge,RXenvs,M,(fun _=>false),
 set(RXaux false nil enabled(negb enabled::ci))OwnershipReady(false,nil,negb enabled::ci)),OwnershipReady)
 (set(RXtasks tail)OwnershipReady(SKIP,(kenil,tail)),
 (BXge,set RXenvs OwnershipReady SXcaller,Mf,(fun _=>false),
 set(RXaux false nil enabled(negb enabled::ci))OwnershipReady(negb enabled,nil,ci)),OwnershipReady) /\
 set(RXaux false nil enabled(negb enabled::ci))OwnershipReady(enabled,nil,negb enabled::ci)<>
 set(RXaux false nil enabled(negb enabled::ci))OwnershipReady(negb enabled,nil,ci).
Proof.
 intros;destruct(V293_success_scheduler_storage(SXmemory 1 6)RXblock RXfresh)
 as(M&Store&Writable&FreeBack&Outside).
 pose proof(RXpending_bindings tail false nil enabled(negb enabled::ci)OwnershipReady FXhighest)as(Code&Env&Aux).
 destruct(V293_int_exit_stack_ablation GXempty(BXprogram true)GXempty((fun _=>None):intunit)
 (RXtasks tail)RXenvs(RXaux false nil enabled(negb enabled::ci))OwnershipReady cst BXge M(fun _=>false)
 false enabled nil ci(RIabstract SXct)(spec_done None)Atrue 300%Z(BXbody true)SXcaller tail
 Tvoid dnil(dcons 601%Z Tint32 dnil)601%Z RXblock(Vint32 Int.zero)
 eq_refl I Code Env Aux(RXsaved M _ _ _ _ _ Store))as(Mf&Positive&Negative&Free&Unequal).
 exists M;exists Mf;repeat first[assumption|split];congruence.
Qed.

Definition RXint_tail := kseq(sprim exint)(kint(curs(scall 501%Z nil))kenil
 (set emp 909%Z(701%positive,Tint8))kstop).
Definition RXint_aux enabled := GXaux false nil((false,[7],enabled::nil):localst).
Theorem RXexplicit_exint : forall enabled cst,
 exists M Mf,
 free Tint32 RXblock M=Some Mf /\ Mf=SXmemory 1 6 /\
 V293_global_steps(BXglobal true)cst
 (RXtasks RXint_tail,(BXge,RXenvs,M,(fun _=>false),RXint_aux enabled),OwnershipReady)
 (set(RXtasks RXint_tail)OwnershipReady(curs(scall 501%Z nil),(kenil,kstop)),
 (BXge,set RXenvs OwnershipReady(set emp 909%Z(701%positive,Tint8)),Mf,(fun _=>false),
 set(RXint_aux enabled)OwnershipReady(true,nil,nil)),OwnershipReady) /\
 (forall j,(0<=j<4)%Z ->get Mf(RXblock,j)=None).
Proof.
 intros;destruct(V293_success_scheduler_storage(SXmemory 1 6)RXblock RXfresh)
 as(M&Store&Writable&FreeBack&Outside).
 assert(Code:get(RXtasks RXint_tail)OwnershipReady=Some(RXpending RXint_tail)).
 { unfold RXtasks,GXtasks;rewrite map_get_set' by discriminate;apply map_get_set. }
 assert(Env:get RXenvs OwnershipReady=Some(V293_cpu_lenv 601%Z RXblock)).
 { unfold RXenvs,GXenvs;rewrite map_get_set' by discriminate;apply map_get_set. }
 assert(Aux:get(RXint_aux enabled)OwnershipReady=Some(false,[7],enabled::nil)).
 { unfold RXint_aux,GXaux;rewrite map_get_set' by discriminate;apply map_get_set. }
 destruct(V293_int_exit_pending_exint GXempty(BXprogram true)GXempty((fun _=>None):intunit)
 (RXtasks RXint_tail)RXenvs(RXint_aux enabled)OwnershipReady cst BXge M(fun _=>false)
 false enabled 7 nil nil(RIabstract SXct)(spec_done None)Atrue
 300%Z(BXbody true)SXcaller kstop Tvoid dnil(dcons 601%Z Tint32 dnil)601%Z RXblock(Vint32 Int.zero)
 (curs(scall 501%Z nil))kenil(set emp 909%Z(701%positive,Tint8))
 eq_refl I Code Env Aux(RXsaved M _ _ _ _ _ Store))as(Mf&Trace&Free&Removed&Frame).
 exists M;exists Mf;repeat first[assumption|split];congruence.
Qed.
Lemma RXbare_kint_rejects_auto_pop : forall M aux,
 ~exists C' st',loststep(BXprogram true)
 (SKIP,(kenil,kint(curs(scall 501%Z nil))kenil SXcaller kstop))
 ((BXge,SXcaller,M),(fun _=>false),aux)C' st'.
Proof.
 intros M aux[C'[st' Step]];eapply V293_bare_kint_no_local_step;exact Step.
Qed.
