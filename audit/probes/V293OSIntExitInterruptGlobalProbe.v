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
Definition GXempty : progunit := fun _=>None.
Definition GXprogram := (GXempty,(SXprogram,GXempty,(fun _=>None):intunit)).
Definition GXirq := kint(curs(scall 501%Z nil))kenil SXcaller kstop.
Definition GXtasks(other:code):tasks :=
 set(set emp OwnershipReady other)SXct(curs(scall 300%Z nil),(kenil,GXirq)).
Definition GXenvs(other:env):cltenvs := set(set emp OwnershipReady other)SXct SXcaller.
Definition GXaux(enabled:bool)(ci:cs)(other:localst):ltaskstset :=
 set(set emp OwnershipReady other)SXct(enabled,nil,ci).
Definition GXend : code := (curs(sfexec 112%Z nil nil),(kenil,SXK GXirq)).
Lemma GXmerge : SXprogram=pumerge SXprogram GXempty.
Proof. apply functional_extensionality;intro f;unfold pumerge,GXempty;destruct(SXprogram f);reflexivity. Qed.
Lemma GXcode : forall other,get(GXtasks other)SXct=Some(curs(scall 300%Z nil),(kenil,GXirq)).
Proof. intros;unfold GXtasks;apply map_get_set. Qed.
Lemma GXenv : forall other,get(GXenvs other)SXct=Some SXcaller.
Proof. intros;unfold GXenvs;apply map_get_set. Qed.
Lemma GXaux_current : forall enabled ci other,
 @get tid localst ltaskstset TaskLStMap(GXaux enabled ci other)SXct=Some(enabled,nil,ci).
Proof. intros;unfold GXaux;apply map_get_set. Qed.
Theorem GXcomplete_global_prefix : forall enabled ci other otherle otheraux cst,
 exists bs Mf,
 fresh(SXmemory 1 6)bs /\
 V293_global_steps GXprogram cst
 (GXtasks other,(SXge,GXenvs otherle,SXmemory 1 6,(fun _=>false),GXaux enabled ci otheraux),SXct)
 (set(GXtasks other)SXct GXend,
 (SXge,set(GXenvs otherle)SXct(V293_cpu_lenv 601%Z bs),Mf,(fun _=>false),
 set(GXaux enabled ci otheraux)SXct(false,nil,cons enabled ci)),SXct) /\
 (SXge,V293_cpu_lenv 601%Z bs,Mf,(fun _=>false),(false,nil,cons enabled ci),RIabstract SXct,spec_done None)|=SXpost bs /\
 load(Tptr V293_tcb_type)Mf(93%positive,0%Z)=Some(Vptr OwnershipReady) /\
 load Tint32 Mf(97%positive,0%Z)=Some(Vint32(Int.repr 20)) /\
 load Tint8 Mf(96%positive,0%Z)=Some(V293_byteval 6) /\
 (forall k,k<4 ->exists v,get Mf(bs,Z.of_nat k)=Some(true,v)).
Proof.
 intros enabled ci other otherle otheraux cst.
 destruct(V293_OSIntExit_interrupt_switch_entry 80%positive 81%positive 82%positive
 SXprogram kstop GXempty SXprogram GXempty((fun _=>None):intunit)
 (GXtasks other)(GXenvs otherle)(GXaux enabled ci otheraux)cst
 (curs(scall 501%Z nil))kenil SXcaller
 SXge SXcaller(SXmemory 1 6)(fun _=>false)enabled nil ci(RIabstract SXct)(spec_done None)
 SXct SXframe OwnershipTasks 6 300%Z 107%Z 100%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z
 108%Z 109%Z 113%Z 601%Z 110%Z 111%Z 112%Z
 92%positive 91%positive 93%positive 94%positive 95%positive 98%positive 96%positive 97%positive(Int.repr 19)
 (V293_byteval 88)(Vptr OwnershipWaiting)
 GXmerge(GXcode other)(GXenv otherle)(GXaux_current enabled ci otheraux)I
 eq_refl eq_refl ltac:(vm_compute;intuition congruence)
 ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)
 ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)
 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
 (RIfixed_tasks SXct)SXcurrent SXnot_highest SXframe_good(SXlookup 1 6)(SXindependent_entry ci))
 as(bs&next&nh&Mf&Fresh&Different&PriorityDifferent&Highest&NextPriority&Exec&Post&Target&Counter&Cache&Alive&Frame).
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
 subst nh;exists bs;exists Mf;repeat split;try assumption.
Qed.
Lemma GXother_maps : forall other otherle otheraux enabled ci bs,
 @get tid code tasks TasksMap(set(GXtasks other)SXct GXend)OwnershipReady=Some other /\
 get(set(GXenvs otherle)SXct(V293_cpu_lenv 601%Z bs))OwnershipReady=Some otherle /\
 @get tid localst ltaskstset TaskLStMap(set(GXaux enabled ci otheraux)SXct(false,nil,enabled::ci))OwnershipReady=Some otheraux.
Proof.
 intros;unfold GXtasks,GXenvs,GXaux;repeat split;
 repeat rewrite map_get_set' by discriminate;apply map_get_set.
Qed.
Theorem GXboth_IE_complete_global : forall ci other otherle otheraux cst,
 exists b0 M0 b1 M1,
 V293_global_steps GXprogram cst
 (GXtasks other,(SXge,GXenvs otherle,SXmemory 1 6,(fun _=>false),GXaux false ci otheraux),SXct)
 (set(GXtasks other)SXct GXend,
 (SXge,set(GXenvs otherle)SXct(V293_cpu_lenv 601%Z b0),M0,(fun _=>false),
 set(GXaux false ci otheraux)SXct(false,nil,cons false ci)),SXct) /\
 V293_global_steps GXprogram cst
 (GXtasks other,(SXge,GXenvs otherle,SXmemory 1 6,(fun _=>false),GXaux true ci otheraux),SXct)
 (set(GXtasks other)SXct GXend,
 (SXge,set(GXenvs otherle)SXct(V293_cpu_lenv 601%Z b1),M1,(fun _=>false),
 set(GXaux true ci otheraux)SXct(false,nil,cons true ci)),SXct) /\
 load Tint32 M0(97%positive,0%Z)=Some(Vint32(Int.repr 20)) /\
 load Tint32 M1(97%positive,0%Z)=Some(Vint32(Int.repr 20)) /\
 load Tint8 M0(99%positive,0%Z)=Some(V293_byteval 23) /\
 load Tint8 M1(99%positive,0%Z)=Some(V293_byteval 23) /\
 load Tint8 M0(100%positive,0%Z)=Some(V293_byteval 0) /\
 load Tint8 M1(100%positive,0%Z)=Some(V293_byteval 0) /\
 (forall k,k<4 ->exists v,get M0(b0,Z.of_nat k)=Some(true,v)) /\
 (forall k,k<4 ->exists v,get M1(b1,Z.of_nat k)=Some(true,v)).
Proof.
 intros ci other otherle otheraux cst.
 destruct(GXcomplete_global_prefix false ci other otherle otheraux cst)
 as(b0&M0&Fresh0&Exec0&Post0&Target0&Counter0&Cache0&Alive0).
 destruct(GXcomplete_global_prefix true ci other otherle otheraux cst)
 as(b1&M1&Fresh1&Exec1&Post1&Target1&Counter1&Cache1&Alive1).
 destruct(SXpost_loads false ci b0 M0 Post0)as(Canary0&Saved0&Run0&Local0).
 destruct(SXpost_loads true ci b1 M1 Post1)as(Canary1&Saved1&Run1&Local1).
 exists b0;exists M0;exists b1;exists M1;repeat split;assumption.
Qed.
Theorem GXprefix_endpoint_stuck : forall other otherle otheraux enabled ci bs Mf cst,
 ~exists T' cst' S' t',lpstep GXprogram
 (set(GXtasks other)SXct GXend)cst
 (SXge,set(GXenvs otherle)SXct(V293_cpu_lenv 601%Z bs),Mf,(fun _=>false),
 set(GXaux enabled ci otheraux)SXct(false,nil,enabled::ci))SXct T' cst' S' t'.
Proof.
 intros;unfold GXprogram,GXend.
 eapply V293_missing_port_disabled_no_global_step.
 - apply map_get_set.
 - apply map_get_set.
 - apply map_get_set.
 - exists(curs(sfexec 112%Z nil nil));exists kenil;exists(SXK GXirq);split;[reflexivity| ].
   right;left;exists 300%Z;exists SXcaller;exists GXirq.
   exists Tvoid;exists dnil;exists(dcons 601%Z Tint32 dnil);exists SXbody;exists SXbody.
   split;reflexivity.
 - rewrite <-GXmerge;exact SXswitch_lookup_absent.
Qed.

(* Independent boundary control, NOT the completed-prefix endpoint: ci=nil
   is identical on both sides, as required by the existing lintstep rule. *)
Definition GXinterrupts : intunit := fun _=>Some(sskip None).
Definition GXboundary_program := (GXempty,(SXprogram,GXempty,GXinterrupts)).
Definition GXboundary_aux enabled otheraux : ltaskstset :=
 set(GXaux false nil otheraux)SXct(enabled,nil,nil).
Lemma GXboundary_inos : InOS GXend(pumerge SXprogram GXempty).
Proof.
 exists(curs(sfexec 112%Z nil nil));exists kenil;exists(SXK GXirq);split;[reflexivity| ].
 right;left;exists 300%Z;exists SXcaller;exists GXirq.
 exists Tvoid;exists dnil;exists(dcons 601%Z Tint32 dnil);exists SXbody;exists SXbody.
 split;reflexivity.
Qed.
Theorem GXboundary_disabled_stuck : forall other otherle otheraux cst,
 ~exists T' cst' S' t',lpstep GXboundary_program
 (set(GXtasks other)SXct GXend)cst
 (SXge,GXenvs otherle,SXmemory 1 6,(fun _=>false),GXboundary_aux false otheraux)SXct
 T' cst' S' t'.
Proof.
 intros;unfold GXboundary_program,GXboundary_aux,GXend.
 eapply V293_missing_port_disabled_no_global_step.
 - apply map_get_set.
 - apply GXenv.
 - apply map_get_set.
 - exact GXboundary_inos.
 - rewrite <-GXmerge;exact SXswitch_lookup_absent.
Qed.
Theorem GXboundary_enabled_interrupt : forall other otherle otheraux cst,
 lpstep GXboundary_program
 (set(GXtasks other)SXct GXend)cst
 (SXge,GXenvs otherle,SXmemory 1 6,(fun _=>false),GXboundary_aux true otheraux)SXct
 (set(set(GXtasks other)SXct GXend)SXct
   (curs(sskip None),(kenil,kint(curs(sfexec 112%Z nil nil))kenil SXcaller(SXK GXirq))))cst
 (SXge,set(GXenvs otherle)SXct emp,SXmemory 1 6,isrupd(fun _=>false)0 true,
   set(GXboundary_aux true otheraux)SXct(false,[0],nil))SXct.
Proof.
 intros;eapply pint_step.
 - reflexivity.
 - apply map_get_set.
 - reflexivity.
 - unfold projS,projD,GXboundary_aux;rewrite GXenv,map_get_set;reflexivity.
 - unfold projS,projD;rewrite !map_get_set;reflexivity.
 - split;[unfold Dteq|unfold Piteq];intros otherid Apart;cbn;
   rewrite map_get_set' by congruence;reflexivity.
 - unfold GXend;eapply li_step with(i:=0).
   + exact 0.
   + reflexivity.
   + intros i Bound;reflexivity.
   + unfold INUM;lia.
   + reflexivity.
Qed.
Theorem GXonly_IE_changed : forall otheraux t,
 t<>SXct ->
 @get tid localst ltaskstset TaskLStMap(GXboundary_aux false otheraux)t=
 @get tid localst ltaskstset TaskLStMap(GXboundary_aux true otheraux)t.
Proof.
 intros;unfold GXboundary_aux;rewrite !map_get_set' by congruence;reflexivity.
Qed.
(* Concrete nonempty second task: the prefix quantifies over its code, env
   and auxiliary state, so replacing any one of them does not affect reachability. *)
Definition GXother : code := (curs(scall 777%Z nil),(kenil,kstop)).
Theorem GXnonempty_other_task_frame : forall bs,
 @get tid code tasks TasksMap(set(GXtasks GXother)SXct GXend)OwnershipReady=Some GXother /\
 get(set(GXenvs SXcaller)SXct(V293_cpu_lenv 601%Z bs))OwnershipReady=Some SXcaller /\
 @get tid localst ltaskstset TaskLStMap
 (set(GXaux true nil(true,[1],nil))SXct(false,nil,[true]))OwnershipReady=Some(true,[1],nil) /\
 get SXcaller 601%Z=Some(99%positive,Tint8).
Proof.
 intro bs;destruct(GXother_maps GXother SXcaller(true,[1],nil)true nil bs)as(C&E&A).
 repeat split;try assumption;reflexivity.
Qed.
