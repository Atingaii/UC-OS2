Require Import CertiOS.certiucos.v293.proofs.V293InterruptBuilderEnterCall.
(* Nonempty canonical storage/ready/TCB heap, actual unfiltered builder.
   The builder is a handler-entry resource, not an initialized predecessor. *)
Require Import CertiOS.certiucos.v293.proofs.V293InterruptBuilderEnterResources.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptBindings.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptQuietBuilder.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptControlRetention.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptFixedControlSpec.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterInternal.
Require Import CertiOS.certiucos.v293.code.V293OSIntEnter.
Require Import CertiOS.audit.probes.V293InterruptQuietBuilderProbe.
Require Import CertiOS.audit.probes.V293InterruptBoundQuietContinuousProbe.
Require Import CertiOS.audit.probes.V293InterruptQuietContinuousProbe.
Require Import CertiOS.audit.probes.V293OSIntExitReadyDynamicProbe.
Require Import CertiOS.audit.probes.V293OSIntExitLocalDispatchProbe.
Require Import CertiOS.audit.probes.V293InterruptReadyEnvironmentProbe.
Require Import CertiOS.audit.probes.V293OSIntExitReadyBodyProbe.
Require Import CertiOS.audit.probes.V293TaskRecordInvariantProbe.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.framework.include_frm.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptSourceRoundtrip.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptQuietISRReturn.

Require Import CertiOS.certiucos.v293.proofs.V293InterruptBuilderNestedExit.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitCallExecution.
Require Import CertiOS.audit.probes.V293InterruptBuilderEnterResourcesProbe.

Require Import CertiOS.certiucos.v293.proofs.V293InterruptBuilderNestedReturn.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyGlobalTrace.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.audit.probes.V293InterruptBuilderNestedExitProbe.
Require Import CertiOS.audit.probes.V293InterruptQuietISRReturnProbe.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.framework.proof.join_prop.

(* Same two-function BNprogram, no RDprogram substitution. The caller shadows
   both control names and has a nontrivial expression continuation. *)
Definition NGcaller:env:=set(set emp 112%Z(96%positive,Tint8))110%Z(99%positive,Tint8).
Definition NGempty:progunit:=fun _=>None.
Definition NGwrapper:=V293_irq_source_wrapper 301%Z 300%Z Int.zero.
Definition NGip:intunit:=fun i=>if Nat.eq_dec i 0 then Some NGwrapper else None.
Definition NGprog:lprog:=(NGempty,(BNprogram,NGempty,NGip)).
Definition NGcode:code:=(cure(econst32(Int.repr 7)),(keop1 negation Tint32 kenil,kseq(sskip None)kstop)).
Definition NGT:tasks:=set emp OwnershipWaiting NGcode.
Definition NGles:cltenvs:=set emp OwnershipWaiting NGcaller.
Definition NGaus:ltaskstset:=set emp OwnershipWaiting((true,nil,nil):localst).
Definition NGcst:clientst:=(emp,emp,emp).
Definition NGpre:=ipreasrt' 0 QKother nil(spec_done None)RDinv **p_local LDli OwnershipWaiting nil.
Definition NGret:=iretasrt' 0 QKother nil RDinv **p_local LDli OwnershipWaiting nil.
Definition NGsaved:=kint(fst NGcode)(fst(snd NGcode))NGcaller(snd(snd NGcode)).
Definition NGstart (M:mem):=(NGT,(JBge,NGles,M,QKother,NGaus),OwnershipWaiting).
Definition NGentered (M:mem):=(set NGT OwnershipWaiting(curs NGwrapper,(kenil,NGsaved)),
 (JBge,set NGles OwnershipWaiting emp,M,isrupd QKother 0 true,
 set NGaus OwnershipWaiting(false,[0],nil)),OwnershipWaiting).
Definition NGreturning (M:mem):=(set NGT OwnershipWaiting(curs(sprim exint),(kenil,NGsaved)),
 (JBge,set NGles OwnershipWaiting emp,M,QKother,
 set NGaus OwnershipWaiting(false,[0],nil)),OwnershipWaiting).
Definition NGone a b:=match a,b with(ts,os,t),(ts',os',t')=>lpstep NGprog ts NGcst os t ts' NGcst os' t' end.
Definition NGpath M:=NGone(NGstart M)(NGentered M) /\
 V293_global_steps NGprog NGcst(NGentered M)(NGreturning M) /\
 NGone(NGreturning M)(NGstart M).

Theorem NGnonempty_roundtrip : forall n,1<=n ->n<255 ->exists M frame O Of,
 join M frame(JBmemory n Int.zero Int.zero) /\join O Of(RIabstract OwnershipWaiting) /\
 QKstate(isrupd QKother 0 true)M O|=NGpre /\NGpath M /\
 QKstate(isrupd QKother 0 false)M O|=NGret.
Proof.
 intros n Lower Bound;destruct(QJentry_nonempty n ltac:(lia))as(M&frame&O&Of&JM&JO&Old).
 assert(Original:QKstate(isrupd(fun _:hid=>false)0 true)M O|=
 QKsnapshot n(isrupd(fun _:hid=>false)0 true)).
 { unfold QKsnapshot,BQsnapshot;apply V293_irq_bound_snapshot_pack;exact Old. }
 assert(Snapshot:QKstate(isrupd QKother 0 true)M O|=QKsnapshot n(isrupd QKother 0 true)).
 { apply QKsnapshot_change_isr with(irq:=isrupd(fun _:hid=>false)0 true);exact Original. }
 assert(Pre:QKstate(isrupd QKother 0 true)M O|=NGpre).
 { apply QKsnapshot_builder with(nest:=n);[lia|exact Snapshot]. }
 assert(Capture:V293_control_capture 99%positive 96%positive 97%positive
 (QKstate(isrupd QKother 0 true)M O)=Some(O,V293_control 1 n 0)).
 { eapply V293_control_capture_owned;try lia;eapply V293_irq_bound_snapshot_controls;exact Snapshot. }
 assert(Code:get NGT OwnershipWaiting=Some NGcode)by(apply map_get_set).
 assert(Env:get NGles OwnershipWaiting=Some NGcaller)by(apply map_get_set).
 assert(Aux:get NGaus OwnershipWaiting=Some((true,nil,nil):localst))by(apply map_get_set).
 assert(Higher:higherint QKother 0).
 { unfold higherint;intros j BoundJ;assert(j=0)by lia;subst;reflexivity. }
 destruct(V293_builder_nested_global_roundtrip 106%Z 112%Z 110%Z 111%Z
 92%positive 81%positive 80%positive 91%positive 82%positive 94%positive 95%positive
 99%positive 96%positive 97%positive nil NGempty BNprogram NGempty NGip NGT NGles NGaus NGcst OwnershipWaiting
 JBge NGcaller M QKother nil O(fst NGcode)(fst(snd NGcode))(snd(snd NGcode))QCintspec 0 nil NGpre NGret
 V293_scheduler 301%Z 300%Z Int.zero 120%Z 105%Z 103%Z 108%Z 109%Z 200%Z 302%Z n 0
 Code Env Aux I Higher ltac:(unfold INUM;lia)eq_refl eq_refl eq_refl eq_refl Pre Capture Lower Bound
 eq_refl eq_refl ltac:(discriminate)ltac:(discriminate)eq_refl ltac:(change(0<=0<2)%Z;lia))
 as[Entry[Body[Return Ready]]].
 exists M;exists frame;exists O;exists Of.
 split;[exact JM| ];split;[exact JO| ];split;[exact Pre| ];split;[ |exact Ready].
 unfold NGpath;split;[exact Entry| ];split;[exact Body|exact Return].
Qed.

Corollary NGboundaries :
 (exists M frame O Of,join M frame(JBmemory 1 Int.zero Int.zero) /\
 join O Of(RIabstract OwnershipWaiting) /\NGpath M) /\
 (exists M frame O Of,join M frame(JBmemory 254 Int.zero Int.zero) /\
 join O Of(RIabstract OwnershipWaiting) /\NGpath M).
Proof.
 split.
 - destruct(NGnonempty_roundtrip 1 ltac:(lia)ltac:(lia))as(M&frame&O&Of&JM&JO&Pre&Path&Ret).
   exists M;exists frame;exists O;exists Of;split;[exact JM| ];split;assumption.
 - destruct(NGnonempty_roundtrip 254 ltac:(lia)ltac:(lia))as(M&frame&O&Of&JM&JO&Pre&Path&Ret).
   exists M;exists frame;exists O;exists Of;split;[exact JM| ];split;assumption.
Qed.

Theorem NGcompleted_caller_observation : exists M frame O Of,
 join M frame(JBmemory 254 Int.zero Int.zero) /\join O Of(RIabstract OwnershipWaiting) /\
 NGpath M /\QKstate(isrupd QKother 0 false)M O|=NGret /\
 get NGles OwnershipWaiting=Some NGcaller /\get NGcaller 112%Z=Some(96%positive,Tint8).
Proof.
 destruct(NGnonempty_roundtrip 254 ltac:(lia)ltac:(lia))as(M&frame&O&Of&JM&JO&Pre&Path&Ret).
 exists M;exists frame;exists O;exists Of;split;[exact JM| ];split;[exact JO| ];
 split;[exact Path| ];split;[exact Ret| ];split;[apply map_get_set|reflexivity].
Qed.

Theorem NGcontext_and_other_ISR :
 get NGcaller 112%Z<>get(emp:env)112%Z /\
 fst(snd NGcode)<>kenil /\snd(snd NGcode)<>kstop /\
 QKother 1=true /\isrupd QKother 0 false 1=true.
Proof. repeat split;discriminate. Qed.
