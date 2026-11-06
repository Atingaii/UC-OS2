(* Same nonempty canonical fixture and same two-function program in every case. *)
Require Import CertiOS.certiucos.v293.proofs.V293InterruptBuilderQuietExecution.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptBuilderEnterCall.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptBindings.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptQuietBuilder.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptBoundEntry.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptControlRetention.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptFixedControlSpec.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyGlobalTrace.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterInternal.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.code.V293OSIntEnter.
Require Import CertiOS.audit.probes.V293InterruptBuilderNestedReturnProbe.
Require Import CertiOS.audit.probes.V293InterruptBuilderNestedExitProbe.
Require Import CertiOS.audit.probes.V293InterruptQuietBuilderProbe.
Require Import CertiOS.audit.probes.V293InterruptBoundQuietContinuousProbe.
Require Import CertiOS.audit.probes.V293InterruptQuietContinuousProbe.
Require Import CertiOS.audit.probes.V293InterruptQuietISRReturnProbe.
Require Import CertiOS.audit.probes.V293InterruptReadyEnvironmentProbe.
Require Import CertiOS.audit.probes.V293OSIntExitReadyDynamicProbe.
Require Import CertiOS.audit.probes.V293OSIntExitLocalDispatchProbe.
Require Import CertiOS.audit.probes.V293OSIntExitReadyBodyProbe.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.audit.probes.V293TaskRecordInvariantProbe.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.framework.proof.join_prop.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition QEsnapshot r n l irq:=BQsnapshot r n l(spec_done None)false irq[0]nil OwnershipWaiting.
Definition QEinput r l M:=V293_put_byte(V293_put_byte M(99%positive,0%Z)r)(97%positive,0%Z)l.
Definition QEfinal r n l:=V293_control_exit(V293_control_enter(V293_control r n l)).
Definition QEmemory r n l M:=V293_put_byte M(96%positive,0%Z)(V293_control_nesting(QEfinal r n l)).
Definition QEpath M Mf:=NGone(NGstart M)(NGentered M) /\
 V293_global_steps NGprog NGcst(NGentered M)(NGreturning Mf) /\
 NGone(NGreturning Mf)(NGstart Mf).

Lemma QEbyte_update : forall b old n F ge le M ir aux O op,n<256 ->
 (ge,le,M,ir,aux,O,op)|=Amapsto(b,0%Z)Tint8 true(V293_byteval old) **F ->
 (ge,le,V293_put_byte M(b,0%Z)n,ir,aux,O,op)|=Amapsto(b,0%Z)Tint8 true(V293_byteval n) **F.
Proof.
 intros b old n F ge le M ir aux O op N Held.
 destruct(V293_builder_byte_writable _ _ _ _ Held)as[v Writable].
 destruct(V293_tick_raw_slot_update(b,0%Z)Tint8(V293_byteval old)(V293_byteval n)
 F ge le M ir aux O op(V293_byte_type n N)Held)as[Mf[Store Updated]].
 assert(Same:Mf=V293_put_byte M(b,0%Z)n).
 { pose proof(V293_put_byte_store M(b,0%Z)n v Writable);congruence. }
 subst Mf;unfold V293_owned_record_cell in Updated.
 apply astar_mono with(P':=Amapsto(b,0%Z)Tint8 true(V293_byteval n))(Q':=F)in Updated.
 2:{ intros s K;apply astar_l_apure_elim in K;tauto. }
 2:{ intros s K;exact K. }
 exact Updated.
Qed.

Lemma QEreplace_controls : forall r n l irq M O,r<256 ->l<256 ->
 QKstate irq M O|=QEsnapshot 1 n 0 irq ->
 QKstate irq(QEinput r l M)O|=QEsnapshot r n l irq.
Proof.
 intros r n l irq M O R L Held.
 set(F:=<||spec_done None||> ** OS[irq,false,[0],nil] **
 (Amapsto(96%positive,0%Z)Tint8 true(V293_byteval n) **
 (Amapsto(97%positive,0%Z)Tint8 true(V293_byteval 0) **
 (p_local LDli OwnershipWaiting nil ** Aemp **
 (QCkept ** A_dom_lenv nil))))).
 assert(Owned:QKstate irq M O|=Amapsto(99%positive,0%Z)Tint8 true(V293_byteval 1) **F).
 { clear -Held;unfold F,QEsnapshot,BQsnapshot,V293_irq_bound_snapshot,V293_enter_bound_external,LDli,QCkept in *;sep auto. }
 pose proof(QEbyte_update 99%positive 1 r F JBge emp M irq(false,[0],nil)O(spec_done None)R Owned)as Running.
 set(G:=<||spec_done None||> ** OS[irq,false,[0],nil] **
 (Amapsto(96%positive,0%Z)Tint8 true(V293_byteval n) **
 (Amapsto(99%positive,0%Z)Tint8 true(V293_byteval r) **
 (p_local LDli OwnershipWaiting nil ** Aemp **
 (QCkept ** A_dom_lenv nil))))).
 assert(OwnedLock:QKstate irq(V293_put_byte M(99%positive,0%Z)r)O|=
 Amapsto(97%positive,0%Z)Tint8 true(V293_byteval 0) **G).
 { unfold F,G in *;clear Held Owned;sep auto. }
 pose proof(QEbyte_update 97%positive 0 l G JBge emp(V293_put_byte M(99%positive,0%Z)r)
 irq(false,[0],nil)O(spec_done None)L OwnedLock)as Locked.
 unfold QEinput,QKstate,QEsnapshot,BQsnapshot,V293_irq_bound_snapshot,V293_enter_bound_external,G,LDli,QCkept in *;
 clear Held Owned Running OwnedLock;sep auto.
Qed.

(* A complete run, not merely arithmetic examples or assumed post-resources. *)
Theorem QEnonempty_execution : forall r n l,r<256 ->n<256 ->l<256 ->
 V293_control_dispatch(V293_control_enter(V293_control r n l))=false ->
 exists M0 frame O Of,
 join M0 frame(JBmemory n Int.zero Int.zero) /\join O Of(RIabstract OwnershipWaiting) /\
 let M:=QEinput r l M0 in let Mf:=QEmemory r n l M in
 QKstate(isrupd QKother 0 true)M O|=NGpre /\
 QKstate(isrupd QKother 0 true)M O|=QEsnapshot r n l(isrupd QKother 0 true) /\
 QEpath M Mf /\QKstate(isrupd QKother 0 false)Mf O|=NGret /\
 V293_control_steps V293_scheduler V293_fixed_control_handler(O,V293_control r n l)
 (V293_control_Core(spec_done None))(O,QEfinal r n l).
Proof.
 intros r n l R N L Quiet;destruct(QJentry_nonempty n N)as(M0&frame&O&Of&JM&JO&Old).
 assert(Original:QKstate(isrupd(fun _:hid=>false)0 true)M0 O|=
 QKsnapshot n(isrupd(fun _:hid=>false)0 true)).
 { unfold QKsnapshot,BQsnapshot;apply V293_irq_bound_snapshot_pack;exact Old. }
 assert(Snapshot0:QKstate(isrupd QKother 0 true)M0 O|=QKsnapshot n(isrupd QKother 0 true)).
 { apply QKsnapshot_change_isr with(irq:=isrupd(fun _:hid=>false)0 true);exact Original. }
 pose proof(QEreplace_controls r n l(isrupd QKother 0 true)M0 O R L Snapshot0)as Snapshot.
 set(M:=QEinput r l M0).
 assert(Pre:QKstate(isrupd QKother 0 true)M O|=NGpre).
 { unfold QEsnapshot,BQsnapshot in Snapshot.
   eapply V293_bound_outer_snapshot_pre;[exact R|exact N|exact L|exact Snapshot]. }
 assert(Capture:V293_control_capture 99%positive 96%positive 97%positive
 (QKstate(isrupd QKother 0 true)M O)=Some(O,V293_control r n l)).
 { eapply V293_control_capture_owned;try assumption;eapply V293_irq_bound_snapshot_controls;exact Snapshot. }
 assert(Code:get NGT OwnershipWaiting=Some NGcode)by(apply map_get_set).
 assert(Env:get NGles OwnershipWaiting=Some NGcaller)by(apply map_get_set).
 assert(Aux:get NGaus OwnershipWaiting=Some((true,nil,nil):localst))by(apply map_get_set).
 assert(Higher:higherint QKother 0).
 { unfold higherint;intros j BoundJ;assert(j=0)by lia;subst;reflexivity. }
 destruct(V293_builder_quiet_global_return 106%Z 112%Z 110%Z 111%Z
 92%positive 81%positive 80%positive 91%positive 82%positive 94%positive 95%positive
 99%positive 96%positive 97%positive nil NGempty BNprogram NGempty NGip NGT NGles NGaus NGcst OwnershipWaiting
 JBge NGcaller M QKother nil O(fst NGcode)(fst(snd NGcode))(snd(snd NGcode))QCintspec 0 nil NGpre NGret
 V293_scheduler 301%Z 300%Z Int.zero 120%Z 105%Z 103%Z 108%Z 109%Z 200%Z 302%Z(V293_control r n l)
 Code Env Aux I Higher ltac:(unfold INUM;lia)eq_refl eq_refl eq_refl eq_refl Pre Capture Quiet
 eq_refl eq_refl ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)eq_refl ltac:(change(0<=0<2)%Z;lia))
 as[Entry[Body[Return[Ready Fixed]]]].
 exists M0;exists frame;exists O;exists Of;split;[exact JM| ];split;[exact JO| ].
 cbn zeta;split;[exact Pre| ];split;[exact Snapshot| ];split;[ |split;[exact Ready|exact Fixed]].
 unfold QEpath;split;[exact Entry| ];split;[exact Body|exact Return].
Qed.

Definition QEcase r n l:=exists M0 frame O Of,
 join M0 frame(JBmemory n Int.zero Int.zero) /\join O Of(RIabstract OwnershipWaiting) /\
 QEpath(QEinput r l M0)(QEmemory r n l(QEinput r l M0)).
Corollary QEall_quiet_boundaries :
 QEcase 0 0 0 /\QEcase 2 255 0 /\QEcase 1 1 0 /\QEcase 1 254 0 /\QEcase 1 255 0 /\QEcase 1 0 1.
Proof.
 assert(H:forall r n l,r<256 ->n<256 ->l<256 ->
 V293_control_dispatch(V293_control_enter(V293_control r n l))=false ->QEcase r n l).
 { intros r n l R N L Quiet.
   destruct(QEnonempty_execution r n l R N L Quiet)as(M&frame&O&Of&JM&JO&Pre&Snapshot&Path&Ret&Fixed).
   exists M;exists frame;exists O;exists Of;split;[exact JM| ];split;[exact JO|exact Path]. }
 repeat split;apply H;try lia;reflexivity.
Qed.

Theorem QEcompleted_saturated_observation : exists M0 frame O Of,
 join M0 frame(JBmemory 255 Int.zero Int.zero) /\join O Of(RIabstract OwnershipWaiting) /\
 let M:=QEinput 1 0 M0 in let Mf:=QEmemory 1 255 0 M in
 QEpath M Mf /\QKstate(isrupd QKother 0 false)Mf O|=NGret /\
 load Tint8 Mf(96%positive,0%Z)=Some(V293_byteval 254) /\Mf<>M.
Proof.
 destruct(QEnonempty_execution 1 255 0 ltac:(lia)ltac:(lia)ltac:(lia)eq_refl)
 as(M0&frame&O&Of&JM&JO&Pre&Snapshot&Path&Ret&Fixed).
 exists M0;exists frame;exists O;exists Of;split;[exact JM| ];split;[exact JO| ].
 cbn zeta;split;[exact Path| ];split;[exact Ret| ];split.
 - apply V293_put_byte_load;lia.
 - assert(Controls:QKstate(isrupd QKother 0 true)(QEinput 1 0 M0)O|=V293_irq_controls 99%positive 96%positive 97%positive 1 255 0).
   { eapply V293_irq_bound_snapshot_controls;exact Snapshot. }
   destruct(V293_irq_controls_load 99%positive 96%positive 97%positive 1 255 0
   _ ltac:(lia)ltac:(lia)ltac:(lia)Controls)as[Run[Initial Lock]].
   intro E;pose proof(V293_put_byte_load(QEinput 1 0 M0)(96%positive,0%Z)254 ltac:(lia))as Final.
   change(load Tint8(QEinput 1 0 M0)(96%positive,0%Z)=Some(V293_byteval 255))in Initial.
   change(V293_put_byte(QEinput 1 0 M0)(96%positive,0%Z)254=QEinput 1 0 M0)in E.
   rewrite E in Final;rewrite Initial in Final;vm_compute in Final;discriminate.
Qed.
