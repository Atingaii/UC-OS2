(* Open the actual interrupt builder without guessing any control byte. *)
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptQuietContinuous.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyBoundary.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyEnvironment.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyEnter.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyLocal.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterOpenExact.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitQuietExact.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitUnifiedInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitch.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyDynamic.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyStorageInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchState.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Require Import CertiOS.certiucos.v293.proofs.V293InterruptEntryControl.
Section EntryGeneral.
Variables target running nesting lock:var.
Variables bt bg br bh bp bc bk brun bn bl:block.
Variable rest:list(addr*type).
Let Inv0:=V293_ready_dynamic_exit_inv target bt bg br bh bp bc bk brun bn bl rest.
Let globals:=V293_quiet_globals running nesting lock brun bn bl.
Let snapshot:=V293_quiet_irq_snapshot target running nesting lock bt bg br bh bp bc bk brun bn bl rest.
Let physical:=V293_quiet_irq_physical target running nesting lock bt bg br bh bp bc bk brun bn bl rest.
Let efp:=V293_enter_open_fpre running nesting lock brun bn bl Aemp Logic.I.
Let efq:=V293_enter_open_fpost running nesting lock brun bn bl Aemp Logic.I.

(* The previously active ISR bits need not be clear. *)
Lemma V293_irq_entry_prefix_general : forall Spec sd r ri enter i ir si aop t id run nest locked,
 run<256 ->nest<256 ->locked<256 ->
 Spec enter=Some(efp,efq,(Tvoid,nil)) ->
 (0<=Int.unsigned id<Z.of_nat INUM)%Z ->i=Z.to_nat(Int.unsigned id) ->
 InfRules Spec sd V293_shared_li Inv0 r ri
 (snapshot run nest locked aop false(isrupd ir i true)(i::si)nil t)
 (sseq(sprim(eoi id))(scall enter nil))
 (snapshot run(V293_interrupt_nest_after run nest)locked aop false
 (isrupd(isrupd ir i true)i false)(i::si)nil t)t.
Proof.
 intros Spec sd r ri enter i ir si aop t id run nest locked Run Nest Lock Enter Bound Index.
 eapply seq_rule with(p':=snapshot run nest locked aop false
 (isrupd(isrupd ir i true)i false)(i::si)nil t).
 - eapply conseq_rule with
   (p:=<||aop||> ** OS[isrupd ir i true,false,i::si,nil] ** physical run nest locked t)
   (q:=<||aop||> ** OS[isrupd(isrupd ir i true)i false,false,i::si,nil] ** physical run nest locked t).
   + unfold snapshot,V293_quiet_irq_snapshot,V293_enter_open_external,physical,V293_quiet_irq_physical;intros s H;sep auto.
   + unfold snapshot,V293_quiet_irq_snapshot,V293_enter_open_external,physical,V293_quiet_irq_physical;intros s H;sep auto.
   + apply eoi_ieoff_rule;[exact Bound|exact Index|apply V293_quiet_irq_physical_good].
 - unfold snapshot,V293_quiet_irq_snapshot;apply(V293_OSIntEnter_open_call running nesting lock brun bn bl Aemp Logic.I);try assumption.
   split;[apply V293_quiet_irq_kept_good|exact Logic.I].
Qed.

Definition V293_irq_entry_general_after i ir si aop t :=
 EX run,EX oldnest,EX locked,[|run<256 /\ oldnest<256 /\ locked<256|] **
 snapshot run(V293_interrupt_nest_after run oldnest)locked aop false
 (isrupd(isrupd ir i true)i false)(i::si)nil t.

Theorem V293_interrupt_entry_general : forall Spec sd r ri enter intspec i ir si aop t lg pre id,
 intspec i=Some aop ->Some pre=BuildintPre i intspec ir si Inv0 V293_shared_li t lg ->
 Spec enter=Some(efp,efq,(Tvoid,nil)) ->
 (0<=Int.unsigned id<Z.of_nat INUM)%Z ->i=Z.to_nat(Int.unsigned id) ->
 InfRules Spec sd V293_shared_li Inv0 r ri (pre ** globals)
 (sseq(sprim(eoi id))(scall enter nil))(V293_irq_entry_general_after i ir si aop t)t.
Proof.
 intros Spec sd r ri enter intspec i ir si aop t lg pre id Lookup Pre Enter Bound Index.
 unfold BuildintPre in Pre;rewrite Lookup in Pre;inversion Pre;subst pre.
 eapply conseq_rule;[apply V293_irq_entry_builder_open|intros s H;exact H| ].
 apply ex_intro_rule;intro run;apply ex_intro_rule;intro nest;apply ex_intro_rule;intro locked.
 eapply conseq_rule;[intros s H;apply astar_comm;exact H|intros s H;exact H| ].
 apply pure_split_rule;intros[Run [Nest Lock]].
 eapply conseq_rule;[intros s H;exact H| |eapply V293_irq_entry_prefix_general;try eassumption].
 intros s H;unfold V293_irq_entry_general_after;exists run;exists nest;exists locked;sep auto.
Qed.
End EntryGeneral.

(* A precise limitation of this framework's stack-insensitive Inv closure.
   This does not exclude a heap-only nesting bound or reachable-state relation. *)
Theorem V293_irq_inv_depth_relation_empty_at_clear : forall p (depth:mem->nat),
 assertion.inv_isr_prop p ->
 (forall st,st |= p ->depth(getmem st)=length(get_is_s st)) ->
 forall st,get_isr_s st=empisr ->~st |= p.
Proof.
 intros p depth [_ [_ [_ Reset]]] Rel st Clear Held.
 pose proof(Reset st nil Held Clear)as EmptyStack.
 pose proof(Reset st [0] Held Clear)as OneStack.
 specialize(Rel _ EmptyStack)as Zero.
 specialize(Rel _ OneStack)as One.
 destruct st as [[[[[[ge le] M] ir] [[ie si] cs]] O] op].
 cbn[set_is_s getmem get_is_s]in Zero,One;cbn in Zero,One;lia.
Qed.
