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

Section EntryControl.
Variables target running nesting lock:var.
Variables bt bg br bh bp bc bk brun bn bl:block.
Variable rest:list(addr*type).
Let prefix:=V293_ready_irq_prefix bt bh bc bk.
Let cells:=prefix++[((brun,0%Z),Tint8);((bn,0%Z),Tint8);((bl,0%Z),Tint8)]++rest.
Let Inv0:=V293_ready_dynamic_exit_inv target bt bg br bh bp bc bk brun bn bl rest.
Let globals:=V293_quiet_globals running nesting lock brun bn bl.
Let snapshot:=V293_quiet_irq_snapshot target running nesting lock bt bg br bh bp bc bk brun bn bl rest.
Let physical:=V293_quiet_irq_physical target running nesting lock bt bg br bh bp bc bk brun bn bl rest.
Let efp:=V293_enter_open_fpre running nesting lock brun bn bl Aemp Logic.I.
Let efq:=V293_enter_open_fpost running nesting lock brun bn bl Aemp Logic.I.

Lemma V293_irq_entry_controls_open :
 V293_storage ([((brun,0%Z),Tint8);((bn,0%Z),Tint8);((bl,0%Z),Tint8)]) ==>
 EX run,EX nest,EX locked,[|run<256 /\ nest<256 /\ locked<256|] **
 (Amapsto(brun,0%Z)Tint8 true(V293_byteval run) **
 (Amapsto(bn,0%Z)Tint8 true(V293_byteval nest) **
 Amapsto(bl,0%Z)Tint8 true(V293_byteval locked))).
Proof.
 intros st H;cbn[V293_storage]in H.
 eapply astar_mono in H;[ |apply V293_storage_byte_open|intros s K;exact K].
 sep normal in H;sep destruct H.
 assert(K:st |= V293_storage_cell(bn,0%Z)Tint8 **
 ([|x<256|] ** Amapsto(brun,0%Z)Tint8 true(V293_byteval x) **
 (V293_storage_cell(bl,0%Z)Tint8 ** Aemp)))by(sep auto).
 eapply astar_mono in K;[ |apply V293_storage_byte_open|intros s T;exact T].
 sep normal in K;sep destruct K.
 assert(K2:st |= V293_storage_cell(bl,0%Z)Tint8 **
 ([|x<256|] ** [|x0<256|] ** Amapsto(brun,0%Z)Tint8 true(V293_byteval x) **
 (Amapsto(bn,0%Z)Tint8 true(V293_byteval x0) ** Aemp)))by(clear H;sep auto).
 eapply astar_mono in K2;[ |apply V293_storage_byte_open|intros s T;exact T].
 sep normal in K2;sep destruct K2.
 exists x;exists x0;exists x1;clear H K;sep auto.
Qed.

Theorem V293_irq_entry_builder_open : forall i ir si aop t lg,
 (ipreasrt' i ir si aop Inv0 ** p_local V293_shared_li t lg) ** globals ==>
 EX run,EX nest,EX locked,[|run<256 /\ nest<256 /\ locked<256|] **
 snapshot run nest locked aop false(isrupd ir i true)(i::si)nil t.
Proof.
 intros i ir si aop t lg st H.
 assert(B:st |= (ipreasrt' i ir si aop Inv0 ** p_local V293_shared_li t lg) ** globals)by exact H.
 change Inv0 with(V293_ready_storage_inv br bg bp target V293_tcb_type cells)in B.
 eapply astar_mono in B;[ |apply V293_irq_ready_builder_resources|intros s K;exact K].
 unfold V293_irq_ready_frame,V293_ready_storage_core,V293_ready_storage_extra in B.
 assert(K:st |= V293_storage cells **
 (<||aop||> ** OS[isrupd ir i true,false,i::si,nil] **
 (V293ReadyTaskInvariant.V293_ready_core br bg bp ** V293_dispatch_cell target V293_tcb_type **
 (A_dom_lenv nil ** p_local V293_shared_li t lg ** globals))))by(sep auto).
 unfold cells in K;eapply astar_mono in K;[ |apply V293_storage_split|intros s T;exact T].
 assert(K2:st |= V293_storage([((brun,0%Z),Tint8);((bn,0%Z),Tint8);((bl,0%Z),Tint8)]++rest) **
 (<||aop||> ** OS[isrupd ir i true,false,i::si,nil] **
 (V293ReadyTaskInvariant.V293_ready_core br bg bp ** V293_dispatch_cell target V293_tcb_type **
 (A_dom_lenv nil ** p_local V293_shared_li t lg ** globals ** V293_storage prefix))))by(clear H B;sep auto).
 eapply astar_mono in K2;[ |apply V293_storage_split|intros s T;exact T].
 eapply astar_mono in K2;[ |apply astar_mono;[apply V293_irq_entry_controls_open|intros s T;exact T]|intros s T;exact T].
 sep normal in K2;sep destruct K2.
 exists x;exists x0;exists x1.
 unfold snapshot,V293_quiet_irq_snapshot,V293_enter_open_external,V293_quiet_irq_kept.
 rewrite V293_local_witness_identity in K2.
 clear H B K;sep auto.
Qed.

Lemma V293_irq_entry_prefix_exact : forall Spec sd r ri enter i ir si aop t id run nest locked,
 run<256 ->nest<256 ->locked<256 ->
 Spec enter=Some(efp,efq,(Tvoid,nil)) ->
 (forall j,ir j=false) ->(0<=Int.unsigned id<Z.of_nat INUM)%Z ->i=Z.to_nat(Int.unsigned id) ->
 InfRules Spec sd V293_shared_li Inv0 r ri
 (snapshot run nest locked aop false(isrupd ir i true)(i::si)nil t)
 (sseq(sprim(eoi id))(scall enter nil))
 (snapshot run(V293_interrupt_nest_after run nest)locked aop false(fun _:hid=>false)(i::si)nil t)t.
Proof.
 intros Spec sd r ri enter i ir si aop t id run nest locked Run Nest Lock Enter Clear Bound Index.
 eapply seq_rule with(p':=snapshot run nest locked aop false(fun _:hid=>false)(i::si)nil t).
 - eapply conseq_rule with
   (p:=<||aop||> ** OS[isrupd ir i true,false,i::si,nil] ** physical run nest locked t)
   (q:=<||aop||> ** OS[isrupd(isrupd ir i true)i false,false,i::si,nil] ** physical run nest locked t).
   + unfold snapshot,V293_quiet_irq_snapshot,V293_enter_open_external,physical,V293_quiet_irq_physical;intros s H;sep auto.
   + rewrite V293_irq_clear_update by assumption.
     unfold snapshot,V293_quiet_irq_snapshot,V293_enter_open_external,physical,V293_quiet_irq_physical;intros s H;sep auto.
   + apply eoi_ieoff_rule;[exact Bound|exact Index|apply V293_quiet_irq_physical_good].
 - unfold snapshot,V293_quiet_irq_snapshot;apply(V293_OSIntEnter_open_call running nesting lock brun bn bl Aemp Logic.I);try assumption.
   split;[apply V293_quiet_irq_kept_good|exact Logic.I].
Qed.

Definition V293_irq_entry_after_enter i si aop t :=
 EX run,EX oldnest,EX locked,[|run<256 /\ oldnest<256 /\ locked<256|] **
 snapshot run(V293_interrupt_nest_after run oldnest)locked aop false(fun _:hid=>false)(i::si)nil t.

Theorem V293_interrupt_entry_control : forall Spec sd r ri enter intspec i ir si aop t lg pre id,
 intspec i=Some aop ->Some pre=BuildintPre i intspec ir si Inv0 V293_shared_li t lg ->
 Spec enter=Some(efp,efq,(Tvoid,nil)) ->
 (forall j,ir j=false) ->(0<=Int.unsigned id<Z.of_nat INUM)%Z ->i=Z.to_nat(Int.unsigned id) ->
 InfRules Spec sd V293_shared_li Inv0 r ri (pre ** globals)
 (sseq(sprim(eoi id))(scall enter nil))(V293_irq_entry_after_enter i si aop t)t.
Proof.
 intros Spec sd r ri enter intspec i ir si aop t lg pre id Lookup Pre Enter Clear Bound Index.
 unfold BuildintPre in Pre;rewrite Lookup in Pre;inversion Pre;subst pre.
 eapply conseq_rule;[apply V293_irq_entry_builder_open|intros s H;exact H| ].
 apply ex_intro_rule;intro run;apply ex_intro_rule;intro nest;apply ex_intro_rule;intro locked.
 eapply conseq_rule;[intros s H;apply astar_comm;exact H|intros s H;exact H| ].
 apply pure_split_rule;intros[Run [Nest Lock]].
 eapply conseq_rule;[intros s H;exact H| |eapply V293_irq_entry_prefix_exact;try eassumption].
 intros s H;unfold V293_irq_entry_after_enter;exists run;exists nest;exists locked;sep auto.
Qed.
End EntryControl.
