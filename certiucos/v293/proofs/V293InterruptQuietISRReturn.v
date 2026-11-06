(* Preserve unrelated ISR bits through the existing quiet interrupt wrapper. *)
Require Import CertiOS.certiucos.v293.proofs.V293InterruptQuietBuilder.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptBoundQuietContinuous.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptBindings.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyBoundary.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptQuietContinuous.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBoundDynamic.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterOpenExact.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyDynamic.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyStorageInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchState.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitQuietExact.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitUnifiedInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitNondispatch.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyEnter.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyLocal.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyEnvironment.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptSourceRoundtrip.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitch.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStoragePrefix.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia Coq.Logic.FunctionalExtensionality.
Import ListNotations.
Local Open Scope nat_scope.

Lemma V293_irq_builder_lower_clear : forall i ir si aop I R st,
 st|=ipreasrt' i ir si aop I **R ->forall j,j<i ->ir j=false.
Proof.
 intros i ir si aop I R st Held.
 assert(Meta:st|=Aisr(isrupd ir i true) **(Ais(i::si) **Atrue))
 by(unfold ipreasrt' in Held;sep auto).
 apply astar_l_aisr_elim in Meta;destruct Meta as[IRQ Meta].
 apply astar_l_ais_elim in Meta;destruct Meta as[Stack _].
 assert(Flags:st|=isr_inv **Atrue)by(unfold ipreasrt' in Held;sep auto).
 destruct st as[[[[[[ge le] M] irq] [[ie stack] cs]] O] op].
 apply sat_split in Flags;destruct Flags as(m1&m2&o1&o2&JM&JO&Flags&Rest).
 destruct Flags as[r[[ER Empty][k[[Top EmptyTop][Lower EmptyLower]]]]].
 cbn in IRQ,Stack,ER,Top;subst irq stack r.
 unfold gettopis in Top;cbn in Top;subst k.
 intros j Less;specialize(Lower j ltac:(lia)).
 unfold isrupd in Lower.
 assert(E:Nat.eqb i j=false)by(apply Nat.eqb_neq;lia).
 rewrite E in Lower;exact Lower.
Qed.

Lemma V293_irq_eoi_exact : forall ir i,
 isrupd(isrupd ir i true)i false=isrupd ir i false.
Proof.
 intros;apply functional_extensionality;intro j;unfold isrupd;
 destruct(Nat.eqb i j);reflexivity.
Qed.

(* Only the invariant interval being returned must be clear. *)
Lemma V293_irq_noisr_interval_close : forall n low I ge le M ir aux O op,
 (forall j,low<=j<=low+n ->ir j=false) ->
 (ge,le,M,ir,aux,O,op)|=starinv_noisr I low n ->
 (ge,le,M,ir,aux,O,op)|=starinv_isr I low n.
Proof.
 induction n;intros low I ge le M ir aux O op Clear Held.
 - exists ir;right;apply sat_split';exists(emp:mem);exists M;exists(emp:osabst);exists O.
   split;[apply map_join_comm;apply map_join_emp| ];
   split;[apply map_join_comm;apply map_join_emp| ];split;[ |exact Held].
   split;[apply apure_intro;[split;reflexivity|apply Clear;lia]|repeat split;reflexivity].
 - apply sat_split in Held;destruct Held as(m1&m2&o1&o2&JM&JO&First&Tail).
   apply sat_split';exists m1;exists m2;exists o1;exists o2.
   split;[exact JM| ];split;[exact JO| ];split.
   + exists ir;right;apply sat_split';exists(emp:mem);exists m1;exists(emp:osabst);exists o1.
     split;[apply map_join_comm;apply map_join_emp| ];
     split;[apply map_join_comm;apply map_join_emp| ];split;[ |exact First].
     split;[apply apure_intro;[split;reflexivity|apply Clear;lia]|repeat split;reflexivity].
   + apply IHn;[intros j Range;apply Clear;lia|exact Tail].
Qed.

Section PartialReturn.
Variables br bg bp:block.
Variable target:var.
Variable tp:type.
Variable cells:list(addr*type).
Let G:=V293_ready_storage_inv br bg bp target tp cells.
Let Core:=V293_ready_storage_core br bg bp target tp cells.
Lemma V293_irq_ready_partial_return : forall i ir si t lg,
 (forall j,j<i ->ir j=false) ->
 <||spec_done None||> ** OS[isrupd ir i false,false,i::si,nil] **
 (Core **(A_dom_lenv nil **p_local V293_shared_li t lg)) ==>
 iretasrt' i ir si G **p_local V293_shared_li t lg.
Proof.
 intros i ir si t lg Lower st Held.
 destruct st as[[[[[[ge le] M] irq] [[ie stack] cs]] O] op].
 assert(Meta:(ge,le,M,irq,(ie,stack,cs),O,op)|=
 Aisr(isrupd ir i false) **(Ais(i::si) **Atrue))by(sep auto).
 apply astar_l_aisr_elim in Meta;destruct Meta as[IRQ Meta].
 apply astar_l_ais_elim in Meta;destruct Meta as[Stack _].
 cbn in IRQ,Stack;subst irq stack.
 assert(Clear:forall j,j<=i ->isrupd ir i false j=false).
 { intros j Range;unfold isrupd;destruct(Nat.eqb i j)eqn:E;[reflexivity| ].
   apply Nat.eqb_neq in E;apply Lower;lia. }
 assert(Convert:Aisr(isrupd ir i false) **Core ==>invlth_isr G 0 i).
 { intros s H;apply astar_l_aisr_elim in H;destruct H as[EQ H].
   destruct s as[[[[[[ge' le'] M'] ir'] aux'] O'] op'];cbn in EQ;subst ir'.
   unfold invlth_isr;rewrite Nat.sub_0_r.
   apply V293_irq_noisr_interval_close.
   - intros j Range;apply Clear;lia.
   - apply V293_ready_storage_noisr_core;exact H. }
 assert(Flags:(ge,le,(emp:mem),isrupd ir i false,(false,i::si,nil),(emp:osabst),op)|=
 isr_inv //\\ Aie false).
 { split.
   - exists(isrupd ir i false);split;[repeat split;reflexivity| ].
     exists i;split;[repeat split;reflexivity| ].
     apply apure_intro;[split;reflexivity|intros j Range;apply Clear;lia].
   - repeat split;reflexivity. }
 assert(Pack:(ge,le,M,isrupd ir i false,(ie,i::si,cs),O,op)|=
 (Aisr(isrupd ir i false) **Core) **(<||spec_done None||> ** OS[isrupd ir i false,false,i::si,nil] **
 (A_dom_lenv nil **p_local V293_shared_li t lg)))by(sep auto).
 eapply astar_mono in Pack;[ |exact Convert|intros s H;exact H].
 assert(IE:ie=false).
 { assert(X:(ge,le,M,isrupd ir i false,(ie,i::si,cs),O,op)|=Aie false **Atrue)by(sep auto).
   apply astar_l_aie_elim in X;exact(proj1 X). }
 assert(CS:cs=nil).
 { assert(X:(ge,le,M,isrupd ir i false,(ie,i::si,cs),O,op)|=Acs nil **Atrue)by(sep auto).
   apply astar_l_acs_elim in X;exact(proj1 X). }
 subst ie cs.
 assert(WithFlags:(ge,le,M,isrupd ir i false,(false,i::si,nil),O,op)|=
 (isr_inv //\\ Aie false) **
 (invlth_isr G 0 i **(<||spec_done None||> ** OS[isrupd ir i false,false,i::si,nil] **
 (A_dom_lenv nil **p_local V293_shared_li t lg)))).
 { apply sat_split';exists(emp:mem);exists M;exists(emp:osabst);exists O.
   split;[apply map_join_comm;apply map_join_emp| ];
   split;[apply map_join_comm;apply map_join_emp| ];split;assumption. }
 assert(End:Ais(i::si) **invlth_isr G 0 i ==>
 EX ii,EX k,[|hd_error ii=Some k|] **Ais ii **invlth_isr G 0 k).
 { intros s H;exists(i::si);exists i;sep auto. }
 assert(Close:(isr_inv //\\ Aie false) **(Ais(i::si) **invlth_isr G 0 i) ==>IRINV G).
 { intros s H;right;unfold iret_ieoff.
   eapply astar_mono;[intros ss HH;exact HH|exact End|exact H]. }
 assert(PackIR:(ge,le,M,isrupd ir i false,(false,i::si,nil),O,op)|=
 ((isr_inv //\\ Aie false) **(Ais(i::si) **invlth_isr G 0 i)) **
 (<||spec_done None||> ** OS[isrupd ir i false,false,i::si,nil] **
 (A_dom_lenv nil **p_local V293_shared_li t lg)))by(sep auto).
 eapply astar_mono in PackIR;[ |exact Close|intros s H;exact H].
 unfold iretasrt';clear Held Pack Flags WithFlags;sep auto.
Qed.
End PartialReturn.

Section QuietISRReturn.
Variables unmap group rows high table target current counter running nesting lock:var.
Variables bt bg br bh bp bo bc bk brun bn bl:block.
Variable rest:list(addr*type).
Let prefix:=V293_ready_irq_prefix bt bh bc bk.
Let cells:=prefix++[((brun,0%Z),Tint8);((bn,0%Z),Tint8);((bl,0%Z),Tint8)]++rest.
Let Inv0:=V293_ready_dynamic_exit_inv target bt bg br bh bp bc bk brun bn bl rest.
Let li:=V293_irq_bound_li running nesting lock brun bn bl.
Let globals:=V293_quiet_globals running nesting lock brun bn bl.
Let efp:=V293_enter_bound_fpre running nesting lock brun bn bl Aemp Logic.I.
Let efq:=V293_enter_bound_fpost running nesting lock brun bn bl Aemp Logic.I.
Let xfp:=V293_bound_dynamic_fpre unmap group rows high table target current counter running nesting lock
 bt bg br bh bp bo bc bk brun bn bl rest Aemp Logic.I.
Let xfq:=V293_bound_dynamic_fpost unmap group rows high table target current counter running nesting lock
 bt bg br bh bp bo bc bk brun bn bl rest Aemp Logic.I.
Let snapshot:=V293_irq_bound_snapshot target running nesting lock bt bg br bh bp bc bk brun bn bl rest.
Let oldsnapshot:=V293_quiet_irq_snapshot target running nesting lock bt bg br bh bp bc bk brun bn bl rest.
Let filter:=V293_irq_quiet_filter brun bn bl.

Lemma V293_quiet_irq_snapshot_storage : forall run nest locked i ir si t,
 run<256 ->nest<256 ->locked<256 ->
 oldsnapshot run nest locked(spec_done None)false ir(i::si)nil t ==>
 <||spec_done None||> ** OS[ir,false,i::si,nil] **
 (V293_ready_storage_core br bg bp target V293_tcb_type cells **
 (A_dom_lenv nil **p_local V293_shared_li t nil)).
Proof.
 intros run nest locked i ir si t Run Nest Lock s H.
 assert(Globals:V293_quiet_globals running nesting lock brun bn bl ==>Aemp).
 { intros st [G _];apply agvarenv_elim in G;exact(proj2 G). }
 unfold oldsnapshot,V293_quiet_irq_snapshot,V293_enter_open_external,V293_quiet_irq_kept in H.
 eapply astar_mono in H;[ |apply astar_mono;[intros st K;exact K|apply astar_mono;[intros st K;exact K|apply astar_mono;[exact Globals|intros st K;exact K]]]|intros st K;exact K].
 assert(P:s |= (Amapsto(brun,0%Z)Tint8 true(V293_byteval run) **
 (Amapsto(bn,0%Z)Tint8 true(V293_byteval nest) **
 Amapsto(bl,0%Z)Tint8 true(V293_byteval locked))) **
 (<||spec_done None||> ** OS[ir,false,i::si,nil] **
 (p_local V293_shared_li t nil ** (V293ReadyTaskInvariant.V293_ready_core br bg bp **
 (V293_dispatch_cell target V293_tcb_type ** (V293_storage prefix ** (V293_storage rest ** A_dom_lenv nil)))))))by(sep auto).
 eapply astar_mono in P;[ |apply astar_mono;[apply V293_storage_byte_close;exact Run|apply astar_mono;apply V293_storage_byte_close;assumption]|intros st K;exact K].
 assert(P2:s |= (V293_storage prefix ** V293_storage([((brun,0%Z),Tint8);((bn,0%Z),Tint8);((bl,0%Z),Tint8)]++rest)) **
 (<||spec_done None||> ** OS[ir,false,i::si,nil] **
 (p_local V293_shared_li t nil ** (V293ReadyTaskInvariant.V293_ready_core br bg bp **
 (V293_dispatch_cell target V293_tcb_type ** A_dom_lenv nil)))))by(cbn[app V293_storage];clear H;sep auto).
 eapply astar_mono in P2;[ |apply V293_storage_append|intros st K;exact K].
 unfold V293_ready_storage_core,V293_ready_storage_extra,cells;clear H P;sep auto.
Qed.

Lemma V293_bound_quiet_partial_return : forall i ir si t lg run nest locked,
 run<256 ->nest<256 ->locked<256 ->(forall j,j<i ->ir j=false) ->
 snapshot run nest locked(spec_done None)false(isrupd ir i false)(i::si)nil t ==>
 iretasrt' i ir si Inv0 **p_local li t lg.
Proof.
 intros i ir si t lg run nest locked Run Nest Lock Lower st H.
 apply V293_bound_quiet_snapshot_shared in H.
 eapply astar_mono in H;[ |apply V293_quiet_irq_snapshot_storage;assumption|intros s K;exact K].
 eapply astar_mono in H;[ |apply V293_irq_ready_partial_return;exact Lower|intros s K;exact K].
 assert(P:st|=iretasrt' i ir si Inv0 **(p_local V293_shared_li t nil **globals))by(sep auto).
 eapply astar_mono in P;[ |intros s K;exact K|apply V293_irq_bound_local_close];exact P.
Qed.

Theorem V293_interrupt_quiet_partial_snapshot : forall Spec enter exit intspec i ir si t lg ret id run nest locked,
 run<256 ->nest<256 ->locked<256 ->(run=1 ->1<=nest \/ 0<locked) ->
 Spec enter=Some(efp,efq,(Tvoid,nil)) ->Spec exit=Some(xfp,xfq,(Tvoid,nil)) ->
 Some ret=BuildintRet i intspec ir si Inv0 li t lg ->
 (forall j,j<i ->ir j=false) ->(0<=Int.unsigned id<Z.of_nat INUM)%Z ->i=Z.to_nat(Int.unsigned id) ->
 InfRules Spec V293_scheduler li Inv0 arfalse ret
 (snapshot run nest locked(spec_done None)false(isrupd ir i true)(i::si)nil t)
 (V293_irq_source_wrapper enter exit id)Afalse t.
Proof.
 intros Spec enter exit intspec i ir si t lg ret id run nest locked Run Nest Lock Quiet Enter Exit Ret Lower Bound Index.
 assert(Top:gettopis(i::si)<=INUM).
 { unfold gettopis;cbn;rewrite Index;apply Nat.lt_le_incl.
   apply Nat2Z.inj_lt;rewrite Z2Nat.id by lia;lia. }
 unfold V293_irq_source_wrapper.
 eapply seq_rule with(p':=snapshot run nest locked(spec_done None)false
 (isrupd(isrupd ir i true)i false)(i::si)nil t).
 - eapply conseq_rule with
   (p:=<||spec_done None||> ** OS[isrupd ir i true,false,i::si,nil] **
    V293_irq_bound_physical target running nesting lock bt bg br bh bp bc bk brun bn bl rest run nest locked t)
   (q:=<||spec_done None||> ** OS[isrupd(isrupd ir i true)i false,false,i::si,nil] **
    V293_irq_bound_physical target running nesting lock bt bg br bh bp bc bk brun bn bl rest run nest locked t).
   + unfold snapshot,V293_irq_bound_snapshot,V293_enter_bound_external,V293_irq_bound_physical;intros st H;sep auto.
   + unfold snapshot,V293_irq_bound_snapshot,V293_enter_bound_external,V293_irq_bound_physical;intros st H;sep auto.
   + apply eoi_ieoff_rule;[exact Bound|exact Index|apply V293_irq_bound_physical_good].
 - eapply seq_rule with(p':=snapshot run(V293_interrupt_nest_after run nest)locked(spec_done None)false
   (isrupd(isrupd ir i true)i false)(i::si)nil t).
   + unfold snapshot,V293_irq_bound_snapshot;apply(V293_OSIntEnter_bound_call running nesting lock brun bn bl Aemp Logic.I);try assumption.
     split;[apply V293_quiet_irq_kept_good|exact Logic.I].
   + rewrite V293_irq_eoi_exact.
     eapply seq_rule with(p':=snapshot run(V293_exit_quiet_depth run(V293_interrupt_nest_after run nest))locked
     (spec_done None)false(isrupd ir i false)(i::si)nil t).
     * unfold snapshot,V293_irq_bound_snapshot;eapply V293_interrupt_bound_quiet_exit_depth;try eassumption.
       -- apply V293_interrupt_nest_bound;assumption.
       -- apply V293_quiet_pair_valid_saturated;assumption.
       -- split;[apply V293_quiet_irq_kept_good|exact Logic.I].
     * unfold BuildintRet in Ret;destruct(intspec i);[ |discriminate].
       inversion Ret;subst ret;apply iret_rule;apply V293_bound_quiet_partial_return;try assumption.
       apply V293_quiet_pair_final_bound;assumption.
Qed.

Theorem V293_interrupt_quiet_builder_general : forall Spec enter exit intspec i ir si t lg pre ret id,
 intspec i=Some(spec_done None) ->
 Some pre=BuildintPre i intspec ir si Inv0 li t lg ->
 Some ret=BuildintRet i intspec ir si Inv0 li t lg ->
 Spec enter=Some(efp,efq,(Tvoid,nil)) ->Spec exit=Some(xfp,xfq,(Tvoid,nil)) ->
 (0<=Int.unsigned id<Z.of_nat INUM)%Z ->i=Z.to_nat(Int.unsigned id) ->
 InfRules Spec V293_scheduler li Inv0 arfalse ret(pre //\\ filter)
 (V293_irq_source_wrapper enter exit id)Afalse t.
Proof.
 intros Spec enter exit intspec i ir si t lg pre ret id Lookup Pre Ret Enter Exit Bound Index.
 unfold BuildintPre in Pre;rewrite Lookup in Pre;inversion Pre;subst pre.
 eapply conseq_rule with(p:=((ipreasrt' i ir si(spec_done None)Inv0 **p_local li t lg) //\\ filter) **
 [|forall j,j<i ->ir j=false|]).
 - intros st H;apply astar_comm;apply astar_l_apure_intro;[exact H| ].
   apply V293_irq_builder_lower_clear with(si:=si)(aop:=spec_done None)(I:=Inv0)(R:=p_local li t lg)(st:=st);exact(proj1 H).
 - intros st H;exact H.
 - apply pure_split_rule;intro Lower.
   eapply conseq_rule;[apply V293_irq_quiet_builder_open|intros st H;exact H| ].
   apply ex_intro_rule;intro run;apply ex_intro_rule;intro nest;apply ex_intro_rule;intro locked.
   eapply conseq_rule;[intros st H;apply astar_comm;exact H|intros st H;exact H| ].
   apply pure_split_rule;intros[Run[Nest[Lock Quiet]]].
   apply V293_interrupt_quiet_partial_snapshot with(intspec:=intspec)(lg:=lg);assumption.
Qed.
End QuietISRReturn.
