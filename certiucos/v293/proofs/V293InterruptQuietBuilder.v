(* Quiet entries are filtered on the builder's own heap, without extra cells. *)
Require Import CertiOS.certiucos.v293.proofs.V293InterruptBoundQuietContinuous.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptBindings.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBoundDynamic.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitUnifiedInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitNondispatch.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterOpenExact.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitQuietExact.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyDynamic.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptQuietContinuous.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyEnter.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyBoundary.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptSourceRoundtrip.
Require Import CertiOS.certiucos.v293.proofs.V293TCBJointShared.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitch.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

(* Unlike an exact restoration postcondition, the quiet exit condition needs
   no room at 255. The resulting depth is kept, not rewritten to the old one. *)
Lemma V293_quiet_pair_valid_saturated : forall run nest locked si,
 run<256 ->nest<256 ->locked<256 ->gettopis si<=INUM ->
 (run=1 ->1<=nest \/ 0<locked) ->
 V293_quiet_exit_valid run(V293_interrupt_nest_after run nest)locked si.
Proof.
 intros run nest locked si Run Nest Lock Top Quiet.
 unfold V293_quiet_exit_valid;repeat split;try assumption.
 - apply V293_interrupt_nest_bound;assumption.
 - intro E;subst run;specialize(Quiet eq_refl).
   unfold V293_interrupt_nest_after;change(2<=(if Nat.ltb nest 255 then S nest else nest) \/ 0<locked).
   destruct(Nat.ltb nest 255)eqn:N;[ |apply Nat.ltb_ge in N];lia.
Qed.
Lemma V293_quiet_pair_final_bound : forall run nest,
 run<256 ->nest<256 ->
 V293_exit_quiet_depth run(V293_interrupt_nest_after run nest)<256.
Proof.
 intros run nest Run Nest;pose proof(V293_interrupt_nest_bound run nest Nest)as N.
 unfold V293_exit_quiet_depth,V293_exit_depth;destruct(Nat.eqb run 1);lia.
Qed.

Section QuietControls.
Variables brun bn bl:block.
Definition V293_irq_controls run nest locked :=
 Amapsto(brun,0%Z)Tint8 true(V293_byteval run) **
 (Amapsto(bn,0%Z)Tint8 true(V293_byteval nest) **
 (Amapsto(bl,0%Z)Tint8 true(V293_byteval locked) ** Atrue)).
Definition V293_irq_quiet_filter :=
 EX run,EX nest,EX locked,
 [|run<256 /\ nest<256 /\ locked<256 /\ (run=1 ->1<=nest \/ 0<locked)|] **
 V293_irq_controls run nest locked.
Lemma V293_irq_controls_load : forall run nest locked st,
 run<256 ->nest<256 ->locked<256 ->st|=V293_irq_controls run nest locked ->
 load Tint8(getmem st)(brun,0%Z)=Some(V293_byteval run) /\
 load Tint8(getmem st)(bn,0%Z)=Some(V293_byteval nest) /\
 load Tint8(getmem st)(bl,0%Z)=Some(V293_byteval locked).
Proof.
 intros run nest locked st Run Nest Lock H.
 assert(L:forall b n,n<256 ->st|=Amapsto(b,0%Z)Tint8 true(V293_byteval n) ** Atrue ->
 load Tint8(getmem st)(b,0%Z)=Some(V293_byteval n)).
 { intros b n Bound Held;eapply V293_star_load_l;[ |exact Held].
   intros s[Map _];eapply mapstoval_load;[apply V293_byte_type;exact Bound|exact Map]. }
 unfold V293_irq_controls in H;repeat split;apply L;try assumption;sep auto.
Qed.
Lemma V293_irq_controls_unique : forall run nest locked run' nest' locked' st,
 run<256 ->nest<256 ->locked<256 ->run'<256 ->nest'<256 ->locked'<256 ->
 st|=V293_irq_controls run nest locked ->st|=V293_irq_controls run' nest' locked' ->
 run=run' /\ nest=nest' /\ locked=locked'.
Proof.
 intros run nest locked run' nest' locked' st R N L R' N' L' H H'.
 pose proof(V293_irq_controls_load _ _ _ _ R N L H)as[LR[LN LL]].
 pose proof(V293_irq_controls_load _ _ _ _ R' N' L' H')as[LR'[LN' LL']].
 repeat split;eapply V293_byteval_injective_bounded;try eassumption;congruence.
Qed.
End QuietControls.

Section QuietBuilder.
Variables unmap group rows high table target current counter running nesting lock:var.
Variables bt bg br bh bp bo bc bk brun bn bl:block.
Variable rest:list(addr*type).
Let li:=V293_irq_bound_li running nesting lock brun bn bl.
Let Inv0:=V293_ready_dynamic_exit_inv target bt bg br bh bp bc bk brun bn bl rest.
Let efp:=V293_enter_bound_fpre running nesting lock brun bn bl Aemp Logic.I.
Let efq:=V293_enter_bound_fpost running nesting lock brun bn bl Aemp Logic.I.
Let xfp:=V293_bound_dynamic_fpre unmap group rows high table target current counter running nesting lock
 bt bg br bh bp bo bc bk brun bn bl rest Aemp Logic.I.
Let xfq:=V293_bound_dynamic_fpost unmap group rows high table target current counter running nesting lock
 bt bg br bh bp bo bc bk brun bn bl rest Aemp Logic.I.
Let ext:=V293_enter_bound_external running nesting lock brun bn bl Aemp.
Let qext:=V293_quiet_exact_external running nesting lock brun bn bl li Aemp.
Let snapshot:=V293_irq_bound_snapshot target running nesting lock bt bg br bh bp bc bk brun bn bl rest.
Let filter:=V293_irq_quiet_filter brun bn bl.
Let controls:=V293_irq_controls brun bn bl.
Lemma V293_irq_bound_snapshot_controls : forall run nest locked aop enabled ir si ci t,
 snapshot run nest locked aop enabled ir si ci t ==>controls run nest locked.
Proof.
 intros run nest locked aop enabled ir si ci t st H;
 unfold snapshot,V293_irq_bound_snapshot,V293_enter_bound_external,controls,V293_irq_controls in *;sep auto.
Qed.
Theorem V293_irq_quiet_builder_open : forall i ir si aop t lg,
 ((ipreasrt' i ir si aop Inv0 **p_local li t lg) //\\ filter) ==>
 EX run,EX nest,EX locked,
 [|run<256 /\ nest<256 /\ locked<256 /\ (run=1 ->1<=nest \/ 0<locked)|] **
 snapshot run nest locked aop false(isrupd ir i true)(i::si)nil t.
Proof.
 intros i ir si aop t lg st[Builder Filter].
 apply V293_irq_bound_builder_open in Builder.
 destruct Builder as[run[nest[locked Builder]]].
 apply astar_l_apure_elim in Builder;destruct Builder as[[Run[Nest Lock]]Held].
 destruct Filter as[run'[nest'[locked' Filter]]].
 apply astar_l_apure_elim in Filter;destruct Filter as[[Run'[Nest'[Lock' Quiet]]]Filtered].
 pose proof(V293_irq_bound_snapshot_controls _ _ _ _ _ _ _ _ _ _ Held)as Controls.
 destruct(V293_irq_controls_unique brun bn bl run nest locked run' nest' locked' st
 Run Nest Lock Run' Nest' Lock' Controls Filtered)as[ER[EN EL]].
 subst run' nest' locked';exists run;exists nest;exists locked;sep auto.
Qed.

(* One call in the existing three-function specification, with its exact
   calculated depth. Both read halves are recombined before returning. *)
Theorem V293_interrupt_bound_quiet_exit_depth : forall Spec sd RI r ri exit t run nest locked
 aop enabled ir si ci callerframe,
 run<256 ->nest<256 ->locked<256 ->V293_quiet_exit_valid run nest locked si ->
 GoodFrm callerframe ->Spec exit=Some(xfp,xfq,(Tvoid,nil)) ->
 InfRules Spec sd li RI r ri
 (ext run nest locked aop enabled ir si ci t ** callerframe)(scall exit nil)
 (ext run(V293_exit_quiet_depth run nest)locked aop enabled ir si ci t ** callerframe)t.
Proof.
 intros Spec sd RI r ri exit t run nest locked aop enabled ir si ci callerframe
 Run Nest Lock Quiet GF Exit.
 set(lg:=logic_ie false::logic_ie true::V293_quiet_exit_args run nest locked aop enabled ir si ci).
 assert(P:getasrt(xfp nil lg t)=[|V293_quiet_exit_valid run nest locked si|] ** qext run nest locked aop enabled ir si ci t).
 { unfold xfp,lg,V293_bound_dynamic_fpre,V293_exit_path,V293_quiet_exact_exit_fpre,V293_quiet_exact_exit_pre.
   rewrite V293_quiet_exit_roundtrip by assumption;reflexivity. }
 assert(F:forall result,getasrt(xfq nil result lg t)=[|result=None|] **
 qext run(V293_exit_quiet_depth run nest)locked aop enabled ir si ci t).
 { intro result;unfold xfq,lg,V293_bound_dynamic_fpost,V293_exit_path,V293_quiet_exact_exit_fpost,V293_quiet_exact_exit_post.
   rewrite V293_quiet_exit_roundtrip by assumption;reflexivity. }
 eapply conseq_rule with(p:=getasrt(xfp nil lg t) ** (V293_bound_quiet_half brun run ** callerframe))
 (q:=EX result:option val,getasrt(xfq nil result lg t) ** (V293_bound_quiet_half brun run ** callerframe)).
 - rewrite P;intros st H;apply V293_bound_quiet_split in H;sep auto.
 - intros st[result H];rewrite F in H.
   apply V293_bound_quiet_combine;unfold qext in H;sep auto.
 - apply V293_OSIntExit_bound_dynamic_call;try assumption.
   unfold V293_bound_quiet_half;split;[exact Logic.I|exact GF].
Qed.
Theorem V293_interrupt_bound_quiet_snapshot_depth : forall Spec enter exit intspec i ir si t lg ret id run nest locked,
 run<256 ->nest<256 ->locked<256 ->gettopis(i::si)<=INUM ->
 (run=1 ->1<=nest \/ 0<locked) ->
 Spec enter=Some(efp,efq,(Tvoid,nil)) ->Spec exit=Some(xfp,xfq,(Tvoid,nil)) ->
 Some ret=BuildintRet i intspec ir si Inv0 li t lg ->
 (forall j,ir j=false) ->(0<=Int.unsigned id<Z.of_nat INUM)%Z ->i=Z.to_nat(Int.unsigned id) ->
 InfRules Spec V293_scheduler li Inv0 arfalse ret
 (snapshot run nest locked(spec_done None)false(isrupd ir i true)(i::si)nil t)
 (V293_irq_source_wrapper enter exit id)Afalse t.
Proof.
 intros Spec enter exit intspec i ir si t lg ret id run nest locked Run Nest Lock Top Quiet Enter Exit Ret Clear Bound Index.
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
   + rewrite V293_irq_clear_update by assumption.
     eapply seq_rule with(p':=snapshot run(V293_exit_quiet_depth run(V293_interrupt_nest_after run nest))locked
     (spec_done None)false(fun _:hid=>false)(i::si)nil t).
     * unfold snapshot,V293_irq_bound_snapshot;apply V293_interrupt_bound_quiet_exit_depth;try assumption.
       -- apply V293_interrupt_nest_bound;assumption.
       -- apply V293_quiet_pair_valid_saturated;assumption.
       -- split;[apply V293_quiet_irq_kept_good|exact Logic.I].
     * unfold BuildintRet in Ret;destruct(intspec i);[ |discriminate].
       inversion Ret;subst ret;apply iret_rule;apply V293_bound_quiet_return_resources;try assumption.
       apply V293_quiet_pair_final_bound;assumption.
Qed.

(* This is the actual builder intersected with a same-state byte observation.
   No caller-supplied ready/TCB snapshot or execution of the middle is needed. *)
Theorem V293_interrupt_quiet_builder_continuous : forall Spec enter exit intspec i ir si t lg pre ret id,
 intspec i=Some(spec_done None) ->
 Some pre=BuildintPre i intspec ir si Inv0 li t lg ->
 Some ret=BuildintRet i intspec ir si Inv0 li t lg ->
 Spec enter=Some(efp,efq,(Tvoid,nil)) ->Spec exit=Some(xfp,xfq,(Tvoid,nil)) ->
 gettopis(i::si)<=INUM ->(forall j,ir j=false) ->
 (0<=Int.unsigned id<Z.of_nat INUM)%Z ->i=Z.to_nat(Int.unsigned id) ->
 InfRules Spec V293_scheduler li Inv0 arfalse ret(pre //\\ filter)
 (V293_irq_source_wrapper enter exit id)Afalse t.
Proof.
 intros Spec enter exit intspec i ir si t lg pre ret id Lookup Pre Ret Enter Exit Top Clear Bound Index.
 unfold BuildintPre in Pre;rewrite Lookup in Pre;inversion Pre;subst pre.
 eapply conseq_rule;[apply V293_irq_quiet_builder_open|intros st H;exact H| ].
 apply ex_intro_rule;intro run;apply ex_intro_rule;intro nest;apply ex_intro_rule;intro locked.
 eapply conseq_rule;[intros st H;apply astar_comm;exact H|intros st H;exact H| ].
 apply pure_split_rule;intros[Run[Nest[Lock Quiet]]].
 apply V293_interrupt_bound_quiet_snapshot_depth with(intspec:=intspec)(lg:=lg);assumption.
Qed.
End QuietBuilder.
