Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitUnifiedInternal.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptSourceRoundtrip.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
(* Conditional quiet composition under one bound LocalInv. *)
Require Import CertiOS.certiucos.v293.proofs.V293InterruptBindings.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBoundDynamic.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitLocalDispatch.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptQuietContinuous.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyBoundary.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyEnter.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterOpenExact.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitQuietExact.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitNondispatch.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterInternal.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyDynamic.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitch.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.sep_combine_lemmas.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope nat_scope.

Section BoundQuietPair.
Variables unmap group rows high table target current counter running nesting lock:var.
Variables bt bg br bh bp bo bc bk brun bn bl:block.
Variable rest:list(addr*type).
Let li:=V293_irq_bound_li running nesting lock brun bn bl.
Let globals:=V293_quiet_globals running nesting lock brun bn bl.
Let Inv0:=V293_ready_dynamic_exit_inv target bt bg br bh bp bc bk brun bn bl rest.
Let efp:=V293_enter_bound_fpre running nesting lock brun bn bl Aemp Logic.I.
Let efq:=V293_enter_bound_fpost running nesting lock brun bn bl Aemp Logic.I.
Let xfp:=V293_bound_dynamic_fpre unmap group rows high table target current counter running nesting lock
 bt bg br bh bp bo bc bk brun bn bl rest Aemp Logic.I.
Let xfq:=V293_bound_dynamic_fpost unmap group rows high table target current counter running nesting lock
 bt bg br bh bp bo bc bk brun bn bl rest Aemp Logic.I.
Let ext:=V293_enter_bound_external running nesting lock brun bn bl Aemp.
Let qext:=V293_quiet_exact_external running nesting lock brun bn bl li Aemp.
Definition V293_bound_quiet_half run:=Amapsto(brun,0%Z)Tint8 false(V293_byteval run).
Lemma V293_bound_quiet_split : forall run nest locked aop enabled ir si ci t callerframe,
 ext run nest locked aop enabled ir si ci t ** callerframe ==>
 qext run nest locked aop enabled ir si ci t ** (V293_bound_quiet_half run ** callerframe).
Proof.
 intros run nest locked aop enabled ir si ci t callerframe;unfold ext,qext,V293_enter_bound_external,V293_quiet_exact_external,
 V293OSIntExitHoare.V293_exit_cells,V293OSIntEnterInternal.V293_interrupt_cells;
 cbn[V293_rdy_raw_cells];intros s H.
 assert(B:s |=globals ** Atrue)by(unfold p_local,LINV,li,V293_irq_bound_li in H;sep auto).
 pose proof(V293_bound_dispatch_add_globals running nesting lock brun bn bl _ _ B H)as Added.
 clear H;rename Added into H.
 assert(P:s |=Amapsto(brun,0%Z)Tint8 true(V293_byteval run) **
 (<||aop||> ** OS[ir,enabled,si,ci] ** (V293_quiet_globals running nesting lock brun bn bl **
 (Amapsto(bn,0%Z)Tint8 true(V293_byteval nest) **
 (Amapsto(bl,0%Z)Tint8 true(V293_byteval locked) **
 (p_local li t nil ** Aemp ** callerframe))))))by(sep auto).
 eapply astar_mono in P;[ |apply separate_rw2ro|intros st K;exact K].
 unfold V293_bound_quiet_half;clear H;sep auto.
Qed.
Lemma V293_bound_quiet_combine : forall run nest locked aop enabled ir si ci t callerframe,
 qext run nest locked aop enabled ir si ci t ** (V293_bound_quiet_half run ** callerframe) ==>
 ext run nest locked aop enabled ir si ci t ** callerframe.
Proof.
 intros run nest locked aop enabled ir si ci t callerframe;unfold ext,qext,V293_enter_bound_external,V293_quiet_exact_external,
 V293OSIntExitHoare.V293_exit_cells,V293OSIntEnterInternal.V293_interrupt_cells,V293_bound_quiet_half;
 cbn[V293_rdy_raw_cells];intros s H.
 assert(P:s |= (Amapsto(brun,0%Z)Tint8 false(V293_byteval run) **
 Amapsto(brun,0%Z)Tint8 false(V293_byteval run)) **
 (<||aop||> ** OS[ir,enabled,si,ci] ** (V293_quiet_globals running nesting lock brun bn bl **
 (Amapsto(bn,0%Z)Tint8 true(V293_byteval nest) **
 (Amapsto(bl,0%Z)Tint8 true(V293_byteval locked) **
 (p_local li t nil ** Aemp ** callerframe))))))by(sep auto).
 eapply astar_mono in P;[ |apply combine_ro2rw_p1|intros st K;exact K].
 assert(F:s |=globals ** (ext run nest locked aop enabled ir si ci t ** callerframe))by(unfold ext,V293_enter_bound_external;sep auto).
 eapply astar_mono in F;[ |apply (V293_irq_bound_empty running nesting lock brun bn bl t nil)|intros st K;exact K].
 unfold ext,V293_enter_bound_external in F;clear H P;sep auto.
Qed.
Theorem V293_interrupt_bound_quiet_exit : forall Spec sd RI r ri exit t run nest locked
 aop enabled ir si ci callerframe,
 run<256 ->nest<256 ->locked<256 ->gettopis si<=INUM ->
 (run=1 ->nest<255) ->(run=1 ->1<=nest \/ 0<locked) ->GoodFrm callerframe ->
 Spec exit=Some(xfp,xfq,(Tvoid,nil)) ->
 InfRules Spec sd li RI r ri
 (ext run(V293_interrupt_nest_after run nest)locked aop enabled ir si ci t ** callerframe)
 (scall exit nil)
 (ext run nest locked aop enabled ir si ci t ** callerframe)t.
Proof.
 intros Spec sd RI r ri exit t run nest locked aop enabled ir si ci callerframe
 Run Nest Lock Top Room Quiet GF Exit.
 set(n:=V293_interrupt_nest_after run nest).
   assert(N:n<256)by(apply V293_interrupt_nest_bound;assumption).
   assert(Q:V293_quiet_exit_valid run n locked si)by(apply V293_quiet_pair_valid;assumption).
   set(lg:=logic_ie false::logic_ie true::V293_quiet_exit_args run n locked aop enabled ir si ci).
   assert(P:getasrt(xfp nil lg t)=[|V293_quiet_exit_valid run n locked si|] ** qext run n locked aop enabled ir si ci t).
   { unfold xfp,lg,V293_bound_dynamic_fpre,V293_exit_path,V293_quiet_exact_exit_fpre,V293_quiet_exact_exit_pre.
     rewrite V293_quiet_exit_roundtrip by assumption;reflexivity. }
   assert(F:forall result,getasrt(xfq nil result lg t)=[|result=None|] **
   qext run(V293_exit_quiet_depth run n)locked aop enabled ir si ci t).
   { intro result;unfold xfq,lg,V293_bound_dynamic_fpost,V293_exit_path,V293_quiet_exact_exit_fpost,V293_quiet_exact_exit_post.
     rewrite V293_quiet_exit_roundtrip by assumption;reflexivity. }
   eapply conseq_rule with(p:=getasrt(xfp nil lg t) ** (V293_bound_quiet_half run ** callerframe))
   (q:=EX result:option val,getasrt(xfq nil result lg t) ** (V293_bound_quiet_half run ** callerframe)).
   + rewrite P;intros s H;apply V293_bound_quiet_split in H;sep auto.
   + intros s[result H];rewrite F in H.
     assert(K:s |=qext run(V293_exit_quiet_depth run n)locked aop enabled ir si ci t **
      (V293_bound_quiet_half run ** callerframe))by(unfold ext,V293_enter_bound_external;sep auto).
     unfold n in K;rewrite V293_quiet_pair_depth in K by assumption.
     apply V293_bound_quiet_combine;exact K.
   + apply V293_OSIntExit_bound_dynamic_call;try assumption.
     unfold V293_bound_quiet_half;split;[exact Logic.I|exact GF].
Qed.
Theorem V293_interrupt_bound_quiet_pair : forall Spec sd RI r ri enter exit t run nest locked
 aop enabled ir si ci callerframe,
 run<256 ->nest<256 ->locked<256 ->gettopis si<=INUM ->
 (run=1 ->nest<255) ->(run=1 ->1<=nest \/ 0<locked) ->GoodFrm callerframe ->
 Spec enter=Some(efp,efq,(Tvoid,nil)) ->Spec exit=Some(xfp,xfq,(Tvoid,nil)) ->
 InfRules Spec sd li RI r ri
 (ext run nest locked aop enabled ir si ci t ** callerframe)
 (sseq(scall enter nil)(scall exit nil))
 (ext run nest locked aop enabled ir si ci t ** callerframe)t.
Proof.
 intros;eapply seq_rule;[apply(V293_OSIntEnter_bound_call running nesting lock brun bn bl Aemp Logic.I);assumption| ].
 apply V293_interrupt_bound_quiet_exit;assumption.
Qed.
End BoundQuietPair.

Section BoundQuietContinuous.
Variables unmap group rows high table target current counter running nesting lock:var.
Variables bt bg br bh bp bo bc bk brun bn bl:block.
Variable rest:list(addr*type).
Let li:=V293_irq_bound_li running nesting lock brun bn bl.
Let globals:=V293_quiet_globals running nesting lock brun bn bl.
Let Inv0:=V293_ready_dynamic_exit_inv target bt bg br bh bp bc bk brun bn bl rest.
Let efp:=V293_enter_bound_fpre running nesting lock brun bn bl Aemp Logic.I.
Let efq:=V293_enter_bound_fpost running nesting lock brun bn bl Aemp Logic.I.
Let xfp:=V293_bound_dynamic_fpre unmap group rows high table target current counter running nesting lock
 bt bg br bh bp bo bc bk brun bn bl rest Aemp Logic.I.
Let xfq:=V293_bound_dynamic_fpost unmap group rows high table target current counter running nesting lock
 bt bg br bh bp bo bc bk brun bn bl rest Aemp Logic.I.
Let snapshot:=V293_irq_bound_snapshot target running nesting lock bt bg br bh bp bc bk brun bn bl rest.
Let oldsnapshot:=V293_quiet_irq_snapshot target running nesting lock bt bg br bh bp bc bk brun bn bl rest.

(* Only assertion resources are rearranged. No derivation changes its LocalInv. *)
Lemma V293_bound_quiet_snapshot_shared : forall run nest locked aop enabled ir si ci t,
 snapshot run nest locked aop enabled ir si ci t ==>
 oldsnapshot run nest locked aop enabled ir si ci t ** globals.
Proof.
 intros run nest locked aop enabled ir si ci t st H.
 unfold snapshot,V293_irq_bound_snapshot,V293_enter_bound_external in H.
 assert(G:st |=globals ** Atrue)by(unfold p_local,LINV,li,V293_irq_bound_li in H;sep auto).
 assert(P:st |=p_local li t nil **
 (<||aop||> ** OS[ir,enabled,si,ci] **
 (Amapsto(brun,0%Z)Tint8 true(V293_byteval run) **
 (Amapsto(bn,0%Z)Tint8 true(V293_byteval nest) **
 (Amapsto(bl,0%Z)Tint8 true(V293_byteval locked) **
 (V293_quiet_irq_kept target bt bg br bh bp bc bk rest ** A_dom_lenv nil))))))by(clear G;unfold li;sep auto).
 eapply astar_mono in P;[ |apply V293_irq_bound_local_open|intros s K;exact K].
 assert(Old:st |=oldsnapshot run nest locked aop enabled ir si ci t).
 { unfold oldsnapshot,V293_quiet_irq_snapshot,V293_enter_open_external;clear H;sep auto. }
 apply astar_comm;apply(V293_bound_dispatch_add_globals running nesting lock brun bn bl _ _ G Old).
Qed.
Lemma V293_bound_quiet_return_resources : forall i ir si t lg run nest locked,
 run<256 ->nest<256 ->locked<256 ->(forall j,ir j=false) ->
 snapshot run nest locked(spec_done None)false(fun _:hid=>false)(i::si)nil t ==>
 iretasrt' i ir si Inv0 ** p_local li t lg.
Proof.
 intros i ir si t lg run nest locked Run Nest Lock Clear st H.
 apply V293_bound_quiet_snapshot_shared in H.
 eapply astar_mono in H;[ |apply V293_quiet_irq_snapshot_close;assumption|intros s K;exact K].
 eapply astar_mono in H;[ |apply V293_irq_ready_return_resources;exact Clear|intros s K;exact K].
 assert(P:st |=iretasrt' i ir si Inv0 ** (p_local V293_shared_li t nil ** globals))by(sep auto).
 eapply astar_mono in P;[ |intros s K;exact K|apply V293_irq_bound_local_close];exact P.
Qed.
Theorem V293_interrupt_bound_quiet_continuous : forall Spec enter exit intspec i ir si t lg ret id run nest locked,
 run<256 ->nest<256 ->locked<256 ->gettopis(i::si)<=INUM ->
 (run=1 ->nest<255) ->(run=1 ->1<=nest \/ 0<locked) ->
 Spec enter=Some(efp,efq,(Tvoid,nil)) ->Spec exit=Some(xfp,xfq,(Tvoid,nil)) ->
 Some ret=BuildintRet i intspec ir si Inv0 li t lg ->
 (forall j,ir j=false) ->(0<=Int.unsigned id<Z.of_nat INUM)%Z ->i=Z.to_nat(Int.unsigned id) ->
 InfRules Spec V293_scheduler li Inv0 arfalse ret
 (snapshot run nest locked(spec_done None)false(isrupd ir i true)(i::si)nil t)
 (V293_irq_source_wrapper enter exit id)Afalse t.
Proof.
 intros Spec enter exit intspec i ir si t lg ret id run nest locked Run Nest Lock Top Room Quiet Enter Exit Ret Clear Bound Index.
 unfold V293_irq_source_wrapper;eapply seq_rule with
 (p':=snapshot run nest locked(spec_done None)false(fun _:hid=>false)(i::si)nil t).
 - eapply conseq_rule with
   (p:=<||spec_done None||> ** OS[isrupd ir i true,false,i::si,nil] **
    V293_irq_bound_physical target running nesting lock bt bg br bh bp bc bk brun bn bl rest run nest locked t)
   (q:=<||spec_done None||> ** OS[isrupd(isrupd ir i true)i false,false,i::si,nil] **
    V293_irq_bound_physical target running nesting lock bt bg br bh bp bc bk brun bn bl rest run nest locked t).
   + unfold snapshot,V293_irq_bound_snapshot,V293_enter_bound_external,V293_irq_bound_physical;intros s H;sep auto.
   + rewrite V293_irq_clear_update by assumption.
     unfold snapshot,V293_irq_bound_snapshot,V293_enter_bound_external,V293_irq_bound_physical;intros s H;sep auto.
   + apply eoi_ieoff_rule;[exact Bound|exact Index|apply V293_irq_bound_physical_good].
 - eapply seq_rule.
   + unfold snapshot,V293_irq_bound_snapshot;apply(V293_OSIntEnter_bound_call running nesting lock brun bn bl Aemp Logic.I);try assumption.
     split;[apply V293_quiet_irq_kept_good|exact Logic.I].
   + eapply seq_rule with(p':=snapshot run nest locked(spec_done None)false(fun _:hid=>false)(i::si)nil t).
     * unfold snapshot,V293_irq_bound_snapshot;apply(V293_interrupt_bound_quiet_exit
       unmap group rows high table target current counter running nesting lock bt bg br bh bp bo bc bk brun bn bl rest);try assumption.
       split;[apply V293_quiet_irq_kept_good|exact Logic.I].
     * unfold BuildintRet in Ret;destruct(intspec i);[ |discriminate].
       inversion Ret;subst ret;apply iret_rule;apply V293_bound_quiet_return_resources;assumption.
Qed.
End BoundQuietContinuous.
