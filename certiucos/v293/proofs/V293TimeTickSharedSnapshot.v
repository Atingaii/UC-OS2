(* Runtime shared snapshots use existing logical arguments, not a new invariant. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickBodyHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickReturnTail.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickHookContract.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.soundness.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope nat_scope.

Require Import CertiOS.certiucos.v293.proofs.V293TimeTickCallContext.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickScanSlot.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickPostHookHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickSwitchBoundary.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickPostHookCore.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickChainOpen.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCritical.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293TimeReadyShared.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickSuffix.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLoop.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickWhileRecords.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.code.V293OSTimeTick.

Local Open Scope nat_scope.

Require Import CertiOS.certiucos.v293.proofs.V293TimeTickBuilderLocals.
Local Open Scope nat_scope.

Require Import CertiOS.certiucos.v293.proofs.V293TimeTickUniformSpec.
Require Import Coq.Bool.Bool.
Require Import CertiOS.framework.proof.auxdef.
Local Open Scope nat_scope.

Definition V293_tick_shared_index (lg:list logicvar)
 : option (int * nat * tid * EcbMod.map * is * cs) :=
 match lg with
 | [logic_val(Vint32 clock);logic_val(Vint32 running);logic_val(Vptr ct);
    logic_absecb es;logic_is si;logic_cs ci] =>
    Some(clock,Z.to_nat(Int.unsigned running),ct,es,si,ci)
 | _ => None
 end.
Definition V293_tick_shared_logic clock running ct es si ci :=
 [logic_val(Vint32 clock);logic_val(Vint32 running);logic_val(Vptr ct);
  logic_absecb es;logic_is si;logic_cs ci].
Definition V293_tick_shared_guard run ct si tid :=
 if tid_eq_dec ct tid then andb(Nat.ltb run 256)(Nat.leb(gettopis si)INUM) else false.
Lemma V293_tick_shared_guard_valid : forall run ct si tid,
 V293_tick_shared_guard run ct si tid=true <->
 ct=tid /\ run<256 /\ gettopis si<=INUM.
Proof.
 intros;unfold V293_tick_shared_guard;destruct(tid_eq_dec ct tid)as[Same|Different].
 - rewrite andb_true_iff,Nat.ltb_lt,Nat.leb_le;intuition.
 - split;[discriminate|intros[E _];contradiction].
Qed.
Section SharedSnapshot.
Variables(bindings:list(V293_tick_task*(taskstatus*val)))(idle:addrval)(message:val)
 (br bg bp bn bu bh:block)(R:asrt).
Let ir:isr:=fun _=>false.
Definition V293_tick_shared_resource lg :=
 match V293_tick_shared_index lg with
 | Some(clock,run,ct,es,si,ci) => V293_tick_builder_resource bindings idle message ct es br bg bp bn bu bh run R clock ir si ci
 | None => Afalse
 end.
Lemma V293_tick_shared_resource_good : forall lg,
 GoodFunAsrt R -> GoodFunAsrt(V293_tick_shared_resource lg).
Proof.
 intros lg Good;unfold V293_tick_shared_resource.
 destruct(V293_tick_shared_index lg)as[[[[[[clock run]ct]es]si]ci]| ];[apply V293_tick_builder_resource_good;exact Good|exact I].
Qed.
Definition V293_tick_shared_hook_pre (Good:GoodFunAsrt R) : fpre :=
 fun vl lg tid => @mkfunasrt ([|vl=[]|] ** V293_tick_shared_resource lg)
 (conj I (V293_tick_shared_resource_good lg Good)).
Definition V293_tick_shared_hook_post (Good:GoodFunAsrt R) : fpost :=
 fun vl result lg tid => @mkfunasrt ([|vl=[] /\ result=None|] ** V293_tick_shared_resource lg)
 (conj I (V293_tick_shared_resource_good lg Good)).

Lemma V293_tick_shared_hook_call : forall Spec sd li I r ri tid hook caller lg clock run ct es si ci
 (Good:GoodFunAsrt R),
 V293_tick_shared_index lg=Some(clock,run,ct,es,si,ci) ->
 GoodFrm caller ->
 (V293_tick_builder_resource bindings idle message ct es br bg bp bn bu bh run R clock ir si ci ==> CurLINV li tid) ->
 Spec hook=Some(V293_tick_shared_hook_pre Good,V293_tick_shared_hook_post Good,(Tvoid,[])) ->
 InfRules Spec sd li I r ri
 (V293_tick_builder_resource bindings idle message ct es br bg bp bn bu bh run R clock ir si ci ** caller)
 (scall hook[])
 (V293_tick_builder_resource bindings idle message ct es br bg bp bn bu bh run R clock ir si ci ** caller)tid.
Proof.
 intros Spec sd li I r ri tid hook caller lg clock run ct es si ci Good Decode Frame Local Lookup.
 eapply conseq_rule with(q:=EX result:option val,
 getasrt(V293_tick_shared_hook_post Good [] result lg tid) ** caller).
 - intros s H;exact H.
 - intros s[result H];cbn[V293_tick_shared_hook_post getasrt]in H.
   unfold V293_tick_shared_resource in H;rewrite Decode in H;clear -H;sep auto.
 - eapply call_rule with(pre:=V293_tick_shared_hook_pre Good)
   (post:=V293_tick_shared_hook_post Good)(vl:=[])(logicl:=lg)
   (tp:=Tvoid)(tl:=[])(p:=caller).
   + exact Frame.
   + exact Lookup.
   + intros s H;cbn[V293_tick_shared_hook_pre getasrt];unfold V293_tick_shared_resource;
     rewrite Decode;clear -H;sep auto.
   + intros s H;destruct s as [[[[[[ge le] M] irq] aux] O] op];cbn;repeat split;reflexivity.
   + reflexivity.
   + cbn[V293_tick_shared_hook_pre getasrt];unfold V293_tick_shared_resource;rewrite Decode.
     apply V293_star_CurLINV_r;exact Local.
   + intros s[result H];cbn[V293_tick_shared_hook_post getasrt]in H.
     unfold V293_tick_shared_resource in H;rewrite Decode in H.
     eapply V293_star_CurLINV_r;[exact Local|exact H].
Qed.
Theorem V293_tick_shared_body_hoare : forall Spec sd li tid bc bs lg clock run ct es si ci
 ptcb rows group saved now running head hook caller old scan
 (Good:GoodFunAsrt R),
 V293_tick_shared_index lg=Some(clock,run,ct,es,si,ci) ->
 NoAbs li -> (Int.unsigned(snd idle)+50<=Int.max_unsigned)%Z ->
 Forall V293_tick_binding_valid bindings -> NoDup(V293_tick_record_keys bindings idle) -> run<256 ->
 (forall st,st |= caller ** R ->
 V293_tick_post_env ptcb rows group now running head bc br bg bn bu bh(getgenv st)(getlenv st)) ->
 ((CurTid ct ** R) ==> CurLINV li tid) ->
 GoodFrm caller -> GoodFrm R -> can_change_aop caller -> can_change_aop R ->
 (gettopis si<=INUM)%nat -> (forall i,ir i=false) ->
 Spec hook=Some(V293_tick_shared_hook_pre Good,V293_tick_shared_hook_post Good,(Tvoid,[])) ->
 InfRules Spec sd li(V293_time_ready_inv br bg bp bn)
 (V293_tick_builder_result bindings idle br bg bp bn bu bh run R bc bs saved caller scan ir si ci)Afalse
 (V293_tick_builder_entry bindings idle message ct es br bg bp bn bu bh run R bc bs saved caller old scan clock ir si ci)
 (sseq(V293_tick_body ptcb rows group saved now running head hook)sret)Afalse tid.
Proof.
 intros Spec sd li tid bc bs lg clock run ct es si ci ptcb rows group saved now running head hook caller old scan Good Decode
 NA Limit Valid Unique Range Env Local CallerFrame Frame CallerChange Change Bound Clear Lookup.
 apply seq_rule with(p':=V293_tick_scan_switch_result bindings idle br bg bp bn bc bu bh run
 (V293_tick_saved_frame bs((V293_time_binding true saved bs ** caller) ** R))scan ir si ci).
 - change(InfRules Spec sd li(V293_time_ready_inv br bg bp bn)
   (V293_tick_builder_result bindings idle br bg bp bn bu bh run R bc bs saved caller scan ir si ci)Afalse
   (V293_tick_builder_entry bindings idle message ct es br bg bp bn bu bh run R bc bs saved caller old scan clock ir si ci)
   (sseq(sassign(evar saved)(econst32 Int.zero))
    (sseq(scall hook[])(V293_tick_post_hook ptcb rows group now running head)))
   (V293_tick_scan_switch_result bindings idle br bg bp bn bc bu bh run
    (V293_tick_saved_frame bs((V293_time_binding true saved bs ** caller) ** R))scan ir si ci)tid).
   eapply seq_rule;[apply V293_tick_builder_initialize;exact Local| ].
   eapply seq_rule.
   + apply V293_tick_shared_hook_call with(lg:=lg)(Good:=Good);try assumption.
     * unfold V293_time_cell,V293_time_binding;cbn[GoodFrm];repeat split;try exact I;exact CallerFrame.
     * apply V293_tick_builder_resource_local;exact Local.
   + eapply conseq_rule with(p:=<||V293_tick_post_hook_core_code bindings run||> ** OS[ir,false,si,ci] **
       V293_tick_scan_switch_pre bindings idle message ct es br bg bp bn bc bu bh run
       (V293_tick_saved_frame bs((V293_time_binding true saved bs ** caller) ** R))clock scan).
     * unfold V293_tick_builder_resource,V293_time_cell,V293_tick_scan_switch_pre,
       V293_tick_scan_supplement,V293_tick_saved_frame,V293_tick_call_shared,V293_owned_record_cell;
       intros s H;clear -H;sep auto.
     * intros s H;exact H.
     * apply V293_tick_scan_switch_hoare;try assumption.
       -- intros s H;eapply V293_star_env_r;[exact Env| ].
          unfold V293_tick_saved_frame in H;clear -H;sep auto.
       -- intros s H.
          assert(K:s |= (CurTid ct ** R) ** Atrue)by(unfold V293_tick_saved_frame in H;clear -H;sep auto).
          eapply V293_CurLINV_extend with(extra:=Atrue).
          eapply astar_mono;[exact Local|intros st Hs;exact Hs|exact K].
       -- unfold V293_tick_saved_frame,V293_owned_record_cell,V293_time_binding;
          cbn[GoodFrm];repeat split;try exact I;assumption.
       -- unfold V293_tick_saved_frame,V293_owned_record_cell,V293_time_binding;
          cbn[can_change_aop];repeat split;try exact I;assumption.
 - apply ret_rule;unfold V293_tick_builder_result;intros s H;clear -H;sep auto.
Qed.


Definition V293_tick_shared_pre_asrt lg tid :=
 match V293_tick_shared_index lg with
 | Some(clock,run,ct,es,si,ci) => if V293_tick_shared_guard run ct si tid then
   V293_tick_builder_resource bindings idle message ct es br bg bp bn bu bh run R clock ir si ci
   else Afalse
 | None => Afalse
 end.
Definition V293_tick_shared_post_asrt lg tid (result:option val) :=
 match V293_tick_shared_index lg with
 | Some(clock,run,ct,es,si,ci) => if V293_tick_shared_guard run ct si tid then
   [|result=None|] ** V293_tick_return_resources bindings idle br bg bp bn bu bh run R ir si ci
   else Afalse
 | None => Afalse
 end.
Lemma V293_tick_shared_pre_good : forall lg tid,
 GoodFunAsrt R -> GoodFunAsrt(V293_tick_shared_pre_asrt lg tid).
Proof.
 intros lg tid Good;unfold V293_tick_shared_pre_asrt.
 destruct(V293_tick_shared_index lg)as[[[[[[clock run]ct]es]si]ci]| ];
 [destruct(V293_tick_shared_guard run ct si tid)| ];
 try exact I;apply V293_tick_builder_resource_good;exact Good.
Qed.
Lemma V293_tick_shared_post_good : forall lg tid result,
 GoodFunAsrt R -> GoodFunAsrt(V293_tick_shared_post_asrt lg tid result).
Proof.
 intros lg tid result Good;unfold V293_tick_shared_post_asrt.
 destruct(V293_tick_shared_index lg)as[[[[[[clock run]ct]es]si]ci]| ];
 [destruct(V293_tick_shared_guard run ct si tid)| ];try exact I.
 split;[exact I|apply V293_tick_return_resources_good;exact Good].
Qed.
Definition V293_tick_shared_fpre (Good:GoodFunAsrt R) : fpre :=
 fun vl lg tid => @mkfunasrt (V293_tick_shared_pre_asrt lg tid)(V293_tick_shared_pre_good lg tid Good).
Definition V293_tick_shared_fpost (Good:GoodFunAsrt R) : fpost :=
 fun vl result lg tid => @mkfunasrt (V293_tick_shared_post_asrt lg tid result)(V293_tick_shared_post_good lg tid result Good).
Theorem V293_tick_shared_internal_resources : forall Spec sd li tid lg clock run ct es si ci
 ptcb rows group saved now running head hook (Good:GoodFunAsrt R),
 V293_tick_shared_index lg=Some(clock,run,ct,es,si,ci) ->
 NoAbs li -> (Int.unsigned(snd idle)+50<=Int.max_unsigned)%Z ->
 Forall V293_tick_binding_valid bindings -> NoDup(V293_tick_record_keys bindings idle) -> run<256 ->
 (forall bc st,st |= V293_tick_builder_caller ptcb saved bc ** R ->
 V293_tick_post_env ptcb rows group now running head bc br bg bn bu bh(getgenv st)(getlenv st)) ->
 ((CurTid ct ** R) ==> CurLINV li tid) ->
 GoodFrm R -> can_change_aop R -> (gettopis si<=INUM)%nat -> (forall i,ir i=false) ->
 Spec hook=Some(V293_tick_shared_hook_pre Good,V293_tick_shared_hook_post Good,(Tvoid,[])) ->
 InfRules Spec sd li(V293_time_ready_inv br bg bp bn)
 (V293_tick_builder_post bindings idle br bg bp bn bu bh run R ptcb saved ir si ci)Afalse
 (V293_tick_builder_pre bindings idle message ct es br bg bp bn bu bh run R ptcb saved clock ir si ci)
 (sseq(V293_tick_body ptcb rows group saved now running head hook)sret)Afalse tid.
Proof.
 intros Spec sd li tid lg clock run ct es si ci ptcb rows group saved now running head hook Good Decode
 NA Limit Valid Unique Range Env Local Frame Change Bound Clear Lookup.
 eapply conseq_rule;[apply V293_tick_builder_unpack|intros s H;exact H| ].
 apply ex_intro_rule;intro old;apply ex_intro_rule;intro scan.
 apply ex_intro_rule;intro bc;apply ex_intro_rule;intro bs.
 eapply r_conseq_rule with(r:=V293_tick_builder_result bindings idle br bg bp bn bu bh run R bc bs saved
   (V293_tick_builder_caller ptcb saved bc)scan ir si ci).
 - intro result;apply V293_tick_builder_pack.
 - intros s H;exact H.
 - apply V293_tick_shared_body_hoare with(lg:=lg)(Good:=Good);try assumption.
   + apply Env.
   + unfold V293_tick_builder_caller,V293_tick_builder_domain;cbn[GoodFrm];split;exact I.
   + unfold V293_tick_builder_caller,V293_tick_builder_domain;cbn[can_change_aop];split;exact I.
Qed.

Theorem V293_tick_shared_internal_contract : forall P f Spec sd li tid
 ptcb rows group saved now running head hook vl lg pre post (Good:GoodFunAsrt R),
 ptcb<>saved ->
 NoAbs li -> (Int.unsigned(snd idle)+50<=Int.max_unsigned)%Z ->
 Forall V293_tick_binding_valid bindings -> NoDup(V293_tick_record_keys bindings idle) ->
 (forall bc st,st |= V293_tick_builder_caller ptcb saved bc ** R ->
 V293_tick_post_env ptcb rows group now running head bc br bg bn bu bh(getgenv st)(getlenv st)) ->
 (forall owner,(CurTid owner ** R) ==> CurLINV li owner) ->
 GoodFrm R -> can_change_aop R ->
 Spec hook=Some(V293_tick_shared_hook_pre Good,V293_tick_shared_hook_post Good,(Tvoid,[])) ->
 P f=Some(V293_tick_function ptcb rows group saved now running head hook) ->
 Some pre=BuildPreI P f vl lg(V293_tick_shared_fpre Good)tid ->
 Some post=BuildRetI P f vl lg(V293_tick_shared_fpost Good)tid ->
 InfRules Spec sd li(V293_time_ready_inv br bg bp bn)post Afalse pre
 (sseq(V293_tick_body ptcb rows group saved now running head hook)sret)Afalse tid.
Proof.
 intros P f Spec sd li tid ptcb rows group saved now running head hook vl lg pre post Good
 Different NA Limit Valid Unique Env Local Frame Change Lookup Body Pre Post.
 destruct(V293_tick_builder_buildp ptcb saved Different)as[Buildp Buildq].
 unfold BuildPreI in Pre;rewrite Body in Pre.
 destruct vl as[ |v vl].
 2:{ assert(E:dl_vl_match dnil(rev(v::vl))=false).
     { destruct(rev(v::vl))eqn:Rev;[ |reflexivity].
       apply(f_equal(@rev val))in Rev;rewrite rev_involutive in Rev;discriminate. }
     unfold V293_tick_function in Pre;rewrite E in Pre;discriminate. }
 change(Some pre=match buildp (dcons ptcb(Tptr V293_tcb_type)(dcons saved Tint32 dnil))nil with
 |Some cells=>Some(cells ** V293_tick_shared_pre_asrt lg tid ** V293_tick_builder_domain ptcb saved)
 |None=>None end)in Pre.
 rewrite Buildp in Pre;inversion Pre;subst pre.
 unfold BuildRetI in Post;rewrite Body in Post.
 change(Some post=match buildq(dcons ptcb(Tptr V293_tcb_type)(dcons saved Tint32 dnil))with
 |Some cells=>Some(fun result=>cells ** V293_tick_shared_post_asrt lg tid result **
 V293_tick_builder_domain ptcb saved)|None=>None end)in Post.
 rewrite Buildq in Post;inversion Post;subst post.
 unfold V293_tick_shared_pre_asrt,V293_tick_shared_post_asrt.
 destruct(V293_tick_shared_index lg)as[[[[[[clock run]ct]es]si]ci]| ]eqn:Decode.
 - destruct(V293_tick_shared_guard run ct si tid)eqn:Guard.
   + apply V293_tick_shared_guard_valid in Guard;destruct Guard as[Same[Range Bound]];subst ct.
     apply V293_tick_shared_internal_resources with(lg:=lg)(Good:=Good);try assumption.
     * apply Local.
     * reflexivity.
   + eapply conseq_rule with(p:=Afalse);[intros s H;apply astar_comm in H;apply astar_assoc_elim in H;apply astar_l_afalse_elim in H;exact H|intros s H;exact H|apply pfalse_rule].
 - eapply conseq_rule with(p:=Afalse);[intros s H;apply astar_comm in H;apply astar_assoc_elim in H;apply astar_l_afalse_elim in H;exact H|intros s H;exact H|apply pfalse_rule].
Qed.
End SharedSnapshot.
