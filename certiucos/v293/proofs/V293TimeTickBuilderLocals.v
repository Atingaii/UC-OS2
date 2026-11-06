(* Real builders accept arbitrary raw local values. The CPU hook keeps only
   shared resources; caller locals are framed, not hidden in its contract. *)
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
Section BuilderLocals.
Variables(bindings:list(V293_tick_task*(taskstatus*val)))(idle:addrval)(message:val)
 (ct:tid)(es:EcbMod.map)(br bg bp bn bu bh:block)(run:nat)(R:asrt).
Let code:=V293_tick_post_hook_core_code bindings run.
Definition V293_tick_builder_resource clock ir si ci:=
 <||code||> ** OS[ir,false,si,ci] **
 V293_tick_call_shared bindings idle message ct es br bg bp bn bu bh run R clock.
Definition V293_tick_builder_entry bc bs saved caller old scan clock ir si ci:=
 <||code||> ** (V293_time_cell true saved bs old **
  (OS[ir,false,si,ci] ** (Amapsto(bc,0%Z)(Tptr V293_tcb_type)true scan **
   V293_tick_call_shared bindings idle message ct es br bg bp bn bu bh run(caller ** R)clock))).
Definition V293_tick_builder_result bc bs saved caller scan ir si ci (result:option val):=
 [|result=None|] ** V293_tick_scan_switch_result bindings idle br bg bp bn bc bu bh run
 (V293_tick_saved_frame bs((V293_time_binding true saved bs ** caller) ** R))scan ir si ci.

Lemma V293_tick_builder_resource_good : forall clock ir si ci,
 GoodFunAsrt R -> GoodFunAsrt(V293_tick_builder_resource clock ir si ci).
Proof.
 intros clock ir si ci Good.
 unfold V293_tick_builder_resource,V293_tick_call_shared.
 split;[exact I| ];split;[cbn[GoodFunAsrt];repeat split;exact I| ];split.
 - unfold V293_tick_switch_view;split.
   + exact(proj1(V293_sched_critical_good(V293_time_ready_inv br bg bp bn)[][])).
   + split;[unfold V293_shared_fields;cbn[GoodFunAsrt];repeat split;exact I|exact I].
 - split;[apply V293_inv_function_assertion;apply V293_owned_cells_good| ].
   split;[apply V293_inv_function_assertion;apply V293_owned_cells_good|exact Good].
Qed.
Lemma V293_tick_builder_resource_local : forall clock ir si ci li tid,
 ((CurTid ct ** R) ==> CurLINV li tid) ->
 V293_tick_builder_resource clock ir si ci ==> CurLINV li tid.
Proof.
 intros clock ir si ci li tid Local s Held.
 assert(Shared:s |= V293_tick_call_shared bindings idle message ct es br bg bp bn bu bh run(Aemp ** R)clock ** Atrue).
 { unfold V293_tick_builder_resource,V293_tick_call_shared in *;clear -Held;sep auto. }
 eapply V293_star_CurLINV_l;[ |exact Shared].
 apply V293_tick_body_shared_local;exact Local.
Qed.
Lemma V293_tick_builder_initialize : forall Spec sd li I r ri tid bc bs saved caller old scan clock ir si ci,
 ((CurTid ct ** R) ==> CurLINV li tid) ->
 InfRules Spec sd li I r ri
 (V293_tick_builder_entry bc bs saved caller old scan clock ir si ci)
 (sassign(evar saved)(econst32 Int.zero))
 (V293_tick_builder_resource clock ir si ci **
  (V293_time_cell true saved bs(Vint32 Int.zero) **
   (Amapsto(bc,0%Z)(Tptr V293_tcb_type)true scan ** caller)))tid.
Proof.
 intros Spec sd li I r ri tid bc bs saved caller old scan clock ir si ci Local.
 eapply conseq_rule with(q:=V293_tick_builder_entry bc bs saved caller(Vint32 Int.zero)scan clock ir si ci).
 - intros s H;exact H.
 - unfold V293_tick_builder_entry,V293_tick_builder_resource,V293_tick_call_shared;
   intros s H;clear -H;sep auto.
 - unfold V293_tick_builder_entry;apply V293_time_zero.
   apply V293_star_CurLINV_r;apply V293_star_CurLINV_r.
   apply V293_tick_body_shared_local;exact Local.
Qed.

(* The hook Spec is independent of both local addresses and values. *)
Theorem V293_tick_builder_body_hoare : forall Spec sd li tid bc bs clock ir si ci
 ptcb rows group saved now running head hook caller old scan
 (good:GoodFunAsrt(V293_tick_builder_resource clock ir si ci)),
 NoAbs li -> (Int.unsigned(snd idle)+50<=Int.max_unsigned)%Z ->
 Forall V293_tick_binding_valid bindings -> NoDup(V293_tick_record_keys bindings idle) -> run<256 ->
 (forall st,st |= caller ** R ->
 V293_tick_post_env ptcb rows group now running head bc br bg bn bu bh(getgenv st)(getlenv st)) ->
 ((CurTid ct ** R) ==> CurLINV li tid) ->
 GoodFrm caller -> GoodFrm R -> can_change_aop caller -> can_change_aop R ->
 (gettopis si<=INUM)%nat -> (forall i,ir i=false) ->
 Spec hook=Some(V293_tick_hook_fpre tid _ good,V293_tick_hook_fpost tid _ good,(Tvoid,[])) ->
 InfRules Spec sd li(V293_time_ready_inv br bg bp bn)
 (V293_tick_builder_result bc bs saved caller scan ir si ci)Afalse
 (V293_tick_builder_entry bc bs saved caller old scan clock ir si ci)
 (sseq(V293_tick_body ptcb rows group saved now running head hook)sret)Afalse tid.
Proof.
 intros Spec sd li tid bc bs clock ir si ci ptcb rows group saved now running head hook caller old scan good
 NA Limit Valid Unique Range Env Local CallerFrame Frame CallerChange Change Bound Clear Lookup.
 apply seq_rule with(p':=V293_tick_scan_switch_result bindings idle br bg bp bn bc bu bh run
 (V293_tick_saved_frame bs((V293_time_binding true saved bs ** caller) ** R))scan ir si ci).
 - change(InfRules Spec sd li(V293_time_ready_inv br bg bp bn)
   (V293_tick_builder_result bc bs saved caller scan ir si ci)Afalse
   (V293_tick_builder_entry bc bs saved caller old scan clock ir si ci)
   (sseq(sassign(evar saved)(econst32 Int.zero))
    (sseq(scall hook[])(V293_tick_post_hook ptcb rows group now running head)))
   (V293_tick_scan_switch_result bindings idle br bg bp bn bc bu bh run
    (V293_tick_saved_frame bs((V293_time_binding true saved bs ** caller) ** R))scan ir si ci)tid).
   eapply seq_rule;[apply V293_tick_builder_initialize;exact Local| ].
   eapply seq_rule.
   + apply V293_tick_hook_call_rule with(good:=good);try assumption.
     * unfold V293_time_cell,V293_time_binding;cbn[GoodFrm];repeat split;try exact I;exact CallerFrame.
     * apply V293_tick_builder_resource_local;exact Local.
   + eapply conseq_rule with(p:=<||code||> ** OS[ir,false,si,ci] **
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
Definition V293_tick_builder_cells ptcb saved :=
 (EX scan:val, LV ptcb @(Tptr V293_tcb_type)|->scan) **
 ((EX old:val, LV saved @Tint32|->old) ** Aemp).
Definition V293_tick_builder_domain ptcb saved :=
 A_dom_lenv (cons (ptcb,Tptr V293_tcb_type) (cons (saved,Tint32) nil)).
Definition V293_tick_builder_caller ptcb saved bc :=
 Alvarenv ptcb (Tptr V293_tcb_type)(bc,0%Z) ** V293_tick_builder_domain ptcb saved.
Definition V293_tick_builder_pre ptcb saved clock ir si ci :=
 V293_tick_builder_cells ptcb saved ** V293_tick_builder_resource clock ir si ci **
 V293_tick_builder_domain ptcb saved.
Definition V293_tick_builder_post ptcb saved ir si ci (result:option val) :=
 V293_tick_builder_cells ptcb saved **
 ([|result=None|] ** V293_tick_return_resources bindings idle br bg bp bn bu bh run R ir si ci) **
 V293_tick_builder_domain ptcb saved.

Lemma V293_tick_builder_unpack : forall ptcb saved clock ir si ci,
 V293_tick_builder_pre ptcb saved clock ir si ci ==>
 EX old:val, EX scan:val, EX bc:block, EX bs:block,
 V293_tick_builder_entry bc bs saved (V293_tick_builder_caller ptcb saved bc) old scan clock ir si ci.
Proof.
 intros ptcb saved clock ir si ci s H.
 unfold V293_tick_builder_pre,V293_tick_builder_cells,Alvarmapsto,Alvarenv',Aptrmapsto,
 V293_tick_builder_entry,V293_tick_builder_caller,V293_tick_builder_resource,
 V293_tick_call_shared,V293_time_cell,V293_time_binding in *;clear -H;sep auto.
Qed.

Lemma V293_tick_builder_pack : forall ptcb saved bc bs scan ir si ci result,
 V293_tick_builder_result bc bs saved (V293_tick_builder_caller ptcb saved bc) scan ir si ci result ==>
 V293_tick_builder_post ptcb saved ir si ci result.
Proof.
 intros ptcb saved bc bs scan ir si ci result s Held.
 unfold V293_tick_builder_result in Held.
 apply astar_l_apure_elim in Held;destruct Held as[Result Held];subst result.
 unfold V293_tick_builder_post,V293_tick_return_resources,V293_tick_scan_switch_result in *.
 unfold V293_tick_builder_cells,Alvarmapsto,Alvarenv',Aptrmapsto.
 destruct(Nat.eqb run 1)eqn:Running.
 - destruct Held as[actual Held].
   unfold V293_tick_post_hook_core_frame,V293_tick_saved_frame,V293_owned_record_cell,
    V293_time_binding,V293_tick_builder_caller,V293_tick_pointer_cell in Held.
   clear -Held;sep auto.
 - unfold V293_tick_scan_supplement,V293_tick_saved_frame,V293_owned_record_cell,
    V293_time_binding,V293_tick_builder_caller in Held;clear -Held;sep auto.
Qed.

Definition V293_tick_builder_fpre clock ir si ci
 (good:GoodFunAsrt(V293_tick_builder_resource clock ir si ci)) : fpre :=
 fun vl lg tid => @mkfunasrt (V293_tick_builder_resource clock ir si ci) good.
Definition V293_tick_builder_fpost ir si ci (Good:GoodFunAsrt R) : fpost :=
 fun vl result lg tid => @mkfunasrt
  ([|result=None|] ** V293_tick_return_resources bindings idle br bg bp bn bu bh run R ir si ci)
  (conj I (V293_tick_return_resources_good bindings idle br bg bp bn bu bh run R ir si ci Good)).
Theorem V293_tick_builder_internal_resources : forall Spec sd li tid clock ir si ci
 ptcb rows group saved now running head hook
 (good:GoodFunAsrt(V293_tick_builder_resource clock ir si ci)),
 NoAbs li -> (Int.unsigned(snd idle)+50<=Int.max_unsigned)%Z ->
 Forall V293_tick_binding_valid bindings -> NoDup(V293_tick_record_keys bindings idle) -> run<256 ->
 (forall bc st,st |= V293_tick_builder_caller ptcb saved bc ** R ->
 V293_tick_post_env ptcb rows group now running head bc br bg bn bu bh(getgenv st)(getlenv st)) ->
 ((CurTid ct ** R) ==> CurLINV li tid) ->
 GoodFrm R -> can_change_aop R -> (gettopis si<=INUM)%nat -> (forall i,ir i=false) ->
 Spec hook=Some(V293_tick_hook_fpre tid _ good,V293_tick_hook_fpost tid _ good,(Tvoid,[])) ->
 InfRules Spec sd li(V293_time_ready_inv br bg bp bn)
 (V293_tick_builder_post ptcb saved ir si ci)Afalse
 (V293_tick_builder_pre ptcb saved clock ir si ci)
 (sseq(V293_tick_body ptcb rows group saved now running head hook)sret)Afalse tid.
Proof.
 intros Spec sd li tid clock ir si ci ptcb rows group saved now running head hook good
 NA Limit Valid Unique Range Env Local Frame Change Bound Clear Lookup.
 eapply conseq_rule;[apply V293_tick_builder_unpack|intros s H;exact H| ].
 apply ex_intro_rule;intro old;apply ex_intro_rule;intro scan.
 apply ex_intro_rule;intro bc;apply ex_intro_rule;intro bs.
 eapply r_conseq_rule with(r:=V293_tick_builder_result bc bs saved
   (V293_tick_builder_caller ptcb saved bc)scan ir si ci).
 - intro result;apply V293_tick_builder_pack.
 - intros s H;exact H.
 - apply V293_tick_builder_body_hoare with(good:=good);try assumption.
   + apply Env.
   + unfold V293_tick_builder_caller,V293_tick_builder_domain;cbn[GoodFrm];split;exact I.
   + unfold V293_tick_builder_caller,V293_tick_builder_domain;cbn[can_change_aop];split;exact I.
Qed.

Lemma V293_tick_builder_buildp : forall ptcb saved,
 ptcb<>saved ->
 buildp (dcons ptcb(Tptr V293_tcb_type)(dcons saved Tint32 dnil))nil=
 Some(V293_tick_builder_cells ptcb saved) /\
 buildq (dcons ptcb(Tptr V293_tcb_type)(dcons saved Tint32 dnil))=
 Some(V293_tick_builder_cells ptcb saved).
Proof.
 intros ptcb saved Different.
 assert(E:Zeq_bool ptcb saved=false).
 { destruct(Zeq_bool ptcb saved)eqn:E;[ |reflexivity].
   apply Zeq_is_eq_bool in E;contradiction. }
 cbn[buildp buildq good_decllist in_decllist];rewrite E;split;reflexivity.
Qed.

(* This is one function's actual builder obligation, not EqDom or WFFunEnv. *)
Theorem V293_tick_builder_internal_contract : forall P f Spec sd li tid clock ir si ci
 ptcb rows group saved now running head hook vl lg pre post
 (good:GoodFunAsrt(V293_tick_builder_resource clock ir si ci))(Good:GoodFunAsrt R),
 ptcb<>saved ->
 NoAbs li -> (Int.unsigned(snd idle)+50<=Int.max_unsigned)%Z ->
 Forall V293_tick_binding_valid bindings -> NoDup(V293_tick_record_keys bindings idle) -> run<256 ->
 (forall bc st,st |= V293_tick_builder_caller ptcb saved bc ** R ->
 V293_tick_post_env ptcb rows group now running head bc br bg bn bu bh(getgenv st)(getlenv st)) ->
 ((CurTid ct ** R) ==> CurLINV li tid) ->
 GoodFrm R -> can_change_aop R -> (gettopis si<=INUM)%nat -> (forall i,ir i=false) ->
 Spec hook=Some(V293_tick_hook_fpre tid _ good,V293_tick_hook_fpost tid _ good,(Tvoid,[])) ->
 P f=Some(V293_tick_function ptcb rows group saved now running head hook) ->
 Some pre=BuildPreI P f vl lg(V293_tick_builder_fpre clock ir si ci good)tid ->
 Some post=BuildRetI P f vl lg(V293_tick_builder_fpost ir si ci Good)tid ->
 InfRules Spec sd li(V293_time_ready_inv br bg bp bn)post Afalse pre
 (sseq(V293_tick_body ptcb rows group saved now running head hook)sret)Afalse tid.
Proof.
 intros P f Spec sd li tid clock ir si ci ptcb rows group saved now running head hook vl lg pre post good Good
 Different NA Limit Valid Unique Range Env Local Frame Change Bound Clear Lookup Body Pre Post.
 destruct(V293_tick_builder_buildp ptcb saved Different)as[Buildp Buildq].
 unfold BuildPreI in Pre;rewrite Body in Pre.
 destruct vl as[ |v vl].
 2:{ assert(E:dl_vl_match dnil(rev(v::vl))=false).
     { destruct(rev(v::vl))eqn:Rev;[ |reflexivity].
       apply(f_equal(@rev val))in Rev;rewrite rev_involutive in Rev;discriminate. }
     unfold V293_tick_function in Pre;rewrite E in Pre;discriminate. }
 change(Some pre=match buildp (dcons ptcb(Tptr V293_tcb_type)(dcons saved Tint32 dnil))nil with
 |Some cells=>Some(cells ** V293_tick_builder_resource clock ir si ci ** V293_tick_builder_domain ptcb saved)
 |None=>None end)in Pre.
 rewrite Buildp in Pre;inversion Pre;subst pre.
 unfold BuildRetI in Post;rewrite Body in Post.
 change(Some post=match buildq(dcons ptcb(Tptr V293_tcb_type)(dcons saved Tint32 dnil))with
 |Some cells=>Some(fun result=>cells **
 ([|result=None|] ** V293_tick_return_resources bindings idle br bg bp bn bu bh run R ir si ci) **
 V293_tick_builder_domain ptcb saved)|None=>None end)in Post.
 rewrite Buildq in Post;inversion Post;subst post.
 apply V293_tick_builder_internal_resources with(good:=good);assumption.
Qed.
End BuilderLocals.
