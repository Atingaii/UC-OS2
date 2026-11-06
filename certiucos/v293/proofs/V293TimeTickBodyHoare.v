(* The configured tick has a REAL nil-argument CPU hook. Its external Spec
   entry remains an implementation obligation, not a manufactured port body.
   Caller-local bindings stay outside the callee's GoodFunAsrt resource. *)
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
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.soundness.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope nat_scope.

Require Import CertiOS.certiucos.v293.proofs.V293TimeTickHookContract.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickReturnTail.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.code.V293OSTimeTick.

(* Body-level contract, before BuildRetI and deallocation. The external CPU
   hook Spec is explicit; no CPU hook implementation or WFFunEnv is asserted. *)
Section TickBody.
Variables (bindings:list(V293_tick_task*(taskstatus*val))) (idle:addrval) (message:val)
 (ct:tid) (es:EcbMod.map) (br bg bp bn bc bs bu bh:block) (run:nat) (R:asrt).
Let code:=V293_tick_post_hook_core_code bindings run.
Definition V293_tick_body_entry saved caller old clock ir si ci :=
 <||code||> ** (V293_time_cell true saved bs old **
  (OS[ir,false,si,ci] ** (Amapsto(bc,0%Z)(Tptr V293_tcb_type)true Vundef **
   V293_tick_call_shared bindings idle message ct es br bg bp bn bu bh run(caller ** R)clock))).
Definition V293_tick_body_return saved caller ir si ci (result:option val) :=
 [|result=None|] **
 V293_tick_scan_switch_result bindings idle br bg bp bn bc bu bh run
  (V293_tick_saved_frame bs((V293_time_binding true saved bs ** caller) ** R))Vundef ir si ci.

Lemma V293_tick_body_shared_local : forall clock li tid,
 ((CurTid ct ** R) ==> CurLINV li tid) -> forall caller,
 V293_tick_call_shared bindings idle message ct es br bg bp bn bu bh run(caller ** R)clock
 ==> CurLINV li tid.
Proof.
 intros clock li tid Local caller s Held.
 assert(Open:s |= (V293_shared_flags **
  (((CurTid ct ** V293_shared_fields ct(V293_tick_record_map false bindings idle message)es clock) **
   V293_ready_payload br bg bp(V293_tick_record_map false bindings idle message)) **
   PV(bn,Int.zero)@Tint32|->Vint32 clock)) **
  (V293_owned_record_cells(V293_tick_chain_missing bindings idle) **
   (V293_owned_record_cells(V293_tick_post_hook_core_globals bindings idle bu bh run) ** (caller ** R)))).
 { eapply astar_mono;[apply V293_tick_switch_open|intros st H;exact H|exact Held]. }
 assert(Keep:s |= (CurTid ct ** R) ** Atrue)by(clear -Open;sep auto).
 eapply V293_star_CurLINV_l;[exact Local|exact Keep].
Qed.

Lemma V293_tick_body_initialize : forall Spec sd li I r ri tid clock ir si ci saved caller old,
 ((CurTid ct ** R) ==> CurLINV li tid) ->
 InfRules Spec sd li I r ri(V293_tick_body_entry saved caller old clock ir si ci)
  (sassign(evar saved)(econst32 Int.zero))
  (<||code||> ** OS[ir,false,si,ci] **
   V293_tick_call_suffix bindings idle message ct es br bg bp bn bc bs bu bh run
     ((V293_time_binding true saved bs ** caller) ** R)clock)tid.
Proof.
 intros Spec sd li I r ri tid clock ir si ci saved caller old Local.
 eapply conseq_rule with(q:=<||code||> ** (V293_time_cell true saved bs(Vint32 Int.zero) **
  (OS[ir,false,si,ci] ** (Amapsto(bc,0%Z)(Tptr V293_tcb_type)true Vundef **
   V293_tick_call_shared bindings idle message ct es br bg bp bn bu bh run(caller ** R)clock)))).
 - intros s H;exact H.
 - intros s H.
   unfold V293_time_cell,V293_tick_call_suffix,V293_tick_scan_switch_pre,
    V293_tick_scan_supplement,V293_tick_saved_frame,V293_tick_call_shared,
    V293_owned_record_cell in *;clear -H;sep auto.
 - unfold V293_tick_body_entry.
   apply V293_time_zero.
   apply V293_star_CurLINV_r;apply V293_star_CurLINV_r.
   apply V293_tick_body_shared_local;exact Local.
Qed.

(* Stable logical interface for the EXACT normalized function body. *)
Theorem V293_tick_body_hoare : forall Spec sd li tid clock ir si ci
 ptcb rows group saved now running head hook caller old
 (good:GoodFunAsrt(V293_tick_hook_resource bindings idle message ct es
    br bg bp bn bc bs bu bh run R clock ir si ci)),
 NoAbs li -> (Int.unsigned(snd idle)+50<=Int.max_unsigned)%Z ->
 Forall V293_tick_binding_valid bindings -> NoDup(V293_tick_record_keys bindings idle) -> run<256 ->
 (forall st,st |= caller ** R ->
   V293_tick_post_env ptcb rows group now running head bc br bg bn bu bh(getgenv st)(getlenv st)) ->
 ((CurTid ct ** R) ==> CurLINV li tid) ->
 GoodFrm caller -> GoodFrm R -> can_change_aop caller -> can_change_aop R ->
 (gettopis si<=INUM)%nat -> (forall i,ir i=false) ->
 Spec hook=Some(V293_tick_hook_fpre tid _ good,V293_tick_hook_fpost tid _ good,(Tvoid,[])) ->
 InfRules Spec sd li(V293_time_ready_inv br bg bp bn)
  (V293_tick_body_return saved caller ir si ci)Afalse
  (V293_tick_body_entry saved caller old clock ir si ci)
  (sseq(V293_tick_body ptcb rows group saved now running head hook)sret)Afalse tid.
Proof.
 intros Spec sd li tid clock ir si ci ptcb rows group saved now running head hook caller old good
 NA Limit Valid Unique Range Env Local CallerFrame Frame CallerChange Change Bound Clear Lookup.
 apply seq_rule with(p':=V293_tick_scan_switch_result bindings idle br bg bp bn bc bu bh run
   (V293_tick_saved_frame bs((V293_time_binding true saved bs ** caller) ** R))Vundef ir si ci).
 - change(InfRules Spec sd li(V293_time_ready_inv br bg bp bn)
    (V293_tick_body_return saved caller ir si ci)Afalse
    (V293_tick_body_entry saved caller old clock ir si ci)
    (sseq(sassign(evar saved)(econst32 Int.zero))
      (sseq(scall hook[])(V293_tick_post_hook ptcb rows group now running head)))
    (V293_tick_scan_switch_result bindings idle br bg bp bn bc bu bh run
     (V293_tick_saved_frame bs((V293_time_binding true saved bs ** caller) ** R))Vundef ir si ci)tid).
   eapply seq_rule.
   + apply V293_tick_body_initialize;exact Local.
   + apply V293_tick_hook_then_suffix with(good:=good);try assumption.
     * intros s H.
       eapply V293_star_env_r;[exact Env| ].
       clear -H;sep auto.
     * cbn[V293_time_binding GoodFrm];split;[exact I|exact CallerFrame].
     * cbn[V293_time_binding can_change_aop];split;[exact I|exact CallerChange].
 - apply ret_rule;unfold V293_tick_body_return;intros s H;clear -H;sep auto.
Qed.

Lemma V293_tick_body_return_not_value : forall saved caller ir si ci v,
 V293_tick_body_return saved caller ir si ci(Some v) ==> Afalse.
Proof.
 intros saved caller ir si ci v s H;unfold V293_tick_body_return in H.
 assert(E:Some v=None)by(clear -H;sep auto). discriminate.
Qed.
(* Consume the logical None return post with the already proved real free
   semantics. This is conditional on that post, not a trace through the hook. *)
Theorem V293_tick_body_return_to_caller : forall P ks ge caller M ir si ci O
 ptcb saved f body B,
 ptcb<>saved -> GoodFunAsrt R -> (B ==> Aemp) ->
 (ge,V293_tick_locals ptcb saved bc bs,M,ir,(false,si,ci),O,END None) |=
  V293_tick_body_return saved B ir si ci None -> exists Mf,
 V293_local_steps P(curs(sskip None),(kenil,kseq sret(kcall f body caller ks)))
  ((ge,V293_tick_locals ptcb saved bc bs,M),ir,(false,si,ci))
  (curs(sskip None),(kenil,ks))((ge,caller,Mf),ir,(false,si,ci)) /\
 (ge,caller,Mf,ir,(false,si,ci),O,END None) |=
  V293_tick_return_resources bindings idle br bg bp bn bu bh run R ir si ci /\
 (forall k,k<4 -> get Mf(bc,Z.of_nat k)=None /\ get Mf(bs,Z.of_nat k)=None).
Proof.
 intros P ks ge caller M ir si ci O ptcb saved f body B Different Good Empty Held.
 assert(Post:(ge,V293_tick_locals ptcb saved bc bs,M,ir,(false,si,ci),O,END None) |=
  V293_tick_scan_switch_result bindings idle br bg bp bn bc bu bh run
   (V293_tick_saved_frame bs((V293_time_binding true saved bs ** B) ** R))Vundef ir si ci).
 { unfold V293_tick_body_return in Held;clear -Held;sep auto. }
 apply V293_tick_result_forget_bindings in Post.
 - eapply V293_tick_return_tail;[exact Different|exact Good|exact Post].
 - intros s H.
   assert(E:s |= Aemp ** Aemp).
   { eapply astar_mono;[ |exact Empty|exact H].
     intros st K;destruct st as[[[[[[ge0 le]M0]ir0]aux]O0]op].
     destruct K as[b[Binding[Address[Mem Abs]]]];split;assumption. }
   clear -E;sep auto.
Qed.
End TickBody.
