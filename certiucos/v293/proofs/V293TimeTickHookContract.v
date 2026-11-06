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

Definition V293_tick_hook_fpre (owner:tid) (resource:asrt)
 (good:GoodFunAsrt resource) : fpre :=
 fun vl lg t => @mkfunasrt
  ([|vl=[] /\ lg=[] /\ t=owner|] ** resource)(conj I good).
Definition V293_tick_hook_fpost (owner:tid) (resource:asrt)
 (good:GoodFunAsrt resource) : fpost :=
 fun vl result lg t => @mkfunasrt
  ([|vl=[] /\ lg=[] /\ t=owner /\ result=None|] ** resource)(conj I good).

Lemma V293_tick_hook_call_rule : forall Spec sd li I r ri tid hook resource caller
 (good:GoodFunAsrt resource),
 GoodFrm caller -> (resource ==> CurLINV li tid) ->
 Spec hook=Some(V293_tick_hook_fpre tid resource good,
   V293_tick_hook_fpost tid resource good,(Tvoid,[])) ->
 InfRules Spec sd li I r ri(resource ** caller)(scall hook [])(resource ** caller)tid.
Proof.
 intros Spec sd li I r ri tid hook resource caller good Frame Local Lookup.
 eapply conseq_rule with(q:=EX result:option val,
  getasrt(V293_tick_hook_fpost tid resource good [] result [] tid) ** caller).
 - intros s H;exact H.
 - intros s[result H];cbn[V293_tick_hook_fpost getasrt]in H;clear -H;sep auto.
 - eapply call_rule with(pre:=V293_tick_hook_fpre tid resource good)
   (post:=V293_tick_hook_fpost tid resource good)(vl:=[])(logicl:=[])
   (tp:=Tvoid)(tl:=[])(p:=caller).
   + exact Frame.
   + exact Lookup.
   + intros s H;cbn[V293_tick_hook_fpre getasrt];clear -H;sep auto.
   + intros s H;destruct s as [[[[[[ge le] M] ir] aux] O] op];cbn;repeat split;reflexivity.
   + reflexivity.
   + cbn[V293_tick_hook_fpre getasrt];apply V293_star_CurLINV_r;exact Local.
   + intros s[result H];cbn[V293_tick_hook_fpost getasrt]in H.
     eapply V293_star_CurLINV_r;[exact Local|exact H].
Qed.

Section TickHook.
Variables (bindings:list(V293_tick_task*(taskstatus*val))) (idle:addrval) (message:val)
 (ct:tid) (es:EcbMod.map) (br bg bp bn bc bs bu bh:block) (run:nat) (R:asrt).
Let code:=V293_tick_post_hook_core_code bindings run.
Definition V293_tick_hook_resource clock ir si ci :=
 <||code||> ** OS[ir,false,si,ci] **
 V293_tick_call_suffix bindings idle message ct es br bg bp bn bc bs bu bh run R clock.

Lemma V293_tick_hook_resource_good : forall clock ir si ci,
 GoodFunAsrt R -> GoodFunAsrt(V293_tick_hook_resource clock ir si ci).
Proof.
 intros clock ir si ci Good.
 unfold V293_tick_hook_resource,V293_tick_call_suffix,V293_tick_scan_switch_pre,
 V293_tick_scan_supplement,V293_tick_saved_frame.
 split;[exact I| ];split;[cbn[GoodFunAsrt];repeat split;exact I| ];split.
 - unfold V293_tick_switch_view;split.
   + exact(proj1(V293_sched_critical_good(V293_time_ready_inv br bg bp bn)[][])).
   + split;[unfold V293_shared_fields;cbn[GoodFunAsrt];repeat split;exact I|exact I].
 - split;[exact I| ];split.
   + apply V293_inv_function_assertion;apply V293_owned_cells_good.
   + split;[apply V293_inv_function_assertion;apply V293_owned_cells_good| ].
     split;[unfold V293_owned_record_cell;cbn[GoodFunAsrt];split;exact I|exact Good].
Qed.

Lemma V293_tick_hook_resource_local : forall clock ir si ci li tid,
 ((CurTid ct ** R) ==> CurLINV li tid) ->
 V293_tick_hook_resource clock ir si ci ==> CurLINV li tid.
Proof.
 intros clock ir si ci li tid Local s Held.
 assert(Open:s |= (V293_shared_flags **
  (((CurTid ct ** V293_shared_fields ct(V293_tick_record_map false bindings idle message)es clock) **
   V293_ready_payload br bg bp(V293_tick_record_map false bindings idle message)) **
   PV(bn,Int.zero)@Tint32|->Vint32 clock)) **
  (V293_tick_scan_supplement bindings idle bc bu bh run(V293_tick_saved_frame bs R)Vundef **
   (<||code||> ** OS[ir,false,si,ci]))).
 { eapply astar_mono;[apply V293_tick_switch_open|intros st H;exact H| ].
   unfold V293_tick_hook_resource,V293_tick_call_suffix,V293_tick_scan_switch_pre in Held;
   clear -Held;sep auto. }
 assert(Keep:s |= (CurTid ct ** R) ** Atrue).
 { unfold V293_tick_scan_supplement,V293_tick_saved_frame in Open;clear -Open;sep auto. }
 eapply V293_star_CurLINV_l;[exact Local|exact Keep].
Qed.

(* Only reassociation: the callee gets no Alvarenv or A_notin_lenv. *)
Lemma V293_tick_hook_resource_factor : forall clock ir si ci caller s,
 (s |= <||code||> ** OS[ir,false,si,ci] **
  V293_tick_call_suffix bindings idle message ct es br bg bp bn bc bs bu bh run(caller ** R)clock) <->
 (s |= V293_tick_hook_resource clock ir si ci ** caller).
Proof.
 intros;unfold V293_tick_hook_resource,V293_tick_call_suffix,V293_tick_scan_switch_pre,
 V293_tick_scan_supplement,V293_tick_saved_frame;split;intro H;clear -H;sep auto.
Qed.

Theorem V293_tick_hook_then_suffix : forall Spec sd li r ri tid clock ir si ci
 ptcb rows group now running head hook caller
 (good:GoodFunAsrt(V293_tick_hook_resource clock ir si ci)),
 NoAbs li -> (Int.unsigned(snd idle)+50<=Int.max_unsigned)%Z ->
 Forall V293_tick_binding_valid bindings -> NoDup(V293_tick_record_keys bindings idle) -> run<256 ->
 (forall st,st |= caller ** R ->
   V293_tick_post_env ptcb rows group now running head bc br bg bn bu bh(getgenv st)(getlenv st)) ->
 ((CurTid ct ** R) ==> CurLINV li tid) ->
 GoodFrm caller -> GoodFrm R -> can_change_aop caller -> can_change_aop R ->
 (gettopis si<=INUM)%nat -> (forall i,ir i=false) ->
 Spec hook=Some(V293_tick_hook_fpre tid(V293_tick_hook_resource clock ir si ci)good,
   V293_tick_hook_fpost tid(V293_tick_hook_resource clock ir si ci)good,(Tvoid,[])) ->
 InfRules Spec sd li(V293_time_ready_inv br bg bp bn)r ri
 (<||code||> ** OS[ir,false,si,ci] **
   V293_tick_call_suffix bindings idle message ct es br bg bp bn bc bs bu bh run(caller ** R)clock)
 (sseq(scall hook[])(V293_tick_post_hook ptcb rows group now running head))
 (V293_tick_scan_switch_result bindings idle br bg bp bn bc bu bh run
   (V293_tick_saved_frame bs(caller ** R))Vundef ir si ci)tid.
Proof.
 intros Spec sd li r ri tid clock ir si ci ptcb rows group now running head hook caller good
 NA Limit Valid Unique Range Env Local CallerFrame Frame CallerChange Change Bound Clear Lookup.
 eapply seq_rule.
 - eapply conseq_rule.
   + intros s H;apply(proj1(V293_tick_hook_resource_factor clock ir si ci caller s));exact H.
   + intros s H;apply(proj2(V293_tick_hook_resource_factor clock ir si ci caller s));exact H.
   + apply V293_tick_hook_call_rule with(good:=good);try assumption.
     apply V293_tick_hook_resource_local;exact Local.
 - apply V293_tick_call_suffix_hoare;try assumption.
   + intros s H.
     assert(K:s |= (CurTid ct ** R) ** caller)by(clear -H;sep auto).
     eapply V293_star_CurLINV_l;[exact Local|exact K].
   + cbn[GoodFrm];split;assumption.
   + cbn[can_change_aop];split;assumption.
Qed.
End TickHook.
