(* One precise scheduling operation for enabled changed/same dispatch only. *)
Require Import CertiOS.certiucos.v293.proofs.V293InterruptBoundDispatchContinuous.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptBoundEntry.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptSameContinuous.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptChangedContinuous.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptSourceRoundtrip.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptBindings.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterOpenExact.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBoundDynamic.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyDynamic.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitSameInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitResourceCodec.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitChangedInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBuilders.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedDispatchFinish.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrent.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Lemma V293_equal_current_highest : forall lo hi entries tasks t nc,
 V293_ready_rel lo hi entries tasks -> V293_current_task tasks t nc ->
 V293_ready_select lo hi(V293_ready_group lo hi)=nc -> V293_highest_ready tasks t.
Proof.
 intros lo hi entries tasks t nc [L[H[R[B T]]]] Current Equal.
 destruct(V293_ready_selection_task lo hi entries tasks L H R B T)as[next[m[Task[Entry Highest]]]].
 pose proof(proj2(V293_OSSched_current_target lo hi entries tasks t nc next L H R B T Current Highest)Equal)as E.
 subst next;exact Highest.
Qed.

Section CommonDispatch.
Variables unmap group rows high table target current counter running nesting lock:var.
Variables bt bg br bh bp bo bc bk brun bn bl:block.
Variable rest:list(addr*type).
Variables lo hi nc:nat.
Variable entries:list val.
Variable tasks:TcbMod.map.
Variable events:EcbMod.map.
Variable now:int32.
Variables hv out:val.
Variable c:int32.
Let tp:=V293_tcb_type.
Let li:=V293_irq_bound_li running nesting lock brun bn bl.
Let Inv0:=V293_ready_dynamic_exit_inv target bt bg br bh bp bc bk brun bn bl rest.
Let efp:=V293_enter_bound_fpre running nesting lock brun bn bl Aemp Logic.I.
Let efq:=V293_enter_bound_fpost running nesting lock brun bn bl Aemp Logic.I.
Let xfp:=V293_bound_dynamic_fpre unmap group rows high table target current counter running nesting lock
 bt bg br bh bp bo bc bk brun bn bl rest Aemp Logic.I.
Let xfq:=V293_bound_dynamic_fpost unmap group rows high table target current counter running nesting lock
 bt bg br bh bp bo bc bk brun bn bl rest Aemp Logic.I.
Let changed:=V293_changed_irq_snapshot unmap group rows high table target current counter running nesting lock
 bt bg br bh bp bo bc bk brun bn bl rest lo hi nc entries tasks events now hv out c.
Let same:=V293_same_irq_snapshot unmap group rows high table target current counter running nesting lock
 bt bg br bh bp bo bc bk brun bn bl rest lo hi nc entries tasks events now hv out c.

Lemma V293_same_resources_sched : forall nest ir si t st,
 V293_ready_rel lo hi entries tasks -> V293_current_task tasks t nc ->
 V293_ready_select lo hi(V293_ready_group lo hi)=nc ->
 st|=OS[ir,false,si,nil] ** V293_same_irq_physical unmap group rows high table target current counter running nesting lock
 bt bg br bh bp bo bc bk brun bn bl rest lo hi nc entries tasks events now hv out c nest t ->
 sched_self V293_scheduler(getabst st).
Proof.
 intros nest ir si t st Rel Current Equal H.
 assert(P:st|=(CurTid t ** V293_shared_fields t tasks events now) ** Atrue)
 by(unfold V293_same_irq_physical,V293_same_irq_payload in H;sep auto).
 destruct(V293_shared_fields_core_get _ _ _ _ _ _ P)as[C[T _]].
 exists t;split;[exact C|exists tasks;split;[exact T| ]].
 eapply V293_equal_current_highest;eassumption.
Qed.

Lemma V293_same_schedule_reduce : forall nest aop ir si t,
 V293_ready_rel lo hi entries tasks -> V293_current_task tasks t nc ->
 V293_ready_select lo hi(V293_ready_group lo hi)=nc ->
 absinferfull V293_scheduler li(same nest(sched;;aop)ir si t)(same nest aop ir si t)t.
Proof.
 intros nest aop ir si t Rel Current Equal.
 unfold same,V293_same_irq_snapshot.
 set(P:=OS[ir,false,si,nil] **
 V293_same_irq_physical unmap group rows high table target current counter running nesting lock
 bt bg br bh bp bo bc bk brun bn bl rest lo hi nc entries tasks events now hv out c nest t).
 assert(Free:can_change_aop P).
 { unfold P;split;[cbn[can_change_aop];tauto| ].
   apply V293_good_frame_action_free;apply V293_same_irq_physical_good. }
 eapply absinfer_trans' with(q:=<||spec_done None;;aop||> ** P).
 - apply absinfer_seq';try exact Free.
   eapply(absinfer_sched' _ (fun _=>True) _ _ _ _);try exact Free.
   + intros s H;exact H.
   + intros s H;apply V293_same_resources_sched with(nest:=nest)(ir:=ir)(si:=si)(t:=t);assumption.
 - apply absinfer_seq_end';try exact Free;intros s H;exact H.
Qed.

Theorem V293_interrupt_common_same_continuous : forall Spec enter exit intspec i ir si t ret id,
 V293_same_exit_valid(i::si)(V293_same_irq_index lo hi nc entries tasks out c(spec_done None)) ->
 V293_current_task tasks t nc ->
 Forall(fun v=>rule_type_val_match(Tptr tp)v=true)entries ->
 Spec enter=Some(efp,efq,(Tvoid,nil)) ->Spec exit=Some(xfp,xfq,(Tvoid,nil)) ->
 Some ret=BuildintRet i intspec ir si Inv0 li t nil ->
 (forall j,ir j=false) ->(0<=Int.unsigned id<Z.of_nat INUM)%Z ->i=Z.to_nat(Int.unsigned id) ->
 InfRules Spec V293_scheduler li Inv0 arfalse ret
 (same 0(sched;;spec_done None)(isrupd ir i true)(i::si)t)
 (V293_irq_source_wrapper enter exit id)Afalse t.
Proof.
 intros Spec enter exit intspec i ir si t ret id Valid Current Types Enter Exit Ret Clear Bound Index.
 eapply abscsq_rule_full with(p:=same 0(spec_done None)(isrupd ir i true)(i::si)t)(q:=Afalse).
 - apply V293_same_schedule_reduce;[ |exact Current| ].
   + destruct Valid as[_[B[_[_[R[T[P E]]]]]]].
     unfold V293_same_irq_index,V293_exit_snapshot_bounded in *;cbn in *.
     unfold V293_ready_rel;tauto.
   + destruct Valid as[_[_[_[_[_[_[_ E]]]]]]];exact E.
 - apply absinfer_eq'.
 - eapply V293_interrupt_bound_same_continuous with(intspec:=intspec);eassumption.
Qed.

Definition V293_common_dispatch_entry i si t:=
 (changed 0(spec_done None)(isrupd(fun _:hid=>false)i true)(i::si)t **
 [|V293_changed_builder_valid tp lo hi nc 1 entries tasks t|]) \\//
 (same 0(sched;;spec_done None)(isrupd(fun _:hid=>false)i true)(i::si)t **
 [|V293_same_exit_valid(i::si)(V293_same_irq_index lo hi nc entries tasks out c(spec_done None)) /\
 V293_current_task tasks t nc|]).

Theorem V293_common_dispatch_BuildintPre : forall si t intspec pre,
 V293_ready_rel lo hi entries tasks ->
 Forall(fun v=>rule_type_val_match(Tptr tp)v=true)entries ->nc<256 ->
 rule_type_val_match Tint8 hv=true ->rule_type_val_match(Tptr tp)out=true ->
 intspec 0=Some(sched;;spec_done None) ->
 Some pre=BuildintPre 0 intspec(fun _:hid=>false)si Inv0 li t nil ->
 V293_common_dispatch_entry 0 si t ==>pre.
Proof.
 intros si t intspec pre Rel Types Cur High Output Spec Builder st H.
 unfold V293_common_dispatch_entry in H;destruct H as[H|H];apply astar_comm in H;apply astar_l_apure_elim in H;destruct H as[_ H].
 - eapply(V293_changed_entry_BuildintPre unmap group rows high table target current counter running nesting lock
 bt bg br bh bp bo bc bk brun bn bl rest lo hi nc entries tasks events now hv out c
 0 (spec_done None)(fun _:hid=>false)si t intspec pre);try eassumption;lia.
 - eapply(V293_same_entry_BuildintPre unmap group rows high table target current counter running nesting lock
 bt bg br bh bp bo bc bk brun bn bl rest lo hi nc entries tasks events now hv out c
 0 (sched;;spec_done None)(fun _:hid=>false)si t intspec pre);try eassumption;lia.
Qed.

Theorem V293_interrupt_common_dispatch_continuous : forall Spec enter exit intspec i si t ret id,
 Forall(fun v=>rule_type_val_match(Tptr tp)v=true)entries ->
 Spec enter=Some(efp,efq,(Tvoid,nil)) ->Spec exit=Some(xfp,xfq,(Tvoid,nil)) ->
 Some ret=BuildintRet i intspec(fun _:hid=>false)si Inv0 li t nil ->
 (0<=Int.unsigned id<Z.of_nat INUM)%Z ->i=Z.to_nat(Int.unsigned id) ->
 InfRules Spec V293_scheduler li Inv0 arfalse ret(V293_common_dispatch_entry i si t)
 (V293_irq_source_wrapper enter exit id)Afalse t.
Proof.
 intros Spec enter exit intspec i si t ret id Types Enter Exit Ret Bound Index.
 unfold V293_common_dispatch_entry;apply disj_rule;apply pure_split_rule.
 - intro Valid;eapply V293_interrupt_bound_changed_continuous with(intspec:=intspec);try eassumption;reflexivity.
 - intros[Valid Current];eapply V293_interrupt_common_same_continuous with(intspec:=intspec);try eassumption;reflexivity.
Qed.
End CommonDispatch.
