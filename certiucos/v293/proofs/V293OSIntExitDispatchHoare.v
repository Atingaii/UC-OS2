(* The actual dispatch on ONE opened resource state. The interrupt wrapper,
   its arbitrary ISR context, and its function builders are not included. *)
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitHandoffHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBoundarySwitch.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStoragePrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStorageTail.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedShared.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCritical.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitch.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Lemma V293_handoff_cast : forall x b n rest s,
 n<256 ->s |= V293_handoff_byte x b n ** rest ->
 evalval(ecast(evar x)Tint32)(getsmem s)=Some(V293_byteval n) /\
 evaltype(ecast(evar x)Tint32)(getsmem s)=Some Tint32.
Proof.
 intros x b n rest s Bound Held.
 destruct(V293_handoff_byte_read x b n rest s Bound Held)as[V T].
 destruct s as[[[[[[ge le]M]ir]aux]O]op].
 cbn[getsmem get_smem evalval evaltype]in V,T|-*.
 rewrite V,T. split;reflexivity.
Qed.
Lemma V293_handoff_comparison : forall high current bh bc nh nc rest s,
 nh<256 ->nc<256 ->
 s |= V293_handoff_byte high bh nh ** (V293_handoff_byte current bc nc ** rest) ->
 evalval(V293_OSSched_different high current)(getsmem s)=
 Some(Vint32(if Nat.eqb nh nc then Int.zero else Int.one)) /\
 evaltype(V293_OSSched_different high current)(getsmem s)=Some Tint32.
Proof.
 intros high current bh bc nh nc rest s Hnh Hnc Held.
 destruct(V293_handoff_cast high bh nh _ s Hnh Held)as[Eh Th].
 assert(C:s |= V293_handoff_byte current bc nc ** Atrue)by(clear -Held;sep auto).
 destruct(V293_handoff_cast current bc nc Atrue s Hnc C)as[Ec Tc].
 unfold V293_OSSched_different;destruct s as[[[[[[ge le]M]ir]aux]O]op].
 cbn[getsmem get_smem evalval evaltype]in Eh,Th,Ec,Tc|-*.
 rewrite Eh,Ec,Th,Tc. unfold V293_byteval;cbn[bop_eval val_eq bop_type].
 rewrite V293_byte_eq by assumption.
 destruct(Nat.eqb nh nc);split;reflexivity.
Qed.

Section Dispatch.
Variables unmap group rows high table target current counter : var.
Variables bt bg br bh bp bo bc bk : block.
Variable tp:type.
Variables lo hi nc:nat.
Variable entries:list val.
Variable rest:list(addr*type).
Variable tid:Modules.tid.
Variable tasks:TcbMod.map.
Variable events:EcbMod.map.
Variable now:int32.
Variable aop:spec_code.
Variable stack:list hid.
Variable critical:list bool.
Variable px:asrt.
Let nh:=V293_ready_select lo hi(V293_ready_group lo hi).
Let arrays:=V293_input_cells bt bg br ++ V293_array_cells bp 0 4(Tptr tp)(length entries) ++ rest.
Let cells:=((bk,0%Z),Tint32)::((bh,0%Z),Tint8)::((bc,0%Z),Tint8)::arrays.
Let inv:=V293_storage_inv cells target tp.
Let bindings:=V293_sched_globals unmap group rows high bt bg br bh **
 V293_prefix_bindings table high target tp bp bo.
Let private:=bindings ** (px ** Atrue).
Let kept c:=V293_handoff_byte current bc nc ** (V293_counter_cell counter bk c ** V293_storage rest).
Let reserve:=V293_handoff_binding high bh ** px.
Definition V293_exit_dispatch_entry old c:=
 V293_retained_storage_prefix_borrowed unmap group rows high table target bt bg br bh bp bo tp
 lo hi entries(kept c)tid tasks events now(sched;;aop)stack critical reserve old.
Let middle c:=V293_retained_storage_prefix_returned unmap group rows high table target bt bg br bh bp bo tp
 lo hi entries(kept c)tid tasks events now(sched;;aop)stack critical reserve.
Definition V293_exit_dispatch_tail next c:=
 V293_exit_handoff_tail high current counter target bh bc bk tp arrays tid tasks events now next
 aop stack critical private nh nc c.
Definition V293_exit_dispatch_resumed:=
 V293_exit_handoff_resumed high current counter target bh bc bk tp arrays tid aop stack critical private.

Lemma V293_exit_dispatch_open : forall c,
 lo<256 ->hi<256 ->
 Forall(fun v=>rule_type_val_match(Tptr tp)v=true)entries ->
 middle c ==> EX next:Modules.tid,[|V293_highest_ready tasks next|] ** V293_exit_dispatch_tail next c.
Proof.
 intros c Hlo Hhi Hptr s[next Held]. exists next.
 unfold V293_retained_prefix_returned,V293_retained_prefix_physical in Held.
 assert(Heap:s |=
 (V293_inputs_full bt bg br lo hi ** (V293_array true bp 0 4(Tptr tp)entries ** V293_storage rest)) **
 ([|V293_highest_ready tasks next|] **
 (<||sched;;aop||> ** ((V293_storage_open target tp tid tasks events now next ** CurTid tid) **
 ((Ais stack ** Acs critical) **
 (V293_handoff_byte high bh nh ** (V293_handoff_byte current bc nc **
 (V293_counter_cell counter bk c ** private)))))))).
 { unfold V293_exit_dispatch_tail,V293_handoff_byte,kept,reserve,private,bindings,nh in *.
   clear -Held;sep auto. }
 assert(ReturnArrays:V293_inputs_full bt bg br lo hi **
 (V293_array true bp 0 4(Tptr tp)entries ** V293_storage rest) ==> V293_storage arrays).
 { intros st H. eapply astar_mono in H.
   2: {apply V293_inputs_to_storage;assumption. }
   2: {apply astar_mono;[apply V293_array_to_storage;exact Hptr|intros s0 H0;exact H0]. }
   unfold arrays;apply V293_storage_append.
   eapply astar_mono;[intros s0 H0;exact H0|apply V293_storage_append|exact H]. }
 eapply astar_mono in Heap;[ |exact ReturnArrays|intros st H;exact H].
 unfold V293_exit_dispatch_tail,V293_exit_handoff_tail;clear -Heap;sep auto.
Qed.
Lemma V293_exit_dispatch_guard : forall next c s,
 lo<256 ->hi<256 ->(exists p,V293_bitmap_ready lo hi p) ->nc<256 ->
 s |= V293_exit_dispatch_tail next c ->
 evalval(V293_OSSched_different high current)(getsmem s)=
 Some(Vint32(if Nat.eqb nh nc then Int.zero else Int.one)) /\
 evaltype(V293_OSSched_different high current)(getsmem s)=Some Tint32.
Proof.
 intros next c s Hlo Hhi Ready Hnc Held.
 eapply V293_handoff_comparison with(bh:=bh)(bc:=bc)(rest:=Atrue).
 - unfold nh;pose proof(V293_ready_selection_range lo hi(V293_ready_group lo hi)Hlo Hhi eq_refl Ready);lia.
 - exact Hnc.
 - unfold V293_exit_dispatch_tail,V293_exit_handoff_tail in Held;clear -Held;sep auto.
Qed.
Theorem V293_OSIntExit_changed_dispatch : forall Spec r ri sched_id old c,
 lo<256 ->hi<256 ->(exists p,V293_bitmap_ready lo hi p) ->nc<256 ->nh<>nc ->
 V293_bitmap_tasks lo hi tasks ->V293_priority_table entries tasks ->
 Forall(fun v=>rule_type_val_match(Tptr tp)v=true)entries ->
 indom tasks tid ->GoodFrm px ->(px ==> LINV V293_shared_li tid nil ** Atrue) ->
 Spec sched_id=Some
 (V293_critical_fpre unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
 V293_critical_fpost unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
 (Tvoid,nil)) ->
 InfRules Spec V293_scheduler V293_shared_li inv r ri
 (V293_exit_dispatch_entry old c)
 (V293_exit_boundary_dispatch table high target current counter sched_id
 (V293_interrupt_handoff high current target)) V293_exit_dispatch_resumed tid.
Proof.
 intros Spec r ri sched_id old c Hlo Hhi Ready Hnc Different Bitmap Htable Hptr Member Good Hlocal Callee.
 unfold V293_exit_boundary_dispatch;eapply seq_rule with(p':=middle c).
 - apply V293_retained_OSSched_storage_prefix_returned;try assumption.
   + unfold kept,V293_handoff_byte,V293_handoff_binding,V293_counter_cell,V293_counter_bindings.
     cbn[GoodFrm];repeat split;try exact I;apply V293_storage_frame_good.
   + unfold reserve,V293_handoff_binding;cbn[GoodFrm];tauto.
 - eapply conseq_rule.
   + apply V293_exit_dispatch_open;assumption.
   + intros st H;exact H.
   + apply ex_intro_rule;intro next.
     eapply conseq_rule with(p:=V293_exit_dispatch_tail next c ** [|V293_highest_ready tasks next|]).
     1: { apply astar_comm. }
     1: { intros st H;exact H. }
     apply pure_split_rule;intro Highest.
     eapply if_rule with(tp:=Tint32).
     * intros st Held. destruct(V293_exit_dispatch_guard next c st Hlo Hhi Ready Hnc Held)as[V T].
       exists(Vint32(if Nat.eqb nh nc then Int.zero else Int.one));repeat split;try assumption;discriminate.
     * eapply conseq_rule.
       -- intros st[Held _];exact Held.
       -- intros st H;exact H.
       -- apply V293_OSIntExit_changed_tail;try assumption.
          ++ unfold nh;pose proof(V293_ready_selection_range lo hi(V293_ready_group lo hi)Hlo Hhi eq_refl Ready);lia.
          ++ unfold private,bindings,V293_sched_globals,V293_prefix_bindings;cbn[GoodFrm];tauto.
          ++ intros st H. assert(P:st |= px ** Atrue)by(unfold private in H;clear -H;sep auto).
             eapply astar_mono in P;[ |exact Hlocal|intros s HS;exact HS];clear -P;sep auto.
     * eapply conseq_rule with(p:=Afalse)(q:=V293_exit_dispatch_resumed).
       -- intros st[Held FalseGuard].
          destruct(V293_exit_dispatch_guard next c st Hlo Hhi Ready Hnc Held)as[V T].
          assert(Ne:Nat.eqb nh nc=false)by(apply Nat.eqb_neq;exact Different).
          rewrite Ne in V.
          destruct FalseGuard as[v[Eval FalseVal]]. rewrite V in Eval;inversion Eval;subst v.
          vm_compute in FalseVal;discriminate.
       -- intros st H;exact H.
       -- apply pfalse_rule.
Qed.
End Dispatch.
