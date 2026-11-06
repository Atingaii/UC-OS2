(* Actual scheduler call, target read and changed guard, with ready ownership
   returned to the same invariant as the interrupt-exit suffix. *)
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

Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitDispatchHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyHandoff.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyStorageInvariant.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.

Lemma V293_owned_cells_frame : forall cells, GoodFrm(V293_owned_record_cells cells).
Proof.
 induction cells as [ | [[a tp] v] tail IH];cbn[V293_owned_record_cells];[exact I| ].
 unfold V293_owned_record_cell;cbn[GoodFrm];auto.
Qed.
Lemma V293_owned_tasks_frame : forall tasks, GoodFrm(V293_owned_task_records tasks).
Proof.
 intro tasks;unfold V293_owned_task_records.
 induction(TcbMod.lst tasks)as [ | [t [[p st] msg]] tail IH];cbn[V293_owned_task_list];[exact I| ].
 split;[ |exact IH].
 unfold V293_owned_task_record;cbn[GoodFrm];intros;split;[exact I|apply V293_owned_cells_frame].
Qed.
Lemma V293_priority_array_owned : forall entries b offset,
 Forall(fun v=>rule_type_val_match(Tptr V293_tcb_type)v=true)entries ->
 V293_array true b offset 4(Tptr V293_tcb_type)entries ==>
 V293_owned_record_cells(V293_priority_cells b offset entries).
Proof.
 intros entries b offset Types;revert offset.
 induction Types as [ | v vs Hv Types IH];intros offset st H;
 cbn[V293_array V293_priority_cells V293_owned_record_cells]in *;[exact H| ].
 eapply astar_mono;[ |apply IH|exact H].
 intros s S;unfold V293_owned_record_cell;sep auto.
Qed.
Lemma V293_retained_arrays_ready : forall bt bg br bp lo hi entries tasks rest,
 V293_ready_rel lo hi entries tasks ->
 Forall(fun v=>rule_type_val_match(Tptr V293_tcb_type)v=true)entries ->
 (V293_inputs_full bt bg br lo hi **
 (V293_array true bp 0 4(Tptr V293_tcb_type)entries **
 (V293_owned_task_records tasks ** V293_storage rest))) ==>
 V293_ready_payload br bg bp tasks **
 V293_storage(V293_array_cells bt 0 1 Tint8(length V293_ready_table)++rest).
Proof.
 intros bt bg br bp lo hi entries tasks rest Rel Types st H.
 destruct Rel as[Lo[Hi[Ready[Bitmap Table]]]].
 assert(Raw:st |=
 V293_array true bp 0 4(Tptr V293_tcb_type)entries **
 (V293_array true bt 0 1 Tint8(map V293_byteval V293_ready_table) **
 (V293_owned_task_records tasks **
 (Amapsto(br,0%Z)Tint8 true(V293_byteval lo) **
 (Amapsto(br,1%Z)Tint8 true(V293_byteval hi) **
 (Amapsto(bg,0%Z)Tint8 true(V293_byteval(V293_ready_group lo hi)) ** V293_storage rest)))))).
 { unfold V293_inputs_full in H;cbn[V293_array map]in H;clear -H;sep auto. }
 eapply astar_mono in Raw;[ |apply V293_priority_array_owned;exact Types|intros s S;exact S].
 assert(Lookup:Forall(fun v=>rule_type_val_match Tint8 v=true)(map V293_byteval V293_ready_table))
 by(vm_compute;repeat constructor).
 eapply astar_mono in Raw;[ |intros s S;exact S|apply astar_mono;
 [apply V293_array_to_storage;exact Lookup|intros s S;exact S]].
 rewrite map_length in Raw.
 assert(Pack:
 (V293_owned_task_records tasks **
 (Amapsto(br,0%Z)Tint8 true(V293_byteval lo) **
 (Amapsto(br,1%Z)Tint8 true(V293_byteval hi) **
 (Amapsto(bg,0%Z)Tint8 true(V293_byteval(V293_ready_group lo hi)) **
 V293_owned_record_cells(V293_priority_cells bp 0 entries))))) ==>
 V293_ready_payload br bg bp tasks).
 { unfold V293_ready_payload;apply astar_mono;[intros s S;exact S| ].
   intros s S;unfold V293_ready_owned;exists lo;exists hi;exists entries.
   unfold V293_ready_cells;cbn[app V293_owned_record_cells V293_owned_record_cell].
   clear H Raw;sep auto.
   - apply V293_byte_type;unfold V293_ready_group;
     destruct(Nat.eqb lo 0),(Nat.eqb hi 0);simpl;lia.
   - apply V293_byte_type;exact Hi.
   - apply V293_byte_type;exact Lo.
   - exact(conj Lo(conj Hi(conj Ready(conj Bitmap Table)))). }
 assert(Reordered:st |=
 (V293_owned_task_records tasks **
 (Amapsto(br,0%Z)Tint8 true(V293_byteval lo) **
 (Amapsto(br,1%Z)Tint8 true(V293_byteval hi) **
 (Amapsto(bg,0%Z)Tint8 true(V293_byteval(V293_ready_group lo hi)) **
 V293_owned_record_cells(V293_priority_cells bp 0 entries))))) **
 (V293_storage(V293_array_cells bt 0 1 Tint8(length V293_ready_table)) ** V293_storage rest)).
 { clear -Raw;sep auto. }
 assert(Owned:st |= V293_ready_payload br bg bp tasks **
 (V293_storage(V293_array_cells bt 0 1 Tint8(length V293_ready_table)) ** V293_storage rest)).
 { eapply astar_mono;[exact Pack|intros s S;exact S|exact Reordered]. }
 eapply astar_mono;[intros s S;exact S|apply V293_storage_append|exact Owned].
Qed.
Section Dispatch.
Variables unmap group rows high table target current counter : var.
Variables bt bg br bh bp bo bc bk : block.
Let tp:=V293_tcb_type.
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
Let arrays:=V293_array_cells bt 0 1 Tint8(length V293_ready_table) ++ rest.
Let cells:=((bk,0%Z),Tint32)::((bh,0%Z),Tint8)::((bc,0%Z),Tint8)::arrays.
Let inv:=V293_ready_storage_inv br bg bp target tp cells.
Let bindings:=V293_sched_globals unmap group rows high bt bg br bh **
 V293_prefix_bindings table high target tp bp bo.
Let private:=bindings ** (px ** Atrue).
Let kept c:=V293_handoff_byte current bc nc ** (V293_counter_cell counter bk c ** V293_storage rest).
Let reserve:=V293_handoff_binding high bh ** (V293_owned_task_records tasks ** px).
Definition V293_ready_dispatch_entry old c:=
 V293_retained_storage_prefix_borrowed unmap group rows high table target bt bg br bh bp bo tp
 lo hi entries(kept c)tid tasks events now(sched;;aop)stack critical reserve old.
Let middle c:=V293_retained_storage_prefix_returned unmap group rows high table target bt bg br bh bp bo tp
 lo hi entries(kept c)tid tasks events now(sched;;aop)stack critical reserve.
Definition V293_ready_dispatch_tail next c:=
 V293_ready_exit_tail br bg bp high current counter target bh bc bk tp arrays tid tasks events now next
 aop stack critical private nh nc c.
Definition V293_ready_dispatch_resumed:=
 V293_ready_exit_resumed br bg bp high current counter target bh bc bk tp arrays tid aop stack critical private.

Lemma V293_ready_dispatch_open : forall c,
 V293_ready_rel lo hi entries tasks ->
 Forall(fun v=>rule_type_val_match(Tptr tp)v=true)entries ->
 middle c ==> EX next:Modules.tid,[|V293_highest_ready tasks next|] ** V293_ready_dispatch_tail next c.
Proof.
 intros c Rel Types s[next Held];exists next.
 unfold V293_retained_prefix_returned,V293_retained_prefix_physical in Held.
 assert(Heap:s |=
 (V293_inputs_full bt bg br lo hi ** (V293_array true bp 0 4(Tptr tp)entries **
 (V293_owned_task_records tasks ** V293_storage rest))) **
 ([|V293_highest_ready tasks next|] **
 (<||sched;;aop||> ** ((V293_storage_open target tp tid tasks events now next ** CurTid tid) **
 ((Ais stack ** Acs critical) **
 (V293_handoff_byte high bh nh ** (V293_handoff_byte current bc nc **
 (V293_counter_cell counter bk c ** private)))))))).
 { unfold V293_handoff_byte,kept,reserve,private,bindings,nh in *;clear -Held;sep auto. }
 eapply astar_mono in Heap;[ |apply V293_retained_arrays_ready;assumption|intros st H;exact H].
 unfold V293_ready_dispatch_tail,V293_ready_exit_tail;clear -Heap;sep auto.
Qed.
Lemma V293_ready_dispatch_guard : forall next c s,
 lo<256 ->hi<256 ->(exists p,V293_bitmap_ready lo hi p) ->nc<256 ->
 s |= V293_ready_dispatch_tail next c ->
 evalval(V293_OSSched_different high current)(getsmem s)=
 Some(Vint32(if Nat.eqb nh nc then Int.zero else Int.one)) /\
 evaltype(V293_OSSched_different high current)(getsmem s)=Some Tint32.
Proof.
 intros next c s Hlo Hhi Ready Hnc Held.
 eapply V293_handoff_comparison with(bh:=bh)(bc:=bc)(rest:=Atrue).
 - unfold nh;pose proof(V293_ready_selection_range lo hi(V293_ready_group lo hi)Hlo Hhi eq_refl Ready);lia.
 - exact Hnc.
 - unfold V293_ready_dispatch_tail,V293_ready_exit_tail in Held;clear -Held;sep auto.
Qed.
Theorem V293_OSIntExit_ready_dispatch : forall Spec r ri sched_id old c,
 lo<256 ->hi<256 ->(exists p,V293_bitmap_ready lo hi p) ->nc<256 ->nh<>nc ->
 V293_bitmap_tasks lo hi tasks ->V293_priority_table entries tasks ->
 Forall(fun v=>rule_type_val_match(Tptr tp)v=true)entries ->
 indom tasks tid ->GoodFrm px ->(px ==> LINV V293_shared_li tid nil ** Atrue) ->
 Spec sched_id=Some
 (V293_critical_fpre unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
 V293_critical_fpost unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
 (Tvoid,nil)) ->
 InfRules Spec V293_scheduler V293_shared_li inv r ri
 (V293_ready_dispatch_entry old c)
 (V293_exit_boundary_dispatch table high target current counter sched_id
 (V293_interrupt_handoff high current target)) V293_ready_dispatch_resumed tid.
Proof.
 intros Spec r ri sched_id old c Hlo Hhi Ready Hnc Different Bitmap Htable Hptr Member Good Hlocal Callee.
 unfold V293_exit_boundary_dispatch;eapply seq_rule with(p':=middle c).
 - apply V293_retained_OSSched_storage_prefix_returned;try assumption.
   + unfold kept,V293_handoff_byte,V293_handoff_binding,V293_counter_cell,V293_counter_bindings.
     cbn[GoodFrm];repeat split;try exact I;apply V293_storage_frame_good.
   + unfold reserve,V293_handoff_binding;cbn[GoodFrm];repeat split;try exact I;[apply V293_owned_tasks_frame|exact Good].
 - eapply conseq_rule.
   + apply V293_ready_dispatch_open;[exact(conj Hlo(conj Hhi(conj Ready(conj Bitmap Htable))))|exact Hptr].
   + intros st H;exact H.
   + apply ex_intro_rule;intro next.
     eapply conseq_rule with(p:=V293_ready_dispatch_tail next c ** [|V293_highest_ready tasks next|]).
     1: { apply astar_comm. }
     1: { intros st H;exact H. }
     apply pure_split_rule;intro Highest.
     eapply if_rule with(tp:=Tint32).
     * intros st Held. destruct(V293_ready_dispatch_guard next c st Hlo Hhi Ready Hnc Held)as[V T].
       exists(Vint32(if Nat.eqb nh nc then Int.zero else Int.one));repeat split;try assumption;discriminate.
     * eapply conseq_rule.
       -- intros st[Held _];exact Held.
       -- intros st H;exact H.
       -- apply V293_ready_exit_changed_tail;try assumption.
          ++ unfold nh;pose proof(V293_ready_selection_range lo hi(V293_ready_group lo hi)Hlo Hhi eq_refl Ready);lia.
          ++ unfold private,bindings,V293_sched_globals,V293_prefix_bindings;cbn[GoodFrm];tauto.
          ++ intros st H. assert(P:st |= px ** Atrue)by(unfold private in H;clear -H;sep auto).
             eapply astar_mono in P;[ |exact Hlocal|intros s HS;exact HS];clear -P;sep auto.
     * eapply conseq_rule with(p:=Afalse)(q:=V293_ready_dispatch_resumed).
       -- intros st[Held FalseGuard].
          destruct(V293_ready_dispatch_guard next c st Hlo Hhi Ready Hnc Held)as[V T].
          assert(Ne:Nat.eqb nh nc=false)by(apply Nat.eqb_neq;exact Different).
          rewrite Ne in V.
          destruct FalseGuard as[v[Eval FalseVal]]. rewrite V in Eval;inversion Eval;subst v.
          vm_compute in FalseVal;discriminate.
       -- intros st H;exact H.
       -- apply pfalse_rule.
Qed.
End Dispatch.
