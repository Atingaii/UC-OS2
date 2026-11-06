Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitResourceBridge.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitUnifiedInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedExactLocal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedShared.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCritical.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedDispatchShared.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.code.V293OSSchedDispatch.
Require Import CertiOS.tactics.sepauto.sep_combine_lemmas.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitDispatchHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyDispatch.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyBody.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitChangedBody.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterInternal.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBody.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitNondispatch.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitDispatch.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickDelayHoare.
(* Local-invariant parametric proof of the unchanged ready dispatch suffix. *)
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBoundarySwitch.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStorageTail.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStoragePrefix.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitch.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitchPre.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrent.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitHandoffHoare.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyStorageInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyHandoff.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptBindings.
Section LocalHandoff.
Variable li:LocalInv.
Variables br bg bp : block.
Variables high current counter target : var.
Variables bh bc bk : block.
Variable tp : type.
Variable rest : list (addr * type).
Variable tid : Modules.tid.
Variable tasks : TcbMod.map.
Variable events : EcbMod.map.
Variable now : int32.
Variable next : Modules.tid.
Variable aop : spec_code.
Variable stack : list hid.
Variable critical : list bool.
Variable px : asrt.
Let bytecells := ((bh,0%Z),Tint8)::((bc,0%Z),Tint8)::rest.
Let cells := ((bk,0%Z),Tint32)::bytecells.
Let inv := V293_ready_storage_inv br bg bp target tp cells.
Let private := V293_counter_bindings counter bk **
 ((V293_handoff_binding high bh ** V293_handoff_binding current bc) ** px).
Local Notation tail := (V293_ready_exit_tail br bg bp high current counter target bh bc bk tp rest tid tasks events now next aop stack critical px).
Local Notation resumed := (V293_ready_exit_resumed br bg bp high current counter target bh bc bk tp rest tid aop stack critical px).
Local Notation payload := (V293_ready_exit_switch_payload br bg bp target bh bc bk tp rest tid tasks events now next aop stack critical).
Lemma V293_local_exit_current :
 (px ==> LINV li tid nil ** Atrue) ->
 CurTid tid ** px ==> CurLINV li tid.
Proof.
 intros Local st H;unfold CurLINV;exists(nil:list logicvar).
 eapply astar_mono in H;[ |intros s HS;exact HS|exact Local];clear -H;sep auto.
Qed.
Theorem V293_local_exit_increment : forall Spec r ri nh nc c,
 (px ==> LINV li tid nil ** Atrue) ->
 InfRules Spec V293_scheduler li inv r ri
 (tail nh nc c)(V293_OSSched_increment counter)
 (tail nh nc(Int.add c Int.one))tid.
Proof.
 intros Spec r ri nh nc c Local.
 eapply conseq_rule with
 (p:=<||sched;;aop||> **
 (((V293_storage_open target tp tid tasks events now next ** CurTid tid) **
 ((Ais stack ** Acs critical) **
 (V293_handoff_byte high bh nh ** (V293_handoff_byte current bc nc **
 (V293_ready_payload br bg bp tasks ** (V293_storage rest ** px)))))) ** V293_counter_cell counter bk c))
 (q:=<||sched;;aop||> **
 (((V293_storage_open target tp tid tasks events now next ** CurTid tid) **
 ((Ais stack ** Acs critical) **
 (V293_handoff_byte high bh nh ** (V293_handoff_byte current bc nc **
 (V293_ready_payload br bg bp tasks ** (V293_storage rest ** px)))))) ** V293_counter_cell counter bk(Int.add c Int.one))).
 - unfold V293_ready_exit_tail;intros st H;sep auto.
 - unfold V293_ready_exit_tail;intros st H;sep auto.
 - apply V293_OSSched_counter_increment;intros st H;apply V293_CurLINV_extend with(extra:=Atrue).
   eapply astar_mono;[apply V293_local_exit_current;exact Local|intros s HS;exact HS| ]. clear -H;sep auto.
Qed.
Theorem V293_local_exit_copy : forall Spec r ri nh nc c,
 nh<256 ->(px ==> LINV li tid nil ** Atrue) ->
 InfRules Spec V293_scheduler li inv r ri
 (tail nh nc c)(sassign(evar current)(evar high))
 (tail nh nh c)tid.
Proof.
 intros Spec r ri nh nc c Bound Local.
 eapply conseq_rule with
 (p:=<||sched;;aop||> ** (V293_handoff_byte current bc nc **
 (V293_handoff_byte high bh nh **
 ((V293_storage_open target tp tid tasks events now next ** CurTid tid) **
 ((Ais stack ** Acs critical) ** (V293_counter_cell counter bk c ** (V293_ready_payload br bg bp tasks ** (V293_storage rest ** px))))))))
 (q:=<||sched;;aop||> ** (V293_handoff_byte current bc nh **
 (V293_handoff_byte high bh nh **
 ((V293_storage_open target tp tid tasks events now next ** CurTid tid) **
 ((Ais stack ** Acs critical) ** (V293_counter_cell counter bk c ** (V293_ready_payload br bg bp tasks ** (V293_storage rest ** px)))))))).
 - unfold V293_ready_exit_tail;intros st H;sep auto.
 - unfold V293_ready_exit_tail;intros st H;sep auto.
 - apply V293_handoff_byte_copy;[exact Bound| ].
   intros st H;apply V293_CurLINV_extend with(extra:=Atrue).
   eapply astar_mono;[apply V293_local_exit_current;exact Local|intros s HS;exact HS| ]. clear -H;sep auto.
Qed.
Theorem V293_local_exit_handoff : forall Spec r ri nh nc c,
 nh<256 ->indom tasks tid ->V293_highest_ready tasks next ->GoodFrm px ->
 (px ==> LINV li tid nil ** Atrue) ->
 InfRules Spec V293_scheduler li inv r ri
 (tail nh nc c)(V293_interrupt_handoff high current target)
 resumed tid.
Proof.
 intros Spec r ri nh nc c Bound Member Highest Good Local.
 unfold V293_interrupt_handoff;eapply seq_rule with(p':=tail nh nh c).
 - apply V293_local_exit_copy;assumption.
 - unfold V293_ready_exit_resumed;eapply switch_rule with
 (P':=payload nh nh c)(Px:=private)(lg:=nil).
 + unfold private,V293_handoff_binding,V293_counter_bindings;cbn[GoodFrm];tauto.
 + apply V293_ready_exit_split.
 + apply V293_ready_exit_close;assumption.
 + apply V293_ready_exit_switch_pre;assumption.
 + unfold private;intros st H.
   assert(P:st |= px ** Atrue)by(clear -H;sep auto).
   eapply astar_mono in P;[ |exact Local|intros s HS;exact HS];clear -P;sep auto.
Qed.
Theorem V293_local_exit_changed_tail : forall Spec r ri nh nc c,
 nh<256 ->indom tasks tid ->V293_highest_ready tasks next ->GoodFrm px ->
 (px ==> LINV li tid nil ** Atrue) ->
 InfRules Spec V293_scheduler li inv r ri
 (tail nh nc c)
 (sseq(V293_OSSched_increment counter)
 (sseq(sskip None)(V293_interrupt_handoff high current target)))
 resumed tid.
Proof.
 intros Spec r ri nh nc c Bound Member Highest Good Local.
 eapply seq_rule with(p':=tail nh nc(Int.add c Int.one)).
 - apply V293_local_exit_increment;exact Local.
 - eapply seq_rule with(p':=tail nh nc(Int.add c Int.one)).
 + apply skip_rule.
 + apply V293_local_exit_handoff;assumption.
Qed.
End LocalHandoff.

Require Import CertiOS.certiucos.v293.proofs.V293OSSchedExactPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitExact.
Section LocalStoragePrefix.
Variable li:LocalInv.
Variable Hli:GoodLInvAsrt li.
Variables unmap group rows high table target : var.
Variables bt bg br bh bp bo : block.
Variable tp : type.
Variables lo hi : nat.
Variable entries : list val.
Variable kept : asrt.
Variable tid : Modules.tid.
Variable tasks : TcbMod.map.
Variable events : EcbMod.map.
Variable now : int32.
Variable aop : spec_code.
Variable stack : list hid.
Variable critical : list bool.
Variable px : asrt.
(* This is an OPENED borrowing boundary. The old target and the callee's
   initial output value are not claimed reachable from initialization. *)
Definition V293_local_storage_prefix_borrowed old :=
  (V293_sched_exact_pre unmap group rows high bt bg br bh lo hi li tid aop **
    V293_sched_critical V293_opened_inv stack critical) **
  (V293_prefix_frame table high target tp bp bo entries tasks
    (V293_shared_remainder tid events now ** V293_retained_prefix_reserve bt bg br bp tp lo hi entries kept px) ** V293_prefix_output tp bo old).
Definition V293_local_storage_prefix_returned :=
  EX next : Modules.tid, [|V293_highest_ready tasks next|] **
  ((<||aop||> ** ((V293_retained_prefix_returned target bt bg br bh bp tp lo hi entries kept tid tasks events now next ** p_local li tid nil) ** (Ais stack ** Acs critical))) **
    ((V293_sched_globals unmap group rows high bt bg br bh **
      V293_prefix_bindings table high target tp bp bo) ** px)).

Theorem V293_OSSched_local_storage_prefix_returned : forall Spec (RI : Inv) r ri sched_id old,
  GoodFrm kept ->
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks ->
  GoodFrm px ->
  Spec sched_id = Some
    (V293_sched_exact_fpre unmap group rows high bt bg br bh li V293_opened_inv Hli,
     V293_sched_exact_fpost unmap group rows high bt bg br bh li V293_opened_inv Hli,
     (Tvoid, nil)) ->
  InfRules Spec V293_scheduler li RI r ri
    (V293_local_storage_prefix_borrowed old)
    (V293_OSSched_unlocked_prefix sched_id table high target)
    V293_local_storage_prefix_returned tid.
Proof.
  intros Spec RI r ri sched_id old Hkept Hlo Hhi Hr Hb Htable Hpx Hspec.
  eapply conseq_rule.
  3: { eapply V293_OSSched_exact_critical_prefix with
      (I := V293_opened_inv) (Hli := Hli)
      (frame := V293_shared_remainder tid events now ** V293_retained_prefix_reserve bt bg br bp tp lo hi entries kept px)
      (unmap := unmap) (group := group) (rows := rows) (bt := bt) (bg := bg) (br := br) (bh := bh)
      (lo := lo) (hi := hi) (tp := tp) (bp := bp) (bo := bo) (entries := entries) (tasks := tasks)
      (aop := aop) (old := old) (stack := stack) (critical := critical); try eassumption.
    split; [apply V293_shared_remainder_good | ].
    unfold V293_retained_prefix_reserve, V293_sched_inputs.
    repeat rewrite V293_read_bytes_array. rewrite V293_read_pointers_array.
    repeat split; try apply V293_array_good; try exact Hkept; try exact I; exact Hpx. }
  - intros s Hs. exact Hs.
  - intros s [next Hs]. unfold V293_local_storage_prefix_returned. exists next.
    unfold V293_sched_exact_post, V293_sched_exact_resource,
      V293_prefix_frame, V293_shared_remainder, V293_retained_prefix_reserve, V293_sched_critical in Hs.
    sep normal in Hs. sep split in Hs.
    assert (HP : s |= SWINV V293_opened_inv **
      ([|V293_highest_ready tasks next|] **
        ((V293_prefix_bindings table high target tp bp bo ** V293_prefix_output tp bo (Vptr next)) **
          ((CurTid tid ** V293_shared_fields tid tasks events now) **
            ((V293_sched_inputs bt bg br lo hi (V293_ready_group lo hi) **
              V293_sched_inputs bt bg br lo hi (V293_ready_group lo hi)) **
              ((V293_read_pointers tp bp 0 entries ** V293_read_pointers tp bp 0 entries) **
                ((PV (bh, Int.zero) @ Tint8 |->
                  (V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi)))) **
                  (kept **
                    ((<||aop||> ** p_local li tid nil) ** ((Ais stack ** Acs critical) **
                      (V293_sched_globals unmap group rows high bt bg br bh ** px)))))))))))
      by (unfold V293_shared_fields; sep auto).
    eapply astar_mono in HP; [ | apply V293_opened_switch_open | intros st Hz; exact Hz].
    assert (HK : s |=
      ((V293_prefix_bindings table high target tp bp bo ** V293_prefix_output tp bo (Vptr next)) **
        ((V293_sched_inputs bt bg br lo hi (V293_ready_group lo hi) **
          V293_sched_inputs bt bg br lo hi (V293_ready_group lo hi)) **
          (V293_read_pointers tp bp 0 entries ** V293_read_pointers tp bp 0 entries))) **
      (V293_shared_flags ** ([|V293_highest_ready tasks next|] **
        ((CurTid tid ** V293_shared_fields tid tasks events now) **
          ((PV (bh, Int.zero) @ Tint8 |->
            (V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi)))) **
            (kept **
              ((<||aop||> ** p_local li tid nil) ** ((Ais stack ** Acs critical) **
                (V293_sched_globals unmap group rows high bt bg br bh ** px)))))))))
      by (clear Hs; sep auto).
    eapply astar_mono in HK.
    2: { apply astar_mono; [apply V293_dispatch_output_named | apply astar_mono].
         - apply V293_inputs_reunite.
         - rewrite V293_read_pointers_array. apply V293_array_reunite. }
    2: { intros st Hz; exact Hz. }
    assert (HL : s |= V293_retained_prefix_returned target bt bg br bh bp tp lo hi entries kept tid tasks events now next **
      ([|V293_highest_ready tasks next|] **
        ((<||aop||> ** p_local li tid nil) ** ((Ais stack ** Acs critical) **
          ((V293_sched_globals unmap group rows high bt bg br bh **
            V293_prefix_bindings table high target tp bp bo) ** px)))))
      by (unfold V293_retained_prefix_returned, V293_storage_open, V293_retained_prefix_physical; clear Hs HP; sep auto).
    clear Hs HP HK. sep auto.
Qed.
End LocalStoragePrefix.
Section LocalDispatch.
Variable li:LocalInv.
Variable Hli:GoodLInvAsrt li.
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
Let private:=bindings ** px.
Let kept c:=V293_handoff_byte current bc nc ** (V293_counter_cell counter bk c ** V293_storage rest).
Let reserve:=V293_handoff_binding high bh ** (V293_owned_task_records tasks ** px).
Definition V293_exit_local_dispatch_entry old c:=
 V293_local_storage_prefix_borrowed li unmap group rows high table target bt bg br bh bp bo tp
 lo hi entries(kept c)tid tasks events now(sched;;aop)stack critical reserve old.
Let middle c:=V293_local_storage_prefix_returned li unmap group rows high table target bt bg br bh bp bo tp
 lo hi entries(kept c)tid tasks events now(sched;;aop)stack critical reserve.
Local Notation tail := (V293_exit_exact_dispatch_tail unmap group rows high table target current counter bt bg br bh bp bo bc bk lo hi nc rest tid tasks events now aop stack critical px).
Local Notation resumed := (V293_exit_exact_dispatch_resumed unmap group rows high table target current counter bt bg br bh bp bo bc bk rest tid aop stack critical px).
Lemma V293_local_dispatch_return_forget : forall c,
 (p_local li tid nil ==>p_local V293_shared_li tid nil) ->
 middle c ==>V293_exact_storage_prefix_returned unmap group rows high table target bt bg br bh bp bo tp lo hi entries(kept c)tid tasks events now(sched;;aop)stack critical reserve.
Proof.
 intros c Forget s[next H];exists next.
 unfold V293_local_storage_prefix_returned in H.
 eapply astar_mono in H;[ |intros st S;exact S|apply astar_mono;
 [apply astar_mono;[intros st S;exact S|apply astar_mono;
 [apply astar_mono;[intros st S;exact S|exact Forget]|intros st S;exact S]]|intros st S;exact S]].
 exact H.
Qed.
Lemma V293_local_dispatch_guard : forall next c s,
 lo<256 ->hi<256 ->(exists p,V293_bitmap_ready lo hi p) ->nc<256 ->
 s |= tail next c ->
 evalval(V293_OSSched_different high current)(getsmem s)=
 Some(Vint32(if Nat.eqb nh nc then Int.zero else Int.one)) /\
 evaltype(V293_OSSched_different high current)(getsmem s)=Some Tint32.
Proof.
 intros next c s Hlo Hhi Ready Hnc Held.
 eapply V293_handoff_comparison with(bh:=bh)(bc:=bc)(rest:=Atrue).
 - unfold nh;pose proof(V293_ready_selection_range lo hi(V293_ready_group lo hi)Hlo Hhi eq_refl Ready);lia.
 - exact Hnc.
 - unfold V293_exit_exact_dispatch_tail,V293_ready_exit_tail in Held;clear -Held;sep auto.
Qed.
Theorem V293_OSIntExit_local_dispatch : forall Spec r ri sched_id old c,
 lo<256 ->hi<256 ->(exists p,V293_bitmap_ready lo hi p) ->nc<256 ->nh<>nc ->
 V293_bitmap_tasks lo hi tasks ->V293_priority_table entries tasks ->
 Forall(fun v=>rule_type_val_match(Tptr tp)v=true)entries ->
 indom tasks tid ->GoodFrm px ->
 (px ==> LINV li tid nil ** Atrue) ->
 (p_local li tid nil ==>p_local V293_shared_li tid nil) ->
 Spec sched_id=Some
 (V293_sched_exact_fpre unmap group rows high bt bg br bh li V293_opened_inv Hli,
 V293_sched_exact_fpost unmap group rows high bt bg br bh li V293_opened_inv Hli,
 (Tvoid,nil)) ->
 InfRules Spec V293_scheduler li inv r ri
 (V293_exit_local_dispatch_entry old c)
 (V293_exit_boundary_dispatch table high target current counter sched_id
 (V293_interrupt_handoff high current target)) resumed tid.
Proof.
 intros Spec r ri sched_id old c Hlo Hhi Ready Hnc Different Bitmap Htable Hptr Member Good Local Forget Callee.
 unfold V293_exit_boundary_dispatch;eapply seq_rule with(p':=middle c).
 - apply V293_OSSched_local_storage_prefix_returned with(Hli:=Hli);try assumption.
   + unfold kept,V293_handoff_byte,V293_handoff_binding,V293_counter_cell,V293_counter_bindings.
     cbn[GoodFrm];repeat split;try exact I;apply V293_storage_frame_good.
   + unfold reserve,V293_handoff_binding;cbn[GoodFrm];repeat split;try exact I;[apply V293_owned_tasks_frame|exact Good].
 - eapply conseq_rule.
   + intros st H;eapply V293_exit_exact_dispatch_open;[exact(conj Hlo(conj Hhi(conj Ready(conj Bitmap Htable))))|exact Hptr| ].
     eapply V293_local_dispatch_return_forget;[exact Forget|exact H].
   + intros st H;exact H.
   + apply ex_intro_rule;intro next.
     eapply conseq_rule with(p:=tail next c ** [|V293_highest_ready tasks next|]).
     1: { apply astar_comm. }
     1: { intros st H;exact H. }
     apply pure_split_rule;intro Highest.
     eapply if_rule with(tp:=Tint32).
     * intros st Held. destruct(V293_local_dispatch_guard next c st Hlo Hhi Ready Hnc Held)as[V T].
       exists(Vint32(if Nat.eqb nh nc then Int.zero else Int.one));repeat split;try assumption;discriminate.
     * eapply conseq_rule.
       -- intros st[Held _];exact Held.
       -- intros st H;exact H.
       -- apply V293_local_exit_changed_tail;try assumption.
          ++ unfold nh;pose proof(V293_ready_selection_range lo hi(V293_ready_group lo hi)Hlo Hhi eq_refl Ready);lia.
          ++ unfold private,bindings,V293_sched_globals,V293_prefix_bindings;cbn[GoodFrm];tauto.
          ++ intros st H. assert(P:st |= px ** Atrue)by(unfold private in H;clear -H;sep auto).
             eapply astar_mono in P;[ |exact Local|intros s HS;exact HS];clear -P;sep auto.
     * eapply conseq_rule with(p:=Afalse)(q:=resumed).
       -- intros st[Held FalseGuard].
          destruct(V293_local_dispatch_guard next c st Hlo Hhi Ready Hnc Held)as[V T].
          assert(Ne:Nat.eqb nh nc=false)by(apply Nat.eqb_neq;exact Different).
          rewrite Ne in V.
          destruct FalseGuard as[v[Eval FalseVal]]. rewrite V in Eval;inversion Eval;subst v.
          vm_compute in FalseVal;discriminate.
       -- intros st H;exact H.
       -- apply pfalse_rule.
Qed.
End LocalDispatch.

Section BoundDispatch.
Variables unmap group rows high table target current counter running nesting lock saved:var.
Variables bt bg br bh bp bo bc bk brun bn bl bs:block.
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
Variable extra:asrt.
Let tp:=V293_tcb_type.
Let li:=V293_irq_bound_li running nesting lock brun bn bl.
Let Hli:=V293_irq_bound_good running nesting lock brun bn bl.
Let globals:=V293_quiet_globals running nesting lock brun bn bl.
Let returned:= [((brun,0%Z),Tint8);((bn,0%Z),Tint8);((bl,0%Z),Tint8)]++rest.
Let bindings:=V293_exit_ready_body_bindings nesting lock bn bl **
 (V293_handoff_binding running brun ** (V293_time_cell true saved bs(Vint32 Int.zero) ** extra)).
Local Notation bodydata := (V293_exit_ready_body_data unmap group rows high table target current counter running nesting lock saved bt bg br bh bp bo bc bk brun bn bl bs lo hi nc entries rest tid tasks events now extra).
Definition V293_exit_bound_dispatch_entry old c:=
 V293_exit_local_dispatch_entry li unmap group rows high table target current counter bt bg br bh bp bo bc bk lo hi nc entries returned tid tasks events now aop stack critical bindings old c.
Definition V293_exit_bound_dispatch_resumed:=
 V293_exit_exact_dispatch_resumed unmap group rows high table target current counter bt bg br bh bp bo bc bk returned tid aop stack critical bindings.
Lemma V293_bound_dispatch_bindings_local :
 bindings ==>LINV li tid nil ** Atrue.
Proof.
 intros st H.
 assert(N:st |=V293_quiet_bindings running nesting lock brun bn bl ** Atrue).
 { unfold bindings,V293_exit_ready_body_bindings,V293_quiet_bindings,V293_exit_guard_bindings in *;sep auto. }
 eapply astar_mono in N;[ |apply V293_quiet_forget_names|intros s S;exact S].
 unfold LINV,li,V293_irq_bound_li;fold globals in N|-*;clear -N;sep auto;apply V293_irq_bound_good.
Qed.
Lemma V293_bound_dispatch_forget :
 p_local li tid nil ==>p_local V293_shared_li tid nil.
Proof.
 intros st H.
 assert(E:LINV li tid nil ==>Aemp).
 { intros s G;unfold LINV in G;apply astar_comm in G;apply astar_l_apure_elim in G as[_ G];
   apply V293_irq_bound_empty in G;exact G. }
 unfold p_local in H;eapply astar_mono in H;[ |intros s S;exact S|exact E].
 apply V293_current_to_exact_local;clear -H;sep auto.
Qed.
Lemma V293_bound_dispatch_add_globals : forall p st,
 st |=globals ** Atrue ->st |=p ->st |=globals ** p.
Proof.
 intros p st Names Held.
 assert(G: get(getgenv st)running=Some(brun,Tint8) /\
 (get(getgenv st)nesting=Some(bn,Tint8) /\ get(getgenv st)lock=Some(bl,Tint8))).
 { eapply V293_star_env_l with(E:=fun ge le=>get ge running=Some(brun,Tint8) /\
   (get ge nesting=Some(bn,Tint8) /\ get ge lock=Some(bl,Tint8)));[ |exact Names].
   intros s[GR[GN GL]];apply agvarenv_elim in GR,GN,GL;cbn in *;tauto. }
 destruct G as[GR[GN GL]].
 assert(B:st |=Agvarenv running Tint8(brun,0%Z) ** p).
 { apply astar_l_agvarenv_intro;[exact Held|split;[reflexivity|exact GR]]. }
 destruct B as(M1&M2&M&O1&O2&O&EM&JM&EO&JO&Run&Rest).
 exists M1 M2 M O1 O2 O;split;[exact EM| ];split;[exact JM| ];
 split;[exact EO| ];split;[exact JO| ];split;[ |exact Rest].
 destruct st as [[[[[[ge le]MM]ir]aux]OO]op].
 unfold globals,V293_quiet_globals;split;[exact Run| ];split;
 apply agvarenv_intro;[exact(proj2(@agvarenv_elim _ _ _ _ Run))|split;[reflexivity|exact GN]
 |exact(proj2(@agvarenv_elim _ _ _ _ Run))|split;[reflexivity|exact GL]].
Qed.
Lemma V293_bound_dispatch_borrow : forall old c,
 globals ** V293_exit_exact_dispatch_entry unmap group rows high table target current counter
 bt bg br bh bp bo bc bk lo hi nc entries returned tid tasks events now aop stack critical bindings old c ==>
 V293_exit_bound_dispatch_entry old c.
Proof.
 intros old c st H.
 unfold V293_exit_bound_dispatch_entry,V293_exit_local_dispatch_entry,
 V293_exit_exact_dispatch_entry,V293_local_storage_prefix_borrowed,
 V293_exact_storage_prefix_borrowed,V293_sched_exact_pre,V293_sched_exact_resource in *.
 unfold p_local,LINV,li,V293_irq_bound_li,V293_shared_li in *.
 fold globals in H|-*;sep auto;apply V293_irq_bound_good.
Qed.
Theorem V293_exit_bound_body_lend : forall hv out c,
 lo<256 ->hi<256 ->(exists p,V293_bitmap_ready lo hi p) ->
 <||sched;;aop||> ** OS[(fun _:hid=>false),false,stack,critical] **
 bodydata 0 hv out c(Vint32 Int.zero) ==>V293_exit_bound_dispatch_entry out c.
Proof.
 intros hv out c Low High Ready st H.
 assert(Names:st |=globals ** Atrue).
 { assert(N:st |=V293_quiet_bindings running nesting lock brun bn bl ** Atrue).
   { unfold V293_exit_ready_body_data,V293_exit_ready_body_core,
     V293_exit_ready_body_bindings,V293_handoff_byte,V293_exit_cells,V293_interrupt_cells,
     V293_quiet_bindings,V293_exit_guard_bindings in H|-*;cbn[V293_rdy_raw_cells]in H;sep auto. }
   eapply astar_mono;[apply V293_quiet_forget_names|intros s S;exact S|exact N]. }
 apply V293_bound_dispatch_borrow.
 apply V293_bound_dispatch_add_globals;[exact Names| ].
 apply V293_exit_exact_body_lend with(hv:=hv);assumption.
Qed.
Theorem V293_OSIntExit_bound_dispatch : forall Spec r ri sched_id old c,
 lo<256 ->hi<256 ->(exists p,V293_bitmap_ready lo hi p) ->nc<256 ->
 V293_ready_select lo hi(V293_ready_group lo hi)<>nc ->
 V293_bitmap_tasks lo hi tasks ->V293_priority_table entries tasks ->
 Forall(fun v=>rule_type_val_match(Tptr tp)v=true)entries ->
 indom tasks tid ->GoodFrm extra ->
 Spec sched_id=Some
 (V293_sched_exact_fpre unmap group rows high bt bg br bh li V293_opened_inv Hli,
 V293_sched_exact_fpost unmap group rows high bt bg br bh li V293_opened_inv Hli,(Tvoid,nil)) ->
 InfRules Spec V293_scheduler li
 (V293_ready_storage_inv br bg bp target tp
 (((bk,0%Z),Tint32)::((bh,0%Z),Tint8)::((bc,0%Z),Tint8)::
 (V293_array_cells bt 0 1 Tint8(length V293_ready_table)++returned)))r ri
 (V293_exit_bound_dispatch_entry old c)
 (V293_exit_boundary_dispatch table high target current counter sched_id
 (V293_interrupt_handoff high current target))V293_exit_bound_dispatch_resumed tid.
Proof.
 intros;unfold V293_exit_bound_dispatch_entry,V293_exit_bound_dispatch_resumed.
 apply V293_OSIntExit_local_dispatch with(Hli:=Hli);try assumption.
 - unfold bindings,V293_exit_ready_body_bindings,V293_handoff_binding;
   cbn[GoodFrm];repeat split;try exact I;try apply V293_time_cell_good;assumption.
 - apply V293_bound_dispatch_bindings_local.
 - apply V293_bound_dispatch_forget.
Qed.
Lemma V293_exit_bound_dispatch_current :
 V293_exit_bound_dispatch_resumed ==>CurLINV li tid.
Proof.
 intros st H.
 assert(S:st |= (CurTid tid ** bindings) ** Atrue).
 { unfold V293_exit_bound_dispatch_resumed,V293_exit_exact_dispatch_resumed,
   V293_ready_exit_resumed,SWINVt in H;fold(CurTid tid)in H;sep auto. }
 apply V293_CurLINV_extend with(extra:=Atrue).
 eapply astar_mono;[apply V293_local_exit_current;apply V293_bound_dispatch_bindings_local
 |intros s K;exact K|exact S].
Qed.
End BoundDispatch.
