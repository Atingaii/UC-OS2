(* Exact changed-priority exit. The selected LocalInv is constant Aemp;
   CurTid and p_local therefore describe the same owned footprint. Shared
   values are existential after resumption, never frozen across switch. *)
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
Require Import CertiOS.tactics.sepauto.sep_combine_lemmas.
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

Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyDispatch.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedExactPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedExactLocal.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyBody.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitChangedBody.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterInternal.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBody.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitNondispatch.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitDispatch.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickDelayHoare.

Lemma V293_exact_local_to_current : forall tid,
 p_local V293_shared_li tid nil ==> CurTid tid.
Proof.
 intros tid s H;unfold p_local,LINV,V293_shared_li in H;sep auto.
Qed.
Lemma V293_current_to_exact_local : forall tid,
 CurTid tid ==> p_local V293_shared_li tid nil.
Proof.
 intros tid s H;unfold p_local.
 eapply astar_mono;[intros st S;exact S|apply V293_switch_local_empty|apply astar_r_aemp_intro;exact H].
Qed.
Section ExactDispatch.
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
Definition V293_exit_exact_dispatch_entry old c:=
 V293_exact_storage_prefix_borrowed unmap group rows high table target bt bg br bh bp bo tp
 lo hi entries(kept c)tid tasks events now(sched;;aop)stack critical reserve old.
Let middle c:=V293_exact_storage_prefix_returned unmap group rows high table target bt bg br bh bp bo tp
 lo hi entries(kept c)tid tasks events now(sched;;aop)stack critical reserve.
Definition V293_exit_exact_dispatch_tail next c:=
 V293_ready_exit_tail br bg bp high current counter target bh bc bk tp arrays tid tasks events now next
 aop stack critical private nh nc c.
Definition V293_exit_exact_dispatch_resumed:=
 V293_ready_exit_resumed br bg bp high current counter target bh bc bk tp arrays tid aop stack critical private.

Lemma V293_exit_exact_dispatch_open : forall c,
 V293_ready_rel lo hi entries tasks ->
 Forall(fun v=>rule_type_val_match(Tptr tp)v=true)entries ->
 middle c ==> EX next:Modules.tid,[|V293_highest_ready tasks next|] ** V293_exit_exact_dispatch_tail next c.
Proof.
 intros c Rel Types s[next Held];exists next.
 unfold V293_exact_storage_prefix_returned in Held.
 eapply astar_mono in Held;[ |intros st S;exact S|apply astar_mono;
 [apply astar_mono;[intros st S;exact S|apply astar_mono;
 [apply astar_mono;[intros st S;exact S|apply V293_exact_local_to_current]|intros st S;exact S]]|intros st S;exact S]].
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
 unfold V293_exit_exact_dispatch_tail,V293_ready_exit_tail;clear -Heap;sep auto.
Qed.
Lemma V293_exit_exact_dispatch_guard : forall next c s,
 lo<256 ->hi<256 ->(exists p,V293_bitmap_ready lo hi p) ->nc<256 ->
 s |= V293_exit_exact_dispatch_tail next c ->
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
Theorem V293_OSIntExit_exact_dispatch : forall Spec r ri sched_id old c,
 lo<256 ->hi<256 ->(exists p,V293_bitmap_ready lo hi p) ->nc<256 ->nh<>nc ->
 V293_bitmap_tasks lo hi tasks ->V293_priority_table entries tasks ->
 Forall(fun v=>rule_type_val_match(Tptr tp)v=true)entries ->
 indom tasks tid ->GoodFrm px ->
 Spec sched_id=Some
 (V293_sched_exact_fpre unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
 V293_sched_exact_fpost unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
 (Tvoid,nil)) ->
 InfRules Spec V293_scheduler V293_shared_li inv r ri
 (V293_exit_exact_dispatch_entry old c)
 (V293_exit_boundary_dispatch table high target current counter sched_id
 (V293_interrupt_handoff high current target)) V293_exit_exact_dispatch_resumed tid.
Proof.
 intros Spec r ri sched_id old c Hlo Hhi Ready Hnc Different Bitmap Htable Hptr Member Good Callee.
 unfold V293_exit_boundary_dispatch;eapply seq_rule with(p':=middle c).
 - apply V293_OSSched_exact_storage_prefix_returned;try assumption.
   + unfold kept,V293_handoff_byte,V293_handoff_binding,V293_counter_cell,V293_counter_bindings.
     cbn[GoodFrm];repeat split;try exact I;apply V293_storage_frame_good.
   + unfold reserve,V293_handoff_binding;cbn[GoodFrm];repeat split;try exact I;[apply V293_owned_tasks_frame|exact Good].
 - eapply conseq_rule.
   + apply V293_exit_exact_dispatch_open;[exact(conj Hlo(conj Hhi(conj Ready(conj Bitmap Htable))))|exact Hptr].
   + intros st H;exact H.
   + apply ex_intro_rule;intro next.
     eapply conseq_rule with(p:=V293_exit_exact_dispatch_tail next c ** [|V293_highest_ready tasks next|]).
     1: { apply astar_comm. }
     1: { intros st H;exact H. }
     apply pure_split_rule;intro Highest.
     eapply if_rule with(tp:=Tint32).
     * intros st Held. destruct(V293_exit_exact_dispatch_guard next c st Hlo Hhi Ready Hnc Held)as[V T].
       exists(Vint32(if Nat.eqb nh nc then Int.zero else Int.one));repeat split;try assumption;discriminate.
     * eapply conseq_rule.
       -- intros st[Held _];exact Held.
       -- intros st H;exact H.
       -- apply V293_ready_exit_changed_tail;try assumption.
          ++ unfold nh;pose proof(V293_ready_selection_range lo hi(V293_ready_group lo hi)Hlo Hhi eq_refl Ready);lia.
          ++ unfold private,bindings,V293_sched_globals,V293_prefix_bindings;cbn[GoodFrm];tauto.
          ++ intros st H. assert(P:st |= px ** Atrue)by(unfold private in H;clear -H;sep auto).
             apply astar_l_aemp_intro in P.
             eapply astar_mono in P;[ |apply(V293_switch_local_empty tid nil)|intros s HS;exact HS];clear -P;sep auto.
     * eapply conseq_rule with(p:=Afalse)(q:=V293_exit_exact_dispatch_resumed).
       -- intros st[Held FalseGuard].
          destruct(V293_exit_exact_dispatch_guard next c st Hlo Hhi Ready Hnc Held)as[V T].
          assert(Ne:Nat.eqb nh nc=false)by(apply Nat.eqb_neq;exact Different).
          rewrite Ne in V.
          destruct FalseGuard as[v[Eval FalseVal]]. rewrite V in Eval;inversion Eval;subst v.
          vm_compute in FalseVal;discriminate.
       -- intros st H;exact H.
       -- apply pfalse_rule.
Qed.
End ExactDispatch.

Section ExactBody.
Variables unmap group rows high table target current counter running nesting lock saved:var.
Variables bt bg br bh bp bo bc bk brun bn bl bs:block.
Let tp:=V293_tcb_type.
Variables lo hi nc:nat.
Variable entries:list val.
Variable rest:list(addr*type).
Variable tid:Modules.tid.
Variable tasks:TcbMod.map.
Variable events:EcbMod.map.
Variable now:int32.
Variable aop:spec_code.
Variable si:list hid.
Variable ci:list bool.
Variable px:asrt.
Let controls:= [((brun,0%Z),Tint8);((bn,0%Z),Tint8);((bl,0%Z),Tint8)].
Let returned:=controls++rest.
Let arrays:=V293_array_cells bt 0 1 Tint8(length V293_ready_table)++returned.
Let cells:=((bk,0%Z),Tint32)::((bh,0%Z),Tint8)::((bc,0%Z),Tint8)::arrays.
Let inv:=V293_ready_storage_inv br bg bp target tp cells.
Local Notation bodybindings := (V293_exit_ready_body_bindings nesting lock bn bl).
Local Notation core := (V293_exit_ready_body_core unmap group rows high table target current counter nesting lock
 bt bg br bh bp bo bc bk bn bl lo hi nc entries rest tid tasks events now px).
Local Notation bodydata := (V293_exit_ready_body_data unmap group rows high table target current counter running nesting lock saved
 bt bg br bh bp bo bc bk brun bn bl bs lo hi nc entries rest tid tasks events now px).
Let env:=V293_sched_globals unmap group rows high bt bg br bh **
 (V293_prefix_bindings table high target tp bp bo **
 (V293_handoff_binding high bh ** bodybindings)).
Let dispatchpx:=bodybindings ** (V293_handoff_binding running brun **
 (V293_time_cell true saved bs(Vint32 Int.zero) ** px)).
Definition V293_exit_exact_body_resumed critical:=
 V293_exit_exact_dispatch_resumed unmap group rows high table target current counter
 bt bg br bh bp bo bc bk returned tid aop si critical dispatchpx.
Let private:=V293_counter_bindings counter bk **
 ((V293_handoff_binding high bh ** V293_handoff_binding current bc) **
 ((V293_sched_globals unmap group rows high bt bg br bh **
 V293_prefix_bindings table high target tp bp bo) ** dispatchpx)).
Definition V293_exit_exact_body_post critical:=
 <||aop||> ** ((SWINV inv ** p_local V293_shared_li tid nil) **
 ((Ais si ** Acs critical) ** private)).
Lemma V293_exit_exact_body_post_pack : forall critical,
 V293_exit_exact_body_resumed critical ==> V293_exit_exact_body_post critical.
Proof.
 intros critical st H.
 unfold V293_exit_exact_body_resumed,V293_exit_exact_dispatch_resumed,V293_ready_exit_resumed,SWINVt in H.
 fold(CurTid tid)in H.
 assert(S:st |=CurTid tid ** (<||aop||> ** (SWINV inv ** ((Ais si ** Acs critical) ** private))))
 by(unfold private;clear -H;sep auto).
 eapply astar_mono in S;[ |apply V293_current_to_exact_local|intros s HS;exact HS].
 unfold V293_exit_exact_body_post;clear -S;sep auto.
Qed.
Lemma V293_exit_exact_body_lend : forall hv out c critical,
 lo<256 ->hi<256 ->(exists p,V293_bitmap_ready lo hi p) ->
 <||sched;;aop||> ** OS[(fun _:hid=>false),false,si,critical] **
 bodydata 0 hv out c(Vint32 Int.zero) ==>
 V293_exit_exact_dispatch_entry unmap group rows high table target current counter
 bt bg br bh bp bo bc bk lo hi nc entries returned tid tasks events now aop si critical dispatchpx out c.
Proof.
 intros hv out c critical Low High Ready st H.
 assert(C:Amapsto(brun,0%Z)Tint8 true(V293_byteval 1) **
 (Amapsto(bn,0%Z)Tint8 true(V293_byteval 0) **
 (Amapsto(bl,0%Z)Tint8 true(V293_byteval 0) ** V293_storage rest)) ==>
 V293_storage returned).
 { assert(B:forall b n,n<256 -> Amapsto(b,0%Z)Tint8 true(V293_byteval n) ==>
      V293_storage_cell(b,0%Z)Tint8).
   { intros b n Bound s HS;exists(V293_byteval n);sep auto;apply V293_byte_type;exact Bound. }
   unfold returned,controls;cbn[V293_storage].
   apply astar_mono;[apply B;lia| ].
   apply astar_mono;[apply B;lia| ].
   apply astar_mono;[apply B;lia|intros s HS;exact HS]. }
 assert(S:st |= OS[(fun _:hid=>false),false,si,critical] **
 (<||sched;;aop||> ** bodydata 0 hv out c(Vint32 Int.zero)))by(clear -H;sep auto).
 eapply astar_mono in S;[ |apply V293_disabled_clear_flags|intros s HS;exact HS].
 assert(T:st |= (GV OSTCBCur@(Tptr tp)|->Vptr tid) **
 ((Amapsto(brun,0%Z)Tint8 true(V293_byteval 1) **
 (Amapsto(bn,0%Z)Tint8 true(V293_byteval 0) **
 (Amapsto(bl,0%Z)Tint8 true(V293_byteval 0) ** V293_storage rest))) **
 (<||sched;;aop||> ** ((V293_shared_flags ** (Ais si ** Acs critical)) **
 (V293_shared_fields tid tasks events now ** (GV target@(Tptr tp)|->out **
 (V293_inputs_full bt bg br lo hi ** (PV(bh,Int.zero)@Tint8|->hv **
 (V293_array true bp 0 4(Tptr tp)entries ** (V293_handoff_byte current bc nc **
 (V293_counter_cell counter bk c ** (env ** (V293_handoff_binding running brun **
 (V293_time_cell true saved bs(Vint32 Int.zero) ** (px ** V293_owned_task_records tasks))))))))))))))).
 { unfold V293_exit_ready_body_data,V293_exit_ready_body_core,V293_handoff_byte,
 V293_exit_cells,V293_interrupt_cells,env,V293_exit_ready_body_bindings in *;cbn[V293_rdy_raw_cells]in S;clear -S;sep auto. }
 eapply astar_mono in T;[ |apply GV_separate_rw|apply astar_mono;[exact C|intros s HS;exact HS]].
 unfold V293_exit_exact_dispatch_entry.
 apply V293_exact_storage_prefix_lend_value with(hv:=hv);try assumption.
 unfold V293_retained_prefix_entry_heap,dispatchpx,env,CurTid;clear -T;sep auto.
Qed.

Theorem V293_OSIntExit_exact_body : forall Spec sched_id nest hv out c old,
 lo<256 ->hi<256 ->(exists p,V293_bitmap_ready lo hi p) ->nc<256 ->nest<=1 ->
 V293_ready_select lo hi(V293_ready_group lo hi)<>nc ->
 V293_bitmap_tasks lo hi tasks ->V293_priority_table entries tasks ->
 Forall(fun v=>rule_type_val_match(Tptr tp)v=true)entries ->indom tasks tid ->GoodFrm px ->
 Spec sched_id=Some
 (V293_sched_exact_fpre unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
 V293_sched_exact_fpost unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,(Tvoid,nil)) ->
 InfRules Spec V293_scheduler V293_shared_li inv
 (fun v=>[|v=None|] ** V293_exit_exact_body_post ci) Afalse
 (<||sched;;aop||> ** OS[(fun _:hid=>false),false,si,ci] **
 bodydata nest hv out c old)
 (V293_exit_boundary_body running nesting lock saved table high target current counter sched_id
 (V293_interrupt_handoff high current target)) Afalse tid.
Proof.
 intros Spec sched_id nest hv out c old Low High Ready Cur Nest Different Bitmap Table Pointer Member GP Lookup.
 unfold V293_exit_boundary_body.
 eapply seq_rule with(p':=<||sched;;aop||> ** OS[(fun _:hid=>false),false,si,ci] **
 bodydata nest hv out c(Vint32 Int.zero)).
 - eapply conseq_rule;[ | |apply(V293_time_zero Spec V293_scheduler V293_shared_li inv _ _ tid(sched;;aop)
  (V293_handoff_byte running brun 1 **
  (V293_rdy_raw_cells(V293_exit_cells bn bl nest 0)(core hv out c) **
  OS[(fun _:hid=>false),false,si,ci]))saved bs old)].
   + unfold V293_exit_ready_body_data;intros st H;sep auto.
   + unfold V293_exit_ready_body_data;intros st H;sep auto.
   + intros st H;apply V293_CurLINV_extend with(extra:=Atrue).
     eapply astar_mono;[apply V293_exit_ready_body_core_local|intros s HS;exact HS| ].
     unfold V293_exit_cells,V293_interrupt_cells in H;cbn[V293_rdy_raw_cells]in H;clear -H;sep auto.
 - eapply seq_rule with(p':=V293_exit_exact_body_resumed ci).
   + eapply V293_tick_known_ift_hoare with(flag:=true).
     * intros st H.
       assert(G:st |= (V293_handoff_binding running brun **
        Amapsto(brun,0%Z)Tint8 true(V293_byteval 1)) ** Atrue)
        by(unfold V293_exit_ready_body_data,V293_handoff_byte in H;clear -H;sep auto).
       eapply astar_mono in G;[ |apply astar_mono;[intros s HS;exact HS|apply separate_rw2ro]|intros s HS;exact HS].
       assert(B:st |= V293_guard_cell running brun 1 ** Atrue)
        by(unfold V293_guard_cell,V293_handoff_binding in *;clear -G;sep auto).
       destruct(V293_exit_running_eval running brun 1 Atrue st ltac:(lia)B)as[V T].
       split;[exact V|split;[exact T|discriminate]].
     * eapply seq_rule.
       -- apply encrit2_rule;apply V293_exit_ready_body_data_good;exact GP.
       -- eapply seq_rule with(p':=V293_exit_exact_body_resumed(false::ci)).
          ++ eapply conseq_rule with
             (p:=<||sched;;aop||> ** V293_rdy_raw_cells(V293_exit_cells bn bl nest 0)
              (core hv out c **
              (V293_time_cell true saved bs(Vint32 Int.zero) **
              (V293_handoff_byte running brun 1 ** OS[(fun _:hid=>false),false,si,false::ci])))).
             ** unfold V293_exit_ready_body_data,V293_exit_cells,V293_interrupt_cells;
                cbn[V293_rdy_raw_cells];intros st H;sep auto.
             ** intros st H;exact H.
             ** pose proof(V293_OSIntExit_nesting_dispatch_hoare Spec V293_scheduler V293_shared_li inv (fun v=>[|v=None|] ** V293_exit_exact_body_post ci) Afalse tid(sched;;aop)
                 nesting lock bn bl nest 0
                 (core hv out c **
                 (V293_time_cell true saved bs(Vint32 Int.zero) **
                 (V293_handoff_byte running brun 1 ** OS[(fun _:hid=>false),false,si,false::ci])))
                 (V293_exit_boundary_dispatch table high target current counter sched_id(V293_interrupt_handoff high current target))
                 (V293_exit_exact_body_resumed(false::ci))ltac:(lia)ltac:(lia))as Dispatch.
                assert(E:V293_exit_enabled nest 0=true)by(apply V293_exit_enabled_iff;lia).
                rewrite E in Dispatch;apply Dispatch.
                --- apply V293_star_env_l;apply V293_exit_ready_body_core_env.
                --- apply V293_star_CurLINV_l;apply V293_exit_ready_body_core_local.
                --- intros Depth Locked.
                    eapply conseq_rule with(p:=V293_exit_exact_dispatch_entry unmap group rows high table target current counter
                     bt bg br bh bp bo bc bk lo hi nc entries returned tid tasks events now aop si(false::ci)dispatchpx out c).
                    +++ intros st H;apply V293_exit_exact_body_lend with(hv:=hv);try assumption.
                        rewrite Depth in H. unfold V293_exit_ready_body_data,V293_exit_cells,V293_interrupt_cells in *;
                        cbn[V293_rdy_raw_cells]in *;clear -H;sep auto.
                    +++ intros st H;exact H.
                    +++ apply V293_OSIntExit_exact_dispatch;try assumption.
                        *** unfold dispatchpx,V293_exit_ready_body_bindings,V293_handoff_binding;
                            cbn[GoodFrm];repeat split;try exact I;try apply V293_time_cell_good;exact GP.
          ++ unfold V293_exit_exact_body_resumed,V293_exit_exact_dispatch_resumed,
             V293_ready_exit_resumed.
             apply V293_ready_storage_resumed_excrit.
             unfold dispatchpx,V293_exit_ready_body_bindings,V293_handoff_binding,
              V293_counter_bindings,V293_sched_globals,V293_prefix_bindings.
             cbn[GoodFrm];repeat split;try exact I;try apply V293_time_cell_good;exact GP.
   + apply ret_rule;intros st H;apply astar_l_apure_intro;
     [apply V293_exit_exact_body_post_pack;exact H|reflexivity].
Qed.
End ExactBody.
