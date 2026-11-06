(* The full normalized changed-priority body, on the opened clear-ISR,
   interrupt-disabled boundary. Shared control bytes are not a switch frame. *)
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitDispatchHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitSamePriority.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBody.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickDelayHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStoragePrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStorageTail.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitch.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.sep_combine_lemmas.
Require Import Coq.Lists.List Lia.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitHandoffHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBoundarySwitch.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedShared.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCritical.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedISRContext.
Require Import CertiOS.certiucos.v293.code.V293OSIntExit.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitNondispatch.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitDispatch.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Import ListNotations.
Local Open Scope nat_scope.

Lemma V293_full_current_local : forall tp tid R,
 GV OSTCBCur@(Tptr tp)|->Vptr tid ** R ==> CurLINV V293_shared_li tid.
Proof.
 intros tp tid R st H. eapply astar_mono in H;
 [ |apply GV_separate_rw|intros s HS;exact HS].
 unfold CurLINV;exists(nil:list logicvar).
 assert(L:Aemp ==> LINV V293_shared_li tid nil)by apply V293_switch_local_empty.
  apply astar_l_aemp_intro in H.
 eapply astar_mono in H;[ |exact L|intros s HS;exact HS].
 unfold CurTid;clear -H;sep auto.
Qed.
Lemma V293_disabled_clear_flags : forall si ci,
 OS[(fun _:hid=>false),false,si,ci] ==>
 V293_shared_flags ** (Ais si ** Acs ci).
Proof.
 intros si ci st H.
 assert(C:Aisr(fun _:hid=>false) ==> isrclr).
 { intros s HS;exists(fun _:hid=>false);split;[exact HS| ].
   destruct HS as[E HE];split;[intros;reflexivity|exact HE]. }
 assert(S:st |= Ais si ** Atrue)by(clear -H;sep auto).
 pose proof(V293_time_topis si Atrue st S)as Top.
 apply astar_l_atopis_elim in Top as[Top _].
 pose proof(@astar_l_atopis_intro st(gettopis si)_ H Top)as HT.
 eapply astar_mono in H;[ |exact C|intros s HS;exact HS].
 unfold V293_shared_flags;clear -H HT;sep auto.
Qed.
Lemma V293_storage_full_frame : forall cells target tp tid,
 GoodFrm(V293_storage_full cells target tp tid).
Proof.
 intros;unfold V293_storage_full,V293_shared_fields,V293_dispatch_cell,
 Agvarmapsto,Agvarenv',Aptrmapsto.
 cbn[GoodFrm];intros;repeat split;try exact I;apply V293_storage_frame_good.
Qed.
Lemma V293_storage_resumed_excrit : forall Spec r ri tid aop cells target tp si ci P,
 GoodFrm P ->
 InfRules Spec V293_scheduler V293_shared_li(V293_storage_inv cells target tp)r ri
 (<||aop||> ** SWINVt(V293_storage_inv cells target tp)tid ** Ais si ** Acs(false::ci) ** P)
 (sprim excrit)
 (<||aop||> ** SWINVt(V293_storage_inv cells target tp)tid ** Ais si ** Acs ci ** P)tid.
Proof.
 intros Spec r ri tid aop cells target tp si ci P GP.
 eapply conseq_rule with
 (p:=<||aop||> ** OS[(fun _:hid=>false),false,si,false::ci] **
   (V293_storage_full cells target tp tid ** P))
 (q:=<||aop||> ** OS[(fun _:hid=>false),false,si,ci] **
   (V293_storage_full cells target tp tid ** P)).
 - intros st H.
   assert(S:st |= SWINVt(V293_storage_inv cells target tp)tid **
    (<||aop||> ** (Ais si ** (Acs(false::ci) ** P))))by(clear -H;sep auto).
   eapply astar_mono in S;[ |apply V293_storage_switch_full|intros s HS;exact HS].
   unfold V293_shared_flags in S;sep normal in S;sep destruct S.
   assert(T:st |= isrclr ** Atrue)by(clear -S;sep auto).
   eapply astar_mono in T;[ |apply V293_ready_isr_clear|intros s HS;exact HS].
   apply astar_l_aisr_elim in T as[T _].
   pose proof(@astar_l_aisr_intro st(fun _:hid=>false)_ S T)as ST.
   clear S;rename ST into S;sep auto.
   all: destruct S as[ir[AI[Clear Empty]]];exact Empty.
 - intros st H.
   assert(S:st |= OS[(fun _:hid=>false),false,si,ci] **
    (<||aop||> ** (V293_storage_full cells target tp tid ** P)))by(clear -H;sep auto).
   eapply astar_mono in S;[ |apply V293_disabled_clear_flags|intros s HS;exact HS].
   assert(T:st |= (V293_shared_flags ** V293_storage_full cells target tp tid) **
    (<||aop||> ** (Ais si ** (Acs ci ** P))))by(clear -S;sep auto).
   eapply astar_mono in T;[ |apply V293_storage_switch_halves|intros s HS;exact HS].
   clear -T;sep auto.
 - apply excrit2_rule;split;[apply V293_storage_full_frame|exact GP].
Qed.

Section ChangedBody.
Variables unmap group rows high table target current counter running nesting lock saved:var.
Variables bt bg br bh bp bo bc bk brun bn bl bs:block.
Variable tp:type.
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
Let arrays:=V293_input_cells bt bg br++V293_array_cells bp 0 4(Tptr tp)(length entries)++returned.
Let cells:=((bk,0%Z),Tint32)::((bh,0%Z),Tint8)::((bc,0%Z),Tint8)::arrays.
Let inv:=V293_storage_inv cells target tp.
Definition V293_exit_changed_bindings:=
 V293_handoff_binding nesting bn ** V293_handoff_binding lock bl.
Let env:=V293_sched_globals unmap group rows high bt bg br bh **
 (V293_prefix_bindings table high target tp bp bo **
 (V293_handoff_binding high bh ** V293_exit_changed_bindings)).
Definition V293_exit_changed_core hv out c:=
 GV OSTCBCur@(Tptr tp)|->Vptr tid **
 (V293_shared_fields tid tasks events now ** (GV target@(Tptr tp)|->out **
 (V293_inputs_full bt bg br lo hi ** (PV(bh,Int.zero)@Tint8|->hv **
 (V293_array true bp 0 4(Tptr tp)entries **
 (V293_handoff_byte current bc nc ** (V293_counter_cell counter bk c **
 (V293_storage rest ** (env ** px))))))))).
Definition V293_exit_changed_data nest hv out c value:=
 V293_time_cell true saved bs value ** (V293_handoff_byte running brun 1 **
 V293_rdy_raw_cells(V293_exit_cells bn bl nest 0)(V293_exit_changed_core hv out c)).
Let dispatchpx:=V293_exit_changed_bindings ** (V293_handoff_binding running brun **
 (V293_time_cell true saved bs(Vint32 Int.zero) ** px)).
Definition V293_exit_changed_resumed critical:=
 V293_exit_dispatch_resumed unmap group rows high table target current counter
 bt bg br bh bp bo bc bk tp entries returned tid aop si critical dispatchpx.
Lemma V293_exit_changed_core_good : forall hv out c,
 GoodFrm px ->GoodFrm(V293_exit_changed_core hv out c).
Proof.
 intros;unfold V293_exit_changed_core,V293_shared_fields,V293_inputs_full,
 env,V293_sched_globals,V293_prefix_bindings,V293_exit_changed_bindings,
 V293_handoff_byte,V293_handoff_binding,V293_counter_cell,V293_counter_bindings,
 Agvarmapsto,Agvarenv',Aptrmapsto.
 cbn[GoodFrm];repeat split;try exact I;try apply V293_array_good;
 try apply V293_storage_frame_good;assumption.
Qed.
Lemma V293_exit_changed_data_good : forall nest hv out c value,
 GoodFrm px ->GoodFrm(V293_exit_changed_data nest hv out c value).
Proof.
 intros;unfold V293_exit_changed_data,V293_exit_cells,V293_interrupt_cells;
 cbn[V293_rdy_raw_cells GoodFrm].
 split;[apply V293_time_cell_good| ].
 split;[unfold V293_handoff_byte,V293_handoff_binding;cbn[GoodFrm];tauto| ].
 repeat split;try exact I;apply V293_exit_changed_core_good;assumption.
Qed.
Lemma V293_exit_changed_core_local : forall hv out c,
 V293_exit_changed_core hv out c ==> CurLINV V293_shared_li tid.
Proof.
 intros hv out c st H;unfold V293_exit_changed_core in H.
 eapply V293_full_current_local;exact H.
Qed.
Lemma V293_exit_changed_core_env : forall hv out c st,
 st |= V293_exit_changed_core hv out c ->
 V293_interrupt_env nesting lock bn bl(getgenv st)(getlenv st).
Proof.
 intros hv out c st H.
 assert(N:get(getgenv st)nesting=Some(bn,Tint8) /\ get(getlenv st)nesting=None).
 { assert(B:st |= V293_handoff_binding nesting bn ** Atrue)
   by(unfold V293_exit_changed_core,env,V293_exit_changed_bindings in H;clear -H;sep auto).
   eapply V293_star_env_l;[apply V293_handoff_binding_env|exact B]. }
 assert(L:get(getgenv st)lock=Some(bl,Tint8) /\ get(getlenv st)lock=None).
 { assert(B:st |= V293_handoff_binding lock bl ** Atrue)
   by(unfold V293_exit_changed_core,env,V293_exit_changed_bindings in H;clear -H;sep auto).
   eapply V293_star_env_l;[apply V293_handoff_binding_env|exact B]. }
 unfold V293_interrupt_env;tauto.
Qed.
Lemma V293_exit_changed_lend : forall hv out c critical,
 lo<256 ->hi<256 ->(exists p,V293_bitmap_ready lo hi p) ->
 <||sched;;aop||> ** OS[(fun _:hid=>false),false,si,critical] **
 V293_exit_changed_data 0 hv out c(Vint32 Int.zero) ==>
 V293_exit_dispatch_entry unmap group rows high table target current counter
 bt bg br bh bp bo bc bk tp lo hi nc entries returned tid tasks events now aop si critical dispatchpx out c.
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
 (<||sched;;aop||> ** V293_exit_changed_data 0 hv out c(Vint32 Int.zero)))by(clear -H;sep auto).
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
 (V293_time_cell true saved bs(Vint32 Int.zero) ** px)))))))))))))).
 { unfold V293_exit_changed_data,V293_exit_changed_core,V293_handoff_byte,
 V293_exit_cells,V293_interrupt_cells in S;cbn[V293_rdy_raw_cells]in S;clear -S;sep auto. }
 eapply astar_mono in T;[ |apply GV_separate_rw|apply astar_mono;[exact C|intros s HS;exact HS]].
 unfold V293_exit_dispatch_entry.
 apply V293_retained_storage_prefix_lend_value with(hv:=hv);try assumption.
 unfold V293_retained_prefix_entry_heap,dispatchpx,env,CurTid;clear -T;sep auto.
Qed.

Theorem V293_OSIntExit_changed_body : forall Spec sched_id nest hv out c old,
 lo<256 ->hi<256 ->(exists p,V293_bitmap_ready lo hi p) ->nc<256 ->nest<=1 ->
 V293_ready_select lo hi(V293_ready_group lo hi)<>nc ->
 V293_bitmap_tasks lo hi tasks ->V293_priority_table entries tasks ->
 Forall(fun v=>rule_type_val_match(Tptr tp)v=true)entries ->indom tasks tid ->GoodFrm px ->
 Spec sched_id=Some
 (V293_critical_fpre unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
 V293_critical_fpost unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,(Tvoid,nil)) ->
 InfRules Spec V293_scheduler V293_shared_li inv
 (fun v=>[|v=None|] ** V293_exit_changed_resumed ci) Afalse
 (<||sched;;aop||> ** OS[(fun _:hid=>false),false,si,ci] **
 V293_exit_changed_data nest hv out c old)
 (V293_exit_boundary_body running nesting lock saved table high target current counter sched_id
 (V293_interrupt_handoff high current target)) Afalse tid.
Proof.
 intros Spec sched_id nest hv out c old Low High Ready Cur Nest Different Bitmap Table Pointer Member GP Lookup.
 unfold V293_exit_boundary_body.
 eapply seq_rule with(p':=<||sched;;aop||> ** OS[(fun _:hid=>false),false,si,ci] **
 V293_exit_changed_data nest hv out c(Vint32 Int.zero)).
 - eapply conseq_rule;[ | |apply(V293_time_zero Spec V293_scheduler V293_shared_li inv _ _ tid(sched;;aop)
  (V293_handoff_byte running brun 1 **
  (V293_rdy_raw_cells(V293_exit_cells bn bl nest 0)(V293_exit_changed_core hv out c) **
  OS[(fun _:hid=>false),false,si,ci]))saved bs old)].
   + unfold V293_exit_changed_data;intros st H;sep auto.
   + unfold V293_exit_changed_data;intros st H;sep auto.
   + intros st H;apply V293_CurLINV_extend with(extra:=Atrue).
     eapply astar_mono;[apply V293_exit_changed_core_local|intros s HS;exact HS| ].
     unfold V293_exit_cells,V293_interrupt_cells in H;cbn[V293_rdy_raw_cells]in H;clear -H;sep auto.
 - eapply seq_rule with(p':=V293_exit_changed_resumed ci).
   + eapply V293_tick_known_ift_hoare with(flag:=true).
     * intros st H.
       assert(G:st |= (V293_handoff_binding running brun **
        Amapsto(brun,0%Z)Tint8 true(V293_byteval 1)) ** Atrue)
        by(unfold V293_exit_changed_data,V293_handoff_byte in H;clear -H;sep auto).
       eapply astar_mono in G;[ |apply astar_mono;[intros s HS;exact HS|apply separate_rw2ro]|intros s HS;exact HS].
       assert(B:st |= V293_guard_cell running brun 1 ** Atrue)
        by(unfold V293_guard_cell,V293_handoff_binding in *;clear -G;sep auto).
       destruct(V293_exit_running_eval running brun 1 Atrue st ltac:(lia)B)as[V T].
       split;[exact V|split;[exact T|discriminate]].
     * eapply seq_rule.
       -- apply encrit2_rule;apply V293_exit_changed_data_good;exact GP.
       -- eapply seq_rule with(p':=V293_exit_changed_resumed(false::ci)).
          ++ eapply conseq_rule with
             (p:=<||sched;;aop||> ** V293_rdy_raw_cells(V293_exit_cells bn bl nest 0)
              (V293_exit_changed_core hv out c **
              (V293_time_cell true saved bs(Vint32 Int.zero) **
              (V293_handoff_byte running brun 1 ** OS[(fun _:hid=>false),false,si,false::ci])))).
             ** unfold V293_exit_changed_data,V293_exit_cells,V293_interrupt_cells;
                cbn[V293_rdy_raw_cells];intros st H;sep auto.
             ** intros st H;exact H.
             ** pose proof(V293_OSIntExit_nesting_dispatch_hoare Spec V293_scheduler V293_shared_li inv (fun v=>[|v=None|] ** V293_exit_changed_resumed ci) Afalse tid(sched;;aop)
                 nesting lock bn bl nest 0
                 (V293_exit_changed_core hv out c **
                 (V293_time_cell true saved bs(Vint32 Int.zero) **
                 (V293_handoff_byte running brun 1 ** OS[(fun _:hid=>false),false,si,false::ci])))
                 (V293_exit_boundary_dispatch table high target current counter sched_id(V293_interrupt_handoff high current target))
                 (V293_exit_changed_resumed(false::ci))ltac:(lia)ltac:(lia))as Dispatch.
                assert(E:V293_exit_enabled nest 0=true)by(apply V293_exit_enabled_iff;lia).
                rewrite E in Dispatch;apply Dispatch.
                --- apply V293_star_env_l;apply V293_exit_changed_core_env.
                --- apply V293_star_CurLINV_l;apply V293_exit_changed_core_local.
                --- intros Depth Locked.
                    eapply conseq_rule with(p:=V293_exit_dispatch_entry unmap group rows high table target current counter
                     bt bg br bh bp bo bc bk tp lo hi nc entries returned tid tasks events now aop si(false::ci)dispatchpx out c).
                    +++ intros st H;apply V293_exit_changed_lend with(hv:=hv);try assumption.
                        rewrite Depth in H. unfold V293_exit_changed_data,V293_exit_cells,V293_interrupt_cells in *;
                        cbn[V293_rdy_raw_cells]in *;clear -H;sep auto.
                    +++ intros st H;exact H.
                    +++ apply V293_OSIntExit_changed_dispatch;try assumption.
                        *** unfold dispatchpx,V293_exit_changed_bindings,V293_handoff_binding;
                            cbn[GoodFrm];repeat split;try exact I;try apply V293_time_cell_good;exact GP.
                        *** intros st H;apply astar_l_aemp_intro in H.
                            eapply astar_mono in H;[ |apply V293_switch_local_empty|intros s HS;exact HS].
                            clear -H;sep auto.
          ++ unfold V293_exit_changed_resumed,V293_exit_dispatch_resumed,
             V293_exit_handoff_resumed,V293_storage_resumed.
             apply V293_storage_resumed_excrit.
             unfold dispatchpx,V293_exit_changed_bindings,V293_handoff_binding,
              V293_counter_bindings,V293_sched_globals,V293_prefix_bindings.
             cbn[GoodFrm];repeat split;try exact I;try apply V293_time_cell_good;exact GP.
   + apply ret_rule;intros st H;apply astar_l_apure_intro;[exact H|reflexivity].
Qed.
End ChangedBody.
