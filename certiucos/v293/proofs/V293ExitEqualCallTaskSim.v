(* Full highest-current client branch; resources and generic entry machinery are reused. *)
Require Import CertiOS.certiucos.v293.proofs.V293ExitCriticalPrefixTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293ExitHelperTargetTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCriticalGlobal.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitSharedReclose.
Require Import CertiOS.certiucos.v293.proofs.V293SchedHelperBodyTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCallGlobal.
Require Import CertiOS.certiucos.v293.proofs.V293HandoffProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293ExitChangedTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBoundarySwitch.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyStorageInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293PendingReturnTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293ClientSkipTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyFullCall.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrent.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.certiucos.v293.code.V293OSSchedDispatch.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStoragePrefix.
Require Import CertiOS.certiucos.v293.code.V293OSIntExit.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.simulation.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Require Import CertiOS.certiucos.v293.proofs.V293ExitGuardHelperTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293SchedHelperTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293InvariantPendingTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.certiucos.v293.proofs.V293ReadySchedCall.
Require Import CertiOS.certiucos.v293.code.V293OSIntEnter.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.framework.proof.memory_prop.
Require Import CertiOS.certiucos.v293.proofs.V293ExitActiveCallTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293ExitClientCallTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293ExitTargetTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPointerCompare.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchState.
Require Import CertiOS.certiucos.v293.proofs.V293StoragePendingTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.proofs.V293ExitEqualHelperTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.proofs.V293ExitNestingProgSim.
Require Import CertiOS.certiucos.v293.code.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.proofs.V293SchedCallProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293ExitNestedCallTaskSim.
Import ListNotations.
Local Open Scope nat_scope.

Section EqualGuard.
Variables br bg bp bt bc bh bo bk saved_block bn bl : block.
Variable rest : list(addr*type).
Variables target : var.
Variable t : tid.
Variable nc : nat.
Variable saved_value oldtarget : val.
Variable c : int32.
Let Frame:=V293_exit_helper_frame bt bc bo bk saved_block rest nc saved_value oldtarget c.
Let Resource:=V293_helper_resource br bg bp bt bh t Frame.
Let Cells:=((bc,0%Z),Tint8)::((bh,0%Z),Tint8)::((bk,0%Z),Tint32)::
 (V293_array_cells bt 0%Z 1%Z Tint8(length V293_ready_table)++
 (((bn,0%Z),Tint8)::((bl,0%Z),Tint8)::rest)).
Let G:=V293_ready_storage_inv br bg bp target V293_tcb_type Cells.

Lemma V293_exit_equal_guard_TaskSim : forall pc po pi ip A ge M ir ci O op
 table high current counter f body caller tail tau d1 d2 saved
 helper unmap group rows y oldhigh tasks nesting lock n,
 po f=Some(tau,d1,d2,body) ->V293_skip_client_state(SKIP,(kenil,tail)) ->
 po helper=Some(V293_OSSchedNew_function unmap group rows high y) ->
 y<>unmap ->y<>group ->y<>rows ->y<>high ->
 get ge unmap=Some(bt,Tarray Tint8 256) ->get ge group=Some(bg,Tint8) ->
 get ge rows=Some(br,Tarray Tint8 2) ->get ge high=Some(bh,Tint8) ->
 get(V293_cpu_lenv saved saved_block)table=None ->
 get(V293_cpu_lenv saved saved_block)target=None ->
 get(V293_cpu_lenv saved saved_block)high=None ->
 get(V293_cpu_lenv saved saved_block)current=None ->
 get(V293_cpu_lenv saved saved_block)counter=None ->
 get ge table=Some(bp,Tarray(Tptr V293_tcb_type)13) ->
 get ge current=Some(bc,Tint8) ->get ge counter=Some(bk,Tint32) ->
 get ge target=Some(bo,Tptr V293_tcb_type) ->
 get O abstcblsid=Some(abstcblist tasks) ->
 V293_current_task tasks t nc ->V293_highest_ready tasks t ->
 n<=1 ->get(V293_cpu_lenv saved saved_block)nesting=None ->
 get(V293_cpu_lenv saved saved_block)lock=None ->
 get ge nesting=Some(bn,Tint8) ->get ge lock=Some(bl,Tint8) ->
 (forall i,ir i=false) ->
 (ge,V293_cpu_lenv saved saved_block,M,ir,(false,nil,ci),O,op)|=
 V293_exit_guard_resource bn bl n(Resource oldhigh) ->
 TaskSim(pc,(po,pi,ip))
 (curs(sseq(sprim encrit)
 (sseq(V293_OSIntExit_nesting_dispatch nesting lock
 (V293_exit_boundary_dispatch table high target current counter helper
 (V293_interrupt_handoff high current target)))(sprim excrit))),
 (kenil,kseq sret(kcall f body caller tail)))
 (ge,V293_cpu_lenv saved saved_block,M,ir,(false,nil,ci))
 (pc,A)(SKIP,(kenil,tail))O V293_shared_li G
 (fun st=>satp(fst st)(snd st)(RDYINV G t **LINV V293_shared_li t nil))t.
Proof.
 intros pc po pi ip A ge M ir ci O op table high current counter f body caller tail tau d1 d2 saved
 helper unmap group rows y oldhigh tasks nesting lock n Bind Cases Helper YU YG YR YH GU GG GR GH
 TN ON HN CN KN TG CG KG OG Map Current Highest Bound NN LN NG LG Clear Held.
 assert(Inside:InOS(SKIP,(kenil,kcall f body caller tail))(pumerge po pi)).
 { eapply V293_bound_call_inos;exact Bind. }
 assert(Context:forall ks, callcont ks=callcont(kcall f body caller tail) ->
 intcont ks=intcont(kcall f body caller tail) ->InOS(SKIP,(kenil,ks))(pumerge po pi)).
 { intros;eapply V293_context_inos;eassumption. }
 assert(ResourceCurrent:Resource oldhigh ==>CurTid t **Atrue).
 { unfold Resource;apply V293_helper_resource_current. }
 assert(Before:satp(ge,V293_cpu_lenv saved saved_block,M,ir,(false,nil,ci))O(CurLINV V293_shared_li t)).
 { eapply V293_exit_guards_local;[exact ResourceCurrent|exact Held]. }
 assert(Entered:(ge,V293_cpu_lenv saved saved_block,M,ir,(false,nil,false::ci),O,op)|=
 V293_exit_guard_resource bn bl n(Resource oldhigh)).
 { unfold Resource,Frame in *;eapply V293_guard_helper_stack;
   [apply V293_exit_helper_frame_good|exact Held]. }
 assert(After:satp(ge,V293_cpu_lenv saved saved_block,M,ir,(false,nil,false::ci))O(CurLINV V293_shared_li t)).
 { eapply V293_exit_guards_local;[exact ResourceCurrent|exact Entered]. }
 eapply V293_changed_pure_TaskSim with(ks:=kcall f body caller tail);
 [exact Inside|reflexivity|reflexivity| | |exact Before| ].
 - intros[x E];discriminate E.
 - intros;eapply stmt_step;[reflexivity|apply sseq_step].
 - eapply V293_invariant_encrit_TaskSim.
   + reflexivity.
   + eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
   + exact After.
   + eapply V293_changed_pure_TaskSim with(ks:=kcall f body caller tail);
     [exact Inside|reflexivity|reflexivity| | |exact After| ].
     * intros[x E];discriminate E.
     * intros;eapply stmt_step;[reflexivity|apply sskip_step].
     * eapply V293_changed_pure_TaskSim with(ks:=kcall f body caller tail);
       [exact Inside|reflexivity|reflexivity| | |exact After| ].
       -- intros[x E];discriminate E.
       -- intros;eapply stmt_step;[reflexivity|apply sseq_step].
       -- eapply V293_exit_nesting_prefix_TaskSim with(op:=op)(n:=n)(bn:=bn)(bl:=bl)(R:=Resource oldhigh).
          ++ apply Context;reflexivity.
          ++ exact Bound.
          ++ exact NN.
          ++ exact LN.
          ++ exact NG.
          ++ exact LG.
          ++ exact ResourceCurrent.
          ++ exact Entered.
          ++ intros M' Ready.
             assert(Local:satp(ge,V293_cpu_lenv saved saved_block,M',ir,(false,nil,false::ci))O(CurLINV V293_shared_li t)).
             { eapply V293_exit_guards_local;[exact ResourceCurrent|exact Ready]. }
             unfold V293_exit_boundary_dispatch,V293_OSSched_unlocked_prefix.
             eapply V293_changed_pure_TaskSim with(ks:=kcall f body caller tail);
             [exact Inside|reflexivity|reflexivity| | |exact Local| ].
             ** intros[x E];discriminate E.
             ** intros;eapply stmt_step;[reflexivity|apply sseq_step].
             ** eapply V293_changed_pure_TaskSim with(ks:=kcall f body caller tail);
                [exact Inside|reflexivity|reflexivity| | |exact Local| ].
                --- intros[x E];discriminate E.
                --- intros;eapply stmt_step;[reflexivity|apply sseq_step].
                --- unfold G,Cells.
                    eapply V293_exit_equal_helper_TaskSim with(nc:=nc)(bc:=bc)(bo:=bo)
                    (saved_value:=saved_value)(oldtarget:=oldtarget)(c:=c)(oldhigh:=oldhigh)
                    (tasks:=tasks)(unmap:=unmap)(group:=group)(rows:=rows)(y:=y);
                    try eassumption.
                    unfold Resource,Frame in Ready;eapply V293_guard_helper_storage;exact Ready.
Qed.
End EqualGuard.

Section EqualCall.
Variables br bg bp bt bc bh bo bk bn bl bu : block.
Variable rest : list(addr*type).
Variable target : var.
Variable t : tid.
Variable nc : nat.
Variable oldtarget : val.
Variable c : int32.
Let Resource:=V293_exit_active_resource br bg bp bt bc bh bo bk bn bl bu rest t nc oldtarget c.
Let Cells:=((bc,0%Z),Tint8)::((bh,0%Z),Tint8)::((bk,0%Z),Tint32)::
 (V293_array_cells bt 0%Z 1%Z Tint8(length V293_ready_table)++
 (((bn,0%Z),Tint8)::((bl,0%Z),Tint8)::((bu,0%Z),Tint8)::rest)).
Let G:=V293_ready_storage_inv br bg bp target V293_tcb_type Cells.

Lemma V293_exit_equal_body_TaskSim : forall pc po pi ip A ge M ir ci O op
 table high current counter f caller tail saved bs
 helper unmap group rows y oldhigh tasks running nesting lock n,
 po f=Some(V293_exit_boundary_function running nesting lock saved table high target current counter helper
 (V293_interrupt_handoff high current target)) ->
 V293_skip_client_state(SKIP,(kenil,tail)) ->
 po helper=Some(V293_OSSchedNew_function unmap group rows high y) ->
 y<>unmap ->y<>group ->y<>rows ->y<>high ->
 get ge unmap=Some(bt,Tarray Tint8 256) ->get ge group=Some(bg,Tint8) ->
 get ge rows=Some(br,Tarray Tint8 2) ->get ge high=Some(bh,Tint8) ->
 saved<>table ->saved<>target ->saved<>high ->saved<>current ->saved<>counter ->
 get ge table=Some(bp,Tarray(Tptr V293_tcb_type)13) ->
 get ge current=Some(bc,Tint8) ->get ge counter=Some(bk,Tint32) ->
 get ge target=Some(bo,Tptr V293_tcb_type) ->
 get O abstcblsid=Some(abstcblist tasks) ->
 V293_current_task tasks t nc ->V293_highest_ready tasks t ->
 n<=1 ->saved<>running ->saved<>nesting ->saved<>lock ->
 get ge running=Some(bu,Tint8) ->get ge nesting=Some(bn,Tint8) ->get ge lock=Some(bl,Tint8) ->
 (forall i,ir i=false) ->
 (ge,V293_cpu_lenv saved bs,M,ir,(false,nil,ci),O,op)|=
 Amapsto(bs,0%Z)Tint32 true Vundef **Resource n oldhigh ->
 TaskSim(pc,(po,pi,ip))
 (curs(V293_exit_boundary_body running nesting lock saved table high target current counter helper
 (V293_interrupt_handoff high current target)),
 (kenil,kcall f(V293_exit_boundary_body running nesting lock saved table high target current counter helper
 (V293_interrupt_handoff high current target))caller tail))
 (ge,V293_cpu_lenv saved bs,M,ir,(false,nil,ci))
 (pc,A)(SKIP,(kenil,tail))O V293_shared_li G
 (fun st=>satp(fst st)(snd st)(RDYINV G t **LINV V293_shared_li t nil))t.
Proof.
 intros pc po pi ip A ge M ir ci O op table high current counter f caller tail saved bs
 helper unmap group rows y oldhigh tasks running nesting lock n Bind Cases Helper YU YG YR YH GU GG GR GH
 ST SO SH SC SK TG CG KG OG Map Current Highest Bound SU SN SL UG NG LG Clear Held.
 set(body:=V293_exit_boundary_body running nesting lock saved table high target current counter helper
 (V293_interrupt_handoff high current target)).
 set(k:=kcall f body caller tail).
 assert(Inside:InOS(SKIP,(kenil,k))(pumerge po pi)).
 { unfold k,body;eapply V293_bound_call_inos;exact Bind. }
 assert(Context:forall ks,callcont ks=callcont k ->intcont ks=intcont k ->
 InOS(SKIP,(kenil,ks))(pumerge po pi)).
 { intros;eapply V293_context_inos;eassumption. }
 assert(Before:satp(ge,V293_cpu_lenv saved bs,M,ir,(false,nil,ci))O(CurLINV V293_shared_li t)).
 { eapply V293_pending_local with(op:=op).
   apply astar_mono with(P':=Atrue)(Q':=CurTid t **Atrue)in Held;
   [sep auto|intros st H;exact Logic.I|apply V293_exit_active_current]. }
 destruct(V293_tick_raw_slot_update(bs,0%Z)Tint32 Vundef(Vint32 Int.zero)
 (Resource n oldhigh) _ _ _ _ _ _ _ eq_refl Held)as(M'&Store&Updated).
 assert(After:satp(ge,V293_cpu_lenv saved bs,M',ir,(false,nil,ci))O(CurLINV V293_shared_li t)).
 { eapply V293_pending_local with(op:=op).
   apply astar_mono with(P':=Atrue)(Q':=CurTid t **Atrue)in Updated;
   [sep auto|intros st H;exact Logic.I|apply V293_exit_active_current]. }
 assert(Absent:forall x,saved<>x ->get(V293_cpu_lenv saved bs)x=None).
 { intros x Ne;unfold V293_cpu_lenv;rewrite map_get_set' by congruence;apply map_emp_get. }
 assert(Running:load Tint8 M'(bu,0%Z)=Some(V293_byteval 1)).
 { change(load Tint8(assertion.getmem(ge,V293_cpu_lenv saved bs,M',ir,(false,nil,ci),O,op))(bu,0%Z)=Some(V293_byteval 1)).
   eapply V293_record_star_load_r;[ |exact Updated];intros st H.
   unfold V293_exit_active_resource in H;eapply V293_record_star_load_l;[ |exact H];
   apply V293_owned_record_cell_load. }
 assert(Eval:evalval(V293_OSIntEnter_running running)(ge,V293_cpu_lenv saved bs,M')=Some(Vint32 Int.one)).
 { eapply V293_exit_active_running_eval;[apply Absent;exact SU|exact UG|exact Running]. }
 unfold V293_exit_boundary_body;fold body k.
 eapply V293_changed_pure_TaskSim with(ks:=k);
 [exact Inside|reflexivity|reflexivity| | |exact Before| ].
 - intros[x E];discriminate E.
 - intros;eapply stmt_step;[reflexivity|apply sseq_step].
 - eapply V293_exit_saved_assignment_TaskSim with(b:=bs)(M':=M');
   [apply Context;reflexivity| | |reflexivity|reflexivity|exact Store|exact Before|exact After| ].
   + cbn[evaltype get_lenv];unfold V293_cpu_lenv;rewrite map_get_set;reflexivity.
   + cbn[evaladdr get_lenv];unfold V293_cpu_lenv;rewrite map_get_set;reflexivity.
   + eapply V293_changed_pure_TaskSim with(ks:=k);
     [exact Inside|reflexivity|reflexivity| | |exact After| ].
     * intros[x E];discriminate E.
     * intros;eapply stmt_step;[reflexivity|apply sskip_step].
     * eapply V293_changed_pure_TaskSim with(ks:=k);
       [exact Inside|reflexivity|reflexivity| | |exact After| ].
       -- intros[x E];discriminate E.
       -- intros;eapply stmt_step;[reflexivity|apply sseq_step].
       -- eapply V293_exit_ifthen_TaskSim with(v:=Vint32 Int.one)(take:=true);
          [apply Context;reflexivity|exact After|exact Eval|reflexivity| ].
          unfold G,Cells,k,body.
          eapply V293_exit_equal_guard_TaskSim with(nc:=nc)(bc:=bc)(bo:=bo)
          (saved_value:=Vint32 Int.zero)(oldtarget:=oldtarget)(c:=c)(oldhigh:=oldhigh)
          (tasks:=tasks)(unmap:=unmap)(group:=group)(rows:=rows)(y:=y);
          try eassumption;try(apply Absent;assumption).
          eapply V293_exit_active_saved_pack;exact Updated.
Qed.

Lemma V293_exit_equal_entry_TaskSim : forall pc po pi ip A ge M ir ci O op
 table high current counter f caller tail saved
 helper unmap group rows y oldhigh tasks running nesting lock n,
 po f=Some(V293_exit_boundary_function running nesting lock saved table high target current counter helper
 (V293_interrupt_handoff high current target)) ->
 V293_skip_client_state(SKIP,(kenil,tail)) ->
 po helper=Some(V293_OSSchedNew_function unmap group rows high y) ->
 y<>unmap ->y<>group ->y<>rows ->y<>high ->
 get ge unmap=Some(bt,Tarray Tint8 256) ->get ge group=Some(bg,Tint8) ->
 get ge rows=Some(br,Tarray Tint8 2) ->get ge high=Some(bh,Tint8) ->
 saved<>table ->saved<>target ->saved<>high ->saved<>current ->saved<>counter ->
 get ge table=Some(bp,Tarray(Tptr V293_tcb_type)13) ->
 get ge current=Some(bc,Tint8) ->get ge counter=Some(bk,Tint32) ->
 get ge target=Some(bo,Tptr V293_tcb_type) ->
 get O abstcblsid=Some(abstcblist tasks) ->
 V293_current_task tasks t nc ->V293_highest_ready tasks t ->
 n<=1 ->saved<>running ->saved<>nesting ->saved<>lock ->
 get ge running=Some(bu,Tint8) ->get ge nesting=Some(bn,Tint8) ->get ge lock=Some(bl,Tint8) ->
 (forall i,ir i=false) ->
 (ge,caller,M,ir,(false,nil,ci),O,op)|=Resource n oldhigh ->
 TaskSim(pc,(po,pi,ip))
 (curs(sfexec f nil nil),(kenil,tail))
 (ge,caller,M,ir,(false,nil,ci))
 (pc,A)(SKIP,(kenil,tail))O V293_shared_li G
 (fun st=>satp(fst st)(snd st)(RDYINV G t **LINV V293_shared_li t nil))t.
Proof.
 intros pc po pi ip A ge M ir ci O op table high current counter f caller tail saved
 helper unmap group rows y oldhigh tasks running nesting lock n Bind Cases Helper YU YG YR YH GU GG GR GH
 ST SO SH SC SK TG CG KG OG Map Current Highest Bound SU SN SL UG NG LG Clear Held.
 set(body:=V293_exit_boundary_body running nesting lock saved table high target current counter helper
 (V293_interrupt_handoff high current target)).
 set(k:=kcall f body caller tail).
 set(ph:=(pc,A):hprog).
 set(Ch:=(SKIP,(kenil,tail)):code).
 set(Post:=fun st:taskst*osabst=>satp(fst st)(snd st)(RDYINV G t **LINV V293_shared_li t nil)).
 set(Res:=Resource n oldhigh).
 assert(Body:forall b,fresh M b ->
  (ge,V293_cpu_lenv saved b,allocb M b 0%Z(typelen Tint32),ir,(false,nil,ci),O,op)|=
    Amapsto(b,0%Z)Tint32 true Vundef **Res ->
  TaskSim(pc,(po,pi,ip))(curs body,(kenil,k))
   (ge,V293_cpu_lenv saved b,allocb M b 0%Z(typelen Tint32),ir,(false,nil,ci))
   ph Ch O V293_shared_li G Post t).
 { intros b Fresh Own;unfold body,k,ph,Ch,Post,Res in *.
   eapply V293_exit_equal_body_TaskSim with(op:=op)(oldhigh:=oldhigh)(tasks:=tasks)
   (unmap:=unmap)(group:=group)(rows:=rows)(y:=y);eassumption. }
 assert(Program:(pumerge po pi)f=Some(Tvoid,dnil,dcons saved Tint32 dnil,body)).
 { unfold pumerge;rewrite Bind;reflexivity. }
 assert(Inside:InOS(SKIP,(kenil,k))(pumerge po pi)).
 { unfold k,body;eapply V293_bound_call_inos;exact Bind. }
 assert(CurrentRes:forall s,s|=Res ->s|=CurTid t **Atrue).
 { unfold Res;apply V293_exit_active_current. }
 assert(Local:forall le',satp(ge,le',M,ir,(false,nil,ci))O(CurLINV V293_shared_li t)).
 { intros le';eapply V293_pending_local with(op:=op);apply CurrentRes.
   eapply V293_exit_active_lenv;exact Held. }
 assert(Allocated:forall b,fresh M b ->
  (ge,V293_cpu_lenv saved b,allocb M b 0%Z(typelen Tint32),ir,(false,nil,ci),O,op)|=
   Amapsto(b,0%Z)Tint32 true Vundef **Res).
 { intros b Fresh;eapply V293_tick_allocate_frame;[exact Fresh| ].
   eapply V293_exit_active_lenv;exact Held. }
 assert(AllocatedLocal:forall b,fresh M b ->
  satp(ge,V293_cpu_lenv saved b,allocb M b 0%Z(typelen Tint32),ir,(false,nil,ci))O
   (CurLINV V293_shared_li t)).
 { intros b Fresh;eapply V293_pending_local with(op:=op).
   pose proof(Allocated b Fresh)as Own.
   apply astar_mono with(P':=Amapsto(b,0%Z)Tint32 true Vundef)(Q':=CurTid t **Atrue)in Own;
    [sep auto|intros st H;exact H|exact CurrentRes]. }
 assert(AllocatedEnd:forall b,fresh M b ->
  TaskSim(pc,(po,pi,ip))(curs(salloc nil dnil),(kenil,k))
   (ge,V293_cpu_lenv saved b,allocb M b 0%Z(typelen Tint32),ir,(false,nil,ci))
   ph Ch O V293_shared_li G Post t).
 { intros b Fresh;eapply V293_invariant_cstep_TaskSim;
    [ | | |apply AllocatedLocal;exact Fresh|apply Body;[exact Fresh|apply Allocated;exact Fresh]].
   - eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
   - intros[x E];discriminate E.
   - intros Mf Mall Join;exists Mall;split;[exact Join| ].
     assert(Next:cstep(pumerge po pi)(curs(salloc nil dnil),(kenil,k))
      (ge,V293_cpu_lenv saved b,Mall)(curs body,(kenil,k))(ge,V293_cpu_lenv saved b,Mall)).
     { unfold k;eapply stmt_step;[reflexivity|apply sallocend_step]. }
     split;[exact Next| ];intros Cf mf Other.
     destruct(cstep_idmove_deter _ _ _ _ _ _ Next Other)as[EC EM];split;symmetry;assumption. }
 assert(Allocate:TaskSim(pc,(po,pi,ip))(curs(salloc nil(dcons saved Tint32 dnil)),(kenil,k))
  (ge,(emp:env),M,ir,(false,nil,ci))ph Ch O V293_shared_li G Post t).
 { eapply V293_branching_cstep_TaskSim.
   - eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
   - intros[x E];discriminate E.
   - intros Mf Mall Join;destruct(memory_has_fresh_block Mall)as[b Fresh].
     exists(curs(salloc nil dnil),(kenil,k));
     exists(ge,V293_cpu_lenv saved b,allocb Mall b 0%Z(typelen Tint32)).
     eapply stmt_step;[reflexivity| ];eapply salloclv_step;[reflexivity|reflexivity| ].
     exists b;repeat split;try assumption;try reflexivity.
     intros[v E];rewrite map_emp_get in E;discriminate E.
   - intros Cf mf Step;destruct(V293_exit_saved_successor _ _ _ _ _ _ _ _ Step)
      as(b&Fresh&Absent&EC&EM);subst Cf mf.
     do 2 eexists;split;[reflexivity| ];split;
      [apply AllocatedLocal;exact Fresh|apply AllocatedEnd;exact Fresh]. }
 eapply V293_invariant_cstep_TaskSim;[ | | |apply Local|exact Allocate].
 - exists(curs(sfexec f nil nil));exists kenil;exists tail;split;[reflexivity| ];left.
   exists f;exists(@nil val);exists(Tvoid,dnil,dcons saved Tint32 dnil,body);exists(@nil type).
   split;[reflexivity|exact Program].
 - intros[x E];discriminate E.
 - intros Mf Mall Join;exists Mall;split;[exact Join| ];split.
   + eapply stmt_step;[reflexivity| ];eapply sfexec_step with(d1:=dnil)(d2:=dcons saved Tint32 dnil);
     [reflexivity|reflexivity|exact Program|exact Logic.I|reflexivity].
   + intros;eapply V293_exit_exec_successor;[exact Program|eassumption].
Qed.

Theorem V293_exit_equal_client_call_TaskSim : forall pc po pi ip A ge M ir ci O op
 table high current counter f caller tail saved
 helper unmap group rows y oldhigh tasks running nesting lock n,
 fst(fst A)f=Some((fun _:vallist=>spec_done None),(Tvoid,nil)) ->
 po f=Some(V293_exit_boundary_function running nesting lock saved table high target current counter helper
 (V293_interrupt_handoff high current target)) ->
 V293_skip_client_state(SKIP,(kenil,tail)) ->
 po helper=Some(V293_OSSchedNew_function unmap group rows high y) ->
 y<>unmap ->y<>group ->y<>rows ->y<>high ->
 get ge unmap=Some(bt,Tarray Tint8 256) ->get ge group=Some(bg,Tint8) ->
 get ge rows=Some(br,Tarray Tint8 2) ->get ge high=Some(bh,Tint8) ->
 saved<>table ->saved<>target ->saved<>high ->saved<>current ->saved<>counter ->
 get ge table=Some(bp,Tarray(Tptr V293_tcb_type)13) ->
 get ge current=Some(bc,Tint8) ->get ge counter=Some(bk,Tint32) ->
 get ge target=Some(bo,Tptr V293_tcb_type) ->
 get O abstcblsid=Some(abstcblist tasks) ->
 V293_current_task tasks t nc ->V293_highest_ready tasks t ->
 n<=1 ->saved<>running ->saved<>nesting ->saved<>lock ->
 get ge running=Some(bu,Tint8) ->get ge nesting=Some(bn,Tint8) ->get ge lock=Some(bl,Tint8) ->
 (forall i,ir i=false) ->
 (ge,caller,M,ir,(false,nil,ci),O,op)|=V293_exit_active_resource br bg bp bt bc bh bo bk bn bl bu rest t nc oldtarget c n oldhigh ->
 TaskSim(pc,(po,pi,ip))
 (curs(scall f nil),(kenil,tail))
 (ge,caller,M,ir,(false,nil,ci))
 (pc,A)(curs(scall f nil),(kenil,tail))O V293_shared_li G
 (fun st=>satp(fst st)(snd st)(RDYINV G t **LINV V293_shared_li t nil))t.
Proof.
 intros pc po pi ip A ge M ir ci O op table high current counter f caller tail saved
 helper unmap group rows y oldhigh tasks running nesting lock n APIBind Bind Cases Helper YU YG YR YH GU GG GR GH
 ST SO SH SC SK TG CG KG OG Map Current Highest Bound SU SN SL UG NG LG Clear Held.
 eapply V293_nested_nil_call_bridge.
 - apply V293_client_nil_call_outside;exact Cases.
 - exact APIBind.
 - eapply V293_pending_local with(op:=op);eapply V293_exit_active_current;exact Held.
 - unfold G,Cells;eapply V293_exit_equal_entry_TaskSim with(op:=op)(oldhigh:=oldhigh)(tasks:=tasks)
   (unmap:=unmap)(group:=group)(rows:=rows)(y:=y);eassumption.
Qed.
End EqualCall.
