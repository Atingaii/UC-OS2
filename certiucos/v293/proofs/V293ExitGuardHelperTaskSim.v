(* Original critical block, joined to the real helper and changed suffix.
   Guard ownership is retained as storage across the switch boundary. *)
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
Import ListNotations.
Local Open Scope nat_scope.

Lemma V293_guard_helper_stack : forall br bg bp bt bh t R hv bn bl n
 ge le M ir ci ci' O op,
 GoodInvAsrt R ->
 (ge,le,M,ir,(false,nil,ci),O,op)|=
 V293_exit_guard_resource bn bl n(V293_helper_resource br bg bp bt bh t R hv) ->
 (ge,le,M,ir,(false,nil,ci'),O,op)|=
 V293_exit_guard_resource bn bl n(V293_helper_resource br bg bp bt bh t R hv).
Proof.
 intros br bg bp bt bh t R hv bn bl n ge le M ir ci ci' O op Good Held.
 assert(Pack:(ge,le,M,ir,(false,nil,ci),O,op)|=
 SWINVt(V293ReadyTaskInvariant.V293_ready_inv br bg bp)t **
 (V293_owned_record_cell((bn,0%Z),Tint8,V293_byteval n) **
 (V293_owned_record_cell((bl,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((bh,0%Z),Tint8,hv) **
 (V293_read_bytes bt 0%Z V293_ready_table **R))))).
 { unfold V293_exit_guard_resource,V293_helper_resource in Held;sep auto. }
 assert(GoodRest:GoodInvAsrt
 (V293_owned_record_cell((bn,0%Z),Tint8,V293_byteval n) **
 (V293_owned_record_cell((bl,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((bh,0%Z),Tint8,hv) **
 (V293_read_bytes bt 0%Z V293_ready_table **R))))).
 { unfold V293_owned_record_cell;split;[cbn;auto| ];split;[cbn;auto| ];
   split;[cbn;auto| ];split;[apply V293_helper_read_good|exact Good]. }
 pose proof(V293_ready_critical_stack br bg bp t _ ge le M ir nil ci ci' O op GoodRest Pack)as Move.
 unfold V293_exit_guard_resource,V293_helper_resource;clear Held Pack;sep auto.
Qed.

Lemma V293_guard_helper_storage : forall br bg bp bt bc bh bo bk bs rest t nc sv old c hv bn bl,
 V293_exit_guard_resource bn bl 0
 (V293_helper_resource br bg bp bt bh t
 (V293_exit_helper_frame bt bc bo bk bs rest nc sv old c)hv) ==>
 V293_helper_resource br bg bp bt bh t
 (V293_exit_helper_frame bt bc bo bk bs
 (((bn,0%Z),Tint8)::((bl,0%Z),Tint8)::rest) nc sv old c)hv.
Proof.
 intros br bg bp bt bc bh bo bk bs rest t nc sv old c hv bn bl s Held.
 unfold V293_exit_guard_resource in Held.
 eapply astar_mono in Held;[ |apply V293_exit_cell_to_storage|
 apply astar_mono;[apply V293_exit_cell_to_storage|intros st H;exact H]].
 unfold V293_helper_resource,V293_exit_helper_frame in Held|-*.
 cbn[V293_storage];sep auto.
Qed.

Section GuardHelper.
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

Theorem V293_exit_guard_helper_TaskSim : forall pc po pi ip A ge M ir ci O op
 table high current counter f body caller tail tau d1 d2 saved
 helper unmap group rows y oldhigh tasks nesting lock n,
 getsched(pc,A)=V293_scheduler ->
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
 V293_current_task tasks t nc ->~V293_highest_ready tasks t ->
 n<=1 ->get(V293_cpu_lenv saved saved_block)nesting=None ->
 get(V293_cpu_lenv saved saved_block)lock=None ->
 get ge nesting=Some(bn,Tint8) ->get ge lock=Some(bl,Tint8) ->
 (ge,V293_cpu_lenv saved saved_block,M,ir,(false,nil,ci),O,op)|=
 V293_exit_guard_resource bn bl n(Resource oldhigh) ->
 TaskSim(pc,(po,pi,ip))
 (curs(sseq(sprim encrit)
 (sseq(V293_OSIntExit_nesting_dispatch nesting lock
 (V293_exit_boundary_dispatch table high target current counter helper
 (V293_interrupt_handoff high current target)))(sprim excrit))),
 (kenil,kseq sret(kcall f body caller tail)))
 (ge,V293_cpu_lenv saved saved_block,M,ir,(false,nil,ci))
 (pc,A)(curs(hapi_code(spec_seq sched(spec_done None))),(kenil,tail))O V293_shared_li G
 (fun st=>satp(fst st)(snd st)(RDYINV G t **LINV V293_shared_li t nil))t.
Proof.
 intros pc po pi ip A ge M ir ci O op table high current counter f body caller tail tau d1 d2 saved
 helper unmap group rows y oldhigh tasks nesting lock n Sched Bind Cases Helper YU YG YR YH GU GG GR GH
 TN ON HN CN KN TG CG KG OG Map Current NotHighest Bound NN LN NG LG Held.
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
                    eapply V293_exit_helper_target_TaskSim with(nc:=nc)(bc:=bc)(bo:=bo)
                    (saved_value:=saved_value)(oldtarget:=oldtarget)(c:=c)(oldhigh:=oldhigh)
                    (tasks:=tasks)(unmap:=unmap)(group:=group)(rows:=rows)(y:=y);
                    try eassumption.
                    unfold Resource,Frame in Ready;eapply V293_guard_helper_storage;exact Ready.
Qed.
End GuardHelper.
