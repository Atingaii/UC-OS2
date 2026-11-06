(* Compose the original helper call with target assignment and changed suffix.
   Two decoder read shares are reunited before dispatch storage is transferred. *)
Require Import CertiOS.certiucos.v293.proofs.V293ExitChangedTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293HandoffProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCallGlobal.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrent.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.code.V293OSSchedDispatch.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyFullCall.
Require Import CertiOS.certiucos.v293.proofs.V293InvariantPendingTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293PendingReturnTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyStorageInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293ClientSkipTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBoundarySwitch.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.simulation.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.framework.proof.memory_prop.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Require Import CertiOS.certiucos.v293.proofs.V293SchedHelperReturnTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293SchedHelperTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293SchedCallProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293ReadySchedCall.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.

Require Import CertiOS.certiucos.v293.proofs.V293SchedHelperBodyTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293ExitTargetTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStoragePrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.

Lemma V293_helper_decoder_storage : forall bt,
 V293_read_bytes bt 0%Z V293_ready_table **V293_read_bytes bt 0%Z V293_ready_table ==>
 V293_storage(V293_array_cells bt 0%Z 1%Z Tint8(length V293_ready_table)).
Proof.
 intros bt s Held;rewrite !V293_read_bytes_array in Held.
 apply V293_array_reunite in Held.
 rewrite <- (map_length V293_byteval V293_ready_table).
 eapply V293_array_to_storage;[vm_compute;repeat constructor|exact Held].
Qed.

Section HelperTarget.
Variables br bg bp bt bc bh bo bk saved_block : block.
Variable rest : list(addr*type).
Variables target : var.
Variable t : tid.
Variable nc : nat.
Variable saved_value oldtarget : val.
Variable c : int32.
Let DecoderCells := V293_array_cells bt 0%Z 1%Z Tint8(length V293_ready_table).
Let Rest := DecoderCells++rest.
Let Cells := ((bc,0%Z),Tint8)::((bh,0%Z),Tint8)::((bk,0%Z),Tint32)::Rest.
Let G := V293_ready_storage_inv br bg bp target V293_tcb_type Cells.
Definition V293_exit_helper_frame :=
 Amapsto(saved_block,0%Z)Tint32 true saved_value **
 (V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval nc) **
 (V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,oldtarget) **
 (V293_owned_record_cell((bk,0%Z),Tint32,Vint32 c) **
 (V293_read_bytes bt 0%Z V293_ready_table **V293_storage rest)))).
Lemma V293_exit_helper_frame_good : GoodInvAsrt V293_exit_helper_frame.
Proof.
 unfold V293_exit_helper_frame,V293_owned_record_cell.
 split;[exact Logic.I| ];split;[cbn;auto| ];split;[cbn;auto| ];
 split;[cbn;auto| ];split;[apply V293_helper_read_good|apply V293_storage_good].
Qed.

Lemma V293_exit_helper_target_resources : forall nh,
 V293_helper_resource br bg bp bt bh t V293_exit_helper_frame(V293_byteval nh) ==>
 Amapsto(saved_block,0%Z)Tint32 true saved_value **
 (SWINVt(V293ReadyTaskInvariant.V293_ready_inv br bg bp)t **
 (V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval nc) **
 (V293_owned_record_cell((bh,0%Z),Tint8,V293_byteval nh) **
 (V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,oldtarget) **
 (V293_owned_record_cell((bk,0%Z),Tint32,Vint32 c) **V293_storage Rest))))).
Proof.
 intros nh s Held.
 assert(Pair:s|=(V293_read_bytes bt 0%Z V293_ready_table **V293_read_bytes bt 0%Z V293_ready_table) **
 (Amapsto(saved_block,0%Z)Tint32 true saved_value **
 (SWINVt(V293ReadyTaskInvariant.V293_ready_inv br bg bp)t **
 (V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval nc) **
 (V293_owned_record_cell((bh,0%Z),Tint8,V293_byteval nh) **
 (V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,oldtarget) **
 (V293_owned_record_cell((bk,0%Z),Tint32,Vint32 c) **V293_storage rest))))))).
 { unfold V293_helper_resource,V293_exit_helper_frame in Held;sep auto. }
 eapply astar_mono in Pair;
 [ |apply V293_helper_decoder_storage|intros st H;exact H].
 assert(Pack:s|=Amapsto(saved_block,0%Z)Tint32 true saved_value **
 (SWINVt(V293ReadyTaskInvariant.V293_ready_inv br bg bp)t **
 (V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval nc) **
 (V293_owned_record_cell((bh,0%Z),Tint8,V293_byteval nh) **
 (V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,oldtarget) **
 (V293_owned_record_cell((bk,0%Z),Tint32,Vint32 c) **
 (V293_storage DecoderCells **V293_storage rest))))))).
 { unfold DecoderCells;clear Held;sep auto. }
 assert(JoinStorage:V293_storage DecoderCells **V293_storage rest ==>V293_storage Rest).
 { unfold Rest;apply V293_storage_append. }
 eapply astar_mono in Pack;[ |intros st H;exact H|
 apply astar_mono;[intros st H;exact H|
 apply astar_mono;[intros st H;exact H|
 apply astar_mono;[intros st H;exact H|
 apply astar_mono;[intros st H;exact H|
 apply astar_mono;[intros st H;exact H|exact JoinStorage]]]]]].
 exact Pack.
Qed.

Theorem V293_exit_helper_target_TaskSim : forall pc po pi ip A ge M ir top ci O op
 table high current counter f body caller tail tau d1 d2 saved
 helper unmap group rows y oldhigh tasks,
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
 (ge,V293_cpu_lenv saved saved_block,M,ir,(false,nil,top::ci),O,op)|=
 V293_helper_resource br bg bp bt bh t V293_exit_helper_frame oldhigh ->
 TaskSim(pc,(po,pi,ip))
 (curs(scall helper nil),
 (kenil,kseq(V293_OSSched_target_update table high target)
 (kseq(sif(V293_OSSched_different high current)
 (sseq(V293_OSSched_increment counter)
 (sseq(sskip None)(V293_interrupt_handoff high current target)))(sskip None))
 (kseq(sprim excrit)(kseq sret(kcall f body caller tail))))))
 (ge,V293_cpu_lenv saved saved_block,M,ir,(false,nil,top::ci))
 (pc,A)(curs(hapi_code(spec_seq sched(spec_done None))),(kenil,tail))O V293_shared_li G
 (fun st=>satp(fst st)(snd st)(RDYINV G t **LINV V293_shared_li t nil))t.
Proof.
 intros pc po pi ip A ge M ir top ci O op table high current counter f body caller tail tau d1 d2 saved
 helper unmap group rows y oldhigh tasks Sched Bind Cases Helper YU YG YR YH GU GG GR GH
 TN ON HN CN KN TG CG KG OG Map Current NotHighest Held.
 assert(Inside:InOS(SKIP,(kenil,kcall f body caller tail))(pumerge po pi)).
 { eapply V293_bound_call_inos;exact Bind. }
 eapply V293_sched_helper_full_TaskSim with(op:=op)(oldhigh:=oldhigh)(R:=V293_exit_helper_frame)
 (unmap:=unmap)(group:=group)(rows:=rows)(y:=y);
 [exact Helper| |apply V293_exit_helper_frame_good|exact YU|exact YG|exact YR|exact YH|
 exact GU|exact GG|exact GR|exact GH|exact Held| ].
 - eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
 - intros ts lo hi entries next message Mret Map' Rel Task Returned.
   assert(ts=tasks)by congruence;subst ts.
   destruct Rel as[Lo[Hi[Nonempty[Bitmap Table]]]].
   set(nh:=V293_ready_select lo hi(V293_ready_group lo hi)).
   assert(Range:nh<13)by(unfold nh;eapply V293_ready_selection_range;
    [exact Lo|exact Hi|reflexivity|exact Nonempty]).
   destruct(V293_ready_selection_task lo hi entries tasks Lo Hi Nonempty Bitmap Table)
    as(selected&msg&Selected&Pointer&Highest).
   assert(next=selected).
   { destruct(proj2 Table _ _ _ _ Task)as(p&P&EP&Slot).
     destruct(proj2 Table _ _ _ _ Selected)as(q&Q&EQ&Slot').
     assert(p=nh)by(eapply V293_priority_repr_injective;[exact P|exact Range|symmetry;exact EP]).
     assert(q=nh)by(eapply V293_priority_repr_injective;[exact Q|exact Range|symmetry;exact EQ]).
     subst p q;rewrite Slot in Slot';inversion Slot';reflexivity. }
   subst selected.
   assert(Different:nh<>nc).
   { intro E;apply NotHighest.
     assert(next=t).
     { apply(proj2(V293_OSSched_current_target lo hi entries tasks t nc next
        Lo Hi Nonempty Bitmap Table Current Highest));exact E. }
     subst next;exact Highest. }
   pose proof(V293_exit_helper_target_resources nh _ Returned)as Owned.
   assert(Local:satp(ge,V293_cpu_lenv saved saved_block,Mret,ir,(false,nil,top::ci))O
    (CurLINV V293_shared_li t)).
   { eapply V293_pending_local with(op:=op);eapply V293_helper_resource_current;exact Returned. }
   eapply V293_changed_pure_TaskSim with(ks:=kcall f body caller tail);
    [exact Inside|reflexivity|reflexivity| | |exact Local| ].
   + intros[x E];discriminate E.
   + intros;eapply stmt_step;[reflexivity|apply sskip_step].
   + unfold G,Cells,Rest;eapply V293_exit_target_TaskSim with(nh:=nh)(nc:=nc)
      (next:=next)(saved_value:=saved_value)(tasks:=tasks)(c:=c);
      try eassumption.
     * split;[exact Range|exists rdy;exists message;exact Task].
     * pose proof(proj1 Current);lia.
     * destruct Current as[B[st[oldmsg C]]];exists(Int.repr(Z.of_nat nc),st,oldmsg);exact C.
Qed.
End HelperTarget.
