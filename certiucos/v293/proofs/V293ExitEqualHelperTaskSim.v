(* Actual helper/target/equal branch to return; outer entry remains separate. *)
Require Import CertiOS.certiucos.v293.proofs.V293ExitHelperTargetTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStoragePrefix.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.certiucos.v293.proofs.V293ExitTargetTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPointerCompare.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchState.
Require Import CertiOS.certiucos.v293.proofs.V293SchedHelperBodyTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293SchedHelperTaskSim.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.certiucos.v293.proofs.V293StoragePendingTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitSharedReclose.
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

Section EqualTarget.
Variables br bg bp bc bh bo bk saved_block : block.
Variable rest : list(addr*type).
Variable target : var.
Variable t : tid.
Variable nc : nat.
Variable saved_value : val.
Let Cells := ((bc,0%Z),Tint8)::((bh,0%Z),Tint8)::((bk,0%Z),Tint32)::rest.
Let G := V293_ready_storage_inv br bg bp target V293_tcb_type Cells.
Let V293_equal_target_resource (v:val) (c:int32) := Amapsto(saved_block,0%Z)Tint32 true saved_value **
 (SWINVt(V293_ready_inv br bg bp)t **
 (V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval nc) **
 (V293_owned_record_cell((bh,0%Z),Tint8,V293_byteval nc) **
 (V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,v) **
 (V293_owned_record_cell((bk,0%Z),Tint32,Vint32 c) **V293_storage rest))))).

Lemma V293_equal_target_local : forall ge le M ir aux O op v c,
 (ge,le,M,ir,aux,O,op)|=V293_equal_target_resource v c ->satp(ge,le,M,ir,aux)O(CurLINV V293_shared_li t).
Proof.
 intros ge le M ir aux O op v c Held;eapply V293_pending_local with(op:=op).
 unfold V293_equal_target_resource,SWINVt in Held;fold(CurTid t)in Held;sep auto.
Qed.


Lemma V293_equal_target_reclose : forall ge le M ir aux O op c,
 get ge target=Some(bo,Tptr V293_tcb_type) ->
 (ge,le,M,ir,aux,O,op)|=V293_equal_target_resource(Vptr t)c ->
 (ge,le,M,ir,aux,O,op)|=
 Amapsto(saved_block,0%Z)Tint32 true saved_value **
 (V293_ready_storage_core br bg bp target V293_tcb_type Cells **CurTid t).
Proof.
 intros ge le M ir aux O op c Target Held.
 assert(Storage:V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval nc) **
 (V293_owned_record_cell((bh,0%Z),Tint8,V293_byteval nc) **
 (V293_owned_record_cell((bk,0%Z),Tint32,Vint32 c) **V293_storage rest)) ==>
 V293_storage Cells).
 { unfold Cells;cbn[V293_storage];repeat apply astar_mono;
   try(intros st H;exact H);apply V293_exit_cell_to_storage. }
 assert(Global:forall m o,
 (ge,le,m,ir,aux,o,op)|=V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,Vptr t) ->
 (ge,le,m,ir,aux,o,op)|=V293_dispatch_cell target V293_tcb_type).
 { intros m o H;unfold V293_dispatch_cell.
   apply astar_l_apure_elim in H;destruct H as[_ H].
   exists(Vptr t);apply astar_l_apure_intro;[ |reflexivity].
   exists bo;unfold Agvarenv',Aptrmapsto;cbn[addrval_to_addr].
   apply astar_l_agvarenv_intro;[exact H|split;[reflexivity|exact Target]]. }
 assert(Packed:(ge,le,M,ir,aux,O,op)|=
 (V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval nc) **
 (V293_owned_record_cell((bh,0%Z),Tint8,V293_byteval nc) **
 (V293_owned_record_cell((bk,0%Z),Tint32,Vint32 c) **V293_storage rest))) **
 (V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,Vptr t) **
 (Amapsto(saved_block,0%Z)Tint32 true saved_value **
 SWINVt(V293_ready_inv br bg bp)t)))by(unfold V293_equal_target_resource in Held;sep auto).
 eapply astar_mono with(P':=V293_storage Cells)in Packed;
 [ |exact Storage|intros st H;exact H].
 apply sat_split in Packed;destruct Packed as(ms&mr&os&orr&JM&JO&HS&Rest).
 apply sat_split in Rest;destruct Rest as(mt&mc&ot&oc&JM'&JO'&Cell&Ready).
 apply Global in Cell.
 assert(All:(ge,le,M,ir,aux,O,op)|=
 V293_storage Cells **(V293_dispatch_cell target V293_tcb_type **
 (Amapsto(saved_block,0%Z)Tint32 true saved_value **SWINVt(V293_ready_inv br bg bp)t))).
 { apply sat_split';exists ms;exists mr;exists os;exists orr;repeat first[assumption|split].
   apply sat_split';exists mt;exists mc;exists ot;exists oc;repeat first[assumption|split]. }
 assert(Joined:(ge,le,M,ir,aux,O,op)|=
 (SWINVt(V293_ready_inv br bg bp)t **V293_ready_storage_extra target V293_tcb_type Cells) **
 Amapsto(saved_block,0%Z)Tint32 true saved_value).
 { unfold V293_ready_storage_extra;clear -All;sep auto. }
 eapply astar_mono in Joined;
 [ |intros st H;apply V293_ready_storage_switch_resources;exact H|intros st H;exact H].
 unfold SWINVt in Joined;fold(CurTid t)in Joined.
 eapply astar_mono with(P':=(V293_shared_flags **V293_ready_storage_core br bg bp target V293_tcb_type Cells) **CurTid t)in Joined.
 2:{ apply astar_mono;[apply V293_ready_storage_switch_open|intros st H;exact H]. }
 2:{ intros st H;exact H. }
 assert(Empty:V293_shared_flags ==>Aemp).
 { intros s Flags;unfold V293_shared_flags in Flags.
   apply astar_l_aemp_elim.
   eapply astar_mono with(P:=isrclr **Aie false)(Q:=EX k:hid,ATopis k);
   [ |intros s0[k[_ E]];exact E|exact Flags].
   intros s0 F;apply astar_l_aemp_elim.
   eapply astar_mono with(P:=isrclr)(Q:=Aie false);
   [ |intros s1[_ E];exact E|exact F].
   intros s1[r[Flag Clear]];exact(proj2 Flag). }
 eapply astar_mono in Joined.
 2:{ apply astar_mono;[apply astar_mono;[exact Empty|intros st H;exact H]|intros st H;exact H]. }
 2:{ intros st H;exact H. }
 clear -Joined;sep auto.
Qed.

Lemma V293_equal_compare_TaskSim : forall pc po pi ip A ge M ir top ci O op
 high current counter handoff f body caller tail tau d1 d2 saved c,
 po f=Some(tau,d1,d2,body) ->V293_skip_client_state(SKIP,(kenil,tail)) ->
 (forall i,ir i=false) ->nc<256 ->
 get(V293_cpu_lenv saved saved_block)high=None ->
 get(V293_cpu_lenv saved saved_block)current=None ->
 get ge high=Some(bh,Tint8) ->get ge current=Some(bc,Tint8) ->
 get ge target=Some(bo,Tptr V293_tcb_type) ->
 (ge,V293_cpu_lenv saved saved_block,M,ir,(false,nil,top::ci),O,op)|=
 V293_equal_target_resource(Vptr t)c ->
 TaskSim(pc,(po,pi,ip))
 (curs(sif(V293_OSSched_different high current)
 (sseq(V293_OSSched_increment counter)(sseq(sskip None)handoff))(sskip None)),
 (kenil,kseq(sprim excrit)(kseq sret(kcall f body caller tail))))
 (ge,V293_cpu_lenv saved saved_block,M,ir,(false,nil,top::ci))
 (pc,A)(SKIP,(kenil,tail))O V293_shared_li G
 (fun st=>satp(fst st)(snd st)(RDYINV G t **LINV V293_shared_li t nil))t.
Proof.
 intros pc po pi ip A ge M ir top ci O op high current counter handoff f body caller tail tau d1 d2 saved c
 Bind Cases Clear Bound HN CN HG CG Target Held.
 assert(High:load Tint8 M(bh,0%Z)=Some(V293_byteval nc)).
 { eapply V293_record_star_load_l with(s:=(ge,V293_cpu_lenv saved saved_block,M,ir,(false,nil,top::ci),O,op))
 (P:=V293_owned_record_cell((bh,0%Z),Tint8,V293_byteval nc))(Q:=Atrue).
   - intros st H;apply V293_owned_record_cell_load;exact H.
   - unfold V293_equal_target_resource in Held;sep auto. }
 assert(Cache:load Tint8 M(bc,0%Z)=Some(V293_byteval nc)).
 { eapply V293_record_star_load_l with(s:=(ge,V293_cpu_lenv saved saved_block,M,ir,(false,nil,top::ci),O,op))
 (P:=V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval nc))(Q:=Atrue).
   - intros st H;apply V293_owned_record_cell_load;exact H.
   - unfold V293_equal_target_resource in Held;sep auto. }
 destruct(V293_OSSched_byte_comparison_eval _ _ _ _ _ _ _ _ _ Bound Bound HN CN HG CG High Cache)as(Guard&GuardType).
 rewrite Nat.eqb_refl in Guard.
 eapply V293_changed_if_TaskSim with(v:=Vint32 Int.zero)(take:=false).
 - eapply V293_context_inos with(ks:=kcall f body caller tail);
   [eapply V293_bound_call_inos;exact Bind|reflexivity|reflexivity].
 - eapply V293_equal_target_local;exact Held.
 - exact Guard.
 - reflexivity.
 - unfold G;eapply V293_storage_pending_TaskSim;
   [exact Bind|exact Cases|exact Clear| ].
   eapply V293_equal_target_reclose;[exact Target|exact Held].
Qed.

(* The public entry derives the RHS and allocates no additional assumption. *)
Lemma V293_equal_target_TaskSim : forall pc po pi ip A ge M ir top ci O op
 table high current counter f body caller tail tau d1 d2 saved oldtarget c tasks,
 po f=Some(tau,d1,d2,body) ->V293_skip_client_state(SKIP,(kenil,tail)) ->
 V293_current_task tasks t nc ->(forall i,ir i=false) ->
 get(V293_cpu_lenv saved saved_block)table=None ->
 get(V293_cpu_lenv saved saved_block)target=None ->
 get(V293_cpu_lenv saved saved_block)high=None ->
 get(V293_cpu_lenv saved saved_block)current=None ->
 get(V293_cpu_lenv saved saved_block)counter=None ->
 get ge table=Some(bp,Tarray(Tptr V293_tcb_type)13) ->
 get ge high=Some(bh,Tint8) ->get ge current=Some(bc,Tint8) ->get ge counter=Some(bk,Tint32) ->
 get ge target=Some(bo,Tptr V293_tcb_type) ->
 get O abstcblsid=Some(abstcblist tasks) ->
 (ge,V293_cpu_lenv saved saved_block,M,ir,(false,nil,top::ci),O,op)|=V293_equal_target_resource oldtarget c ->
 TaskSim(pc,(po,pi,ip))
 (curs(V293_OSSched_target_update table high target),
 (kenil,kseq(sif(V293_OSSched_different high current)
 (sseq(V293_OSSched_increment counter)
 (sseq(sskip None)(V293_interrupt_handoff high current target)))(sskip None))
 (kseq(sprim excrit)(kseq sret(kcall f body caller tail)))))
 (ge,V293_cpu_lenv saved saved_block,M,ir,(false,nil,top::ci))
 (pc,A)(SKIP,(kenil,tail))O V293_shared_li G
 (fun st=>satp(fst st)(snd st)(RDYINV G t **LINV V293_shared_li t nil))t.
Proof.
 intros pc po pi ip A ge M ir top ci O op table high current counter f body caller tail tau d1 d2 saved oldtarget c tasks
 Bind Cases Current Clear TN ON HN CN KN TG HG CG KG OG Map Held.
 assert(Range:nc<13)by exact(proj1 Current).
 assert(Ready:(ge,V293_cpu_lenv saved saved_block,M,ir,(false,nil,top::ci),O,op)|=
 SWINVt(V293_ready_inv br bg bp)t **Atrue)by(unfold V293_equal_target_resource in Held;sep auto).
 pose proof(V293_target_owned_pointer br bg bp t tasks t nc Atrue (ge,V293_cpu_lenv saved saved_block,M,ir,(false,nil,top::ci),O,op) Map Current Ready)as Pointer.
 assert(High:load Tint8 M(bh,0%Z)=Some(V293_byteval nc)).
 { eapply V293_record_star_load_l with(s:=(ge,V293_cpu_lenv saved saved_block,M,ir,(false,nil,top::ci),O,op))
 (P:=V293_owned_record_cell((bh,0%Z),Tint8,V293_byteval nc))(Q:=Atrue).
   - intros st H;apply V293_owned_record_cell_load;exact H.
   - unfold V293_equal_target_resource in Held;clear Ready;sep auto. }
 assert(ToWrite:(ge,V293_cpu_lenv saved saved_block,M,ir,(false,nil,top::ci),O,op)|=
 V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,oldtarget) **
 (Amapsto(saved_block,0%Z)Tint32 true saved_value **
 (SWINVt(V293_ready_inv br bg bp)t **
 (V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval nc) **
 (V293_owned_record_cell((bh,0%Z),Tint8,V293_byteval nc) **
 (V293_owned_record_cell((bk,0%Z),Tint32,Vint32 c) **V293_storage rest))))))
 by(unfold V293_equal_target_resource in Held;clear Ready;sep auto).
 destruct(V293_owned_record_cell_update (bo,0%Z) (Tptr V293_tcb_type) oldtarget (Vptr t) _ _ _ _ _ _ _ _
 eq_refl ToWrite)as(M'&Store&Written).
 assert(AfterOwned:(ge,V293_cpu_lenv saved saved_block,M',ir,(false,nil,top::ci),O,op)|=V293_equal_target_resource(Vptr t)c)
 by(unfold V293_equal_target_resource;clear -Written;sep auto).
 assert(Inside:InOS(SKIP,(kenil,kseq(sprim excrit)(kseq sret(kcall f body caller tail))))(pumerge po pi)).
 { eapply V293_context_inos with(ks:=kcall f body caller tail);
   [eapply V293_bound_call_inos;exact Bind|reflexivity|reflexivity]. }
 assert(LocalBefore:satp(ge,V293_cpu_lenv saved saved_block,M,ir,(false,nil,top::ci))O(CurLINV V293_shared_li t)).
 { eapply V293_equal_target_local;exact Held. }
 assert(LocalAfter:satp(ge,V293_cpu_lenv saved saved_block,M',ir,(false,nil,top::ci))O(CurLINV V293_shared_li t)).
 { eapply V293_equal_target_local;exact AfterOwned. }
 eapply V293_target_assignment_TaskSim;
 [ |exact TN|exact HN|exact ON|exact TG|exact HG|exact OG|exact High|exact Range|exact Pointer|exact Store|exact LocalBefore|exact LocalAfter| ].
 - eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
 - eapply V293_changed_pure_TaskSim with(ks:=kseq(sprim excrit)(kseq sret(kcall f body caller tail)));
   [exact Inside|reflexivity|reflexivity| | |exact LocalAfter| ].
   + intros[x E];discriminate E.
   + intros;eapply stmt_step;[reflexivity|apply sskip_step].
   + unfold G,Cells;eapply V293_equal_compare_TaskSim with(c:=c);try eassumption;try lia.
Qed.
End EqualTarget.

Section EqualHelper.
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
Theorem V293_exit_equal_helper_TaskSim : forall pc po pi ip A ge M ir top ci O op
 table high current counter f body caller tail tau d1 d2 saved
 helper unmap group rows y oldhigh tasks,
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
 V293_current_task tasks t nc ->V293_highest_ready tasks t ->(forall i,ir i=false) ->
 (ge,V293_cpu_lenv saved saved_block,M,ir,(false,nil,top::ci),O,op)|=
 V293_helper_resource br bg bp bt bh t (V293_exit_helper_frame bt bc bo bk saved_block rest nc saved_value oldtarget c) oldhigh ->
 TaskSim(pc,(po,pi,ip))
 (curs(scall helper nil),
 (kenil,kseq(V293_OSSched_target_update table high target)
 (kseq(sif(V293_OSSched_different high current)
 (sseq(V293_OSSched_increment counter)
 (sseq(sskip None)(V293_interrupt_handoff high current target)))(sskip None))
 (kseq(sprim excrit)(kseq sret(kcall f body caller tail))))))
 (ge,V293_cpu_lenv saved saved_block,M,ir,(false,nil,top::ci))
 (pc,A)(SKIP,(kenil,tail))O V293_shared_li G
 (fun st=>satp(fst st)(snd st)(RDYINV G t **LINV V293_shared_li t nil))t.
Proof.
 intros pc po pi ip A ge M ir top ci O op table high current counter f body caller tail tau d1 d2 saved
 helper unmap group rows y oldhigh tasks Bind Cases Helper YU YG YR YH GU GG GR GH
 TN ON HN CN KN TG CG KG OG Map Current HighestCurrent Clear Held.
 assert(Inside:InOS(SKIP,(kenil,kcall f body caller tail))(pumerge po pi)).
 { eapply V293_bound_call_inos;exact Bind. }
 eapply V293_sched_helper_full_TaskSim with(op:=op)(oldhigh:=oldhigh)(R:=V293_exit_helper_frame bt bc bo bk saved_block rest nc saved_value oldtarget c)
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
   assert(Same:next=t)by(eapply V293_highest_unique;[exact Table|exact Highest|exact HighestCurrent]).
   subst next.
   assert(Equal:nh=nc).
   { apply(proj1(V293_OSSched_current_target lo hi entries tasks t nc t
       Lo Hi Nonempty Bitmap Table Current Highest));reflexivity. }
   pose proof(V293_exit_helper_target_resources br bg bp bt bc bh bo bk saved_block rest t nc saved_value oldtarget c nh _ Returned)as Owned.
   assert(Local:satp(ge,V293_cpu_lenv saved saved_block,Mret,ir,(false,nil,top::ci))O
    (CurLINV V293_shared_li t)).
   { eapply V293_pending_local with(op:=op);eapply V293_helper_resource_current;exact Returned. }
   eapply V293_changed_pure_TaskSim with(ks:=kcall f body caller tail);
    [exact Inside|reflexivity|reflexivity| | |exact Local| ].
   + intros[x E];discriminate E.
   + intros;eapply stmt_step;[reflexivity|apply sskip_step].
   + rewrite Equal in Owned;unfold G,Cells,Rest;
     eapply V293_equal_target_TaskSim with(nc:=nc)(op:=op)(oldtarget:=oldtarget)
      (saved_value:=saved_value)(tasks:=tasks)(c:=c);try eassumption.
Qed.
End EqualHelper.
