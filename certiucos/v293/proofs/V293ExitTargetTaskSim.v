(* Target-array assignment before the changed-priority TaskSim suffix. *)
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

Lemma V293_target_owned_pointer : forall br bg bp t tasks next nh R s,
 get(getabst s)abstcblsid=Some(abstcblist tasks) ->
 V293_current_task tasks next nh ->
 s|=SWINVt(V293_ready_inv br bg bp)t **R ->
 load(Tptr V293_tcb_type)(assertion.getmem s)(bp,4*Z.of_nat nh)%Z=Some(Vptr next).
Proof.
 intros br bg bp t tasks next nh R s Map [Range[st[msg Task]]] Held.
 destruct(V293_ready_switch_sound br bg bp t R s Held)
 as(ts&lo&hi&entries&Map'&Records&Rel&Loads).
 assert(ts=tasks)by congruence;subst ts.
 destruct Rel as[Lo[Hi[Nonempty[Bitmap[Length Table]]]]].
 destruct(Table _ _ _ _ Task)as(p&Bound&Priority&Slot).
 assert(p=nh)by(eapply V293_priority_repr_injective;[exact Bound|exact Range|symmetry;exact Priority]).
 subst p;destruct Loads as[LoadLo [LoadHi [LoadGroup Pointer]]];rewrite <-Slot;apply Pointer;exact Range.
Qed.

Lemma V293_target_assignment_TaskSim : forall pc po pi ip ph Ch O li I Post t ks
 ge le M M' ir ci table high target bp bh bo nh next,
 InOS(SKIP,(kenil,ks))(pumerge po pi) ->
 get le table=None ->get le high=None ->get le target=None ->
 get ge table=Some(bp,Tarray(Tptr V293_tcb_type)13) ->
 get ge high=Some(bh,Tint8) ->get ge target=Some(bo,Tptr V293_tcb_type) ->
 load Tint8 M(bh,0%Z)=Some(V293_byteval nh) ->nh<13 ->
 load(Tptr V293_tcb_type)M(bp,4*Z.of_nat nh)%Z=Some(Vptr next) ->
 store(Tptr V293_tcb_type)M(bo,0%Z)(Vptr next)=Some M' ->
 satp(ge,le,M,ir,(false,nil,ci))O(CurLINV li t) ->
 satp(ge,le,M',ir,(false,nil,ci))O(CurLINV li t) ->
 TaskSim(pc,(po,pi,ip))(SKIP,(kenil,ks))(ge,le,M',ir,(false,nil,ci))ph Ch O li I Post t ->
 TaskSim(pc,(po,pi,ip))(curs(V293_OSSched_target_update table high target),(kenil,ks))
 (ge,le,M,ir,(false,nil,ci))ph Ch O li I Post t.
Proof.
 intros pc po pi ip ph Ch O li I Post t ks ge le M M' ir ci table high target bp bh bo nh next
 Context TN HN ON TG HG OG High Range Pointer Store Before After Tail.
 destruct(V293_eval_pointer_array ge le M table high V293_tcb_type bp bh nh(Vptr next)
 TN HN TG HG High Range Pointer)as(Value&TR).
 assert(TL:evaltype(evar target)(ge,le,M)=Some(Tptr V293_tcb_type)).
 { cbn[evaltype get_lenv get_genv];rewrite ON,OG;reflexivity. }
 assert(Addr:evaladdr(evar target)(ge,le,M)=Some(Vptr(bo,Int.zero))).
 { cbn[evaladdr get_lenv get_genv];rewrite ON,OG;reflexivity. }
 unfold V293_OSSched_target_update.
 eapply V293_changed_pure_TaskSim with(ks:=ks)
 (C':=(cure(V293_OSSched_target_expr table high),(kenil,kassignr(evar target)(Tptr V293_tcb_type) ks)));
 [exact Context|reflexivity|reflexivity| | |exact Before| ].
 - intros[x E];discriminate E.
 - intros Mf Mall Join;eapply stmt_step;[reflexivity| ];eapply sassign_step.
   + rewrite(lmachLib.evaltype_mono _ _ _ _ _ _ Join);exact TL.
   + rewrite(lmachLib.evaltype_mono _ _ _ _ _ _ Join);exact TR.
   + apply eq_vptr;eauto.
 - eapply V293_changed_expr_TaskSim with(m:=(ge,le,M))(m':=(ge,le,M))
   (c':=curs(sskip(Some(Vptr next))))(ke':=kenil);
   [ |reflexivity| |exact Before| ].
   + apply cstepLib.evalval_imply_estepstar;exact Value.
   + eapply V293_context_inos;[exact Context|reflexivity|reflexivity].
   + eapply V293_changed_pure_TaskSim with(ks:=ks)
     (C':=(cure(eaddrof(evar target)),(kenil,kassignl(Vptr next)(Tptr V293_tcb_type) ks)));
     [exact Context|reflexivity|reflexivity| | |exact Before| ].
     * intros[x E];discriminate E.
     * intros;eapply stmt_step;[reflexivity|apply sassignrv_step].
     * eapply V293_changed_expr_TaskSim with(m:=(ge,le,M))(m':=(ge,le,M))
       (c':=curs(sskip(Some(Vptr(bo,Int.zero)))))(ke':=kenil);
       [ |reflexivity| |exact Before| ].
       -- apply cstepLib.evaladdr_imply_estepstar;exact Addr.
       -- eapply V293_context_inos;[exact Context|reflexivity|reflexivity].
       -- eapply V293_invariant_cstep_TaskSim;[ | | |exact After|exact Tail].
          ++ eapply V293_context_inos;[exact Context|reflexivity|reflexivity].
          ++ intros[x E];discriminate E.
          ++ intros Mf Mall Join;destruct(lmachLib.store_mono _ _ _ _ _ _ _ Join Store)as(Mall'&WholeStore).
             exists Mall';split.
             ** apply map_join_comm;eapply join_store_join;[apply map_join_comm;exact Join|exact Store|exact WholeStore].
             ** split.
                --- eapply stmt_step;[reflexivity| ];eapply sassignend_step;try reflexivity;exact WholeStore.
                --- intros;eapply V293_store_cstep_unique;[exact WholeStore|eassumption].
Qed.


Section OwnedTarget.
Variables br bg bp bc bh bo bk saved_block : block.
Variable rest : list(addr*type).
Variable target : var.
Variables next t : tid.
Variables nh nc : nat.
Variable saved_value : val.
Let Cells := ((bc,0%Z),Tint8)::((bh,0%Z),Tint8)::((bk,0%Z),Tint32)::rest.
Let G := V293_ready_storage_inv br bg bp target V293_tcb_type Cells.
Let TargetOwned (v:val) (c:int32) := Amapsto(saved_block,0%Z)Tint32 true saved_value **
 (SWINVt(V293_ready_inv br bg bp)t **
 (V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval nc) **
 (V293_owned_record_cell((bh,0%Z),Tint8,V293_byteval nh) **
 (V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,v) **
 (V293_owned_record_cell((bk,0%Z),Tint32,Vint32 c) **V293_storage rest))))).

Lemma V293_target_owned_local : forall ge le M ir aux O op v c,
 (ge,le,M,ir,aux,O,op)|=TargetOwned v c ->satp(ge,le,M,ir,aux)O(CurLINV V293_shared_li t).
Proof.
 intros ge le M ir aux O op v c Held;eapply V293_pending_local with(op:=op).
 unfold TargetOwned,SWINVt in Held;fold(CurTid t)in Held;sep auto.
Qed.


(* The public entry derives the RHS and allocates no additional assumption. *)
Theorem V293_exit_target_TaskSim : forall pc po pi ip A ge M ir top ci O op
 table high current counter f body caller tail tau d1 d2 saved oldtarget c tasks,
 getsched(pc,A)=V293_scheduler ->
 po f=Some(tau,d1,d2,body) ->V293_skip_client_state(SKIP,(kenil,tail)) ->
 V293_current_task tasks next nh ->nc<256 ->nh<>nc ->
 get(V293_cpu_lenv saved saved_block)table=None ->
 get(V293_cpu_lenv saved saved_block)target=None ->
 get(V293_cpu_lenv saved saved_block)high=None ->
 get(V293_cpu_lenv saved saved_block)current=None ->
 get(V293_cpu_lenv saved saved_block)counter=None ->
 get ge table=Some(bp,Tarray(Tptr V293_tcb_type)13) ->
 get ge high=Some(bh,Tint8) ->get ge current=Some(bc,Tint8) ->get ge counter=Some(bk,Tint32) ->
 get ge target=Some(bo,Tptr V293_tcb_type) ->
 get O abstcblsid=Some(abstcblist tasks) ->indom tasks t ->V293_highest_ready tasks next ->
 (ge,V293_cpu_lenv saved saved_block,M,ir,(false,nil,top::ci),O,op)|=TargetOwned oldtarget c ->
 TaskSim(pc,(po,pi,ip))
 (curs(V293_OSSched_target_update table high target),
 (kenil,kseq(sif(V293_OSSched_different high current)
 (sseq(V293_OSSched_increment counter)
 (sseq(sskip None)(V293_interrupt_handoff high current target)))(sskip None))
 (kseq(sprim excrit)(kseq sret(kcall f body caller tail)))))
 (ge,V293_cpu_lenv saved saved_block,M,ir,(false,nil,top::ci))
 (pc,A)(curs(hapi_code(spec_seq sched(spec_done None))),(kenil,tail))O V293_shared_li G
 (fun st=>satp(fst st)(snd st)(RDYINV G t **LINV V293_shared_li t nil))t.
Proof.
 intros pc po pi ip A ge M ir top ci O op table high current counter f body caller tail tau d1 d2 saved oldtarget c tasks
 Sched Bind Cases NextTask Nc Different TN ON HN CN KN TG HG CG KG OG Map Member Highest Held.
 assert(Range:nh<13)by exact(proj1 NextTask).
 assert(Ready:(ge,V293_cpu_lenv saved saved_block,M,ir,(false,nil,top::ci),O,op)|=
 SWINVt(V293_ready_inv br bg bp)t **Atrue)by(unfold TargetOwned in Held;sep auto).
 pose proof(V293_target_owned_pointer br bg bp t tasks next nh Atrue (ge,V293_cpu_lenv saved saved_block,M,ir,(false,nil,top::ci),O,op) Map NextTask Ready)as Pointer.
 assert(High:load Tint8 M(bh,0%Z)=Some(V293_byteval nh)).
 { eapply V293_record_star_load_l with(s:=(ge,V293_cpu_lenv saved saved_block,M,ir,(false,nil,top::ci),O,op))
 (P:=V293_owned_record_cell((bh,0%Z),Tint8,V293_byteval nh))(Q:=Atrue).
   - intros st H;apply V293_owned_record_cell_load;exact H.
   - unfold TargetOwned in Held;clear Ready;sep auto. }
 assert(ToWrite:(ge,V293_cpu_lenv saved saved_block,M,ir,(false,nil,top::ci),O,op)|=
 V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,oldtarget) **
 (Amapsto(saved_block,0%Z)Tint32 true saved_value **
 (SWINVt(V293_ready_inv br bg bp)t **
 (V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval nc) **
 (V293_owned_record_cell((bh,0%Z),Tint8,V293_byteval nh) **
 (V293_owned_record_cell((bk,0%Z),Tint32,Vint32 c) **V293_storage rest))))))
 by(unfold TargetOwned in Held;clear Ready;sep auto).
 destruct(V293_owned_record_cell_update (bo,0%Z) (Tptr V293_tcb_type) oldtarget (Vptr next) _ _ _ _ _ _ _ _
 eq_refl ToWrite)as(M'&Store&Written).
 assert(AfterOwned:(ge,V293_cpu_lenv saved saved_block,M',ir,(false,nil,top::ci),O,op)|=TargetOwned(Vptr next)c)
 by(unfold TargetOwned;clear -Written;sep auto).
 assert(Inside:InOS(SKIP,(kenil,kseq(sprim excrit)(kseq sret(kcall f body caller tail))))(pumerge po pi)).
 { eapply V293_context_inos with(ks:=kcall f body caller tail);
   [eapply V293_bound_call_inos;exact Bind|reflexivity|reflexivity]. }
 assert(LocalBefore:satp(ge,V293_cpu_lenv saved saved_block,M,ir,(false,nil,top::ci))O(CurLINV V293_shared_li t)).
 { eapply V293_target_owned_local;exact Held. }
 assert(LocalAfter:satp(ge,V293_cpu_lenv saved saved_block,M',ir,(false,nil,top::ci))O(CurLINV V293_shared_li t)).
 { eapply V293_target_owned_local;exact AfterOwned. }
 eapply V293_target_assignment_TaskSim;
 [ |exact TN|exact HN|exact ON|exact TG|exact HG|exact OG|exact High|exact Range|exact Pointer|exact Store|exact LocalBefore|exact LocalAfter| ].
 - eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
 - eapply V293_changed_pure_TaskSim with(ks:=kseq(sprim excrit)(kseq sret(kcall f body caller tail)));
   [exact Inside|reflexivity|reflexivity| | |exact LocalAfter| ].
   + intros[x E];discriminate E.
   + intros;eapply stmt_step;[reflexivity|apply sskip_step].
   + unfold G,Cells;eapply V293_exit_changed_TaskSim with(next:=next)(nh:=nh)(nc:=nc)
     (bo:=bo)(saved_value:=saved_value)(tasks:=tasks)(c:=c);try eassumption;try lia.
Qed.
End OwnedTarget.
