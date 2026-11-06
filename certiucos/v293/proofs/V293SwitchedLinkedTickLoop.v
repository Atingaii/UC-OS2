(* A real while cutpoint with canonical ready ownership. The current task
   may differ from the scanned waiting task. This is not an ISR entry. *)
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTickLinkedEntry.
Require Import CertiOS.certiucos.v293.proofs.V293SwitchedCountdownClosure.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLoop.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickTaskBridge.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.code.V293OSTimeTick.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Local Open Scope nat_scope.

(* The guard reads the actual owned scanner and canonical priority field.
   No successful load or evaluation is supplied as an input. *)
Lemma V293_ready_tick_guard : forall br bg bp current tasks bt base p status message
 R ge le M ir aux O op ptcb bc,
 get le ptcb=Some(bc,Tptr V293_tcb_type) ->
 (0<=base)%Z ->(base+50<=Int.max_unsigned)%Z ->p<13 ->
 get O abstcblsid=Some(abstcblist tasks) ->
 get tasks(bt,Int.repr base)=Some(Int.repr(Z.of_nat p),status,message) ->
 (ge,le,M,ir,aux,O,op)|=V293_ready_full br bg bp current **
 (V293_owned_record_cell((bc,0%Z),Tptr V293_tcb_type,Vptr(bt,Int.repr base)) **R) ->
 evalval(V293_tick_guard ptcb)(ge,le,M)=
 Some(Vint32(if Nat.eqb p 12 then Int.zero else Int.one)).
Proof.
 intros br bg bp current tasks bt base p status message R ge le M ir aux O op
 ptcb bc Bind Base Limit Range Slot Task Held.
 assert(Records:V293_task_records M tasks).
 { eapply V293_ready_full_records;[exact Slot|exact Held]. }
 destruct(Records _ _ _ _ Task)as(q&Q&Priority&Fields&Status).
 assert(Same:p=q)by(eapply V293_priority_repr_injective;eassumption).
 subst q;unfold V293_tcb_updated_loads in Fields.
 destruct Fields as(Read&Rest).
 cbn[fst snd]in Read;rewrite Int.unsigned_repr in Read by lia.
 assert(Pointer:load(Tptr V293_tcb_type)M(bc,0%Z)=Some(Vptr(bt,Int.repr base))).
 { assert(Cell:(ge,le,M,ir,aux,O,op)|=
   V293_owned_record_cell((bc,0%Z),Tptr V293_tcb_type,Vptr(bt,Int.repr base)) **Atrue)
   by(clear -Held;sep auto).
   exact(V293_record_star_load_l _ _ _ _ _ (V293_owned_record_cell_load _ _ _) _ Cell). }
 eapply V293_tick_guard_eval;try eassumption;lia.
Qed.

(* Stable seam: unroll one real guard, execute the complete source iteration,
   and return to the residual while. All effects are conclusions. *)
Theorem V293_ready_countdown_while_step : forall br bg bp current tasks bt base p d message
 R P ks ge le M ir enabled si ci O op sd ptcb rows group bc next,
 get le ptcb=Some(bc,Tptr V293_tcb_type) ->
 (0<=base)%Z ->(base+50<=Int.max_unsigned)%Z ->p<13 ->p<>12 ->
 (2<=d<=Int.max_unsigned)%Z ->
 get O abstcblsid=Some(abstcblist tasks) ->
 get tasks(bt,Int.repr base)=Some(Int.repr(Z.of_nat p),wait os_stat_time(Int.repr d),message) ->
 GoodInvAsrt R ->
 (ge,le,M,ir,(enabled,si,ci),O,op)|=V293_ready_full br bg bp current **
 (V293_owned_record_cell((bc,0%Z),Tptr V293_tcb_type,Vptr(bt,Int.repr base)) **
 (V293_owned_record_cell((bt,(base+20)%Z),Tcom_ptr 410%Z,Vptr next) **R)) ->
 exists Md Mf,
 let tasks':=set tasks(bt,Int.repr base)(Int.repr(Z.of_nat p),wait os_stat_time(Int.repr(d-1)),message)in
 let O':=set O abstcblsid(abstcblist tasks')in
 store Tint32 M(bt,(base+44)%Z)(Vint32(Int.repr(d-1)))=Some Md /\
 store(Tptr V293_tcb_type)Md(bc,0%Z)(Vptr next)=Some Mf /\
 V293_local_steps P
 (curs(swhile(V293_tick_guard ptcb)(V293_tick_iteration ptcb rows group)),(kenil,ks))
 ((ge,le,M),ir,(enabled,si,ci))
 (curs(swhile(V293_tick_guard ptcb)(V293_tick_iteration ptcb rows group)),(kenil,ks))
 ((ge,le,Mf),ir,(enabled,si,ci)) /\
 spec_step sd(spec_prim nil(V293_tick_wait_step(bt,Int.repr base)))O(END None)O' /\
 (ge,le,Mf,ir,(enabled,si,ci),O',op)|=V293_ready_full br bg bp current **
 (V293_owned_record_cell((bc,0%Z),Tptr V293_tcb_type,Vptr next) **
 (V293_owned_record_cell((bt,(base+20)%Z),Tcom_ptr 410%Z,Vptr next) **R)) /\
 load Tint32 Mf(bt,(base+44)%Z)=Some(Vint32(Int.repr(d-1))) /\
 load(Tptr V293_tcb_type)Mf(bc,0%Z)=Some(Vptr next) /\
 (forall b i,(b<>bt \/(i<base+44)%Z \/(base+48<=i)%Z) ->
 (b<>bc \/(i<0)%Z \/(4<=i)%Z) ->get Mf(b,i)=get M(b,i)).
Proof.
 intros br bg bp current tasks bt base p d message R P ks ge le M ir enabled si ci O op sd
 ptcb rows group bc next Bind Base Limit Range Nonidle Delay Slot Task Good Held.
 pose proof(V293_ready_tick_guard br bg bp current tasks bt base p _ message
 _ ge le M ir(enabled,si,ci)O op ptcb bc Bind Base Limit Range Slot Task Held)as Guard.
 rewrite(proj2(Nat.eqb_neq p 12)Nonidle)in Guard.
 destruct(V293_ready_countdown_linked_iteration br bg bp current tasks bt base
 (Int.repr(Z.of_nat p))d message R P
 (kseq(swhile(V293_tick_guard ptcb)(V293_tick_iteration ptcb rows group))ks)
 ge le M ir enabled si ci O op sd ptcb rows group bc next
 Bind Base ltac:(lia)Delay Slot Task Good Held)
 as(Md&Mf&Store&Next&Execute&Abstract&After&Read&Pointer&Outside).
 exists Md;exists Mf;cbn zeta;split;[exact Store| ];split;[exact Next| ];split.
 - eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply swhile_step]| ].
   eapply V293_local_trans.
   { apply V293_csteps_local;apply V293_expr_steps;apply evalval_imply_estepstar;exact Guard. }
   eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply svwhilet_step;reflexivity]| ].
   eapply V293_local_trans;[exact Execute| ].
   eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sskip_step]|apply V293_local_refl].
 - split;[exact Abstract| ];split;[exact After| ];split;[exact Read| ];split;assumption.
Qed.
