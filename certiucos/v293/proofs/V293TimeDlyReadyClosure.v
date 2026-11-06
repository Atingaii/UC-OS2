(* Joint owned ready-state closure at the actual scheduler-call boundary.
   No scheduler execution, cache synchronization, or whole-API claim. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeDlyCallGlobal.
Require Import CertiOS.certiucos.v293.proofs.V293TimeDlyAllocated.
Require Import CertiOS.certiucos.v293.proofs.V293TimeDlyCallEntry.
Require Import CertiOS.certiucos.v293.proofs.V293TimeDlyBlocking.
Require Import CertiOS.certiucos.v293.proofs.V293TimeDlyTaskBridge.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickTaskBridge.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickRecordReassembly.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293LocalGlobalTrace.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyGlobalTrace.
Require Import CertiOS.certiucos.v293.code.V293OSTimeDlyCall.
Require Import CertiOS.certiucos.v293.code.V293OSTimeDly.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition V293_dly_local_frame byloc ba bs bi bl p duration R :=
 V293_owned_record_cells
 (cons ((byloc,0%Z),Tint8,V293_byteval(V293_prio_row p)) (cons ((ba,0%Z),Tint32,Vint32 duration) nil)) **
 (Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **
 (V293_owned_record_cells(V293_dly_guard_cells bi bl) **R)).

Lemma V293_dly_ready_resources : forall bc byloc ba bt br bg bp base p duration
 lo hi entries tasks message events now R ge le M ir au O op,
 p<13 ->(0<=base<=Int.max_unsigned)%Z ->
 get ge OSTCBCur=Some(bc,Tptr V293_tcb_type) ->
 V293_ready_rel lo hi entries
 (set tasks(bt,Int.repr base)(Int.repr(Z.of_nat p),wait os_stat_time duration,message)) ->
 (ge,le,M,ir,au,O,op)|=V293_owned_record_cells
 (V293_dly_cells bc byloc ba bt br bg base p duration duration
 (V293_byteval(V293_prio_row p))lo hi(V293_ready_group lo hi)) **
 (V293_owned_record_cells(V293_dly_record_extra bt base p message) **
 (V293_owned_task_records(del tasks(bt,Int.repr base)) **
 (V293_shared_fields(bt,Int.repr base)
 (set tasks(bt,Int.repr base)(Int.repr(Z.of_nat p),wait os_stat_time duration,message))events now **
 (V293_owned_record_cells(V293_priority_cells bp 0%Z entries) **R)))) ->
 V293_ready_loads M br bg bp lo hi entries /\
 (ge,le,M,ir,au,O,op)|=V293_ready_full br bg bp(bt,Int.repr base) **
 (V293_owned_record_cells
 (cons ((byloc,0%Z),Tint8,V293_byteval(V293_prio_row p)) (cons ((ba,0%Z),Tint32,Vint32 duration) nil)) **R).
Proof.
 intros bc byloc ba bt br bg bp base p duration lo hi entries tasks message events now
 R ge le M ir au O op Pb Base Global Rel Owned.
 assert(U:Int.unsigned(Int.repr base)=base)by(apply Int.unsigned_repr;exact Base).
 destruct(V293_prio_coordinates p Pb)as[Y X].
 destruct(V293_mask_byte_value(V293_prio_row p)ltac:(lia))as[_ MaskY].
 destruct(V293_mask_byte_value(V293_prio_bit p)X)as[_ MaskX].
 set(blocked:=set tasks(bt,Int.repr base)
 (Int.repr(Z.of_nat p),wait os_stat_time duration,message)).
 set(Tail:=V293_owned_record_cells(V293_ready_cells br bg bp lo hi entries) **
 (Amapsto(bc,0%Z)(Tptr V293_tcb_type)true(Vptr(bt,Int.repr base)) **
 (V293_shared_fields(bt,Int.repr base)blocked events now **
 (V293_owned_record_cells
 (cons ((byloc,0%Z),Tint8,V293_byteval(V293_prio_row p)) (cons ((ba,0%Z),Tint32,Vint32 duration) nil)) **R)))).
 assert(Record:(ge,le,M,ir,au,O,op)|=
 V293_owned_record_cells
 (V293_record_layout(bt,Int.repr base)p(wait os_stat_time duration)message 0) **
 (V293_owned_task_records(del tasks(bt,Int.repr base)) **Tail)).
 { unfold Tail,blocked,V293_ready_cells,V293_record_layout;cbn[fst snd];rewrite U,MaskY,MaskX.
   unfold V293_dly_cells,V293_dly_record_extra in Owned.
   cbn[app V293_owned_record_cells]in Owned|-*.
   unfold V293_owned_record_cell in Owned|-*.
   clear -Owned;sep auto. }
 assert(Canonical:(ge,le,M,ir,au,O,op)|=V293_owned_task_records blocked **Tail).
 { unfold blocked;apply V293_owned_task_records_reassemble.
   eapply astar_mono;[ |intros s H;exact H|exact Record].
   intros s H;exists p;exists 0;apply astar_l_apure_intro;
   [exact H|repeat split;try reflexivity;lia]. }
 assert(Loads:V293_ready_loads M br bg bp lo hi entries).
 { assert(ExactCells:(ge,le,M,ir,au,O,op)|=
   V293_owned_record_cells(V293_ready_cells br bg bp lo hi entries) **Atrue)
   by(unfold Tail in Canonical;clear -Canonical;sep auto).
   apply sat_split in ExactCells.
   destruct ExactCells as(m1&m2&o1&o2&JM&JO&Cells&Rest).
   eapply V293_ready_loads_sub;[exists m2;exact JM| ].
   exact(V293_ready_cells_loads br bg bp lo hi entries(ge,le,m1,ir,au,o1,op)
   (proj1(proj2(proj2(proj2(proj2 Rel)))))Cells). }
 assert(Ready:(ge,le,M,ir,au,O,op)|=V293_ready_payload br bg bp blocked **
 (Amapsto(bc,0%Z)(Tptr V293_tcb_type)true(Vptr(bt,Int.repr base)) **
 (V293_shared_fields(bt,Int.repr base)blocked events now **
 (V293_owned_record_cells
 (cons ((byloc,0%Z),Tint8,V293_byteval(V293_prio_row p)) (cons ((ba,0%Z),Tint32,Vint32 duration) nil)) **R)))).
 { unfold V293_ready_payload;apply astar_assoc_intro.
   eapply astar_mono;[intros s H;exact H| |exact Canonical].
   unfold Tail;apply astar_mono;[ |intros s H;exact H].
   intros s H;exists lo;exists hi;exists entries;apply astar_l_apure_intro;[exact H|exact Rel]. }

 assert(Full:(ge,le,M,ir,au,O,op)|=
 (GV OSTCBCur @(Tptr V293_tcb_type)|->Vptr(bt,Int.repr base)) **
 (V293_shared_fields(bt,Int.repr base)blocked events now **
 (V293_ready_payload br bg bp blocked **
 (V293_owned_record_cells
 (cons ((byloc,0%Z),Tint8,V293_byteval(V293_prio_row p)) (cons ((ba,0%Z),Tint32,Vint32 duration) nil)) **R)))).
 { assert(Reordered:(ge,le,M,ir,au,O,op)|=
   Amapsto(bc,0%Z)(Tptr V293_tcb_type)true(Vptr(bt,Int.repr base)) **
   (V293_shared_fields(bt,Int.repr base)blocked events now **
   (V293_ready_payload br bg bp blocked **
   (V293_owned_record_cells
   (cons ((byloc,0%Z),Tint8,V293_byteval(V293_prio_row p)) (cons ((ba,0%Z),Tint32,Vint32 duration) nil)) **R))))by(clear -Ready;sep auto).
   apply sat_split in Reordered.
   destruct Reordered as(m1&m2&o1&o2&JM&JO&Pointer&Rest).
   apply sat_split';exists m1;exists m2;exists o1;exists o2.
   split;[exact JM| ];split;[exact JO| ];split;[ |exact Rest].
   unfold Agvarmapsto,Aptrmapsto;exists bc.
   apply astar_l_agvarenv_intro;[exact Pointer|split;[reflexivity|exact Global]]. }
 split;[exact Loads| ];unfold V293_ready_full;clear -Full;sep auto.
Qed.

Lemma V293_dly_ready_rel_after : forall lo hi p entries tasks message bt base duration,
 p<13 ->lo<256 ->hi<256 ->
 V293_priority_table entries tasks ->V293_bitmap_tasks lo hi tasks ->
 get tasks(bt,Int.repr base)=Some(Int.repr(Z.of_nat p),rdy,message) ->
 (exists q,q<13 /\ q<>p /\ V293_bitmap_ready lo hi q) ->
 V293_ready_rel(fst(V293_ready_clear_rows lo hi p))
 (snd(V293_ready_clear_rows lo hi p))entries
 (set tasks(bt,Int.repr base)(Int.repr(Z.of_nat p),wait os_stat_time duration,message)).
Proof.
 intros lo hi p entries tasks message bt base duration P Lo Hi Table Bitmap Task
 (q&Q&Different&Ready).
 assert(Bounds:fst(V293_ready_clear_rows lo hi p)<256 /\
 snd(V293_ready_clear_rows lo hi p)<256).
 { unfold V293_ready_clear_rows;destruct(p<?8)eqn:E;cbn[fst snd].
   - apply Nat.ltb_lt in E;split;[exact(proj1(V293_rekey_byte_arithmetic lo p Lo E))|exact Hi].
   - apply Nat.ltb_ge in E;split;[exact Lo|exact(proj1(V293_rekey_byte_arithmetic hi(p-8)Hi ltac:(lia)))]. }
 destruct Bounds as[L H];split;[exact L| ];split;[exact H| ];split.
 - exists q;apply V293_ready_clear_membership;[exact P|exact Q|split;assumption].
 - split.
   + eapply V293_dly_bitmap_tasks; eassumption.
   + eapply V293_tick_priority_table; eassumption.
Qed.

(* Stable executable interface: the input has split cells, not final ownership. *)
Theorem V293_dly_global_call_ready:forall pc po pi ip T les aus t cge cles CM cle ge caller M ir enabled si ci O op sd R
 f current rows group y ticks nesting lock sched saved ba byloc bs bc bt br bg bi bl
 base p duration delay lo hi entries tasks message events now bp,
 get cles t=Some cle ->
 po f=Some(V293_dly_function current rows group y ticks nesting lock sched saved) ->
 ticks<>y ->ticks<>saved ->y<>saved ->ba<>byloc ->ba<>bs ->byloc<>bs ->
 fresh M ba ->fresh M byloc ->fresh M bs ->
 let le:=V293_dly_call_lenv ticks y saved ba byloc bs in
 V293_dly_env current rows group y ticks bc byloc ba br bg ge le ->
 get le nesting=None ->get ge nesting=Some(bi,Tint8) ->
 get le lock=None ->get ge lock=Some(bl,Tint8) ->
 p<13 ->lo<256 ->hi<256 ->(0<=base)%Z ->(base+54<=Int.max_unsigned)%Z ->
 get ge OSTCBCur=Some(bc,Tptr V293_tcb_type) ->
 (exists q,q<13 /\ q<>p /\ V293_bitmap_ready lo hi q) ->
 duration<>Int.zero ->V293_priority_table entries tasks ->V293_bitmap_tasks lo hi tasks ->
 get tasks(bt,Int.repr base)=Some(Int.repr(Z.of_nat p),rdy,message) ->
 (ge,le,M,ir,(enabled,si,ci),O,op)|=V293_owned_record_cells
 (V293_dly_call_cells bc bt br bg bi bl base p delay lo hi) **
 (V293_owned_record_cells(V293_dly_record_extra bt base p message) **
 (V293_owned_task_records(del tasks(bt,Int.repr base)) **
 (V293_shared_fields(bt,Int.repr base)tasks events now **
 (V293_owned_record_cells(V293_priority_cells bp 0%Z entries) **R)))) ->
 let outer:=kcall f(V293_dly_full_body current rows group y ticks nesting lock sched saved)caller kstop in
 let blocked:=set tasks(bt,Int.repr base)(Int.repr(Z.of_nat p),wait os_stat_time duration,message) in
 let O':=set O abstcblsid(abstcblist blocked) in
 let cleared:=V293_ready_clear_rows lo hi p in
 exists Mf,
 V293_global_steps(pc,(po,pi,ip))(cge,cles,CM)
 (V293_local_global_at T les aus t(curs(scall f[econst32 duration]),(kenil,kstop))((ge,caller,M),ir,(enabled,si,ci)))
 (V293_local_global_at T les aus t(curs(scall sched nil),(kenil,kseq sret outer))((ge,le,Mf),ir,(enabled,si,ci))) /\
 spec_step sd(spec_prim(cons(Vint32 duration)nil)V293_dly_block_step)O(END None)O' /\
 V293_task_records Mf blocked /\V293_priority_table entries blocked /\
 V293_bitmap_tasks(fst cleared)(snd cleared)blocked /\
 V293_ready_loads Mf br bg bp(fst cleared)(snd cleared)entries /\
 (ge,le,Mf,ir,(enabled,si,ci),O',op)|=
 V293_ready_full br bg bp(bt,Int.repr base) **
 V293_dly_local_frame byloc ba bs bi bl p duration R.
Proof.
 intros pc po pi ip T les aus t cge cles CM cle ge caller M ir enabled si ci O op sd R
 f current rows group y ticks nesting lock sched saved ba byloc bs bc bt br bg bi bl
 base p duration delay lo hi entries tasks message events now bp
 Get Bind TY TS YS BAY BAS BYS FreshA FreshY FreshS le Env Nn Gn Nl Gl
 Pb Lo Hi Base Limit Global Other Positive Table Bits Task Held outer blocked O' cleared.
 destruct(V293_dly_global_call_to_sched_refines pc po pi ip T les aus t cge cles CM cle
 ge caller M ir enabled si ci O op sd
 (V293_owned_record_cells(V293_priority_cells bp 0%Z entries) **R)
 f current rows group y ticks nesting lock sched saved ba byloc bs bc bt br bg bi bl
 base p duration delay lo hi entries tasks message events now
 Get Bind TY TS YS BAY BAS BYS FreshA FreshY FreshS Env Nn Gn Nl Gl
 Pb Lo Hi Base Limit Positive Table Bits Task Held)
 as(Mf&Run&Step&Records&Prio&Bitmap&Returned).
 assert(Rel:V293_ready_rel(fst cleared)(snd cleared)entries blocked).
 { unfold cleared,blocked;eapply V293_dly_ready_rel_after;eassumption. }
 assert(Reordered:(ge,le,Mf,ir,(enabled,si,ci),O',op)|=V293_owned_record_cells
 (V293_dly_cells bc byloc ba bt br bg base p duration duration(V293_byteval(V293_prio_row p))
 (fst cleared)(snd cleared)(V293_ready_group(fst cleared)(snd cleared))) **
 (V293_owned_record_cells(V293_dly_record_extra bt base p message) **
 (V293_owned_task_records(del tasks(bt,Int.repr base)) **
 (V293_shared_fields(bt,Int.repr base)blocked events now **
 (V293_owned_record_cells(V293_priority_cells bp 0%Z entries) **
 (Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **
 (V293_owned_record_cells(V293_dly_guard_cells bi bl) **R)))))))
 by(clear -Returned;sep auto).
 pose proof(V293_dly_ready_resources bc byloc ba bt br bg bp base p duration
 (fst cleared)(snd cleared)entries tasks message events now _ ge le Mf ir(enabled,si,ci)O' op
 Pb ltac:(lia)Global Rel Reordered)as[Loads Ready].
 exists Mf;split;[exact Run| ];split;[exact Step| ];split;[exact Records| ];
 split;[exact Prio| ];split;[exact Bitmap| ];split;[exact Loads| ].
 unfold V293_dly_local_frame;clear -Ready;sep auto.
Qed.
