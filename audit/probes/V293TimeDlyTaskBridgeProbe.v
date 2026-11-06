(* Literal TWO-task heap, a disjoint writable canary and original shared slots.
   The lower-priority task is already ready; this is not wakeup reachability. *)
Require Import CertiOS.audit.probes.V293TimeDlyBlockingProbe.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TimeDlyTaskBridge.
Require Import CertiOS.certiucos.v293.proofs.V293TimeDlyBlocking.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickTaskBridge.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293SharedStateWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.code.V293OSTimeDly.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition DTframecells : list V293_record_cell :=
 [((90%positive,0%Z),Tint32,Vint32(Int.repr 99))].
Definition DTall := DLcells++(DLextra++(DLlow++DTframecells)).
Definition DTmem := OwnershipCellsMemory DTall.
Definition DTabstract := V293_shared_fixture_abs OwnershipReady DLtasks
 (emp:EcbMod.map)(Int.repr 37).
Definition DTblocked := set DLtasks OwnershipReady
 (Int.repr 4,wait os_stat_time(Int.repr 3),Vnull).
Definition DTfinalabs := set DTabstract abstcblsid(abstcblist DTblocked).
Definition DTstate M O := V293_target_wstate DLge DLle M O.
Definition DTexecution P ks Mf :=
 cstepstar P(curs(V293_dly_updates 103%Z 106%Z 105%Z 400%Z 401%Z),(kenil,ks))
 (DLge,DLle,DTmem)(SKIP,(kenil,ks))(DLge,DLle,Mf).

Lemma DTdeleted : del DLtasks OwnershipReady=
 sig OwnershipWaiting(Int.repr 6,rdy,Vptr(120%positive,Int.repr 7)).
Proof.
 apply TcbMod.extensionality;intro t.
 change(get(del DLtasks OwnershipReady)t=
 get(sig OwnershipWaiting(Int.repr 6,rdy,Vptr(120%positive,Int.repr 7)))t).
 rewrite map_del_sem.
 match goal with |-context[if ?d then _ else _]=>destruct d as[Same|Other]end.
 - subst t;rewrite map_get_sig' by discriminate;reflexivity.
 - unfold DLtasks. destruct(TcbMod.eq_dec t OwnershipWaiting)as[E|E].
   + subst t;rewrite map_get_set,map_get_sig;reflexivity.
   + rewrite map_get_set' by congruence;rewrite map_get_sig' by congruence;
     rewrite map_get_sig' by congruence;reflexivity.
Qed.
Lemma DTlow_owned : forall s, s|=V293_owned_record_cells DLlow ->
 s|=V293_owned_task_records(del DLtasks OwnershipReady).
Proof.
 intros s H;rewrite DTdeleted.
 change(s|=V293_owned_task_record OwnershipWaiting(Int.repr 6)rdy(Vptr(120%positive,Int.repr 7)) **Aemp).
 apply astar_r_aemp_intro;exists 6;exists 0;apply astar_l_apure_intro;
 [exact H|repeat split;try reflexivity;lia].
Qed.
Theorem DTentry : DTstate DTmem DTabstract|=
 V293_owned_record_cells DLcells **(V293_owned_record_cells DLextra **
 (V293_owned_task_records(del DLtasks OwnershipReady) **
 (V293_shared_fields OwnershipReady DLtasks(emp:EcbMod.map)(Int.repr 37) **
 V293_owned_record_cells DTframecells))).
Proof.
 assert(Cells:DTstate DTmem emp|=V293_owned_record_cells DTall).
 { apply OwnershipCellsSpatial.
   - vm_compute;repeat split;intros;intuition congruence.
   - repeat constructor;reflexivity. }
 assert(Physical:DTstate DTmem emp|=V293_owned_record_cells DLcells **
 (V293_owned_record_cells DLextra **(V293_owned_record_cells DLlow **V293_owned_record_cells DTframecells))).
 { apply(proj1(OwnershipCellsAppend DLcells(DLextra++(DLlow++DTframecells))_))in Cells.
   eapply astar_mono;[intros s H;exact H| |exact Cells].
   intros s H;apply OwnershipCellsAppend in H.
   eapply astar_mono;[intros st H';exact H'| |exact H].
   intros st H';apply OwnershipCellsAppend in H';exact H'. }
 assert(Joint:DTstate DTmem DTabstract|=
 (V293_owned_record_cells DLcells **(V293_owned_record_cells DLextra **
 (V293_owned_record_cells DLlow **V293_owned_record_cells DTframecells))) **
 V293_shared_fields OwnershipReady DLtasks(emp:EcbMod.map)(Int.repr 37)).
 { eapply V293_target_wstate_star with(m1:=DTmem)(m2:=emp)(o1:=emp)(o2:=DTabstract).
   - apply map_join_emp.
   - apply map_join_comm;apply map_join_emp.
   - exact Physical.
   - exact(V293_shared_fixture_fields OwnershipReady DLtasks(emp:EcbMod.map)(Int.repr 37)). }
 assert(Reordered:DTstate DTmem DTabstract|=V293_owned_record_cells DLcells **
 (V293_owned_record_cells DLextra **(V293_owned_record_cells DLlow **
 (V293_shared_fields OwnershipReady DLtasks(emp:EcbMod.map)(Int.repr 37) **V293_owned_record_cells DTframecells))))
 by(clear -Joint;sep auto).
 eapply astar_mono;[intros s H;exact H| |exact Reordered].
 intros s H;eapply astar_mono;[intros st H';exact H'| |exact H].
 intros st H';eapply astar_mono;[apply DTlow_owned|intros st' H'';exact H''|exact H'].
Qed.

Theorem DTliteral : forall P ks sd,exists Mf,
 DTexecution P ks Mf /\
 spec_step sd(spec_prim(cons(Vint32(Int.repr 3))nil)V293_dly_block_step)
 DTabstract(END None)DTfinalabs /\
 V293_task_records Mf DTblocked /\V293_priority_table DLentries DTblocked /\
 V293_bitmap_tasks 64 0 DTblocked /\
 load Tint32 Mf(90%positive,0%Z)=Some(Vint32(Int.repr 99)) /\
 get DTfinalabs curtid=Some(oscurt OwnershipReady) /\
 get DTfinalabs abstcblsid=Some(abstcblist DTblocked) /\
 get DTfinalabs absecblsid=Some(absecblist(emp:EcbMod.map)) /\
 get DTfinalabs ostmid=Some(ostm(Int.repr 37)).
Proof.
 intros P ks sd.
 destruct(V293_OSTimeDly_updates_refines 103%Z 106%Z 105%Z 400%Z 401%Z
 10%positive 11%positive 12%positive 60%positive 30%positive 31%positive 0%Z 4(Int.repr 3)
 P ks DLge DLle DTmem(fun _=>false)(false,nil,nil)DTabstract(spec_done None)sd
 (V293_owned_record_cells DTframecells)Int.zero(V293_byteval 0)80 0 DLentries DLtasks Vnull
 (emp:EcbMod.map)(Int.repr 37)
 DLenv ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(change(54<=4294967295)%Z;lia)
 ltac:(discriminate)DLtable DLbitmap eq_refl DTentry)
 as(Mf&Exec&Step&Records&Table&Bitmap&Returned).
 exists Mf;split;[exact Exec| ]. split;[exact Step| ]. split;[exact Records| ].
 split;[exact Table| ]. split;[exact Bitmap| ]. split.
 - assert(Canary:DTstate Mf DTfinalabs|=V293_owned_record_cells DTframecells **Atrue)
   by(clear -Returned;sep auto).
   change(load Tint32(getmem(DTstate Mf DTfinalabs))(90%positive,0%Z)=Some(Vint32(Int.repr 99))).
   eapply V293_record_star_load_l;[ |exact Canary].
   apply V293_owned_record_cells_load;left;reflexivity.
 - repeat split;reflexivity.
Qed.

(* Only the abstract task-slot commit varies, AFTER the same physical run. *)
Definition DTchosenabs(commit:bool):=if commit then DTfinalabs else DTabstract.
Theorem DTchosen : forall commit,exists Mf,
 DTexecution(fun _=>None)kstop Mf /\
 V293_task_records Mf DTblocked /\
 V293_bitmap_tasks 64 0 DTblocked /\
 load Tint32 Mf(90%positive,0%Z)=Some(Vint32(Int.repr 99)) /\
 get(DTchosenabs commit)abstcblsid=Some(abstcblist(if commit then DTblocked else DLtasks)).
Proof.
 intro commit;destruct(DTliteral(fun _=>None)kstop(fun _ _=>False))
 as(Mf&Executed&Step&Records&Table&Bitmap&Canary&Current&Slot&Events&Time).
 exists Mf;split;[exact Executed| ]. split;[exact Records| ]. split;[exact Bitmap| ].
 split;[exact Canary| ]. destruct commit;[exact Slot|reflexivity].
Qed.

(* Semantic inequality, not just a failure of definitional conversion. *)
Theorem DTstale_slot_mismatch :
 get DTabstract abstcblsid<>Some(abstcblist DTblocked).
Proof.
 intro Same;change(Some(abstcblist DLtasks)=Some(abstcblist DTblocked))in Same.
 inversion Same.
Qed.
