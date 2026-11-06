(* The priority pointer is published before the ready bitmap.  A relation
   suitable at successful return need not hold at the intervening excrit.
   This is an invariant integration obstruction, not a kernel counterexample. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293InitPriorityTable.
Require Import CertiOS.certiucos.v293.proofs.V293InitReadyPayload.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPriorityHook.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293InitAllRecords.
Require Import CertiOS.certiucos.v293.proofs.V293CanonicalInitReturn.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFunction.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitEntry.
Require Import CertiOS.certiucos.v293.proofs.V293NullBytes.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Lemma V293_creation_null_slot_not_ready : forall entries tasks lo hi p,
 V293_init_priority_table entries tasks -> V293_bitmap_tasks lo hi tasks ->
 p<13 -> nth p entries Vnull=Vnull -> ~V293_bitmap_ready lo hi p.
Proof.
 intros entries tasks lo hi p Table Bitmap Range Empty Ready.
 destruct(proj1(Bitmap p Range)Ready)as(t&msg&Lookup).
 exact(proj1(V293_init_priority_null_exact entries tasks p Table Range)Empty
   t rdy msg Lookup).
Qed.

Lemma V293_creation_insert_before_ready_rejected : forall entries tasks lo hi p t,
 V293_init_priority_table entries tasks -> V293_bitmap_tasks lo hi tasks ->
 p<13 -> nth p entries Vnull=Vnull ->
 ~V293_bitmap_tasks lo hi(set tasks t(Int.repr(Z.of_nat p),rdy,Vnull)).
Proof.
 intros entries tasks lo hi p t Table Bitmap Range Empty Updated.
 apply(V293_creation_null_slot_not_ready entries tasks lo hi p Table Bitmap Range Empty).
 apply(proj2(Updated p Range)). exists t. exists Vnull. apply map_get_set.
Qed.

Lemma V293_creation_pointer_before_insert_rejected : forall entries tasks p t,
 V293_init_priority_table entries tasks -> p<13 -> get tasks t=None ->
 ~V293_init_priority_table(update_nth_val p entries(Vptr t))tasks.
Proof.
 intros entries tasks p t Table Range Fresh Published.
 assert(Len:length entries=13)by exact(proj1(proj1 Table)).
 destruct(proj1(V293_init_priority_pointer_exact _ _ p t Published Range)
   (V293_init_priority_nth_same entries p(Vptr t)ltac:(lia)))as(st&msg&Lookup).
 change(TcbMod.get tasks t=Some(Int.repr(Z.of_nat p),st,msg))in Lookup.
 change(TcbMod.get tasks t=None)in Fresh. congruence.
Qed.

(* The existing ready relation is deliberately only task-to-slot.  Keeping
   the old task map can satisfy it despite an extra unpublished pointer. *)
Lemma V293_creation_old_ready_rel_preserved : forall entries tasks lo hi p replacement,
 V293_ready_rel lo hi entries tasks -> nth p entries Vnull=Vnull ->
 V293_ready_rel lo hi(update_nth_val p entries replacement)tasks.
Proof.
 intros entries tasks lo hi p replacement (Low&High&Nonempty&Bitmap&Len&Forward) Empty.
 split;[exact Low | ]. split;[exact High | ]. split;[exact Nonempty | ].
 split;[exact Bitmap | ]. split;[rewrite V293_priority_update_length;exact Len | ].
 intros t priority status message Lookup.
 destruct(Forward t priority status message Lookup)as(q&Range&Priority&Slot).
 exists q. split;[exact Range | ]. split;[exact Priority | ].
 rewrite V293_init_priority_nth_other;[exact Slot | ]. intro Same;subst q.
 rewrite Empty in Slot;discriminate.
Qed.

Definition V293_publication_old_bitmap br bg lo hi : list V293_record_cell :=
 [((br,0%Z),Tint8,V293_byteval lo);((br,1%Z),Tint8,V293_byteval hi);
  ((bg,0%Z),Tint8,V293_byteval(V293_ready_group lo hi))].

(* Actual priority store, excrit, and argument evaluation reach the second
   call while retaining exactly the old ready bytes and initialized records.
   The two rejected maps differ only by the usual abstract ready insertion. *)
Theorem V293_OS_TCBInit_publication_window :
 forall P f hook_init hook_create caller ks ge le M ir aux O op enabled si ci
 bp bc table bt base p reserved br bg lo hi entries tasks cells F,
 let t:=(bt,Int.repr base) in
 let tasks':=set tasks t(Int.repr(Z.of_nat p),rdy,Vnull) in
 let frame:=V293_rdy_raw_cells
  (V293_publication_old_bitmap br bg lo hi++V293_priority_hole entries table 0%Z p++cells)
  (V293_owned_task_records tasks' ** F) in
 get le 101%Z=Some(bp,Tint8) -> get le 108%Z=Some(bc,Tptr V293_tcb_type) ->
 get le 92%Z=None -> get ge 92%Z=Some(table,Tarray(Tptr V293_tcb_type)13) ->
 lo<256 -> hi<256 -> p<13 -> V293_init_priority_table entries tasks ->
 V293_bitmap_tasks lo hi tasks -> nth p entries Vnull=Vnull -> get tasks t=None ->
 (ge,le,M,ir,aux,O,op) |= V293_rdy_raw_cells
  (V293_tcb_priority_cells bp bc table bt base p(Vptr reserved))frame ->
 exists Mf,
 V293_local_steps P
  (curs(sskip None),(kenil,V293_tcb_first_hook_cont f hook_init hook_create caller ks))
  ((ge,le,M),ir,(enabled,si,ci))
  (curs(sfexec hook_create[Vptr t][Tptr V293_tcb_type]),
   (kenil,V293_tcb_second_hook_cont f hook_init hook_create caller ks))
  ((ge,le,Mf),ir,(enabled,si,ci)) /\
 (ge,le,Mf,ir,aux,O,op) |= V293_rdy_raw_cells
  (V293_tcb_priority_cells bp bc table bt base p(Vptr t))frame /\
 load(Tptr V293_tcb_type)Mf(table,(4*Z.of_nat p)%Z)=Some(Vptr t) /\
 load Tint8 Mf(br,0%Z)=Some(V293_byteval lo) /\
 load Tint8 Mf(br,1%Z)=Some(V293_byteval hi) /\
 V293_init_priority_table(update_nth_val p entries(Vptr t))tasks' /\
 ~V293_init_priority_table(update_nth_val p entries(Vptr t))tasks /\
 ~V293_bitmap_tasks lo hi tasks' /\
 V293_ready_rel(fst(V293_ready_set_rows lo hi p))(snd(V293_ready_set_rows lo hi p))
  (update_nth_val p entries(Vptr t))tasks'.
Proof.
 intros P f hook_init hook_create caller ks ge le M ir aux O op enabled si ci
 bp bc table bt base p reserved br bg lo hi entries tasks cells F t tasks' frame
 Priority Pointer Local Global Low High Range Table Bitmap Empty Fresh Entry.
 destruct(V293_OS_TCBInit_priority_to_second_hook P f hook_init hook_create caller ks ge le M ir aux O op
  frame enabled si ci bp bc table bt base p(Vptr reserved)
  Priority Pointer Local Global Range Entry)as(Mf&Exec&Final&Missing).
 exists Mf. split;[exact Exec | ]. split;[exact Final | ].
 assert(Flat:(ge,le,Mf,ir,aux,O,op) |= V293_rdy_raw_cells
  (V293_tcb_priority_cells bp bc table bt base p(Vptr t)++
   V293_publication_old_bitmap br bg lo hi++V293_priority_hole entries table 0%Z p++cells)
  (V293_owned_task_records tasks' ** F)).
 { unfold frame in Final. rewrite V293_raw_cells_append. exact Final. }
 split.
 - change(load(Tptr V293_tcb_type)(getmem(ge,le,Mf,ir,aux,O,op))
     (table,(4*Z.of_nat p)%Z)=Some(Vptr t)).
   eapply V293_rdy_raw_load;[ |reflexivity |exact Flat].
   apply in_or_app;left. unfold V293_tcb_priority_cells;cbn;auto.
 - split.
   + change(load Tint8(getmem(ge,le,Mf,ir,aux,O,op))(br,0%Z)=Some(V293_byteval lo)).
     eapply V293_rdy_raw_load;[ |apply V293_byte_type;lia |exact Flat].
     apply in_or_app;right. apply in_or_app;left. unfold V293_publication_old_bitmap;cbn;tauto.
   + split.
     * change(load Tint8(getmem(ge,le,Mf,ir,aux,O,op))(br,1%Z)=Some(V293_byteval hi)).
       eapply V293_rdy_raw_load;[ |apply V293_byte_type;lia |exact Flat].
       apply in_or_app;right. apply in_or_app;left. unfold V293_publication_old_bitmap;cbn;tauto.
     * split;[apply V293_init_priority_insert;assumption | ]. split.
       -- apply V293_creation_pointer_before_insert_rejected;assumption.
       -- split.
          ++ apply(V293_creation_insert_before_ready_rejected entries tasks lo hi p t);assumption.
          ++ apply V293_init_ready_insert;assumption.
Qed.
