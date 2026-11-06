(* The existing ready payload is reconstructed on the same return heap.
   Neither CPU hook implementation nor abstract shared-state commit is supplied. *)
Require Import CertiOS.certiucos.v293.proofs.V293CanonicalInitReturn.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293InitPriorityTable.
Require Import CertiOS.certiucos.v293.proofs.V293InitPublishRecords.
Require Import CertiOS.certiucos.v293.proofs.V293PublishRecords.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBClear.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293InitAllRecords.
Require Import CertiOS.certiucos.v293.proofs.V293StartRecord.
Require Import CertiOS.certiucos.v293.proofs.V293NullBytes.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFunction.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitEntry.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPriorityHook.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPublish.
Require Import CertiOS.certiucos.v293.proofs.V293TCBCallSuccess.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitPrefix.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitFunction.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Coq.Sorting.Permutation Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition V293_init_other_row br lo hi p : V293_record_cell :=
 ((br,if p <? 8 then 1%Z else 0%Z),Tint8,V293_byteval(if p <? 8 then hi else lo)).

Lemma V293_init_bitmap_insert : forall lo hi (tasks:TcbMod.map) (t:tid) p,
 p<13 -> get tasks t=None -> V293_bitmap_tasks lo hi tasks ->
 V293_bitmap_tasks (fst(V293_ready_set_rows lo hi p)) (snd(V293_ready_set_rows lo hi p))
  (set tasks t (Int.repr(Z.of_nat p),rdy,Vnull)).
Proof.
 intros lo hi tasks t p Range Fresh Bitmap q QR.
 rewrite V293_ready_set_membership by assumption. split.
 - intros [Same | Old].
   + subst q. exists t. exists Vnull. apply map_get_set.
   + destruct(proj1(Bitmap q QR)Old)as(u&msg&Lookup).
     assert(u<>t)by(intro E;subst u;unfold priority in Fresh;rewrite Fresh in Lookup;discriminate).
     exists u. exists msg. rewrite map_get_set' by congruence. exact Lookup.
 - intros(u&msg&Lookup). destruct(tidspec.beq u t)eqn:Same.
   + apply tidspec.beq_true_eq in Same;subst u. rewrite map_get_set in Lookup.
     inversion Lookup. left. eapply V293_priority_repr_injective;[exact QR |exact Range |congruence].
   + apply tidspec.beq_false_neq in Same. rewrite map_get_set' in Lookup by congruence.
     right. apply(proj2(Bitmap q QR)). exists u. exists msg. exact Lookup.
Qed.

Lemma V293_init_ready_insert : forall lo hi entries (tasks:TcbMod.map) (t:tid) p,
 lo<256 -> hi<256 -> p<13 -> get tasks t=None ->
 V293_bitmap_tasks lo hi tasks -> V293_init_priority_table entries tasks -> nth p entries Vnull=Vnull ->
 V293_ready_rel (fst(V293_ready_set_rows lo hi p)) (snd(V293_ready_set_rows lo hi p))
  (update_nth_val p entries(Vptr t)) (set tasks t (Int.repr(Z.of_nat p),rdy,Vnull)).
Proof.
 intros lo hi entries tasks t p L H Range Fresh Bitmap Table Null.
 assert(Bounds:fst(V293_ready_set_rows lo hi p)<256 /\ snd(V293_ready_set_rows lo hi p)<256).
 { unfold V293_ready_set_rows. destruct(p <? 8)eqn:E;cbn[fst snd].
   - apply Nat.ltb_lt in E. pose proof(V293_rekey_byte_arithmetic lo p L E)as(_&B&_). auto.
   - apply Nat.ltb_ge in E. pose proof(V293_rekey_byte_arithmetic hi (p-8) H ltac:(lia))as(_&B&_). auto. }
 destruct Bounds as [L' H']. split;[exact L' | ]. split;[exact H' | ]. split.
 - exists p. apply V293_ready_set_membership;[exact Range |exact Range |left;reflexivity].
 - split;[apply V293_init_bitmap_insert;assumption | ].
   exact(proj1(V293_init_priority_insert entries tasks t p rdy Vnull Table Range Null Fresh)).
Qed.

Lemma V293_init_owned_append : forall before after R,
 V293_owned_record_cells before ** (V293_owned_record_cells after ** R) ==>
 V293_owned_record_cells(before++after) ** R.
Proof.
 induction before as[ | [[a tp] v] xs IH];intros after R s Held;cbn[V293_owned_record_cells]in *.
 - clear -Held;sep auto.
 - assert(K:s |= V293_owned_record_cell(a,tp,v) **
    (V293_owned_record_cells xs ** (V293_owned_record_cells after ** R)))by(clear -Held;sep auto).
   eapply astar_mono in K;[ |intros st H;exact H |apply IH]. clear -K;sep auto.
Qed.

Lemma V293_init_ready_pack : forall br bg bp lo hi p entries tasks prefix middle suffix,
 V293_ready_rel (fst(V293_ready_set_rows lo hi p)) (snd(V293_ready_set_rows lo hi p)) entries tasks ->
 V293_owned_priority_table bp entries **
 (V293_owned_task_records tasks ** V293_rdy_raw_cells
  (prefix++[((bg,0%Z),Tint8,V293_byteval(Nat.setbit(V293_ready_group lo hi)(V293_prio_row p)));
             ((br,Z.of_nat(V293_prio_row p)),Tint8,
               V293_byteval(Nat.setbit(V293_ready_row lo hi(V293_prio_row p))(V293_prio_bit p)))]++
   middle++V293_init_other_row br lo hi p::suffix) Atrue) ==>
 V293_ready_payload br bg bp tasks ** V293_rdy_raw_cells(prefix++middle++suffix) Atrue.
Proof.
 intros br bg bp lo hi p entries tasks prefix middle suffix Rel s Held.
 set(rows:=V293_ready_set_rows lo hi p).
 set(bytes:=[((br,0%Z),Tint8,V293_byteval(fst rows));
  ((br,1%Z),Tint8,V293_byteval(snd rows));
  ((bg,0%Z),Tint8,V293_byteval(V293_ready_group(fst rows)(snd rows)))] : list V293_record_cell).
 assert(Order:forall (A B C:list V293_record_cell) x y z,
  Permutation(A++[x;y]++B++z::C)(x::y::z::(A++B++C))).
 { intros A B C x y z. eapply Permutation_trans;[apply Permutation_app_swap_app | ].
   cbn[app]. apply perm_skip. apply perm_skip. repeat rewrite app_assoc.
   apply Permutation_sym. apply Permutation_middle. }
 assert(Ordered:s |= V293_owned_priority_table bp entries **
  (V293_owned_task_records tasks ** V293_rdy_raw_cells bytes
   (V293_rdy_raw_cells(prefix++middle++suffix) Atrue))).
 { eapply astar_mono;[intros st H;exact H | |exact Held].
   eapply astar_mono;[intros st H;exact H | ]. intros st H.
   rewrite <-V293_raw_cells_append.
   eapply V293_raw_cells_permutation;[ |exact H].
   unfold V293_prio_row. rewrite V293_ready_set_group_correct.
   unfold V293_init_other_row,V293_prio_bit,V293_ready_row,bytes,rows,V293_ready_set_rows.
   destruct(p <? 8);cbn[fst snd Z.of_nat Nat.eqb].
   - eapply Permutation_trans;[apply Order | ].
     cbn[app]. eapply Permutation_trans;[apply perm_swap | ].
     apply perm_skip. apply perm_swap.
   - eapply Permutation_trans;[apply Order | ].
     cbn[app]. eapply Permutation_trans;[apply perm_swap | ].
     eapply Permutation_trans;[apply perm_skip;apply perm_swap |apply perm_swap]. }
 assert(Raw:s |= V293_rdy_raw_cells bytes
  (V293_owned_priority_table bp entries **
   (V293_owned_task_records tasks ** V293_rdy_raw_cells(prefix++middle++suffix) Atrue))).
 { apply V293_raw_cells_frame_in.
   eapply astar_mono;[intros st H;exact H |apply V293_raw_cells_frame_in |exact Ordered]. }
 assert(Types:Forall(fun c=>let '(_,tp,v):=c in rule_type_val_match tp v=true)bytes).
 { unfold bytes. constructor;[apply V293_byte_type;exact(proj1 Rel) | ].
   constructor;[apply V293_byte_type;exact(proj1(proj2 Rel)) | ].
   constructor;[ |constructor]. apply V293_byte_type.
   unfold V293_ready_group. destruct(fst rows =? 0);destruct(snd rows =? 0);lia. }
 apply(V293_raw_record_ownership _ _ Types)in Raw.
 assert(Combined:s |= V293_owned_record_cells(bytes++V293_priority_cells bp 0%Z entries) **
  (V293_owned_task_records tasks ** V293_rdy_raw_cells(prefix++middle++suffix) Atrue)).
 { apply V293_init_owned_append. exact Raw. }
 assert(Ready:s |= V293_owned_task_records tasks **
  (V293_owned_record_cells(V293_ready_cells br bg bp (fst rows)(snd rows)entries) **
   V293_rdy_raw_cells(prefix++middle++suffix) Atrue))by(clear -Combined;sep auto).
 unfold V293_ready_payload.
 assert(Closed:forall st,st |= V293_owned_record_cells(V293_ready_cells br bg bp(fst rows)(snd rows)entries) ->
    st |= V293_ready_owned br bg bp tasks).
 { intros st Cells. exists(fst rows). exists(snd rows). exists entries. apply astar_l_apure_intro;assumption. }
 assert(K:s |= V293_owned_task_records tasks **
   (V293_ready_owned br bg bp tasks ** V293_rdy_raw_cells(prefix++middle++suffix) Atrue)).
 { eapply astar_mono;[intros st H;exact H | |exact Ready].
   eapply astar_mono;[exact Closed |intros st H;exact H]. }
 clear -K;sep auto.
Qed.

Theorem V293_OS_TCBInit_ready_return_under_hooks :
 forall entries tasks lo0 hi0 P f hi hc caller ks ge M ir aux O op enabled si ci
 b1 b2 b3 b4 b5 b6 b7 b8 b9 bf table bt base bh bg br bn bo obase present p n
 top bottom identity size ext options pc next old prev back frame,
 let g:=V293_ready_group lo0 hi0 in
 let r:=V293_ready_row lo0 hi0 (V293_prio_row p) in
 let le:=V293_tcb_function_env b1 b2 b3 b4 b5 b6 b7 b8 b9 in
 let blocks:=V293_tcb_function_blocks b1 b2 b3 b4 b5 b6 b7 b8 b9 in
 let tasks':=set tasks (bt,Int.repr base) (Int.repr(Z.of_nat p),rdy,Vnull) in
 let extra:=V293_priority_hole entries table 0%Z p++V293_init_other_row br lo0 hi0 p::frame in
 let tail:=V293_tcb_creation_tail bt base bh bg br bn bo obase present p prev g r n back++extra in
 let survivors:=V293_tcb_init_record_remainder bt base top bottom identity size ext options++
  [((bf,0%Z),Tptr V293_tcb_type,next);((table,(4*Z.of_nat p)%Z),Tptr V293_tcb_type,Vptr(bt,Int.repr base))]++extra in
 let after:=V293_pub_link_cells b8 bt base bh bg br bn bo obase present p
  (V293_pub_old_head present bo obase) Vnull (Vptr(bt,Int.repr base))
  (Nat.setbit g (V293_prio_row p)) (Nat.setbit r (V293_prio_bit p)) (S n) (Vptr(bt,Int.repr base)) in
 lo0<256 -> hi0<256 -> V293_bitmap_tasks lo0 hi0 tasks ->
 V293_init_priority_table entries tasks -> nth p entries Vnull=Vnull ->
 get ge 91%Z=Some(bf,Tptr V293_tcb_type) -> get ge 92%Z=Some(table,Tarray(Tptr V293_tcb_type) 13) ->
 V293_pub_env ge le 108%Z 93%Z 94%Z 95%Z 96%Z b8 bh bg br bn ->
 get tasks (bt,Int.repr base)=None -> p<13 -> NoDup blocks ->
 (0<=base)%Z -> (base+55<=Int.max_unsigned)%Z ->
 (0<=obase)%Z -> (obase+24<=Int.max_unsigned)%Z -> n<255 ->
 V293_tcb_init_values_valid top bottom identity size ext options ->
 rule_type_val_match (Tptr V293_tcb_type) next=true ->
 (forall t value, In (t,value) (TcbMod.lst tasks') -> ~In (fst t) blocks) ->
 (forall a tp v, In (a,tp,v) (tl after++survivors) -> ~In (fst a) blocks) ->
 V293_records_hook_return tasks' P hi bt base (V293_tcb_first_hook_cont f hi hc caller ks)
  ge le ir aux O op enabled si ci
  (V293_record_hook_cells b1 b2 b3 b4 b5 b6 b7 b8 b9 bf table bt base p
   top bottom identity size ext options next Vnull tail) ->
 V293_records_hook_return tasks' P hc bt base (V293_tcb_second_hook_cont f hi hc caller ks)
  ge le ir aux O op enabled si ci
  (V293_record_hook_cells b1 b2 b3 b4 b5 b6 b7 b8 b9 bf table bt base p
   top bottom identity size ext options next (Vptr(bt,Int.repr base)) tail) ->
 (ge,le,M,ir,aux,O,op)  |= V293_rdy_raw_cells
  (V293_tcb_init_old_fields bt base old ++
   V293_tcb_prefix_inputs b8 b1 b2 b3 b4 b5 b6 b7 pc p top bottom identity size ext options ++
   V293_tcb_prefix_links bf bt base (Vptr(bt,Int.repr base)) next ++
   ((b9,0%Z),Tint32,Vint32 Int.zero)::((table,(4*Z.of_nat p)%Z),Tptr V293_tcb_type,Vnull)::tail)
  (V293_owned_task_records tasks ** Atrue) ->
 exists Mf,
 V293_local_steps P
  (curs(V293_TCBInit_prefix 91%Z 108%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z
   (V293_TCBInit_success_suffix hi hc)),(kenil,kcall f (V293_TCBInit_function_body hi hc) caller ks))
  ((ge,le,M),ir,(enabled,si,ci))
  (curs(sskip(Some(Vint32 Int.zero))),(kenil,ks)) ((ge,caller,Mf),ir,(enabled,si,ci)) /\
 (ge,caller,Mf,ir,aux,O,op)  |= V293_owned_task_records tasks' **
  V293_rdy_raw_cells (tl after++survivors) Atrue /\
 (forall b tp k, In (b,tp) (V293_tcb_function_addresses b1 b2 b3 b4 b5 b6 b7 b8 b9) ->
  k<typelen tp -> get Mf (b,Z.of_nat k)=None) /\
 V293_init_priority_table(update_nth_val p entries(Vptr(bt,Int.repr base)))tasks' /\
 (ge,caller,Mf,ir,aux,O,op)  |=
 V293_ready_payload br bg table tasks' ** V293_rdy_raw_cells
  ([((bt,(base+20)%Z),Tcom_ptr 410%Z,V293_pub_old_head present bo obase);
    ((bt,(base+24)%Z),Tcom_ptr 410%Z,Vnull);
    ((bh,0%Z),Tptr V293_tcb_type,Vptr(bt,Int.repr base))]++
   [((bn,0%Z),Tint8,V293_byteval(S n))]++
   (if present then [((bo,(obase+24)%Z),Tcom_ptr 410%Z,Vptr(bt,Int.repr base))] else [])++
   V293_tcb_init_record_remainder bt base top bottom identity size ext options++
   ((bf,0%Z),Tptr V293_tcb_type,next)::frame) Atrue.
Proof.
 intros entries tasks lo0 hi0 P f hi hc caller ks ge M ir aux O op enabled si ci
 b1 b2 b3 b4 b5 b6 b7 b8 b9 bf table bt base bh bg br bn bo obase present p n
 top bottom identity size ext options pc next old prev back frame
 g r le blocks tasks' extra tail survivors after Low High Bitmap Canonical Null
 FreeGlobal TableGlobal PubEnv Fresh Range ND Base Bound OldBase OldBound Count Valid Next
 TasksAway CellsAway Hook1 Hook2 Entry.
 assert(G:g<256).
 { unfold g,V293_ready_group. destruct(lo0 =? 0);destruct(hi0 =? 0);lia. }
 assert(Row:r<256).
 { unfold r,V293_ready_row. destruct(V293_prio_row p =? 0);assumption. }
 destruct(V293_OS_TCBInit_canonical_return_under_hooks entries tasks P f hi hc caller ks ge M ir aux O op
 enabled si ci b1 b2 b3 b4 b5 b6 b7 b8 b9 bf table bt base bh bg br bn bo obase present p g r n
 top bottom identity size ext options pc next old prev back (V293_init_other_row br lo0 hi0 p::frame)
 Canonical Null FreeGlobal TableGlobal PubEnv Fresh Range ND Base Bound OldBase OldBound G Row Count Valid Next
 TasksAway CellsAway Hook1 Hook2 Entry)as(Mf&Exec&Final&Freed&NewCanonical&Joint).
 exists Mf. split;[exact Exec | ]. split;[exact Final | ]. split;[exact Freed | ].
 split;[exact NewCanonical | ].
 pose proof(V293_init_ready_insert lo0 hi0 entries tasks (bt,Int.repr base) p
 Low High Range Fresh Bitmap Canonical Null)as Rel.
 pose proof (V293_init_ready_pack br bg table lo0 hi0 p
 (update_nth_val p entries(Vptr(bt,Int.repr base))) tasks'
 [((bt,(base+20)%Z),Tcom_ptr 410%Z,V293_pub_old_head present bo obase);
  ((bt,(base+24)%Z),Tcom_ptr 410%Z,Vnull);
  ((bh,0%Z),Tptr V293_tcb_type,Vptr(bt,Int.repr base))]
 ([((bn,0%Z),Tint8,V293_byteval(S n))]++
  (if present then [((bo,(obase+24)%Z),Tcom_ptr 410%Z,Vptr(bt,Int.repr base))] else [])++
  V293_tcb_init_record_remainder bt base top bottom identity size ext options++
  [((bf,0%Z),Tptr V293_tcb_type,next)]) frame Rel)as Pack.
 specialize(Pack (ge,caller,Mf,ir,aux,O,op)).
 unfold after,V293_pub_link_cells in Joint. cbn[tl]in Joint.
 cbn[app]in Pack,Joint |- *.
 repeat rewrite <-app_assoc in Pack,Joint |- *.
 destruct present;exact(Pack Joint).
Qed.
Print Assumptions V293_OS_TCBInit_ready_return_under_hooks.
