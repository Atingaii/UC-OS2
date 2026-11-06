(* Continuous initialization-to-return with complete priority table and task
   records in one heap. Both original CPU hook contracts remain explicit. *)
Require Import CertiOS.certiucos.v293.proofs.V293InitPriorityTable.
Require Import CertiOS.certiucos.v293.proofs.V293InitPublishRecords.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBClear.
Require Import CertiOS.certiucos.v293.proofs.V293StartRecord.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFunction.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitEntry.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPriorityHook.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPublish.
Require Import CertiOS.certiucos.v293.proofs.V293TCBCallSuccess.
Require Import CertiOS.certiucos.v293.proofs.V293PublishRecords.
Require Import CertiOS.certiucos.v293.proofs.V293NullBytes.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitPrefix.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitFunction.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Coq.Sorting.Permutation Lia.
Import ListNotations.
Local Open Scope nat_scope.

Fixpoint V293_priority_hole (entries:list val) b off p : list V293_record_cell :=
 match entries,p with
  |  nil,_=>nil
  |  _::xs,O=>V293_priority_cells b (off+4)%Z xs
  |  v::xs,S q=>((b,off),Tptr V293_tcb_type,v)::V293_priority_hole xs b (off+4)%Z q
 end.

Lemma V293_priority_hole_split : forall entries p b off,
 p<length entries ->
 Permutation (V293_priority_cells b off entries)
 (((b,(off+4*Z.of_nat p)%Z),Tptr V293_tcb_type,nth p entries Vnull)::
  V293_priority_hole entries b off p).
Proof.
 induction entries as [  |  v xs IH ];intros [  |  p] b off Range;cbn in Range;try lia.
 - cbn[V293_priority_cells V293_priority_hole nth].
   replace (off+4*Z.of_nat 0)%Z with off by lia. reflexivity.
 - cbn[V293_priority_cells V293_priority_hole nth].
   pose proof (IH p b (off+4)%Z ltac:(lia)) as Tail.
   eapply Permutation_trans; [ apply perm_skip;exact Tail | ].
   replace (off+4*Z.of_nat(S p))%Z with (off+4+4*Z.of_nat p)%Z by lia.
   apply perm_swap.
Qed.
Lemma V293_priority_hole_update : forall entries p b off replacement,
 p<length entries ->
 V293_priority_hole (update_nth_val p entries replacement) b off p=
 V293_priority_hole entries b off p.
Proof.
 induction entries as [ | v xs IH];intros [ | p] b off replacement Range;
 cbn [length] in Range;try lia.
 - reflexivity.
 - cbn[V293_priority_hole update_nth_val]. f_equal;apply IH;lia.
Qed.
Lemma V293_canonical_priority_valid : forall entries tasks b off,
 V293_init_priority_table entries tasks ->
 Forall (fun cell=>let '(_,tp,v):=cell in rule_type_val_match tp v=true)
  (V293_priority_cells b off entries).
Proof.
 intros entries tasks b off [[Len Forward] Reverse].
 assert (Values:Forall(fun v=>rule_type_val_match(Tptr V293_tcb_type)v=true)entries).
 { apply Forall_forall. intros v Member. apply In_nth with (d:=Vnull) in Member.
   destruct Member as(p&Range&Slot). destruct(Reverse p ltac:(lia))as [ Null | (u&st&msg&Existing&Lookup) ].
   - rewrite <-Slot,Null;reflexivity.
   - rewrite <-Slot,Existing;reflexivity. }
 clear Len Forward Reverse. revert off. induction Values;intro off;cbn[V293_priority_cells ];constructor;auto.
Qed.

Lemma V293_priority_reassemble : forall entries tasks b p replacement R,
 V293_init_priority_table (update_nth_val p entries replacement) tasks ->
 p<length entries ->
 V293_rdy_raw_cells
 (((b,(4*Z.of_nat p)%Z),Tptr V293_tcb_type,replacement)::V293_priority_hole entries b 0%Z p) R ==>
 V293_owned_priority_table b(update_nth_val p entries replacement) ** R.
Proof.
 intros entries tasks b p replacement R Canonical Bound s Held.
 assert (UpdatedBound:p<length(update_nth_val p entries replacement)).
 { rewrite V293_priority_update_length;exact Bound. }
 pose proof(V293_priority_hole_split(update_nth_val p entries replacement)p b 0%Z UpdatedBound)as Order.
 rewrite V293_init_priority_nth_same in Order by exact Bound.
 rewrite V293_priority_hole_update in Order by exact Bound.
 replace (0+4*Z.of_nat p)%Z with (4*Z.of_nat p)%Z in Order by lia.
 apply(V293_raw_cells_permutation _ _ (Permutation_sym Order) R)in Held.
 apply(V293_raw_record_ownership _ R(V293_canonical_priority_valid _ _ _ _ Canonical))in Held.
 exact Held.
Qed.

Lemma V293_raw_cells_frame_in : forall cells A B,
 A ** V293_rdy_raw_cells cells B ==> V293_rdy_raw_cells cells(A ** B).
Proof.
 induction cells as [  |  [[a tp] v] cells IH ];intros A B s Held;cbn[V293_rdy_raw_cells]in *.
 - exact Held.
 - assert(K:s  |= Amapsto a tp true v ** (A ** V293_rdy_raw_cells cells B))by(clear -Held;sep auto).
   eapply astar_mono; [ intros st H;exact H | apply IH | exact K].
Qed.

Theorem V293_OS_TCBInit_canonical_return_under_hooks :
 forall entries tasks P f hi hc caller ks ge M ir aux O op enabled si ci
 b1 b2 b3 b4 b5 b6 b7 b8 b9 bf table bt base bh bg br bn bo obase present p g r n
 top bottom identity size ext options pc next old prev back frame,
 let le:=V293_tcb_function_env b1 b2 b3 b4 b5 b6 b7 b8 b9 in
 let blocks:=V293_tcb_function_blocks b1 b2 b3 b4 b5 b6 b7 b8 b9 in
 let tasks':=set tasks (bt,Int.repr base) (Int.repr(Z.of_nat p),rdy,Vnull) in
 let extra:=V293_priority_hole entries table 0%Z p++frame in
 let tail:=V293_tcb_creation_tail bt base bh bg br bn bo obase present p prev g r n back++extra in
 let survivors:=V293_tcb_init_record_remainder bt base top bottom identity size ext options++
  [((bf,0%Z),Tptr V293_tcb_type,next);((table,(4*Z.of_nat p)%Z),Tptr V293_tcb_type,Vptr(bt,Int.repr base))]++extra in
 let after:=V293_pub_link_cells b8 bt base bh bg br bn bo obase present p
  (V293_pub_old_head present bo obase) Vnull (Vptr(bt,Int.repr base))
  (Nat.setbit g (V293_prio_row p)) (Nat.setbit r (V293_prio_bit p)) (S n) (Vptr(bt,Int.repr base)) in
 V293_init_priority_table entries tasks -> nth p entries Vnull=Vnull ->
 get ge 91%Z=Some(bf,Tptr V293_tcb_type) -> get ge 92%Z=Some(table,Tarray(Tptr V293_tcb_type) 13) ->
 V293_pub_env ge le 108%Z 93%Z 94%Z 95%Z 96%Z b8 bh bg br bn ->
 get tasks (bt,Int.repr base)=None -> p<13 -> NoDup blocks ->
 (0<=base)%Z -> (base+55<=Int.max_unsigned)%Z ->
 (0<=obase)%Z -> (obase+24<=Int.max_unsigned)%Z -> g<256 -> r<256 -> n<255 ->
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
 V293_owned_priority_table table(update_nth_val p entries(Vptr(bt,Int.repr base))) **
 (V293_owned_task_records tasks' ** V293_rdy_raw_cells
  (tl after++V293_tcb_init_record_remainder bt base top bottom identity size ext options++
   ((bf,0%Z),Tptr V293_tcb_type,next)::frame) Atrue).
Proof.
 intros entries tasks P f hi hc caller ks ge M ir aux O op enabled si ci
 b1 b2 b3 b4 b5 b6 b7 b8 b9 bf table bt base bh bg br bn bo obase present p g r n
 top bottom identity size ext options pc next old prev back frame
 le blocks tasks' extra tail survivors after Canonical Null FreeGlobal TableGlobal PubEnv Fresh Range ND Base Bound
 OldBase OldBound G Row Count Valid Next TasksAway CellsAway Hook1 Hook2 Entry.
 destruct(V293_OS_TCBInit_prefix_return_records_under_hooks tasks P f hi hc caller ks ge M ir aux O op
 enabled si ci b1 b2 b3 b4 b5 b6 b7 b8 b9 bf table bt base bh bg br bn bo obase present p g r n
 top bottom identity size ext options pc next old Vnull prev back extra
 FreeGlobal TableGlobal PubEnv Fresh Range ND Base Bound OldBase OldBound G Row Count Valid Next
 TasksAway CellsAway Hook1 Hook2 Entry)as(Mf&Exec&Final&Freed).
 assert (NewCanonical:V293_init_priority_table(update_nth_val p entries(Vptr(bt,Int.repr base)))tasks').
 { apply V293_init_priority_insert;assumption. }
 exists Mf. split; [ exact Exec | ]. split; [ exact Final | ]. split; [ exact Freed | ].
 split; [ exact NewCanonical | ].
 set (rest:=tl after++V293_tcb_init_record_remainder bt base top bottom identity size ext options++
  ((bf,0%Z),Tptr V293_tcb_type,next)::frame).
 assert (TableFirst:(ge,caller,Mf,ir,aux,O,op) |=V293_rdy_raw_cells
  (((table,(4*Z.of_nat p)%Z),Tptr V293_tcb_type,Vptr(bt,Int.repr base))::
   V293_priority_hole entries table 0%Z p)
  (V293_owned_task_records tasks' ** V293_rdy_raw_cells rest Atrue)).
 { set(prefix:=tl after++V293_tcb_init_record_remainder bt base top bottom identity size ext options++
      [((bf,0%Z),Tptr V293_tcb_type,next)]).
   set(cells:=((table,(4*Z.of_nat p)%Z),Tptr V293_tcb_type,Vptr(bt,Int.repr base))::
     V293_priority_hole entries table 0%Z p).
   change ((ge,caller,Mf,ir,aux,O,op) |= V293_owned_task_records tasks' **
    V293_rdy_raw_cells (tl after++survivors) Atrue) in Final.
   replace (tl after++survivors) with (prefix++cells++frame) in Final.
   2:{ unfold prefix,cells,survivors,extra. repeat rewrite <-app_assoc;reflexivity. }
   assert(Shuffled:(ge,caller,Mf,ir,aux,O,op) |=V293_owned_task_records tasks' **
     V293_rdy_raw_cells cells(V293_rdy_raw_cells(prefix++frame)Atrue)).
   { eapply astar_mono; [ intros st H;exact H |   | exact Final].
     intros st H. apply(V293_raw_cells_permutation _ _ (Permutation_app_swap_app prefix cells frame) Atrue)in H.
     rewrite V293_raw_cells_append in H. exact H. }
   apply V293_raw_cells_frame_in in Shuffled.
   replace (prefix++frame) with rest in Shuffled.
   2:{ unfold prefix,rest. repeat rewrite <-app_assoc;reflexivity. }
   exact Shuffled.
 }
 eapply V293_priority_reassemble; [ exact NewCanonical |   | exact TableFirst].
 exact (ltac:(pose proof(proj1(proj1 Canonical));lia)).
Qed.
Print Assumptions V293_OS_TCBInit_canonical_return_under_hooks.
