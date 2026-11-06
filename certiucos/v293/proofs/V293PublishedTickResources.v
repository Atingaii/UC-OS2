(* Initialization-to-publication provenance with the two real CPU hook contracts
   still explicit. The separate scan is not a legal interrupt entry. *)
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitPrefix.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInit.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitEntry.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293TCBSuccessReturn.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293InitPublishRecords.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitTickZero.
Require Import CertiOS.certiucos.v293.proofs.V293PublishRecords.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPublish.
Require Import CertiOS.certiucos.v293.proofs.V293StartRecord.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTickLinkedEntry.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickTraversal.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFunction.
Require Import CertiOS.certiucos.v293.proofs.V293TCBCallSuccess.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPriorityHook.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitFunction.
Require Import CertiOS.certiucos.v293.code.V293OSTimeTick.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

(* The returned link list has Next, Prev, head, group, row, count, old Prev.
   Remove only Next and head; keep every other link in its original order. *)
Definition V293_published_link_spares (links:list V293_record_cell) := firstn 1 (tl links)++skipn 3 links.
Definition V293_published_tick_owned tasks bt base bh next spares links tail : asrt :=
 V293_owned_record_cell((bh,0%Z),Tptr V293_tcb_type,Vptr(bt,Int.repr base)) **
 (V293_tick_zero_node bt base next **
 (V293_owned_task_records tasks **
 V293_rdy_raw_cells spares
 (V293_rdy_raw_cells(V293_published_link_spares links)
 (V293_rdy_raw_cells tail Atrue)))).

(* Pure resource rearrangement, retaining the exact initialized remainder.
   In particular, delay is not inferred from the abstract ready status. *)
Lemma V293_published_tick_extract : forall tasks bc bt base bh bg br bn bo obase p g r n
 top bottom identity size ext options tail,
 let links:=tl(V293_pub_link_cells bc bt base bh bg br bn bo obase true p
 (Vptr(bo,Int.repr obase))Vnull(Vptr(bt,Int.repr base))g r n(Vptr(bt,Int.repr base)))in
 V293_owned_task_records tasks **
 V293_rdy_raw_cells(links++V293_tcb_init_record_remainder bt base top bottom identity size ext options++tail)Atrue ==>
 V293_published_tick_owned tasks bt base bh(bo,Int.repr obase)
 (V293_tcb_tick_spares bt base top bottom identity size ext options)links tail.
Proof.
 intros tasks bc bt base bh bg br bn bo obase p g r n top bottom identity size ext options tail links s Held.
 assert(Raw:s |= V293_rdy_raw_cells
 (((bh,0%Z),Tptr V293_tcb_type,Vptr(bt,Int.repr base))::
 ((bt,(base+44)%Z),Tint32,Vint32 Int.zero)::
 ((bt,(base+20)%Z),Tcom_ptr 410%Z,Vptr(bo,Int.repr obase))::nil)
 (V293_owned_task_records tasks **
 V293_rdy_raw_cells(V293_tcb_tick_spares bt base top bottom identity size ext options)
 (V293_rdy_raw_cells(V293_published_link_spares links)(V293_rdy_raw_cells tail Atrue)))).
 { unfold links,V293_pub_link_cells,V293_published_link_spares,V293_tcb_tick_spares,
   V293_tcb_init_record_remainder in Held|-*.
   cbn[tl firstn skipn app V293_rdy_raw_cells]in Held|-*;clear -Held;sep auto. }
 apply(V293_raw_record_ownership
 (((bh,0%Z),Tptr V293_tcb_type,Vptr(bt,Int.repr base))::
 ((bt,(base+44)%Z),Tint32,Vint32 Int.zero)::
 ((bt,(base+20)%Z),Tcom_ptr 410%Z,Vptr(bo,Int.repr obase))::nil) _
 ltac:(repeat constructor;reflexivity))in Raw.
 unfold V293_published_tick_owned,V293_tick_zero_node.
 cbn[V293_owned_record_cells]in Raw;clear -Raw;sep auto.
Qed.

(* Actual continuous source head assignment followed by a zero-delay iteration.
   Scanner storage is explicit; every other byte and all frame ownership return. *)
Theorem V293_published_head_then_zero_iteration : forall P ks ge le M ir enabled si ci O op
 ptcb head rows group bc bh bt base next scan R,
 get le ptcb=Some(bc,Tptr V293_tcb_type) ->
 get le head=None ->get ge head=Some(bh,Tptr V293_tcb_type) ->
 (0<=base)%Z ->(base+44<=Int.max_unsigned)%Z ->
 (ge,le,M,ir,(enabled,si,ci),O,op)|=Amapsto(bc,0%Z)(Tptr V293_tcb_type)true scan **
 (V293_owned_record_cell((bh,0%Z),Tptr V293_tcb_type,Vptr(bt,Int.repr base)) **
 (V293_tick_zero_node bt base next **R)) ->
 exists Mh Mf,
 store(Tptr V293_tcb_type)M(bc,0%Z)(Vptr(bt,Int.repr base))=Some Mh /\
 store(Tptr V293_tcb_type)Mh(bc,0%Z)(Vptr next)=Some Mf /\
 V293_local_steps P
 (curs(sseq(sassign(evar ptcb)(evar head))(V293_tick_iteration ptcb rows group)),(kenil,ks))
 ((ge,le,M),ir,(enabled,si,ci))
 (curs(sskip None),(kenil,ks))((ge,le,Mf),ir,(enabled,si,ci)) /\
 (ge,le,Mf,ir,(enabled,si,ci),O,op)|=
 V293_owned_record_cell((bc,0%Z),Tptr V293_tcb_type,Vptr next) **
 (V293_owned_record_cell((bh,0%Z),Tptr V293_tcb_type,Vptr(bt,Int.repr base)) **
 (V293_tick_zero_node bt base next **R)) /\
 load(Tptr V293_tcb_type)Mf(bc,0%Z)=Some(Vptr next) /\
 (forall b i,b<>bc \/(i<0)%Z \/(4<=i)%Z ->get Mf(b,i)=get M(b,i)).
Proof.
 intros P ks ge le M ir enabled si ci O op ptcb head rows group bc bh bt base next scan R
 Bind NoHead Head Base Limit Held.
 destruct(V293_ready_tick_head_execution P(kseq(V293_tick_iteration ptcb rows group)ks)
 ge le M ir(enabled,si,ci)O op ptcb head bc bh scan(bt,Int.repr base)_ Bind NoHead Head Held)
 as(Mh&HeadStore&HeadExec&HeadOwned&HeadRead&HeadOutside).
 assert(TickOwned:(ge,le,Mh,ir,(enabled,si,ci),O,op)|=
 V293_owned_record_cell((bc,0%Z),Tptr V293_tcb_type,Vptr(bt,Int.repr base)) **
 (V293_tick_zero_node bt base next **
 (V293_owned_record_cell((bh,0%Z),Tptr V293_tcb_type,Vptr(bt,Int.repr base)) **R)))
 by(clear -HeadOwned;sep auto).
 destruct(V293_tick_zero_iteration_owned_execution P ks ge le Mh ir enabled si ci O op
 ptcb rows group bc bt base next _ Bind Base Limit TickOwned)
 as(Mf&NextStore&TickExec&ScanRead&Final&TickOutside).
 exists Mh;exists Mf;split;[exact HeadStore| ];split;[exact NextStore| ];split.
 - eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sseq_step]| ].
   eapply V293_local_trans;[apply V293_csteps_local;exact HeadExec| ].
   eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sskip_step]|exact TickExec].
 - split;[clear -Final;sep auto| ];split;[exact ScanRead| ].
   intros b i Outside;rewrite TickOutside by exact Outside;apply HeadOutside;exact Outside.
Qed.

(* The initialization execution is continuous through publication and physical
   return/free, conditional on the two unchanged real hook contracts. *)
Theorem V293_TCBInit_returns_published_zero_under_hooks :
 forall tasks P f hi hc caller ks ge M ir aux O op enabled si ci
 b1 b2 b3 b4 b5 b6 b7 b8 b9 bf table bt base bh bg br bn bo obase p g r n
 top bottom identity size ext options pc next old slot prev back frame,
 let le:=V293_tcb_function_env b1 b2 b3 b4 b5 b6 b7 b8 b9 in
 let blocks:=V293_tcb_function_blocks b1 b2 b3 b4 b5 b6 b7 b8 b9 in
 let tasks':=set tasks (bt,Int.repr base) (Int.repr(Z.of_nat p),rdy,Vnull) in
 let tail:=V293_tcb_creation_tail bt base bh bg br bn bo obase true p prev g r n back++frame in
 let survivors:=V293_tcb_init_record_remainder bt base top bottom identity size ext options++
  [((bf,0%Z),Tptr V293_tcb_type,next);((table,(4*Z.of_nat p)%Z),Tptr V293_tcb_type,Vptr(bt,Int.repr base))]++frame in
 let after:=V293_pub_link_cells b8 bt base bh bg br bn bo obase true p
  (V293_pub_old_head true bo obase) Vnull (Vptr(bt,Int.repr base))
  (Nat.setbit g (V293_prio_row p)) (Nat.setbit r (V293_prio_bit p)) (S n) (Vptr(bt,Int.repr base)) in
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
   top bottom identity size ext options next slot tail) ->
 V293_records_hook_return tasks' P hc bt base (V293_tcb_second_hook_cont f hi hc caller ks)
  ge le ir aux O op enabled si ci
  (V293_record_hook_cells b1 b2 b3 b4 b5 b6 b7 b8 b9 bf table bt base p
   top bottom identity size ext options next (Vptr(bt,Int.repr base)) tail) ->
 (ge,le,M,ir,aux,O,op) |= V293_rdy_raw_cells
  (V293_tcb_init_old_fields bt base old ++
   V293_tcb_prefix_inputs b8 b1 b2 b3 b4 b5 b6 b7 pc p top bottom identity size ext options ++
   V293_tcb_prefix_links bf bt base (Vptr(bt,Int.repr base)) next ++
   ((b9,0%Z),Tint32,Vint32 Int.zero)::((table,(4*Z.of_nat p)%Z),Tptr V293_tcb_type,slot)::tail)
  (V293_owned_task_records tasks ** Atrue) ->
 exists Mf,
 V293_local_steps P
  (curs(V293_TCBInit_prefix 91%Z 108%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z
   (V293_TCBInit_success_suffix hi hc)),(kenil,kcall f (V293_TCBInit_function_body hi hc) caller ks))
  ((ge,le,M),ir,(enabled,si,ci))
  (curs(sskip(Some(Vint32 Int.zero))),(kenil,ks)) ((ge,caller,Mf),ir,(enabled,si,ci)) /\
 (ge,caller,Mf,ir,aux,O,op) |= V293_owned_task_records tasks' **
  V293_rdy_raw_cells (tl after++survivors) Atrue /\
 (forall b tp k, In (b,tp) (V293_tcb_function_addresses b1 b2 b3 b4 b5 b6 b7 b8 b9) ->
  k<typelen tp -> get Mf (b,Z.of_nat k)=None) /\
 (ge,caller,Mf,ir,aux,O,op) |= V293_published_tick_owned tasks' bt base bh(bo,Int.repr obase)
 (V293_tcb_tick_spares bt base top bottom identity size ext options)(tl after)
 ([((bf,0%Z),Tptr V293_tcb_type,next);((table,(4*Z.of_nat p)%Z),Tptr V293_tcb_type,Vptr(bt,Int.repr base))]++frame).
Proof.
 intros tasks P f hi hc caller ks ge M ir aux O op enabled si ci
 b1 b2 b3 b4 b5 b6 b7 b8 b9 bf table bt base bh bg br bn bo obase p g r n
 top bottom identity size ext options pc next old slot prev back frame
 le blocks tasks' tail survivors after FreeGlobal TableGlobal PubEnv Fresh Range ND Base Bound
 OldBase OldBound G Row Count Valid Next TasksAway CellsAway Hook1 Hook2 Entry.
 destruct(V293_OS_TCBInit_prefix_return_records_under_hooks tasks P f hi hc caller ks ge M ir aux O op
 enabled si ci b1 b2 b3 b4 b5 b6 b7 b8 b9 bf table bt base bh bg br bn bo obase true p g r n
 top bottom identity size ext options pc next old slot prev back frame
 FreeGlobal TableGlobal PubEnv Fresh Range ND Base Bound OldBase OldBound G Row Count Valid Next
 TasksAway CellsAway Hook1 Hook2 Entry)as(Mf&Exec&Final&Freed).
 exists Mf;split;[exact Exec| ];split;[exact Final| ];split;[exact Freed| ].
 exact(V293_published_tick_extract tasks' b8 bt base bh bg br bn bo obase p
 (Nat.setbit g(V293_prio_row p))(Nat.setbit r(V293_prio_bit p))(S n)
 top bottom identity size ext options
 ([((bf,0%Z),Tptr V293_tcb_type,next);((table,(4*Z.of_nat p)%Z),Tptr V293_tcb_type,Vptr(bt,Int.repr base))]++frame)
 (ge,caller,Mf,ir,aux,O,op)Final).
Qed.
