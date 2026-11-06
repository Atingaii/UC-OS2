(* The real field initializer supplies runtime delay ownership missing from
   canonical ready records. Next is an explicit frame resource. The later tick
   fragment starts on the same heap, but is not a legal interrupt entry. *)
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293StartRecord.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293NullBytes.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickTraversal.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInit.
Require Import CertiOS.certiucos.v293.code.V293OSTimeTick.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

(* Remove only delay44 from the existing initializer remainder. *)
Definition V293_tcb_tick_spares bt base top bottom identity size ext options :=
 let cells:=V293_tcb_init_record_remainder bt base top bottom identity size ext options in
 firstn 2 cells++skipn 3 cells.

(* All eighteen initialized fields are retained, without overlapping ownership.
   The initializer's pointer parameter becomes the scan pointer; its other
   seven parameters and all remaining TCB fields stay in the explicit frame. *)
Lemma V293_initialized_tick_resources : forall bt base p top bottom identity size ext options
 bc bp bs bb bi bz be bo next R,
 p<13 ->(0<=base<=Int.max_unsigned)%Z ->
 V293_tcb_init_values_valid top bottom identity size ext options ->
 V293_rdy_raw_cells
 (V293_tcb_init_final_fields bt base p top bottom identity size ext options++
  V293_tcb_init_input_cells bc bp bs bb bi bz be bo bt base p top bottom identity size ext options)
 (V293_owned_record_cell((bt,(base+20)%Z),Tcom_ptr 410%Z,Vptr next) **R) ==>
 V293_owned_record_cell((bc,0%Z),Tptr V293_tcb_type,Vptr(bt,Int.repr base)) **
 (V293_tick_zero_node bt base next **
 (V293_owned_task_record(bt,Int.repr base)(Int.repr(Z.of_nat p))rdy Vnull **
 V293_rdy_raw_cells(V293_tcb_tick_spares bt base top bottom identity size ext options)
 (V293_rdy_raw_cells
  (tl(V293_tcb_init_input_cells bc bp bs bb bi bz be bo bt base p top bottom identity size ext options)) R))).
Proof.
 intros bt base p top bottom identity size ext options bc bp bs bb bi bz be bo next R
 Range Bound Valid s Held.
 rewrite V293_raw_cells_append in Held.
 apply(V293_initialized_ready_record bt base p top bottom identity size ext options
 _ Range Bound Valid)in Held.
 assert (Raw : s |= V293_rdy_raw_cells
 (((bc,0%Z),Tptr V293_tcb_type,Vptr(bt,Int.repr base))::
  ((bt,(base+44)%Z),Tint32,Vint32 Int.zero)::nil)
 (V293_owned_record_cell((bt,(base+20)%Z),Tcom_ptr 410%Z,Vptr next) **
 (V293_owned_task_record(bt,Int.repr base)(Int.repr(Z.of_nat p))rdy Vnull **
 V293_rdy_raw_cells(V293_tcb_tick_spares bt base top bottom identity size ext options)
 (V293_rdy_raw_cells
  (tl(V293_tcb_init_input_cells bc bp bs bb bi bz be bo bt base p top bottom identity size ext options)) R)))).
 { unfold V293_tcb_tick_spares,V293_tcb_init_record_remainder,V293_tcb_init_input_cells in *.
   cbn[firstn skipn tl app V293_rdy_raw_cells]in *;clear -Held;sep auto. }
 apply(V293_raw_record_ownership
 (((bc,0%Z),Tptr V293_tcb_type,Vptr(bt,Int.repr base))::
 ((bt,(base+44)%Z),Tint32,Vint32 Int.zero)::nil) _
 ltac:(repeat constructor;reflexivity))in Raw.
 cbn[V293_owned_record_cells]in Raw;unfold V293_tick_zero_node;clear -Raw;sep auto.
Qed.

(* Stable source-fragment seam. Neither successful reads, stores nor executions
   are premises. The initialized zero value is derived from actual stores. *)
Theorem V293_TCBInit_fields_then_zero_iteration : forall P ki kt ge le M ir enabled si ci O op R
 ptcb prio ptos pbos id stk_size pext opt rows group
 bc bp bs bb bi bz be bo bt base p top bottom identity size ext options old next,
 p<13 ->(0<=base)%Z ->(base+55<=Int.max_unsigned)%Z ->
 V293_tcb_init_env le ptcb prio ptos pbos id stk_size pext opt bc bp bs bb bi bz be bo ->
 V293_tcb_init_values_valid top bottom identity size ext options ->
 (ge,le,M,ir,(enabled,si,ci),O,op) |= V293_rdy_raw_cells
 (V293_tcb_init_old_fields bt base old++
  V293_tcb_init_input_cells bc bp bs bb bi bz be bo bt base p top bottom identity size ext options)
 (V293_owned_record_cell((bt,(base+20)%Z),Tcom_ptr 410%Z,Vptr next) **R) ->
 exists Mi Mf,
 cstepstar P(curs(V293_TCBInit_fields ptcb prio ptos pbos id stk_size pext opt),(kenil,ki))
 (ge,le,M)(curs(sskip None),(kenil,ki))(ge,le,Mi) /\
 load Tint32 Mi(bt,(base+44)%Z)=Some(Vint32 Int.zero) /\
 V293_local_steps P(curs(V293_tick_iteration ptcb rows group),(kenil,kt))
 ((ge,le,Mi),ir,(enabled,si,ci))
 (curs(sskip None),(kenil,kt))((ge,le,Mf),ir,(enabled,si,ci)) /\
 store(Tptr V293_tcb_type)Mi(bc,0%Z)(Vptr next)=Some Mf /\
 (ge,le,Mf,ir,(enabled,si,ci),O,op) |=
 V293_owned_record_cell((bc,0%Z),Tptr V293_tcb_type,Vptr next) **
 (V293_tick_zero_node bt base next **
 (V293_owned_task_record(bt,Int.repr base)(Int.repr(Z.of_nat p))rdy Vnull **
 V293_rdy_raw_cells(V293_tcb_tick_spares bt base top bottom identity size ext options)
 (V293_rdy_raw_cells
  (tl(V293_tcb_init_input_cells bc bp bs bb bi bz be bo bt base p top bottom identity size ext options)) R))) /\
 load(Tptr V293_tcb_type)Mf(bc,0%Z)=Some(Vptr next) /\
 (forall b i,b<>bc \/(i<0)%Z \/(4<=i)%Z ->get Mf(b,i)=get Mi(b,i)).
Proof.
 intros P ki kt ge le M ir enabled si ci O op R ptcb prio ptos pbos id stk_size pext opt rows group
 bc bp bs bb bi bz be bo bt base p top bottom identity size ext options old next
 Range Base Limit Env Valid Held.
 destruct(V293_OS_TCBInit_fields_execution P ki ge le M ir(enabled,si,ci)O op
 _ ptcb prio ptos pbos id stk_size pext opt bc bp bs bb bi bz be bo bt base p
 top bottom identity size ext options old Range Base Limit Env Valid Held)
 as(Mi&Init&Owned).
 assert(Zero:load Tint32 Mi(bt,(base+44)%Z)=Some(Vint32 Int.zero)).
 { change(load Tint32(getmem(ge,le,Mi,ir,(enabled,si,ci),O,op))(bt,(base+44)%Z)=Some(Vint32 Int.zero)).
   eapply V293_rdy_raw_load;[ |reflexivity|exact Owned].
   apply in_or_app;left;unfold V293_tcb_init_final_fields;cbn[In];tauto. }
 apply(V293_initialized_tick_resources bt base p top bottom identity size ext options
 bc bp bs bb bi bz be bo next R Range ltac:(lia)Valid)in Owned.
 destruct(V293_tick_zero_iteration_owned_execution P kt ge le Mi ir enabled si ci O op
 ptcb rows group bc bt base next _ (proj1 Env)Base ltac:(lia)Owned)
 as(Mf&Store&Tick&Read&Final&Outside).
 exists Mi;exists Mf;repeat split;assumption.
Qed.
