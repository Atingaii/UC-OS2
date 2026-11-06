(* Source pointer assignments and a complete non-expiring iteration. Head and
   Next are explicit resources, not consequences of selected record ownership. *)
Require Import CertiOS.certiucos.v293.proofs.V293SwitchedTickPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyOwnedSchedCall.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickTraversal.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickCountdown.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickTaskBridge.
Require Import CertiOS.certiucos.v293.proofs.V293SwitchedCountdownClosure.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.code.V293OSTimeTick.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Local Open Scope nat_scope.

(* Construct the source assignment from raw scanner storage. The source head
   is read from its named global, never substituted by an expected pointer. *)
Theorem V293_ready_tick_head_execution : forall P ks ge le M ir aux O op
 ptcb head bc bh scan first R,
 get le ptcb=Some(bc,Tptr V293_tcb_type) ->
 get le head=None ->get ge head=Some(bh,Tptr V293_tcb_type) ->
 (ge,le,M,ir,aux,O,op)|=Amapsto(bc,0%Z)(Tptr V293_tcb_type)true scan **
 (V293_owned_record_cell((bh,0%Z),Tptr V293_tcb_type,Vptr first) **R) ->
 exists Mh,
 store(Tptr V293_tcb_type)M(bc,0%Z)(Vptr first)=Some Mh /\
 cstepstar P(curs(sassign(evar ptcb)(evar head)),(kenil,ks))(ge,le,M)
 (curs(sskip None),(kenil,ks))(ge,le,Mh) /\
 (ge,le,Mh,ir,aux,O,op)|=
 V293_owned_record_cell((bc,0%Z),Tptr V293_tcb_type,Vptr first) **
 (V293_owned_record_cell((bh,0%Z),Tptr V293_tcb_type,Vptr first) **R) /\
 load(Tptr V293_tcb_type)Mh(bc,0%Z)=Some(Vptr first) /\
 (forall b i,b<>bc \/(i<0)%Z \/(4<=i)%Z ->get Mh(b,i)=get M(b,i)).
Proof.
 intros P ks ge le M ir aux O op ptcb head bc bh scan first R Bc Nh Gh Held.
 assert(Read:load(Tptr V293_tcb_type)M(bh,0%Z)=Some(Vptr first)).
 { change(load(Tptr V293_tcb_type)(getmem(ge,le,M,ir,aux,O,op))(bh,0%Z)=Some(Vptr first)).
   eapply V293_record_star_load_r;[ |exact Held].
   eapply V293_record_star_load_l;apply V293_owned_record_cell_load. }
 destruct(V293_tick_raw_slot_update(bc,0%Z)(Tptr V293_tcb_type)scan(Vptr first)
 _ ge le M ir aux O op eq_refl Held)as(Mh&Store&After).
 exists Mh;split;[exact Store| ];split.
 - eapply V293_assign_pointer_execution with(tp:=V293_tcb_type)(tr:=Tptr V293_tcb_type)
   (b:=bc)(off:=0%Z);try exact Store.
   + cbn[evaltype get_lenv];rewrite Bc;reflexivity.
   + cbn[evaltype get_lenv get_genv];rewrite Nh,Gh;reflexivity.
   + apply eq_vptr;eauto.
   + cbn[evaladdr get_lenv];rewrite Bc;reflexivity.
   + cbn[evalval evaltype get_lenv get_genv get_mem];rewrite Nh,Gh;exact Read.
   + change(0<=0<=4294967295)%Z;lia.
 - split;[exact After| ];split.
   + eapply V293_store_readback;[reflexivity|exact Store].
   + intros b i Outside;eapply V293_storebytes_outside;[exact Store| ].
     rewrite encode_val_length;exact Outside.
Qed.

(* Shared pointer-assignment seam. Reading the owned Next and writing the
   scanner preserves every byte of R, including the full ready invariant. *)
Theorem V293_ready_tick_advance_execution : forall P ks ge le M ir aux O op
 ptcb bc bt base next R,
 get le ptcb=Some(bc,Tptr V293_tcb_type) ->
 (0<=base)%Z ->(base+20<=Int.max_unsigned)%Z ->
 (ge,le,M,ir,aux,O,op)|=
 V293_owned_record_cell((bc,0%Z),Tptr V293_tcb_type,Vptr(bt,Int.repr base)) **
 (V293_owned_record_cell((bt,(base+20)%Z),Tcom_ptr 410%Z,Vptr next) **R) ->
 exists Mf,
 store(Tptr V293_tcb_type)M(bc,0%Z)(Vptr next)=Some Mf /\
 cstepstar P(curs(V293_tick_advance ptcb),(kenil,ks))(ge,le,M)
 (curs(sskip None),(kenil,ks))(ge,le,Mf) /\
 (ge,le,Mf,ir,aux,O,op)|=
 V293_owned_record_cell((bc,0%Z),Tptr V293_tcb_type,Vptr next) **
 (V293_owned_record_cell((bt,(base+20)%Z),Tcom_ptr 410%Z,Vptr next) **R) /\
 load(Tptr V293_tcb_type)Mf(bc,0%Z)=Some(Vptr next) /\
 (forall b i,b<>bc \/(i<0)%Z \/(4<=i)%Z ->get Mf(b,i)=get M(b,i)).
Proof.
 intros P ks ge le M ir aux O op ptcb bc bt base next R Bind Base Limit Held.
 assert(Pointer:load(Tptr V293_tcb_type)M(bc,0%Z)=Some(Vptr(bt,Int.repr base))).
 { change(load(Tptr V293_tcb_type)(getmem(ge,le,M,ir,aux,O,op))(bc,0%Z)=Some(Vptr(bt,Int.repr base))).
   eapply V293_record_star_load_l;[apply V293_owned_record_cell_load|exact Held]. }
 assert(Next:load(Tcom_ptr 410%Z)M(bt,(base+20)%Z)=Some(Vptr next)).
 { change(load(Tcom_ptr 410%Z)(getmem(ge,le,M,ir,aux,O,op))(bt,(base+20)%Z)=Some(Vptr next)).
   eapply V293_record_star_load_r;[ |exact Held].
   eapply V293_record_star_load_l;apply V293_owned_record_cell_load. }
 destruct(V293_tick_field_eval ge le M ptcb bc bt base 7%Z 20%Z(Tcom_ptr 410%Z)_
 Bind Pointer eq_refl eq_refl Base ltac:(lia)Limit Next)as[Ty Value].
 destruct(V293_owned_record_cell_update(bc,0%Z)(Tptr V293_tcb_type)
 (Vptr(bt,Int.repr base))(Vptr next)_ _ _ _ _ _ _ _ eq_refl Held)as(Mf&Store&After).
 exists Mf;split;[exact Store| ];split.
 - unfold V293_tick_advance.
   eapply V293_assign_pointer_execution with(tp:=V293_tcb_type)(tr:=Tcom_ptr 410%Z)
   (b:=bc)(off:=0%Z);try eassumption.
   + cbn[evaltype];rewrite Bind;reflexivity.
   + apply eq_vcomptr;split;left;eauto.
   + cbn[evaladdr get_lenv];rewrite Bind;reflexivity.
   + change(0<=0<=4294967295)%Z;lia.
 - split;[exact After| ];split.
   + eapply V293_store_readback;[reflexivity|exact Store].
   + intros b i Outside;eapply V293_storebytes_outside;[exact Store| ].
     rewrite encode_val_length;exact Outside.
Qed.

(* Stable endpoint: original iteration, including Next and excrit, closes
   the same full ready invariant. Neither execution nor store is an input. *)
Theorem V293_ready_countdown_linked_iteration : forall br bg bp current tasks bt base priority d message
 R P ks ge le M ir enabled si ci O op sd ptcb rows group bc next,
 get le ptcb=Some(bc,Tptr V293_tcb_type) ->
 (0<=base)%Z ->(base+44<=Int.max_unsigned)%Z ->(2<=d<=Int.max_unsigned)%Z ->
 get O abstcblsid=Some(abstcblist tasks) ->
 get tasks(bt,Int.repr base)=Some(priority,wait os_stat_time(Int.repr d),message) ->
 GoodInvAsrt R ->
 (ge,le,M,ir,(enabled,si,ci),O,op)|=V293_ready_full br bg bp current **
 (V293_owned_record_cell((bc,0%Z),Tptr V293_tcb_type,Vptr(bt,Int.repr base)) **
 (V293_owned_record_cell((bt,(base+20)%Z),Tcom_ptr 410%Z,Vptr next) **R)) ->
 exists Md Mf,
 let tasks':=set tasks(bt,Int.repr base)(priority,wait os_stat_time(Int.repr(d-1)),message)in
 let O':=set O abstcblsid(abstcblist tasks')in
 store Tint32 M(bt,(base+44)%Z)(Vint32(Int.repr(d-1)))=Some Md /\
 store(Tptr V293_tcb_type)Md(bc,0%Z)(Vptr next)=Some Mf /\
 V293_local_steps P(curs(V293_tick_iteration ptcb rows group),(kenil,ks))
 ((ge,le,M),ir,(enabled,si,ci))
 (curs(sskip None),(kenil,ks))((ge,le,Mf),ir,(enabled,si,ci)) /\
 spec_step sd(spec_prim nil(V293_tick_wait_step(bt,Int.repr base)))O(END None)O' /\
 (ge,le,Mf,ir,(enabled,si,ci),O',op)|=V293_ready_full br bg bp current **
 (V293_owned_record_cell((bc,0%Z),Tptr V293_tcb_type,Vptr next) **
 (V293_owned_record_cell((bt,(base+20)%Z),Tcom_ptr 410%Z,Vptr next) **R)) /\
 load Tint32 Mf(bt,(base+44)%Z)=Some(Vint32(Int.repr(d-1))) /\
 load(Tptr V293_tcb_type)Mf(bc,0%Z)=Some(Vptr next) /\
 (forall b i,(b<>bt \/(i<base+44)%Z \/(base+48<=i)%Z) ->
 (b<>bc \/(i<0)%Z \/(4<=i)%Z) ->get Mf(b,i)=get M(b,i)).
Proof.
 intros br bg bp current tasks bt base priority d message R P ks ge le M ir enabled si ci O op sd
 ptcb rows group bc next Bind Base Limit Range Slot Task Good Held.
 set(Rnext:=V293_owned_record_cell((bt,(base+20)%Z),Tcom_ptr 410%Z,Vptr next) **R).
 assert(GoodNext:GoodInvAsrt Rnext)by(split;[split;exact I|exact Good]).
 destruct(V293_ready_countdown_iteration_prefix br bg bp current tasks bt base priority d message
 Rnext P ks ge le M ir enabled si ci O op sd ptcb rows group bc
 Bind Base Limit Range Slot Task GoodNext Held)
 as(Md&Dec&Prefix&Abstract&After&Delay&OutsideD).
 set(O':=set O abstcblsid(abstcblist(set tasks(bt,Int.repr base)
 (priority,wait os_stat_time(Int.repr(d-1)),message)))).
 assert(ToAdvance:(ge,le,Md,ir,(false,si,enabled::ci),O',op)|=
 V293_owned_record_cell((bc,0%Z),Tptr V293_tcb_type,Vptr(bt,Int.repr base)) **
 (V293_owned_record_cell((bt,(base+20)%Z),Tcom_ptr 410%Z,Vptr next) **
 (V293_ready_full br bg bp current **R)))by(unfold Rnext in After;clear -After;sep auto).
 destruct(V293_ready_tick_advance_execution P(kseq(sprim excrit)ks)ge le Md ir
 (false,si,enabled::ci)O' op ptcb bc bt base next _ Bind Base ltac:(lia)ToAdvance)
 as(Mf&AdvanceStore&Advance&Returned&Read&OutsideA).
 assert(Enabled:(ge,le,Mf,ir,(enabled,si,ci),O',op)|=V293_ready_full br bg bp current **
 (V293_owned_record_cell((bc,0%Z),Tptr V293_tcb_type,Vptr next) **
 (V293_owned_record_cell((bt,(base+20)%Z),Tcom_ptr 410%Z,Vptr next) **R))).
 { assert(Reordered:(ge,le,Mf,ir,(false,si,enabled::ci),O',op)|=V293_ready_full br bg bp current **
   (V293_owned_record_cell((bc,0%Z),Tptr V293_tcb_type,Vptr next) **Rnext))
   by(unfold Rnext;clear -Returned;sep auto).
   eapply good_inv_prop;[split;[apply V293_owned_ready_good|split;[split;exact I|exact GoodNext]]|exact Reordered]. }
 assert(Records:V293_task_records Mf(set tasks(bt,Int.repr base)
 (priority,wait os_stat_time(Int.repr(d-1)),message))).
 { eapply V293_ready_full_records;[unfold O';apply map_get_set|exact Enabled]. }
 destruct(Records(bt,Int.repr base)priority(wait os_stat_time(Int.repr(d-1)))message
 (map_get_set _ _ _))as(p&Prange&Priority&Fields&Status).
 destruct Status as(Stat&DelayFinal&MessageFinal).
 cbn[fst snd]in DelayFinal;rewrite Int.unsigned_repr in DelayFinal by lia.
 exists Md;exists Mf;cbn zeta;split;[exact Dec| ];split;[exact AdvanceStore| ];split.
 - eapply V293_local_trans;[exact Prefix| ].
   eapply V293_local_trans;[apply V293_csteps_local;exact Advance| ].
   eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sskip_step]| ].
   eapply V293_local_cons;[apply excrit_step;reflexivity|apply V293_local_refl].
 - split;[exact Abstract| ];split;[exact Enabled| ];split;[exact DelayFinal| ];split;[exact Read| ].
   intros b i OD OA;rewrite OutsideA by exact OA;apply OutsideD;exact OD.
Qed.
