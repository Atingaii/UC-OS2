(* Original normalized tick prefix with full ready ownership. Scanner storage
   is explicit; execution stops before reading Next or claiming ISR entry. *)
Require Import CertiOS.certiucos.v293.proofs.V293SwitchedCountdownClosure.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickCountdown.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickTraversal.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickTaskBridge.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.code.V293OSTimeTick.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Local Open Scope nat_scope.

Lemma V293_ready_full_good : forall br bg bp current,
 GoodInvAsrt(V293_ready_full br bg bp current).
Proof.
 intros;change(forall tasks events now,GoodInvAsrt
 ((EX tp:type,GV OSTCBCur@(Tptr tp)|->Vptr current) **
 (V293_shared_fields current tasks events now **V293_ready_payload br bg bp tasks))).
 intros;split;[ | split;[ | apply V293_ready_payload_good]].
 - unfold Agvarmapsto,Aptrmapsto;cbn;intros;repeat split;exact I.
 - unfold V293_shared_fields;cbn;repeat split;exact I.
Qed.

Theorem V293_ready_countdown_delay_execution : forall br bg bp current tasks bt base priority d message
 R P ks ge le M ir aux O op sd ptcb rows group bc,
 get le ptcb=Some(bc,Tptr V293_tcb_type) ->
 (0<=base)%Z ->(base+44<=Int.max_unsigned)%Z ->(2<=d<=Int.max_unsigned)%Z ->
 get O abstcblsid=Some(abstcblist tasks) ->
 get tasks(bt,Int.repr base)=Some(priority,wait os_stat_time(Int.repr d),message) ->
 (ge,le,M,ir,aux,O,op)|=V293_ready_full br bg bp current **
 (V293_owned_record_cell((bc,0%Z),Tptr V293_tcb_type,Vptr(bt,Int.repr base)) **R) ->
 exists Mf,
 let tasks':=set tasks(bt,Int.repr base)(priority,wait os_stat_time(Int.repr(d-1)),message)in
 let O':=set O abstcblsid(abstcblist tasks')in
 store Tint32 M(bt,(base+44)%Z)(Vint32(Int.repr(d-1)))=Some Mf /\
 cstepstar P(curs(V293_tick_delay ptcb rows group),(kenil,ks))(ge,le,M)
 (curs(sskip None),(kenil,ks))(ge,le,Mf) /\
 spec_step sd(spec_prim nil(V293_tick_wait_step(bt,Int.repr base)))O(END None)O' /\
 (ge,le,Mf,ir,aux,O',op)|=V293_ready_full br bg bp current **
 (V293_owned_record_cell((bc,0%Z),Tptr V293_tcb_type,Vptr(bt,Int.repr base)) **R) /\
 load Tint32 Mf(bt,(base+44)%Z)=Some(Vint32(Int.repr(d-1))) /\
 (forall b i,b<>bt \/(i<base+44)%Z \/(base+48<=i)%Z ->get Mf(b,i)=get M(b,i)).
Proof.
 intros br bg bp current tasks bt base priority d message R P ks ge le M ir aux O op sd
 ptcb rows group bc Bind Base Limit Range Slot Task Held.
 assert(Records:V293_task_records M tasks).
 { eapply(V293_ready_full_records br bg bp current tasks _ ge le M ir aux O op Slot);exact Held. }
 destruct(Records _ _ _ _ Task)as(p&Prange&Priority&Fields&Status).
 destruct Status as(Stat&Delay&Message).
 cbn[fst snd]in Delay;rewrite Int.unsigned_repr in Delay by lia.
 assert(Pointer:load(Tptr V293_tcb_type)M(bc,0%Z)=Some(Vptr(bt,Int.repr base))).
 { assert(Cell:(ge,le,M,ir,aux,O,op)|=
   V293_owned_record_cell((bc,0%Z),Tptr V293_tcb_type,Vptr(bt,Int.repr base)) **Atrue)
   by(clear -Held;sep auto).
   exact(V293_record_star_load_l _ _ _ _ _ (V293_owned_record_cell_load _ _ _) _ Cell). }
 destruct(V293_ready_countdown_store br bg bp current tasks(bt,Int.repr base)priority d message
 _ ge le M ir aux O op sd Range Slot Task Held)as(Mf&Store&Abstract&After&Load&Outside).
 cbn[fst snd]in Store,Load,Outside;rewrite Int.unsigned_repr in Store,Load,Outside by lia.
 assert(Pointer':load(Tptr V293_tcb_type)Mf(bc,0%Z)=Some(Vptr(bt,Int.repr base))).
 { assert(Cell:(ge,le,Mf,ir,aux,set O abstcblsid(abstcblist
   (set tasks(bt,Int.repr base)(priority,wait os_stat_time(Int.repr(d-1)),message))),op)|=
   V293_owned_record_cell((bc,0%Z),Tptr V293_tcb_type,Vptr(bt,Int.repr base)) **Atrue)
   by(clear -After;sep auto).
   exact(V293_record_star_load_l _ _ _ _ _ (V293_owned_record_cell_load _ _ _) _ Cell). }
 destruct(V293_tick_countdown_arithmetic d Range)as(NE&Subtract&NE').
 destruct(V293_tick_field_eval ge le M ptcb bc bt base 13%Z 44%Z Tint32 _
 Bind Pointer eq_refl eq_refl Base ltac:(lia) Limit Delay)as(Ty&Value).
 destruct(V293_tick_field_eval ge le Mf ptcb bc bt base 13%Z 44%Z Tint32 _
 Bind Pointer' eq_refl eq_refl Base ltac:(lia) Limit Load)as(Ty'&Value').
 assert(Guard:evalval(V293_tick_ne(V293_tick_field ptcb 13%Z)0)(ge,le,M)=Some(Vint32 Int.one)).
 { unfold V293_tick_ne,V293_tick_eq;cbn[evalval evaltype];rewrite Ty,Value.
   change(match(if Int.eq(Int.repr d)Int.zero then Some(Vint32 Int.one)else Some(Vint32 Int.zero))
   with Some v=>notint v|None=>None end=Some(Vint32 Int.one));rewrite NE;reflexivity. }
 assert(Expiry:evalval(V293_tick_eq(V293_tick_field ptcb 13%Z)0)(ge,le,Mf)=Some(Vint32 Int.zero)).
 { unfold V293_tick_eq;cbn[evalval evaltype];rewrite Ty',Value'.
   change((if Int.eq(Int.repr(d-1))Int.zero then Some(Vint32 Int.one)else Some(Vint32 Int.zero))=
   Some(Vint32 Int.zero));rewrite NE';reflexivity. }
 assert(Dec:forall tail,cstepstar P
 (curs(sassign(V293_tick_field ptcb 13%Z)
 (ebinop ominus(V293_tick_field ptcb 13%Z)(econst32 Int.one))),(kenil,tail))(ge,le,M)
 (curs(sskip None),(kenil,tail))(ge,le,Mf)).
 { intro tail;eapply V293_tick_assign32_execution with(off:=(base+44)%Z);try eassumption.
   - cbn[evaltype];rewrite Ty;reflexivity.
   - eapply V293_tick_delay_address;eassumption.
   - cbn[evalval evaltype];rewrite Ty,Value;cbn[bop_eval sub];rewrite Subtract;reflexivity.
   - lia. }
 exists Mf;cbn zeta;split;[exact Store| ];split.
 - unfold V293_tick_delay;eapply V293_rekey_if_execution with(flag:=true);
   [exact Guard| |discriminate].
   intros _;eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply sseq_step]| ].
   eapply V293_cstepstar_trans;[apply Dec| ].
   eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply sskip_step]| ].
   eapply V293_rekey_if_execution with(flag:=false);[exact Expiry|discriminate|reflexivity].
 - split;[exact Abstract| ];split;[exact After| ];split;assumption.
Qed.

(* Stable source cutpoint: the same original iteration starts at encrit and
   stops immediately before the Next assignment, with the actual saved IE. *)
Theorem V293_ready_countdown_iteration_prefix : forall br bg bp current tasks bt base priority d message
 R P ks ge le M ir enabled si ci O op sd ptcb rows group bc,
 get le ptcb=Some(bc,Tptr V293_tcb_type) ->
 (0<=base)%Z ->(base+44<=Int.max_unsigned)%Z ->(2<=d<=Int.max_unsigned)%Z ->
 get O abstcblsid=Some(abstcblist tasks) ->
 get tasks(bt,Int.repr base)=Some(priority,wait os_stat_time(Int.repr d),message) ->
 GoodInvAsrt R ->
 (ge,le,M,ir,(enabled,si,ci),O,op)|=V293_ready_full br bg bp current **
 (V293_owned_record_cell((bc,0%Z),Tptr V293_tcb_type,Vptr(bt,Int.repr base)) **R) ->
 exists Mf,
 let tasks':=set tasks(bt,Int.repr base)(priority,wait os_stat_time(Int.repr(d-1)),message)in
 let O':=set O abstcblsid(abstcblist tasks')in
 store Tint32 M(bt,(base+44)%Z)(Vint32(Int.repr(d-1)))=Some Mf /\
 V293_local_steps P(curs(V293_tick_iteration ptcb rows group),(kenil,ks))
 ((ge,le,M),ir,(enabled,si,ci))
 (curs(V293_tick_advance ptcb),(kenil,kseq(sprim excrit)ks))
 ((ge,le,Mf),ir,(false,si,enabled::ci)) /\
 spec_step sd(spec_prim nil(V293_tick_wait_step(bt,Int.repr base)))O(END None)O' /\
 (ge,le,Mf,ir,(false,si,enabled::ci),O',op)|=V293_ready_full br bg bp current **
 (V293_owned_record_cell((bc,0%Z),Tptr V293_tcb_type,Vptr(bt,Int.repr base)) **R) /\
 load Tint32 Mf(bt,(base+44)%Z)=Some(Vint32(Int.repr(d-1))) /\
 (forall b i,b<>bt \/(i<base+44)%Z \/(base+48<=i)%Z ->get Mf(b,i)=get M(b,i)).
Proof.
 intros br bg bp current tasks bt base priority d message R P ks ge le M ir enabled si ci O op sd
 ptcb rows group bc Bind Base Limit Range Slot Task Good Held.
 assert(Disabled:(ge,le,M,ir,(false,si,enabled::ci),O,op)|=
 V293_ready_full br bg bp current **
 (V293_owned_record_cell((bc,0%Z),Tptr V293_tcb_type,Vptr(bt,Int.repr base)) **R)).
 { eapply good_inv_prop;[ | exact Held].
   split;[apply V293_ready_full_good|split;[unfold V293_owned_record_cell;cbn;split;exact I|exact Good]]. }
 destruct(V293_ready_countdown_delay_execution br bg bp current tasks bt base priority d message
 R P(kseq(sseq(V293_tick_advance ptcb)(sprim excrit))ks)ge le M ir(false,si,enabled::ci)O op sd
 ptcb rows group bc Bind Base Limit Range Slot Task Disabled)
 as(Mf&Store&Execute&Abstract&After&Load&Outside).
 exists Mf;cbn zeta;split;[exact Store| ];split.
 - unfold V293_tick_iteration.
   eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sseq_step]| ].
   eapply V293_local_cons;[apply encrit_step;reflexivity| ].
   eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sskip_step]| ].
   eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sseq_step]| ].
   eapply V293_local_trans;[apply V293_csteps_local;exact Execute| ].
   eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sskip_step]| ].
   eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sseq_step]| ].
   apply V293_local_refl.
 - split;[exact Abstract| ];split;[exact After| ];split;assumption.
Qed.
