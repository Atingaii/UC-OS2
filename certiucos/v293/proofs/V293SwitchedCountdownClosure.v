(* Delay-store closure of the existing full ready resources. This file does
   not construct an ISR entry, a scanner context, or a source tick execution. *)
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickRecordReassembly.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickTaskBridge.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLoop.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Local Open Scope nat_scope.

Lemma V293_time_wait_record_store : forall t priority message old new R ge le M ir aux O op,
 (ge,le,M,ir,aux,O,op)|=
 V293_owned_task_record t priority(wait os_stat_time old)message **R ->
 exists Mf,
 store Tint32 M(fst t,(Int.unsigned(snd t)+44)%Z)(Vint32 new)=Some Mf /\
 (ge,le,Mf,ir,aux,O,op)|=
 V293_owned_task_record t priority(wait os_stat_time new)message **R /\
 load Tint32 Mf(fst t,(Int.unsigned(snd t)+44)%Z)=Some(Vint32 new).
Proof.
 intros t priority message old new R ge le M ir aux O op Held.
 unfold V293_owned_task_record in Held;sep normal in Held;sep destruct Held;sep split in Held.
 set(prefix:=firstn 7(V293_record_layout t x(wait os_stat_time old)message x0)).
 assert(Opened:(ge,le,M,ir,aux,O,op)|=
 V293_owned_record_cell((fst t,(Int.unsigned(snd t)+44)%Z),Tint32,Vint32 old) **
 (V293_owned_record_cells prefix **R)).
 { unfold prefix,V293_record_layout in *;cbn[V293_owned_record_cells app firstn]in *.
   clear -Held;sep auto. }
 destruct(V293_owned_record_cell_update _ Tint32 _ (Vint32 new)
 _ ge le M ir aux O op eq_refl Opened)as(Mf&Store&After).
 exists Mf;split;[exact Store| ];split.
 - assert(Cells:(ge,le,Mf,ir,aux,O,op)|=
   V293_owned_record_cells(V293_record_layout t x(wait os_stat_time new)message x0) **R).
   { unfold prefix,V293_record_layout in After|-*;cbn[V293_owned_record_cells app firstn]in *.
     clear -After;sep auto. }
   unfold V293_owned_task_record;sep normal;exists x;exists x0;apply astar_l_apure_intro;[exact Cells|exact H].
 - exact(V293_record_star_load_l _ _ _ _ _ (V293_owned_record_cell_load _ _ _) _ After).
Qed.

Lemma V293_ready_countdown_rel : forall lo hi entries tasks t priority d message,
 (2<=d<=Int.max_unsigned)%Z ->
 get tasks t=Some(priority,wait os_stat_time(Int.repr d),message) ->
 V293_ready_rel lo hi entries tasks ->
 V293_ready_rel lo hi entries
 (set tasks t(priority,wait os_stat_time(Int.repr(d-1)),message)).
Proof.
 intros lo hi entries tasks t priority d message Range Task Rel.
 destruct Rel as(Lo&Hi&Nonempty&Bitmap&Table).
 destruct(proj2 Table _ _ _ _ Task)as(p&P&Prio&Slot);subst priority.
 split;[exact Lo| ];split;[exact Hi| ];split;[exact Nonempty| ];split.
 - pose proof(V293_tick_wait_bitmap_tasks lo hi tasks t p os_stat_time d message P Bitmap Task)as B.
   unfold V293_tick_wait_rows,V293_tick_wait_status,V293_tick_after_delay in B.
   assert(E:Z.eqb d 1=false)by(apply Z.eqb_neq;lia).
   assert(Z:Z.eqb d 0=false)by(apply Z.eqb_neq;lia).
   rewrite E,Z in B. exact B.
 - eapply V293_tick_priority_table;[exact Table|exact Task].
Qed.

(* The input is precisely the existing full invariant plus lookup facts.
   The physical store and abstract transition are conclusions, not oracles. *)
Theorem V293_ready_countdown_store : forall br bg bp current tasks t priority d message
 R ge le M ir aux O op sd,
 (2<=d<=Int.max_unsigned)%Z ->
 get O abstcblsid=Some(abstcblist tasks) ->
 get tasks t=Some(priority,wait os_stat_time(Int.repr d),message) ->
 (ge,le,M,ir,aux,O,op)|=V293_ready_full br bg bp current **R ->
 exists Mf,
 let tasks':=set tasks t(priority,wait os_stat_time(Int.repr(d-1)),message)in
 let O':=set O abstcblsid(abstcblist tasks')in
 store Tint32 M(fst t,(Int.unsigned(snd t)+44)%Z)(Vint32(Int.repr(d-1)))=Some Mf /\
 spec_step sd(spec_prim nil(V293_tick_wait_step t))O(END None)O' /\
 (ge,le,Mf,ir,aux,O',op)|=V293_ready_full br bg bp current **R /\
 load Tint32 Mf(fst t,(Int.unsigned(snd t)+44)%Z)=Some(Vint32(Int.repr(d-1))) /\
 (forall b i,b<>fst t \/(i<Int.unsigned(snd t)+44)%Z \/
 (Int.unsigned(snd t)+48<=i)%Z ->get Mf(b,i)=get M(b,i)).
Proof.
 intros br bg bp current tasks t priority d message R ge le M ir aux O op sd
 Range Slot Task Held.
 unfold V293_ready_full in Held;sep normal in Held;sep destruct Held.
 assert(Actual:get O abstcblsid=Some(abstcblist x)).
 { change(get(getabst(ge,le,M,ir,aux,O,op))abstcblsid=Some(abstcblist x)).
   eapply V293_star_abst_get_l with(p:=V293_shared_fields current x x0 x1)(q:=Atrue).
   - intros st H;exact(proj1(proj2(V293_shared_fields_get _ _ _ _ st H))).
   - clear -Held;sep auto. }
 rewrite Slot in Actual;inversion Actual;subst x.
 set(Tail:=(EX tp:type,GV OSTCBCur@(Tptr tp)|->Vptr current) **
 (V293_shared_fields current tasks x0 x1 **
 (V293_ready_owned br bg bp tasks **R))).
 assert(Records:(ge,le,M,ir,aux,O,op)|=V293_owned_task_records tasks **Tail).
 { unfold Tail,V293_ready_payload in *;clear -Held;sep auto. }
 pose proof(V293_owned_task_records_focus tasks t priority _ message Tail _ Task Records)as Focused.
 destruct(V293_time_wait_record_store t priority message(Int.repr d)(Int.repr(d-1))
 _ ge le M ir aux O op Focused)as(Mf&Store&Changed&Load).
 pose proof(V293_owned_task_records_reassemble tasks t priority _ message Tail _ Changed)as Closed.
 set(updated:=set tasks t(priority,wait os_stat_time(Int.repr(d-1)),message)).
 assert(Ready:(ge,le,Mf,ir,aux,O,op)|=V293_owned_task_records updated **
 ((EX tp:type,GV OSTCBCur@(Tptr tp)|->Vptr current) **
 (V293_shared_fields current tasks x0 x1 **(V293_ready_owned br bg bp updated **R)))).
 { unfold Tail in Closed.
   assert(RelChange:V293_ready_owned br bg bp tasks ==> V293_ready_owned br bg bp updated).
   { intros st(lo&hi&entries&H);apply astar_l_apure_elim in H;destruct H as[Rel Cells].
     exists lo;exists hi;exists entries;apply astar_l_apure_intro;[exact Cells| ].
     unfold updated;eapply V293_ready_countdown_rel;eassumption. }
   eapply astar_mono;[intros st H;exact H| |exact Closed].
   apply astar_mono;[intros st H;exact H| ].
   apply astar_mono;[intros st H;exact H| ].
   apply astar_mono;[exact RelChange|intros st H;exact H]. }
 assert(Final:(ge,le,Mf,ir,aux,O,op)|=Aabsdata abstcblsid(abstcblist tasks) **
 ((EX tp:type,GV OSTCBCur@(Tptr tp)|->Vptr current) **
 ((Aabsdata curtid(oscurt current) **
 (Aabsdata absecblsid(absecblist x0) **Aabsdata ostmid(ostm x1))) **
 (V293_ready_payload br bg bp updated **R)))).
 { unfold V293_shared_fields,V293_ready_payload in *;clear -Ready;sep auto. }
 apply V293_shared_replace_slot with(new:=abstcblist updated)in Final.
 exists Mf;cbn zeta;split;[exact Store| ];split.
 - assert(E:V293_tick_wait_status os_stat_time d=wait os_stat_time(Int.repr(d-1))).
   { unfold V293_tick_wait_status,V293_tick_after_delay.
     assert(N:Z.eqb d 1=false)by(apply Z.eqb_neq;lia);assert(Z:Z.eqb d 0=false)by(apply Z.eqb_neq;lia);rewrite N,Z;reflexivity. }
   unfold updated;rewrite <-E;apply V293_tick_wait_transition;try assumption;lia.
 - split.
   + unfold V293_ready_full;sep normal;exists updated;exists x0;exists x1.
     unfold V293_shared_fields;clear -Final;sep auto.
   + split;[exact Load| ];intros b i Outside;eapply V293_storebytes_outside;[exact Store| ].
     rewrite encode_val_length;cbn[typelen];intuition lia.
Qed.

Lemma V293_ready_full_records : forall br bg bp current tasks R ge le M ir aux O op,
 get O abstcblsid=Some(abstcblist tasks) ->
 (ge,le,M,ir,aux,O,op)|=V293_ready_full br bg bp current **R ->
 V293_task_records M tasks.
Proof.
 intros br bg bp current tasks R ge le M ir aux O op Slot Held.
 unfold V293_ready_full in Held;sep normal in Held;sep destruct Held.
 assert(Actual:get O abstcblsid=Some(abstcblist x)).
 { change(get(getabst(ge,le,M,ir,aux,O,op))abstcblsid=Some(abstcblist x)).
   eapply V293_star_abst_get_l with(p:=V293_shared_fields current x x0 x1)(q:=Atrue).
   - intros st H;exact(proj1(proj2(V293_shared_fields_get _ _ _ _ st H))).
   - clear -Held;sep auto. }
 rewrite Slot in Actual;inversion Actual;subst x.
 assert(Owned:(ge,le,M,ir,aux,O,op)|=V293_owned_task_records tasks **Atrue)
 by(unfold V293_ready_payload in Held;clear -Held;sep auto).
 apply sat_split in Owned;destruct Owned as(m1&m2&o1&o2&JM&JO&Records&Rest).
 intros u p status msg Lookup;eapply V293_task_record_sub;[exists m2;exact JM| ].
 apply(V293_owned_task_records_sound _ _ Records);exact Lookup.
Qed.
