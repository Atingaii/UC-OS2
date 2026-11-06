(* The source blocking fragment, one original abstract primitive step, and
   shared/all-task record consistency at ONE terminal memory. This does not
   register a whole API spec or assume that a physical switch has occurred. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeDlyBlocking.
Require Import CertiOS.certiucos.v293.code.V293OSTimeDly.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickTaskBridge.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
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

(* A critical-update contract, NOT the complete OSTimeDly API contract.
   Its current task is read from the abstract state, not selected separately. *)
Definition V293_dly_block_step : osabstep := fun vl O result =>
 exists duration tasks t priority message,
 vl=[Vint32 duration] /\ duration<>Int.zero /\
 get O curtid=Some(oscurt t) /\get O abstcblsid=Some(abstcblist tasks) /\
 get tasks t=Some(priority,rdy,message) /\
 result=(None,set O abstcblsid(abstcblist
   (set tasks t(priority,wait os_stat_time duration,message)))).

Theorem V293_dly_block_transition : forall sd O tasks t priority duration message,
 get O curtid=Some(oscurt t) ->get O abstcblsid=Some(abstcblist tasks) ->
 get tasks t=Some(priority,rdy,message) ->duration<>Int.zero ->
 spec_step sd(spec_prim (cons (Vint32 duration) nil) V293_dly_block_step) O(END None)
  (set O abstcblsid(abstcblist(set tasks t(priority,wait os_stat_time duration,message)))).
Proof.
 intros sd O tasks t priority duration message Current Slot Task Positive.
 eapply spec_prim_step with(O:=O)(Of:=emp).
 - exists duration;exists tasks;exists t;exists priority;exists message.
   repeat split;assumption || reflexivity.
 - split.
   + intro id;unfold indom;destruct(OSAbstMod.eq_dec id abstcblsid)as[Same|Apart].
     * subst id;rewrite map_get_set;split;intros;eauto.
     * split;intros[v Lookup];exists v;
       [rewrite map_get_set' by congruence|rewrite map_get_set' in Lookup by congruence];exact Lookup.
   + intros ts Lookup;rewrite Slot in Lookup;inversion Lookup;subst ts.
     exists(set tasks t(priority,wait os_stat_time duration,message)).
     split;[apply map_get_set| ]. unfold eqdomtls;intro u;unfold indom.
     change((exists v,get tasks u=Some v)<->
       (exists v,get(set tasks t(priority,wait os_stat_time duration,message))u=Some v)).
     destruct(TcbMod.eq_dec u t)as[Same|Apart].
     * subst u;split;intros;[eexists;apply map_get_set|eexists;exact Task].
     * split;intros[v Lookup'];exists v;
       [rewrite map_get_set' by congruence|rewrite map_get_set' in Lookup' by congruence];exact Lookup'.
 - unfold tidsame;rewrite map_get_set';[reflexivity|discriminate].
 - apply map_join_emp.
 - apply map_join_emp.
Qed.

Lemma V293_dly_owned_blocked_record : forall bc byloc bd bt br bg base p duration delay yv lo hi g message R ge le M ir au O op,
 p<13 ->(0<=base<=Int.max_unsigned)%Z ->
 (ge,le,M,ir,au,O,op)|=V293_owned_record_cells
  (V293_dly_cells bc byloc bd bt br bg base p duration delay yv lo hi g) **
  (V293_owned_record_cells(V293_dly_record_extra bt base p message) **R) ->
 (ge,le,M,ir,au,O,op)|=V293_owned_task_record(bt,Int.repr base)
  (Int.repr(Z.of_nat p))(wait os_stat_time delay)message **Atrue.
Proof.
 intros bc byloc bd bt br bg base p duration delay yv lo hi g message R ge le M ir au O op P Base Owned.
 assert(U:Int.unsigned(Int.repr base)=base)by(apply Int.unsigned_repr;exact Base).
 destruct(V293_prio_coordinates p P)as[Y X].
 destruct(V293_mask_byte_value(V293_prio_row p)ltac:(lia))as[_ MaskY].
 destruct(V293_mask_byte_value(V293_prio_bit p)X)as[_ MaskX].
 assert(Cells:(ge,le,M,ir,au,O,op)|=V293_owned_record_cells
   (V293_record_layout(bt,Int.repr base)p(wait os_stat_time delay)message 0) **Atrue).
 { unfold V293_record_layout;cbn[fst snd];rewrite U.
   unfold V293_dly_cells,V293_dly_record_extra in Owned.
   rewrite MaskY,MaskX.
   cbn[app V293_owned_record_cells]in Owned|-*.
   clear -Owned;sep auto. }
 eapply astar_mono;[ |intros;exact I|exact Cells].
 intros s H;exists p;exists 0;apply astar_l_apure_intro;
 [exact H|repeat split;try reflexivity;lia].
Qed.

(* Stable interface for the SAME source execution, shared abstract state,
   all canonical task records and ready-table relation. current is unchanged
   and now blocked: the later scheduler/context-switch obligation stays open. *)
Theorem V293_OSTimeDly_updates_refines : forall current rows group y ticks
 bc byloc bd bt br bg base p duration P ks ge le M ir au O op sd R delay yv lo hi entries tasks message events now,
 V293_dly_env current rows group y ticks bc byloc bd br bg ge le ->
 p<13 ->lo<256 ->hi<256 ->(0<=base)%Z ->(base+54<=Int.max_unsigned)%Z ->
 duration<>Int.zero ->V293_priority_table entries tasks ->V293_bitmap_tasks lo hi tasks ->
 get tasks(bt,Int.repr base)=Some(Int.repr(Z.of_nat p),rdy,message) ->
 (ge,le,M,ir,au,O,op)|=V293_owned_record_cells
  (V293_dly_cells bc byloc bd bt br bg base p duration delay yv lo hi(V293_ready_group lo hi)) **
  (V293_owned_record_cells(V293_dly_record_extra bt base p message) **
  (V293_owned_task_records(del tasks(bt,Int.repr base)) **
  (V293_shared_fields(bt,Int.repr base)tasks events now **R))) ->
 let blocked:=set tasks(bt,Int.repr base)(Int.repr(Z.of_nat p),wait os_stat_time duration,message) in
 let O':=set O abstcblsid(abstcblist blocked) in
 let cleared:=V293_ready_clear_rows lo hi p in
 exists Mf,
 cstepstar P(curs(V293_dly_updates current rows group y ticks),(kenil,ks))(ge,le,M)
  (SKIP,(kenil,ks))(ge,le,Mf) /\
 spec_step sd(spec_prim (cons (Vint32 duration) nil) V293_dly_block_step) O(END None)O' /\
 V293_task_records Mf blocked /\V293_priority_table entries blocked /\
 V293_bitmap_tasks(fst cleared)(snd cleared)blocked /\
 (ge,le,Mf,ir,au,O',op)|=V293_owned_record_cells
  (V293_dly_cells bc byloc bd bt br bg base p duration duration(V293_byteval(V293_prio_row p))
   (fst cleared)(snd cleared)(V293_ready_group(fst cleared)(snd cleared))) **
  (V293_owned_record_cells(V293_dly_record_extra bt base p message) **
  (V293_owned_task_records(del tasks(bt,Int.repr base)) **
  (V293_shared_fields(bt,Int.repr base)blocked events now **R))).
Proof.
 intros current rows group y ticks bc byloc bd bt br bg base p duration P ks ge le M ir au O op sd R delay yv lo hi entries tasks message events now
 Env Pb Lo Hi Base Limit Positive Table Bitmap Task Owned blocked O' cleared.
 destruct(V293_OSTimeDly_blocking_bridge current rows group y ticks bc byloc bd bt br bg base p duration
 P ks ge le M ir au O op _ delay yv lo hi entries tasks message Env Pb Lo Hi Base Limit Positive Table Bitmap Task Owned)
 as(Mf&Exec&Returned&Record&Bits&Prio&NotReady&NotHighest).
 assert(Selected:(ge,le,Mf,ir,au,O,op)|=V293_owned_task_record(bt,Int.repr base)
   (Int.repr(Z.of_nat p))(wait os_stat_time duration)message **Atrue).
 { eapply V293_dly_owned_blocked_record;[exact Pb|lia|exact Returned]. }
 assert(Others:(ge,le,Mf,ir,au,O,op)|=V293_owned_task_records(del tasks(bt,Int.repr base)) **Atrue)
 by(clear -Returned;sep auto).
 pose proof(V293_tick_records_replace tasks _ _ _ _ _ _ _ _ _ _ _ Selected Others)as Records.
 assert(Fields:(ge,le,Mf,ir,au,O,op)|=V293_shared_fields(bt,Int.repr base)tasks events now **Atrue)
 by(clear -Returned;sep auto).
 assert(Slots:get O curtid=Some(oscurt(bt,Int.repr base)) /\get O abstcblsid=Some(abstcblist tasks)).
 { split.
   - change(get(getabst(ge,le,Mf,ir,au,O,op))curtid=Some(oscurt(bt,Int.repr base))).
     eapply V293_star_abst_get_l with(p:=V293_shared_fields(bt,Int.repr base)tasks events now)(q:=Atrue);
     [intros s H;exact(proj1(V293_shared_fields_get _ _ _ _ s H))|exact Fields].
   - change(get(getabst(ge,le,Mf,ir,au,O,op))abstcblsid=Some(abstcblist tasks)).
     eapply V293_star_abst_get_l with(p:=V293_shared_fields(bt,Int.repr base)tasks events now)(q:=Atrue);
     [intros s H;exact(proj1(proj2(V293_shared_fields_get _ _ _ _ s H)))|exact Fields]. }
 assert(Final:(ge,le,Mf,ir,au,O,op)|=Aabsdata abstcblsid(abstcblist tasks) **
  (V293_owned_record_cells
   (V293_dly_cells bc byloc bd bt br bg base p duration duration(V293_byteval(V293_prio_row p))
    (fst cleared)(snd cleared)(V293_ready_group(fst cleared)(snd cleared))) **
   (V293_owned_record_cells(V293_dly_record_extra bt base p message) **
   (V293_owned_task_records(del tasks(bt,Int.repr base)) **
   ((Aabsdata curtid(oscurt(bt,Int.repr base)) **
     (Aabsdata absecblsid(absecblist events) **Aabsdata ostmid(ostm now))) **R))))).
 { unfold V293_shared_fields in Returned;clear -Returned;sep auto. }
 apply V293_shared_replace_slot with(new:=abstcblist blocked)in Final.
 exists Mf;split;[exact Exec| ]. split.
 - apply V293_dly_block_transition;try assumption;tauto.
 - split;[exact Records| ]. split;[exact Prio| ]. split;[exact Bits| ].
   unfold V293_shared_fields;clear -Final;sep auto.
Qed.

Lemma V293_dly_other_abstract_slots : forall O tasks t priority duration message id,
 id<>abstcblsid ->get(set O abstcblsid(abstcblist
 (set tasks t(priority,wait os_stat_time duration,message))))id=get O id.
Proof. intros;apply map_get_set';congruence. Qed.
