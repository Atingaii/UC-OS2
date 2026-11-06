(* Continue the already executed first-y cut; no replay of entry or y store. *)
Require Import CertiOS.certiucos.v293.code.V293OSTimeDly.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickExpiry.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickCountdown.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickTaskBridge.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPublish.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrent.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Require Import CertiOS.certiucos.v293.proofs.V293TimeDlyCallEntry.
Require Import CertiOS.certiucos.v293.proofs.V293TimeDlyTaskBridge.
Require Import CertiOS.certiucos.v293.proofs.V293TimeDlyBlocking.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Import ListNotations.
Section DelayUpdates.
Variables current rows group y ticks : var.
Variables bc byloc bd bt br bg : block.
Variable base : Z.
Variable p : nat.
Variable duration : int32.
Local Ltac dly_read Owned n name :=
 lazymatch type of Owned with
 | (?ge,?le,?M,?ir,?au,?O,?op) |= V293_owned_record_cells ?cs ** ?R =>
 let cell:=eval cbn [V293_dly_cells nth] in (nth n cs ((1%positive,0%Z),Tint8,Vundef)) in
 lazymatch cell with (?a,?tp,?v) =>
 let name:=fresh name in
 assert(name:load tp M a=Some v) by
  (change(load tp (getmem(ge,le,M,ir,au,O,op))a=Some v);
   eapply (V293_record_star_load_l (V293_owned_record_cells cs) R);[apply (V293_owned_record_cells_load cs);cbn [V293_dly_cells In];tauto|exact Owned])
 end end.

Theorem V293_dly_after_y_execution : forall P ge le M ir au O op R delay lo hi,
 V293_dly_env current rows group y ticks bc byloc bd br bg ge le ->p<13 ->lo<256 ->hi<256 ->
 (0<=base)%Z ->(base+54<=Int.max_unsigned)%Z ->
 (ge,le,M,ir,au,O,op)|=V293_owned_record_cells
  (V293_dly_cells bc byloc bd bt br bg base p duration delay(V293_byteval(V293_prio_row p)) lo hi(V293_ready_group lo hi)) **R ->
 let cleared:=V293_ready_clear_rows lo hi p in
 exists Mf,
 (forall tail,cstepstar P(curs(V293_dly_after_y current rows group y),(kenil,tail))(ge,le,M)
  (SKIP,(kenil,tail))(ge,le,Mf)) /\
 (ge,le,Mf,ir,au,O,op)|=V293_owned_record_cells
  (V293_dly_cells bc byloc bd bt br bg base p duration delay(V293_byteval(V293_prio_row p))
   (fst cleared)(snd cleared)(V293_ready_group(fst cleared)(snd cleared))) **R /\
 load Tint32 Mf(bt,(base+44)%Z)=Some(Vint32 delay).
Proof.
 intros P ge le M ir au O op R delay lo hi Env Pbound Lo Hi Base Limit Owned cleared.
 pose proof Env as(Nc&Gc&Nr&Gr&Ng&Gg&By&Bd).
 destruct(V293_prio_coordinates p Pbound)as[Ybound Xbound].
 pose(r:=V293_ready_row lo hi(V293_prio_row p)).
 assert(Rbound:r<256)by(unfold r,V293_ready_row;destruct(V293_prio_row p=?0);assumption).
 pose(cv:=Nat.clearbit r(V293_prio_bit p)).
 destruct(V293_rekey_byte_arithmetic r(V293_prio_bit p)Rbound Xbound)as[Cbound _].
 change(cv<256)in Cbound.
 assert(CV:V293_ready_row(fst cleared)(snd cleared)(V293_prio_row p)=cv)by(apply V293_rekey_clear_row_value).
 assert(CL:fst cleared<256 /\snd cleared<256).
 { unfold cleared,V293_ready_clear_rows;destruct(p<?8)eqn:E;cbn;
   unfold cv,r,V293_ready_row,V293_prio_row,V293_prio_bit in Cbound;rewrite E in Cbound;cbn in Cbound;auto. }
 assert(Gbound:V293_ready_group lo hi<256)by(unfold V293_ready_group;destruct(lo=?0);destruct(hi=?0);lia).
 set(M1:=M).
 assert(H1:(ge,le,M1,ir,au,O,op)|=V293_owned_record_cells
  (V293_dly_cells bc byloc bd bt br bg base p duration delay(V293_byteval(V293_prio_row p))lo hi(V293_ready_group lo hi)) **R)by exact Owned.
 destruct(V293_dly_row_from_cells current rows group y ticks bc byloc bd bt br bg base p duration _ _ _ _ _ _ _ _ _ _ _ _ Env Pbound H1)as[Trow[Arow Vrow]].
 destruct(V293_dly_field_from_cells current rows group y ticks bc byloc bd bt br bg base p duration _ _ _ _ _ _ _ _ _ _ _ _ _ 19%Z 53%Z Tint8 _ Env Base Limit eq_refl eq_refl ltac:(lia)ltac:(cbn[V293_dly_cells In];tauto)H1)as[Tx[Ax Vx]].
 destruct(V293_task_prio_byte_expr_eval ge le M1(V293_dly_row rows y)(V293_dly_field current 19%Z)r(V293_prio_bit p)Rbound Xbound Trow Tx Vrow Vx)as[Tclear[_[Vclear _]]].
 (* Select exactly the physically addressed row; the other row is retained. *)
 assert(RowStore:exists M2,store Tint8 M1(br,Z.of_nat(V293_prio_row p))(V293_byteval cv)=Some M2 /\
  (ge,le,M2,ir,au,O,op)|=V293_owned_record_cells
   (V293_dly_cells bc byloc bd bt br bg base p duration delay(V293_byteval(V293_prio_row p))(fst cleared)(snd cleared)(V293_ready_group lo hi)) **R).
 { unfold cv,r,V293_ready_row,cleared,V293_ready_clear_rows,V293_prio_row,V293_prio_bit in Cbound |- *.
   destruct(p<?8)eqn:E;cbn [fst snd Nat.eqb] in Cbound |- *.
   - destruct(V293_tick_cells_store_at _ 7 _ _ _ (V293_byteval(Nat.clearbit lo p)) _ _ _ _ _ _ _ _ H1 eq_refl(V293_byte_type (Nat.clearbit lo p) Cbound))as(M2&S2&H2).
     exists M2;split;[exact S2| ].
     cbn [firstn skipn app V293_dly_cells] in H2 |- *.
     unfold V293_prio_row,V293_prio_bit in H2;rewrite E in H2;unfold V293_dly_cells,V293_prio_row,V293_prio_bit;rewrite E;exact H2.
   - destruct(V293_tick_cells_store_at _ 8 _ _ _ (V293_byteval(Nat.clearbit hi(p-8))) _ _ _ _ _ _ _ _ H1 eq_refl(V293_byte_type (Nat.clearbit hi(p-8)) Cbound))as(M2&S2&H2).
     exists M2;split;[exact S2| ].
     cbn [firstn skipn app V293_dly_cells] in H2 |- *.
     unfold V293_prio_row,V293_prio_bit in H2;rewrite E in H2;unfold V293_dly_cells,V293_prio_row,V293_prio_bit;rewrite E;exact H2. }
 destruct RowStore as(M2&S2&H2).
 assert(RowStep:forall tail,cstepstar P(curs(V293_dly_clear_row current rows y),(kenil,tail))(ge,le,M1)(SKIP,(kenil,tail))(ge,le,M2)).
 { intro tail;unfold V293_dly_clear_row;eapply V293_assign_byte_offset_execution;try eassumption;unfold Int.max_unsigned,Int.modulus,Int.wordsize;cbn;lia. }
 pose(gc:=V293_ready_clear_group lo hi p).
 assert(GC:gc=if cv=?0 then Nat.clearbit(V293_ready_group lo hi)(V293_prio_row p)else V293_ready_group lo hi).
 { unfold gc,V293_ready_clear_group,cv,r,V293_ready_row,V293_ready_clear_rows,V293_prio_row,V293_prio_bit;destruct(p<?8);reflexivity. }
 assert(GroupStore:exists M3,
  (forall tail,cstepstar P(curs(V293_dly_group_if current rows group y),(kenil,tail))(ge,le,M2)(SKIP,(kenil,tail))(ge,le,M3)) /\
  (ge,le,M3,ir,au,O,op)|=V293_owned_record_cells
   (V293_dly_cells bc byloc bd bt br bg base p duration delay(V293_byteval(V293_prio_row p))(fst cleared)(snd cleared)gc) **R).
 { destruct(V293_dly_row_from_cells current rows group y ticks bc byloc bd bt br bg base p duration _ _ _ _ _ _ _ _ _ _ _ _ Env Pbound H2)as[Tr[Ar Vr]].
   rewrite CV in Vr.
   assert(Test:evalval(ebinop oeq(ecast(V293_dly_row rows y)Tint32)(econst32 Int.zero))(ge,le,M2)=Some(Vint32(if cv=?0 then Int.one else Int.zero))).
   { eapply V293_rekey_byte_zero_eval;eassumption. }
   destruct(cv=?0)eqn:Zero.
   - destruct(V293_rekey_byte_arithmetic(V293_ready_group lo hi)(V293_prio_row p)Gbound ltac:(lia))as[GB _].
     destruct(V293_tick_cells_store_at _ 9 _ _ _ (V293_byteval(Nat.clearbit(V293_ready_group lo hi)(V293_prio_row p))) _ _ _ _ _ _ _ _ H2 eq_refl(V293_byte_type (Nat.clearbit(V293_ready_group lo hi)(V293_prio_row p)) GB))as(M3&S3&H3).
     exists M3;split.
     + intro tail;unfold V293_dly_group_if;apply V293_rekey_if_execution with(flag:=true);[exact Test| |intro;discriminate].
       intro Yes;dly_read H2 9 GroupLoad.
       destruct(V293_dly_field_from_cells current rows group y ticks bc byloc bd bt br bg base p duration _ _ _ _ _ _ _ _ _ _ _ _ _ 20%Z 54%Z Tint8 _ Env Base Limit eq_refl eq_refl ltac:(lia)ltac:(cbn[V293_dly_cells In];tauto)H2)as[Tb[Ab Vb]].
       assert(Tg:evaltype(evar group)(ge,le,M2)=Some Tint8)by(cbn[evaltype get_lenv get_genv];rewrite Ng,Gg;reflexivity).
       assert(Ag:evaladdr(evar group)(ge,le,M2)=Some(Vptr(bg,Int.repr 0)))by(cbn[evaladdr get_lenv get_genv];rewrite Ng,Gg;reflexivity).
       assert(Vg:evalval(evar group)(ge,le,M2)=Some(V293_byteval(V293_ready_group lo hi)))by(cbn[evalval evaltype evaladdr get_lenv get_genv get_mem];rewrite Ng,Gg;cbn;exact GroupLoad).
       destruct(V293_task_prio_byte_expr_eval ge le M2(evar group)(V293_dly_field current 20%Z)(V293_ready_group lo hi)(V293_prio_row p)Gbound ltac:(lia)Tg Tb Vg Vb)as[Tc[_[Vc _]]].
       unfold V293_dly_clear_group;eapply V293_assign_byte_offset_execution with(off:=0%Z);eauto;lia.
     + rewrite GC;exact H3.
   - exists M2;split.
     + intro tail;unfold V293_dly_group_if;apply V293_rekey_if_execution with(flag:=false);[exact Test|intro;discriminate|reflexivity].
     + rewrite GC;exact H2. }
 destruct GroupStore as(M3&GroupStep&H3).
 exists M3;split.
 - intro tail;unfold V293_dly_after_y.
   eapply V293_rekey_sequence_execution;[exact RowStep| ].
   eapply V293_rekey_sequence_execution;[intro;constructor|apply GroupStep].
 - split.
   + unfold gc in H3;rewrite V293_ready_clear_group_correct in H3 by assumption;exact H3.
   + dly_read H3 6 Delay;exact Delay.
Qed.

Theorem V293_dly_after_y_updates : forall P ks ge le M ir au O op R delay lo hi,
 V293_dly_env current rows group y ticks bc byloc bd br bg ge le ->p<13 ->lo<256 ->hi<256 ->
 (0<=base)%Z ->(base+54<=Int.max_unsigned)%Z ->
 (ge,le,M,ir,au,O,op)|=V293_owned_record_cells
  (V293_dly_cells bc byloc bd bt br bg base p duration delay(V293_byteval(V293_prio_row p)) lo hi(V293_ready_group lo hi)) **R ->
 let cleared:=V293_ready_clear_rows lo hi p in
 exists Mf,
 cstepstar P(curs(V293_dly_after_y current rows group y),(kenil,kseq(sseq(sassign(V293_dly_field current 13%Z)(evar ticks))(sskip None))ks))(ge,le,M)
  (SKIP,(kenil,ks))(ge,le,Mf) /\
 (ge,le,Mf,ir,au,O,op)|=V293_owned_record_cells
  (V293_dly_cells bc byloc bd bt br bg base p duration duration(V293_byteval(V293_prio_row p))
   (fst cleared)(snd cleared)(V293_ready_group(fst cleared)(snd cleared))) **R /\
 load Tint32 Mf(bt,(base+44)%Z)=Some(Vint32 duration).
Proof.
 intros P ks ge le M ir au O op R delay lo hi Env Pbound Lo Hi Base Limit Owned cleared.
 pose proof Env as(Nc&Gc&Nr&Gr&Ng&Gg&By&Bd).
 destruct(V293_dly_after_y_execution P ge le M ir au O op R delay lo hi
   Env Pbound Lo Hi Base Limit Owned)as(M3&Prefix&H3&OldDelay).
 pose(gc:=V293_ready_group(fst cleared)(snd cleared)).
 destruct(V293_tick_cells_store_at _ 6 _ _ _ (Vint32 duration) _ _ _ _ _ _ _ _ H3 eq_refl eq_refl)as(M4&S4&H4).
 change((ge,le,M4,ir,au,O,op)|=V293_owned_record_cells
  (V293_dly_cells bc byloc bd bt br bg base p duration duration(V293_byteval(V293_prio_row p))(fst cleared)(snd cleared)gc) **R)in H4.
 assert(DelayStep:forall tail,cstepstar P(curs(sassign(V293_dly_field current 13%Z)(evar ticks)),(kenil,tail))(ge,le,M3)(SKIP,(kenil,tail))(ge,le,M4)).
 { intro tail;destruct(V293_dly_field_from_cells current rows group y ticks bc byloc bd bt br bg base p duration _ _ _ _ _ _ _ _ _ _ _ _ _ 13%Z 44%Z Tint32 _ Env Base Limit eq_refl eq_refl ltac:(lia)ltac:(cbn[V293_dly_cells In];tauto)H3)as[Td[Ad Vd]].
   dly_read H3 2 Ticks.
   eapply V293_tick_assign32_execution with(off:=(base+44)%Z);try eassumption;try lia;
   cbn[evaltype evalval evaladdr get_lenv get_genv get_mem];rewrite Bd;cbn;first[reflexivity|exact Ticks]. }
 exists M4;split.
 - eapply V293_cstepstar_trans;[apply Prefix| ].
   eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply sskip_step]| ].
   eapply V293_rekey_sequence_execution;[exact DelayStep|constructor].
 - split;[exact H4|dly_read H4 6 Delay;exact Delay].
Qed.
End DelayUpdates.

(* Same-heap refinement at the first-y cut, not replay of whole updates. *)
Theorem V293_dly_after_y_refines : forall current rows group y ticks
 bc byloc bd bt br bg base p duration P ks ge le M ir au O op sd R delay lo hi entries tasks message events now,
 V293_dly_env current rows group y ticks bc byloc bd br bg ge le ->
 p<13 ->lo<256 ->hi<256 ->(0<=base)%Z ->(base+54<=Int.max_unsigned)%Z ->
 duration<>Int.zero ->V293_priority_table entries tasks ->V293_bitmap_tasks lo hi tasks ->
 get tasks(bt,Int.repr base)=Some(Int.repr(Z.of_nat p),rdy,message) ->
 (ge,le,M,ir,au,O,op)|=V293_owned_record_cells
  (V293_dly_cells bc byloc bd bt br bg base p duration delay(V293_byteval(V293_prio_row p)) lo hi(V293_ready_group lo hi)) **
  (V293_owned_record_cells(V293_dly_record_extra bt base p message) **
  (V293_owned_task_records(del tasks(bt,Int.repr base)) **
  (V293_shared_fields(bt,Int.repr base)tasks events now **R))) ->
 let blocked:=set tasks(bt,Int.repr base)(Int.repr(Z.of_nat p),wait os_stat_time duration,message) in
 let O':=set O abstcblsid(abstcblist blocked) in
 let cleared:=V293_ready_clear_rows lo hi p in
 exists Mf,
 cstepstar P(curs(V293_dly_after_y current rows group y),(kenil,kseq(sseq(sassign(V293_dly_field current 13%Z)(evar ticks))(sskip None))ks))(ge,le,M)
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
 intros current rows group y ticks bc byloc bd bt br bg base p duration P ks ge le M ir au O op sd R delay lo hi entries tasks message events now
 Env Pb Lo Hi Base Limit Positive Table Bitmap Task Owned blocked O' cleared.
 destruct(V293_dly_after_y_updates current rows group y ticks bc byloc bd bt br bg base p duration
 P ks ge le M ir au O op _ delay lo hi Env Pb Lo Hi Base Limit Owned)
 as(Mf&Exec&Returned&DelayRead).
 pose proof(V293_dly_bitmap_tasks entries tasks(bt,Int.repr base)p message duration lo hi Pb Table Bitmap Task)as Bits.
 pose proof(V293_tick_priority_table entries tasks(bt,Int.repr base)(Int.repr(Z.of_nat p))rdy
 (wait os_stat_time duration)message Table Task)as Prio.
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


(* Stable suffix interface: actual critical aux at input, restored aux at output.
   Generic ownership retains entry aux; no transport of aux-sensitive R. *)
Theorem V293_dly_after_y_to_sched_refines : forall current rows group y ticks sched
 bc byloc bd bt br bg base p duration P ks ge le M ir enabled si ci O op sd R
 delay lo hi entries tasks message events now,
 V293_dly_env current rows group y ticks bc byloc bd br bg ge le ->
 p<13 ->lo<256 ->hi<256 ->(0<=base)%Z ->(base+54<=Int.max_unsigned)%Z ->
 duration<>Int.zero ->V293_priority_table entries tasks ->V293_bitmap_tasks lo hi tasks ->
 get tasks(bt,Int.repr base)=Some(Int.repr(Z.of_nat p),rdy,message) ->
 (ge,le,M,ir,(enabled,si,ci),O,op)|=V293_owned_record_cells
  (V293_dly_cells bc byloc bd bt br bg base p duration delay(V293_byteval(V293_prio_row p)) lo hi(V293_ready_group lo hi)) **
  (V293_owned_record_cells(V293_dly_record_extra bt base p message) **
  (V293_owned_task_records(del tasks(bt,Int.repr base)) **
  (V293_shared_fields(bt,Int.repr base)tasks events now **R))) ->
 let blocked:=set tasks(bt,Int.repr base)(Int.repr(Z.of_nat p),wait os_stat_time duration,message) in
 let O':=set O abstcblsid(abstcblist blocked) in
 let cleared:=V293_ready_clear_rows lo hi p in
 exists Mf,
 V293_local_steps P(curs(V293_dly_after_y current rows group y),(kenil,V293_dly_after_y_cont current ticks sched ks))
 ((ge,le,M),ir,(false,si,cons enabled ci))
 (curs(scall sched nil),(kenil,kseq sret ks))((ge,le,Mf),ir,(enabled,si,ci)) /\
 spec_step sd(spec_prim(cons(Vint32 duration)nil)V293_dly_block_step)O(END None)O' /\
 V293_task_records Mf blocked /\V293_priority_table entries blocked /\
 V293_bitmap_tasks(fst cleared)(snd cleared)blocked /\
 (ge,le,Mf,ir,(enabled,si,ci),O',op)|=V293_owned_record_cells
  (V293_dly_cells bc byloc bd bt br bg base p duration duration(V293_byteval(V293_prio_row p))
   (fst cleared)(snd cleared)(V293_ready_group(fst cleared)(snd cleared))) **
  (V293_owned_record_cells(V293_dly_record_extra bt base p message) **
  (V293_owned_task_records(del tasks(bt,Int.repr base)) **
  (V293_shared_fields(bt,Int.repr base)blocked events now **R))).
Proof.
 intros current rows group y ticks sched bc byloc bd bt br bg base p duration P ks
 ge le M ir enabled si ci O op sd R delay lo hi entries tasks message events now
 Env Pb Lo Hi Base Limit Positive Table Bitmap Task Owned blocked O' cleared.
 set(tail:=kseq sret ks).
 destruct(V293_dly_after_y_refines current rows group y ticks bc byloc bd bt br bg base p duration
 P(kseq(sseq(sprim excrit)(scall sched nil))tail)ge le M ir(enabled,si,ci)O op sd R
 delay lo hi entries tasks message events now Env Pb Lo Hi Base Limit Positive Table Bitmap Task Owned)
 as(Mf&Updates&Step&Records&Prio&Bits&Returned).
 exists Mf;split;[ |split;[exact Step|split;[exact Records|split;[exact Prio|split;[exact Bits|exact Returned]]]]].
 unfold V293_dly_after_y_cont;fold tail.
 eapply V293_local_trans;[apply V293_csteps_local;exact Updates| ].
 eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sskip_step]| ].
 eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sseq_step]| ].
 eapply V293_local_cons;[apply excrit_step;reflexivity| ].
 eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sskip_step]| ].
 apply V293_local_refl.
Qed.

