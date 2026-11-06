(* Actual OSTimeDly critical updates, not a caller-supplied execution oracle.
   Original cstepstar, exact owned output, unchanged arbitrary spatial frame. *)
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

Section DelayUpdates.
Variables current rows group y ticks : var.
Variables bc byloc bd bt br bg : block.
Variable base : Z.
Variable p : nat.
Variable duration : int32.
Definition V293_dly_cells (delay:int32) yv lo hi g : list V293_record_cell :=
 [((byloc,0%Z),Tint8,yv);
  ((bc,0%Z),Tptr V293_tcb_type,Vptr(bt,Int.repr base));
  ((bd,0%Z),Tint32,Vint32 duration);
  ((bt,(base+52)%Z),Tint8,V293_byteval(V293_prio_row p));
  ((bt,(base+53)%Z),Tint8,V293_mask_value(V293_prio_bit p));
  ((bt,(base+54)%Z),Tint8,V293_mask_value(V293_prio_row p));
  ((bt,(base+44)%Z),Tint32,Vint32 delay);
  ((br,0%Z),Tint8,V293_byteval lo);
  ((br,1%Z),Tint8,V293_byteval hi);
  ((bg,0%Z),Tint8,V293_byteval g)].
Definition V293_dly_env (ge le:env) :=
 get le current=None /\get ge current=Some(bc,Tptr V293_tcb_type) /\
 get le rows=None /\get ge rows=Some(br,Tarray Tint8 2) /\
 get le group=None /\get ge group=Some(bg,Tint8) /\
 get le y=Some(byloc,Tint8) /\get le ticks=Some(bd,Tint32).

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

Lemma V293_dly_field_from_cells : forall delay yv lo hi g R ge le M ir au O op tag off tp value,
 V293_dly_env ge le ->(0<=base)%Z ->(base+54<=Int.max_unsigned)%Z ->
 ftype tag V293_tcb_fields=Some tp ->field_offset tag V293_tcb_fields=Some(Int.repr off) ->
 (0<=off<=54)%Z ->
 In ((bt,(base+off)%Z),tp,value) (V293_dly_cells delay yv lo hi g) ->
 (ge,le,M,ir,au,O,op)|=V293_owned_record_cells(V293_dly_cells delay yv lo hi g) **R ->
 evaltype(V293_dly_field current tag)(ge,le,M)=Some tp /\
 evaladdr(V293_dly_field current tag)(ge,le,M)=Some(Vptr(bt,Int.repr(base+off))) /\
 evalval(V293_dly_field current tag)(ge,le,M)=Some value.
Proof.
 intros delay yv lo hi g R ge le M ir au O op tag off tp value
 (Nc&Gc&Nr&Gr&Ng&Gg&By&Bd) Base Limit Ft Fo Off Member Owned.
 dly_read Owned 1 PtrRead.
 assert(T:evaltype(evar current)(ge,le,M)=Some(Tptr V293_tcb_type)).
 { cbn [evaltype get_lenv get_genv];rewrite Nc,Gc;reflexivity. }
 assert(V:evalval(evar current)(ge,le,M)=Some(Vptr(bt,Int.repr base))).
 { cbn [evalval evaltype evaladdr get_lenv get_genv get_mem];rewrite Nc,Gc;cbn;exact PtrRead. }
 assert(Read:load tp M(bt,(base+off)%Z)=Some value).
 { change(load tp(getmem(ge,le,M,ir,au,O,op))(bt,(base+off)%Z)=Some value).
   eapply (V293_record_star_load_l (V293_owned_record_cells (V293_dly_cells delay yv lo hi g)) R);[apply V293_owned_record_cells_load;exact Member|exact Owned]. }
 destruct(V293_pub_field_address _ _ _ _ _ _ _ _ _ T V Ft Fo Base ltac:(lia)ltac:(lia))as[Ty Addr].
 destruct(V293_pub_field_value _ _ _ _ _ _ _ _ _ _ T V Ft Fo Base ltac:(lia)ltac:(lia)Read)as[_ Val].
 split;[exact Ty|split;assumption].
Qed.

Lemma V293_dly_row_from_cells : forall delay lo hi g R ge le M ir au O op,
 V293_dly_env ge le ->p<13 ->
 (ge,le,M,ir,au,O,op)|=V293_owned_record_cells
  (V293_dly_cells delay (V293_byteval(V293_prio_row p)) lo hi g) **R ->
 evaltype(V293_dly_row rows y)(ge,le,M)=Some Tint8 /\
 evaladdr(V293_dly_row rows y)(ge,le,M)=Some(Vptr(br,Int.repr(Z.of_nat(V293_prio_row p)))) /\
 evalval(V293_dly_row rows y)(ge,le,M)=Some(V293_byteval(V293_ready_row lo hi(V293_prio_row p))).
Proof.
 intros delay lo hi g R ge le M ir au O op (Nc&Gc&Nr&Gr&Ng&Gg&By&Bd) P Owned.
 dly_read Owned 0 Y;dly_read Owned 7 Low;dly_read Owned 8 High;dly_read Owned 9 Group.
 assert(Ty:evaltype(evar y)(ge,le,M)=Some Tint8)by(cbn[evaltype get_lenv get_genv];rewrite By;reflexivity).
 assert(Vy:evalval(evar y)(ge,le,M)=Some(V293_byteval(V293_prio_row p)))by(cbn[evalval evaltype evaladdr get_lenv get_genv get_mem];rewrite By;cbn;exact Y).
 apply(V293_rekey_row_eval ge le M rows(evar y)br lo hi g bg(V293_prio_row p)Nr Gr Ty Vy ltac:(destruct(V293_prio_coordinates p P);lia)).
 repeat split;assumption.
Qed.

Theorem V293_OSTimeDly_before_delay_execution : forall P ge le M ir au O op R delay yv lo hi,
 V293_dly_env ge le ->p<13 ->lo<256 ->hi<256 ->
 (0<=base)%Z ->(base+54<=Int.max_unsigned)%Z ->
 (ge,le,M,ir,au,O,op)|=V293_owned_record_cells
  (V293_dly_cells delay yv lo hi(V293_ready_group lo hi)) **R ->
 let cleared:=V293_ready_clear_rows lo hi p in
 exists Mf,
 (forall tail,cstepstar P(curs(V293_dly_before_delay current rows group y),(kenil,tail))(ge,le,M)
  (SKIP,(kenil,tail))(ge,le,Mf)) /\
 (ge,le,Mf,ir,au,O,op)|=V293_owned_record_cells
  (V293_dly_cells delay(V293_byteval(V293_prio_row p))
   (fst cleared)(snd cleared)(V293_ready_group(fst cleared)(snd cleared))) **R /\
 load Tint32 Mf(bt,(base+44)%Z)=Some(Vint32 delay).
Proof.
 intros P ge le M ir au O op R delay yv lo hi Env Pbound Lo Hi Base Limit Owned cleared.
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
 destruct(V293_tick_cells_store_at _ 0 _ _ _ (V293_byteval(V293_prio_row p)) _ _ _ _ _ _ _ _ Owned eq_refl(V293_byte_type (V293_prio_row p) ltac:(lia)))as(M1&S1&H1).
 change((ge,le,M1,ir,au,O,op)|=V293_owned_record_cells
  (V293_dly_cells delay(V293_byteval(V293_prio_row p))lo hi(V293_ready_group lo hi)) **R)in H1.
 assert(Ystep:forall tail,cstepstar P(curs(sassign(evar y)(V293_dly_field current 18%Z)),(kenil,tail))(ge,le,M)(SKIP,(kenil,tail))(ge,le,M1)).
 { intro tail;destruct(V293_dly_field_from_cells _ _ _ _ _ _ _ _ _ _ _ _ _ 18%Z 52%Z Tint8 _ Env Base Limit eq_refl eq_refl ltac:(lia)ltac:(cbn[V293_dly_cells In];tauto)Owned)as[Ty[Addr Val]].
   eapply V293_assign_byte_offset_execution with(off:=0%Z);try eassumption;try lia;
   cbn[evaltype evaladdr get_lenv get_genv];rewrite By;reflexivity. }
 destruct(V293_dly_row_from_cells _ _ _ _ _ _ _ _ _ _ _ _ Env Pbound H1)as[Trow[Arow Vrow]].
 destruct(V293_dly_field_from_cells _ _ _ _ _ _ _ _ _ _ _ _ _ 19%Z 53%Z Tint8 _ Env Base Limit eq_refl eq_refl ltac:(lia)ltac:(cbn[V293_dly_cells In];tauto)H1)as[Tx[Ax Vx]].
 destruct(V293_task_prio_byte_expr_eval ge le M1(V293_dly_row rows y)(V293_dly_field current 19%Z)r(V293_prio_bit p)Rbound Xbound Trow Tx Vrow Vx)as[Tclear[_[Vclear _]]].
 (* Select exactly the physically addressed row; the other row is retained. *)
 assert(RowStore:exists M2,store Tint8 M1(br,Z.of_nat(V293_prio_row p))(V293_byteval cv)=Some M2 /\
  (ge,le,M2,ir,au,O,op)|=V293_owned_record_cells
   (V293_dly_cells delay(V293_byteval(V293_prio_row p))(fst cleared)(snd cleared)(V293_ready_group lo hi)) **R).
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
   (V293_dly_cells delay(V293_byteval(V293_prio_row p))(fst cleared)(snd cleared)gc) **R).
 { destruct(V293_dly_row_from_cells _ _ _ _ _ _ _ _ _ _ _ _ Env Pbound H2)as[Tr[Ar Vr]].
   rewrite CV in Vr.
   assert(Test:evalval(ebinop oeq(ecast(V293_dly_row rows y)Tint32)(econst32 Int.zero))(ge,le,M2)=Some(Vint32(if cv=?0 then Int.one else Int.zero))).
   { eapply V293_rekey_byte_zero_eval;eassumption. }
   destruct(cv=?0)eqn:Zero.
   - destruct(V293_rekey_byte_arithmetic(V293_ready_group lo hi)(V293_prio_row p)Gbound ltac:(lia))as[GB _].
     destruct(V293_tick_cells_store_at _ 9 _ _ _ (V293_byteval(Nat.clearbit(V293_ready_group lo hi)(V293_prio_row p))) _ _ _ _ _ _ _ _ H2 eq_refl(V293_byte_type (Nat.clearbit(V293_ready_group lo hi)(V293_prio_row p)) GB))as(M3&S3&H3).
     exists M3;split.
     + intro tail;unfold V293_dly_group_if;apply V293_rekey_if_execution with(flag:=true);[exact Test| |intro;discriminate].
       intro Yes;dly_read H2 9 GroupLoad.
       destruct(V293_dly_field_from_cells _ _ _ _ _ _ _ _ _ _ _ _ _ 20%Z 54%Z Tint8 _ Env Base Limit eq_refl eq_refl ltac:(lia)ltac:(cbn[V293_dly_cells In];tauto)H2)as[Tb[Ab Vb]].
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
 - intro tail;unfold V293_dly_before_delay.
   eapply V293_rekey_sequence_execution;[exact Ystep| ].
   eapply V293_rekey_sequence_execution;[exact RowStep| ].
   eapply V293_rekey_sequence_execution;[intro;constructor|apply GroupStep].
 - split.
   + unfold gc in H3;rewrite V293_ready_clear_group_correct in H3 by assumption;exact H3.
   + dly_read H3 6 Delay;exact Delay.
Qed.

Theorem V293_OSTimeDly_updates_execution : forall P ks ge le M ir au O op R delay yv lo hi,
 V293_dly_env ge le ->p<13 ->lo<256 ->hi<256 ->
 (0<=base)%Z ->(base+54<=Int.max_unsigned)%Z ->
 (ge,le,M,ir,au,O,op)|=V293_owned_record_cells
  (V293_dly_cells delay yv lo hi(V293_ready_group lo hi)) **R ->
 let cleared:=V293_ready_clear_rows lo hi p in
 exists Mf,
 cstepstar P(curs(V293_dly_updates current rows group y ticks),(kenil,ks))(ge,le,M)
  (SKIP,(kenil,ks))(ge,le,Mf) /\
 (ge,le,Mf,ir,au,O,op)|=V293_owned_record_cells
  (V293_dly_cells duration(V293_byteval(V293_prio_row p))
   (fst cleared)(snd cleared)(V293_ready_group(fst cleared)(snd cleared))) **R /\
 load Tint32 Mf(bt,(base+44)%Z)=Some(Vint32 duration).
Proof.
 intros P ks ge le M ir au O op R delay yv lo hi Env Pbound Lo Hi Base Limit Owned cleared.
 pose proof Env as(Nc&Gc&Nr&Gr&Ng&Gg&By&Bd).
 destruct(V293_OSTimeDly_before_delay_execution P ge le M ir au O op R delay yv lo hi
   Env Pbound Lo Hi Base Limit Owned)as(M3&Prefix&H3&OldDelay).
 pose(gc:=V293_ready_group(fst cleared)(snd cleared)).
 destruct(V293_tick_cells_store_at _ 6 _ _ _ (Vint32 duration) _ _ _ _ _ _ _ _ H3 eq_refl eq_refl)as(M4&S4&H4).
 change((ge,le,M4,ir,au,O,op)|=V293_owned_record_cells
  (V293_dly_cells duration(V293_byteval(V293_prio_row p))(fst cleared)(snd cleared)gc) **R)in H4.
 assert(DelayStep:forall tail,cstepstar P(curs(sassign(V293_dly_field current 13%Z)(evar ticks)),(kenil,tail))(ge,le,M3)(SKIP,(kenil,tail))(ge,le,M4)).
 { intro tail;destruct(V293_dly_field_from_cells _ _ _ _ _ _ _ _ _ _ _ _ _ 13%Z 44%Z Tint32 _ Env Base Limit eq_refl eq_refl ltac:(lia)ltac:(cbn[V293_dly_cells In];tauto)H3)as[Td[Ad Vd]].
   dly_read H3 2 Ticks.
   eapply V293_tick_assign32_execution with(off:=(base+44)%Z);try eassumption;try lia;
   cbn[evaltype evalval evaladdr get_lenv get_genv get_mem];rewrite Bd;cbn;first[reflexivity|exact Ticks]. }
 exists M4;split.
 - unfold V293_dly_updates.
   eapply V293_rekey_sequence_execution.
   + exact Prefix.
   + eapply V293_rekey_sequence_execution;[exact DelayStep|constructor].
 - split;[exact H4|dly_read H4 6 Delay;exact Delay].
Qed.
End DelayUpdates.

(* A status update is justified by the represented priority table, not by
   an assumed scheduler choice. No other task can share the removed priority. *)
Lemma V293_dly_bitmap_tasks : forall entries tasks t p message duration lo hi,
 p<13 -> V293_priority_table entries tasks -> V293_bitmap_tasks lo hi tasks ->
 get tasks t=Some(Int.repr(Z.of_nat p),rdy,message) ->
 V293_bitmap_tasks (fst(V293_ready_clear_rows lo hi p))
  (snd(V293_ready_clear_rows lo hi p))
  (set tasks t (Int.repr(Z.of_nat p),wait os_stat_time duration,message)).
Proof.
 intros entries tasks t p message duration lo hi P Table Bitmap Task q Q.
 rewrite V293_ready_clear_membership by assumption;split.
 - intros[Ready Different]. destruct(proj1(Bitmap q Q)Ready)as(u&msg&Lookup).
   assert(Apart:u<>t).
   { intro Same;subst u;rewrite Task in Lookup;inversion Lookup.
     apply Different;apply(V293_priority_repr_injective q p Q P);congruence. }
   exists u;exists msg;rewrite map_get_set' by congruence;exact Lookup.
 - intros(u&msg&Lookup). destruct(TcbMod.eq_dec u t)as[Same|Apart].
   + subst u;rewrite map_get_set in Lookup;discriminate.
   + rewrite map_get_set' in Lookup by congruence;split.
     * apply(proj2(Bitmap q Q));exists u;exists msg;exact Lookup.
     * intro Same;subst q;apply Apart;symmetry.
       eapply V293_rekey_priority_unique;eauto.
Qed.

Lemma V293_dly_higher_ready_prevents_selection : forall tasks high low p q mh ml,
 p<q ->q<13 ->
 get tasks high=Some(Int.repr(Z.of_nat p),rdy,mh) ->
 get tasks low=Some(Int.repr(Z.of_nat q),rdy,ml) ->
 ~V293_highest_ready tasks low.
Proof.
 intros tasks high low p q mh ml Less Q High Low(pr&msg&Ready&Min).
 rewrite Low in Ready;inversion Ready;subst pr msg.
 specialize(Min _ _ _ High).
 rewrite !V293_priority_repr_unsigned in Min by lia;lia.
Qed.

Definition V293_dly_record_extra bt base p message : list V293_record_cell :=
 [((bt,(base+50)%Z),Tint8,V293_byteval p);
  ((bt,(base+51)%Z),Tint8,V293_byteval(V293_prio_bit p));
  ((bt,(base+48)%Z),Tint8,V293_byteval 0);
  ((bt,(base+32)%Z),Tptr Tvoid,message)].

Lemma V293_dly_blocked_record : forall bc byloc bd bt br bg base p duration delay yv lo hi g message R ge le M ir au O op,
 p<13 ->(0<=base<=Int.max_unsigned)%Z ->
 (ge,le,M,ir,au,O,op)|=V293_owned_record_cells
  (V293_dly_cells bc byloc bd bt br bg base p duration delay yv lo hi g) **
  (V293_owned_record_cells(V293_dly_record_extra bt base p message) **R) ->
 V293_task_record M(bt,Int.repr base)(Int.repr(Z.of_nat p))
   (wait os_stat_time delay)message.
Proof.
 intros bc byloc bd bt br bg base p duration delay yv lo hi g message R ge le M ir au O op P Base Owned.
 assert(Loads:forall a tp v,In(a,tp,v)
  (V293_dly_cells bc byloc bd bt br bg base p duration delay yv lo hi g ++
   V293_dly_record_extra bt base p message) -> load tp M a=Some v).
 { intros a tp v Member;apply in_app_or in Member;destruct Member as[Member|Member];
   change(load tp(getmem(ge,le,M,ir,au,O,op))a=Some v).
   - eapply V293_record_star_load_l;[apply V293_owned_record_cells_load;exact Member|exact Owned].
   - eapply V293_record_star_load_r;[ |exact Owned].
     eapply V293_record_star_load_l;apply V293_owned_record_cells_load;exact Member. }
 eapply V293_record_layout_sound with(p:=p)(pend:=0);[exact P|reflexivity|lia| ].
 intros a tp v Member;apply Loads.
 unfold V293_record_layout in Member;cbn [fst snd app] in Member.
 rewrite Int.unsigned_repr in Member by exact Base.
 destruct(V293_prio_coordinates p P)as[Y X].
 destruct(V293_mask_byte_value(V293_prio_row p)ltac:(lia))as[_ MaskY].
 destruct(V293_mask_byte_value(V293_prio_bit p)X)as[_ MaskX].
 unfold V293_dly_cells,V293_dly_record_extra;rewrite <-MaskY,<-MaskX.
 cbn [In app] in Member |- *;tauto.
Qed.

(* Stable source-to-model boundary: same Mf supplies the physical blocked
   record and the cleared bitmap for the derived task-map status update.
   It deliberately does not claim the full API, abstract spec_step, global
   record invariant, or a physical context switch. *)
Theorem V293_OSTimeDly_blocking_bridge : forall current rows group y ticks
 bc byloc bd bt br bg base p duration P ks ge le M ir au O op R delay yv lo hi entries tasks message,
 V293_dly_env current rows group y ticks bc byloc bd br bg ge le ->
 p<13 ->lo<256 ->hi<256 ->(0<=base)%Z ->(base+54<=Int.max_unsigned)%Z ->
 duration<>Int.zero ->V293_priority_table entries tasks ->V293_bitmap_tasks lo hi tasks ->
 get tasks(bt,Int.repr base)=Some(Int.repr(Z.of_nat p),rdy,message) ->
 (ge,le,M,ir,au,O,op)|=V293_owned_record_cells
  (V293_dly_cells bc byloc bd bt br bg base p duration delay yv lo hi(V293_ready_group lo hi)) **
  (V293_owned_record_cells(V293_dly_record_extra bt base p message) **R) ->
 let cleared:=V293_ready_clear_rows lo hi p in
 let blocked:=set tasks(bt,Int.repr base)(Int.repr(Z.of_nat p),wait os_stat_time duration,message) in
 exists Mf,
 cstepstar P(curs(V293_dly_updates current rows group y ticks),(kenil,ks))(ge,le,M)
  (SKIP,(kenil,ks))(ge,le,Mf) /\
 (ge,le,Mf,ir,au,O,op)|=V293_owned_record_cells
  (V293_dly_cells bc byloc bd bt br bg base p duration duration(V293_byteval(V293_prio_row p))
   (fst cleared)(snd cleared)(V293_ready_group(fst cleared)(snd cleared))) **
  (V293_owned_record_cells(V293_dly_record_extra bt base p message) **R) /\
 V293_task_record Mf(bt,Int.repr base)(Int.repr(Z.of_nat p))(wait os_stat_time duration)message /\
 V293_bitmap_tasks(fst cleared)(snd cleared)blocked /\V293_priority_table entries blocked /\
 ~V293_bitmap_ready(fst cleared)(snd cleared)p /\
 ~V293_highest_ready blocked(bt,Int.repr base).
Proof.
 intros current rows group y ticks bc byloc bd bt br bg base p duration P ks ge le M ir au O op R delay yv lo hi entries tasks message
 Env Pb Lo Hi Base Limit Nonzero Table Bitmap Task Owned cleared blocked.
 destruct(V293_OSTimeDly_updates_execution current rows group y ticks bc byloc bd bt br bg base p duration
 P ks ge le M ir au O op _ delay yv lo hi Env Pb Lo Hi Base Limit Owned)as(Mf&Exec&Final&Dly).
 exists Mf;split;[exact Exec| ]. split;[exact Final| ]. split.
 - eapply V293_dly_blocked_record;[exact Pb|lia|exact Final].
 - split;[eapply V293_dly_bitmap_tasks;eassumption| ]. split.
   + eapply V293_tick_priority_table;eassumption.
   + split.
     * unfold cleared;rewrite V293_ready_clear_membership by assumption;tauto.
     * intros(pr&msg&Lookup&Min). unfold blocked in Lookup;rewrite map_get_set in Lookup;discriminate.
Qed.
