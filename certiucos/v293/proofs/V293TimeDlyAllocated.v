(* Full local call prefix: locals are allocated here, never supplied typed. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeDlyTail.
Require Import CertiOS.certiucos.v293.proofs.V293TimeDlyCallEntry.
Require Import CertiOS.certiucos.v293.proofs.V293TimeDlyTaskBridge.
Require Import CertiOS.certiucos.v293.proofs.V293TimeDlyBlocking.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.code.V293OSTimeDlyCall.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition V293_dly_call_cells bc bt br bg bi bl base p delay lo hi:list V293_record_cell:=
 [((bc,0%Z),Tptr V293_tcb_type,Vptr(bt,Int.repr base));
  ((bt,(base+52)%Z),Tint8,V293_byteval(V293_prio_row p));
  ((bt,(base+53)%Z),Tint8,V293_mask_value(V293_prio_bit p));
  ((bt,(base+54)%Z),Tint8,V293_mask_value(V293_prio_row p));
  ((bt,(base+44)%Z),Tint32,Vint32 delay);
  ((br,0%Z),Tint8,V293_byteval lo);((br,1%Z),Tint8,V293_byteval hi);
  ((bg,0%Z),Tint8,V293_byteval(V293_ready_group lo hi));
  ((bi,0%Z),Tint8,V293_byteval 0);((bl,0%Z),Tint8,V293_byteval 0)].
Definition V293_dly_guard_cells bi bl:list V293_record_cell:=
 [((bi,0%Z),Tint8,V293_byteval 0);((bl,0%Z),Tint8,V293_byteval 0)].

Theorem V293_dly_allocated_to_sched_refines:forall P ks ge caller M ir enabled si ci O op sd R
 f current rows group y ticks nesting lock sched saved ba byloc bs bc bt br bg bi bl
 base p duration delay lo hi entries tasks message events now,
 P f=Some(V293_dly_function current rows group y ticks nesting lock sched saved) ->
 ticks<>y ->ticks<>saved ->y<>saved ->ba<>byloc ->ba<>bs ->byloc<>bs ->
 fresh M ba ->fresh M byloc ->fresh M bs ->
 let le:=V293_dly_call_lenv ticks y saved ba byloc bs in
 V293_dly_env current rows group y ticks bc byloc ba br bg ge le ->
 get le nesting=None ->get ge nesting=Some(bi,Tint8) ->
 get le lock=None ->get ge lock=Some(bl,Tint8) ->
 p<13 ->lo<256 ->hi<256 ->(0<=base)%Z ->(base+54<=Int.max_unsigned)%Z ->
 duration<>Int.zero ->V293_priority_table entries tasks ->V293_bitmap_tasks lo hi tasks ->
 get tasks(bt,Int.repr base)=Some(Int.repr(Z.of_nat p),rdy,message) ->
 (ge,le,M,ir,(enabled,si,ci),O,op)|=V293_owned_record_cells
 (V293_dly_call_cells bc bt br bg bi bl base p delay lo hi) **
 (V293_owned_record_cells(V293_dly_record_extra bt base p message) **
 (V293_owned_task_records(del tasks(bt,Int.repr base)) **
 (V293_shared_fields(bt,Int.repr base)tasks events now **R))) ->
 let outer:=kcall f(V293_dly_full_body current rows group y ticks nesting lock sched saved)caller ks in
 let blocked:=set tasks(bt,Int.repr base)(Int.repr(Z.of_nat p),wait os_stat_time duration,message) in
 let O':=set O abstcblsid(abstcblist blocked) in
 let cleared:=V293_ready_clear_rows lo hi p in
 exists Mf,
 V293_local_steps P(curs(scall f[econst32 duration]),(kenil,ks))((ge,caller,M),ir,(enabled,si,ci))
 (curs(scall sched nil),(kenil,kseq sret outer))((ge,le,Mf),ir,(enabled,si,ci)) /\
 spec_step sd(spec_prim(cons(Vint32 duration)nil)V293_dly_block_step)O(END None)O' /\
 V293_task_records Mf blocked /\V293_priority_table entries blocked /\
 V293_bitmap_tasks(fst cleared)(snd cleared)blocked /\
 (ge,le,Mf,ir,(enabled,si,ci),O',op)|=V293_owned_record_cells
 (V293_dly_cells bc byloc ba bt br bg base p duration duration(V293_byteval(V293_prio_row p))
 (fst cleared)(snd cleared)(V293_ready_group(fst cleared)(snd cleared))) **
 (V293_owned_record_cells(V293_dly_record_extra bt base p message) **
 (V293_owned_task_records(del tasks(bt,Int.repr base)) **
 (V293_shared_fields(bt,Int.repr base)blocked events now **
 (Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **
 (V293_owned_record_cells(V293_dly_guard_cells bi bl) **R))))).
Proof.
 intros P ks ge caller M ir enabled si ci O op sd R f current rows group y ticks nesting lock sched saved
 ba byloc bs bc bt br bg bi bl base p duration delay lo hi entries tasks message events now
 Program TY TS YS BAY BAS BYS FreshA FreshY FreshS le Env Nn Gn Nl Gl
 Pb Lo Hi Base Limit Positive Table Bits Task Held outer blocked O' cleared.
 destruct(V293_dly_call_entry P ks ge caller M ir(enabled,si,ci)O op
 f current rows group y ticks nesting lock sched saved ba byloc bs duration _
 Program TY TS YS BAY BAS BYS FreshA FreshY FreshS Held)
 as(Mp&Mi&ParamStore&Init&Entry&Owned).
 assert(Cells:(ge,le,Mi,ir,(enabled,si,ci),O,op)|=V293_owned_record_cells
 (V293_dly_call_cells bc bt br bg bi bl base p delay lo hi) **Atrue)
 by(unfold le;clear -Owned;sep auto).
 assert(Read:forall a tp v,In(a,tp,v)(V293_dly_call_cells bc bt br bg bi bl base p delay lo hi) ->
 load tp Mi a=Some v).
 { intros a tp v Member;change(load tp(getmem(ge,le,Mi,ir,(enabled,si,ci),O,op))a=Some v).
   eapply V293_record_star_load_l;[apply V293_owned_record_cells_load;exact Member|exact Cells]. }
 assert(Ticks:load Tint32 Mi(ba,0%Z)=Some(Vint32 duration)).
 { assert(Slot:(ge,le,Mi,ir,(enabled,si,ci),O,op)|=Amapsto(ba,0%Z)Tint32 true(Vint32 duration) **Atrue)
   by(unfold le;clear -Owned;sep auto).
   change(load Tint32(getmem(ge,le,Mi,ir,(enabled,si,ci),O,op))(ba,0%Z)=Some(Vint32 duration)).
   eapply(V293_record_star_load_l(Amapsto(ba,0%Z)Tint32 true(Vint32 duration))Atrue);
   [intros st[H _];eapply mapstoval_load;[reflexivity|exact H]|exact Slot]. }
 assert(YOwned:(ge,le,Mi,ir,(enabled,si,ci),O,op)|=Amapsto(byloc,0%Z)Tint8 true Vundef **
 (Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **
 (Amapsto(ba,0%Z)Tint32 true(Vint32 duration) **
 (V293_owned_record_cells(V293_dly_call_cells bc bt br bg bi bl base p delay lo hi) **
 (V293_owned_record_cells(V293_dly_record_extra bt base p message) **
 (V293_owned_task_records(del tasks(bt,Int.repr base)) **
 (V293_shared_fields(bt,Int.repr base)tasks events now **R)))))))
 by(unfold le;clear -Owned;sep auto).
 pose proof Env as[Nc[Gc[Nr[Gr[Ng[Gg[By Ba]]]]]]].
 destruct(V293_prio_coordinates p Pb)as[Ybound Xbound].
 destruct(V293_dly_body_first_y P outer ge le Mi ir enabled si ci O op _
 current rows group y ticks nesting lock sched bc byloc bt base(V293_prio_row p)bi bl ba duration
 Nn Gn ltac:(apply Read;cbn[V293_dly_call_cells In];tauto)
 Nl Gl ltac:(apply Read;cbn[V293_dly_call_cells In];tauto)Ba Ticks Positive Nc Gc By
 ltac:(apply Read;cbn[V293_dly_call_cells In];tauto)ltac:(apply Read;cbn[V293_dly_call_cells In];tauto)
 Base Limit ltac:(lia)YOwned)as(My&YStore&FirstY&Post&Outside).
 assert(Typed:forall s,s|=Amapsto(ba,0%Z)Tint32 true(Vint32 duration) ->
 s|=V293_owned_record_cell((ba,0%Z),Tint32,Vint32 duration)).
 { intros s H;unfold V293_owned_record_cell;apply astar_l_apure_intro;[exact H|reflexivity]. }
 assert(Converted:(ge,le,My,ir,(enabled,si,ci),O,op)|=
 V293_owned_record_cell((byloc,0%Z),Tint8,V293_byteval(V293_prio_row p)) **
 (Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **
 (V293_owned_record_cell((ba,0%Z),Tint32,Vint32 duration) **
 (V293_owned_record_cells(V293_dly_call_cells bc bt br bg bi bl base p delay lo hi) **
 (V293_owned_record_cells(V293_dly_record_extra bt base p message) **
 (V293_owned_task_records(del tasks(bt,Int.repr base)) **
 (V293_shared_fields(bt,Int.repr base)tasks events now **R))))))).
 { eapply astar_mono;[intros s H;exact H| |exact Post].
   intros s H;eapply astar_mono;[intros st H';exact H'| |exact H].
   intros st H';eapply astar_mono;[apply Typed|intros st' H'';exact H''|exact H']. }
 assert(Ready:(ge,le,My,ir,(enabled,si,ci),O,op)|=V293_owned_record_cells
 (V293_dly_cells bc byloc ba bt br bg base p duration delay(V293_byteval(V293_prio_row p))lo hi(V293_ready_group lo hi)) **
 (V293_owned_record_cells(V293_dly_record_extra bt base p message) **
 (V293_owned_task_records(del tasks(bt,Int.repr base)) **
 (V293_shared_fields(bt,Int.repr base)tasks events now **
 (Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **
 (V293_owned_record_cells(V293_dly_guard_cells bi bl) **R)))))).
 { cbn[V293_dly_call_cells V293_dly_guard_cells V293_dly_cells V293_owned_record_cells]in Converted|-*.
   clear -Converted;sep auto. }
 destruct(V293_dly_after_y_to_sched_refines current rows group y ticks sched
 bc byloc ba bt br bg base p duration P outer ge le My ir enabled si ci O op sd _
 delay lo hi entries tasks message events now Env Pb Lo Hi Base Limit Positive Table Bits Task Ready)
 as(Mf&Tail&Step&Records&Prio&Bitmap&Returned).
 exists Mf;split.
 - eapply V293_local_trans;[exact Entry| ]. eapply V293_local_trans;[exact FirstY|exact Tail].
 - split;[exact Step| ];split;[exact Records| ];split;[exact Prio| ];split;[exact Bitmap|exact Returned].
Qed.
