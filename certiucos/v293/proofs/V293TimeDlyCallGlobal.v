(* Real client constant evaluation and OS allocation use separate heaps.
   Classification is derived at each boundary, never supplied as a trace. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeDlyAllocated.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyGlobalTrace.
Require Import CertiOS.certiucos.v293.proofs.V293LocalGlobalTrace.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCallGlobal.
Require Import CertiOS.certiucos.v293.proofs.V293TimeDlyGlobalSwitch.
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
Require Import CertiOS.certiucos.v293.code.V293OSTimeDly.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAPICall.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.framework.proof.join_prop.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Require Import Coq.Relations.Relation_Operators.
Import ListNotations.
Local Open Scope nat_scope.


Lemma V293_client_no_os_context:forall P c ke ks,
 callcont ks=None ->intcont ks=None ->
 (forall f vl tl,c<>curs(sfexec f vl tl)) ->~InOS(c,(ke,ks))P.
Proof.
 intros P c ke ks Call Int NotExec (c'&ke'&ks'&Eq&Cases).
 inversion Eq;subst c' ke' ks'. destruct Cases as[(f&vl&fc&tl&E&Bind)|Cases].
 - eapply NotExec;exact E.
 - destruct Cases as[(f&le&tail&ty&d1&d2&s&body&E&Bind)|NoInt];congruence.
Qed.

Lemma V293_client_unchanged_global:forall pc po pi ip T les aus t ge ole OM ir aux
 cge cles CM cle C C',get cles t=Some cle ->
 cstep(pumerge pc po)C(cge,cle,CM)C'(cge,cle,CM) ->~InOS C(pumerge po pi) ->
 V293_global_steps(pc,(po,pi,ip))(cge,cles,CM)
 (V293_local_global_at T les aus t C((ge,ole,OM),ir,aux))
 (V293_local_global_at T les aus t C'((ge,ole,OM),ir,aux)).
Proof.
 intros pc po pi ip T les aus t ge ole OM ir aux cge cles CM cle C C' Get Step Outside.
 unfold V293_global_steps; eapply rt1n_trans;[ |apply rt1n_refl].
 cbn[V293_local_global_at V293_global_at];eapply pt_step.
 - apply map_get_set.
 - symmetry;apply set_set_eq.
 - unfold projS,projD;rewrite !map_get_set;reflexivity.
 - unfold projS,projD;rewrite !map_get_set;reflexivity.
 - split;[unfold Dteq|unfold Piteq];intros other Ne;simpl;
   rewrite !map_get_set';reflexivity ||congruence.
 - eapply clt_step with(cenvs:=cles)(le:=cle)(le':=cle)(M:=CM)(M':=CM)(ge:=cge);
   [reflexivity|exact Step|exact Outside|reflexivity|reflexivity|exact Get|reflexivity| ].
   change((cge,cles,CM)=(cge,set cles t cle,CM)).
   assert(Identity:set cles t cle=cles)by exact(CltEnvMod.get_set_same Get).
   rewrite Identity;reflexivity.
Qed.

Theorem V293_constant_call_global:forall pc po pi ip T les aus t ge ole OM ir aux
 cge cles CM cle f n,get cles t=Some cle ->
 V293_global_steps(pc,(po,pi,ip))(cge,cles,CM)
 (V293_local_global_at T les aus t(curs(scall f[econst32 n]),(kenil,kstop))((ge,ole,OM),ir,aux))
 (V293_local_global_at T les aus t(curs(sfexec f[Vint32 n][Tint32]),(kenil,kstop))((ge,ole,OM),ir,aux)).
Proof.
 intros pc po pi ip T les aus t ge ole OM ir aux cge cles CM cle f n Get.
 eapply V293_global_trans with(b:=V293_local_global_at T les aus t
 (cure(econst32 n),(kenil,kfuneval f nil[Tint32]nil kstop))((ge,ole,OM),ir,aux)).
 - eapply V293_client_unchanged_global;[exact Get| | ].
   + eapply stmt_step;[reflexivity|apply spcall_step;reflexivity].
   + apply V293_client_no_os_context;try reflexivity;intros;discriminate.
 - eapply V293_global_trans with(b:=V293_local_global_at T les aus t
   (curs(sskip(Some(Vint32 n))),(kenil,kfuneval f nil[Tint32]nil kstop))((ge,ole,OM),ir,aux)).
   + eapply V293_client_unchanged_global;[exact Get| | ].
     * eapply expr_step;[reflexivity|constructor].
     * apply V293_client_no_os_context;try reflexivity;intros;discriminate.
   + eapply V293_client_unchanged_global;[exact Get| | ].
     * eapply stmt_step;[reflexivity|apply svfevalnil_step].
     * apply V293_client_no_os_context;try reflexivity;intros;discriminate.
Qed.

Theorem V293_dly_raw_body_to_sched:forall P ge le M ir enabled si ci O op sd R
 current rows group y ticks nesting lock sched bs bc byloc ba bt br bg bi bl
 base p duration delay lo hi entries tasks message events now,
 V293_dly_env current rows group y ticks bc byloc ba br bg ge le ->
 get le nesting=None ->get ge nesting=Some(bi,Tint8) ->
 get le lock=None ->get ge lock=Some(bl,Tint8) ->
 p<13 ->lo<256 ->hi<256 ->(0<=base)%Z ->(base+54<=Int.max_unsigned)%Z ->
 duration<>Int.zero ->V293_priority_table entries tasks ->V293_bitmap_tasks lo hi tasks ->
 get tasks(bt,Int.repr base)=Some(Int.repr(Z.of_nat p),rdy,message) ->
 (ge,le,M,ir,(enabled,si,ci),O,op)|=Amapsto(byloc,0%Z)Tint8 true Vundef **
 (Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **
 (Amapsto(ba,0%Z)Tint32 true(Vint32 duration) **
 (V293_owned_record_cells(V293_dly_call_cells bc bt br bg bi bl base p delay lo hi) **
 (V293_owned_record_cells(V293_dly_record_extra bt base p message) **
 (V293_owned_task_records(del tasks(bt,Int.repr base)) **
 (V293_shared_fields(bt,Int.repr base)tasks events now **R)))))) ->
 let blocked:=set tasks(bt,Int.repr base)(Int.repr(Z.of_nat p),wait os_stat_time duration,message) in
 let O':=set O abstcblsid(abstcblist blocked) in let cleared:=V293_ready_clear_rows lo hi p in
 exists Mf,
 V293_local_steps P(curs(V293_dly_body current rows group y ticks nesting lock sched),(kenil,kstop))
 ((ge,le,M),ir,(enabled,si,ci))
 (curs(scall sched nil),(kenil,kseq sret kstop))((ge,le,Mf),ir,(enabled,si,ci)) /\
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
 intros P ge le M ir enabled si ci O op sd R current rows group y ticks nesting lock sched
 bs bc byloc ba bt br bg bi bl base p duration delay lo hi entries tasks message events now
 Env Nn Gn Nl Gl Pb Lo Hi Base Limit Positive Table Bits Task YOwned blocked O' cleared.
 assert(Cells:(ge,le,M,ir,(enabled,si,ci),O,op)|=V293_owned_record_cells
 (V293_dly_call_cells bc bt br bg bi bl base p delay lo hi) **Atrue)
 by(clear -YOwned;sep auto).
 assert(Read:forall a tp v,In(a,tp,v)(V293_dly_call_cells bc bt br bg bi bl base p delay lo hi) ->
 load tp M a=Some v).
 { intros a tp v Member;change(load tp(getmem(ge,le,M,ir,(enabled,si,ci),O,op))a=Some v).
   eapply V293_record_star_load_l;[apply V293_owned_record_cells_load;exact Member|exact Cells]. }
 assert(Ticks:load Tint32 M(ba,0%Z)=Some(Vint32 duration)).
 { assert(Slot:(ge,le,M,ir,(enabled,si,ci),O,op)|=Amapsto(ba,0%Z)Tint32 true(Vint32 duration) **Atrue)
   by(clear -YOwned;sep auto).
   change(load Tint32(getmem(ge,le,M,ir,(enabled,si,ci),O,op))(ba,0%Z)=Some(Vint32 duration)).
   eapply(V293_record_star_load_l(Amapsto(ba,0%Z)Tint32 true(Vint32 duration))Atrue);
   [intros st[H _];eapply mapstoval_load;[reflexivity|exact H]|exact Slot]. }
 pose proof Env as[Nc[Gc[Nr[Gr[Ng[Gg[By Ba]]]]]]].
 destruct(V293_prio_coordinates p Pb)as[Ybound Xbound].
 destruct(V293_dly_body_first_y P kstop ge le M ir enabled si ci O op _
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
 bc byloc ba bt br bg base p duration P kstop ge le My ir enabled si ci O op sd _
 delay lo hi entries tasks message events now Env Pb Lo Hi Base Limit Positive Table Bits Task Ready)
 as(Mf&Tail&Step&Records&Prio&Bitmap&Returned).
 exists Mf;split.
 - eapply V293_local_trans;[exact FirstY|exact Tail].
 - split;[exact Step| ];split;[exact Records| ];split;[exact Prio| ];split;[exact Bitmap|exact Returned].
Qed.

(* The client prefix reads no OS memory. Only sfexec enters the bound OS
   function, and only that transition creates its real saved caller frame. *)
Theorem V293_dly_global_call_entry:forall pc po pi ip T les aus t
 cge cles CM cle ge caller M ir aux O op
 f current rows group y ticks nesting lock sched saved ba byloc bs n R,
 get cles t=Some cle ->
 po f=Some(V293_dly_function current rows group y ticks nesting lock sched saved) ->
 ticks<>y ->ticks<>saved ->y<>saved ->
 ba<>byloc ->ba<>bs ->byloc<>bs ->fresh M ba ->fresh M byloc ->fresh M bs ->
 (ge,V293_dly_call_lenv ticks y saved ba byloc bs,M,ir,aux,O,op)|=R ->
 exists Mp Mi,
 store Tint32(allocb M ba 0%Z 4)(ba,0%Z)(Vint32 n)=Some Mp /\
 store Tint32(allocb(allocb Mp byloc 0%Z 1)bs 0%Z 4)(bs,0%Z)(Vint32 Int.zero)=Some Mi /\
 V293_global_steps(pc,(po,pi,ip))(cge,cles,CM)
 (V293_local_global_at T les aus t(curs(scall f[econst32 n]),(kenil,kstop))((ge,caller,M),ir,aux))
 (V293_local_global_at T les aus t
 (curs(V293_dly_body current rows group y ticks nesting lock sched),
 (kenil,kcall f(V293_dly_full_body current rows group y ticks nesting lock sched saved)caller kstop))
 ((ge,V293_dly_call_lenv ticks y saved ba byloc bs,Mi),ir,aux)) /\
 (ge,V293_dly_call_lenv ticks y saved ba byloc bs,Mi,ir,aux,O,op)|=
 Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **
 (Amapsto(byloc,0%Z)Tint8 true Vundef **(Amapsto(ba,0%Z)Tint32 true(Vint32 n) **R)).
Proof.
 intros pc po pi ip T les aus t cge cles CM cle ge caller M ir aux O op
 f current rows group y ticks nesting lock sched saved ba byloc bs n R
 Get Bind TY TS YS BTY BTS BYS FreshT FreshY FreshS Held.
 assert(Program:pumerge po pi f=Some(V293_dly_function current rows group y ticks nesting lock sched saved)).
 { unfold pumerge;rewrite Bind;reflexivity. }
 destruct(V293_dly_call_entry(pumerge po pi)kstop ge caller M ir aux O op
 f current rows group y ticks nesting lock sched saved ba byloc bs n R
 Program TY TS YS BTY BTS BYS FreshT FreshY FreshS Held)
 as(Mp&Mi&Store&Init&LocalEntry&Owned).
 assert(FY:fresh Mp byloc).
 { eapply V293_time_fresh_after_store;[exact BTY| |exact Store].
   apply V293_time_fresh_after_alloc;assumption. }
 assert(FS:fresh(allocb Mp byloc 0%Z 1)bs).
 { apply V293_dly_fresh_byte_alloc;[exact BYS| ].
   eapply V293_time_fresh_after_store;[exact BTS| |exact Store].
   apply V293_time_fresh_after_alloc;assumption. }
 set(body:=V293_dly_full_body current rows group y ticks nesting lock sched saved).
 set(frame:=kcall f body caller kstop).
 exists Mp;exists Mi;split;[exact Store| ];split;[exact Init| ];split;[ |exact Owned].
 eapply V293_global_trans;[eapply V293_constant_call_global;exact Get| ].
 eapply V293_global_trans with(b:=V293_local_global_at T les aus t
 (curs(salloc (cons (Vint32 n) nil)(dcons ticks Tint32(dcons y Tint8(dcons saved Tint32 dnil)))),(kenil,frame))
 ((ge,emp,M),ir,aux)).
 { apply V293_loststep_global_single.
   - exists(curs(sfexec f[Vint32 n][Tint32]));exists kenil;exists kstop;split;[reflexivity|left].
     exists f;exists [Vint32 n];exists(V293_dly_function current rows group y ticks nesting lock sched saved);exists [Tint32].
     split;[reflexivity|exact Program].
   - apply ostc_step;eapply stmt_step;[reflexivity| ].
     eapply sfexec_step with(d1:=dcons ticks Tint32 dnil)(d2:=dcons y Tint8(dcons saved Tint32 dnil));
     [reflexivity|reflexivity|exact Program|split;[exact I|reflexivity]|reflexivity]. }
 eapply V293_global_trans with(b:=V293_local_global_at T les aus t
 (curs(salloc nil(dcons y Tint8(dcons saved Tint32 dnil))),(kenil,frame))
 ((ge,set emp ticks(ba,Tint32),Mp),ir,aux)).
 { apply V293_loststep_global_single.
   - unfold frame,body;eapply V293_bound_call_inos;exact Bind.
   - apply ostc_step;eapply stmt_step;[reflexivity| ];eapply sallocp_step with(b:=ba);
     [reflexivity|reflexivity| |apply map_get_set|exact Store].
     exists ba;repeat split;try assumption;try reflexivity.
     intros[v E];rewrite map_emp_get in E;discriminate. }
 eapply V293_global_trans with(b:=V293_local_global_at T les aus t
 (curs(salloc nil(dcons saved Tint32 dnil)),(kenil,frame))
 ((ge,set(set emp ticks(ba,Tint32))y(byloc,Tint8),allocb Mp byloc 0%Z 1),ir,aux)).
 { apply V293_loststep_global_single.
   - unfold frame,body;eapply V293_bound_call_inos;exact Bind.
   - apply ostc_step;eapply stmt_step;[reflexivity| ];eapply salloclv_step;
     [reflexivity|reflexivity| ]. exists byloc;repeat split;try assumption;try reflexivity.
     intros[v E];rewrite map_get_set' in E by congruence;rewrite map_emp_get in E;discriminate. }
 eapply V293_global_trans with(b:=V293_local_global_at T les aus t
 (curs(salloc nil dnil),(kenil,frame))
 ((ge,V293_dly_call_lenv ticks y saved ba byloc bs,allocb(allocb Mp byloc 0%Z 1)bs 0%Z 4),ir,aux)).
 { apply V293_loststep_global_single.
   - unfold frame,body;eapply V293_bound_call_inos;exact Bind.
   - apply ostc_step;eapply stmt_step;[reflexivity| ];eapply salloclv_step;
     [reflexivity|reflexivity| ]. exists bs;repeat split;try assumption;try reflexivity.
     intros[v E];rewrite !map_get_set' in E by congruence;rewrite map_emp_get in E;discriminate. }
 eapply V293_global_trans with(b:=V293_local_global_at T les aus t(curs body,(kenil,frame))
 ((ge,V293_dly_call_lenv ticks y saved ba byloc bs,allocb(allocb Mp byloc 0%Z 1)bs 0%Z 4),ir,aux)).
 { apply V293_loststep_global_single.
   - unfold frame,body;eapply V293_bound_call_inos;exact Bind.
   - apply ostc_step;eapply stmt_step;[reflexivity|apply sallocend_step]. }
 assert(Initialize:V293_local_steps(pumerge po pi)(curs body,(kenil,kstop))
 ((ge,V293_dly_call_lenv ticks y saved ba byloc bs,allocb(allocb Mp byloc 0%Z 1)bs 0%Z 4),ir,aux)
 (curs(V293_dly_body current rows group y ticks nesting lock sched),(kenil,kstop))
 ((ge,V293_dly_call_lenv ticks y saved ba byloc bs,Mi),ir,aux)).
 { unfold body,V293_dly_full_body.
   eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sseq_step]| ].
   eapply V293_local_trans.
   { apply V293_csteps_local;eapply V293_success_assign_zero;
     [unfold V293_dly_call_lenv;apply map_get_set|exact Init]. }
   eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sskip_step]| ].
   apply V293_local_refl. }
 eapply(V293_local_steps_global pc po pi ip _ _ _ _ Initialize f body caller kstop
 Tvoid(dcons ticks Tint32 dnil)(dcons y Tint8(dcons saved Tint32 dnil))T les aus t(cge,cles,CM)Bind).
 change(goodks(pc,(po,pi,ip))frame);unfold frame;cbn[goodks];unfold pumerge;rewrite Bind;exact I.
Qed.

(* Stable function interface: a real constant client call reaches the blocking
   scheduler boundary in the original global transition closure. *)
Theorem V293_dly_global_call_to_sched_refines:forall pc po pi ip T les aus t cge cles CM cle ge caller M ir enabled si ci O op sd R
 f current rows group y ticks nesting lock sched saved ba byloc bs bc bt br bg bi bl
 base p duration delay lo hi entries tasks message events now,
 get cles t=Some cle ->
 po f=Some(V293_dly_function current rows group y ticks nesting lock sched saved) ->
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
 let outer:=kcall f(V293_dly_full_body current rows group y ticks nesting lock sched saved)caller kstop in
 let blocked:=set tasks(bt,Int.repr base)(Int.repr(Z.of_nat p),wait os_stat_time duration,message) in
 let O':=set O abstcblsid(abstcblist blocked) in
 let cleared:=V293_ready_clear_rows lo hi p in
 exists Mf,
 V293_global_steps(pc,(po,pi,ip))(cge,cles,CM)
 (V293_local_global_at T les aus t(curs(scall f[econst32 duration]),(kenil,kstop))((ge,caller,M),ir,(enabled,si,ci)))
 (V293_local_global_at T les aus t(curs(scall sched nil),(kenil,kseq sret outer))((ge,le,Mf),ir,(enabled,si,ci))) /\
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
 intros pc po pi ip T les aus t cge cles CM cle ge caller M ir enabled si ci O op sd R
 f current rows group y ticks nesting lock sched saved ba byloc bs bc bt br bg bi bl
 base p duration delay lo hi entries tasks message events now
 Get Bind TY TS YS BAY BAS BYS FreshA FreshY FreshS le Env Nn Gn Nl Gl
 Pb Lo Hi Base Limit Positive Table Bits Task Held outer blocked O' cleared.
 destruct(V293_dly_global_call_entry pc po pi ip T les aus t cge cles CM cle
 ge caller M ir(enabled,si,ci)O op f current rows group y ticks nesting lock sched saved
 ba byloc bs duration _ Get Bind TY TS YS BAY BAS BYS FreshA FreshY FreshS Held)
 as(Mp&Mi&ParamStore&Init&Entry&Owned).
 assert(YOwned:(ge,le,Mi,ir,(enabled,si,ci),O,op)|=Amapsto(byloc,0%Z)Tint8 true Vundef **
 (Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **
 (Amapsto(ba,0%Z)Tint32 true(Vint32 duration) **
 (V293_owned_record_cells(V293_dly_call_cells bc bt br bg bi bl base p delay lo hi) **
 (V293_owned_record_cells(V293_dly_record_extra bt base p message) **
 (V293_owned_task_records(del tasks(bt,Int.repr base)) **
 (V293_shared_fields(bt,Int.repr base)tasks events now **R)))))))
 by(unfold le;clear -Owned;sep auto).
 destruct(V293_dly_raw_body_to_sched(pumerge po pi)ge le Mi ir enabled si ci O op sd R
 current rows group y ticks nesting lock sched bs bc byloc ba bt br bg bi bl
 base p duration delay lo hi entries tasks message events now
 Env Nn Gn Nl Gl Pb Lo Hi Base Limit Positive Table Bits Task YOwned)
 as(Mf&Body&Step&Records&Table'&Bits'&Returned).
 exists Mf;split.
 - eapply V293_global_trans;[exact Entry| ].
   eapply(V293_local_steps_global pc po pi ip _ _ _ _ Body f
   (V293_dly_full_body current rows group y ticks nesting lock sched saved)caller kstop
   Tvoid(dcons ticks Tint32 dnil)(dcons y Tint8(dcons saved Tint32 dnil))T les aus t(cge,cles,CM)Bind).
   change(goodks(pc,(po,pi,ip))(kcall f
   (V293_dly_full_body current rows group y ticks nesting lock sched saved)caller kstop)).
   cbn[goodks];unfold pumerge;rewrite Bind;exact I.
 - split;[exact Step| ];split;[exact Records| ];split;[exact Table'| ];split;[exact Bits'|exact Returned].
Qed.
