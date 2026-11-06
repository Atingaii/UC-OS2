(* A source-call wrapper in the accepted interrupt abstraction, not a
   fabricated platform ISR. Entry creates the continuation it later consumes. *)
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitDispatchCall.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitInterruptGlobal.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitResumedReturn.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterInternal.
Require Import CertiOS.certiucos.v293.code.V293OSIntEnter.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCriticalGlobal.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCallGlobal.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.framework.proof.join_prop.
Require Import CertiOS.framework.proof.memory_prop.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Logic.FunctionalExtensionality Coq.Lists.List Lia.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitDispatchExecution.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitCallExecution.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyFullCall.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrent.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitExecution.
Require Import CertiOS.certiucos.v293.proofs.V293ReadySchedCall.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.code.V293OSIntExit.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
Require Import Coq.Lists.List Lia.
Require Import CertiOS.certiucos.v293.proofs.V293LocalGlobalTrace.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyGlobalTrace.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import Coq.Relations.Relation_Operators.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Import ListNotations.
Local Open Scope nat_scope.

Definition V293_irq_source_wrapper enter exit vector :=
 sseq(sprim(eoi vector))
 (sseq(scall enter nil)(sseq(scall exit nil)(sprim exint))).

Theorem V293_OSIntEnter_zero_call : forall P ks ge caller M
 f running nesting br bn,
 P f=Some(V293_OSIntEnter_function running nesting) ->
 get ge running=Some(br,Tint8) ->get ge nesting=Some(bn,Tint8) ->
 load Tint8 M(br,0%Z)=Some(V293_byteval 1) ->
 load Tint8 M(bn,0%Z)=Some(V293_byteval 0) ->
 (exists v,get M(bn,0%Z)=Some(true,v)) ->
 cstepstar P(curs(scall f nil),(kenil,ks))(ge,caller,M)
 (SKIP,(kenil,ks))(ge,caller,V293_put_byte M(bn,0%Z)1) /\
 load Tint8(V293_put_byte M(bn,0%Z)1)(bn,0%Z)=Some(V293_byteval 1) /\
 (forall b j,(b,j)<>(bn,0%Z) ->
 get(V293_put_byte M(bn,0%Z)1)(b,j)=get M(b,j)).
Proof.
 intros P ks ge caller M f running nesting br bn Program GR GN Run Nest[v Writable].
 assert(NR:get(emp:env)running=None)by apply map_emp_get.
 assert(NN:get(emp:env)nesting=None)by apply map_emp_get.
 assert(Room:evalval(V293_OSIntEnter_room nesting)(ge,emp,M)=Some(Vint32 Int.one)).
 { unfold V293_OSIntEnter_room;cbn[evalval evaltype get_lenv get_genv].
   rewrite NN,GN;cbn -[load];rewrite Nest;reflexivity. }
 assert(Assign:cstepstar P
 (curs(sassign(evar nesting)(V293_OSIntEnter_next nesting)),
 (kenil,kseq(sskip None)(kseq sret(kcall f(V293_OSIntEnter_body running nesting)caller ks))))
 (ge,emp,M)(SKIP,
 (kenil,kseq(sskip None)(kseq sret(kcall f(V293_OSIntEnter_body running nesting)caller ks))))
 (ge,emp,V293_put_byte M(bn,0%Z)1)).
 { eapply V293_assign_byte_execution.
   - cbn[evaltype];rewrite NN,GN;reflexivity.
   - cbn[evaladdr get_lenv get_genv];rewrite NN,GN;reflexivity.
   - unfold V293_OSIntEnter_next;cbn[evaltype];rewrite NN,GN;reflexivity.
   - unfold V293_OSIntEnter_next;cbn[evalval evaltype get_lenv get_genv].
     rewrite NN,GN;cbn -[load];rewrite Nest;reflexivity.
   - change(store Tint8 M(bn,0%Z)(V293_byteval 1)=Some(V293_put_byte M(bn,0%Z)1)).
     apply V293_put_byte_store with(old:=v);exact Writable. }
 split.
 - eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply snpcall_step]| ].
   eapply c_stepstarn.
   { eapply stmt_step;[reflexivity| ];eapply sfexec_step with(d1:=dnil)(d2:=dnil);
     [reflexivity|reflexivity|exact Program|exact I|reflexivity]. }
   eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply sallocend_step]| ].
   unfold V293_OSIntEnter_body at 1.
   eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply sseq_step]| ].
   unfold V293_OSIntEnter_updates.
   eapply V293_cstepstar_trans.
   { apply V293_entry_if_select with(flag:=true).
     exact(V293_success_global_byte_eq ge emp M running br 1 1
       ltac:(lia)ltac:(lia)NR GR Run). }
   eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply sseq_step]| ].
   eapply V293_cstepstar_trans.
   { eapply V293_rekey_if_execution with(flag:=true);
     [exact Room|intros _;exact Assign|discriminate]. }
   eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply sskip_step]| ].
   eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply sskip_step]| ].
   eapply c_stepstarn.
   { eapply stmt_step;[reflexivity| ];eapply sret_step with(al:=nil);
     [reflexivity|reflexivity|reflexivity]. }
   eapply c_stepstarn;[eapply stmt_step;[reflexivity|eapply sfreeend_step;reflexivity]| ].
   apply c_stepstar0.
 - split;[apply V293_put_byte_load;lia|intros;apply V293_put_byte_other;assumption].
Qed.

(* This is the actual pint_step, including emp handler environment, ISR bit,
   interrupt stack and the saved expression continuation. No input kint. *)
Theorem V293_interrupt_source_enter : forall pc po pi ip T les aus cst t
 ge le M ir si c ke ks i handler,
 get T t=Some(c,(ke,ks)) ->get les t=Some le ->get aus t=Some((true,si,nil):localst) ->
 higherint ir i ->i<INUM ->ip i=Some handler ->
 lpstep(pc,(po,pi,ip))T cst(ge,les,M,ir,aus)t
 (set T t(curs handler,(kenil,kint c ke le ks)))cst
 (ge,set les t emp,M,isrupd ir i true,set aus t(false,i::si,nil))t.
Proof.
 intros pc po pi ip T les aus cst t ge le M ir si c ke ks i handler Code Env Aux Higher Range Installed.
 eapply pint_step.
 - reflexivity.
 - exact Code.
 - reflexivity.
 - unfold projS,projD;cbn;rewrite Env. rewrite Aux. reflexivity.
 - unfold projS,projD;cbn;rewrite !map_get_set;reflexivity.
 - split;[unfold Dteq|unfold Piteq];intros other Apart;cbn;
   rewrite !map_get_set';reflexivity||congruence.
 - eapply li_step;eassumption||reflexivity.
Qed.

Lemma V293_interrupt_eoi_restores_ir : forall ir i,
 ir i=false ->isrupd(isrupd ir i true)i false=ir.
Proof.
 intros ir i Clear;apply functional_extensionality;intro j.
 unfold isrupd;destruct(Nat.eqb i j)eqn:E;[apply Nat.eqb_eq in E;subst;exact(eq_sym Clear)|reflexivity].
Qed.

(* Both complete calls are built from owned cells. This endpoint deliberately
   stops before exint, so the generated continuation can be framed around it. *)
Theorem V293_interrupt_source_calls :
 forall br bg bp P ge M ir i si O op ct R tasks nc entry
 f sched_id unmap group rows high y table target nesting lock running saved current counter int_switch
 bt bh bo bn bl brun bc oldhigh oldtarget,
 P entry=Some(V293_OSIntEnter_function running nesting) ->
 P f=Some(V293_OSIntExit_abstract_function running nesting lock saved table high target current counter sched_id int_switch) ->
 P sched_id=Some(V293_OSSchedNew_function unmap group rows high y) ->
 ~In saved [unmap;group;rows;high;table;target;nesting;lock;running;current] ->
 y<>unmap ->y<>group ->y<>rows ->y<>high ->y<>table ->bh<>bp ->bn<>bt ->
 get ge unmap=Some(bt,Tarray Tint8 256) ->get ge group=Some(bg,Tint8) ->
 get ge rows=Some(br,Tarray Tint8 2) ->get ge high=Some(bh,Tint8) ->
 get ge table=Some(bp,Tarray(Tptr V293_tcb_type)13) ->get ge target=Some(bo,Tptr V293_tcb_type) ->
 get ge nesting=Some(bn,Tint8) ->get ge lock=Some(bl,Tint8) ->
 get ge running=Some(brun,Tint8) ->get ge current=Some(bc,Tint8) ->
 get O abstcblsid=Some(abstcblist tasks) ->V293_current_task tasks ct nc ->
 V293_highest_ready tasks ct ->GoodInvAsrt R ->
 (forall n,n<256 ->load Tint8 M(bt,Z.of_nat n)=Some(V293_byteval(V293_ready_lookup n))) ->
 (ge,emp,M,ir,(false,i::si,nil),O,op)|=SWINVt(V293_ready_inv br bg bp)ct **
 (V293_owned_record_cell((bh,0%Z),Tint8,oldhigh) **
 (V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,oldtarget) **
 (V293_owned_record_cell((bn,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((bl,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval nc) **
 (V293_owned_record_cell((brun,0%Z),Tint8,V293_byteval 1) **R)))))) ->
 exists bs Mf,fresh(V293_put_byte M(bn,0%Z)1)bs /\
 V293_local_steps P
 (curs(sseq(scall entry nil)(sseq(scall f nil)(sprim exint))),(kenil,kstop))
 ((ge,emp,M),ir,(false,i::si,nil))
 (curs(sprim exint),(kenil,kstop))((ge,emp,Mf),ir,(false,i::si,nil)) /\
 (ge,emp,Mf,ir,(false,i::si,nil),O,op)|=SWINVt(V293_ready_inv br bg bp)ct **
 (V293_owned_record_cell((bh,0%Z),Tint8,V293_byteval nc) **
 (V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,Vptr ct) **
 (V293_owned_record_cell((bn,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((bl,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval nc) **
 (V293_owned_record_cell((brun,0%Z),Tint8,V293_byteval 1) **R)))))) /\
 load(Tptr V293_tcb_type)Mf(bo,0%Z)=Some(Vptr ct) /\
 (forall k,k<4 ->get Mf(bs,Z.of_nat k)=None) /\
 (forall c i,c<>bs ->c<>bo ->(c,i)<>(bh,0%Z) ->(c,i)<>(bn,0%Z) ->get Mf(c,i)=get M(c,i)).

Proof.
 intros br bg bp P ge M ir i si O op ct R tasks nc entry
 f sched_id unmap group rows high y table target nesting lock running saved current counter int_switch
 bt bh bo bn bl brun bc oldhigh oldtarget
 Enter Program Scheduler SavedNames YU YG YR YH YT HP NT GU GG GR GH GT GO GN GL GRun GC
 Map Current Highest Good Lookup Held.
 set(Frame:=SWINVt(V293_ready_inv br bg bp)ct **
 (V293_owned_record_cell((bh,0%Z),Tint8,oldhigh) **
 (V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,oldtarget) **
 (V293_owned_record_cell((bl,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval nc) **
 (V293_owned_record_cell((brun,0%Z),Tint8,V293_byteval 1) **R)))))).
 assert(Raw:(ge,emp,M,ir,(false,i::si,nil),O,op)|=
 Amapsto(bn,0%Z)Tint8 true(V293_byteval 0) **Frame).
 { unfold Frame;unfold V293_owned_record_cell in Held|-*;sep auto. }
 assert(Run:load Tint8 M(brun,0%Z)=Some(V293_byteval 1)).
 { change(load Tint8(getmem(ge,emp,M,ir,(false,i::si,nil),O,op))(brun,0%Z)=Some(V293_byteval 1)).
   eapply V293_record_star_load_l;[apply V293_owned_record_cell_load| ].
   assert(H:(ge,emp,M,ir,(false,i::si,nil),O,op)|=
     V293_owned_record_cell((brun,0%Z),Tint8,V293_byteval 1) **
     (SWINVt(V293_ready_inv br bg bp)ct **
     (V293_owned_record_cell((bh,0%Z),Tint8,oldhigh) **
     (V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,oldtarget) **
     (V293_owned_record_cell((bn,0%Z),Tint8,V293_byteval 0) **
     (V293_owned_record_cell((bl,0%Z),Tint8,V293_byteval 0) **
     (V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval nc) **R))))))).
   { clear Raw;sep auto. } exact H. }
 assert(Nest:load Tint8 M(bn,0%Z)=Some(V293_byteval 0)).
 { change(load Tint8(getmem(ge,emp,M,ir,(false,i::si,nil),O,op))(bn,0%Z)=Some(V293_byteval 0)).
   eapply V293_record_star_load_l;[ |exact Raw].
   intros st [Points Empty];eapply mapstoval_load;[reflexivity|exact Points]. }
 pose proof(V293_tick_raw_owned_writable _ _ _ _ _ _ _ _ _ _ _ Raw)as Writable.
 destruct(Writable 0 ltac:(cbn;lia))as[v Writable0].
 cbn in Writable0.
 destruct(V293_tick_raw_slot_update (bn,0%Z) Tint8 (V293_byteval 0) (V293_byteval 1) Frame ge emp M ir (false,i::si,nil) O op eq_refl Raw)
 as(M1&Store&Updated).
 assert(Same:M1=V293_put_byte M(bn,0%Z)1).
 { pose proof(V293_put_byte_store M(bn,0%Z)1 v Writable0);congruence. } subst M1.
 assert(Next:(ge,emp,V293_put_byte M(bn,0%Z)1,ir,(false,i::si,nil),O,op)|=
 SWINVt(V293_ready_inv br bg bp)ct **
 (V293_owned_record_cell((bh,0%Z),Tint8,oldhigh) **
 (V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,oldtarget) **
 (V293_owned_record_cell((bn,0%Z),Tint8,V293_byteval 1) **
 (V293_owned_record_cell((bl,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval nc) **
 (V293_owned_record_cell((brun,0%Z),Tint8,V293_byteval 1) **R))))))).
 { clear Held Raw;unfold Frame in Updated;sep auto. }
 assert(Lookup1:forall n,n<256 ->load Tint8(V293_put_byte M(bn,0%Z)1)(bt,Z.of_nat n)=
 Some(V293_byteval(V293_ready_lookup n))).
 { intros n Bound;rewrite V293_put_byte_other_load by congruence;apply Lookup;exact Bound. }
 destruct(V293_OSIntExit_same_task_call_execution br bg bp P(kseq(sprim exint)kstop)
 ge emp(V293_put_byte M(bn,0%Z)1)ir false(i::si)nil O op ct R tasks nc
 f sched_id unmap group rows high y table target nesting lock running saved current counter int_switch
 bt bh bo bn bl brun bc oldhigh oldtarget
 Program Scheduler SavedNames YU YG YR YH YT HP NT GU GG GR GH GT GO GN GL GRun GC
 Map Current Highest Good Lookup1 Next)as(bs&Mf&Fresh&Exit&After&Target&Dead&Preserved).
 exists bs;exists Mf;split;[exact Fresh| ];split.
 - eapply V293_local_cons.
   { apply ostc_step;eapply stmt_step;[reflexivity|apply sseq_step]. }
   eapply V293_local_trans.
   { apply V293_csteps_local.
     exact(proj1(V293_OSIntEnter_zero_call P _ ge emp M entry running nesting brun bn
     Enter GRun GN Run Nest(ex_intro _ v Writable0))). }
   eapply V293_local_cons.
   { apply ostc_step;eapply stmt_step;[reflexivity|apply sskip_step]. }
   eapply V293_local_cons.
   { apply ostc_step;eapply stmt_step;[reflexivity|apply sseq_step]. }
   eapply V293_local_trans;[exact Exit| ].
   eapply V293_local_cons.
   { apply ostc_step;eapply stmt_step;[reflexivity|apply sskip_step]. }
   apply V293_local_refl.
 - split;[exact After| ];split;[exact Target| ];split;[exact Dead| ].
   intros b j A B C D;rewrite Preserved by assumption.
   apply V293_put_byte_other;exact D.
Qed.

(* No kint, call trace, allocation result, store result or returned code is a
   premise. The logical assertion is at the cleared-IR, pushed-stack view;
   it is not silently transported across entry or exint. *)
Theorem V293_interrupt_source_roundtrip :
 forall br bg bp P pc po pi ip T les aus cst interrupted ike interrupted_le ks
 ge M ir i si O op ct R tasks nc entry vector
 f sched_id unmap group rows high y table target nesting lock running saved current counter int_switch
 bt bh bo bn bl brun bc oldhigh oldtarget,
 P=pumerge po pi ->
 get T ct=Some(interrupted,(ike,ks)) ->get les ct=Some interrupted_le ->
 get aus ct=Some((true,si,nil):localst) ->goodks(pc,(po,pi,ip))ks ->
 higherint ir i ->i<INUM ->i=Z.to_nat(Int.unsigned vector) ->
 (0<=Int.unsigned vector<Z.of_nat INUM)%Z ->
 ip i=Some(V293_irq_source_wrapper entry f vector) ->
 P entry=Some(V293_OSIntEnter_function running nesting) ->
 P f=Some(V293_OSIntExit_abstract_function running nesting lock saved table high target current counter sched_id int_switch) ->
 P sched_id=Some(V293_OSSchedNew_function unmap group rows high y) ->
 ~In saved [unmap;group;rows;high;table;target;nesting;lock;running;current] ->
 y<>unmap ->y<>group ->y<>rows ->y<>high ->y<>table ->bh<>bp ->bn<>bt ->
 get ge unmap=Some(bt,Tarray Tint8 256) ->get ge group=Some(bg,Tint8) ->
 get ge rows=Some(br,Tarray Tint8 2) ->get ge high=Some(bh,Tint8) ->
 get ge table=Some(bp,Tarray(Tptr V293_tcb_type)13) ->get ge target=Some(bo,Tptr V293_tcb_type) ->
 get ge nesting=Some(bn,Tint8) ->get ge lock=Some(bl,Tint8) ->
 get ge running=Some(brun,Tint8) ->get ge current=Some(bc,Tint8) ->
 get O abstcblsid=Some(abstcblist tasks) ->V293_current_task tasks ct nc ->
 V293_highest_ready tasks ct ->GoodInvAsrt R ->
 (forall n,n<256 ->load Tint8 M(bt,Z.of_nat n)=Some(V293_byteval(V293_ready_lookup n))) ->
 (ge,emp,M,ir,(false,i::si,nil),O,op)|=SWINVt(V293_ready_inv br bg bp)ct **
 (V293_owned_record_cell((bh,0%Z),Tint8,oldhigh) **
 (V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,oldtarget) **
 (V293_owned_record_cell((bn,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((bl,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval nc) **
 (V293_owned_record_cell((brun,0%Z),Tint8,V293_byteval 1) **R)))))) ->
 exists bs Mf,
 V293_global_steps(pc,(po,pi,ip))cst(T,(ge,les,M,ir,aus),ct)
 (T,(ge,les,Mf,ir,aus),ct) /\
 fresh(V293_put_byte M(bn,0%Z)1)bs /\
 load Tint8 Mf(bn,0%Z)=Some(V293_byteval 0) /\
 load(Tptr V293_tcb_type)Mf(bo,0%Z)=Some(Vptr ct) /\
 (forall k,k<4 ->get Mf(bs,Z.of_nat k)=None) /\
 (forall b j,b<>bs ->b<>bo ->(b,j)<>(bh,0%Z) ->(b,j)<>(bn,0%Z) ->get Mf(b,j)=get M(b,j)).
Proof.
 intros br bg bp P pc po pi ip T les aus cst interrupted ike interrupted_le ks
 ge M ir i si O op ct R tasks nc entry vector
 f sched_id unmap group rows high y table target nesting lock running saved current counter int_switch
 bt bh bo bn bl brun bc oldhigh oldtarget
 Merge Code Env Aux Goodks Higher Range Vector VRange Installed
 Enter Program Scheduler SavedNames YU YG YR YH YT HP NT GU GG GR GH GT GO GN GL GRun GC
 Map Current Highest Good Lookup Held.
 destruct(V293_interrupt_source_calls br bg bp P ge M ir i si O op ct R tasks nc entry
 f sched_id unmap group rows high y table target nesting lock running saved current counter int_switch
 bt bh bo bn bl brun bc oldhigh oldtarget
 Enter Program Scheduler SavedNames YU YG YR YH YT HP NT GU GG GR GH GT GO GN GL GRun GC
 Map Current Highest Good Lookup Held)as(bs&Mf&Fresh&Calls&After&Target&Dead&Frame).
 assert(Clear:ir i=false)by(apply Higher;lia).
 assert(Cleared:isrupd(isrupd ir i true)i false=ir)by(apply V293_interrupt_eoi_restores_ir;exact Clear).
 assert(Prefix:V293_local_steps P
 (curs(V293_irq_source_wrapper entry f vector),(kenil,kstop))
 ((ge,emp,M),isrupd ir i true,(false,i::si,nil))
 (curs(sprim exint),(kenil,kstop))((ge,emp,Mf),ir,(false,i::si,nil))).
 { unfold V293_irq_source_wrapper.
   eapply V293_local_cons.
   { apply ostc_step;eapply stmt_step;[reflexivity|apply sseq_step]. }
   eapply V293_local_cons.
   { eapply eoi_step;[reflexivity|exact Vector|exact VRange]. }
   rewrite Cleared.
   eapply V293_local_cons.
   { apply ostc_step;eapply stmt_step;[reflexivity|apply sskip_step]. }
   exact Calls. }
 rewrite Merge in Prefix.
 pose proof(V293_interrupt_local_steps_global pc po pi ip _ _ _ _ Prefix
 interrupted ike interrupted_le ks T les aus ct cst Goodks)as Lifted.
 assert(Return:V293_global_steps(pc,(po,pi,ip))cst
 (V293_local_global_at T les aus ct
 (curs(sprim exint),(kenil,kint interrupted ike interrupted_le ks))
 ((ge,emp,Mf),ir,(false,i::si,nil)))
 (V293_local_global_at T les aus ct(interrupted,(ike,ks))
 ((ge,interrupted_le,Mf),ir,(true,si,nil)))).
 { apply V293_loststep_global_single.
   - exists(curs(sprim exint));exists kenil;exists(kint interrupted ike interrupted_le ks).
     split;[reflexivity|right;right;discriminate].
   - eapply exint_step;reflexivity. }
 assert(TSame:set T ct(interrupted,(ike,ks))=T)by(exact(TasksMod.get_set_same Code)).
 assert(ESame:set les ct interrupted_le=les)by(exact(CltEnvMod.get_set_same Env)).
 assert(ASame:set aus ct((true,si,nil):localst)=aus)by(exact(TaskLStMod.get_set_same Aux)).
 assert(Nest:load Tint8 Mf(bn,0%Z)=Some(V293_byteval 0)).
 { change(load Tint8(getmem(ge,emp,Mf,ir,(false,i::si,nil),O,op))(bn,0%Z)=Some(V293_byteval 0)).
   eapply V293_record_star_load_r;[ |exact After].
   intros s1 H1;eapply V293_record_star_load_r;[ |exact H1].
   intros s2 H2;eapply V293_record_star_load_r;[ |exact H2].
   intros s3 H3;eapply V293_record_star_load_l;[apply V293_owned_record_cell_load|exact H3]. }
 exists bs;exists Mf;split.
 - unfold V293_global_steps;eapply rt1n_trans with(y:=
     (set T ct(curs(V293_irq_source_wrapper entry f vector),(kenil,kint interrupted ike interrupted_le ks)),
     (ge,set les ct emp,M,isrupd ir i true,set aus ct(false,i::si,nil)),ct)).
   + eapply V293_interrupt_source_enter;[exact Code|exact Env|exact Aux|exact Higher|exact Range|exact Installed].
   + fold(V293_global_steps(pc,(po,pi,ip))cst).
     change(V293_global_steps(pc,(po,pi,ip))cst
       (set T ct(curs(sprim exint),(kenil,kint interrupted ike interrupted_le ks)),
        (ge,set les ct emp,Mf,ir,set aus ct(false,i::si,nil)),ct)
       (set T ct(interrupted,(ike,ks)),
        (ge,set les ct interrupted_le,Mf,ir,set aus ct((true,si,nil):localst)),ct))in Return.
     rewrite TSame,ESame,ASame in Return.
     eapply V293_global_trans;[exact Lifted|exact Return].
 - split;[exact Fresh| ];split;[exact Nest| ];split;[exact Target| ];split;assumption.
Qed.
