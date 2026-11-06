(* Complete same-task call of the explicit ADR-0005 abstract function.
   Spatial pre/post use a disabled-IE logical view; the actual trace restores
   arbitrary IE and its existing critical stack. No production ISR closure. *)
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitDispatchExecution.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitCallExecution.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyFullCall.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCriticalGlobal.
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
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.code.V293OSIntExit.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.code.V293OSIntEnter.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Lemma V293_exit_same_priority_skip : forall P ks ge le M high current bh bc nc yes,
 nc<256 ->get le high=None ->get le current=None ->
 get ge high=Some(bh,Tint8) ->get ge current=Some(bc,Tint8) ->
 load Tint8 M(bh,0%Z)=Some(V293_byteval nc) ->
 load Tint8 M(bc,0%Z)=Some(V293_byteval nc) ->
 cstepstar P(curs(sif(V293_OSSched_different high current)yes(sskip None)),(kenil,ks))(ge,le,M)
 (curs(sskip None),(kenil,ks))(ge,le,M).
Proof.
 intros P ks ge le M high current bh bc nc yes Bound HN CN HG CG High Current.
 pose proof(V293_byte_variable (V293_target_wstate ge le M emp) high bh nc HG HN High)as[Eh Th].
 pose proof(V293_byte_variable (V293_target_wstate ge le M emp) current bc nc CG CN Current)as[Ec Tc].
 assert(Eval:evalval(V293_OSSched_different high current)(ge,le,M)=Some(Vint32 Int.zero)).
 { unfold V293_OSSched_different.
   cbn[V293_target_wstate getsmem get_smem evalval evaltype]in Eh,Th,Ec,Tc|-*.
   rewrite Eh,Ec,Th,Tc. unfold V293_byteval;cbn[bop_eval bop_type val_eq].
   rewrite V293_byte_eq by lia. rewrite Nat.eqb_refl;reflexivity. }
 eapply c_stepstarn;[eapply stmt_step;[reflexivity|constructor]| ].
 eapply V293_cstepstar_trans;[apply V293_expr_steps;apply evalval_imply_estepstar;exact Eval| ].
 eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply sviff_step;reflexivity]|apply c_stepstar0].
Qed.

(* Current is already highest ready in the SAME task map. This is a semantic
   path precondition, not a premise supplying any execution or comparison. *)
Theorem V293_OSIntExit_same_task_call_execution :
 forall br bg bp P ks ge caller M ir enabled si ci O op ct R tasks nc
 f sched_id unmap group rows high y table target nesting lock running saved current counter int_switch
 bt bh bo bn bl brun bc oldhigh oldtarget,
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
 (ge,caller,M,ir,(false,si,ci),O,op)|=SWINVt(V293_ready_inv br bg bp)ct **
 (V293_owned_record_cell((bh,0%Z),Tint8,oldhigh) **
 (V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,oldtarget) **
 (V293_owned_record_cell((bn,0%Z),Tint8,V293_byteval 1) **
 (V293_owned_record_cell((bl,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval nc) **
 (V293_owned_record_cell((brun,0%Z),Tint8,V293_byteval 1) **R)))))) ->
 exists bs Mf,fresh M bs /\
 V293_local_steps P(curs(scall f nil),(kenil,ks))((ge,caller,M),ir,(enabled,si,ci))
 (curs(sskip None),(kenil,ks))((ge,caller,Mf),ir,(enabled,si,ci)) /\
 (ge,caller,Mf,ir,(false,si,ci),O,op)|=SWINVt(V293_ready_inv br bg bp)ct **
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
 intros br bg bp P ks ge caller M ir enabled si ci O op ct R tasks nc
 f sched_id unmap group rows high y table target nesting lock running saved current counter int_switch
 bt bh bo bn bl brun bc oldhigh oldtarget
 Program Scheduler SavedNames YU YG YR YH YT HP NT GU GG GR GH GT GO GN GL GRun GC
 Map Current Highest Good Lookup Held.
 assert(NC:nc<256)by(destruct Current as[Bound _];lia).
 destruct(V293_ready_fresh_avoiding M [bt;bg;br;bh;bp;bo;bn;bl;brun;bc])as(bs&Fresh&Away).
 assert(BT:bs<>bt)by(intro E;apply Away;subst;cbn;tauto).
 set(le:=V293_cpu_lenv saved bs).
 assert(Names:forall x,In x [unmap;group;rows;high;table;target;nesting;lock;running;current] ->get le x=None).
 { intros x Member;unfold le,V293_cpu_lenv;rewrite map_get_set'.
   - apply map_emp_get.
   - intro E;apply SavedNames;subst;exact Member. }
 assert(GoodAll:GoodInvAsrt
 (V293_owned_record_cell((bh,0%Z),Tint8,oldhigh) **
 (V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,oldtarget) **
 (V293_owned_record_cell((bn,0%Z),Tint8,V293_byteval 1) **
 (V293_owned_record_cell((bl,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval nc) **
 (V293_owned_record_cell((brun,0%Z),Tint8,V293_byteval 1) **R))))))).
 { repeat split;try exact I;exact Good. }
 pose proof(V293_ready_critical_stack br bg bp ct _ ge caller M ir si ci(enabled::ci)O op GoodAll Held)as Stacked.
 pose proof(V293_ready_lenv_frame br bg bp ct _ ge caller M ir(false,si,enabled::ci)O op le GoodAll Stacked)as Local.
 destruct(V293_success_scheduler_storage M bs Fresh)as(Ms&Init&Writable&InitialFree&InitFrame).
 pose proof(V293_cpu_initialized_frame ge le M ir(false,si,enabled::ci)O op bs Ms _ Fresh Local Init)as Allocated.
 assert(Entry:(ge,le,Ms,ir,(false,si,enabled::ci),O,op)|=SWINVt(V293_ready_inv br bg bp)ct **
 (V293_owned_record_cell((bh,0%Z),Tint8,oldhigh) **
 (V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,oldtarget) **
 (V293_owned_record_cell((bn,0%Z),Tint8,V293_byteval 1) **
 (V293_owned_record_cell((bl,0%Z),Tint8,V293_byteval 0) **
 (Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **
 (V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval nc) **
 (V293_owned_record_cell((brun,0%Z),Tint8,V293_byteval 1) **R)))))))).
 { clear Held Stacked Local;sep auto. }
 assert(Run:load Tint8 Ms(brun,0%Z)=Some(V293_byteval 1)).
 { eapply V293_record_star_load_l with(s:=(ge,le,Ms,ir,(false,si,enabled::ci),O,op))
   (P:=V293_owned_record_cell((brun,0%Z),Tint8,V293_byteval 1))(Q:=Atrue).
   - intros st H;apply V293_owned_record_cell_load;exact H.
   - clear Held Stacked Local Allocated;sep auto. }
 assert(LookupS:forall n,n<256 ->load Tint8 Ms(bt,Z.of_nat n)=Some(V293_byteval(V293_ready_lookup n))).
 { intros n N;etransitivity;[apply V293_load_block_frame;intro i;apply InitFrame;congruence|apply Lookup;exact N]. }
 assert(GoodFrame:GoodInvAsrt(Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **
 (V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval nc) **
 (V293_owned_record_cell((brun,0%Z),Tint8,V293_byteval 1) **R)))).
 { repeat split;try exact I;exact Good. }
 set(body:=V293_OSIntExit_abstract_body running nesting lock saved table high target current counter sched_id int_switch).
 set(K:=kseq(sprim excrit)(kseq sret(kcall f body caller ks))).
 destruct(V293_OSIntExit_dispatch_prefix_execution br bg bp P K ge le Ms ir(false,si,enabled::ci)O op ct
 (Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **
 (V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval nc) **
 (V293_owned_record_cell((brun,0%Z),Tint8,V293_byteval 1) **R)))
 sched_id unmap group rows high y table target nesting lock current counter int_switch
 bt bh bo bn bl oldhigh oldtarget Scheduler YU YG YR YH YT HP NT GU GG GR GH GT
 (Names high ltac:(cbn;tauto))(Names table ltac:(cbn;tauto))(Names target ltac:(cbn;tauto))GO
 (Names nesting ltac:(cbn;tauto))GN(Names lock ltac:(cbn;tauto))GL GoodFrame LookupS Entry)
 as(ts&lo&hi&entries&next&message&M0&b&My&Mskip&Mmid&Store&FY&FreeY&DeadY&Map'&Rel&Task&Middle&After&TargetLoad&Sched&MidFrame).
 assert(TS:ts=tasks)by congruence;subst ts.
 destruct Sched as(ts'&Map''&NextHighest);assert(TS:ts'=tasks)by congruence;subst ts'.
 destruct Rel as[Lo[Hi[Nonempty[Bitmap Table]]]].
 assert(Next:next=ct)by(eapply V293_highest_unique;[exact Table|exact NextHighest|exact Highest]).
 assert(Selected:V293_ready_select lo hi(V293_ready_group lo hi)=nc).
 { apply(proj1(V293_OSSched_current_target lo hi entries tasks ct nc next Lo Hi Nonempty Bitmap Table Current NextHighest));exact Next. }
 rewrite Selected,Next in After.
 assert(HighLoad:load Tint8 Mmid(bh,0%Z)=Some(V293_byteval nc)).
 { eapply V293_record_star_load_l with(s:=(ge,le,Mmid,ir,(false,si,enabled::ci),O,op))
   (P:=V293_owned_record_cell((bh,0%Z),Tint8,V293_byteval nc))(Q:=Atrue).
   - intros st H;apply V293_owned_record_cell_load;exact H.
   - clear Held Stacked Local Allocated Entry;sep auto. }
 assert(CurrentLoad:load Tint8 Mmid(bc,0%Z)=Some(V293_byteval nc)).
 { eapply V293_record_star_load_l with(s:=(ge,le,Mmid,ir,(false,si,enabled::ci),O,op))
   (P:=V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval nc))(Q:=Atrue).
   - intros st H;apply V293_owned_record_cell_load;exact H.
   - clear Held Stacked Local Allocated Entry;sep auto. }
 assert(Release:(ge,le,Mmid,ir,(false,si,enabled::ci),O,op)|=Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **
 (SWINVt(V293_ready_inv br bg bp)ct **
 (V293_owned_record_cell((bh,0%Z),Tint8,V293_byteval nc) **
 (V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,Vptr ct) **
 (V293_owned_record_cell((bn,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((bl,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval nc) **
 (V293_owned_record_cell((brun,0%Z),Tint8,V293_byteval 1) **R)))))))).
 { clear Held Stacked Local Allocated Entry;sep auto. }
 destruct(V293_cpu_release _ _ _ _ _ _ _ _ _ _ Release)as(Mf&Free&Post&Removed&FreeFrame).
 assert(Caller:(ge,caller,Mf,ir,(false,si,ci),O,op)|=SWINVt(V293_ready_inv br bg bp)ct **
 (V293_owned_record_cell((bh,0%Z),Tint8,V293_byteval nc) **
 (V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,Vptr ct) **
 (V293_owned_record_cell((bn,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((bl,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval nc) **
 (V293_owned_record_cell((brun,0%Z),Tint8,V293_byteval 1) **R))))))).
 { eapply V293_ready_critical_stack;[repeat split;try exact I;exact Good| ].
   eapply V293_ready_lenv_frame;[repeat split;try exact I;exact Good|exact Post]. }
 exists bs;exists Mf;split;[exact Fresh| ];split.
 - eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply snpcall_step]| ].
   eapply V293_local_cons.
   { apply ostc_step;eapply stmt_step;[reflexivity| ];eapply sfexec_step with(d1:=dnil)(d2:=dcons saved Tint32 dnil);
     [reflexivity|reflexivity|exact Program|exact I|reflexivity]. }
   eapply V293_local_cons.
   { apply ostc_step;eapply stmt_step;[reflexivity| ];eapply salloclv_step;[reflexivity|reflexivity| ].
     exists bs;split;[exact Fresh| ];split;[reflexivity| ];split;[intros[v E];rewrite map_emp_get in E;discriminate|reflexivity]. }
   eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sallocend_step]| ].
   unfold V293_OSIntExit_abstract_body.
   eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sseq_step]| ].
   eapply V293_local_trans.
   { apply V293_csteps_local;eapply V293_success_assign_zero;[unfold le,V293_cpu_lenv;apply map_get_set|exact Init]. }
   eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sskip_step]| ].
   eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sseq_step]| ].
   eapply V293_local_trans.
   { apply V293_csteps_local;eapply V293_entry_if_select with(flag:=true).
     unfold V293_OSIntEnter_running;change Int.one with(Int.repr(Z.of_nat 1)).
     exact(V293_success_global_byte_eq ge le Ms running brun 1 1 ltac:(lia)ltac:(lia)
       (Names running ltac:(cbn;tauto))GRun Run). }
   eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sseq_step]| ].
   eapply V293_local_cons;[apply encrit_step;reflexivity| ].
   eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sskip_step]| ].
   eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sseq_step]| ].
   eapply V293_local_trans;[apply V293_csteps_local;exact Middle| ].
   eapply V293_local_trans.
   { apply V293_csteps_local.
     exact(V293_exit_same_priority_skip P K ge le Mmid high current bh bc nc
       (sseq(V293_OSSched_increment counter)(sseq(sskip None)(scall int_switch nil)))
       NC (Names high ltac:(cbn;tauto))(Names current ltac:(cbn;tauto)) GH GC HighLoad CurrentLoad). }
   eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sskip_step]| ].
   eapply V293_local_cons;[apply excrit_step;reflexivity| ].
   eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sskip_step]| ].
   apply V293_sched_call_return;exact Free.
 - split;[exact Caller| ];split.
   + eapply V293_record_star_load_l with(s:=(ge,caller,Mf,ir,(false,si,ci),O,op))
     (P:=V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,Vptr ct))(Q:=Atrue).
     * intros st H;apply V293_owned_record_cell_load;exact H.
     * clear Held Stacked Local Allocated Entry After Post;sep auto.
   + split;[intros k K';apply Removed;cbn;lia| ].
     intros c i NS NO NH NN;rewrite FreeFrame by exact NS.
     rewrite MidFrame by assumption;apply InitFrame;exact NS.
Qed.
