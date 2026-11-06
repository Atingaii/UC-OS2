(* Full unequal-path call prefix of the ADR-0005 abstract OSIntExit.
   Stop at the REAL OSIntCtxSw sfexec boundary; no port implementation. *)
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

Require Import CertiOS.certiucos.v293.proofs.V293ReadySourceTail.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPointerCompare.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickCountdown.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
(* The exact unequal source tail. The counter store is constructed from
   ownership. The empty trace and zero-argument call are not erased. *)
Lemma V293_exit_change_to_sfexec : forall P ks ge le M ir aux O op R
 high current counter int_switch bh bc bcount nh nc c,
 nh<256 ->nc<256 ->nh<>nc ->
 get le high=None ->get le current=None ->get le counter=None ->
 get ge high=Some(bh,Tint8) ->get ge current=Some(bc,Tint8) ->get ge counter=Some(bcount,Tint32) ->
 load Tint8 M(bh,0%Z)=Some(V293_byteval nh) ->load Tint8 M(bc,0%Z)=Some(V293_byteval nc) ->
 (ge,le,M,ir,aux,O,op)|=V293_owned_record_cell((bcount,0%Z),Tint32,Vint32 c) **R ->
 exists Mf,
 cstepstar P
 (curs(sif(V293_OSSched_different high current)
   (sseq(V293_OSSched_increment counter)(sseq(sskip None)(scall int_switch nil)))(sskip None)),(kenil,ks))(ge,le,M)
 (curs(sfexec int_switch nil nil),(kenil,ks))(ge,le,Mf) /\
 store Tint32 M(bcount,0%Z)(Vint32(Int.add c Int.one))=Some Mf /\
 (ge,le,Mf,ir,aux,O,op)|=V293_owned_record_cell((bcount,0%Z),Tint32,Vint32(Int.add c Int.one)) **R /\
 (forall b i,b<>bcount \/(i<0)%Z \/(4<=i)%Z ->get Mf(b,i)=get M(b,i)).
Proof.
 intros P ks ge le M ir aux O op R high current counter int_switch bh bc bcount nh nc c
 Nh Nc Different HN CN NN HG CG NG High Cache Held.
 assert(Counter:load Tint32 M(bcount,0%Z)=Some(Vint32 c)).
 { change(load Tint32(getmem(ge,le,M,ir,aux,O,op))(bcount,0%Z)=Some(Vint32 c)).
   eapply V293_record_star_load_l;[apply V293_owned_record_cell_load|exact Held]. }
 destruct(V293_OSSched_byte_comparison_eval ge le M high current bh bc nh nc
 Nh Nc HN CN HG CG High Cache)as[Guard GuardType].
 assert(E:Nat.eqb nh nc=false)by(apply Nat.eqb_neq;exact Different).
 rewrite E in Guard.
 destruct(V293_owned_record_cell_update (bcount,0%Z) Tint32 (Vint32 c)(Vint32(Int.add c Int.one))
 _ _ _ _ _ _ _ _ ltac:(reflexivity) Held)as(Mf&Store&After).
 destruct(V293_ready_counter_eval ge le M counter bcount c NN NG Counter)as(TL&TR&Addr&Value).
 exists Mf;split.
 - eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply sif_step]| ].
   eapply V293_cstepstar_trans;[apply V293_expr_steps;apply evalval_imply_estepstar;exact Guard| ].
   eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply svift_step;reflexivity]| ].
   eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply sseq_step]| ].
   eapply V293_cstepstar_trans.
   { unfold V293_OSSched_increment;eapply V293_tick_assign32_execution with(off:=0%Z);
     try eassumption;try reflexivity;unfold Int.max_unsigned,Int.modulus,Int.wordsize;cbn;lia. }
   eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply sskip_step]| ].
   eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply sseq_step]| ].
   eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply sskip_step]| ].
   eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply snpcall_step]|apply c_stepstar0].
 - split;[exact Store| ];split;[exact After| ].
   intros b i Outside;eapply V293_storebytes_outside;
     [exact Store|cbn[encode_val inj_bytes length];exact Outside].
Qed.


Theorem V293_OSIntExit_switch_entry_execution :
 forall br bg bp P ks ge caller M ir enabled si ci O op ct R tasks nc
 f sched_id unmap group rows high y table target nesting lock running saved current counter int_switch
 bt bh bo bn bl brun bc bcount c oldhigh oldtarget,
 P f=Some(V293_OSIntExit_abstract_function running nesting lock saved table high target current counter sched_id int_switch) ->
 P sched_id=Some(V293_OSSchedNew_function unmap group rows high y) ->
 ~In saved [unmap;group;rows;high;table;target;nesting;lock;running;current;counter] ->
 y<>unmap ->y<>group ->y<>rows ->y<>high ->y<>table ->bh<>bp ->bn<>bt ->
 get ge unmap=Some(bt,Tarray Tint8 256) ->get ge group=Some(bg,Tint8) ->
 get ge rows=Some(br,Tarray Tint8 2) ->get ge high=Some(bh,Tint8) ->
 get ge table=Some(bp,Tarray(Tptr V293_tcb_type)13) ->get ge target=Some(bo,Tptr V293_tcb_type) ->
 get ge nesting=Some(bn,Tint8) ->get ge lock=Some(bl,Tint8) ->
 get ge running=Some(brun,Tint8) ->get ge current=Some(bc,Tint8) ->get ge counter=Some(bcount,Tint32) ->
 get O abstcblsid=Some(abstcblist tasks) ->V293_current_task tasks ct nc ->
 ~V293_highest_ready tasks ct ->GoodInvAsrt R ->
 (forall n,n<256 ->load Tint8 M(bt,Z.of_nat n)=Some(V293_byteval(V293_ready_lookup n))) ->
 (ge,caller,M,ir,(false,si,ci),O,op)|=SWINVt(V293_ready_inv br bg bp)ct **
 (V293_owned_record_cell((bh,0%Z),Tint8,oldhigh) **
 (V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,oldtarget) **
 (V293_owned_record_cell((bn,0%Z),Tint8,V293_byteval 1) **
 (V293_owned_record_cell((bl,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval nc) **
 (V293_owned_record_cell((brun,0%Z),Tint8,V293_byteval 1) **
 (V293_owned_record_cell((bcount,0%Z),Tint32,Vint32 c) **R))))))) ->
 exists bs next nh Mf,fresh M bs /\ next<>ct /\ nh<>nc /\
 V293_highest_ready tasks next /\V293_current_task tasks next nh /\
 V293_local_steps P(curs(scall f nil),(kenil,ks))((ge,caller,M),ir,(enabled,si,ci))
 (curs(sfexec int_switch nil nil),(kenil,
   kseq(sprim excrit)(kseq sret(kcall f
     (V293_OSIntExit_abstract_body running nesting lock saved table high target current counter sched_id int_switch)caller ks))))
 ((ge,V293_cpu_lenv saved bs,Mf),ir,(false,si,enabled::ci)) /\
 (ge,V293_cpu_lenv saved bs,Mf,ir,(false,si,enabled::ci),O,op)|=
 SWINVt(V293_ready_inv br bg bp)ct **
 (V293_owned_record_cell((bh,0%Z),Tint8,V293_byteval nh) **
 (V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,Vptr next) **
 (V293_owned_record_cell((bn,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((bl,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval nc) **
 (V293_owned_record_cell((brun,0%Z),Tint8,V293_byteval 1) **
 (V293_owned_record_cell((bcount,0%Z),Tint32,Vint32(Int.add c Int.one)) **
 (Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **R)))))))) /\
 load(Tptr V293_tcb_type)Mf(bo,0%Z)=Some(Vptr next) /\
 load Tint32 Mf(bcount,0%Z)=Some(Vint32(Int.add c Int.one)) /\
 load Tint8 Mf(bc,0%Z)=Some(V293_byteval nc) /\
 (forall k,k<4 ->exists v,get Mf(bs,Z.of_nat k)=Some(true,v)) /\
 (forall block i,block<>bs ->block<>bo ->(block,i)<>(bh,0%Z) ->(block,i)<>(bn,0%Z) ->
   (block<>bcount \/(i<0)%Z \/(4<=i)%Z) ->get Mf(block,i)=get M(block,i)).
Proof.
 intros br bg bp P ks ge caller M ir enabled si ci O op ct R tasks nc
 f sched_id unmap group rows high y table target nesting lock running saved current counter int_switch
 bt bh bo bn bl brun bc bcount c oldhigh oldtarget
 Program Scheduler SavedNames YU YG YR YH YT HP NT GU GG GR GH GT GO GN GL GRun GC GCount
 Map Current NotHighest Good Lookup Held.
 assert(NC:nc<256)by(destruct Current as[Bound _];lia).
 destruct(V293_ready_fresh_avoiding M [bt;bg;br;bh;bp;bo;bn;bl;brun;bc;bcount])as(bs&Fresh&Away).
 assert(BT:bs<>bt)by(intro E;apply Away;subst;cbn;tauto).
 set(le:=V293_cpu_lenv saved bs).
 assert(Names:forall x,In x [unmap;group;rows;high;table;target;nesting;lock;running;current;counter] ->get le x=None).
 { intros x Member;unfold le,V293_cpu_lenv;rewrite map_get_set'.
   - apply map_emp_get.
   - intro E;apply SavedNames;subst;exact Member. }
 assert(GoodAll:GoodInvAsrt
 (V293_owned_record_cell((bh,0%Z),Tint8,oldhigh) **
 (V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,oldtarget) **
 (V293_owned_record_cell((bn,0%Z),Tint8,V293_byteval 1) **
 (V293_owned_record_cell((bl,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval nc) **
 (V293_owned_record_cell((brun,0%Z),Tint8,V293_byteval 1) **
 (V293_owned_record_cell((bcount,0%Z),Tint32,Vint32 c) **R)))))))).
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
 (V293_owned_record_cell((brun,0%Z),Tint8,V293_byteval 1) **
 (V293_owned_record_cell((bcount,0%Z),Tint32,Vint32 c) **R))))))))).
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
 (V293_owned_record_cell((brun,0%Z),Tint8,V293_byteval 1) **
 (V293_owned_record_cell((bcount,0%Z),Tint32,Vint32 c) **R))))).
 { repeat split;try exact I;exact Good. }
 set(body:=V293_OSIntExit_abstract_body running nesting lock saved table high target current counter sched_id int_switch).
 set(K:=kseq(sprim excrit)(kseq sret(kcall f body caller ks))).
 destruct(V293_OSIntExit_dispatch_prefix_execution br bg bp P K ge le Ms ir(false,si,enabled::ci)O op ct
 (Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **
 (V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval nc) **
 (V293_owned_record_cell((brun,0%Z),Tint8,V293_byteval 1) **
 (V293_owned_record_cell((bcount,0%Z),Tint32,Vint32 c) **R))))
 sched_id unmap group rows high y table target nesting lock current counter int_switch
 bt bh bo bn bl oldhigh oldtarget Scheduler YU YG YR YH YT HP NT GU GG GR GH GT
 (Names high ltac:(cbn;tauto))(Names table ltac:(cbn;tauto))(Names target ltac:(cbn;tauto))GO
 (Names nesting ltac:(cbn;tauto))GN(Names lock ltac:(cbn;tauto))GL GoodFrame LookupS Entry)
 as(ts&lo&hi&entries&next&message&M0&b&My&Mskip&Mmid&Store&FY&FreeY&DeadY&Map'&Rel&Task&Middle&After&TargetLoad&Sched&MidFrame).
 assert(TS:ts=tasks)by congruence;subst ts.
 destruct Sched as(ts'&Map''&NextHighest);assert(TS:ts'=tasks)by congruence;subst ts'.
 destruct Rel as[Lo[Hi[Nonempty[Bitmap Table]]]].
 assert(Next:next<>ct)by(intro E;apply NotHighest;rewrite <-E;exact NextHighest).
 assert(Different:V293_ready_select lo hi(V293_ready_group lo hi)<>nc).
 { intro E;apply Next;apply(proj2(V293_OSSched_current_target lo hi entries tasks ct nc next
     Lo Hi Nonempty Bitmap Table Current NextHighest));exact E. }
 assert(Range:V293_ready_select lo hi(V293_ready_group lo hi)<13)
   by(eapply V293_ready_selection_range;[exact Lo|exact Hi|reflexivity|exact Nonempty]).
 assert(HighLoad:load Tint8 Mmid(bh,0%Z)=Some(V293_byteval(V293_ready_select lo hi(V293_ready_group lo hi)))).
 { eapply V293_record_star_load_l with(s:=(ge,le,Mmid,ir,(false,si,enabled::ci),O,op))
   (P:=V293_owned_record_cell((bh,0%Z),Tint8,V293_byteval(V293_ready_select lo hi(V293_ready_group lo hi))))(Q:=Atrue).
   - intros st H;apply V293_owned_record_cell_load;exact H.
   - clear Held Stacked Local Allocated Entry;sep auto. }
 assert(CurrentLoad:load Tint8 Mmid(bc,0%Z)=Some(V293_byteval nc)).
 { eapply V293_record_star_load_l with(s:=(ge,le,Mmid,ir,(false,si,enabled::ci),O,op))
   (P:=V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval nc))(Q:=Atrue).
   - intros st H;apply V293_owned_record_cell_load;exact H.
   - clear Held Stacked Local Allocated Entry;sep auto. }
 set(F:=SWINVt(V293_ready_inv br bg bp)ct **
 (V293_owned_record_cell((bh,0%Z),Tint8,V293_byteval(V293_ready_select lo hi(V293_ready_group lo hi))) **
 (V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,Vptr next) **
 (V293_owned_record_cell((bn,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((bl,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval nc) **
 (V293_owned_record_cell((brun,0%Z),Tint8,V293_byteval 1) **
 (Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **R)))))))).
 assert(CounterEntry:(ge,le,Mmid,ir,(false,si,enabled::ci),O,op)|=
 V293_owned_record_cell((bcount,0%Z),Tint32,Vint32 c) **F).
 { unfold F;clear Held Stacked Local Allocated Entry;sep auto. }
 destruct(V293_exit_change_to_sfexec P K ge le Mmid ir(false,si,enabled::ci)O op F
 high current counter int_switch bh bc bcount
 (V293_ready_select lo hi(V293_ready_group lo hi))nc c ltac:(lia) NC Different
 (Names high ltac:(cbn;tauto))(Names current ltac:(cbn;tauto))(Names counter ltac:(cbn;tauto))
 GH GC GCount HighLoad CurrentLoad CounterEntry)as(Mf&Tail&CounterStore&Final&CountFrame).
 assert(Post:(ge,le,Mf,ir,(false,si,enabled::ci),O,op)|=
 SWINVt(V293_ready_inv br bg bp)ct **
 (V293_owned_record_cell((bh,0%Z),Tint8,V293_byteval(V293_ready_select lo hi(V293_ready_group lo hi))) **
 (V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,Vptr next) **
 (V293_owned_record_cell((bn,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((bl,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval nc) **
 (V293_owned_record_cell((brun,0%Z),Tint8,V293_byteval 1) **
 (V293_owned_record_cell((bcount,0%Z),Tint32,Vint32(Int.add c Int.one)) **
 (Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **R))))))))).
 { unfold F in Final;clear Held Stacked Local Allocated Entry After CounterEntry;sep auto. }
 exists bs;exists next;exists(V293_ready_select lo hi(V293_ready_group lo hi));exists Mf.
 split;[exact Fresh| ];split;[exact Next| ];split;[exact Different| ];split;[exact NextHighest| ];split.
 { split;[exact Range| ];exists rdy;exists message;exact Task. }
 split.
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
   apply V293_csteps_local;exact Tail.
 - split;[exact Post| ];split.
   + eapply V293_record_star_load_l with(s:=(ge,le,Mf,ir,(false,si,enabled::ci),O,op))
     (P:=V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,Vptr next))(Q:=Atrue).
     * intros st H;apply V293_owned_record_cell_load;exact H.
     * clear Held Stacked Local Allocated Entry After CounterEntry Final;sep auto.
   + split.
     * eapply V293_record_star_load_l with(s:=(ge,le,Mf,ir,(false,si,enabled::ci),O,op))
       (P:=V293_owned_record_cell((bcount,0%Z),Tint32,Vint32(Int.add c Int.one)))(Q:=F).
       -- intros st H;apply V293_owned_record_cell_load;exact H.
       -- exact Final.
     * split.
       -- eapply V293_record_star_load_l with(s:=(ge,le,Mf,ir,(false,si,enabled::ci),O,op))
          (P:=V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval nc))(Q:=Atrue).
          ++ intros st H;apply V293_owned_record_cell_load;exact H.
          ++ clear Held Stacked Local Allocated Entry After CounterEntry Final;sep auto.
       -- split.
          ++ assert(SavedCell:(ge,le,Mf,ir,(false,si,enabled::ci),O,op)|=Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **Atrue).
             { clear Held Stacked Local Allocated Entry After CounterEntry Final;sep auto. }
             intros k Bound.
             pose proof(V293_tick_raw_owned_writable bs Tint32 (Vint32 Int.zero) _ _ _ _ _ _ _ _ SavedCell)as W.
             apply W;cbn;lia.
          ++ intros block i NS NO NH NN Outside;rewrite CountFrame by exact Outside.
             rewrite MidFrame by assumption;apply InitFrame;exact NS.
Qed.
