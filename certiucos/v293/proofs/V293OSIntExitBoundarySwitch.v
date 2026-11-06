(* Explicit SOURCE-LEVEL interrupt-switch boundary, not a CPU-port body.
   Original call model and original framework semantics remain unchanged. *)
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
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitInterruptGlobal.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCacheContract.
Require Import Coq.Relations.Relation_Operators.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.framework.proof.join_prop.
Require Import CertiOS.tactics.basetac.join_lib.
Require Import CertiOS.certiucos.v293.proofs.V293ReadySwitchStep.
Require Import CertiOS.certiucos.v293.proofs.V293LocalGlobalTrace.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyGlobalTrace.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCallGlobal.
Require Import CertiOS.certiucos.v293.code.V293OSSchedDispatch.
Require Import CertiOS.certiucos.v293.code.V293OSSchedGuards.

(* One explicit interpretation of the accepted source-level port boundary.
   This is NOT a proof about execution of the raw external declaration. *)
Definition V293_interrupt_handoff high current target :=
 sseq(sassign(evar current)(evar high))(sprim(switch target)).
Definition V293_exit_boundary_dispatch table high target current counter sched handoff :=
 sseq(V293_OSSched_unlocked_prefix sched table high target)
 (sif(V293_OSSched_different high current)
 (sseq(V293_OSSched_increment counter)(sseq(sskip None)handoff))(sskip None)).
Definition V293_exit_boundary_body running nesting lock saved table high target current counter sched handoff :=
 sseq(sassign(evar saved)(econst32 Int.zero))
 (sseq(sifthen(V293_OSIntEnter_running running)
 (sseq(sprim encrit)(sseq(V293_OSIntExit_nesting_dispatch nesting lock
 (V293_exit_boundary_dispatch table high target current counter sched handoff))(sprim excrit))))sret).
Definition V293_exit_boundary_function running nesting lock saved table high target current counter sched handoff : function :=
 (Tvoid,dnil,dcons saved Tint32 dnil,
 V293_exit_boundary_body running nesting lock saved table high target current counter sched handoff).

(* Syntactic call-site interpretation only. No global substitution of
   sfexec and no external function implementation is installed. *)
Fixpoint V293_intswitch_calls (port:fid)(replacement:stmts)(s:stmts):option stmts :=
 match s with
 | scall f args =>if Z.eq_dec f port then match args with nil=>Some replacement | _=>None end else Some s
 | scalle _ f _ =>if Z.eq_dec f port then None else Some s
 | sseq a b =>match V293_intswitch_calls port replacement a,V293_intswitch_calls port replacement b with
   Some a',Some b'=>Some(sseq a' b') |_,_=>None end
 | sif e a b =>match V293_intswitch_calls port replacement a,V293_intswitch_calls port replacement b with
   Some a',Some b'=>Some(sif e a' b') |_,_=>None end
 | sifthen e a =>match V293_intswitch_calls port replacement a with Some a'=>Some(sifthen e a') |_=>None end
 | swhile e a =>match V293_intswitch_calls port replacement a with Some a'=>Some(swhile e a') |_=>None end
 | sfexec _ _ _ | salloc _ _ | sfree _ _ =>None
 | _=>Some s
 end.
Theorem V293_OSIntExit_boundary_normalization :
 forall running nesting lock saved table high target current counter sched enter exit port,
 enter<>exit ->sched<>enter ->sched<>exit ->port<>enter ->port<>exit ->sched<>port ->
 (match V293_port_normalize enter exit saved
 (V293_OSIntExit_body running nesting lock saved table high target current counter sched enter exit port) with
 |Some s=>V293_intswitch_calls port(V293_interrupt_handoff high current target)s |None=>None end)=
 Some(V293_exit_boundary_body running nesting lock saved table high target current counter sched
 (V293_interrupt_handoff high current target)).
Proof.
 intros;rewrite V293_OSIntExit_abstract_normalization by assumption.
 unfold V293_OSIntExit_abstract_body,V293_exit_boundary_body,
 V293_OSIntExit_nesting_dispatch,V293_OSIntExit_decrement,V293_OSIntExit_guards,
 V293_OSIntExit_dispatch,V293_exit_boundary_dispatch,V293_OSSched_unlocked_prefix.
 cbn[V293_intswitch_calls];repeat destruct(Z.eq_dec _ _);intuition congruence.
Qed.

Theorem V293_exit_boundary_dispatch_prefix :
 forall br bg bp P ks ge le M ir aux O op ct R
 f unmap group rows high y table target nesting lock current counter handoff
 bt bh bo bn bl oldhigh oldtarget,
 P f=Some(V293_OSSchedNew_function unmap group rows high y) ->
 y<>unmap -> y<>group -> y<>rows -> y<>high -> y<>table -> bh<>bp -> bn<>bt ->
 get ge unmap=Some(bt,Tarray Tint8 256) ->
 get ge group=Some(bg,Tint8) -> get ge rows=Some(br,Tarray Tint8 2) ->
 get ge high=Some(bh,Tint8) -> get ge table=Some(bp,Tarray(Tptr V293_tcb_type)13) ->
 get le high=None -> get le table=None -> get le target=None ->
 get ge target=Some(bo,Tptr V293_tcb_type) ->
 get le nesting=None -> get ge nesting=Some(bn,Tint8) ->
 get le lock=None -> get ge lock=Some(bl,Tint8) -> GoodInvAsrt R ->
 (forall n,n<256 ->load Tint8 M(bt,Z.of_nat n)=Some(V293_byteval(V293_ready_lookup n))) ->
 (ge,le,M,ir,aux,O,op)|=SWINVt(V293_ready_inv br bg bp)ct **
 (V293_owned_record_cell((bh,0%Z),Tint8,oldhigh) **
 (V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,oldtarget) **
 (V293_owned_record_cell((bn,0%Z),Tint8,V293_byteval 1) **
 (V293_owned_record_cell((bl,0%Z),Tint8,V293_byteval 0) ** R)))) ->
 exists tasks, exists lo, exists hi, exists entries, exists next, exists message,
 exists M0, exists b, exists Ms, exists Mskip, exists Mf,
 store Tint8 M(bn,0%Z)(V293_byteval 0)=Some M0 /\
 fresh M0 b /\ free Tint8 b Ms=Some Mskip /\ get Mskip(b,0%Z)=None /\
 get O abstcblsid=Some(abstcblist tasks) /\ V293_ready_rel lo hi entries tasks /\
 get tasks next=Some(Int.repr(Z.of_nat(V293_ready_select lo hi(V293_ready_group lo hi))),rdy,message) /\
 cstepstar P
 (curs(V293_OSIntExit_nesting_dispatch nesting lock
   (V293_exit_boundary_dispatch table high target current counter f handoff)),(kenil,ks))(ge,le,M)
 (curs(sif(V293_OSSched_different high current)
   (sseq(V293_OSSched_increment counter)(sseq(sskip None)handoff))
   (sskip None)),(kenil,ks))(ge,le,Mf) /\
 (ge,le,Mf,ir,aux,O,op)|=SWINVt(V293_ready_inv br bg bp)ct **
 (V293_owned_record_cell((bh,0%Z),Tint8,V293_byteval(V293_ready_select lo hi(V293_ready_group lo hi))) **
 (V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,Vptr next) **
 (V293_owned_record_cell((bn,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((bl,0%Z),Tint8,V293_byteval 0) ** R)))) /\
 load(Tptr V293_tcb_type)Mf(bo,0%Z)=Some(Vptr next) /\ V293_scheduler O next /\
 (forall c i,c<>bo ->(c,i)<>(bh,0%Z) ->(c,i)<>(bn,0%Z) ->get Mf(c,i)=get M(c,i)).
Proof.
 intros br bg bp P ks ge le M ir aux O op ct R f unmap group rows high y table target
 nesting lock current counter handoff bt bh bo bn bl oldhigh oldtarget
 Program YU YG YR YH YT HP NT GU GG GR GH GT NH NL NO GO NN GN NK GK Good Lookup Held.
 assert(NestHeld:(ge,le,M,ir,aux,O,op)|=V293_owned_record_cell((bn,0%Z),Tint8,V293_byteval 1) **
 (SWINVt(V293_ready_inv br bg bp)ct **(V293_owned_record_cell((bh,0%Z),Tint8,oldhigh) **
 (V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,oldtarget) **
 (V293_owned_record_cell((bl,0%Z),Tint8,V293_byteval 0) **R))))) by(sep auto).
 assert(Nest:load Tint8 M(bn,0%Z)=Some(V293_byteval 1)).
 { eapply V293_record_star_load_l with(s:=(ge,le,M,ir,aux,O,op));
   [intros st H;apply V293_owned_record_cell_load;exact H |exact NestHeld]. }
 destruct(V293_owned_record_cell_update _ Tint8 _ (V293_byteval 0) _ _ _ _ _ _ _ _ eq_refl NestHeld)
 as(M0&Store&Updated).
 assert(Ready:(ge,le,M0,ir,aux,O,op)|=SWINVt(V293_ready_inv br bg bp)ct **
 (V293_owned_record_cell((bh,0%Z),Tint8,oldhigh) **
 (V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,oldtarget) **
 (V293_owned_record_cell((bn,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((bl,0%Z),Tint8,V293_byteval 0) **R))))) by(clear Held NestHeld;sep auto).
 assert(Lock:load Tint8 M0(bl,0%Z)=Some(V293_byteval 0)).
 { eapply V293_record_star_load_l with(s:=(ge,le,M0,ir,aux,O,op))
   (P:=V293_owned_record_cell((bl,0%Z),Tint8,V293_byteval 0))(Q:=Atrue).
   - intros st H;apply V293_owned_record_cell_load;exact H.
   - clear Held NestHeld Updated;sep auto. }
 assert(Lookup0:forall n,n<256 ->load Tint8 M0(bt,Z.of_nat n)=Some(V293_byteval(V293_ready_lookup n))).
 { intros n Bound;etransitivity;[eapply V293_load_block_frame |apply Lookup;exact Bound].
   intros i;eapply V293_storebytes_outside;[exact Store |left;congruence]. }
 assert(FrameGood:GoodInvAsrt(V293_owned_record_cell((bn,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((bl,0%Z),Tint8,V293_byteval 0) **R))).
 { repeat split;try exact I;exact Good. }
 set(tail:=sif(V293_OSSched_different high current)
 (sseq(V293_OSSched_increment counter)(sseq(sskip None)handoff))(sskip None)).
 destruct(V293_ready_dispatch_call br bg bp P(kseq tail ks)ge le M0 ir aux O op ct
 (V293_owned_record_cell((bn,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((bl,0%Z),Tint8,V293_byteval 0) **R))
 f unmap group rows high y table target bt bh bo oldhigh oldtarget
 Program YU YG YR YH YT HP GU GG GR GH GT NH NL NO GO FrameGood Lookup0 Ready)
 as(tasks&lo&hi&entries&next&message&b&Ms&Mskip&Mf&Fresh&Map&Rel&Task&Call&Skipped&Free&Removed&High&Exec&TargetStore&After&TargetLoad&Sched&Pre&Live&Dead&CallFrame&TargetFrame).
 exists tasks;exists lo;exists hi;exists entries;exists next;exists message;
 exists M0;exists b;exists Ms;exists Mskip;exists Mf.
 split;[exact Store | ]. split;[exact Fresh | ]. split;[exact Free | ]. split;[exact Removed | ].
 split;[exact Map | ]. split;[exact Rel | ]. split;[exact Task | ]. split.
 - unfold V293_OSIntExit_nesting_dispatch.
   eapply c_stepstarn;[eapply stmt_step;[reflexivity |apply sseq_step] | ].
   eapply V293_cstepstar_trans;[eapply V293_exit_one_decrement_execution;eassumption | ].
   eapply c_stepstarn;[eapply stmt_step;[reflexivity |apply sskip_step] | ].
   eapply V293_cstepstar_trans.
   { eapply V293_exit_zero_guards_enter;try eassumption.
     eapply V293_exit_byte_readback;[lia |exact Store]. }
   unfold V293_exit_boundary_dispatch;fold tail.
   eapply c_stepstarn;[eapply stmt_step;[reflexivity |apply sseq_step] | ].
   eapply V293_cstepstar_trans;[exact Exec | ].
   eapply c_stepstarn;[eapply stmt_step;[reflexivity |apply sskip_step] | ].
   apply c_stepstar0.
 - split;[exact After | ]. split;[exact TargetLoad | ]. split;[exact Sched | ].
   intros c i NotTarget NotHigh NotNest.
   rewrite TargetFrame by(left;exact NotTarget).
   rewrite CallFrame by exact NotHigh.
   eapply V293_storebytes_outside;[exact Store | ].
   destruct(Pos.eq_dec c bn) as[E |E].
   + subst c;right;cbn. assert(i<>0%Z)by(congruence). lia.
   + left;exact E.
Qed.

Lemma V293_exit_boundary_tail : forall P ks ge le M ir aux O op R
 high current counter handoff bh bc bcount nh nc c,
 nh<256 ->nc<256 ->nh<>nc ->
 get le high=None ->get le current=None ->get le counter=None ->
 get ge high=Some(bh,Tint8) ->get ge current=Some(bc,Tint8) ->get ge counter=Some(bcount,Tint32) ->
 load Tint8 M(bh,0%Z)=Some(V293_byteval nh) ->load Tint8 M(bc,0%Z)=Some(V293_byteval nc) ->
 (ge,le,M,ir,aux,O,op)|=V293_owned_record_cell((bcount,0%Z),Tint32,Vint32 c) **R ->
 exists Mf,
 cstepstar P
 (curs(sif(V293_OSSched_different high current)
   (sseq(V293_OSSched_increment counter)(sseq(sskip None)handoff))(sskip None)),(kenil,ks))(ge,le,M)
 (curs handoff,(kenil,ks))(ge,le,Mf) /\
 store Tint32 M(bcount,0%Z)(Vint32(Int.add c Int.one))=Some Mf /\
 (ge,le,Mf,ir,aux,O,op)|=V293_owned_record_cell((bcount,0%Z),Tint32,Vint32(Int.add c Int.one)) **R /\
 (forall b i,b<>bcount \/(i<0)%Z \/(4<=i)%Z ->get Mf(b,i)=get M(b,i)).
Proof.
 intros P ks ge le M ir aux O op R high current counter handoff bh bc bcount nh nc c
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
   apply c_stepstar0.
 - split;[exact Store| ];split;[exact After| ].
   intros b i Outside;eapply V293_storebytes_outside;
     [exact Store|cbn[encode_val inj_bytes length];exact Outside].
Qed.



Theorem V293_exit_boundary_entry_local :
 forall br bg bp P ks ge caller M ir enabled si ci O op ct R tasks nc
 f sched_id unmap group rows high y table target nesting lock running saved current counter handoff
 bt bh bo bn bl brun bc bcount c oldhigh oldtarget,
 P f=Some(V293_exit_boundary_function running nesting lock saved table high target current counter sched_id handoff) ->
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
 (curs handoff,(kenil,
   kseq(sprim excrit)(kseq sret(kcall f
     (V293_exit_boundary_body running nesting lock saved table high target current counter sched_id handoff)caller ks))))
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
 f sched_id unmap group rows high y table target nesting lock running saved current counter handoff
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
 set(body:=V293_exit_boundary_body running nesting lock saved table high target current counter sched_id handoff).
 set(K:=kseq(sprim excrit)(kseq sret(kcall f body caller ks))).
 destruct(V293_exit_boundary_dispatch_prefix br bg bp P K ge le Ms ir(false,si,enabled::ci)O op ct
 (Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **
 (V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval nc) **
 (V293_owned_record_cell((brun,0%Z),Tint8,V293_byteval 1) **
 (V293_owned_record_cell((bcount,0%Z),Tint32,Vint32 c) **R))))
 sched_id unmap group rows high y table target nesting lock current counter handoff
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
 destruct(V293_exit_boundary_tail P K ge le Mmid ir(false,si,enabled::ci)O op F
 high current counter handoff bh bc bcount
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
   unfold V293_exit_boundary_body.
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

Theorem V293_exit_boundary_entry_global :
 forall br bg bp P ks pc po pi ip T les aus cst interrupted ike interrupted_le ge caller M ir enabled si ci O op ct R tasks nc
 f sched_id unmap group rows high y table target nesting lock running saved current counter handoff
 bt bh bo bn bl brun bc bcount c oldhigh oldtarget,
 P=pumerge po pi ->
 get T ct=Some(curs(scall f nil),(kenil,kint interrupted ike interrupted_le ks)) ->
 get les ct=Some caller ->get aus ct=Some(enabled,si,ci) ->
 goodks(pc,(po,pi,ip))ks ->
 P f=Some(V293_exit_boundary_function running nesting lock saved table high target current counter sched_id handoff) ->
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
 V293_global_steps(pc,(po,pi,ip))cst
 (T,(ge,les,M,ir,aus),ct)
 (set T ct(curs handoff,(kenil,
   kseq(sprim excrit)(kseq sret(kcall f
     (V293_exit_boundary_body running nesting lock saved table high target current counter sched_id handoff)
       caller(kint interrupted ike interrupted_le ks))))),
  (ge,set les ct(V293_cpu_lenv saved bs),Mf,ir,set aus ct(false,si,enabled::ci)),ct) /\
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
 intros br bg bp P ks pc po pi ip T les aus cst interrupted ike interrupted_le ge caller M ir enabled si ci O op ct R tasks nc
 f sched_id unmap group rows high y table target nesting lock running saved current counter handoff
 bt bh bo bn bl brun bc bcount c oldhigh oldtarget
 Merge Code Env Aux GoodKs Program Scheduler Names YU YG YR YH YT HP NT
 GU GG GR GH GT GO GN GL GRun GC GCount Map Current NotHighest Good Lookup Held.
 subst P.
 destruct(V293_exit_boundary_entry_local br bg bp(pumerge po pi)kstop
 ge caller M ir enabled si ci O op ct R tasks nc
 f sched_id unmap group rows high y table target nesting lock running saved current counter handoff
 bt bh bo bn bl brun bc bcount c oldhigh oldtarget
 Program Scheduler Names YU YG YR YH YT HP NT
 GU GG GR GH GT GO GN GL GRun GC GCount Map Current NotHighest Good Lookup Held)
 as(bs&next&nh&Mf&Fresh&Different&PrioDifferent&Highest&Next&Trace&Post&Target&Count&Cache&Alive&Frame).
 pose proof(V293_interrupt_local_steps_global pc po pi ip _ _ _ _ Trace
 interrupted ike interrupted_le ks T les aus ct cst GoodKs)as Global.
 cbn[V293_enclose AddKsToTail]in Global.
 cbn[V293_local_global_at V293_global_at]in Global.
 assert(TStart:set T ct(curs(scall f nil),(kenil,kint interrupted ike interrupted_le ks))=T)
 by(apply get_set_same;exact Code).
 assert(EStart:set les ct caller=les)by(apply get_set_same;exact Env).
 assert(AStart:set aus ct(enabled,si,ci)=aus)by(apply get_set_same;exact Aux).
 assert(Start:(set T ct(curs(scall f nil),(kenil,kint interrupted ike interrupted_le ks)),
 (ge,set les ct caller,M,ir,set aus ct(enabled,si,ci)),ct)=(T,(ge,les,M,ir,aus),ct)).
 { rewrite TStart,EStart,AStart;reflexivity. }
 replace (T,(ge,les,M,ir,aus),ct) with
 (set T ct(curs(scall f nil),(kenil,kint interrupted ike interrupted_le ks)),
 (ge,set les ct caller,M,ir,set aus ct(enabled,si,ci)),ct) by exact Start.

 exists bs;exists next;exists nh;exists Mf;repeat first[assumption|split].
Qed.


(* This resource-level command proof is used below after the complete call
   prefix. Store existence follows from ownership, never an execution oracle. *)
Lemma V293_handoff_copy_execution : forall br bg bp P ks ge le M ir aux O op ct R
 high current target bh bc bo nh cached next,
 nh<256 ->get le high=None ->get le current=None ->
 get ge high=Some(bh,Tint8) ->get ge current=Some(bc,Tint8) ->
 (ge,le,M,ir,aux,O,op)|=SWINVt(V293_ready_inv br bg bp)ct **
 (V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval cached) **
 (V293_owned_record_cell((bh,0%Z),Tint8,V293_byteval nh) **
 (V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,Vptr next) **R))) ->
 exists Ms,
 cstepstar P(curs(V293_interrupt_handoff high current target),(kenil,ks))(ge,le,M)
 (curs(sprim(switch target)),(kenil,ks))(ge,le,Ms) /\
 store Tint8 M(bc,0%Z)(V293_byteval nh)=Some Ms /\
 (ge,le,Ms,ir,aux,O,op)|=SWINVt(V293_ready_inv br bg bp)ct **
 (V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval nh) **
 (V293_owned_record_cell((bh,0%Z),Tint8,V293_byteval nh) **
 (V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,Vptr next) **R))) /\
 (forall b i,b<>bc \/i<>0%Z ->get Ms(b,i)=get M(b,i)).
Proof.
 intros br bg bp P ks ge le M ir aux O op ct R high current target bh bc bo nh cached next
 Range HN CN HG CG Held.
 assert(High:load Tint8 M(bh,0%Z)=Some(V293_byteval nh)).
 { eapply V293_record_star_load_l with(s:=(ge,le,M,ir,aux,O,op))
 (P:=V293_owned_record_cell((bh,0%Z),Tint8,V293_byteval nh))(Q:=Atrue).
 - intros st H;apply V293_owned_record_cell_load;exact H.
 - sep auto. }
 destruct(V293_ready_cache_write br bg bp ct _ ge le M ir aux O op bc(V293_byteval cached)nh Range Held)
 as(Ms&Store&After&Read&Outside).
 exists Ms;split.
 - unfold V293_interrupt_handoff.
   eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply sseq_step]| ].
   eapply V293_cstepstar_trans.
   { eapply V293_assign_byte_execution;try exact Store.
   - cbn[evaltype];rewrite CN,CG;reflexivity.
   - cbn[evaladdr get_lenv get_genv];rewrite CN,CG;reflexivity.
   - cbn[evaltype];rewrite HN,HG;reflexivity.
   - cbn[evalval evaltype get_lenv get_genv];rewrite HN,HG;cbn -[load];exact High. }
   eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply sskip_step]|apply c_stepstar0].
 - repeat split;assumption.
Qed.

(* Two explicit programs, differing ONLY by the cache-copy command.
   Both execute the original switch; neither installs a raw port body. *)
Theorem V293_OSIntExit_boundary_switch :
 forall (sync:bool) br bg bp P ks pc po pi ip T les aus cst interrupted ike interrupted_le ge caller M ir enabled si ci O op ct R tasks nc
 f sched_id unmap group rows high y table target nesting lock running saved current counter
 bt bh bo bn bl brun bc bcount c oldhigh oldtarget bcur,
 P=pumerge po pi ->
 get T ct=Some(curs(scall f nil),(kenil,kint interrupted ike interrupted_le ks)) ->
 get les ct=Some caller ->get aus ct=Some(enabled,si,ci) ->
 goodks(pc,(po,pi,ip))ks ->
 P f=Some(V293_exit_boundary_function running nesting lock saved table high target current counter sched_id (if sync then V293_interrupt_handoff high current target else sprim(switch target))) ->
 P sched_id=Some(V293_OSSchedNew_function unmap group rows high y) ->
 ~In saved [unmap;group;rows;high;table;target;nesting;lock;running;current;counter] ->
 y<>unmap ->y<>group ->y<>rows ->y<>high ->y<>table ->bh<>bp ->bn<>bt ->
 get ge unmap=Some(bt,Tarray Tint8 256) ->get ge group=Some(bg,Tint8) ->
 get ge rows=Some(br,Tarray Tint8 2) ->get ge high=Some(bh,Tint8) ->
 get ge table=Some(bp,Tarray(Tptr V293_tcb_type)13) ->get ge target=Some(bo,Tptr V293_tcb_type) ->
 get ge nesting=Some(bn,Tint8) ->get ge lock=Some(bl,Tint8) ->
 get ge running=Some(brun,Tint8) ->get ge current=Some(bc,Tint8) ->get ge counter=Some(bcount,Tint32) ->
 get ge OSTCBCur=Some(bcur,Tptr V293_tcb_type) ->
 (forall t pr st msg,get tasks t=Some(pr,st,msg) ->
   exists C le aux,get T t=Some C /\ get les t=Some le /\ get aus t=Some aux) ->
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
 exists bs next nh Me Ms Mf,fresh M bs /\ next<>ct /\ nh<>nc /\
 V293_highest_ready tasks next /\V293_current_task tasks next nh /\
 V293_global_steps(pc,(po,pi,ip))cst
 (T,(ge,les,M,ir,aus),ct)
 (set T ct(SKIP,(kenil,
   kseq(sprim excrit)(kseq sret(kcall f
     (V293_exit_boundary_body running nesting lock saved table high target current counter sched_id
       (if sync then V293_interrupt_handoff high current target else sprim(switch target)))
       caller(kint interrupted ike interrupted_le ks))))),
  (ge,set les ct(V293_cpu_lenv saved bs),Mf,ir,set aus ct(false,si,enabled::ci)),next) /\
 (ge,V293_cpu_lenv saved bs,Mf,ir,(false,si,enabled::ci),set O curtid(oscurt next),op)|=
 SWINVt(V293_ready_inv br bg bp)next **
 (V293_owned_record_cell((bh,0%Z),Tint8,V293_byteval nh) **
 (V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,Vptr next) **
 (V293_owned_record_cell((bn,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((bl,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval(if sync then nh else nc)) **
 (V293_owned_record_cell((brun,0%Z),Tint8,V293_byteval 1) **
 (V293_owned_record_cell((bcount,0%Z),Tint32,Vint32(Int.add c Int.one)) **
 (Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **R)))))))) /\
 load(Tptr V293_tcb_type)Mf(bcur,0%Z)=Some(Vptr next) /\
 load Tint8 Mf(bc,0%Z)=Some(V293_byteval(if sync then nh else nc)) /\
 load Tint32 Mf(bcount,0%Z)=Some(Vint32(Int.add c Int.one)) /\
 (forall k,k<4 ->exists v,get Mf(bs,Z.of_nat k)=Some(true,v)) /\
 (V293_cache_current tasks next Mf bc <-> sync=true) /\
 (sync=true ->store Tint8 Me(bc,0%Z)(V293_byteval nh)=Some Ms) /\
 store(Tptr V293_tcb_type)Ms(bcur,0%Z)(Vptr next)=Some Mf /\
 (exists C le aux,get T next=Some C /\get les next=Some le /\get aus next=Some aux /\
   get(set T ct(SKIP,(kenil,kseq(sprim excrit)(kseq sret(kcall f
     (V293_exit_boundary_body running nesting lock saved table high target current counter sched_id
       (if sync then V293_interrupt_handoff high current target else sprim(switch target)))
       caller(kint interrupted ike interrupted_le ks))))))next=Some C /\
   get(set les ct(V293_cpu_lenv saved bs))next=Some le /\
   get(set aus ct(false,si,enabled::ci))next=Some aux).
Proof.
 intros sync br bg bp P ks pc po pi ip T les aus cst interrupted ike interrupted_le ge caller M ir enabled si ci O op ct R tasks nc
 f sched_id unmap group rows high y table target nesting lock running saved current counter
 bt bh bo bn bl brun bc bcount c oldhigh oldtarget bcur
 Merge Code Env Aux GoodKs Program Scheduler Names YU YG YR YH YT HP NT
 GU GG GR GH GT GO GN GL GRun GC GCount GCur Domain Map Current NotHighest Good Lookup Held.
 set(cmd:=if sync then V293_interrupt_handoff high current target else sprim(switch target))in *.
 destruct(V293_exit_boundary_entry_global br bg bp P ks pc po pi ip T les aus cst
 interrupted ike interrupted_le ge caller M ir enabled si ci O op ct R tasks nc
 f sched_id unmap group rows high y table target nesting lock running saved current counter cmd
 bt bh bo bn bl brun bc bcount c oldhigh oldtarget
 Merge Code Env Aux GoodKs Program Scheduler Names YU YG YR YH YT HP NT
 GU GG GR GH GT GO GN GL GRun GC GCount Map Current NotHighest Good Lookup Held)
 as(bs&next&nh&Me&Fresh&Different&PrioDifferent&Highest&Next&Prefix&Post&Target&Count&Cache&Alive&Frame).
 set(le:=V293_cpu_lenv saved bs)in *.
 set(rest:=V293_owned_record_cell((bn,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((bl,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((brun,0%Z),Tint8,V293_byteval 1) **
 (V293_owned_record_cell((bcount,0%Z),Tint32,Vint32(Int.add c Int.one)) **
 (Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **R))))).
 set(body:=V293_exit_boundary_body running nesting lock saved table high target current counter sched_id cmd)in *.
 set(inner:=kseq(sprim excrit)(kseq sret(kcall f body caller kstop))).
 set(K:=inner ## kint interrupted ike interrupted_le ks).
 assert(Range:nh<256)by(destruct Next as[Bound _];lia).
 assert(HN:get le high=None).
 { unfold le,V293_cpu_lenv;rewrite map_get_set' by(intro E;apply Names;simpl;intuition congruence);apply map_emp_get. }
 assert(CN:get le current=None).
 { unfold le,V293_cpu_lenv;rewrite map_get_set' by(intro E;apply Names;simpl;intuition congruence);apply map_emp_get. }
 assert(Reordered:(ge,le,Me,ir,(false,si,enabled::ci),O,op)|=
 SWINVt(V293_ready_inv br bg bp)ct **
 (V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval nc) **
 (V293_owned_record_cell((bh,0%Z),Tint8,V293_byteval nh) **
 (V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,Vptr next) **rest)))).
 { unfold rest;clear Held;sep auto. }
 assert(Copy:exists Ms,
 cstepstar P(curs cmd,(kenil,inner))(ge,le,Me)
 (curs(sprim(switch target)),(kenil,inner))(ge,le,Ms) /\
 (ge,le,Ms,ir,(false,si,enabled::ci),O,op)|=
 SWINVt(V293_ready_inv br bg bp)ct **
 (V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval(if sync then nh else nc)) **
 (V293_owned_record_cell((bh,0%Z),Tint8,V293_byteval nh) **
 (V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,Vptr next) **rest))) /\
 (sync=true ->store Tint8 Me(bc,0%Z)(V293_byteval nh)=Some Ms)).
 { unfold cmd;destruct sync.
 - destruct(V293_handoff_copy_execution br bg bp P inner ge le Me ir(false,si,enabled::ci)O op ct rest
   high current target bh bc bo nh nc next Range HN CN GH GC Reordered)
   as(Ms&Exec&Store&After&Outside).
   exists Ms;repeat split;auto.
 - exists Me;split;[apply c_stepstar0| ];split;[exact Reordered|discriminate]. }
 destruct Copy as(Ms&Copy&AfterCopy&CopyStore).
 assert(InnerGood:goodks(pc,(po,pi,ip))(snd(snd(V293_enclose(curs cmd,(kenil,inner))
   (kint interrupted ike interrupted_le ks))))).
 { change (match(pumerge po pi)f with
   |Some _=>goodks(pc,(po,pi,ip))ks
   |None=>no_os(pc,(po,pi,ip))(kint interrupted ike interrupted_le ks) end).
   rewrite <-Merge,Program;exact GoodKs. }
 rewrite Merge in Copy.
 pose proof(V293_csteps_local _ _ _ _ _ ir(false,si,enabled::ci)Copy)as CopyLocal.
 pose proof(V293_interrupt_local_steps_global pc po pi ip _ _ _ _ CopyLocal
 interrupted ike interrupted_le ks T les aus ct cst InnerGood)as CopyGlobal.
 cbn[V293_local_global_at V293_global_at V293_enclose]in CopyGlobal.
 assert(TargetAfter:load(Tptr V293_tcb_type)Ms(bo,0%Z)=Some(Vptr next)).
 { eapply V293_record_star_load_l with(s:=(ge,le,Ms,ir,(false,si,enabled::ci),O,op))
 (P:=V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,Vptr next))(Q:=Atrue).
 - intros st H;apply V293_owned_record_cell_load;exact H.
 - clear Held Post Reordered;sep auto. }
 destruct(V293_ready_switch_cache br bg bp pc po pi ip
 (set T ct(curs(sprim(switch target)),(kenil,K)))cst K ct next target bo bcur bc
 ge le(set les ct le)Ms ir(false,si,enabled::ci)(set aus ct(false,si,enabled::ci))O op
 (V293_owned_record_cell((bh,0%Z),Tint8,V293_byteval nh) **
 (V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,Vptr next) **rest))
 V293_tcb_type tasks(if sync then nh else nc)nh
 (map_get_set _ _ _)(map_get_set _ _ _)(map_get_set _ _ _) GO TargetAfter GCur
 ltac:(destruct sync;[destruct Next|destruct Current];lia)Map Next AfterCopy)
 as(Mf&Switch&PointerStore&Final&Pointer&FinalCache&Coherent&TaskMap&Outside).
 rewrite <-set_set_eq in Switch.
 assert(Global:V293_global_steps(pc,(po,pi,ip))cst
 (T,(ge,les,M,ir,aus),ct)
 (set T ct(SKIP,(kenil,K)),(ge,set les ct le,Mf,ir,set aus ct(false,si,enabled::ci)),next)).
 { eapply V293_global_trans;[exact Prefix| ].
   eapply V293_global_trans;[exact CopyGlobal| ].
   eapply rt1n_trans with(y:=(set T ct(SKIP,(kenil,K)),
     (ge,set les ct le,Mf,ir,set aus ct(false,si,enabled::ci)),next));
     [exact Switch|apply rt1n_refl]. }
 assert(FinalPost:(ge,le,Mf,ir,(false,si,enabled::ci),set O curtid(oscurt next),op)|=
 SWINVt(V293_ready_inv br bg bp)next **
 (V293_owned_record_cell((bh,0%Z),Tint8,V293_byteval nh) **
 (V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,Vptr next) **
 (V293_owned_record_cell((bn,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((bl,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval(if sync then nh else nc)) **
 (V293_owned_record_cell((brun,0%Z),Tint8,V293_byteval 1) **
 (V293_owned_record_cell((bcount,0%Z),Tint32,Vint32(Int.add c Int.one)) **
 (Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **R))))))))).
 { unfold rest in Final;clear Held Post Reordered AfterCopy;sep auto. }
 assert(FinalCount:load Tint32 Mf(bcount,0%Z)=Some(Vint32(Int.add c Int.one))).
 { eapply V293_record_star_load_l with
 (s:=(ge,le,Mf,ir,(false,si,enabled::ci),set O curtid(oscurt next),op))
 (P:=V293_owned_record_cell((bcount,0%Z),Tint32,Vint32(Int.add c Int.one)))(Q:=Atrue).
 - intros st H;apply V293_owned_record_cell_load;exact H.
 - clear Held Post Reordered AfterCopy Final;sep auto. }
 assert(FinalAlive:forall k,k<4 ->exists v,get Mf(bs,Z.of_nat k)=Some(true,v)).
 { assert(Saved:(ge,le,Mf,ir,(false,si,enabled::ci),set O curtid(oscurt next),op)|=
   Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **Atrue).
   { clear Held Post Reordered AfterCopy Final;sep auto. }
   intros k Bound;pose proof(V293_tick_raw_owned_writable bs Tint32(Vint32 Int.zero)_ _ _ _ _ _ _ _ Saved)as W.
   apply W;cbn;lia. }
 assert(ExactCoherence:V293_cache_current tasks next Mf bc <->sync=true).
 { rewrite Coherent;destruct sync;split;intro H;try reflexivity;try discriminate.
   exfalso;apply PrioDifferent;symmetry;exact H. }
 pose proof Next as NextKeep.
 destruct Next as[NextRange[st[msg NextLookup]]].
 destruct(Domain next _ _ _ NextLookup)as(Cnext&lnext&anext&TC&EC&AC).
 exists bs;exists next;exists nh;exists Me;exists Ms;exists Mf.
 repeat first[assumption|split].
 exists Cnext;exists lnext;exists anext;repeat split;try assumption;
 rewrite map_get_set' by congruence;assumption.
Qed.
