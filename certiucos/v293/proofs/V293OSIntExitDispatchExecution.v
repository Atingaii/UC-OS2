(* The last interrupt executes the real scheduler call and pointer handoff.
   This interface stops BEFORE the original priority decision; no switch
   implementation, enclosing critical section, ISR closure or GOOD_OS credit. *)
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitExecution.
Require Import CertiOS.certiucos.v293.proofs.V293ReadySchedCall.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.code.V293OSIntExit.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.certiucos.v293.code.V293OSSchedDispatch.
Require Import CertiOS.certiucos.v293.code.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Lemma V293_exit_one_decrement_execution : forall P ks ge le M M0 nesting bn,
 get le nesting=None -> get ge nesting=Some(bn,Tint8) ->
 load Tint8 M(bn,0%Z)=Some(V293_byteval 1) ->
 store Tint8 M(bn,0%Z)(V293_byteval 0)=Some M0 ->
 cstepstar P(curs(V293_OSIntExit_decrement nesting),(kenil,ks))(ge,le,M)
 (curs(sskip None),(kenil,ks))(ge,le,M0).
Proof.
 intros P ks ge le M M0 nesting bn NL G Load Store.
 assert(Positive:evalval(V293_OSIntExit_positive nesting)(ge,le,M)=Some(Vint32 Int.one)).
 { unfold V293_OSIntExit_positive;cbn[evalval evaltype get_lenv get_genv].
   rewrite NL,G;cbn -[load];rewrite Load;reflexivity. }
 unfold V293_OSIntExit_decrement;eapply V293_rekey_if_execution with(flag:=true).
 - exact Positive.
 - intros _;eapply V293_assign_byte_execution;try exact Store.
   + cbn[evaltype];rewrite NL,G;reflexivity.
   + cbn[evaladdr get_lenv get_genv];rewrite NL,G;reflexivity.
   + unfold V293_OSIntExit_previous;cbn[evaltype];rewrite NL,G;reflexivity.
   + unfold V293_OSIntExit_previous;cbn[evalval evaltype get_lenv get_genv].
     rewrite NL,G;cbn -[load];rewrite Load;reflexivity.
 - discriminate.
Qed.

(* A state-preserving guard prefix, with the actual current memory loads.
   This does not grant any execution of its dispatch argument. *)
Lemma V293_exit_zero_guards_enter : forall P ks ge le M nesting lock bn bl dispatch,
 get le nesting=None -> get ge nesting=Some(bn,Tint8) ->
 get le lock=None -> get ge lock=Some(bl,Tint8) ->
 load Tint8 M(bn,0%Z)=Some(V293_byteval 0) ->
 load Tint8 M(bl,0%Z)=Some(V293_byteval 0) ->
 cstepstar P(curs(V293_OSIntExit_guards nesting lock dispatch),(kenil,ks))(ge,le,M)
 (curs dispatch,(kenil,ks))(ge,le,M).
Proof.
 intros P ks ge le M nesting lock bn bl dispatch NN GN NL GL Nest Lock.
 unfold V293_OSIntExit_guards.
 eapply c_stepstarn;[eapply stmt_step;[reflexivity | constructor] | ].
 eapply V293_cstepstar_trans.
 { apply V293_expr_steps;apply evalval_imply_estepstar.
   exact(V293_success_global_byte_eq ge le M nesting bn 0 0 ltac:(lia)ltac:(lia)NN GN Nest). }
 eapply c_stepstarn;[eapply stmt_step;[reflexivity | apply svift_step;reflexivity] | ].
 eapply c_stepstarn;[eapply stmt_step;[reflexivity | constructor] | ].
 eapply V293_cstepstar_trans.
 { apply V293_expr_steps;apply evalval_imply_estepstar.
   exact(V293_success_global_byte_eq ge le M lock bl 0 0 ltac:(lia)ltac:(lia)NL GL Lock). }
 eapply c_stepstarn;[eapply stmt_step;[reflexivity | apply svift_step;reflexivity] | ].
 apply c_stepstar0.
Qed.

(* No statement/callee-execution, allocation or store premise. The writable
   nesting byte and arbitrary frame survive the real callee's allocation/free.
   The actual priority decision remains in the returned control state. *)
Theorem V293_OSIntExit_dispatch_prefix_execution :
 forall br bg bp P ks ge le M ir aux O op ct R
 f unmap group rows high y table target nesting lock current counter int_switch
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
   (V293_OSIntExit_dispatch table high target current counter f int_switch)),(kenil,ks))(ge,le,M)
 (curs(sif(V293_OSSched_different high current)
   (sseq(V293_OSSched_increment counter)(sseq(sskip None)(scall int_switch nil)))
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
 nesting lock current counter int_switch bt bh bo bn bl oldhigh oldtarget
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
 (sseq(V293_OSSched_increment counter)(sseq(sskip None)(scall int_switch nil)))(sskip None)).
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
   unfold V293_OSIntExit_dispatch;fold tail.
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
