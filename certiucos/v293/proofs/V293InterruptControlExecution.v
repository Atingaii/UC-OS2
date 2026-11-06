(* Concrete, uninterleaved source slices. Dispatch is an unexecuted cut point;
   this does not migrate the interrupt soundness theorem or whole functions. *)
Require Import CertiOS.certiucos.v293.proofs.V293InterruptFixedControlSpec.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptControlRetention.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitExecution.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitDispatchExecution.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.code.V293OSIntEnter.
Require Import CertiOS.certiucos.v293.code.V293OSIntExit.
Require Import CertiOS.certiucos.v293.code.V293OSSchedGuards.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import Coq.Lists.List Lia.
Local Open Scope nat_scope.

Definition V293_control_enter_memory bn c M :=
 if Nat.eqb(V293_control_running c)1 && Nat.ltb(V293_control_nesting c)255
 then V293_put_byte M(bn,0%Z)(S(V293_control_nesting c)) else M.
Definition V293_control_decrement_memory bn n M :=
 match n with 0=>M | S _=>V293_put_byte M(bn,0%Z)(Nat.pred n) end.
Definition V293_control_exit_residual n l dispatch :=
 if Nat.eqb(Nat.pred n)0 && Nat.eqb l 0 then dispatch else sskip None.

Lemma V293_control_enter_eval : forall ge le M running nesting br bn r n,
 r<256 ->n<256 ->V293_interrupt_env running nesting br bn ge le ->
 load Tint8 M(br,0%Z)=Some(V293_byteval r) ->
 load Tint8 M(bn,0%Z)=Some(V293_byteval n) ->
 evalval(V293_OSIntEnter_running running)(ge,le,M)=
  Some(Vint32(if Nat.eqb r 1 then Int.one else Int.zero)) /\
 evalval(V293_OSIntEnter_room nesting)(ge,le,M)=
  Some(Vint32(if Nat.ltb n 255 then Int.one else Int.zero)) /\
 (n<255 ->evalval(V293_OSIntEnter_next nesting)(ge,le,M)=Some(V293_byteval(S n))).
Proof.
 intros ge le M running nesting br bn r n R N[NR[GR[NN GN]]]LR LN.
 unfold V293_OSIntEnter_running,V293_OSIntEnter_room,V293_OSIntEnter_next.
 cbn [evalval evaltype get_lenv get_genv].
 rewrite NR,GR,NN,GN;cbn -[load];rewrite LR,LN.
 unfold V293_byteval;cbn [cast_eval bop_eval val_eq bop_type cmp_val cmpu].
 rewrite V293_interrupt_eq_one by exact R;rewrite V293_interrupt_lt_255 by exact N.
 change(Nat.ltb n 255)with(Nat.leb n 254).
 split;[destruct(Nat.eqb r 1);reflexivity| ];
 split;[destruct(Nat.leb n 254);reflexivity| ].
 intros Room.
 change(Some(Vint32(Int.modu(Int.add(Int.repr(Z.of_nat n))Int.one)(Int.repr Byte.modulus)))=Some(Vint32(Int.repr(Z.of_nat(S n))))).
 rewrite V293_interrupt_byte_add by exact Room;reflexivity.
Qed.

(* No store or execution premise: the sole writable cell constructs the store. *)
Theorem V293_control_enter_execution : forall P ks ge le M running nesting br bn c,
 V293_control_valid c ->V293_interrupt_env running nesting br bn ge le ->
 load Tint8 M(br,0%Z)=Some(V293_byteval(V293_control_running c)) ->
 load Tint8 M(bn,0%Z)=Some(V293_byteval(V293_control_nesting c)) ->
 (exists v,get M(bn,0%Z)=Some(true,v)) ->
 cstepstar P(curs(V293_OSIntEnter_updates running nesting),(kenil,ks))(ge,le,M)
 (curs(sskip None),(kenil,ks))(ge,le,V293_control_enter_memory bn c M).
Proof.
 intros P ks ge le M running nesting br bn[r n l][R[N L]]Env LR LN[v W].
 destruct(V293_control_enter_eval ge le M running nesting br bn r n R N Env LR LN)
 as[Run[Room Next]].
 destruct Env as[NR[GR[NN GN]]].
 unfold V293_control_enter_memory;cbn [V293_control_running V293_control_nesting].
 unfold V293_OSIntEnter_updates.
 eapply V293_rekey_if_execution with(flag:=Nat.eqb r 1);[exact Run| | ].
 - intro Running;rewrite Running;rewrite Bool.andb_true_l.
   eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply sseq_step]| ].
   eapply V293_cstepstar_trans with
    (m2:=(ge,le,if Nat.ltb n 255 then V293_put_byte M(bn,0%Z)(S n)else M)).
   + eapply V293_rekey_if_execution with(flag:=Nat.ltb n 255);[exact Room| | ].
     * intro Space;pose proof(proj1(Nat.ltb_lt n 255)Space)as Bound.
       eapply V293_assign_byte_execution.
       -- cbn [evaltype];rewrite NN,GN;reflexivity.
       -- cbn [evaladdr get_lenv get_genv];rewrite NN,GN;reflexivity.
       -- unfold V293_OSIntEnter_next;cbn [evaltype];rewrite NN,GN;reflexivity.
       -- apply Next;exact Bound.
       -- rewrite Space;eapply V293_put_byte_store;exact W.
     * intro Full;rewrite Full;reflexivity.
   + eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply sskip_step]| ].
     apply c_stepstar0.
 - intro Stopped;rewrite Stopped;reflexivity.
Qed.

Theorem V293_control_enter_observation : forall br bn bl c M,
 V293_control_valid c ->br<>bn ->bl<>bn ->
 load Tint8 M(br,0%Z)=Some(V293_byteval(V293_control_running c)) ->
 load Tint8 M(bn,0%Z)=Some(V293_byteval(V293_control_nesting c)) ->
 load Tint8 M(bl,0%Z)=Some(V293_byteval(V293_control_lock c)) ->
 V293_control_read br bn bl(V293_control_enter_memory bn c M)=Some(V293_control_enter c) /\
 (forall a,a<>(bn,0%Z) ->get(V293_control_enter_memory bn c M)a=get M a).
Proof.
 intros br bn bl[r n l]M[R[N L]]BR BL LR LN LL.
 unfold V293_control_enter_memory,V293_control_enter,V293_interrupt_nest_after;cbn -[Nat.ltb].
 destruct(Nat.eqb r 1 && Nat.ltb n 255)eqn:E.
 - apply Bool.andb_true_iff in E as[_ E];apply Nat.ltb_lt in E.
   split.
   + apply V293_control_read_exact;try assumption;try lia.
     * rewrite V293_put_byte_other_load by congruence;exact LR.
     * apply V293_put_byte_load;lia.
     * rewrite V293_put_byte_other_load by congruence;exact LL.
   + intros;apply V293_put_byte_other;assumption.
 - split;[apply V293_control_read_exact;assumption|intros;reflexivity].
Qed.

(* A single source guard selects its branch without executing that branch. *)
Lemma V293_control_if_select : forall P ks ge le M e yes no (flag:bool),
 evalval e(ge,le,M)=Some(Vint32(if flag then Int.one else Int.zero)) ->
 cstepstar P(curs(sif e yes no),(kenil,ks))(ge,le,M)
 (curs(if flag then yes else no),(kenil,ks))(ge,le,M).
Proof.
 intros P ks ge le M e yes no flag Eval.
 eapply c_stepstarn;[eapply stmt_step;[reflexivity|constructor]| ].
 eapply V293_cstepstar_trans.
 { apply V293_expr_steps;apply evalval_imply_estepstar;exact Eval. }
 destruct flag.
 - eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply svift_step;reflexivity]|apply c_stepstar0].
 - eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply sviff_step;reflexivity]|apply c_stepstar0].
Qed.

Lemma V293_control_guards_execution : forall P ks ge le M nesting lock bn bl n l dispatch,
 n<256 ->l<256 ->V293_interrupt_env nesting lock bn bl ge le ->
 load Tint8 M(bn,0%Z)=Some(V293_byteval n) ->
 load Tint8 M(bl,0%Z)=Some(V293_byteval l) ->
 cstepstar P(curs(V293_OSIntExit_guards nesting lock dispatch),(kenil,ks))(ge,le,M)
 (curs(if Nat.eqb n 0 && Nat.eqb l 0 then dispatch else sskip None),(kenil,ks))(ge,le,M).
Proof.
 intros P ks ge le M nesting lock bn bl n l dispatch N L[NN[GN[NL GL]]]LN LL.
 unfold V293_OSIntExit_guards.
 eapply V293_cstepstar_trans.
 { apply V293_control_if_select with(flag:=Nat.eqb n 0).
   exact(V293_success_global_byte_eq ge le M nesting bn n 0 N ltac:(lia)NN GN LN). }
 destruct(Nat.eqb n 0);cbn;[ |apply c_stepstar0].
 apply V293_control_if_select.
 exact(V293_success_global_byte_eq ge le M lock bl l 0 L ltac:(lia)NL GL LL).
Qed.

Theorem V293_control_decrement_execution : forall P ks ge le M nesting bn n,
 n<256 ->get le nesting=None ->get ge nesting=Some(bn,Tint8) ->
 load Tint8 M(bn,0%Z)=Some(V293_byteval n) ->
 (exists v,get M(bn,0%Z)=Some(true,v)) ->
 cstepstar P(curs(V293_OSIntExit_decrement nesting),(kenil,ks))(ge,le,M)
 (curs(sskip None),(kenil,ks))(ge,le,V293_control_decrement_memory bn n M).
Proof.
 intros P ks ge le M nesting bn n N NN GN LN[v W].
 destruct n as [ | n ].
 - cbn [V293_control_decrement_memory].
   unfold V293_OSIntExit_decrement;eapply V293_rekey_if_execution with(flag:=false).
   + unfold V293_OSIntExit_positive;cbn [evalval evaltype get_lenv get_genv].
     rewrite NN,GN;cbn -[load];rewrite LN;reflexivity.
   + discriminate.
   + reflexivity.
 - destruct n as [ | n ].
   + eapply V293_exit_one_decrement_execution;try eassumption.
     eapply V293_put_byte_store;exact W.
   + destruct(V293_exit_physical_decrement_eval ge le M nesting bn(S(S n))
   ltac:(lia)N NN GN LN)as[Positive[T[A[Previous Eval]]]].
   unfold V293_OSIntExit_decrement;eapply V293_rekey_if_execution with(flag:=true).
     * exact Positive.
     * intros _;eapply V293_assign_byte_execution;try eassumption.
     eapply V293_put_byte_store;exact W.
     * discriminate.
Qed.

Theorem V293_control_decrement_observation : forall br bn bl M n l,
 n<256 ->l<256 ->br<>bn ->bl<>bn ->
 load Tint8 M(br,0%Z)=Some(V293_byteval 1) ->
 load Tint8 M(bn,0%Z)=Some(V293_byteval n) ->
 load Tint8 M(bl,0%Z)=Some(V293_byteval l) ->
 load Tint8(V293_control_decrement_memory bn n M)(bn,0%Z)=Some(V293_byteval(Nat.pred n)) /\
 load Tint8(V293_control_decrement_memory bn n M)(bl,0%Z)=Some(V293_byteval l) /\
 V293_control_read br bn bl(V293_control_decrement_memory bn n M)=
 Some(V293_control_exit(V293_control 1 n l)) /\
 (forall a,a<>(bn,0%Z) ->get(V293_control_decrement_memory bn n M)a=get M a).
Proof.
 intros br bn bl M n l N L BR BL LR LN LL.
 unfold V293_control_exit;cbn.
 assert(Pred:Nat.pred n<256)by lia.
 assert(Nest:load Tint8(V293_control_decrement_memory bn n M)(bn,0%Z)=Some(V293_byteval(Nat.pred n))).
 { destruct n;cbn [V293_control_decrement_memory Nat.pred];[exact LN|apply V293_put_byte_load;lia]. }
 assert(Lock:load Tint8(V293_control_decrement_memory bn n M)(bl,0%Z)=Some(V293_byteval l)).
 { destruct n;cbn [V293_control_decrement_memory];[exact LL|rewrite V293_put_byte_other_load by congruence;exact LL]. }
 split;[exact Nest| ];split;[exact Lock| ];split.
 - apply V293_control_read_exact;try assumption;try lia.
   destruct n;cbn [V293_control_decrement_memory];[exact LR|rewrite V293_put_byte_other_load by congruence;exact LR].
 - intros a Outside;destruct n;cbn [V293_control_decrement_memory];[reflexivity|apply V293_put_byte_other;exact Outside].
Qed.

(* The same resulting memory witnesses real execution, observation, and the
   fixed Exit operation. Enabled dispatch is NOT evaluated or simulated. *)
Theorem V293_control_exit_execution_bridge : forall P ks sd O ge le M
 nesting lock br bn bl n l dispatch,
 n<256 ->l<256 ->br<>bn ->bl<>bn ->
 V293_interrupt_env nesting lock bn bl ge le ->
 load Tint8 M(br,0%Z)=Some(V293_byteval 1) ->
 load Tint8 M(bn,0%Z)=Some(V293_byteval n) ->
 load Tint8 M(bl,0%Z)=Some(V293_byteval l) ->
 (exists v,get M(bn,0%Z)=Some(true,v)) ->
 exists Mf,
 cstepstar P(curs(V293_OSIntExit_nesting_dispatch nesting lock dispatch),(kenil,ks))(ge,le,M)
 (curs(V293_control_exit_residual n l dispatch),(kenil,ks))(ge,le,Mf) /\
 V293_control_read br bn bl Mf=Some(V293_control_exit(V293_control 1 n l)) /\
 V293_control_step sd V293_control_Exit(O,V293_control 1 n l)
 (V293_control_Core(V293_control_exit_code(V293_control 1 n l)))
 (O,V293_control_exit(V293_control 1 n l)) /\
 (forall a,a<>(bn,0%Z) ->get Mf a=get M a).
Proof.
 intros P ks sd O ge le M nesting lock br bn bl n l dispatch
 N L BR BL Env LR LN LL W.
 destruct Env as[NN[GN[NL GL]]].
 destruct(V293_control_decrement_observation br bn bl M n l N L BR BL LR LN LL)
 as[NewN[NewL[Read Frame]]].
 exists(V293_control_decrement_memory bn n M);split.
 - unfold V293_OSIntExit_nesting_dispatch,V293_control_exit_residual.
   eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply sseq_step]| ].
   eapply V293_cstepstar_trans with(m2:=(ge,le,V293_control_decrement_memory bn n M)).
   { eapply V293_control_decrement_execution;eassumption. }
   eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply sskip_step]| ].
   eapply V293_control_guards_execution;try exact NewN;try exact NewL;try lia.
   unfold V293_interrupt_env;auto.
 - split;[exact Read| ];split;[constructor;unfold V293_control_valid;cbn;lia|exact Frame].
Qed.

Theorem V293_control_enter_execution_bridge : forall P ks sd O ge le M
 running nesting br bn bl c,
 V293_control_valid c ->br<>bn ->bl<>bn ->
 V293_interrupt_env running nesting br bn ge le ->
 load Tint8 M(br,0%Z)=Some(V293_byteval(V293_control_running c)) ->
 load Tint8 M(bn,0%Z)=Some(V293_byteval(V293_control_nesting c)) ->
 load Tint8 M(bl,0%Z)=Some(V293_byteval(V293_control_lock c)) ->
 (exists v,get M(bn,0%Z)=Some(true,v)) ->
 exists Mf,
 cstepstar P(curs(V293_OSIntEnter_updates running nesting),(kenil,ks))(ge,le,M)
 (curs(sskip None),(kenil,ks))(ge,le,Mf) /\
 V293_control_read br bn bl Mf=Some(V293_control_enter c) /\
 V293_control_step sd V293_control_Enter(O,c)
 (V293_control_Core(spec_done None))(O,V293_control_enter c) /\
 (forall a,a<>(bn,0%Z) ->get Mf a=get M a).
Proof.
 intros P ks sd O ge le M running nesting br bn bl c Valid BR BL Env LR LN LL W.
 destruct(V293_control_enter_observation br bn bl c M Valid BR BL LR LN LL)as[Read Frame].
 exists(V293_control_enter_memory bn c M);split.
 - eapply V293_control_enter_execution;eassumption.
 - split;[exact Read| ];split;[constructor;exact Valid|exact Frame].
Qed.

(* Physical continuation and abstract scheduler request share one decision. *)
Theorem V293_control_exit_residual_exact : forall n l dispatch,
 V293_control_exit_residual n l dispatch=
 if V293_control_dispatch(V293_control 1 n l)then dispatch else sskip None.
Proof.
 intros;unfold V293_control_exit_residual,V293_control_dispatch,V293_exit_enabled,V293_exit_depth;reflexivity.
Qed.
