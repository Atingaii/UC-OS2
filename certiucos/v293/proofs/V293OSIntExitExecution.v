(* Explicit ADR-0005 macro abstraction. Not execution of the raw port calls.
   The nested path executes real writes and void return; no callee oracle. *)
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.code.V293OSIntExit.
Require Import CertiOS.certiucos.v293.code.V293OSIntEnter.
Require Import CertiOS.certiucos.v293.code.V293OSSchedDispatch.
Require Import CertiOS.certiucos.v293.code.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition V293_OSIntExit_abstract_body running nesting lock saved table high target current counter sched_id int_switch :=
 sseq (sassign (evar saved) (econst32 Int.zero))
 (sseq (sifthen (V293_OSIntEnter_running running)
  (sseq (sprim encrit)
   (sseq (V293_OSIntExit_nesting_dispatch nesting lock
    (V293_OSIntExit_dispatch table high target current counter sched_id int_switch))
    (sprim excrit)))) sret).

Theorem V293_OSIntExit_abstract_normalization : forall running nesting lock saved table high target current counter sched_id enter exit int_switch,
 enter<>exit -> sched_id<>enter -> sched_id<>exit -> int_switch<>enter -> int_switch<>exit ->
 V293_port_normalize enter exit saved
 (V293_OSIntExit_body running nesting lock saved table high target current counter sched_id enter exit int_switch)=
 Some(V293_OSIntExit_abstract_body running nesting lock saved table high target current counter sched_id int_switch).
Proof.
 intros;unfold V293_port_normalize,V293_OSIntExit_body,V293_OSIntExit_abstract_body,
 V293_OSIntExit_nesting_dispatch,V293_OSIntExit_decrement,V293_OSIntExit_guards,
 V293_OSIntExit_dispatch,V293_OSSched_unlocked_prefix.
 cbn[V293_port_calls];repeat destruct(Z.eq_dec _ _);intuition congruence.
Qed.

Lemma V293_exit_physical_decrement_eval : forall ge le M nesting bn n,
 2<=n -> n<256 -> get le nesting=None -> get ge nesting=Some(bn,Tint8) ->
 load Tint8 M(bn,0%Z)=Some(V293_byteval n) ->
 evalval(V293_OSIntExit_positive nesting)(ge,le,M)=Some(Vint32 Int.one) /\
 evaltype(evar nesting)(ge,le,M)=Some Tint8 /\
 evaladdr(evar nesting)(ge,le,M)=Some(Vptr(bn,Int.zero)) /\
 evaltype(V293_OSIntExit_previous nesting)(ge,le,M)=Some Tint8 /\
 evalval(V293_OSIntExit_previous nesting)(ge,le,M)=Some(V293_byteval(Nat.pred n)).
Proof.
 intros ge le M nesting bn n Lower Bound NL G Load.
 unfold V293_OSIntExit_positive,V293_OSIntExit_previous.
 cbn[evalval evaltype evaladdr get_lenv get_genv];rewrite NL,G.
 cbn -[load];rewrite Load;unfold V293_byteval.
 cbn[cast_eval bop_eval bop_type cmp_val cmpu].
 rewrite V293_exit_positive by exact Bound.
 assert(N:Nat.eqb n 0=false)by(apply Nat.eqb_neq;lia);rewrite N.
 repeat split;try reflexivity.
 change (Some(Vint32(Int.modu(Int.sub(Int.repr(Z.of_nat n))Int.one)(Int.repr Byte.modulus)))=Some(Vint32(Int.repr(Z.of_nat(Nat.pred n))))).
 rewrite V293_exit_byte_sub by lia;reflexivity.
Qed.

Lemma V293_exit_byte_readback : forall M M' bn n,
 n<256 -> store Tint8 M(bn,0%Z)(V293_byteval n)=Some M' ->
 load Tint8 M'(bn,0%Z)=Some(V293_byteval n).
Proof.
 intros M M' bn n Bound Store;unfold load,loadm.
 rewrite <-(encode_val_length Tint8(V293_byteval n)).
 rewrite V293_loadbytes_get.
 - rewrite type_val_mach_encode_val_decode_val by(apply V293_byte_type;exact Bound);reflexivity.
 - intros k K;exists true;eapply V293_storebytes_nth;eassumption.
Qed.

(* The guard reads the UPDATED byte. Lock and both callees are unreachable,
   and therefore need no binding, implementation or specification here. *)
Theorem V293_OSIntExit_nested_middle_execution : forall P ks ge le M M' nesting lock bn n dispatch,
 2<=n -> n<256 -> get le nesting=None -> get ge nesting=Some(bn,Tint8) ->
 load Tint8 M(bn,0%Z)=Some(V293_byteval n) ->
 store Tint8 M(bn,0%Z)(V293_byteval(Nat.pred n))=Some M' ->
 cstepstar P(curs(V293_OSIntExit_nesting_dispatch nesting lock dispatch),(kenil,ks))(ge,le,M)
 (curs(sskip None),(kenil,ks))(ge,le,M').
Proof.
 intros P ks ge le M M' nesting lock bn n dispatch Lower Bound NL G Load Store.
 destruct(V293_exit_physical_decrement_eval ge le M nesting bn n Lower Bound NL G Load)
 as[Positive[Ty[Addr[PrevTy Prev]]]].
 unfold V293_OSIntExit_nesting_dispatch.
 eapply c_stepstarn;[eapply stmt_step;[reflexivity | apply sseq_step ]  |  ].
 eapply V293_cstepstar_trans.
 { unfold V293_OSIntExit_decrement;eapply V293_rekey_if_execution with(flag:=true).
   - exact Positive.
   - intros _;eapply V293_assign_byte_execution;eassumption.
   - discriminate. }
 eapply c_stepstarn;[eapply stmt_step;[reflexivity | apply sskip_step ]  |  ].
 unfold V293_OSIntExit_guards.
 eapply c_stepstarn;[eapply stmt_step;[reflexivity | constructor ]  |  ].
 eapply V293_cstepstar_trans.
 { apply V293_expr_steps;apply evalval_imply_estepstar.
   pose proof(V293_success_global_byte_eq ge le M' nesting bn(Nat.pred n)0
    ltac:(lia)ltac:(lia)NL G(V293_exit_byte_readback M M' bn(Nat.pred n)ltac:(lia)Store))as E.
   assert(N:Nat.eqb(Nat.pred n)0=false)by(apply Nat.eqb_neq;lia).
   rewrite N in E;exact E. }
 eapply c_stepstarn;[eapply stmt_step;[reflexivity | apply sviff_step;reflexivity ]  |  ].
 apply c_stepstar0.
Qed.

Lemma V293_void_return_execution : forall P ks ge le caller M f body next,
 callcont ks=Some(kcall f body caller next) -> NoDup(map fst(getaddr le)) ->
 (forall b t,In(b,t)(getaddr le)->V293_bytes_writable M b 0%Z(typelen t)) ->
 exists Mf,
 cstepstar P(curs sret,(kenil,ks))(ge,le,M)
 (curs(sskip None),(kenil,next))(ge,caller,Mf) /\
 (forall b i,~In b(map fst(getaddr le))->get Mf(b,i)=get M(b,i)) /\
 (forall b t k,In(b,t)(getaddr le)->k<typelen t->get Mf(b,Z.of_nat k)=None).
Proof.
 intros P ks ge le caller M f body next Call ND W.
 destruct(V293_sfree_construct_execution(getaddr le)P ks ge le M None ND W)as[Mf[Free[Frame Removed]]].
 exists Mf;split;[  |  split;assumption].
 eapply c_stepstarn;[eapply stmt_step;[reflexivity | eapply sret_step;eassumption||reflexivity ]  |  ].
 eapply V293_cstepstar_trans;[exact Free | ].
 eapply c_stepstarn;[eapply stmt_step;[reflexivity | eapply sfreeend_step;eassumption||reflexivity ]  |  ].
 apply c_stepstar0.
Qed.

(* Actual continuous local execution, including saved:=0, critical-stack
   push/pop and return/free. The two store premises are concrete memory
   operations, not statement/callee correctness assumptions. Entry allocation
   and global interrupt interference are NOT established by this theorem. *)
Theorem V293_OSIntExit_nested_execution : forall P ks ge le caller M M0 M1 ir enabled si ci
 running nesting lock saved table high target current counter sched_id int_switch br bn bs n f body next,
 2<=n -> n<256 -> get le saved=Some(bs,Tint32) ->
 store Tint32 M(bs,0%Z)(Vint32 Int.zero)=Some M0 ->
 get le running=None -> get ge running=Some(br,Tint8) ->
 load Tint8 M0(br,0%Z)=Some(V293_byteval 1) ->
 get le nesting=None -> get ge nesting=Some(bn,Tint8) ->
 load Tint8 M0(bn,0%Z)=Some(V293_byteval n) ->
 store Tint8 M0(bn,0%Z)(V293_byteval(Nat.pred n))=Some M1 ->
 callcont ks=Some(kcall f body caller next) -> NoDup(map fst(getaddr le)) ->
 (forall b t,In(b,t)(getaddr le)->V293_bytes_writable M1 b 0%Z(typelen t)) ->
 exists Mf,
 V293_local_steps P
 (curs(V293_OSIntExit_abstract_body running nesting lock saved table high target current counter sched_id int_switch),(kenil,ks))
 ((ge,le,M),ir,(enabled,si,ci))
 (curs(sskip None),(kenil,next))((ge,caller,Mf),ir,(enabled,si,ci)) /\
 (forall b i,~In b(map fst(getaddr le))->get Mf(b,i)=get M1(b,i)) /\
 (forall b t k,In(b,t)(getaddr le)->k<typelen t->get Mf(b,Z.of_nat k)=None).
Proof.
 intros P ks ge le caller M M0 M1 ir enabled si ci running nesting lock saved table high target current counter
 sched_id int_switch br bn bs n f body next Lower Bound Saved Init NR GR Run NN GN Nest Dec Call ND W.
 destruct(V293_void_return_execution P ks ge le caller M1 f body next Call ND W)as[Mf[Return[Frame Removed]]].
 exists Mf;split;[  |  split;assumption].
 unfold V293_OSIntExit_abstract_body.
 eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity | apply sseq_step ]  |  ].
 eapply V293_local_trans.
 { apply V293_csteps_local;eapply V293_success_assign_zero;eassumption. }
 eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity | apply sskip_step ]  |  ].
 eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity | apply sseq_step ]  |  ].
 eapply V293_local_trans.
 { apply V293_csteps_local;eapply V293_entry_if_select with(flag:=true).
   unfold V293_OSIntEnter_running;change Int.one with(Int.repr(Z.of_nat 1)).
   exact(V293_success_global_byte_eq ge le M0 running br 1 1 ltac:(lia)ltac:(lia) NR GR Run). }
 eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity | apply sseq_step ]  |  ].
 eapply V293_local_cons;[apply encrit_step;reflexivity | ].
 eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity | apply sskip_step ]  |  ].
 eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity | apply sseq_step ]  |  ].
 eapply V293_local_trans.
 { apply V293_csteps_local;eapply V293_OSIntExit_nested_middle_execution;eassumption. }
 eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity | apply sskip_step ]  |  ].
 eapply V293_local_cons;[apply excrit_step;reflexivity | ].
 eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity | apply sskip_step ]  |  ].
 apply V293_csteps_local;exact Return.
Qed.
