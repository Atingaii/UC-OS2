(* Original saturating nesting decrement and lock guards, before dispatch. *)
Require Import CertiOS.certiucos.v293.proofs.V293ExitCallDispatchProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293ExitDispatchProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293SchedCallProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitHoare.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.code.V293OSIntExit.
Require Import CertiOS.certiucos.v293.code.V293OSSchedDispatch.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.simulation.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.framework.auxlibs.MapLib.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.proofs.V293HandoffProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBoundarySwitch.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import CertiOS.framework.proof.step_prop.
Require Import Coq.micromega.Lia.
Local Open Scope nat_scope.

Definition V293_exit_decrement_memory (M:mem) (bn:block) (n:nat) : mem :=
 if Nat.eqb n 0 then M else V293_write_byte M bn (Nat.pred n).

Lemma V293_exit_decrement_load : forall M bn n,
 n<256 ->load Tint8 M(bn,0%Z)=Some(V293_byteval n) ->
 load Tint8(V293_exit_decrement_memory M bn n)(bn,0%Z)=Some(V293_byteval(Nat.pred n)).
Proof.
 intros M bn n Bound Read;destruct n;cbn[V293_exit_decrement_memory Nat.eqb Nat.pred];
 [exact Read|apply V293_write_byte_load;lia].
Qed.

Lemma V293_exit_decrement_eval : forall ge le M nesting bn n,
 n<256 ->get le nesting=None ->get ge nesting=Some(bn,Tint8) ->
 load Tint8 M(bn,0%Z)=Some(V293_byteval n) ->
 evalval(V293_OSIntExit_positive nesting)(ge,le,M)=
 Some(Vint32(if Nat.eqb n 0 then Int.zero else Int.one)) /\
 (0<n ->evaltype(evar nesting)(ge,le,M)=Some Tint8 /\
 evaladdr(evar nesting)(ge,le,M)=Some(Vptr(bn,Int.zero)) /\
 evaltype(V293_OSIntExit_previous nesting)(ge,le,M)=Some Tint8 /\
 evalval(V293_OSIntExit_previous nesting)(ge,le,M)=Some(V293_byteval(Nat.pred n))).
Proof.
 intros ge le M nesting bn n Bound NL G Load.
 unfold V293_OSIntExit_positive,V293_OSIntExit_previous.
 cbn[evalval evaltype evaladdr get_lenv get_genv];rewrite NL,G.
 cbn -[load];rewrite Load;unfold V293_byteval.
 cbn[cast_eval bop_eval bop_type cmp_val cmpu].
 rewrite V293_exit_positive by exact Bound.
 split.
 - destruct(Nat.eqb n 0);reflexivity.
 - intro Positive;repeat split;try reflexivity.
   change (Some(Vint32(Int.modu(Int.sub(Int.repr(Z.of_nat n))Int.one)(Int.repr Byte.modulus)))=
   Some(Vint32(Int.repr(Z.of_nat(Nat.pred n))))).
   rewrite V293_exit_byte_sub by lia;reflexivity.
Qed.

Section Nesting.
Variables pc po pi:progunit.
Variable ip:intunit.
Variable T:tasks.
Variable cst:clientst.
Variable t:tid.
Variable ks:stmtcont.
Variables ge le:env.
Variable les:cltenvs.
Variable ir:isr.
Variable aus:ltaskstset.
Variable si:is.
Variable cs:cs.
Variable ph:hprog.
Variable Th:tasks.
Variable O:osabst.
Let P:lprog:=(pc,(po,pi,ip)).
Hypothesis Local:get les t=Some le.
Hypothesis Aux:get aus t=Some((false,si,cs):localst).
Hypothesis Inside:InOS(SKIP,(kenil,ks))(pumerge po pi).
Hypothesis Cur:get O curtid=Some(oscurt t).

Lemma V293_exit_ifthen_progsim : forall M e yes v take,
 evalval e(ge,le,M)=Some v ->istrue v=Some take ->
 ProgSim P(set T t(curs(if take then yes else sskip None),(kenil,ks)))(ge,les,M,ir,aus)ph Th O cst t ->
 ProgSim P(set T t(curs(sifthen e yes),(kenil,ks)))(ge,les,M,ir,aus)ph Th O cst t.
Proof.
 intros M e yes v take Eval Truth Post.
 eapply V293_exit_pure_progsim with(ks:=ks)(C':=(cure e,(kenil,kif yes(sskip None)ks)))(le:=le);
 try eassumption;try reflexivity.
 - eapply stmt_step;[reflexivity|apply sifthen_step].
 - eapply V293_exit_expr_progsim with(m:=(ge,le,M))(m':=(ge,le,M))
   (c':=curs(sskip(Some v)))(ke':=kenil)(le:=le);try eassumption;try reflexivity.
   + apply evalval_imply_estepstar;exact Eval.
   + eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
   + eapply V293_exit_pure_progsim with(ks:=ks)
     (C':=(curs(if take then yes else sskip None),(kenil,ks)))(le:=le);
     try eassumption;try reflexivity.
     eapply stmt_step;[reflexivity| ];destruct take;
     [apply svift_step|apply sviff_step];exact Truth.
Qed.

Lemma V293_exit_decrement_progsim : forall M nesting bn n,
 n<256 ->get le nesting=None ->get ge nesting=Some(bn,Tint8) ->
 load Tint8 M(bn,0%Z)=Some(V293_byteval n) ->
 (0<n ->exists raw,get M(bn,0%Z)=Some(true,raw)) ->
 ProgSim P(set T t(SKIP,(kenil,ks)))(ge,les,V293_exit_decrement_memory M bn n,ir,aus)ph Th O cst t ->
 ProgSim P(set T t(curs(V293_OSIntExit_decrement nesting),(kenil,ks)))(ge,les,M,ir,aus)ph Th O cst t.
Proof.
 intros M nesting bn n Bound NL G Read Writable Post.
 destruct(V293_exit_decrement_eval ge le M nesting bn n Bound NL G Read)as[Eval Assignment].
 unfold V293_OSIntExit_decrement.
 destruct n.
 - eapply V293_exit_ifthen_progsim with(v:=Vint32 Int.zero)(take:=false);
   [exact Eval|reflexivity|exact Post].
 - destruct(Assignment ltac:(lia))as[Left[Address[Right Value]]].
   destruct(Writable ltac:(lia))as[raw Full].
   eapply V293_exit_ifthen_progsim with(v:=Vint32 Int.one)(take:=true);
   [exact Eval|reflexivity| ].
   eapply V293_assign_byte_progsim with(le:=le)(b:=bn)(v:=V293_byteval n)
   (M':=V293_write_byte M bn n);try eassumption.
   eapply V293_write_byte_store;exact Full.
Qed.

End Nesting.

Section Nesting.
Variables pc po pi:progunit.
Variable ip:intunit.
Variable T:tasks.
Variable cst:clientst.
Variable t:tid.
Variable ks:stmtcont.
Variables ge le:env.
Variable les:cltenvs.
Variable ir:isr.
Variable aus:ltaskstset.
Variable si:is.
Variable cs:cs.
Variable ph:hprog.
Variable Th:tasks.
Variable O:osabst.
Let P:lprog:=(pc,(po,pi,ip)).
Hypothesis Local:get les t=Some le.
Hypothesis Aux:get aus t=Some((false,si,cs):localst).
Hypothesis Inside:InOS(SKIP,(kenil,ks))(pumerge po pi).
Hypothesis Cur:get O curtid=Some(oscurt t).

(* Lock evidence is required only if the updated nesting is zero. *)
Theorem V293_exit_nesting_progsim : forall M nesting lock dispatch bn n locked,
 n<256 ->locked<256 ->get le nesting=None ->get ge nesting=Some(bn,Tint8) ->
 load Tint8 M(bn,0%Z)=Some(V293_byteval n) ->
 (0<n ->exists raw,get M(bn,0%Z)=Some(true,raw)) ->
 (Nat.pred n=0 ->get le lock=None /\ exists bl,
 get ge lock=Some(bl,Tint8) /\
 load Tint8(V293_exit_decrement_memory M bn n)(bl,0%Z)=Some(V293_byteval locked)) ->
 ProgSim P(set T t(curs(if V293_exit_enabled n locked then dispatch else sskip None),(kenil,ks)))
 (ge,les,V293_exit_decrement_memory M bn n,ir,aus)ph Th O cst t ->
 ProgSim P(set T t(curs(V293_OSIntExit_nesting_dispatch nesting lock dispatch),(kenil,ks)))
 (ge,les,M,ir,aus)ph Th O cst t.
Proof.
 intros M nesting lock dispatch bn n locked Bound LockBound NL G Read Writable Lock Post.
 pose proof(V293_exit_decrement_load M bn n Bound Read)as Updated.
 pose proof(V293_success_global_byte_eq ge le(V293_exit_decrement_memory M bn n)
 nesting bn(Nat.pred n)0 ltac:(lia)ltac:(lia)NL G Updated)as NestGuard.
 unfold V293_OSIntExit_nesting_dispatch.
 eapply V293_exit_pure_progsim with(ks:=ks)
 (C':=(curs(V293_OSIntExit_decrement nesting),(kenil,kseq(V293_OSIntExit_guards nesting lock dispatch)ks)))(le:=le);
 try eassumption;try reflexivity.
 - eapply stmt_step;[reflexivity|apply sseq_step].
 - eapply V293_exit_decrement_progsim with(n:=n)(bn:=bn)(le:=le)(ks:=kseq(V293_OSIntExit_guards nesting lock dispatch)ks);try eassumption.
   + eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
   + eapply V293_exit_pure_progsim with(ks:=ks)
     (C':=(curs(V293_OSIntExit_guards nesting lock dispatch),(kenil,ks)))(le:=le);
     try eassumption;try reflexivity.
     * eapply stmt_step;[reflexivity|apply sskip_step].
     * unfold V293_OSIntExit_guards.
       destruct(Nat.eqb(Nat.pred n)0)eqn:Zero.
       -- apply Nat.eqb_eq in Zero.
          destruct(Lock Zero)as[NLock[bl[GLock ReadLock]]].
          eapply V293_exit_if_progsim with(v:=Vint32 Int.one)(take:=true)(le:=le);
          try eassumption;try reflexivity.
          pose proof(V293_success_global_byte_eq ge le(V293_exit_decrement_memory M bn n)
          lock bl locked 0 LockBound ltac:(lia)NLock GLock ReadLock)as LockGuard.
          unfold V293_exit_enabled,V293_exit_depth in Post;rewrite Zero in Post;cbn in Post.
          destruct(Nat.eqb locked 0)eqn:Locked;
          eapply V293_exit_if_progsim with(le:=le);try eassumption;try reflexivity;
          repeat rewrite tasks_set_a_set_a;exact Post.
       -- eapply V293_exit_if_progsim with(v:=Vint32 Int.zero)(take:=false)(le:=le);
          try eassumption;try reflexivity.
          unfold V293_exit_enabled,V293_exit_depth in Post;rewrite Zero in Post;repeat rewrite tasks_set_a_set_a;exact Post.
Qed.

Theorem V293_exit_nesting_disabled_progsim : forall M nesting lock dispatch bn n locked,
 n<256 ->locked<256 ->get le nesting=None ->get ge nesting=Some(bn,Tint8) ->
 load Tint8 M(bn,0%Z)=Some(V293_byteval n) ->
 (0<n ->exists raw,get M(bn,0%Z)=Some(true,raw)) ->
 (Nat.pred n=0 ->get le lock=None /\ exists bl,get ge lock=Some(bl,Tint8) /\
 load Tint8(V293_exit_decrement_memory M bn n)(bl,0%Z)=Some(V293_byteval locked)) ->
 (2<=n \/ 0<locked) ->
 ProgSim P(set T t(SKIP,(kenil,ks)))(ge,les,V293_exit_decrement_memory M bn n,ir,aus)ph Th O cst t ->
 ProgSim P(set T t(curs(V293_OSIntExit_nesting_dispatch nesting lock dispatch),(kenil,ks)))
 (ge,les,M,ir,aus)ph Th O cst t.
Proof.
 intros M nesting lock dispatch bn n locked Bound LockBound NL G Read Writable Lock Disabled Post.
 eapply V293_exit_nesting_progsim with(n:=n)(locked:=locked)(bn:=bn);try eassumption.
 assert(E:V293_exit_enabled n locked=false).
 { unfold V293_exit_enabled,V293_exit_depth.
   apply Bool.andb_false_iff;destruct Disabled as[N|L].
   - left;apply Nat.eqb_neq;lia.
   - right;apply Nat.eqb_neq;lia. }
 rewrite E;exact Post.
Qed.
End Nesting.

Section NestingDispatch.
Variables pc po pi:progunit.
Variable ip:intunit.
Variable T:tasks.
Variable cst:clientst.
Variable t:tid.
Variables ge le:env.
Variable les:cltenvs.
Variables M0 Mt:mem.
Variables nesting lock:var.
Variable bn:block.
Variable n:nat.
Let M:=V293_exit_decrement_memory M0 bn n.
Variable ir:isr.
Variable aus:ltaskstset.
Variable si:is.
Variable cs:cs.
Variable f:fid.
Variables unmap group rows high y table target:var.
Variables bt bg br bh bp bo:block.
Variables lo hi g:nat.
Variable oldhigh:memval.
Variable tp:type.
Variable value:val.
Variable ph:hprog.
Variable Th:tasks.
Variable O:osabst.
Let P:lprog:=(pc,(po,pi,ip)).
Let Mh:=V293_write_byte M bh(V293_ready_select lo hi g).
Hypothesis Bind:po f=Some(V293_OSSchedNew_function unmap group rows high y).
Hypothesis Local:get les t=Some le.
Hypothesis Aux:get aus t=Some((false,si,cs):localst).
Hypothesis Cur:get O curtid=Some(oscurt t).
Hypothesis Yu:y<>unmap.
Hypothesis Yg:y<>group.
Hypothesis Yr:y<>rows.
Hypothesis Yh:y<>high.
Hypothesis Gu:get ge unmap=Some(bt,Tarray Tint8 256).
Hypothesis Gg:get ge group=Some(bg,Tint8).
Hypothesis Gr:get ge rows=Some(br,Tarray Tint8 2).
Hypothesis Gh:get ge high=Some(bh,Tint8).
Hypothesis Reads:V293_sched_read_memory M bt bg br lo hi g.
Hypothesis High:get M(bh,0%Z)=Some(true,oldhigh).
Hypothesis Lo:lo<256.
Hypothesis Hi:hi<256.
Hypothesis Group:g=V293_ready_group lo hi.
Hypothesis Nonempty:exists p,V293_bitmap_ready lo hi p.
Hypothesis Nt:get le table=None.
Hypothesis Nh:get le high=None.
Hypothesis No:get le target=None.
Hypothesis Gt:get ge table=Some(bp,Tarray(Tptr tp)13).
Hypothesis Go:get ge target=Some(bo,Tptr tp).
Hypothesis Range:V293_ready_select lo hi g<13.
Hypothesis Table:load(Tptr tp)Mh(bp,(4*Z.of_nat(V293_ready_select lo hi g))%Z)=Some value.
Hypothesis TargetStore:store(Tptr tp)Mh(bo,0%Z)value=Some Mt.

Hypothesis Active:n<=1.
Hypothesis Nnest:get le nesting=None.
Hypothesis Gnest:get ge nesting=Some(bn,Tint8).
Hypothesis Nest:load Tint8 M0(bn,0%Z)=Some(V293_byteval n).
Hypothesis Writable:0<n ->exists raw,get M0(bn,0%Z)=Some(true,raw).
Hypothesis Lock:get le lock=None /\ exists bl,get ge lock=Some(bl,Tint8) /\
 load Tint8 M(bl,0%Z)=Some(V293_byteval 0).

Theorem V293_exit_nesting_dispatch_progsim : forall next current counter ks M1 Mc Mf
 bk count b v bc Thf Of,
 get T t=Some(curs(V293_OSIntExit_nesting_dispatch nesting lock
 (V293_exit_boundary_dispatch table high target current counter f
 (V293_interrupt_handoff high current target))),(kenil,ks)) ->
 InOS(SKIP,(kenil,ks))(pumerge po pi) ->
 evalval(V293_OSSched_different high current)(ge,le,Mt)=Some(Vint32 Int.one) ->
 get le counter=None ->get ge counter=Some(bk,Tint32) ->
 load Tint32 Mt(bk,0%Z)=Some(Vint32 count) ->
 store Tint32 Mt(bk,0%Z)(Vint32(Int.add count Int.one))=Some M1 ->
 evaltype(evar current)(ge,le,M1)=Some Tint8 ->
 evaltype(evar high)(ge,le,M1)=Some Tint8 ->
 evalval(evar high)(ge,le,M1)=Some v ->
 evalval(eaddrof(evar current))(ge,le,M1)=Some(Vptr(b,Int.zero)) ->
 store Tint8 M1(b,0%Z)v=Some Mc ->
 load(Tptr tp)Mc(bo,0%Z)=Some(Vptr next) ->
 get ge OSTCBCur=Some(bc,Tptr tp) ->
 store(Tptr tp)Mc(bc,0%Z)(Vptr next)=Some Mf ->
 hpstepstar ph Th cst O Thf cst Of ->
 ProgSim P(set T t(SKIP,(kenil,ks)))(ge,les,Mf,ir,aus)ph Thf Of cst next ->
 ProgSim P T(ge,les,M0,ir,aus)ph Th O cst t.
Proof.
 intros next current counter ks M1 Mc Mf bk count b v bc Thf Of Code Inside Guard
 Ncounter Gcounter Counter Increment CurrentType HighType HighValue Address Copy
 Target Current Store Match Post.
 rewrite <-(TasksMod.get_set_same Code)at 1.
 eapply V293_exit_nesting_progsim with(le:=le)(bn:=bn)(n:=n)(locked:=0)(si:=si)(cs:=cs);
 try eassumption;try lia.
 - intros _;exact Lock.
 - assert(E:V293_exit_enabled n 0=true).
   { apply V293_exit_enabled_iff;auto. }
   rewrite E.
   eapply V293_exit_call_dispatch_progsim with(le:=le)(si:=si)(cs:=cs)
   (M:=M)(Mt:=Mt)(next:=next)(ks:=ks)(M1:=M1)(Mc:=Mc)(Mf:=Mf)
   (f:=f)(unmap:=unmap)(group:=group)(rows:=rows)(high:=high)(y:=y)
   (table:=table)(target:=target)(bt:=bt)(bg:=bg)(br:=br)(bh:=bh)(bp:=bp)(bo:=bo)
   (lo:=lo)(hi:=hi)(g:=g)(oldhigh:=oldhigh)(tp:=tp)(value:=value)
   (bk:=bk)(count:=count)(b:=b)(v:=v)(bc:=bc)(Thf:=Thf)(Of:=Of);
   try eassumption.
   + apply map_get_set.
   + repeat rewrite tasks_set_a_set_a;exact Post.
Qed.
End NestingDispatch.
