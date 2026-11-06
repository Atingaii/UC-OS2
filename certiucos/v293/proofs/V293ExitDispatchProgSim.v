(* Actual OSIntExit comparison and modular counter prefix. The simulation
   crosses all successors, not merely a selected terminating source trace. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.simulation.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.framework.proof.step_prop.
Require Import CertiOS.framework.auxlibs.MapLib.
Require Import CertiOS.certiucos.v293.proofs.V293HandoffProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBoundarySwitch.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293ReadySourceTail.

Lemma V293_exit_pure_progsim : forall pc po pi ip T cst t ks C C' ge le les M ir aus si cs ph Th O,
 get les t=Some le ->get aus t=Some((false,si,cs):localst) ->
 InOS(SKIP,(kenil,ks))(pumerge po pi) ->
 callcont(snd(snd C))=callcont ks ->intcont(snd(snd C))=intcont ks ->
 cstep(pumerge po pi)C(ge,le,M)C'(ge,le,M) ->
 get O curtid=Some(oscurt t) ->
 ProgSim(pc,(po,pi,ip))(set T t C')(ge,les,M,ir,aus)ph Th O cst t ->
 ProgSim(pc,(po,pi,ip))(set T t C)(ge,les,M,ir,aus)ph Th O cst t.
Proof.
 intros pc po pi ip T cst t ks [c [ke kk]] C' ge le les M ir aus si cs ph Th O
 Local Aux Context Call Interrupt Step Cur Post.
 eapply V293_os_silent_progsim with(C:=(c,(ke,kk)))(C':=C')(le:=le);try eassumption.
 - apply map_get_set.
 - eapply V293_context_inos;[exact Context|exact Call|exact Interrupt].
 - intros Cf mf Other;destruct(cstep_idmove_deter _ _ _ _ _ _ Step Other)as[A B];split;symmetry;assumption.
 - rewrite tasks_set_a_set_a;exact Post.
Qed.

Lemma V293_exit_expr_progsim : forall c ke m c' ke' m',
 estepstar c ke m c' ke' m' ->
 forall pc po pi ip T cst t ks ge le les M ir aus si cs ph Th O,
 m=(ge,le,M) ->get les t=Some le ->get aus t=Some((false,si,cs):localst) ->
 InOS(SKIP,(kenil,ks))(pumerge po pi) ->get O curtid=Some(oscurt t) ->
 ProgSim(pc,(po,pi,ip))(set T t(c',(ke',ks)))(ge,les,M,ir,aus)ph Th O cst t ->
 ProgSim(pc,(po,pi,ip))(set T t(c,(ke,ks)))(ge,les,M,ir,aus)ph Th O cst t.
Proof.
 intros c ke m c' ke' m' Steps;induction Steps as
 [c ke m|c ke m c1 ke1 m1 c2 ke2 m2 Step Rest IH];
 intros pc po pi ip T cst t ks ge le les M ir aus si cs ph Th O Eq Local Aux Context Cur Post.
 - exact Post.
 - pose proof(cstepLib.estep_mem_same _ _ _ _ _ _ Step)as Same;subst m1;subst m.
   eapply V293_exit_pure_progsim with(ks:=ks)(C':=(c1,(ke1,ks)))(le:=le);
   try eassumption;try reflexivity.
   + eapply expr_step;[reflexivity|exact Step].
   + eapply IH;try eassumption;reflexivity.
Qed.

Section Prefix.
Variables pc po pi:progunit.
Variable ip:intunit.
Variable T:tasks.
Variable cst:clientst.
Variable t:tid.
Variable ks:stmtcont.
Variables ge le:env.
Variable les:cltenvs.
Variables ir:isr.
Variable aus:ltaskstset.
Variable si:is.
Variable cs:cs.
Variables ph:hprog.
Variable Th:tasks.
Variable O:osabst.
Let P:lprog:=(pc,(po,pi,ip)).
Hypothesis Local:get les t=Some le.
Hypothesis Aux:get aus t=Some((false,si,cs):localst).
Hypothesis Context:InOS(SKIP,(kenil,ks))(pumerge po pi).
Hypothesis Cur:get O curtid=Some(oscurt t).

Lemma V293_exit_if_progsim : forall M e yes no v take,
 evalval e(ge,le,M)=Some v ->istrue v=Some take ->
 ProgSim P(set T t(curs(if take then yes else no),(kenil,ks)))(ge,les,M,ir,aus)ph Th O cst t ->
 ProgSim P(set T t(curs(sif e yes no),(kenil,ks)))(ge,les,M,ir,aus)ph Th O cst t.
Proof.
 intros M e yes no v take Eval Truth Post.
 eapply V293_exit_pure_progsim with(ks:=ks)(C':=(cure e,(kenil,kif yes no ks)))(le:=le);
 try eassumption;try reflexivity.
 - eapply stmt_step;[reflexivity|apply sif_step].
 - eapply V293_exit_expr_progsim with(m:=(ge,le,M))(m':=(ge,le,M))
   (c':=curs(sskip(Some v)))(ke':=kenil)(le:=le);try eassumption;try reflexivity.
   + apply cstepLib.evalval_imply_estepstar;exact Eval.
   + eapply V293_context_inos;[exact Context|reflexivity|reflexivity].
   + eapply V293_exit_pure_progsim with(ks:=ks)
     (C':=(curs(if take then yes else no),(kenil,ks)))(le:=le);
     try eassumption;try reflexivity.
     eapply stmt_step;[reflexivity| ];destruct take;
     [apply svift_step|apply sviff_step];exact Truth.
Qed.

Lemma V293_exit_increment_progsim : forall M M' counter b c pending,
 get le counter=None ->get ge counter=Some(b,Tint32) ->
 load Tint32 M(b,0%Z)=Some(Vint32 c) ->
 store Tint32 M(b,0%Z)(Vint32(Int.add c Int.one))=Some M' ->
 callcont pending=callcont ks ->intcont pending=intcont ks ->
 ProgSim P(set T t(SKIP,(kenil,pending)))(ge,les,M',ir,aus)ph Th O cst t ->
 ProgSim P(set T t(curs(V293_OSSched_increment counter),(kenil,pending)))(ge,les,M,ir,aus)ph Th O cst t.
Proof.
 intros M M' counter b c pending NotLocal Global Read Store Call Interrupt Post.
 destruct(V293_ready_counter_eval ge le M counter b c NotLocal Global Read)as[Left[Right[Address Value]]].
 assert(Inside:InOS(SKIP,(kenil,pending))(pumerge po pi)).
 { eapply V293_context_inos;[exact Context|exact Call|exact Interrupt]. }
 unfold V293_OSSched_increment.
 eapply V293_exit_pure_progsim with(ks:=pending)
 (C':=(cure(ebinop oplus(evar counter)(econst32 Int.one)),(kenil,kassignr(evar counter)Tint32 pending)))
 (le:=le);try eassumption;try reflexivity.
 - eapply stmt_step;[reflexivity| ];eapply sassign_step;try eassumption;apply eq_int;auto.
 - eapply V293_exit_expr_progsim with(m:=(ge,le,M))(m':=(ge,le,M))
   (c':=curs(sskip(Some(Vint32(Int.add c Int.one)))))(ke':=kenil)(le:=le);
   try eassumption;try reflexivity.
   + apply cstepLib.evalval_imply_estepstar;exact Value.
   + eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
   + eapply V293_exit_pure_progsim with(ks:=pending)
     (C':=(cure(eaddrof(evar counter)),(kenil,kassignl(Vint32(Int.add c Int.one))Tint32 pending)))
     (le:=le);try eassumption;try reflexivity.
     * eapply stmt_step;[reflexivity|apply sassignrv_step].
     * eapply V293_exit_expr_progsim with(m:=(ge,le,M))(m':=(ge,le,M))
       (c':=curs(sskip(Some(Vptr(b,Int.zero)))))(ke':=kenil)(le:=le);
       try eassumption;try reflexivity.
       -- apply cstepLib.evaladdr_imply_estepstar;exact Address.
       -- eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
       -- eapply V293_os_silent_progsim with
          (C:=(curs(sskip(Some(Vptr(b,Int.zero)))),(kenil,kassignl(Vint32(Int.add c Int.one))Tint32 pending)))
          (C':=(SKIP,(kenil,pending)))(le:=le)(M':=M');try eassumption.
          ++ apply map_get_set.
          ++ eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
          ++ eapply stmt_step;[reflexivity| ];eapply sassignend_step;try reflexivity;exact Store.
          ++ intros Cf mf Other;eapply V293_store_cstep_unique;[exact Store|exact Other].
          ++ rewrite tasks_set_a_set_a;exact Post.
Qed.

(* This is exactly the source changed branch before the explicit handoff.
   No invariant is demanded at the intervening copy/switch transient. *)
Theorem V293_exit_changed_prefix_progsim : forall M M' high current counter handoff b c,
 evalval(V293_OSSched_different high current)(ge,le,M)=Some(Vint32 Int.one) ->
 get le counter=None ->get ge counter=Some(b,Tint32) ->
 load Tint32 M(b,0%Z)=Some(Vint32 c) ->
 store Tint32 M(b,0%Z)(Vint32(Int.add c Int.one))=Some M' ->
 ProgSim P(set T t(curs handoff,(kenil,ks)))(ge,les,M',ir,aus)ph Th O cst t ->
 ProgSim P(set T t(curs(sif(V293_OSSched_different high current)
 (sseq(V293_OSSched_increment counter)(sseq(sskip None)handoff))(sskip None)),(kenil,ks)))
 (ge,les,M,ir,aus)ph Th O cst t.
Proof.
 intros M M' high current counter handoff b c Guard NotLocal Global Read Store Post.
 eapply V293_exit_if_progsim with(v:=Vint32 Int.one)(take:=true);try eassumption;try reflexivity.
 eapply V293_exit_pure_progsim with(ks:=ks)
 (C':=(curs(V293_OSSched_increment counter),(kenil,kseq(sseq(sskip None)handoff)ks)))(le:=le);
 try eassumption;try reflexivity.
 - eapply stmt_step;[reflexivity|apply sseq_step].
 - eapply V293_exit_increment_progsim;try eassumption;try reflexivity.
   eapply V293_exit_pure_progsim with(ks:=ks)
   (C':=(curs(sseq(sskip None)handoff),(kenil,ks)))(le:=le);
   try eassumption;try reflexivity.
   + eapply stmt_step;[reflexivity|apply sskip_step].
   + eapply V293_exit_pure_progsim with(ks:=ks)
     (C':=(SKIP,(kenil,kseq handoff ks)))(le:=le);
     try eassumption;try reflexivity.
     * eapply stmt_step;[reflexivity|apply sseq_step].
     * eapply V293_exit_pure_progsim with(ks:=ks)
       (C':=(curs handoff,(kenil,ks)))(le:=le);
       try eassumption;try reflexivity.
       eapply stmt_step;[reflexivity|apply sskip_step].
Qed.
End Prefix.

(* Stable interface: the actual unequal branch, increment, copy and original
   switch, retaining the same continuation and an arbitrary resumed task. *)
Theorem V293_exit_dispatch_progsim : forall pc po pi ip T cst t next
 high current counter target ks ge le les M M1 Mc Mf ir aus si cs
 bk c b v bt bc tp ph Th O Thf Of,
 get les t=Some le ->get aus t=Some((false,si,cs):localst) ->
 get T t=Some((curs(sif(V293_OSSched_different high current)
 (sseq(V293_OSSched_increment counter)
   (sseq(sskip None)(V293_interrupt_handoff high current target)))(sskip None)),(kenil,ks)):code) ->
 InOS(SKIP,(kenil,ks))(pumerge po pi) ->
 evalval(V293_OSSched_different high current)(ge,le,M)=Some(Vint32 Int.one) ->
 get le counter=None ->get ge counter=Some(bk,Tint32) ->
 load Tint32 M(bk,0%Z)=Some(Vint32 c) ->
 store Tint32 M(bk,0%Z)(Vint32(Int.add c Int.one))=Some M1 ->
 evaltype(evar current)(ge,le,M1)=Some Tint8 ->
 evaltype(evar high)(ge,le,M1)=Some Tint8 ->
 evalval(evar high)(ge,le,M1)=Some v ->
 evalval(eaddrof(evar current))(ge,le,M1)=Some(Vptr(b,Int.zero)) ->
 store Tint8 M1(b,0%Z)v=Some Mc ->
 get ge target=Some(bt,Tptr tp) ->
 load(Tptr tp)Mc(bt,0%Z)=Some(Vptr next) ->
 get ge OSTCBCur=Some(bc,Tptr tp) ->
 store(Tptr tp)Mc(bc,0%Z)(Vptr next)=Some Mf ->
 get O curtid=Some(oscurt t) ->
 hpstepstar ph Th cst O Thf cst Of ->
 ProgSim(pc,(po,pi,ip))(set T t(SKIP,(kenil,ks)))(ge,les,Mf,ir,aus)ph Thf Of cst next ->
 ProgSim(pc,(po,pi,ip))T(ge,les,M,ir,aus)ph Th O cst t.
Proof.
 intros pc po pi ip T cst t next high current counter target ks ge le les M M1 Mc Mf
 ir aus si cs bk c b v bt bc tp ph Th O Thf Of Local Aux Code Context Guard
 CounterLocal CounterGlobal CounterRead Increment CurrentType HighType HighRead
 CurrentAddress Copy Target Read Current Store Cur Match Post.
 rewrite <-(TasksMod.get_set_same Code)at 1.
 eapply V293_exit_changed_prefix_progsim with(le:=le)(M':=M1)(b:=bk)(c:=c);
 try eassumption.
 eapply V293_handoff_progsim with(high:=high)(current:=current)(target:=target)(le:=le)(Mc:=Mc)(Mf:=Mf)(next:=next)
 (b:=b)(v:=v)(bt:=bt)(bc:=bc)(tp:=tp)(Thf:=Thf)(Of:=Of);
 try eassumption.
 - apply map_get_set.
 - rewrite tasks_set_a_set_a;exact Post.
Qed.

(* The equal source branch changes neither the heap nor the current task.
   The changed suffix is syntactically present, but is not executed. *)
Theorem V293_exit_same_progsim : forall pc po pi ip T cst t high current yes ks
 ge le les M ir aus si cs ph Th O,
 get les t=Some le ->get aus t=Some((false,si,cs):localst) ->
 get T t=Some((curs(sif(V293_OSSched_different high current)yes(sskip None)),(kenil,ks)):code) ->
 InOS(SKIP,(kenil,ks))(pumerge po pi) ->
 evalval(V293_OSSched_different high current)(ge,le,M)=Some(Vint32 Int.zero) ->
 get O curtid=Some(oscurt t) ->
 ProgSim(pc,(po,pi,ip))(set T t(SKIP,(kenil,ks)))(ge,les,M,ir,aus)ph Th O cst t ->
 ProgSim(pc,(po,pi,ip))T(ge,les,M,ir,aus)ph Th O cst t.
Proof.
 intros pc po pi ip T cst t high current yes ks ge le les M ir aus si cs ph Th O
 Local Aux Code Context Guard Cur Post.
 rewrite <-(TasksMod.get_set_same Code)at 1.
 eapply V293_exit_if_progsim with(le:=le)(v:=Vint32 Int.zero)(take:=false);
 try eassumption;reflexivity.
Qed.
