(* Full normalized active call. Existing target pending is consumed;
   final caller simulation and physical resources remain explicit. *)
Require Import CertiOS.certiucos.v293.proofs.V293ExitQuietCallProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293ResumedReturnProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyFullCall.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCallGlobal.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturnProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293ExitNestingProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBoundarySwitch.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293SchedCallEntryProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293HandoffProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293ExitDispatchProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.code.V293OSIntEnter.
Require Import CertiOS.certiucos.v293.code.V293OSIntExit.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.simulation.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.framework.proof.step_prop.
Require Import CertiOS.framework.auxlibs.MapLib.
Require Import Coq.Lists.List Lia.
Local Open Scope nat_scope.

Lemma V293_exit_active_critical_prefix_progsim :
 forall pc po pi ip T cst t ks ge le les M ir aus si cs nesting lock dispatch bn n ph Th O,
 get les t=Some le ->get aus t=Some((false,si,cs):localst) ->
 InOS(SKIP,(kenil,ks))(pumerge po pi) ->get O curtid=Some(oscurt t) ->
 n<=1 ->get le nesting=None ->get ge nesting=Some(bn,Tint8) ->
 load Tint8 M(bn,0%Z)=Some(V293_byteval n) ->
 (0<n ->exists raw,get M(bn,0%Z)=Some(true,raw)) ->
 get le lock=None ->
 (exists bl,get ge lock=Some(bl,Tint8) /\
 load Tint8(V293_exit_decrement_memory M bn n)(bl,0%Z)=Some(V293_byteval 0)) ->
 ProgSim(pc,(po,pi,ip))
 (set T t(curs dispatch,(kenil,kseq(sprim excrit)ks)))
 (ge,les,V293_exit_decrement_memory M bn n,ir,set aus t(false,si,false::cs))ph Th O cst t ->
 ProgSim(pc,(po,pi,ip))(set T t(curs(sseq(sprim encrit)
 (sseq(V293_OSIntExit_nesting_dispatch nesting lock dispatch)(sprim excrit))),(kenil,ks)))
 (ge,les,M,ir,aus)ph Th O cst t.
Proof.
 intros pc po pi ip T cst t ks ge le les M ir aus si cs nesting lock dispatch bn n ph Th O
 Local Aux Inside Cur Active NL GN Nest Writable NK Lock Post.
 set(A:=set aus t(false,si,false::cs)).
 assert(Pushed:get A t=Some((false,si,false::cs):localst))by(apply map_get_set).
 eapply V293_exit_pure_progsim with(ks:=ks)(le:=le)
 (C':=(curs(sprim encrit),(kenil,kseq(sseq(V293_OSIntExit_nesting_dispatch nesting lock dispatch)(sprim excrit))ks)));
 try eassumption;try reflexivity.
 - eapply stmt_step;[reflexivity|apply sseq_step].
 - eapply V293_encrit_progsim with(le:=le)(si:=si)(cs:=cs);try eassumption.
   + eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
   + change(ProgSim(pc,(po,pi,ip))
     (set T t(SKIP,(kenil,kseq(sseq(V293_OSIntExit_nesting_dispatch nesting lock dispatch)(sprim excrit))ks)))
     (ge,les,M,ir,A)ph Th O cst t).
     eapply V293_exit_pure_progsim with(ks:=ks)(le:=le)
     (C':=(curs(sseq(V293_OSIntExit_nesting_dispatch nesting lock dispatch)(sprim excrit)),(kenil,ks)));
     try eassumption;try reflexivity.
     * eapply stmt_step;[reflexivity|apply sskip_step].
     * eapply V293_exit_pure_progsim with(ks:=ks)(le:=le)
       (C':=(curs(V293_OSIntExit_nesting_dispatch nesting lock dispatch),(kenil,kseq(sprim excrit)ks)));
       try eassumption;try reflexivity.
       -- eapply stmt_step;[reflexivity|apply sseq_step].
       -- eapply V293_exit_nesting_progsim with(le:=le)(si:=si)(cs:=false::cs)
          (bn:=bn)(n:=n)(locked:=0);try eassumption;try lia.
          ++ eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
          ++ intros _;split;assumption.
          ++ assert(E:V293_exit_enabled n 0=true)by(apply V293_exit_enabled_iff;auto).
             rewrite E;exact Post.
Qed.

Lemma V293_exit_active_body_prefix_progsim :
 forall pc po pi ip T cst t ge le caller les M Mz ir aus si cs f ks bs
 running nesting lock saved table high target current counter sched bn n ph Th O,
 let handoff:=V293_interrupt_handoff high current target in
 let body:=V293_exit_boundary_body running nesting lock saved table high target current counter sched handoff in
 let pending:=kseq(sprim excrit)(kseq sret(kcall f body caller ks)) in
 get les t=Some le ->get aus t=Some((false,si,cs):localst) ->
 InOS(SKIP,(kenil,kcall f body caller ks))(pumerge po pi) ->get O curtid=Some(oscurt t) ->
 get le saved=Some(bs,Tint32) ->store Tint32 M(bs,0%Z)(Vint32 Int.zero)=Some Mz ->
 evalval(V293_OSIntEnter_running running)(ge,le,Mz)=Some(Vint32 Int.one) ->
 n<=1 ->get le nesting=None ->get ge nesting=Some(bn,Tint8) ->
 load Tint8 Mz(bn,0%Z)=Some(V293_byteval n) ->
 (0<n ->exists raw,get Mz(bn,0%Z)=Some(true,raw)) ->get le lock=None ->
 (exists bl,get ge lock=Some(bl,Tint8) /\
 load Tint8(V293_exit_decrement_memory Mz bn n)(bl,0%Z)=Some(V293_byteval 0)) ->
 ProgSim(pc,(po,pi,ip))(set T t(curs(V293_exit_boundary_dispatch table high target current counter sched handoff),(kenil,pending)))
 (ge,les,V293_exit_decrement_memory Mz bn n,ir,set aus t(false,si,false::cs))ph Th O cst t ->
 ProgSim(pc,(po,pi,ip))(set T t(curs body,(kenil,kcall f body caller ks)))
 (ge,les,M,ir,aus)ph Th O cst t.
Proof.
 intros pc po pi ip T cst t ge le caller les M Mz ir aus si cs f ks bs
 running nesting lock saved table high target current counter sched bn n ph Th O
 handoff body pending Local Aux Inside Cur Saved Store Guard Active NL GN Nest Writable NK Lock Post.
 set(critical:=sseq(sprim encrit)(sseq(V293_OSIntExit_nesting_dispatch nesting lock
 (V293_exit_boundary_dispatch table high target current counter sched handoff))(sprim excrit))).
 change(ProgSim(pc,(po,pi,ip))(set T t(curs(sseq(sassign(evar saved)(econst32 Int.zero))
 (sseq(sifthen(V293_OSIntEnter_running running)critical)sret)),(kenil,kcall f body caller ks)))
 (ge,les,M,ir,aus)ph Th O cst t).
 eapply V293_exit_pure_progsim with(le:=le)(ks:=kcall f body caller ks)
 (C':=(curs(sassign(evar saved)(econst32 Int.zero)),
 (kenil,kseq(sseq(sifthen(V293_OSIntEnter_running running)critical)sret)(kcall f body caller ks))));
 try eassumption;try reflexivity.
 - eapply stmt_step;[reflexivity|apply sseq_step].
 - eapply V293_assign_word_progsim with(le:=le)(b:=bs)(v:=Vint32 Int.zero)(M':=Mz);
   try eassumption;try reflexivity.
   + eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
   + cbn[evaltype get_lenv];rewrite Saved;reflexivity.
   + cbn[evaladdr get_lenv];rewrite Saved;reflexivity.
   + eapply V293_exit_pure_progsim with(le:=le)(ks:=kcall f body caller ks)
     (C':=(curs(sseq(sifthen(V293_OSIntEnter_running running)critical)sret),(kenil,kcall f body caller ks)));
     try eassumption;try reflexivity.
     * eapply stmt_step;[reflexivity|apply sskip_step].
     * eapply V293_exit_pure_progsim with(le:=le)(ks:=kcall f body caller ks)
       (C':=(curs(sifthen(V293_OSIntEnter_running running)critical),(kenil,kseq sret(kcall f body caller ks))));
       try eassumption;try reflexivity.
       -- eapply stmt_step;[reflexivity|apply sseq_step].
       -- eapply V293_exit_ifthen_progsim with(le:=le)(v:=Vint32 Int.one)(take:=true);try eassumption;try reflexivity.
          ++ eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
          ++ unfold critical;eapply V293_exit_active_critical_prefix_progsim with(le:=le)(bn:=bn)(n:=n);try eassumption.
             eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
Qed.

Section CompleteActiveCall.
Variables pc po pi:progunit.
Variable ip:intunit.
Variable T:tasks.
Variable cst:clientst.
Variables t next:tid.
Variables ge caller:env.
Variable les:cltenvs.
Variable M:mem.
Variable ir:isr.
Variable aus:ltaskstset.
Variable si:is.
Variable cs:cs.
Variables f sched exitf:fid.
Variable ks:stmtcont.
Variables running nesting lock saved unmap group rows high y table target current counter:var.
Variables bt bg br bh bp bo bn bk bcache bc:block.
Variables lo hi g n:nat.
Variable count:int32.
Variable tp:type.
Variables value v:val.
Variable nextbody:stmts.
Variable nextcaller:env.
Variable nexttail:stmtcont.
Variable nexttau:type.
Variables nextd1 nextd2:decllist.
Variables nextsaved:var.
Variable nextbs:block.
Variable nsi:is.
Variable ncs:language.cs.
Variable ph:hprog.
Variables Th Thf:tasks.
Variables O Of:osabst.
Let handoff:=V293_interrupt_handoff high current target.
Let body:=V293_exit_boundary_body running nesting lock saved table high target current counter sched handoff.
Let pending:=kseq(sprim excrit)(kseq sret(kcall f body caller ks)).
Let P:lprog:=(pc,(po,pi,ip)).
Hypothesis Bind:po f=Some(V293_exit_boundary_function running nesting lock saved table high target current counter sched handoff).
Hypothesis Schedule:po sched=Some(V293_OSSchedNew_function unmap group rows high y).
Hypothesis Local:get les t=Some caller.
Hypothesis Aux:get aus t=Some((false,si,cs):localst).
Hypothesis Cur:get O curtid=Some(oscurt t).
Hypothesis Different:t<>next.
Hypothesis Pending:get T next=Some(SKIP,(kenil,kseq(sprim excrit)(kseq sret(kcall exitf nextbody nextcaller nexttail)))).
Hypothesis NextBind:po exitf=Some(nexttau,nextd1,nextd2,nextbody).
Hypothesis NextLocal:get les next=Some(V293_cpu_lenv nextsaved nextbs).
Hypothesis NextAux:get aus next=Some((false,nsi,false::ncs):localst).
Hypothesis NextCur:get Of curtid=Some(oscurt next).
Hypothesis Match:hpstepstar ph Th cst O Thf cst Of.
Hypothesis Yu:y<>unmap.
Hypothesis Yg:y<>group.
Hypothesis Yr:y<>rows.
Hypothesis Yh:y<>high.
Hypothesis Gu:get ge unmap=Some(bt,Tarray Tint8 256).
Hypothesis Gg:get ge group=Some(bg,Tint8).
Hypothesis Gr:get ge rows=Some(br,Tarray Tint8 2).
Hypothesis Gh:get ge high=Some(bh,Tint8).
Hypothesis Gt:get ge table=Some(bp,Tarray(Tptr tp)13).
Hypothesis Go:get ge target=Some(bo,Tptr tp).
Hypothesis Gn:get ge nesting=Some(bn,Tint8).
Hypothesis Gcounter:get ge counter=Some(bk,Tint32).
Hypothesis Gcurrent:get ge OSTCBCur=Some(bc,Tptr tp).
Hypothesis Sn:saved<>nesting.
Hypothesis Sl:saved<>lock.
Hypothesis St:saved<>table.
Hypothesis Sh:saved<>high.
Hypothesis So:saved<>target.
Hypothesis Sk:saved<>counter.
Hypothesis Active:n<=1.
Hypothesis Lo:lo<256.
Hypothesis Hi:hi<256.
Hypothesis Group:g=V293_ready_group lo hi.
Hypothesis Nonempty:exists p,V293_bitmap_ready lo hi p.
Hypothesis Range:V293_ready_select lo hi g<13.

(* One resource witness for EVERY possible local allocation, not one chosen
   allocator result. Only the final selected caller simulation is required. *)
Theorem V293_exit_active_call_progsim : forall entry,
 get T t=Some(curs entry,(kenil,ks)) ->
 (entry=sfexec f nil nil \/ (entry=scall f nil /\ InOS(SKIP,(kenil,ks))(pumerge po pi))) ->
 (forall bs,fresh M bs ->exists Mz Mt M1 Mc Msw Mret oldhigh,
 store Tint32(allocb M bs 0%Z 4)(bs,0%Z)(Vint32 Int.zero)=Some Mz /\
 evalval(V293_OSIntEnter_running running)(ge,V293_cpu_lenv saved bs,Mz)=Some(Vint32 Int.one) /\
 load Tint8 Mz(bn,0%Z)=Some(V293_byteval n) /\
 (0<n ->exists raw,get Mz(bn,0%Z)=Some(true,raw)) /\
 (exists bl,get ge lock=Some(bl,Tint8) /\
 load Tint8(V293_exit_decrement_memory Mz bn n)(bl,0%Z)=Some(V293_byteval 0)) /\
 V293_sched_read_memory(V293_exit_decrement_memory Mz bn n)bt bg br lo hi g /\
 get(V293_exit_decrement_memory Mz bn n)(bh,0%Z)=Some(true,oldhigh) /\
 load(Tptr tp)(V293_write_byte(V293_exit_decrement_memory Mz bn n)bh(V293_ready_select lo hi g))
 (bp,(4*Z.of_nat(V293_ready_select lo hi g))%Z)=Some value /\
 store(Tptr tp)(V293_write_byte(V293_exit_decrement_memory Mz bn n)bh(V293_ready_select lo hi g))
 (bo,0%Z)value=Some Mt /\
 evalval(V293_OSSched_different high current)(ge,V293_cpu_lenv saved bs,Mt)=Some(Vint32 Int.one) /\
 load Tint32 Mt(bk,0%Z)=Some(Vint32 count) /\
 store Tint32 Mt(bk,0%Z)(Vint32(Int.add count Int.one))=Some M1 /\
 evaltype(evar current)(ge,V293_cpu_lenv saved bs,M1)=Some Tint8 /\
 evaltype(evar high)(ge,V293_cpu_lenv saved bs,M1)=Some Tint8 /\
 evalval(evar high)(ge,V293_cpu_lenv saved bs,M1)=Some v /\
 evalval(eaddrof(evar current))(ge,V293_cpu_lenv saved bs,M1)=Some(Vptr(bcache,Int.zero)) /\
 store Tint8 M1(bcache,0%Z)v=Some Mc /\
 load(Tptr tp)Mc(bo,0%Z)=Some(Vptr next) /\
 store(Tptr tp)Mc(bc,0%Z)(Vptr next)=Some Msw /\
 free Tint32 nextbs Msw=Some Mret /\
 ProgSim P(set(set T t(SKIP,(kenil,pending)))next(SKIP,(kenil,nexttail)))
 (ge,set(set les t(V293_cpu_lenv saved bs))next nextcaller,Mret,ir,
 set(set aus t(false,si,false::cs))next(false,nsi,ncs))ph Thf Of cst next) ->
 ProgSim P T(ge,les,M,ir,aus)ph Th O cst t.
Proof.
 intros entry Code Mode Resources.
 eapply V293_saved_call_entry_progsim with(saved:=saved)(body:=body);try eassumption.
 intros bs Fresh.
 destruct(Resources bs Fresh)as(Mz&Mt&M1&Mc&Msw&Mret&oldhigh&Init&Running&Nest&Writable&Lock&Reads&High&Table&TargetStore&Guard&Counter&Increment&CurrentType&HighType&HighValue&Address&Copy&Target&Store&Free&Post).
 assert(NotLocal:forall x,saved<>x ->get(V293_cpu_lenv saved bs)x=None).
 { intros x Ne;unfold V293_cpu_lenv;rewrite map_get_set' by congruence;apply map_emp_get. }
 eapply V293_exit_active_body_prefix_progsim with(le:=V293_cpu_lenv saved bs)
 (Mz:=Mz)(bs:=bs)(bn:=bn)(n:=n);try eassumption.
 - apply map_get_set.
 - eapply V293_bound_call_inos;exact Bind.
 - unfold V293_cpu_lenv;apply map_get_set.
 - apply NotLocal;exact Sn.
 - apply NotLocal;exact Sl.
 - eapply V293_exit_call_resume_progsim with(le:=V293_cpu_lenv saved bs)
   (M:=V293_exit_decrement_memory Mz bn n)(Mt:=Mt)(M1:=M1)(Mc:=Mc)(Mf:=Msw)
   (next:=next)(current:=current)(counter:=counter)(ks:=pending)
   (bk:=bk)(count:=count)(b:=bcache)(v:=v)(bc:=bc)(Thf:=Thf)(Of:=Of)
   (f:=sched)(unmap:=unmap)(group:=group)(rows:=rows)(high:=high)(y:=y)(table:=table)(target:=target)
   (bt:=bt)(bg:=bg)(br:=br)(bh:=bh)(bp:=bp)(bo:=bo)(lo:=lo)(hi:=hi)(g:=g)
   (oldhigh:=oldhigh)(value:=value)(tp:=tp)(si:=si)(cs:=false::cs)
   (exitf:=exitf)(body:=nextbody)(caller:=nextcaller)(tail:=nexttail)(tau:=nexttau)
   (d1:=nextd1)(d2:=nextd2)(saved:=nextsaved)(bs:=nextbs)(nsi:=nsi)(ncs:=ncs)(Mret:=Mret);
   try eassumption;try(apply map_get_set).
   + apply NotLocal;exact St.
   + apply NotLocal;exact Sh.
   + apply NotLocal;exact So.
   + eapply V293_context_inos;[eapply V293_bound_call_inos;exact Bind|reflexivity|reflexivity].
   + apply NotLocal;exact Sk.
   + rewrite map_get_set' by congruence;exact Pending.
   + rewrite map_get_set' by congruence;exact NextLocal.
   + rewrite map_get_set' by congruence;exact NextAux.
   + repeat rewrite tasks_set_a_set_a;exact Post.
Qed.
End CompleteActiveCall.
