(* Consume an existing suspended OSIntExit continuation. The caller post
   remains explicit; no fairness or automatic schedule-back is assumed. *)
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturnProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293ExitCallDispatchProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293SwitchProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyFullCall.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCallGlobal.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.simulation.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.framework.proof.step_prop.
Require Import CertiOS.framework.auxlibs.MapLib.
Require Import CertiOS.certiucos.v293.proofs.V293SchedCallEntryProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293ExitDispatchProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293HandoffProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293SchedCallProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBoundarySwitch.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.certiucos.v293.code.V293OSSchedDispatch.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import Coq.Lists.List.

Theorem V293_pending_exit_progsim :
 forall pc po pi ip T cst t ge les M Mf ir aus si cs f body caller tail
 tau d1 d2 saved b ph Th O,
 po f=Some(tau,d1,d2,body) ->
 get T t=Some(SKIP,(kenil,kseq(sprim excrit)(kseq sret(kcall f body caller tail)))) ->
 get les t=Some(V293_cpu_lenv saved b) ->
 get aus t=Some((false,si,false::cs):localst) ->
 free Tint32 b M=Some Mf ->get O curtid=Some(oscurt t) ->
 ProgSim(pc,(po,pi,ip))(set T t(SKIP,(kenil,tail)))
 (ge,set les t caller,Mf,ir,set aus t(false,si,cs))ph Th O cst t ->
 ProgSim(pc,(po,pi,ip))T(ge,les,M,ir,aus)ph Th O cst t.
Proof.
 intros pc po pi ip T cst t ge les M Mf ir aus si cs f body caller tail
 tau d1 d2 saved b ph Th O Bind Code Local Aux Free Cur Post.
 assert(Inside:InOS(SKIP,(kenil,kcall f body caller tail))(pumerge po pi)).
 { eapply V293_bound_call_inos;exact Bind. }
 rewrite <-(TasksMod.get_set_same Code)at 1.
 eapply V293_exit_pure_progsim with(ks:=kcall f body caller tail)
 (le:=V293_cpu_lenv saved b)
 (C':=(curs(sprim excrit),(kenil,kseq sret(kcall f body caller tail))));
 try eassumption;try reflexivity.
 - eapply stmt_step;[reflexivity|apply sskip_step].
 - eapply V293_excrit_progsim with(le:=V293_cpu_lenv saved b)(si:=si)(cs:=cs)(saved:=false);
   try eassumption.
   + eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
   + eapply V293_exit_pure_progsim with(ks:=kcall f body caller tail)
     (le:=V293_cpu_lenv saved b)
     (C':=(curs sret,(kenil,kcall f body caller tail)));
     try eassumption;try reflexivity.
     * apply map_get_set.
     * eapply stmt_step;[reflexivity|apply sskip_step].
     * eapply V293_one_local_return_progsim with(le:=V293_cpu_lenv saved b)
       (b:=b)(tp:=Tint32)(Mf:=Mf)(si:=si)(cs:=cs);try eassumption.
       -- apply map_get_set.
       -- apply V293_cpu_layout.
Qed.

(* The selected task is already pending in T. The outgoing task keeps ks;
   its code and resources are not erased when the selected task returns. *)
Theorem V293_switch_pending_exit_progsim :
 forall pc po pi ip T cst current next x ks ge le les M Msw Mret ir aus si cs
 bt bc tp f body caller tail tau d1 d2 saved b nsi ncs ph Th O Thf Of,
 current<>next ->
 get T current=Some(curs(sprim(switch x)),(kenil,ks)) ->
 get T next=Some(SKIP,(kenil,kseq(sprim excrit)(kseq sret(kcall f body caller tail)))) ->
 get les current=Some le ->get aus current=Some((false,si,cs):localst) ->
 get les next=Some(V293_cpu_lenv saved b) ->
 get aus next=Some((false,nsi,false::ncs):localst) ->
 po f=Some(tau,d1,d2,body) ->
 get ge x=Some(bt,Tptr tp) ->load(Tptr tp)M(bt,0%Z)=Some(Vptr next) ->
 get ge OSTCBCur=Some(bc,Tptr tp) ->store(Tptr tp)M(bc,0%Z)(Vptr next)=Some Msw ->
 free Tint32 b Msw=Some Mret ->get O curtid=Some(oscurt current) ->
 hpstepstar ph Th cst O Thf cst Of ->get Of curtid=Some(oscurt next) ->
 ProgSim(pc,(po,pi,ip))(set(set T current(SKIP,(kenil,ks)))next(SKIP,(kenil,tail)))
 (ge,set les next caller,Mret,ir,set aus next(false,nsi,ncs))ph Thf Of cst next ->
 ProgSim(pc,(po,pi,ip))T(ge,les,M,ir,aus)ph Th O cst current.
Proof.
 intros pc po pi ip T cst current next x ks ge le les M Msw Mret ir aus si cs
 bt bc tp f body caller tail tau d1 d2 saved b nsi ncs ph Th O Thf Of
 Different Code Pending Local Aux NextLocal NextAux Bind Target Read Current Store
 Free Cur Match NextCur Post.
 eapply V293_switch_progsim with(le:=le)(next:=next)(Mf:=Msw)(bt:=bt)(bc:=bc)
 (tp:=tp)(si:=si)(cs:=cs)(Thf:=Thf)(Of:=Of);try eassumption.
 eapply V293_pending_exit_progsim with(saved:=saved)(b:=b)(Mf:=Mret)
 (f:=f)(body:=body)(caller:=caller)(tail:=tail)(si:=nsi)(cs:=ncs);
 try eassumption.
 rewrite map_get_set' by congruence;exact Pending.
Qed.

Section DispatchResume.
Variables pc po pi:progunit.
Variable ip:intunit.
Variable T:tasks.
Variable cst:clientst.
Variable t:tid.
Variables ge le:env.
Variable les:cltenvs.
Variables M Mt:mem.
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


Variable exitf:fid.

Theorem V293_exit_call_resume_progsim : forall next current counter ks M1 Mc Mf
 bk count b v bc Thf Of,
 get T t=Some(curs(V293_exit_boundary_dispatch table high target current counter f
 (V293_interrupt_handoff high current target)),(kenil,ks)) ->
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
 forall body caller tail tau d1 d2 saved bs nsi ncs Mret,
 t<>next ->po exitf=Some(tau,d1,d2,body) ->
 get T next=Some(SKIP,(kenil,kseq(sprim excrit)(kseq sret(kcall exitf body caller tail)))) ->
 get les next=Some(V293_cpu_lenv saved bs) ->
 get aus next=Some((false,nsi,false::ncs):localst) ->
 free Tint32 bs Mf=Some Mret ->get Of curtid=Some(oscurt next) ->
 ProgSim P(set(set T t(SKIP,(kenil,ks)))next(SKIP,(kenil,tail)))
 (ge,set les next caller,Mret,ir,set aus next(false,nsi,ncs))ph Thf Of cst next ->
 ProgSim P T(ge,les,M,ir,aus)ph Th O cst t.
Proof.
 intros next current counter ks M1 Mc Mf bk count b v bc Thf Of Code Inside Guard
 Ncounter Gcounter Counter Increment CurrentType HighType HighValue Address Copy
 Target Current Store Match body caller tail tau d1 d2 saved bs nsi ncs Mret
 Different ExitBind Pending NextLocal NextAux Free NextCur Post.
 eapply V293_exit_call_dispatch_progsim with(le:=le)(Mt:=Mt)(M1:=M1)(Mc:=Mc)(Mf:=Mf)
 (next:=next)(current:=current)(counter:=counter)(ks:=ks)
 (bk:=bk)(count:=count)(b:=b)(v:=v)(bc:=bc)(Thf:=Thf)(Of:=Of)
 (unmap:=unmap)(group:=group)(rows:=rows)(high:=high)(y:=y)(table:=table)(target:=target)
 (bt:=bt)(bg:=bg)(br:=br)(bh:=bh)(bp:=bp)(bo:=bo)(lo:=lo)(hi:=hi)(g:=g)
 (oldhigh:=oldhigh)(value:=value)(tp:=tp)(si:=si)(cs:=cs);try eassumption.
 eapply V293_pending_exit_progsim with(saved:=saved)(b:=bs)(Mf:=Mret)
 (f:=exitf)(body:=body)(caller:=caller)(tail:=tail)(si:=nsi)(cs:=ncs);try eassumption.
 rewrite map_get_set' by congruence;exact Pending.
Qed.
End DispatchResume.
