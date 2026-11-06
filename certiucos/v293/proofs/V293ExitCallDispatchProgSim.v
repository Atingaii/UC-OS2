(* Join the actual scheduler call and pointer store to the existing Exit
   dispatch. The only simulation post is at the final branch endpoint. *)
Require Import CertiOS.certiucos.v293.proofs.V293SchedCallProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBoundarySwitch.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.simulation.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.framework.proof.step_prop.
Require Import CertiOS.framework.auxlibs.MapLib.
Require Import CertiOS.certiucos.v293.proofs.V293ExitDispatchProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293HandoffProgSim.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.certiucos.v293.code.V293OSSchedDispatch.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Local Open Scope nat_scope.

Lemma V293_assign_pointer_progsim :
 forall pc po pi ip T cst t ks ge le les M M' ir aus si cs e1 e2 b v tp ph Th O,
 get les t=Some le ->get aus t=Some((false,si,cs):localst) ->
 InOS(SKIP,(kenil,ks))(pumerge po pi) ->get O curtid=Some(oscurt t) ->
 evaltype e1(ge,le,M)=Some (Tptr tp) ->
 evaladdr e1(ge,le,M)=Some(Vptr(b,Int.zero)) ->
 evaltype e2(ge,le,M)=Some (Tptr tp) ->evalval e2(ge,le,M)=Some v ->
 store (Tptr tp) M(b,0%Z)v=Some M' ->
 ProgSim(pc,(po,pi,ip))(set T t(SKIP,(kenil,ks)))(ge,les,M',ir,aus)ph Th O cst t ->
 ProgSim(pc,(po,pi,ip))(set T t(curs(sassign e1 e2),(kenil,ks)))(ge,les,M,ir,aus)ph Th O cst t.
Proof.
 intros pc po pi ip T cst t ks ge le les M M' ir aus si cs e1 e2 b v tp ph Th O
 Local Aux Inside Cur Left Address Right Value Store Post.
 eapply V293_exit_pure_progsim with(ks:=ks)
 (C':=(cure e2,(kenil,kassignr e1 (Tptr tp) ks)))(le:=le);try eassumption;try reflexivity.
 - eapply stmt_step;[reflexivity| ];eapply sassign_step;try eassumption;apply eq_vptr;exists tp;exists tp;auto.
 - eapply V293_exit_expr_progsim with(m:=(ge,le,M))(m':=(ge,le,M))
   (c':=curs(sskip(Some v)))(ke':=kenil)(le:=le);try eassumption;try reflexivity.
   + apply evalval_imply_estepstar;exact Value.
   + eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
   + eapply V293_exit_pure_progsim with(ks:=ks)
     (C':=(cure(eaddrof e1),(kenil,kassignl v (Tptr tp) ks)))(le:=le);try eassumption;try reflexivity.
     * eapply stmt_step;[reflexivity|apply sassignrv_step].
     * eapply V293_exit_expr_progsim with(m:=(ge,le,M))(m':=(ge,le,M))
       (c':=curs(sskip(Some(Vptr(b,Int.zero)))))(ke':=kenil)(le:=le);try eassumption;try reflexivity.
       -- apply evaladdr_imply_estepstar;exact Address.
       -- eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
       -- eapply V293_os_silent_progsim with
          (C:=(curs(sskip(Some(Vptr(b,Int.zero)))),(kenil,kassignl v (Tptr tp) ks)))
          (C':=(SKIP,(kenil,ks)))(le:=le)(M':=M');try eassumption.
          ++ apply map_get_set.
          ++ eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
          ++ eapply stmt_step;[reflexivity| ];eapply sassignend_step;try reflexivity;exact Store.
          ++ intros Cf mf Other;eapply V293_store_cstep_unique;[exact Store|exact Other].
          ++ rewrite tasks_set_a_set_a;exact Post.
Qed.

Section CallDispatch.
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

(* This endpoint is the actual caller tail, not an oracle for a callee body.
   Pointer expression evaluation is derived from the typed array load. *)
Theorem V293_sched_target_then_progsim : forall tail ks,
 InOS(SKIP,(kenil,ks))(pumerge po pi) ->
 ProgSim P(set T t(curs tail,(kenil,ks)))(ge,les,Mt,ir,aus)ph Th O cst t ->
 ProgSim P(set T t(curs(sseq(V293_OSSched_unlocked_prefix f table high target)tail),(kenil,ks)))
 (ge,les,M,ir,aus)ph Th O cst t.
Proof.
 intros tail ks Inside Post.
 assert(HighRead:load Tint8 Mh(bh,0%Z)=Some(V293_byteval(V293_ready_select lo hi g))).
 { apply V293_write_byte_load;lia. }
 destruct(V293_eval_pointer_array ge le Mh table high tp bp bh
 (V293_ready_select lo hi g)value Nt Nh Gt Gh HighRead Range Table)as[Value RightType].
 unfold V293_OSSched_unlocked_prefix.
 eapply V293_exit_pure_progsim with(ks:=ks)
 (C':=(curs(sseq(scall f nil)(V293_OSSched_target_update table high target)),(kenil,kseq tail ks)))(le:=le);
 try eassumption;try reflexivity.
 - eapply stmt_step;[reflexivity|apply sseq_step].
 - eapply V293_exit_pure_progsim with(ks:=ks)
   (C':=(curs(scall f nil),(kenil,kseq(V293_OSSched_target_update table high target)(kseq tail ks))))(le:=le);
   try eassumption;try reflexivity.
   + eapply stmt_step;[reflexivity|apply sseq_step].
   + eapply V293_sched_call_progsim with(caller:=le)(si:=si)(cs:=cs)
     (ks:=kseq(V293_OSSched_target_update table high target)(kseq tail ks))
     (unmap:=unmap)(group:=group)(rows:=rows)(high:=high)(y:=y)
     (bt:=bt)(bg:=bg)(br:=br)(bh:=bh)(lo:=lo)(hi:=hi)(g:=g)(oldhigh:=oldhigh);
     try eassumption.
     * apply map_get_set.
     * eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
     * rewrite tasks_set_a_set_a.
       eapply V293_exit_pure_progsim with(ks:=ks)
       (C':=(curs(V293_OSSched_target_update table high target),(kenil,kseq tail ks)))(le:=le);
       try eassumption;try reflexivity.
       -- eapply stmt_step;[reflexivity|apply sskip_step].
       -- unfold V293_OSSched_target_update.
          eapply V293_assign_pointer_progsim with(b:=bo)(tp:=tp)(v:=value)(M':=Mt)(le:=le)(si:=si)(cs:=cs)(ks:=kseq tail ks);
          try eassumption.
          ++ eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
          ++ cbn[evaltype];rewrite No;rewrite Go;reflexivity.
          ++ cbn[evaladdr get_lenv get_genv];rewrite No;rewrite Go;reflexivity.
          ++ eapply V293_exit_pure_progsim with(ks:=ks)
             (C':=(curs tail,(kenil,ks)))(le:=le);try eassumption;try reflexivity.
             eapply stmt_step;[reflexivity|apply sskip_step].
Qed.

(* Stable interface for the changed branch. All intermediate simulation
   conditions are discharged; the final switch post and high-level match
   remain explicit rather than being asserted as whole-kernel correctness. *)
Theorem V293_exit_call_dispatch_progsim : forall next current counter ks M1 Mc Mf
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
 ProgSim P(set T t(SKIP,(kenil,ks)))(ge,les,Mf,ir,aus)ph Thf Of cst next ->
 ProgSim P T(ge,les,M,ir,aus)ph Th O cst t.
Proof.
 intros next current counter ks M1 Mc Mf bk count b v bc Thf Of Code Inside Guard
 Ncounter Gcounter Counter Increment CurrentType HighType HighValue Address Copy
 Target Current Store Match Post.
 rewrite <-(TasksMod.get_set_same Code)at 1.
 unfold V293_exit_boundary_dispatch.
 eapply V293_sched_target_then_progsim;[exact Inside| ].
 eapply V293_exit_dispatch_progsim with(le:=le)(si:=si)(cs:=cs)(M1:=M1)(Mc:=Mc)(Mf:=Mf)
 (next:=next)(high:=high)(current:=current)(counter:=counter)(target:=target)(ks:=ks)
 (bk:=bk)(c:=count)(b:=b)(v:=v)(bt:=bo)(bc:=bc)(tp:=tp)(Thf:=Thf)(Of:=Of);
 try eassumption.
 - apply map_get_set.
 - rewrite tasks_set_a_set_a;exact Post.
Qed.

Theorem V293_exit_call_same_progsim : forall current counter ks,
 get T t=Some(curs(V293_exit_boundary_dispatch table high target current counter f
 (V293_interrupt_handoff high current target)),(kenil,ks)) ->
 InOS(SKIP,(kenil,ks))(pumerge po pi) ->
 evalval(V293_OSSched_different high current)(ge,le,Mt)=Some(Vint32 Int.zero) ->
 ProgSim P(set T t(SKIP,(kenil,ks)))(ge,les,Mt,ir,aus)ph Th O cst t ->
 ProgSim P T(ge,les,M,ir,aus)ph Th O cst t.
Proof.
 intros current counter ks Code Inside Guard Post.
 rewrite <-(TasksMod.get_set_same Code)at 1.
 unfold V293_exit_boundary_dispatch.
 eapply V293_sched_target_then_progsim;[exact Inside| ].
 eapply V293_exit_same_progsim with(le:=le)(si:=si)(cs:=cs);try eassumption.
 - apply map_get_set.
 - rewrite tasks_set_a_set_a;exact Post.
Qed.
End CallDispatch.
