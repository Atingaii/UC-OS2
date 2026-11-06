(* Source os_core.c:702-707. A real critical primitive and owned-byte guards.
   Dispatch continuation is explicit; this is not a whole function entry. *)
Require Import CertiOS.certiucos.v293.proofs.V293InvariantPendingTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293ExitChangedTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293SchedHelperBodyTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293ExitNestingProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturnProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293PendingReturnTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293HandoffProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.code.V293OSIntExit.
Require Import CertiOS.certiucos.v293.code.V293OSSchedGuards.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.simulation.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.framework.proof.memory_prop.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Lemma V293_invariant_encrit_TaskSim : forall I pc po pi ip ph Ch ks
 ge le M ir ci O li Post t,
 getinv(I(S INUM))=Aemp ->
 InOS(curs(sprim encrit),(kenil,ks))(pumerge po pi) ->
 satp(ge,le,M,ir,(false,nil,false::ci))O(CurLINV li t) ->
 TaskSim(pc,(po,pi,ip))(SKIP,(kenil,ks))
 (ge,le,M,ir,(false,nil,false::ci))ph Ch O li I Post t ->
 TaskSim(pc,(po,pi,ip))(curs(sprim encrit),(kenil,ks))
 (ge,le,M,ir,(false,nil,ci))ph Ch O li I Post t.
Proof.
 intros I pc po pi ip ph Ch ks ge le M ir ci O li Post t Shape Inside Local Tail.
 apply task_sim.
 - intros Cf Ms Mf cst cst' ofull Os o2 OO Inv JM JO Low.
   destruct(V293_invariant_nil_empty I Shape _ _ _ _ _ _ Inv)as[EM EO];subst Ms Os.
   apply map_join_emp' in JO;subst OO.
   destruct(V293_pending_join_frame _ _ _ _ _ _ _ JM)as(Mall&Join&Eq);subst o2.
   inversion Low;subst;
   match goal with E:(pc,(po,pi,ip))=(_,(_,_,_)) |- _ =>inversion E;subst;clear E end;try contradiction.
   match goal with H:loststep _ _ _ _ _ |- _ =>
    apply V293_encrit_successor in H;destruct H as[EC ES];subst Cf ofull end.
   exists Ch;exists O;exists((ge,le,M,ir,(false,nil,false::ci)):taskst);
   exists(emp:mem);exists O;exists(emp:osabst).
   split;[apply ht_starO| ];split.
   + exists((ge,le,M,ir,(false,nil,false::ci)):taskst);split;unfold joinmem.
     * do 6 eexists;split;[reflexivity| ];split;[reflexivity|apply map_join_emp].
     * do 6 eexists;split;[reflexivity| ];split;[reflexivity|exact Join].
   + split;[apply map_join_emp| ];split.
     * apply V293_invariant_nil_close;exact Shape.
     * split;assumption.
 - intros Cf Ms Mf cst cst' ofull Os o2 OO ev Inv JM JO Low.
   inversion Low;subst.
   match goal with E:(pc,(po,pi,ip))=(_,(_,_,_)) |- _ =>inversion E;subst;clear E end;contradiction.
 - intros Ms k x Os OO Eq;discriminate Eq.
 - intros Ms Os OO(x&Eq);discriminate Eq.
 - intros cst o2 Ms Os Mf OO Of OOO NE NS NI NF Inv JM JO JO' Bad.
   destruct(V293_invariant_nil_empty I Shape _ _ _ _ _ _ Inv)as[EM EO];subst Ms Os.
   destruct(V293_pending_join_frame _ _ _ _ _ _ _ JM)as(Mall&Join&Eq);subst o2.
   inversion Bad;subst;exfalso.
   match goal with H:~(_ \/ _) |- _ =>apply H;left end.
   exists(SKIP,(kenil,ks));exists((ge,le,Mall,ir,(false,nil,false::ci)):taskst);exists cst.
   eapply inapi_step;[reflexivity|apply encrit_step;reflexivity|exact Inside].
 - intros Ms Os e1 e2 e3 k OO Eq;discriminate Eq.
 - intros Ms Os e k OO Eq;discriminate Eq.
Qed.

Lemma V293_exit_ifthen_TaskSim : forall pc po pi ip ph Ch O li I Post t ks
 ge le M ir ci e yes v take,
 InOS(SKIP,(kenil,ks))(pumerge po pi) ->
 satp(ge,le,M,ir,(false,nil,ci))O(CurLINV li t) ->
 evalval e(ge,le,M)=Some v ->istrue v=Some take ->
 TaskSim(pc,(po,pi,ip))(curs(if take then yes else sskip None),(kenil,ks))
 (ge,le,M,ir,(false,nil,ci))ph Ch O li I Post t ->
 TaskSim(pc,(po,pi,ip))(curs(sifthen e yes),(kenil,ks))
 (ge,le,M,ir,(false,nil,ci))ph Ch O li I Post t.
Proof.
 intros pc po pi ip ph Ch O li I Post t ks ge le M ir ci e yes v take
 Context Local Eval Truth Tail.
 eapply V293_changed_pure_TaskSim with(ks:=ks)(C':=(cure e,(kenil,kif yes(sskip None)ks)));
 [exact Context|reflexivity|reflexivity| | |exact Local| ].
 - intros[x E];discriminate E.
 - intros;eapply stmt_step;[reflexivity|apply sifthen_step].
 - eapply V293_changed_expr_TaskSim with(m:=(ge,le,M))(m':=(ge,le,M))
   (c':=curs(sskip(Some v)))(ke':=kenil);[ |reflexivity| |exact Local| ].
   + apply cstepLib.evalval_imply_estepstar;exact Eval.
   + eapply V293_context_inos;[exact Context|reflexivity|reflexivity].
   + eapply V293_changed_pure_TaskSim with(ks:=ks);
     [exact Context|reflexivity|reflexivity| | |exact Local|exact Tail].
     * intros[x E];discriminate E.
     * intros;eapply stmt_step;[reflexivity| ];destruct take;
       [apply svift_step|apply sviff_step];exact Truth.
Qed.

Definition V293_exit_guard_resource bn bl n R :=
 V293_owned_record_cell((bn,0%Z),Tint8,V293_byteval n) **
 (V293_owned_record_cell((bl,0%Z),Tint8,V293_byteval 0) **R).

Lemma V293_exit_guards_local : forall bn bl n R t ge le M ir ci O op,
 (R ==>CurTid t **Atrue) ->
 (ge,le,M,ir,(false,nil,ci),O,op)|=V293_exit_guard_resource bn bl n R ->
 satp(ge,le,M,ir,(false,nil,ci))O(CurLINV V293_shared_li t).
Proof.
 intros bn bl n R t ge le M ir ci O op Current Held.
 eapply V293_pending_local with(op:=op).
 unfold V293_exit_guard_resource in Held.
 eapply astar_mono in Held;[ |intros s H;exact H|apply astar_mono;
  [intros s H;exact H|exact Current]].
 sep auto.
Qed.

Lemma V293_exit_zero_eval : forall ge le M x b,
 get le x=None ->get ge x=Some(b,Tint8) ->
 load Tint8 M(b,0%Z)=Some(V293_byteval 0) ->
 evalval(V293_OSSched_zero x)(ge,le,M)=Some(Vint32 Int.one).
Proof.
 intros ge le M x b NL G Read.
 unfold V293_OSSched_zero;cbn[evalval evaltype get_lenv get_genv];rewrite NL,G.
 cbn -[load];rewrite Read;reflexivity.
Qed.

(* n=0 is preserved without a write; n=1 writes through ownership.
   The same R, memory frame and abstract state reach the dispatch cut. *)
Lemma V293_exit_nesting_prefix_TaskSim : forall pc po pi ip ph Ch O I Post t ks
 ge le M ir ci op nesting lock bn bl n R dispatch,
 InOS(SKIP,(kenil,ks))(pumerge po pi) ->
 n<=1 ->get le nesting=None ->get le lock=None ->
 get ge nesting=Some(bn,Tint8) ->get ge lock=Some(bl,Tint8) ->
 (R ==>CurTid t **Atrue) ->
 (ge,le,M,ir,(false,nil,ci),O,op)|=V293_exit_guard_resource bn bl n R ->
 (forall M', (ge,le,M',ir,(false,nil,ci),O,op)|=V293_exit_guard_resource bn bl 0 R ->
  TaskSim(pc,(po,pi,ip))(curs dispatch,(kenil,ks))
  (ge,le,M',ir,(false,nil,ci))ph Ch O V293_shared_li I Post t) ->
 TaskSim(pc,(po,pi,ip))(curs(V293_OSIntExit_nesting_dispatch nesting lock dispatch),(kenil,ks))
 (ge,le,M,ir,(false,nil,ci))ph Ch O V293_shared_li I Post t.
Proof.
 intros pc po pi ip ph Ch O I Post t ks ge le M ir ci op nesting lock bn bl n R dispatch
 Inside Bound NN LN NG LG Current Held Continue.
 assert(Before:satp(ge,le,M,ir,(false,nil,ci))O(CurLINV V293_shared_li t)).
 { eapply V293_exit_guards_local;[exact Current|exact Held]. }
 assert(Guards:forall M',
  (ge,le,M',ir,(false,nil,ci),O,op)|=V293_exit_guard_resource bn bl 0 R ->
  TaskSim(pc,(po,pi,ip))(curs(V293_OSIntExit_guards nesting lock dispatch),(kenil,ks))
  (ge,le,M',ir,(false,nil,ci))ph Ch O V293_shared_li I Post t).
 { intros M' H.
   assert(Local:satp(ge,le,M',ir,(false,nil,ci))O(CurLINV V293_shared_li t)).
   { eapply V293_exit_guards_local;[exact Current|exact H]. }
   assert(NRead:load Tint8 M'(bn,0%Z)=Some(V293_byteval 0)).
   { change(load Tint8(assertion.getmem(ge,le,M',ir,(false,nil,ci),O,op))(bn,0%Z)=Some(V293_byteval 0)).
     unfold V293_exit_guard_resource in H;eapply V293_record_star_load_l;[ |exact H];intros;eapply V293_owned_record_cell_load;eassumption. }
   assert(LRead:load Tint8 M'(bl,0%Z)=Some(V293_byteval 0)).
   { change(load Tint8(assertion.getmem(ge,le,M',ir,(false,nil,ci),O,op))(bl,0%Z)=Some(V293_byteval 0)).
     unfold V293_exit_guard_resource in H;eapply V293_record_star_load_r;[ |exact H];intros.
     eapply V293_record_star_load_l;[ |eassumption];intros;eapply V293_owned_record_cell_load;eassumption. }
   unfold V293_OSIntExit_guards.
   eapply V293_changed_if_TaskSim with(v:=Vint32 Int.one)(take:=true);
    [exact Inside|exact Local|eapply V293_exit_zero_eval;eassumption|reflexivity| ].
   eapply V293_changed_if_TaskSim with(v:=Vint32 Int.one)(take:=true);
    [exact Inside|exact Local|eapply V293_exit_zero_eval;eassumption|reflexivity| ].
   apply Continue;exact H. }
 unfold V293_OSIntExit_nesting_dispatch.
 eapply V293_changed_pure_TaskSim with(ks:=ks)
 (C':=(curs(V293_OSIntExit_decrement nesting),(kenil,kseq(V293_OSIntExit_guards nesting lock dispatch)ks)));
 [exact Inside|reflexivity|reflexivity| | |exact Before| ].
 - intros[x E];discriminate E.
 - intros;eapply stmt_step;[reflexivity|apply sseq_step].
 - assert(NextInside:InOS(SKIP,(kenil,kseq(V293_OSIntExit_guards nesting lock dispatch)ks))(pumerge po pi)).
   { eapply V293_context_inos;[exact Inside|reflexivity|reflexivity]. }
   assert(NRead:load Tint8 M(bn,0%Z)=Some(V293_byteval n)).
   { change(load Tint8(assertion.getmem(ge,le,M,ir,(false,nil,ci),O,op))(bn,0%Z)=Some(V293_byteval n)).
     unfold V293_exit_guard_resource in Held;eapply V293_record_star_load_l;[ |exact Held];intros;eapply V293_owned_record_cell_load;eassumption. }
   destruct(V293_exit_decrement_eval ge le M nesting bn n ltac:(lia) NN NG NRead)as[Positive Assignment].
   destruct n as [ | n ];[ |destruct n as [ | n ];[ |lia]].
   + unfold V293_OSIntExit_decrement.
     eapply V293_exit_ifthen_TaskSim with(v:=Vint32 Int.zero)(take:=false);
      [exact NextInside|exact Before|exact Positive|reflexivity| ].
     eapply V293_changed_pure_TaskSim with(ks:=ks);
      [exact Inside|reflexivity|reflexivity| | |exact Before|apply Guards;exact Held].
     * intros[x E];discriminate E.
     * intros;eapply stmt_step;[reflexivity|apply sskip_step].
   + destruct(V293_owned_record_cell_update _ _ _ (V293_byteval 0) _ _ _ _ _ _ _ _
      (V293_byte_type 0 ltac:(lia)) Held)as(M'&Store&Updated).
     assert(After:satp(ge,le,M',ir,(false,nil,ci))O(CurLINV V293_shared_li t)).
     { eapply V293_exit_guards_local;[exact Current|exact Updated]. }
     unfold V293_OSIntExit_decrement.
     eapply V293_exit_ifthen_TaskSim with(v:=Vint32 Int.one)(take:=true);
      [exact NextInside|exact Before|exact Positive|reflexivity| ].
     destruct(Assignment ltac:(lia))as(TL&Addr&TR&Value).
     eapply V293_helper_assignment_TaskSim;
      [exact NextInside|exact TL|exact Addr|exact TR|exact Value|exact Store|exact Before|exact After| ].
     eapply V293_changed_pure_TaskSim with(ks:=ks);
      [exact Inside|reflexivity|reflexivity| | |exact After|apply Guards;exact Updated].
     * intros[x E];discriminate E.
     * intros;eapply stmt_step;[reflexivity|apply sskip_step].
Qed.

Theorem V293_exit_critical_prefix_TaskSim : forall pc po pi ip ph Ch O I Post t ks
 ge le M ir ci op nesting lock bn bl n R dispatch,
 getinv(I(S INUM))=Aemp ->
 InOS(SKIP,(kenil,ks))(pumerge po pi) ->
 n<=1 ->get le nesting=None ->get le lock=None ->
 get ge nesting=Some(bn,Tint8) ->get ge lock=Some(bl,Tint8) ->
 GoodInvAsrt R ->(R ==>CurTid t **Atrue) ->
 (ge,le,M,ir,(false,nil,ci),O,op)|=V293_exit_guard_resource bn bl n R ->
 (forall M', (ge,le,M',ir,(false,nil,false::ci),O,op)|=V293_exit_guard_resource bn bl 0 R ->
  TaskSim(pc,(po,pi,ip))(curs dispatch,(kenil,ks))
  (ge,le,M',ir,(false,nil,false::ci))ph Ch O V293_shared_li I Post t) ->
 TaskSim(pc,(po,pi,ip))
 (curs(sseq(sprim encrit)(V293_OSIntExit_nesting_dispatch nesting lock dispatch)),(kenil,ks))
 (ge,le,M,ir,(false,nil,ci))ph Ch O V293_shared_li I Post t.
Proof.
 intros pc po pi ip ph Ch O I Post t ks ge le M ir ci op nesting lock bn bl n R dispatch
 Shape Inside Bound NN LN NG LG Good Current Held Continue.
 assert(Before:satp(ge,le,M,ir,(false,nil,ci))O(CurLINV V293_shared_li t)).
 { eapply V293_exit_guards_local;[exact Current|exact Held]. }
 assert(Entered:(ge,le,M,ir,(false,nil,false::ci),O,op)|=V293_exit_guard_resource bn bl n R).
 { eapply good_inv_prop;[ |exact Held].
   unfold V293_exit_guard_resource,V293_owned_record_cell;split;[cbn;auto| ];split;[cbn;auto|exact Good]. }
 assert(After:satp(ge,le,M,ir,(false,nil,false::ci))O(CurLINV V293_shared_li t)).
 { eapply V293_exit_guards_local;[exact Current|exact Entered]. }
 eapply V293_changed_pure_TaskSim with(ks:=ks)
 (C':=(curs(sprim encrit),(kenil,kseq(V293_OSIntExit_nesting_dispatch nesting lock dispatch)ks)));
 [exact Inside|reflexivity|reflexivity| | |exact Before| ].
 - intros[x E];discriminate E.
 - intros;eapply stmt_step;[reflexivity|apply sseq_step].
 - eapply V293_invariant_encrit_TaskSim;[exact Shape| |exact After| ].
   + eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
   + eapply V293_changed_pure_TaskSim with(ks:=ks);
     [exact Inside|reflexivity|reflexivity| | |exact After| ].
     * intros[x E];discriminate E.
     * intros;eapply stmt_step;[reflexivity|apply sskip_step].
     * eapply V293_exit_nesting_prefix_TaskSim;
       [exact Inside|exact Bound|exact NN|exact LN|exact NG|exact LG|exact Current|exact Entered|exact Continue].
Qed.
