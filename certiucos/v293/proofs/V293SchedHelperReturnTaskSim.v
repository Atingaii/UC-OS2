(* The helper's byte local is released from ownership; the caller resumes. *)
Require Import CertiOS.certiucos.v293.proofs.V293SchedHelperTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293HandoffProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293InvariantPendingTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293PendingReturnTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293SchedCallProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293ReadySchedCall.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCallGlobal.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.simulation.
Require Import CertiOS.framework.proof.memory_prop.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope nat_scope.

Lemma V293_helper_byte_layout : forall y b,
 getaddr(set(emp:env)y(b,Tint8))=[(b,Tint8)].
Proof.
 intros;change(getaddr(EnvMod.set EnvMod.emp y(b,Tint8))=[(b,Tint8)]);reflexivity.
Qed.

Lemma V293_helper_return_steps : forall p ge M Mret y b f body caller ks,
 free Tint8 b M=Some Mret ->
 cstepstar p(SKIP,(kenil,kseq sret(kcall f body caller ks)))
 (ge,set(emp:env)y(b,Tint8),M)(SKIP,(kenil,ks))(ge,caller,Mret).
Proof.
 intros p ge M Mret y b f body caller ks Free.
 eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply sskip_step]| ].
 eapply c_stepstarn.
 { eapply stmt_step;[reflexivity| ];eapply sret_step;
  [reflexivity|reflexivity|apply V293_helper_byte_layout]. }
 eapply c_stepstarn.
 { eapply stmt_step;[reflexivity| ];eapply sfree_step;[reflexivity|reflexivity|exact Free]. }
 eapply c_stepstarn;[eapply stmt_step;[reflexivity| ];eapply sfreeend_step;reflexivity|apply c_stepstar0].
Qed.

(* Only the restored caller continuation is supplied, not this return suffix. *)
Theorem V293_sched_helper_return_TaskSim : forall pc po pi ip ph Ch O I Post t
 ks ge caller M ir ci op R f unmap group rows high y b v,
 po f=Some(V293_OSSchedNew_function unmap group rows high y) ->
 GoodInvAsrt R ->
 (forall s,s|=R ->s|=CurTid t **Atrue) ->
 (ge,set(emp:env)y(b,Tint8),M,ir,(false,nil,ci),O,op)|=
 Amapsto(b,0%Z)Tint8 true v **R ->
 (forall Mret,(ge,caller,Mret,ir,(false,nil,ci),O,op)|=R ->
  TaskSim(pc,(po,pi,ip))(SKIP,(kenil,ks))(ge,caller,Mret,ir,(false,nil,ci))
  ph Ch O V293_shared_li I Post t) ->
 TaskSim(pc,(po,pi,ip))
 (SKIP,(kenil,kseq sret(kcall f(V293_OSSchedNew_body unmap group rows high y)caller ks)))
 (ge,set(emp:env)y(b,Tint8),M,ir,(false,nil,ci))ph Ch O V293_shared_li I Post t.
Proof.
 intros pc po pi ip ph Ch O I Post t ks ge caller M ir ci op R f unmap group rows high y b v
 Bind Good Current Held Tail.
 set(le:=set(emp:env)y(b,Tint8)).
 set(body:=V293_OSSchedNew_body unmap group rows high y).
 set(k:=kcall f body caller ks).
 assert(GoodCell:GoodInvAsrt(Amapsto(b,0%Z)Tint8 true v **R)).
 { split;[exact Logic.I|exact Good]. }
 assert(Before:forall le',satp(ge,le',M,ir,(false,nil,ci))O(CurLINV V293_shared_li t)).
 { intros le';eapply V293_pending_local with(op:=op).
   assert(Own:(ge,le',M,ir,(false,nil,ci),O,op)|=Amapsto(b,0%Z)Tint8 true v **R).
   { eapply good_inv_prop;[exact GoodCell|exact Held]. }
   apply astar_mono with(P':=Amapsto(b,0%Z)Tint8 true v)(Q':=CurTid t **Atrue)in Own;
    [clear Held;sep auto|intros st H;exact H|exact Current]. }
 destruct(V293_ready_release_byte _ _ _ _ _ _ _ _ _ _ Held)as(Mret&Freed&Rest&Removed&Outside).
 assert(After:forall le',satp(ge,le',Mret,ir,(false,nil,ci))O(CurLINV V293_shared_li t)).
 { intros le';eapply V293_pending_local with(op:=op);apply Current.
   eapply good_inv_prop;[exact Good|exact Rest]. }
 assert(Inside:InOS(SKIP,(kenil,k))(pumerge po pi)).
 { unfold k;eapply V293_bound_call_inos;exact Bind. }
 assert(End:TaskSim(pc,(po,pi,ip))(SKIP,(kenil,ks))(ge,caller,Mret,ir,(false,nil,ci))
 ph Ch O V293_shared_li I Post t).
 { apply Tail;eapply good_inv_prop;[exact Good|exact Rest]. }
 assert(FreeEnd:TaskSim(pc,(po,pi,ip))(curs(sfree nil None),(kenil,k))
 (ge,le,Mret,ir,(false,nil,ci))ph Ch O V293_shared_li I Post t).
 { eapply V293_invariant_cstep_TaskSim;[ | | |apply After|exact End].
   - eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
   - intros[x E];discriminate E.
   - intros Mf Mall Join;exists Mall;split;[exact Join| ];split.
     + unfold k;eapply stmt_step;[reflexivity| ];eapply sfreeend_step;reflexivity.
     + intros;eapply V293_free_end_successor;eassumption. }
 assert(FreeCell:TaskSim(pc,(po,pi,ip))(curs(sfree((b,Tint8)::nil)None),(kenil,k))
 (ge,le,M,ir,(false,nil,ci))ph Ch O V293_shared_li I Post t).
 { eapply V293_invariant_cstep_TaskSim;[ | | |apply After|exact FreeEnd].
   - eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
   - intros[x E];discriminate E.
   - intros Mf Mall Join;destruct(free_mono _ _ _ _ _ _ Join Freed)as(Mall'&Free').
     exists Mall';split;[eapply join_free;eassumption| ];split.
     + eapply stmt_step;[reflexivity| ];eapply sfree_step;[reflexivity|reflexivity|exact Free'].
     + intros;eapply V293_free_one_successor;eassumption. }
 assert(Return:TaskSim(pc,(po,pi,ip))(curs sret,(kenil,k))
 (ge,le,M,ir,(false,nil,ci))ph Ch O V293_shared_li I Post t).
 { eapply V293_invariant_cstep_TaskSim;[ | | |apply Before|exact FreeCell].
   - eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
   - intros[x E];discriminate E.
   - intros Mf Mall Join;exists Mall;split;[exact Join| ].
     assert(Next:cstep(pumerge po pi)(curs sret,(kenil,k))(ge,le,Mall)
      (curs(sfree((b,Tint8)::nil)None),(kenil,k))(ge,le,Mall)).
     { unfold k,le;eapply stmt_step;[reflexivity| ];eapply sret_step;
      [reflexivity|reflexivity|apply V293_helper_byte_layout]. }
     split;[exact Next| ];intros Cf mf Other.
     destruct(cstep_idmove_deter _ _ _ _ _ _ Next Other)as[EC EM];split;symmetry;assumption. }
 eapply V293_invariant_cstep_TaskSim;[ | | |apply Before|exact Return].
 - eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
 - intros[x E];discriminate E.
 - intros Mf Mall Join;exists Mall;split;[exact Join| ].
   assert(Next:cstep(pumerge po pi)(SKIP,(kenil,kseq sret k))(ge,le,Mall)
    (curs sret,(kenil,k))(ge,le,Mall)).
   { eapply stmt_step;[reflexivity|apply sskip_step]. }
   split;[exact Next| ];intros Cf mf Other.
   destruct(cstep_idmove_deter _ _ _ _ _ _ Next Other)as[EC EM];split;symmetry;assumption.
Qed.
