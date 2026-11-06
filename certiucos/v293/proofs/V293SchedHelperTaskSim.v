(* All ordinary successors, including nondeterministic local allocation. *)
Require Import CertiOS.certiucos.v293.proofs.V293InvariantPendingTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293HandoffProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293EnabledPendingTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293PendingReturnTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCallGlobal.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.simulation.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.framework.proof.memory_prop.
Require Import CertiOS.framework.proof.cstepLib.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope nat_scope.

Lemma V293_branching_cstep_TaskSim : forall pc po pi ip ph Ch Cl
 ge le M ir ie ci O li I P t,
 InOS Cl(pumerge po pi) ->~IsEnd Cl ->
 (forall Mf Mall,join M Mf Mall ->
  exists Cf mf,cstep(pumerge po pi)Cl(ge,le,Mall)Cf mf) ->
 (forall Cf mf,cstep(pumerge po pi)Cl(ge,le,M)Cf mf ->
  exists le' M',mf=(ge,le',M') /\
   satp(ge,le',M',ir,(ie,nil,ci))O(CurLINV li t) /\
   TaskSim(pc,(po,pi,ip))Cf(ge,le',M',ir,(ie,nil,ci))ph Ch O li I P t) ->
 TaskSim(pc,(po,pi,ip))Cl(ge,le,M,ir,(ie,nil,ci))ph Ch O li I P t.
Proof.
 intros pc po pi ip ph Ch Cl ge le M ir ie ci O li I P t Inside End Progress Posts.
 destruct(Progress(emp:mem)M(map_join_emp M))as(C0&m0&Step).
 assert(Safe:~cstepabt(pumerge po pi)Cl(ge,le,M)).
 { intro Bad;apply Bad;exists C0;exists m0;exists Vundef;left;exact Step. }
 assert(NotSwitch:~IsSwitch Cl).
 { intros(x&ks&E);eapply V293_cstep_not_primitive;[exact Step|exact E]. }
 assert(NotInit:~IsStkInit Cl).
 { intros(e1&e2&e3&ks&E);eapply V293_cstep_not_primitive;[exact Step|exact E]. }
 assert(NotFree:~IsStkFree Cl).
 { intros(e&ks&E);eapply V293_cstep_not_primitive;[exact Step|exact E]. }
 apply task_sim.
 - intros Cf Ms Mf cst cst' ofull Os o2 OO Inv JM JO Low.
   destruct(V293_enabled_join_frames _ _ _ _ _ _ _ _ JM)as(mid&Mall&JS&JF&Eq);subst o2.
   destruct(map_join_assoc JS JF)as(Mframe&JAll&JSF).
   inversion Low;subst;
   match goal with E:(pc,(po,pi,ip))=(_,(_,_,_)) |- _ =>inversion E;subst;clear E end;try contradiction.
   match goal with H:loststep _ _ _ _ _ |- _ =>inversion H;subst end;
   try solve[exfalso;eapply V293_cstep_not_primitive;[exact Step|reflexivity]].
   assert(Framed:SysmemJoinM(ge,le,M)Mframe(ge,le,Mall)).
   { do 4 eexists;split;[reflexivity| ];split;[reflexivity|exact JAll]. }
   match goal with H:cstep _ _ (ge,le,Mall) _ _ |- _ =>
    destruct(@cstep_frame _ _ _ _ _ _ _ Safe Framed H)as(mown&Join'&Owned) end.
   destruct(Posts _ _ Owned)as(le'&M'&EM&Local&Post);subst mown.
   destruct Join' as(G0&E0&Ma&Mb&EA&EB&JAll');inversion EA;subst G0 E0 Ma;clear EA.
   inversion EB;subst.
   apply map_join_comm in JSF,JAll'.
   destruct(map_join_assoc JSF JAll')as(mid'&JF'&JS').
   apply map_join_comm in JF',JS'.
   exists Ch;exists OO;exists((ge,le',M',ir,(ie,nil,ci)):taskst);
   exists Ms;exists O;exists Os.
   split;[apply ht_starO| ];split.
   + exists((ge,le',mid',ir,(ie,nil,ci)):taskst);split;unfold joinmem.
     * do 6 eexists;split;[reflexivity| ];split;[reflexivity|exact JS'].
     * do 6 eexists;split;[reflexivity| ];split;[reflexivity|exact JF'].
   + split;[exact JO| ];split.
     * eapply inv_ncare_le;exact Inv.
     * split;assumption.
 - intros Cf Ms Mf cst cst' ofull Os o2 OO ev Inv JM JO Low.
   inversion Low;subst.
   match goal with E:(pc,(po,pi,ip))=(_,(_,_,_)) |- _ =>inversion E;subst;clear E end;contradiction.
 - intros Ms ks x Os OO Eq;exfalso;apply NotSwitch;do 2 eexists;exact Eq.
 - intros Ms Os OO H;contradiction.
 - intros cst o2 Ms Os Mf OO Of OOO NE NS NI NF Inv JM JO JO' Bad.
   destruct(V293_enabled_join_frames _ _ _ _ _ _ _ _ JM)as(mid&Mall&JS&JF&Eq);subst o2.
   destruct(map_join_assoc JS JF)as(Mframe&JAll&JSF).
   destruct(Progress Mframe Mall JAll)as(Cf&mf&Next).
   inversion Bad;subst;exfalso.
   match goal with H:~(_ \/ _) |- _ =>apply H;left end.
   exists Cf;exists((mf,ir,(ie,nil,ci)):taskst);exists cst.
   eapply inapi_step;[reflexivity|apply ostc_step;exact Next|exact Inside].
 - intros Ms Os e1 e2 e3 ks OO Eq;exfalso;apply NotInit;do 4 eexists;exact Eq.
 - intros Ms Os e ks OO Eq;exfalso;apply NotFree;do 2 eexists;exact Eq.
Qed.

Lemma V293_helper_byte_successor : forall p y ks ge le M Cf mf,
 cstep p(curs(salloc nil(dcons y Tint8 dnil)),(kenil,ks))(ge,le,M)Cf mf ->
 exists b,fresh M b /\~indom le y /\
 Cf=(curs(salloc nil dnil),(kenil,ks)) /\
 mf=(ge,set le y(b,Tint8),allocb M b 0%Z(typelen Tint8)).
Proof.
 intros p y ks ge le M Cf mf Step;inversion Step;subst;inversion H;subst.
 - match goal with H:estep _ _ _ _ _ _ |- _ =>inversion H;subst;try discriminate end.
 - match goal with H:sstep _ _ _ _ _ _ _ |- _ =>inversion H;subst;try discriminate end.
   repeat match goal with E0:(_,_)=(_,_) |- _ =>inversion E0;clear E0;subst end.
   match goal with H:alloc _ _ _ _ _ _ |- _ =>destruct H as(b&Fresh&Mem&Absent&Env);subst end.
   exists b;split;[exact Fresh| ];split;[exact Absent| ];split;reflexivity.
Qed.

Lemma V293_helper_exec_successor : forall p f body y ks ge caller M Cf mf,
 p f=Some(Tvoid,dnil,dcons y Tint8 dnil,body) ->
 cstep p(curs(sfexec f nil nil),(kenil,ks))(ge,caller,M)Cf mf ->
 Cf=(curs(salloc nil(dcons y Tint8 dnil)),(kenil,kcall f body caller ks)) /\
 mf=(ge,(emp:env),M).
Proof.
 intros p f body y ks ge caller M Cf mf Bind Step;inversion Step;subst;inversion H;subst.
 - match goal with H:estep _ _ _ _ _ _ |- _ =>inversion H;subst;try discriminate end.
 - match goal with H:sstep _ _ _ _ _ _ _ |- _ =>inversion H;subst;try discriminate end.
   repeat match goal with E0:(_,_)=(_,_) |- _ =>inversion E0;clear E0;subst end.
   match goal with H:p f=Some _ |- _ =>rewrite Bind in H;inversion H;subst end.
   split;reflexivity.
Qed.

(* The body continuation remains an explicit obligation for every fresh block. *)
Theorem V293_sched_helper_call_TaskSim : forall pc po pi ip ph Ch O I Post t
 ks ge caller M ir ci op R f unmap group rows high y,
 po f=Some(V293_OSSchedNew_function unmap group rows high y) ->
 InOS(SKIP,(kenil,ks))(pumerge po pi) ->
 GoodInvAsrt R ->
 (forall s,s|=R ->s|=CurTid t **Atrue) ->
 (ge,caller,M,ir,(false,nil,ci),O,op)|=R ->
 (forall b,fresh M b ->
  (ge,set(emp:env)y(b,Tint8),allocb M b 0%Z(typelen Tint8),ir,(false,nil,ci),O,op)|=
    Amapsto(b,0%Z)Tint8 true Vundef **R ->
  TaskSim(pc,(po,pi,ip))
   (curs(V293_OSSchedNew_body unmap group rows high y),
    (kenil,kcall f(V293_OSSchedNew_body unmap group rows high y)caller ks))
   (ge,set(emp:env)y(b,Tint8),allocb M b 0%Z(typelen Tint8),ir,(false,nil,ci))
   ph Ch O V293_shared_li I Post t) ->
 TaskSim(pc,(po,pi,ip))(curs(scall f nil),(kenil,ks))
 (ge,caller,M,ir,(false,nil,ci))ph Ch O V293_shared_li I Post t.
Proof.
 intros pc po pi ip ph Ch O I Post t ks ge caller M ir ci op R f unmap group rows high y
 Bind Context Good Current Held Body.
 set(body:=V293_OSSchedNew_body unmap group rows high y).
 set(k:=kcall f body caller ks).
 assert(Program:(pumerge po pi)f=Some(Tvoid,dnil,dcons y Tint8 dnil,body)).
 { unfold pumerge;rewrite Bind;reflexivity. }
 assert(Inside:InOS(SKIP,(kenil,k))(pumerge po pi)).
 { unfold k;eapply V293_bound_call_inos;exact Bind. }
 assert(Local:forall le',satp(ge,le',M,ir,(false,nil,ci))O(CurLINV V293_shared_li t)).
 { intros le';eapply V293_pending_local with(op:=op);apply Current.
   eapply good_inv_prop;[exact Good|exact Held]. }
 assert(Allocated:forall b,fresh M b ->
  (ge,set(emp:env)y(b,Tint8),allocb M b 0%Z(typelen Tint8),ir,(false,nil,ci),O,op)|=
   Amapsto(b,0%Z)Tint8 true Vundef **R).
 { intros b Fresh;eapply V293_tick_allocate_frame;[exact Fresh| ].
   eapply good_inv_prop;[exact Good|exact Held]. }
 assert(AllocatedLocal:forall b,fresh M b ->
  satp(ge,set(emp:env)y(b,Tint8),allocb M b 0%Z(typelen Tint8),ir,(false,nil,ci))O
   (CurLINV V293_shared_li t)).
 { intros b Fresh;eapply V293_pending_local with(op:=op).
   pose proof(Allocated b Fresh)as Own.
   apply astar_mono with(P':=Amapsto(b,0%Z)Tint8 true Vundef)(Q':=CurTid t **Atrue)in Own;
    [sep auto|intros st H;exact H|exact Current]. }
 assert(AllocatedEnd:forall b,fresh M b ->
  TaskSim(pc,(po,pi,ip))(curs(salloc nil dnil),(kenil,k))
   (ge,set(emp:env)y(b,Tint8),allocb M b 0%Z(typelen Tint8),ir,(false,nil,ci))
   ph Ch O V293_shared_li I Post t).
 { intros b Fresh;eapply V293_invariant_cstep_TaskSim;
    [ | | |apply AllocatedLocal;exact Fresh|apply Body;[exact Fresh|apply Allocated;exact Fresh]].
   - eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
   - intros[x E];discriminate E.
   - intros Mf Mall Join;exists Mall;split;[exact Join| ].
     assert(Next:cstep(pumerge po pi)(curs(salloc nil dnil),(kenil,k))
      (ge,set(emp:env)y(b,Tint8),Mall)(curs body,(kenil,k))(ge,set(emp:env)y(b,Tint8),Mall)).
     { unfold k;eapply stmt_step;[reflexivity|apply sallocend_step]. }
     split;[exact Next| ];intros Cf mf Other.
     destruct(cstep_idmove_deter _ _ _ _ _ _ Next Other)as[EC EM];split;symmetry;assumption. }
 assert(Allocate:TaskSim(pc,(po,pi,ip))(curs(salloc nil(dcons y Tint8 dnil)),(kenil,k))
  (ge,(emp:env),M,ir,(false,nil,ci))ph Ch O V293_shared_li I Post t).
 { eapply V293_branching_cstep_TaskSim.
   - eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
   - intros[x E];discriminate E.
   - intros Mf Mall Join;destruct(memory_has_fresh_block Mall)as[b Fresh].
     exists(curs(salloc nil dnil),(kenil,k));
     exists(ge,set(emp:env)y(b,Tint8),allocb Mall b 0%Z(typelen Tint8)).
     eapply stmt_step;[reflexivity| ];eapply salloclv_step;[reflexivity|reflexivity| ].
     exists b;repeat split;try assumption;try reflexivity.
     intros[v E];rewrite map_emp_get in E;discriminate E.
   - intros Cf mf Step;destruct(V293_helper_byte_successor _ _ _ _ _ _ _ _ Step)
      as(b&Fresh&Absent&EC&EM);subst Cf mf.
     do 2 eexists;split;[reflexivity| ];split;
      [apply AllocatedLocal;exact Fresh|apply AllocatedEnd;exact Fresh]. }
 assert(Execute:TaskSim(pc,(po,pi,ip))(curs(sfexec f nil nil),(kenil,ks))
  (ge,caller,M,ir,(false,nil,ci))ph Ch O V293_shared_li I Post t).
 { eapply V293_invariant_cstep_TaskSim;[ | | |apply Local|exact Allocate].
   - eapply V293_context_inos;[exact Context|reflexivity|reflexivity].
   - intros[x E];discriminate E.
   - intros Mf Mall Join;exists Mall;split;[exact Join| ];split.
     + eapply stmt_step;[reflexivity| ];eapply sfexec_step with(d1:=dnil)(d2:=dcons y Tint8 dnil);
       [reflexivity|reflexivity|exact Program|exact Logic.I|reflexivity].
     + intros;eapply V293_helper_exec_successor;[exact Program|eassumption]. }
 eapply V293_invariant_cstep_TaskSim;[ | | |apply Local|exact Execute].
 - eapply V293_context_inos;[exact Context|reflexivity|reflexivity].
 - intros[x E];discriminate E.
 - intros Mf Mall Join;exists Mall;split;[exact Join| ].
   assert(Next:cstep(pumerge po pi)(curs(scall f nil),(kenil,ks))(ge,caller,Mall)
    (curs(sfexec f nil nil),(kenil,ks))(ge,caller,Mall)).
   { eapply stmt_step;[reflexivity|apply snpcall_step]. }
   split;[exact Next| ];intros Cf mf Other.
   destruct(cstep_idmove_deter _ _ _ _ _ _ Next Other)as[EC EM];split;symmetry;assumption.
Qed.
