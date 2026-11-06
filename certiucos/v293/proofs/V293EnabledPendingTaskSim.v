(* Enabled pending return: shared resources are quantified, never fixed. *)
Require Import CertiOS.certiucos.v293.proofs.V293PendingReturnTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293ReturnClientTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293CurrentReturnInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCurrentInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturnProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickReturnTail.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitch.
Require Import CertiOS.certiucos.v293.proofs.V293HandoffProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293SchedCallProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyFullCall.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCallGlobal.
Require Import CertiOS.certiucos.v293.proofs.V293ClientSkipTaskSim.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.simulation.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.framework.proof.memory_prop.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.


Lemma V293_enabled_join_frames : forall ge le M ir aux Ms Mf full,
 joinm2(ge,le,M,ir,aux)Ms Mf full ->
 exists mid Mall,join M Ms mid /\join mid Mf Mall /\full=(ge,le,Mall,ir,aux).
Proof.
 intros ge le M ir aux Ms Mf full(o&J1&J2).
 unfold joinmem in J1,J2.
 destruct J1 as(g&e&m1&m2&i&a&E1&E2&J1);inversion E1;subst.
 destruct J2 as(g2&e2&m12&m22&i2&a2&E12&E22&J22);inversion E12;subst.
 do 2 eexists;split;[exact J1| ];split;[exact J22|reflexivity].
Qed.

Lemma V293_enabled_cstep_TaskSim : forall pc po pi ip ph Ch Cl Cl'
 ge le M le' M' ir ci O li I P t,
 InOS Cl(pumerge po pi) ->~IsEnd Cl ->
 (forall Mf Mall,join M Mf Mall ->exists Mall',join M' Mf Mall' /\
  cstep(pumerge po pi)Cl(ge,le,Mall)Cl'(ge,le',Mall') /\
  forall Cf mf,cstep(pumerge po pi)Cl(ge,le,Mall)Cf mf ->
   Cf=Cl' /\mf=(ge,le',Mall')) ->
 satp(ge,le',M',ir,(true,nil,ci))O(CurLINV li t) ->
 TaskSim(pc,(po,pi,ip))Cl'(ge,le',M',ir,(true,nil,ci))ph Ch O li I P t ->
 TaskSim(pc,(po,pi,ip))Cl(ge,le,M,ir,(true,nil,ci))ph Ch O li I P t.
Proof.
 intros pc po pi ip ph Ch Cl Cl' ge le M le' M' ir ci O li I P t Inside End Frames Local Post.
 destruct(Frames(emp:mem)M(map_join_emp M))as(Mwhole&J&Step&Unique).
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
   destruct(Frames Mframe Mall JAll)as(Mall'&JAll'&Next&Only).
   inversion Low;subst;
   match goal with E:(pc,(po,pi,ip))=(_,(_,_,_)) |- _ =>inversion E;subst;clear E end;try contradiction.
   match goal with H:loststep _ _ _ _ _ |- _ =>
    destruct(V293_pending_cstep_successor _ _ _ _ _ _ _ _ _ Next Only H)as[EC ES];subst Cf ofull end.
   apply map_join_comm in JSF,JAll'.
   destruct(map_join_assoc JSF JAll')as(mid'&JF'&JS').
   apply map_join_comm in JF',JS'.
   exists Ch;exists OO;exists((ge,le',M',ir,(true,nil,ci)):taskst);
   exists Ms;exists O;exists Os.
   split;[apply ht_starO| ];split.
   + exists((ge,le',mid',ir,(true,nil,ci)):taskst);split;unfold joinmem.
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
   destruct(Frames Mframe Mall JAll)as(Mall'&JAll'&Next&Only).
   inversion Bad;subst;exfalso.
   match goal with H:~(_ \/ _) |- _ =>apply H;left end.
   exists Cl';exists((ge,le',Mall',ir,(true,nil,ci)):taskst);exists cst.
   eapply inapi_step;[reflexivity|apply ostc_step;exact Next|exact Inside].
 - intros Ms Os e1 e2 e3 ks OO Eq;exfalso;apply NotInit;do 4 eexists;exact Eq.
 - intros Ms Os e ks OO Eq;exfalso;apply NotFree;do 2 eexists;exact Eq.
Qed.

Section EnabledReturn.
Variables br bg bp : block.
Variable target : var.
Variable tp : type.
Variable cells : list(addr*type).
Variable cache : block.
Let G:=V293_ready_current_inv br bg bp target tp cells cache.
Let Core:=V293_ready_current_core br bg bp target tp cells cache.
(* At excrit, memory and total abstract state stay fixed; ownership moves. *)
Lemma V293_enabled_excrit_TaskSim : forall pc po pi ip ph Ch ks
 ge le M Mt Ms ir ci O Ot Os li P t,
 InOS(curs(sprim excrit),(kenil,ks))(pumerge po pi) ->
 join Mt Ms M ->join Ot Os O ->
 satp(ge,le,Ms,ir,(true,nil,ci))Os(INV G) ->
 satp(ge,le,Mt,ir,(true,nil,ci))Ot(CurLINV li t) ->
 TaskSim(pc,(po,pi,ip))(SKIP,(kenil,ks))(ge,le,Mt,ir,(true,nil,ci))ph Ch Ot li G P t ->
 TaskSim(pc,(po,pi,ip))(curs(sprim excrit),(kenil,ks))
 (ge,le,M,ir,(false,nil,true::ci))ph Ch O li G P t.
Proof.
 intros pc po pi ip ph Ch ks ge le M Mt Ms ir ci O Ot Os li P t Inside Partition AbsPartition Shared Local Post.
 apply task_sim.
 - intros Cf Mshared Mf cst cst' ofull Oshared o2 OO Inv JM JO Step.
   destruct(V293_pending_shared_empty br bg bp target tp cells cache _ _ _ _ _ _ Inv)as[EM EO];subst Mshared Oshared.
   apply map_join_emp' in JO;subst OO.
   destruct(V293_pending_join_frame _ _ _ _ _ _ _ JM)as(Mall&Join&Eq);subst o2.
   inversion Step;subst;
   match goal with E:(pc,(po,pi,ip))=(_,(_,_,_)) |- _ =>inversion E;subst;clear E end;try contradiction.
   match goal with H:loststep _ _ _ _ _ |- _ =>
    apply V293_excrit_successor in H;destruct H as[EC ES];subst Cf ofull end.
   exists Ch;exists O;exists((ge,le,Mt,ir,(true,nil,ci)):taskst);
   exists Ms;exists Ot;exists Os.
   split;[apply ht_starO| ];split.
   + exists((ge,le,M,ir,(true,nil,ci)):taskst);split;unfold joinmem.
     * do 6 eexists;split;[reflexivity| ];split;[reflexivity|exact Partition].
     * do 6 eexists;split;[reflexivity| ];split;[reflexivity|exact Join].
   + split;[exact AbsPartition| ];split;[exact Shared| ];split;assumption.
 - intros Cf Mshared Mf cst cst' ofull Oshared o2 OO ev Inv JM JO Step.
   inversion Step;subst.
   match goal with E:(pc,(po,pi,ip))=(_,(_,_,_)) |- _ =>inversion E;subst;clear E end;contradiction.
 - intros Mshared k x Oshared OO Eq;discriminate Eq.
 - intros Mshared Oshared OO(x&Eq);discriminate Eq.
 - intros cst o2 Mshared Oshared Mf OO Of OOO NE NS NI NF Inv JM JO JO' Bad.
   destruct(V293_pending_shared_empty br bg bp target tp cells cache _ _ _ _ _ _ Inv)as[EM EO];subst Mshared Oshared.
   destruct(V293_pending_join_frame _ _ _ _ _ _ _ JM)as(Mall&Join&Eq);subst o2.
   inversion Bad;subst;exfalso.
   match goal with H:~(_ \/ _) |- _ =>apply H;left end.
   exists(SKIP,(kenil,ks));exists((ge,le,Mall,ir,(true,nil,ci)):taskst);exists cst.
   eapply inapi_step;[reflexivity|apply excrit_step;reflexivity|exact Inside].
 - intros Mshared Oshared e1 e2 e3 k OO Eq;discriminate Eq.
 - intros Mshared Oshared e k OO Eq;discriminate Eq.
Qed.

Lemma V293_enabled_return_suffix : forall pc po pi ip A t ge M ir ci O op
 f body caller tail tau d1 d2 saved b v,
 po f=Some(tau,d1,d2,body) ->
 V293_skip_client_state(SKIP,(kenil,tail)) ->(forall i,ir i=false) ->
 (ge,V293_cpu_lenv saved b,M,ir,(true,nil,ci),O,op)|=
 Amapsto(b,0%Z)Tint32 true v **CurTid t ->
 TaskSim(pc,(po,pi,ip))
 (SKIP,(kenil,kseq sret(kcall f body caller tail)))
 (ge,V293_cpu_lenv saved b,M,ir,(true,nil,ci))
 (pc,A)(SKIP,(kenil,tail))O V293_shared_li G
 (fun s=>satp(fst s)(snd s)(RDYINV G t **LINV V293_shared_li t nil))t.
Proof.
 intros pc po pi ip A t ge M ir ci O op f body caller tail tau d1 d2 saved b v
 Bind Cases Clear Held.
 assert(Good:GoodInvAsrt(CurTid t)).
 { unfold CurTid,Agvarmapsto,Aptrmapsto;cbn[GoodInvAsrt];intros;repeat split;exact I. }
 assert(GoodCell:GoodInvAsrt(Amapsto(b,0%Z)Tint32 true v **CurTid t))by(split;[exact I|exact Good]).
 assert(While:forall le' cs',satp(ge,le',M,ir,(true,nil,cs'))O(CurLINV V293_shared_li t)).
 { intros le' cs';eapply V293_pending_local with(op:=op).
   assert(H:(ge,le',M,ir,(true,nil,cs'),O,op)|=Amapsto(b,0%Z)Tint32 true v **CurTid t).
   { eapply good_inv_prop;[exact GoodCell|exact Held]. }
   clear Held;sep auto. }
 destruct(V293_tick_free_owned _ _ _ _ _ _ _ _ _ _ _ Held)as(Mret&Freed&Rest).
 assert(Ready:forall le' cs',satp(ge,le',Mret,ir,(true,nil,cs'))O
 (RDYINV G t **LINV V293_shared_li t nil)).
 { intros le' cs' ab.
   assert(R:(ge,le',Mret,ir,(true,nil,cs'),O,ab)|=CurTid t).
   { eapply good_inv_prop;[exact Good|exact Rest]. }
   assert(Rdy:(ge,le',Mret,ir,(true,nil,cs'),O,ab)|=RDYINV G t).
   { left;apply sat_split';exists(emp:mem);exists Mret;exists(emp:osabst);exists O.
     split;[apply map_join_comm;apply map_join_emp| ];
     split;[apply map_join_comm;apply map_join_emp| ];split;[ |exact R].
     split;[repeat split;reflexivity|exists ir;split;
     [repeat split;reflexivity|split;[exact Clear|split;reflexivity]]]. }
   apply astar_r_aemp_intro in Rdy.
   eapply astar_mono;[intros st H;exact H|apply V293_switch_local_empty|exact Rdy]. }

 assert(After:forall le' cs',satp(ge,le',Mret,ir,(true,nil,cs'))O(CurLINV V293_shared_li t)).
 { intros;eapply V293_return_ready_local;apply Ready. }
 assert(Inside:InOS(SKIP,(kenil,kcall f body caller tail))(pumerge po pi)).
 { eapply V293_bound_call_inos;exact Bind. }
 assert(End:TaskSim(pc,(po,pi,ip))(SKIP,(kenil,tail))
 (ge,caller,Mret,ir,(true,nil,ci))(pc,A)(SKIP,(kenil,tail))O V293_shared_li G
 (fun s=>satp(fst s)(snd s)(RDYINV G t **LINV V293_shared_li t nil))t).
 { apply V293_return_client_coinduction;[exact Cases|apply After|apply Ready]. }
 assert(FreeEnd:TaskSim(pc,(po,pi,ip))(curs(sfree nil None),(kenil,kcall f body caller tail))
 (ge,V293_cpu_lenv saved b,Mret,ir,(true,nil,ci))(pc,A)(SKIP,(kenil,tail))O V293_shared_li G
 (fun s=>satp(fst s)(snd s)(RDYINV G t **LINV V293_shared_li t nil))t).
 { eapply V293_enabled_cstep_TaskSim;[ | | |apply After|exact End].
   - eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
   - intros[x E];discriminate E.
   - intros Mf Mall Join;exists Mall;split;[exact Join| ].
     split.
     + eapply stmt_step;[reflexivity| ];eapply sfreeend_step;reflexivity.
     + intros;eapply V293_free_end_successor;eassumption. }
 assert(FreeCell:TaskSim(pc,(po,pi,ip))(curs(sfree((b,Tint32)::nil)None),(kenil,kcall f body caller tail))
 (ge,V293_cpu_lenv saved b,M,ir,(true,nil,ci))(pc,A)(SKIP,(kenil,tail))O V293_shared_li G
 (fun s=>satp(fst s)(snd s)(RDYINV G t **LINV V293_shared_li t nil))t).
 { eapply V293_enabled_cstep_TaskSim;[ | | |apply After|exact FreeEnd].
   - eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
   - intros[x E];discriminate E.
   - intros Mf Mall Join;destruct(free_mono _ _ _ _ _ _ Join Freed)as(Mall'&Free').
     exists Mall';split;[eapply join_free;eassumption| ].
     split.
     + eapply stmt_step;[reflexivity| ];eapply sfree_step;[reflexivity|reflexivity|exact Free'].
     + intros;eapply V293_free_cell_successor;eassumption. }
 assert(Return:TaskSim(pc,(po,pi,ip))(curs sret,(kenil,kcall f body caller tail))
 (ge,V293_cpu_lenv saved b,M,ir,(true,nil,ci))(pc,A)(SKIP,(kenil,tail))O V293_shared_li G
 (fun s=>satp(fst s)(snd s)(RDYINV G t **LINV V293_shared_li t nil))t).
 { eapply V293_enabled_cstep_TaskSim;[ | | |apply While|exact FreeCell].
   - eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
   - intros[x E];discriminate E.
   - intros Mf Mall Join;exists Mall;split;[exact Join| ].
     assert(Next:cstep(pumerge po pi)(curs sret,(kenil,kcall f body caller tail))
      (ge,V293_cpu_lenv saved b,Mall)
      (curs(sfree((b,Tint32)::nil)None),(kenil,kcall f body caller tail))(ge,V293_cpu_lenv saved b,Mall)).
     { eapply stmt_step;[reflexivity| ];eapply sret_step;[reflexivity|reflexivity|apply V293_cpu_layout]. }
     split;[exact Next| ];intros Cf mf H.
     destruct(cstep_idmove_deter _ _ _ _ _ _ Next H)as[EC EM];split;symmetry;assumption. }
 assert(SkipReturn:TaskSim(pc,(po,pi,ip))(SKIP,(kenil,kseq sret(kcall f body caller tail)))
 (ge,V293_cpu_lenv saved b,M,ir,(true,nil,ci))(pc,A)(SKIP,(kenil,tail))O V293_shared_li G
 (fun s=>satp(fst s)(snd s)(RDYINV G t **LINV V293_shared_li t nil))t).
 { eapply V293_enabled_cstep_TaskSim;[ | | |apply While|exact Return].
   - eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
   - intros[x E];discriminate E.
   - intros Mf Mall Join;exists Mall;split;[exact Join| ].
     assert(Next:cstep(pumerge po pi)(SKIP,(kenil,kseq sret(kcall f body caller tail)))
      (ge,V293_cpu_lenv saved b,Mall)(curs sret,(kenil,kcall f body caller tail))(ge,V293_cpu_lenv saved b,Mall)).
     { eapply stmt_step;[reflexivity|apply sskip_step]. }
     split;[exact Next| ];intros Cf mf H.
     destruct(cstep_idmove_deter _ _ _ _ _ _ Next H)as[EC EM];split;symmetry;assumption. }
 exact SkipReturn.
Qed.
Theorem V293_enabled_pending_TaskSim : forall pc po pi ip A t ge M ir ci O op
 f body caller tail tau d1 d2 saved b v,
 po f=Some(tau,d1,d2,body) ->
 V293_skip_client_state(SKIP,(kenil,tail)) ->(forall i,ir i=false) ->
 (ge,V293_cpu_lenv saved b,M,ir,(false,nil,true::ci),O,op)|=
 Amapsto(b,0%Z)Tint32 true v **(Core **CurTid t) ->
 TaskSim(pc,(po,pi,ip))
 (SKIP,(kenil,kseq(sprim excrit)(kseq sret(kcall f body caller tail))))
 (ge,V293_cpu_lenv saved b,M,ir,(false,nil,true::ci))
 (pc,A)(SKIP,(kenil,tail))O V293_shared_li G
 (fun s=>satp(fst s)(snd s)(RDYINV G t **LINV V293_shared_li t nil))t.
Proof.
 intros pc po pi ip A t ge M ir ci O op f body caller tail tau d1 d2 saved b v Bind Cases Clear Held.
 assert(Good:GoodInvAsrt(Core **CurTid t)).
 { split;[apply V293_current_core_good|unfold CurTid,Agvarmapsto,Aptrmapsto;cbn[GoodInvAsrt];intros;repeat split;exact I]. }
 assert(GoodCell:GoodInvAsrt(Amapsto(b,0%Z)Tint32 true v **(Core **CurTid t)))by(split;[exact I|exact Good]).
 assert(While:forall le' cs',satp(ge,le',M,ir,(false,nil,cs'))O(CurLINV V293_shared_li t)).
 { intros le' cs';eapply V293_pending_local with(op:=op).
   assert(H:(ge,le',M,ir,(false,nil,cs'),O,op)|=Amapsto(b,0%Z)Tint32 true v **(Core **CurTid t)).
   { eapply good_inv_prop;[exact GoodCell|exact Held]. }
   clear Held;sep auto. }
 assert(Packed:(ge,V293_cpu_lenv saved b,M,ir,(false,nil,true::ci),O,op)|=
 (Amapsto(b,0%Z)Tint32 true v **CurTid t) **Core)by(sep auto).
 apply sat_split in Packed;destruct Packed as(Mt&Ms&Ot&Os&JM&JO&Task&Shared).
 assert(TaskOn:(ge,V293_cpu_lenv saved b,Mt,ir,(true,nil,ci),Ot,op)|=
 Amapsto(b,0%Z)Tint32 true v **CurTid t).
 { eapply good_inv_prop;[split;[exact I|exact(proj2 Good)]|exact Task]. }
 assert(SharedOn:satp(ge,V293_cpu_lenv saved b,Ms,ir,(true,nil,ci))Os(INV G)).
 { intro ab;apply V293_return_enabled_INV;[exact Clear| ].
   eapply good_inv_prop;[apply V293_current_core_good|exact Shared]. }
 assert(LocalOn:satp(ge,V293_cpu_lenv saved b,Mt,ir,(true,nil,ci))Ot(CurLINV V293_shared_li t)).
 { eapply V293_pending_local with(op:=op);clear Held Task Shared;sep auto. }
 assert(Suffix:TaskSim(pc,(po,pi,ip))(SKIP,(kenil,kseq sret(kcall f body caller tail)))
 (ge,V293_cpu_lenv saved b,Mt,ir,(true,nil,ci))(pc,A)(SKIP,(kenil,tail))Ot V293_shared_li G
 (fun s=>satp(fst s)(snd s)(RDYINV G t **LINV V293_shared_li t nil))t).
 { eapply V293_enabled_return_suffix;[exact Bind|exact Cases|exact Clear|exact TaskOn]. }
 assert(Inside:InOS(SKIP,(kenil,kcall f body caller tail))(pumerge po pi)).
 { eapply V293_bound_call_inos;exact Bind. }
 assert(Exit:TaskSim(pc,(po,pi,ip))(curs(sprim excrit),(kenil,kseq sret(kcall f body caller tail)))
 (ge,V293_cpu_lenv saved b,M,ir,(false,nil,true::ci))(pc,A)(SKIP,(kenil,tail))O V293_shared_li G
 (fun s=>satp(fst s)(snd s)(RDYINV G t **LINV V293_shared_li t nil))t).
 { eapply V293_enabled_excrit_TaskSim;[ |exact JM|exact JO|exact SharedOn|exact LocalOn|exact Suffix].
   eapply V293_context_inos;[exact Inside|reflexivity|reflexivity]. }
 eapply V293_pending_cstep_TaskSim;[exact Clear| | | |apply While|exact Exit].
 - eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
 - intros[x E];discriminate E.
 - intros Mf Mall Join;exists Mall;split;[exact Join| ].
   assert(Next:cstep(pumerge po pi)(SKIP,(kenil,kseq(sprim excrit)(kseq sret(kcall f body caller tail))))
    (ge,V293_cpu_lenv saved b,Mall)(curs(sprim excrit),(kenil,kseq sret(kcall f body caller tail)))(ge,V293_cpu_lenv saved b,Mall)).
   { eapply stmt_step;[reflexivity|apply sskip_step]. }
   split;[exact Next| ];intros Cf mf H.
   destruct(cstep_idmove_deter _ _ _ _ _ _ Next H)as[EC EM];split;symmetry;assumption.
Qed.
End EnabledReturn.
