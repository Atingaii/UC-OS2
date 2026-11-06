(* Actual pending return, with universal external frames. The disabled,
   empty-interrupt-stack branch keeps shared resources empty throughout. *)
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

Section PendingReturn.
Variables br bg bp : block.
Variable target : var.
Variable tp : type.
Variable cells : list(addr*type).
Variable cache : block.
Let G:=V293_ready_current_inv br bg bp target tp cells cache.
Let Core:=V293_ready_current_core br bg bp target tp cells cache.

Lemma V293_pending_shared_empty : forall ge le Ms ir ci Os,
 satp(ge,le,Ms,ir,(false,nil,ci))Os(INV G) ->
 Ms=(emp:mem) /\Os=(emp:osabst).
Proof.
 intros ge le Ms ir ci Os Held;specialize(Held(spec_done None)).
 change((ge,le,Ms,ir,(false,nil,ci),Os,spec_done None)|=
 Aemp **(inv_ieon G \\//inv_ieoff G))in Held.
 apply astar_l_aemp_elim in Held;destruct Held as[On|Off].
 - unfold inv_ieon in On;apply sat_split in On.
   destruct On as(m1&m2&o1&o2&JM&JO&Flag&Rest).
   destruct Flag as[Flag _];discriminate Flag.
 - unfold inv_ieoff in Off;apply sat_split in Off.
   destruct Off as(m1&m2&o1&o2&JM&JO&Flag&k&Rest).
   destruct Flag as[_[EM EO]];cbn in EM;change(o1=(emp:osabst))in EO;subst m1 o1.
   apply map_join_comm in JM,JO;apply map_join_emp' in JM,JO;subst m2 o2.
   apply sat_split in Rest;destruct Rest as(m1&m2&o1&o2&JM&JO&Top&Choice).
   destruct Top as[Top[EM EO]];cbn in Top,EM;change(o1=(emp:osabst))in EO;subst k m1 o1.
   apply map_join_comm in JM,JO;apply map_join_emp' in JM,JO;subst m2 o2.
   destruct Choice as[Less|Equal].
   + apply astar_l_apure_elim in Less;destruct Less as[Less _];lia.
   + destruct Equal as[_[EM EO]];split;[exact EM|exact EO].
Qed.

Lemma V293_pending_join_frame : forall ge le M ir ci Mf o2,
 joinm2(ge,le,M,ir,(false,nil,ci))(emp:mem)Mf o2 ->
 exists Mall,join M Mf Mall /\o2=(ge,le,Mall,ir,(false,nil,ci)).
Proof.
 intros ge le M ir ci Mf o2(mid&J1&J2).
 unfold joinmem in J1,J2.
 destruct J1 as(g&e&m1&m2&i&aux&E1&E2&J1);inversion E1;subst.
 apply map_join_emp' in J1;subst m2.
 destruct J2 as(g2&e2&m12&m22&i2&aux2&E12&E22&J22);inversion E12;subst.
 exists m22;split;[exact J22|reflexivity].
Qed.

(* One internal step is sufficient only when it really progresses under
   EVERY external frame, has no other successor, and preserves ownership. *)
Lemma V293_pending_internal_TaskSim : forall pc po pi ip ph Ch Cl Cl'
 ge le M le' M' ir ci ci' O li P t,
 (forall i,ir i=false) ->InOS Cl(pumerge po pi) ->
 ~IsEnd Cl ->~IsSwitch Cl ->~IsStkInit Cl ->~IsStkFree Cl ->
 (forall Mf Mall,join M Mf Mall ->exists Mall',
  join M' Mf Mall' /\
  loststep(pumerge po pi)Cl(ge,le,Mall,ir,(false,nil,ci))
   Cl'(ge,le',Mall',ir,(false,nil,ci')) /\
  forall Cf ofull,loststep(pumerge po pi)Cl(ge,le,Mall,ir,(false,nil,ci))Cf ofull ->
   Cf=Cl' /\ofull=(ge,le',Mall',ir,(false,nil,ci'))) ->
 satp(ge,le',M',ir,(false,nil,ci'))O(CurLINV li t) ->
 TaskSim(pc,(po,pi,ip))Cl'(ge,le',M',ir,(false,nil,ci'))ph Ch O li G P t ->
 TaskSim(pc,(po,pi,ip))Cl(ge,le,M,ir,(false,nil,ci))ph Ch O li G P t.
Proof.
 intros pc po pi ip ph Ch Cl Cl' ge le M le' M' ir ci ci' O li P t
 Clear Inside End Switch Init Free Frames Local Post.
 apply task_sim.
 - intros Cf Ms Mf cst cst' ofull Os o2 OO Inv JM JO Step.
   destruct(V293_pending_shared_empty _ _ _ _ _ _ Inv)as[EM EO];subst Ms Os.
   apply map_join_emp' in JO;subst OO.
   destruct(V293_pending_join_frame _ _ _ _ _ _ _ JM)as(Mall&Join&Eq);subst o2.
   destruct(Frames Mf Mall Join)as(Mall'&Join'&Progress&Unique).
   inversion Step;subst;
   match goal with E:(pc,(po,pi,ip))=(_,(_,_,_)) |- _ =>inversion E;subst;clear E end;try contradiction.
   match goal with H:loststep _ _ _ _ _ |- _ =>destruct(Unique _ _ H)as[EC ES];subst Cf ofull end.
   exists Ch;exists O;exists((ge,le',M',ir,(false,nil,ci')):taskst);
   exists(emp:mem);exists O;exists(emp:osabst).
   split;[apply ht_starO| ];split.
   + exists((ge,le',M',ir,(false,nil,ci')):taskst);split;unfold joinmem.
     * do 6 eexists;split;[reflexivity| ];split;[reflexivity|apply map_join_emp].
     * do 6 eexists;split;[reflexivity| ];split;[reflexivity|exact Join'].
   + split;[apply map_join_emp| ];split.
     * intro ab;eapply V293_return_disabled_INV_empty;[exact Clear|cbn[gettopis];lia].
     * split;assumption.
 - intros Cf Ms Mf cst cst' ofull Os o2 OO ev Inv JM JO Step.
   inversion Step;subst.
   match goal with E:(pc,(po,pi,ip))=(_,(_,_,_)) |- _ =>inversion E;subst;clear E end.
   contradiction.
 - intros Ms ks x Os OO Eq;exfalso;apply Switch;exists x;exists ks;exact Eq.
 - intros Ms Os OO H;contradiction.
 - intros cst o2 Ms Os Mf OO Of OOO NE NS NI NF Inv JM JO JO' Bad.
   destruct(V293_pending_shared_empty _ _ _ _ _ _ Inv)as[EM EO];subst Ms Os.
   destruct(V293_pending_join_frame _ _ _ _ _ _ _ JM)as(Mall&Join&Eq);subst o2.
   destruct(Frames Mf Mall Join)as(Mall'&Join'&Progress&Unique).
   inversion Bad;subst;exfalso.
   match goal with H:~(_ \/ _) |- _ =>apply H;left end.
   exists Cl';exists((ge,le',Mall',ir,(false,nil,ci')):taskst);exists cst.
   eapply inapi_step;[reflexivity|exact Progress|exact Inside].
 - intros Ms Os e1 e2 e3 ks OO Eq;exfalso;apply Init;do 4 eexists;exact Eq.
 - intros Ms Os e ks OO Eq;exfalso;apply Free;do 2 eexists;exact Eq.
Qed.
Lemma V293_pending_cstep_successor : forall pu C m C' m' ir aux Cf ofull,
 cstep pu C m C' m' ->
 (forall C1 m1,cstep pu C m C1 m1 ->C1=C' /\m1=m') ->
 loststep pu C(m,ir,aux)Cf ofull ->
 Cf=C' /\ofull=(m',ir,aux).
Proof.
 intros pu C m C' m' ir aux Cf ofull Step Unique Low;inversion Low;subst;
 try solve[exfalso;eapply V293_cstep_not_primitive;[exact Step|reflexivity]].
 match goal with H:cstep _ _ _ _ _ |- _ =>
    destruct(Unique _ _ H)as[EC EM];subst;split;reflexivity end.
Qed.

Lemma V293_pending_cstep_TaskSim : forall pc po pi ip ph Ch Cl Cl'
 ge le M le' M' ir ci O P t,
 (forall i,ir i=false) ->InOS Cl(pumerge po pi) ->~IsEnd Cl ->
 (forall Mf Mall,join M Mf Mall ->exists Mall',join M' Mf Mall' /\
  cstep(pumerge po pi)Cl(ge,le,Mall)Cl'(ge,le',Mall') /\
  forall Cf mf,cstep(pumerge po pi)Cl(ge,le,Mall)Cf mf ->
   Cf=Cl' /\mf=(ge,le',Mall')) ->
 satp(ge,le',M',ir,(false,nil,ci))O(CurLINV V293_shared_li t) ->
 TaskSim(pc,(po,pi,ip))Cl'(ge,le',M',ir,(false,nil,ci))ph Ch O V293_shared_li G P t ->
 TaskSim(pc,(po,pi,ip))Cl(ge,le,M,ir,(false,nil,ci))ph Ch O V293_shared_li G P t.
Proof.
 intros pc po pi ip ph Ch Cl Cl' ge le M le' M' ir ci O P t Clear Inside End Frames Local Post.
 destruct(Frames(emp:mem)M(map_join_emp M))as(Mwhole&J&Step&Unique).
 eapply V293_pending_internal_TaskSim;try eassumption.
 - intros(x&ks&E);eapply V293_cstep_not_primitive;[exact Step|exact E].
 - intros(e1&e2&e3&ks&E);eapply V293_cstep_not_primitive;[exact Step|exact E].
 - intros(e&ks&E);eapply V293_cstep_not_primitive;[exact Step|exact E].
 - intros Mf Mall Join;destruct(Frames Mf Mall Join)as(Mall'&Join'&Next&Unique').
   exists Mall';split;[exact Join'| ];split;[apply ostc_step;exact Next| ].
   intros;eapply V293_pending_cstep_successor;[exact Next|exact Unique'|eassumption].
Qed.

Lemma V293_pending_local : forall ge le M ir aux O op t,
 (ge,le,M,ir,aux,O,op)|=CurTid t **Atrue ->
 satp(ge,le,M,ir,aux)O(CurLINV V293_shared_li t).
Proof.
 intros ge le M ir aux O op t Held ab;destruct aux as[[enabled si]ci].
 assert(Again:(ge,le,M,ir,(enabled,si,ci),O,ab)|=CurTid t **Atrue).
 { eapply good_inv_prop;[unfold CurTid,Agvarmapsto,Aptrmapsto;cbn[GoodInvAsrt];intros;repeat split;exact I|exact Held]. }
 unfold CurLINV;exists(nil:list logicvar).
 assert(Empty:forall st,st|=Aemp ->st|=LINV V293_shared_li t nil).
 { intros;apply V293_switch_local_empty;assumption. }
 apply astar_r_aemp_intro in Again.
 eapply astar_mono in Again;[ |intros s H;exact H|exact Empty].
 clear Held;sep auto.
Qed.

(* The saved cell is task-owned, not supplied by an arbitrary frame.
   The endpoint P is the original exact RDYINV/LINV packet, not Atrue. *)
Theorem V293_pending_return_TaskSim : forall pc po pi ip A t ge M ir ci O op
 f body caller tail tau d1 d2 saved b v,
 po f=Some(tau,d1,d2,body) ->
 V293_skip_client_state(SKIP,(kenil,tail)) ->(forall i,ir i=false) ->
 (ge,V293_cpu_lenv saved b,M,ir,(false,nil,false::ci),O,op)|=
 Amapsto(b,0%Z)Tint32 true v **(Core **CurTid t) ->
 TaskSim(pc,(po,pi,ip))
 (SKIP,(kenil,kseq(sprim excrit)(kseq sret(kcall f body caller tail))))
 (ge,V293_cpu_lenv saved b,M,ir,(false,nil,false::ci))
 (pc,A)(SKIP,(kenil,tail))O V293_shared_li G
 (fun s=>satp(fst s)(snd s)(RDYINV G t **LINV V293_shared_li t nil))t.
Proof.
 intros pc po pi ip A t ge M ir ci O op f body caller tail tau d1 d2 saved b v
 Bind Cases Clear Held.
 assert(Good:GoodInvAsrt(Core **CurTid t)).
 { split;[apply V293_current_core_good|unfold CurTid,Agvarmapsto,Aptrmapsto;cbn[GoodInvAsrt];intros;repeat split;exact I]. }
 assert(GoodCell:GoodInvAsrt(Amapsto(b,0%Z)Tint32 true v **(Core **CurTid t))).
 { split;[exact I|exact Good]. }
 assert(While:forall le' cs',satp(ge,le',M,ir,(false,nil,cs'))O(CurLINV V293_shared_li t)).
 { intros le' cs';eapply V293_pending_local with(op:=op).
   assert(H:(ge,le',M,ir,(false,nil,cs'),O,op)|=
    Amapsto(b,0%Z)Tint32 true v **(Core **CurTid t)).
   { eapply good_inv_prop;[exact GoodCell|exact Held]. }
   clear Held;sep auto. }
 destruct(V293_tick_free_owned _ _ _ _ _ _ _ _ _ _ _ Held)as(Mret&Freed&Rest).
 assert(Ready:forall le' cs',satp(ge,le',Mret,ir,(false,nil,cs'))O
 (RDYINV G t **LINV V293_shared_li t nil)).
 { intros le' cs' ab.
   assert(R:(ge,le',Mret,ir,(false,nil,cs'),O,ab)|=Core **CurTid t).
   { eapply good_inv_prop;[exact Good|exact Rest]. }
   apply astar_r_aemp_intro in R.
   assert(R':(ge,le',Mret,ir,(false,nil,cs'),O,ab)|=
    Core **(CurTid t **Aemp))by(sep auto).
   pose proof(V293_current_return_invariants br bg bp target tp cells cache t Aemp
    ge le' Mret ir false nil cs' O ab Clear ltac:(intros;cbn[gettopis];lia)R')as Partition.
   assert(Packet:(ge,le',Mret,ir,(false,nil,cs'),O,ab)|=RDYINV G t **Aemp).
   { apply sat_split in Partition;destruct Partition as(m1&m2&o1&o2&JM&JO&Shared&Empty).
     apply sat_split in Shared;destruct Shared as(ms&mt&os&ot&JMs&JOs&Inv&Task).
     assert(All:satp(ge,le',ms,ir,(false,nil,cs'))os(INV G)).
     { intro a;eapply INV_irrev_prop;exact Inv. }
     destruct(V293_pending_shared_empty _ _ _ _ _ _ All)as[EM EO];subst ms os.
     apply map_join_comm in JMs,JOs;apply map_join_emp' in JMs,JOs;subst mt ot.
     apply sat_split';exists m1;exists m2;exists o1;exists o2;
     split;[exact JM| ];split;[exact JO| ];split;assumption. }
   eapply astar_mono;[intros s H;exact H|apply V293_switch_local_empty|exact Packet]. }
 assert(After:forall le' cs',satp(ge,le',Mret,ir,(false,nil,cs'))O(CurLINV V293_shared_li t)).
 { intros;eapply V293_return_ready_local;apply Ready. }
 assert(Inside:InOS(SKIP,(kenil,kcall f body caller tail))(pumerge po pi)).
 { eapply V293_bound_call_inos;exact Bind. }
 assert(End:TaskSim(pc,(po,pi,ip))(SKIP,(kenil,tail))
 (ge,caller,Mret,ir,(false,nil,ci))(pc,A)(SKIP,(kenil,tail))O V293_shared_li G
 (fun s=>satp(fst s)(snd s)(RDYINV G t **LINV V293_shared_li t nil))t).
 { apply V293_return_client_coinduction;[exact Cases|apply After|apply Ready]. }
 assert(FreeEnd:TaskSim(pc,(po,pi,ip))(curs(sfree nil None),(kenil,kcall f body caller tail))
 (ge,V293_cpu_lenv saved b,Mret,ir,(false,nil,ci))(pc,A)(SKIP,(kenil,tail))O V293_shared_li G
 (fun s=>satp(fst s)(snd s)(RDYINV G t **LINV V293_shared_li t nil))t).
 { eapply V293_pending_cstep_TaskSim;[exact Clear| | | |apply After|exact End].
   - eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
   - intros[x E];discriminate E.
   - intros Mf Mall Join;exists Mall;split;[exact Join| ].
     split.
     + eapply stmt_step;[reflexivity| ];eapply sfreeend_step;reflexivity.
     + intros;eapply V293_free_end_successor;eassumption. }
 assert(FreeCell:TaskSim(pc,(po,pi,ip))(curs(sfree((b,Tint32)::nil)None),(kenil,kcall f body caller tail))
 (ge,V293_cpu_lenv saved b,M,ir,(false,nil,ci))(pc,A)(SKIP,(kenil,tail))O V293_shared_li G
 (fun s=>satp(fst s)(snd s)(RDYINV G t **LINV V293_shared_li t nil))t).
 { eapply V293_pending_cstep_TaskSim;[exact Clear| | | |apply After|exact FreeEnd].
   - eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
   - intros[x E];discriminate E.
   - intros Mf Mall Join;destruct(free_mono _ _ _ _ _ _ Join Freed)as(Mall'&Free').
     exists Mall';split;[eapply join_free;eassumption| ].
     split.
     + eapply stmt_step;[reflexivity| ];eapply sfree_step;[reflexivity|reflexivity|exact Free'].
     + intros;eapply V293_free_cell_successor;eassumption. }
 assert(Return:TaskSim(pc,(po,pi,ip))(curs sret,(kenil,kcall f body caller tail))
 (ge,V293_cpu_lenv saved b,M,ir,(false,nil,ci))(pc,A)(SKIP,(kenil,tail))O V293_shared_li G
 (fun s=>satp(fst s)(snd s)(RDYINV G t **LINV V293_shared_li t nil))t).
 { eapply V293_pending_cstep_TaskSim;[exact Clear| | | |apply While|exact FreeCell].
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
 (ge,V293_cpu_lenv saved b,M,ir,(false,nil,ci))(pc,A)(SKIP,(kenil,tail))O V293_shared_li G
 (fun s=>satp(fst s)(snd s)(RDYINV G t **LINV V293_shared_li t nil))t).
 { eapply V293_pending_cstep_TaskSim;[exact Clear| | | |apply While|exact Return].
   - eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
   - intros[x E];discriminate E.
   - intros Mf Mall Join;exists Mall;split;[exact Join| ].
     assert(Next:cstep(pumerge po pi)(SKIP,(kenil,kseq sret(kcall f body caller tail)))
      (ge,V293_cpu_lenv saved b,Mall)(curs sret,(kenil,kcall f body caller tail))(ge,V293_cpu_lenv saved b,Mall)).
     { eapply stmt_step;[reflexivity|apply sskip_step]. }
     split;[exact Next| ];intros Cf mf H.
     destruct(cstep_idmove_deter _ _ _ _ _ _ Next H)as[EC EM];split;symmetry;assumption. }
 assert(Exit:TaskSim(pc,(po,pi,ip))(curs(sprim excrit),(kenil,kseq sret(kcall f body caller tail)))
 (ge,V293_cpu_lenv saved b,M,ir,(false,nil,false::ci))(pc,A)(SKIP,(kenil,tail))O V293_shared_li G
 (fun s=>satp(fst s)(snd s)(RDYINV G t **LINV V293_shared_li t nil))t).
 { eapply V293_pending_internal_TaskSim;[exact Clear| | | | | | |apply While|exact SkipReturn].
   - eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
   - intros[x E];discriminate E.
   - intros(x&ks&E);discriminate E.
   - intros(e1&e2&e3&ks&E);discriminate E.
   - intros(e&ks&E);discriminate E.
   - intros Mf Mall Join;exists Mall;split;[exact Join| ];split.
     + apply excrit_step;reflexivity.
     + intros;eapply V293_excrit_successor;eassumption. }
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
End PendingReturn.
