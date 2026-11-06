(* Invariant-independent return steps; one suffix for both saved IE values. *)
Require Import CertiOS.certiucos.v293.proofs.V293EnabledPendingTaskSim.
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


Lemma V293_invariant_cstep_TaskSim : forall pc po pi ip ph Ch Cl Cl'
 ge le M le' M' ir ie ci O li I P t,
 InOS Cl(pumerge po pi) ->~IsEnd Cl ->
 (forall Mf Mall,join M Mf Mall ->exists Mall',join M' Mf Mall' /\
  cstep(pumerge po pi)Cl(ge,le,Mall)Cl'(ge,le',Mall') /\
  forall Cf mf,cstep(pumerge po pi)Cl(ge,le,Mall)Cf mf ->
   Cf=Cl' /\mf=(ge,le',Mall')) ->
 satp(ge,le',M',ir,(ie,nil,ci))O(CurLINV li t) ->
 TaskSim(pc,(po,pi,ip))Cl'(ge,le',M',ir,(ie,nil,ci))ph Ch O li I P t ->
 TaskSim(pc,(po,pi,ip))Cl(ge,le,M,ir,(ie,nil,ci))ph Ch O li I P t.
Proof.
 intros pc po pi ip ph Ch Cl Cl' ge le M le' M' ir ie ci O li I P t Inside End Frames Local Post.
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
   destruct(Frames Mframe Mall JAll)as(Mall'&JAll'&Next&Only).
   inversion Bad;subst;exfalso.
   match goal with H:~(_ \/ _) |- _ =>apply H;left end.
   exists Cl';exists((ge,le',Mall',ir,(ie,nil,ci)):taskst);exists cst.
   eapply inapi_step;[reflexivity|apply ostc_step;exact Next|exact Inside].
 - intros Ms Os e1 e2 e3 ks OO Eq;exfalso;apply NotInit;do 4 eexists;exact Eq.
 - intros Ms Os e ks OO Eq;exfalso;apply NotFree;do 2 eexists;exact Eq.
Qed.

Section NilShared.
Variable I : Inv.
Hypothesis Shape : getinv(I(S INUM))=Aemp.
Lemma V293_invariant_nil_empty : forall ge le Ms ir ci Os,
 satp(ge,le,Ms,ir,(false,nil,ci))Os(INV I) ->
 Ms=(emp:mem) /\Os=(emp:osabst).
Proof.
 intros ge le Ms ir ci Os Held;specialize(Held(spec_done None)).
 unfold INV in Held;rewrite Shape in Held.
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

Lemma V293_invariant_nil_close : forall ge le ir ci,
 satp(ge,le,(emp:mem),ir,(false,nil,ci))(emp:osabst)(INV I).
Proof.
 intros ge le ir ci ab;unfold INV;rewrite Shape.
 apply astar_l_aemp_intro;right;unfold inv_ieoff.
 apply sat_split';exists(emp:mem);exists(emp:mem);exists(emp:osabst);exists(emp:osabst).
 split;[apply map_join_emp| ];split;[apply map_join_emp| ];split;[repeat split;reflexivity| ].
 exists INUM;apply sat_split';exists(emp:mem);exists(emp:mem);exists(emp:osabst);exists(emp:osabst).
 split;[apply map_join_emp| ];split;[apply map_join_emp| ];split;[repeat split;reflexivity| ].
 right;split;[reflexivity|split;reflexivity].
Qed.
Lemma V293_invariant_excrit_TaskSim : forall pc po pi ip ph Ch ks
 ge le M Mt Ms ir top ci O Ot Os li P t,
 InOS(curs(sprim excrit),(kenil,ks))(pumerge po pi) ->
 join Mt Ms M ->join Ot Os O ->
 satp(ge,le,Ms,ir,(top,nil,ci))Os(INV I) ->
 satp(ge,le,Mt,ir,(top,nil,ci))Ot(CurLINV li t) ->
 TaskSim(pc,(po,pi,ip))(SKIP,(kenil,ks))(ge,le,Mt,ir,(top,nil,ci))ph Ch Ot li I P t ->
 TaskSim(pc,(po,pi,ip))(curs(sprim excrit),(kenil,ks))
 (ge,le,M,ir,(false,nil,top::ci))ph Ch O li I P t.
Proof.
 intros pc po pi ip ph Ch ks ge le M Mt Ms ir top ci O Ot Os li P t Inside Partition AbsPartition Shared Local Post.
 apply task_sim.
 - intros Cf Mshared Mf cst cst' ofull Oshared o2 OO Inv JM JO Step.
   destruct(V293_invariant_nil_empty _ _ _ _ _ _ Inv)as[EM EO];subst Mshared Oshared.
   apply map_join_emp' in JO;subst OO.
   destruct(V293_pending_join_frame _ _ _ _ _ _ _ JM)as(Mall&Join&Eq);subst o2.
   inversion Step;subst;
   match goal with E:(pc,(po,pi,ip))=(_,(_,_,_)) |- _ =>inversion E;subst;clear E end;try contradiction.
   match goal with H:loststep _ _ _ _ _ |- _ =>
    apply V293_excrit_successor in H;destruct H as[EC ES];subst Cf ofull end.
   exists Ch;exists O;exists((ge,le,Mt,ir,(top,nil,ci)):taskst);
   exists Ms;exists Ot;exists Os.
   split;[apply ht_starO| ];split.
   + exists((ge,le,M,ir,(top,nil,ci)):taskst);split;unfold joinmem.
     * do 6 eexists;split;[reflexivity| ];split;[reflexivity|exact Partition].
     * do 6 eexists;split;[reflexivity| ];split;[reflexivity|exact Join].
   + split;[exact AbsPartition| ];split;[exact Shared| ];split;assumption.
 - intros Cf Mshared Mf cst cst' ofull Oshared o2 OO ev Inv JM JO Step.
   inversion Step;subst.
   match goal with E:(pc,(po,pi,ip))=(_,(_,_,_)) |- _ =>inversion E;subst;clear E end;contradiction.
 - intros Mshared k x Oshared OO Eq;discriminate Eq.
 - intros Mshared Oshared OO(x&Eq);discriminate Eq.
 - intros cst o2 Mshared Oshared Mf OO Of OOO NE NS NI NF Inv JM JO JO' Bad.
   destruct(V293_invariant_nil_empty _ _ _ _ _ _ Inv)as[EM EO];subst Mshared Oshared.
   destruct(V293_pending_join_frame _ _ _ _ _ _ _ JM)as(Mall&Join&Eq);subst o2.
   inversion Bad;subst;exfalso.
   match goal with H:~(_ \/ _) |- _ =>apply H;left end.
   exists(SKIP,(kenil,ks));exists((ge,le,Mall,ir,(top,nil,ci)):taskst);exists cst.
   eapply inapi_step;[reflexivity|apply excrit_step;reflexivity|exact Inside].
 - intros Mshared Oshared e1 e2 e3 k OO Eq;discriminate Eq.
 - intros Mshared Oshared e k OO Eq;discriminate Eq.
Qed.

End NilShared.

Lemma V293_invariant_return_suffix : forall (I:Inv)(R:asrt) pc po pi ip A t ge M ir ie ci O op
 f body caller tail tau d1 d2 saved b v,
 po f=Some(tau,d1,d2,body) ->
 V293_skip_client_state(SKIP,(kenil,tail)) ->(forall i,ir i=false) ->
 GoodInvAsrt R ->
 (forall st,st|=R ->st|=CurTid t **Atrue) ->
 (forall ge' le' M' ir' ci' O' op', (forall i,ir' i=false) ->
 (ge',le',M',ir',(ie,nil,ci'),O',op')|=R ->
 (ge',le',M',ir',(ie,nil,ci'),O',op')|=RDYINV I t) ->
 (ge,V293_cpu_lenv saved b,M,ir,(ie,nil,ci),O,op)|=
 Amapsto(b,0%Z)Tint32 true v **R ->
 TaskSim(pc,(po,pi,ip))
 (SKIP,(kenil,kseq sret(kcall f body caller tail)))
 (ge,V293_cpu_lenv saved b,M,ir,(ie,nil,ci))
 (pc,A)(SKIP,(kenil,tail))O V293_shared_li I
 (fun s=>satp(fst s)(snd s)(RDYINV I t **LINV V293_shared_li t nil))t.
Proof.
 intros I R pc po pi ip A t ge M ir ie ci O op f body caller tail tau d1 d2 saved b v
 Bind Cases Clear Good Current ReadyR Held.
 assert(GoodCell:GoodInvAsrt(Amapsto(b,0%Z)Tint32 true v **R)).
 { split;[exact Logic.I|exact Good]. }
 assert(While:forall le' cs',satp(ge,le',M,ir,(ie,nil,cs'))O(CurLINV V293_shared_li t)).
 { intros le' cs';eapply V293_pending_local with(op:=op).
   assert(H:(ge,le',M,ir,(ie,nil,cs'),O,op)|=
    Amapsto(b,0%Z)Tint32 true v **R).
   { eapply good_inv_prop;[exact GoodCell|exact Held]. }
   apply astar_mono with(P':=Amapsto(b,0%Z)Tint32 true v)(Q':=CurTid t **Atrue) in H;
   [clear Held;sep auto|intros st HH;exact HH|exact Current]. }
 destruct(V293_tick_free_owned _ _ _ _ _ _ _ _ _ _ _ Held)as(Mret&Freed&Rest).
 assert(Ready:forall le' cs',satp(ge,le',Mret,ir,(ie,nil,cs'))O
 (RDYINV I t **LINV V293_shared_li t nil)).
 { intros le' cs' ab.
   assert(Rdy:(ge,le',Mret,ir,(ie,nil,cs'),O,ab)|=RDYINV I t).
   { apply ReadyR;[exact Clear|eapply good_inv_prop;[exact Good|exact Rest]]. }
   apply astar_r_aemp_intro in Rdy.
   eapply astar_mono;[intros st H;exact H|apply V293_switch_local_empty|exact Rdy]. }
 assert(After:forall le' cs',satp(ge,le',Mret,ir,(ie,nil,cs'))O(CurLINV V293_shared_li t)).
 { intros;eapply V293_return_ready_local;apply Ready. }
 assert(Inside:InOS(SKIP,(kenil,kcall f body caller tail))(pumerge po pi)).
 { eapply V293_bound_call_inos;exact Bind. }
 assert(End:TaskSim(pc,(po,pi,ip))(SKIP,(kenil,tail))
 (ge,caller,Mret,ir,(ie,nil,ci))(pc,A)(SKIP,(kenil,tail))O V293_shared_li I
 (fun s=>satp(fst s)(snd s)(RDYINV I t **LINV V293_shared_li t nil))t).
 { apply V293_return_client_coinduction;[exact Cases|apply After|apply Ready]. }
 assert(FreeEnd:TaskSim(pc,(po,pi,ip))(curs(sfree nil None),(kenil,kcall f body caller tail))
 (ge,V293_cpu_lenv saved b,Mret,ir,(ie,nil,ci))(pc,A)(SKIP,(kenil,tail))O V293_shared_li I
 (fun s=>satp(fst s)(snd s)(RDYINV I t **LINV V293_shared_li t nil))t).
 { eapply V293_invariant_cstep_TaskSim;[ | | |apply After|exact End].
   - eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
   - intros[x E];discriminate E.
   - intros Mf Mall Join;exists Mall;split;[exact Join| ].
     split.
     + eapply stmt_step;[reflexivity| ];eapply sfreeend_step;reflexivity.
     + intros;eapply V293_free_end_successor;eassumption. }
 assert(FreeCell:TaskSim(pc,(po,pi,ip))(curs(sfree((b,Tint32)::nil)None),(kenil,kcall f body caller tail))
 (ge,V293_cpu_lenv saved b,M,ir,(ie,nil,ci))(pc,A)(SKIP,(kenil,tail))O V293_shared_li I
 (fun s=>satp(fst s)(snd s)(RDYINV I t **LINV V293_shared_li t nil))t).
 { eapply V293_invariant_cstep_TaskSim;[ | | |apply After|exact FreeEnd].
   - eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
   - intros[x E];discriminate E.
   - intros Mf Mall Join;destruct(free_mono _ _ _ _ _ _ Join Freed)as(Mall'&Free').
     exists Mall';split;[eapply join_free;eassumption| ].
     split.
     + eapply stmt_step;[reflexivity| ];eapply sfree_step;[reflexivity|reflexivity|exact Free'].
     + intros;eapply V293_free_cell_successor;eassumption. }
 assert(Return:TaskSim(pc,(po,pi,ip))(curs sret,(kenil,kcall f body caller tail))
 (ge,V293_cpu_lenv saved b,M,ir,(ie,nil,ci))(pc,A)(SKIP,(kenil,tail))O V293_shared_li I
 (fun s=>satp(fst s)(snd s)(RDYINV I t **LINV V293_shared_li t nil))t).
 { eapply V293_invariant_cstep_TaskSim;[ | | |apply While|exact FreeCell].
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
 (ge,V293_cpu_lenv saved b,M,ir,(ie,nil,ci))(pc,A)(SKIP,(kenil,tail))O V293_shared_li I
 (fun s=>satp(fst s)(snd s)(RDYINV I t **LINV V293_shared_li t nil))t).
 { eapply V293_invariant_cstep_TaskSim;[ | | |apply While|exact Return].
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

(* Only logical resource closures are supplied: no execution or simulation
   result is accepted as a premise of this public bridge. *)
Theorem V293_invariant_pending_TaskSim : forall (I:Inv)(Core:asrt),
 getinv(I(S INUM))=Aemp ->GoodInvAsrt Core ->
 (forall ge le M ir ci O op,(forall i,ir i=false) ->
  (ge,le,M,ir,(false,nil,ci),O,op)|=Core ->
  (ge,le,M,ir,(false,nil,ci),O,op)|=SWINV I) ->
 (forall ge le M ir ci O op,(forall i,ir i=false) ->
  (ge,le,M,ir,(true,nil,ci),O,op)|=Core ->
  (ge,le,M,ir,(true,nil,ci),O,op)|=INV I) ->
 forall pc po pi ip A t ge M ir top ci O op f body caller tail tau d1 d2 saved b v,
 po f=Some(tau,d1,d2,body) ->V293_skip_client_state(SKIP,(kenil,tail)) ->
 (forall i,ir i=false) ->
 (ge,V293_cpu_lenv saved b,M,ir,(false,nil,top::ci),O,op)|=
 Amapsto(b,0%Z)Tint32 true v **(Core **CurTid t) ->
 TaskSim(pc,(po,pi,ip))
 (SKIP,(kenil,kseq(sprim excrit)(kseq sret(kcall f body caller tail))))
 (ge,V293_cpu_lenv saved b,M,ir,(false,nil,top::ci))
 (pc,A)(SKIP,(kenil,tail))O V293_shared_li I
 (fun st=>satp(fst st)(snd st)(RDYINV I t **LINV V293_shared_li t nil))t.
Proof.
 intros I Core Shape GoodCore Off On pc po pi ip A t ge M ir top ci O op
 f body caller tail tau d1 d2 saved b v Bind Cases Clear Held.
 assert(GoodCur:GoodInvAsrt(CurTid t)).
 { unfold CurTid,Agvarmapsto,Aptrmapsto;cbn[GoodInvAsrt];intros;repeat split;exact Logic.I. }
 assert(Good:GoodInvAsrt(Core **CurTid t))by(split;assumption).
 assert(GoodCell:GoodInvAsrt(Amapsto(b,0%Z)Tint32 true v **(Core **CurTid t)))by(split;[exact Logic.I|exact Good]).
 assert(While:forall le' cs',satp(ge,le',M,ir,(false,nil,cs'))O(CurLINV V293_shared_li t)).
 { intros le' cs';eapply V293_pending_local with(op:=op).
   assert(H:(ge,le',M,ir,(false,nil,cs'),O,op)|=Amapsto(b,0%Z)Tint32 true v **(Core **CurTid t)).
   { eapply good_inv_prop;[exact GoodCell|exact Held]. }
   clear Held;sep auto. }
 assert(Inside:InOS(SKIP,(kenil,kcall f body caller tail))(pumerge po pi)).
 { eapply V293_bound_call_inos;exact Bind. }
 assert(Exit:TaskSim(pc,(po,pi,ip))(curs(sprim excrit),(kenil,kseq sret(kcall f body caller tail)))
 (ge,V293_cpu_lenv saved b,M,ir,(false,nil,top::ci))(pc,A)(SKIP,(kenil,tail))O V293_shared_li I
 (fun st=>satp(fst st)(snd st)(RDYINV I t **LINV V293_shared_li t nil))t).
 { destruct top.
   - assert(Packed:(ge,V293_cpu_lenv saved b,M,ir,(false,nil,true::ci),O,op)|=
     (Amapsto(b,0%Z)Tint32 true v **CurTid t) **Core)by(sep auto).
     apply sat_split in Packed;destruct Packed as(Mt&Ms&Ot&Os&JM&JO&Task&Shared).
     assert(TaskOn:(ge,V293_cpu_lenv saved b,Mt,ir,(true,nil,ci),Ot,op)|=
      Amapsto(b,0%Z)Tint32 true v **CurTid t).
     { eapply good_inv_prop;[split;[exact Logic.I|exact GoodCur]|exact Task]. }
     eapply V293_invariant_excrit_TaskSim;[exact Shape| |exact JM|exact JO| | | ].
     + eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
     + intro ab;apply On;[exact Clear|eapply good_inv_prop;[exact GoodCore|exact Shared]].
     + eapply V293_pending_local with(op:=op);clear Held Task Shared;sep auto.
     + eapply V293_invariant_return_suffix with(R:=CurTid t);[exact Bind|exact Cases|exact Clear|exact GoodCur| | |exact TaskOn].
       * intros st H;sep auto.
       * intros g e m r c o a Empty H;left.
         apply sat_split';exists(emp:mem);exists m;exists(emp:osabst);exists o.
         split;[apply map_join_comm;apply map_join_emp| ];
         split;[apply map_join_comm;apply map_join_emp| ];split;[ |exact H].
         split;[repeat split;reflexivity|exists r;split;
         [repeat split;reflexivity|split;[exact Empty|split;reflexivity]]].
   - eapply V293_invariant_excrit_TaskSim with(Mt:=M)(Ms:=(emp:mem))(Ot:=O)(Os:=(emp:osabst));
     [exact Shape| |apply map_join_emp|apply map_join_emp|apply V293_invariant_nil_close;exact Shape|apply While| ].
     + eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
     + eapply V293_invariant_return_suffix with(R:=Core **CurTid t)(op:=op);[exact Bind|exact Cases|exact Clear|exact Good| | |eapply good_inv_prop;[exact GoodCell|exact Held]].
       * intros st H;sep auto.
       * intros g e m r c o a Empty H;right;unfold SWINVt;fold(CurTid t).
         apply sat_split in H;destruct H as(mc&mt&oc&ot&JM&JO&HC&HT).
         apply sat_split';exists mc;exists mt;exists oc;exists ot.
         split;[exact JM| ];split;[exact JO| ];split;[apply Off;assumption|exact HT]. }
 eapply V293_invariant_cstep_TaskSim;[ | | |apply While|exact Exit].
 - eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
 - intros[x E];discriminate E.
 - intros Mf Mall Join;exists Mall;split;[exact Join| ].
   assert(Next:cstep(pumerge po pi)(SKIP,(kenil,kseq(sprim excrit)(kseq sret(kcall f body caller tail))))
    (ge,V293_cpu_lenv saved b,Mall)(curs(sprim excrit),(kenil,kseq sret(kcall f body caller tail)))(ge,V293_cpu_lenv saved b,Mall)).
   { eapply stmt_step;[reflexivity|apply sskip_step]. }
   split;[exact Next| ];intros Cf mf H.
   destruct(cstep_idmove_deter _ _ _ _ _ _ Next H)as[EC EM];split;symmetry;assumption.
Qed.
