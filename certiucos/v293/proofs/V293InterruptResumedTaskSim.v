(* Actual return under a saved interrupt context, not a schedule-back claim. *)
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


Require Import CertiOS.certiucos.v293.proofs.V293SelectedScalarTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.

Lemma V293_interrupt_cstep_TaskSim : forall pc po pi ip ph Ch Cl Cl'
 ge le M le' M' ir ie si ci O li I P t,
 InOS Cl(pumerge po pi) ->~IsEnd Cl ->
 (forall Mf Mall,join M Mf Mall ->exists Mall',join M' Mf Mall' /\
  cstep(pumerge po pi)Cl(ge,le,Mall)Cl'(ge,le',Mall') /\
  forall Cf mf,cstep(pumerge po pi)Cl(ge,le,Mall)Cf mf ->
   Cf=Cl' /\mf=(ge,le',Mall')) ->
 satp(ge,le',M',ir,(ie,si,ci))O(CurLINV li t) ->
 TaskSim(pc,(po,pi,ip))Cl'(ge,le',M',ir,(ie,si,ci))ph Ch O li I P t ->
 TaskSim(pc,(po,pi,ip))Cl(ge,le,M,ir,(ie,si,ci))ph Ch O li I P t.
Proof.
 intros pc po pi ip ph Ch Cl Cl' ge le M le' M' ir ie si ci O li I P t Inside End Frames Local Post.
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
   exists Ch;exists OO;exists((ge,le',M',ir,(ie,si,ci)):taskst);
   exists Ms;exists O;exists Os.
   split;[apply ht_starO| ];split.
   + exists((ge,le',mid',ir,(ie,si,ci)):taskst);split;unfold joinmem.
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
   exists Cl';exists((ge,le',Mall',ir,(ie,si,ci)):taskst);exists cst.
   eapply inapi_step;[reflexivity|apply ostc_step;exact Next|exact Inside].
 - intros Ms Os e1 e2 e3 ks OO Eq;exfalso;apply NotInit;do 4 eexists;exact Eq.
 - intros Ms Os e ks OO Eq;exfalso;apply NotFree;do 2 eexists;exact Eq.
Qed.


Section InterruptReturn.
Variables br bg bp : block.
Variable target : var.
Variable tp : type.
Variable cells : list(addr*type).
Variable cache : block.
Let G:=V293_ready_current_inv br bg bp target tp cells cache.
Let Core:=V293_ready_current_core br bg bp target tp cells cache.

Lemma V293_interrupt_isr_tail_empty : forall n k st,
 st|=starinv_isr G(S k)n ->st|=Aemp.
Proof.
 induction n;intros k st Held;cbn[starinv_isr]in Held.
 - change(st|=EX r:isr,([|r(S k)=true|] //\\ Aisr r) \\//
    ([|r(S k)=false|] //\\ Aisr r) **Aemp)in Held.
   destruct Held as[r[On|Off]].
   + destruct On as[_[_ Empty]];exact Empty.
   + apply astar_r_aemp_elim in Off;destruct Off as[_[_ Empty]];exact Empty.
 - destruct st as[[[[[[ge le]M]ir]aux]O]op].
   apply sat_split in Held;destruct Held as(m1&m2&o1&o2&JM&JO&Flag&Rest).
   assert(Empty1:(ge,le,m1,ir,aux,o1,op)|=Aemp).
   { change((ge,le,m1,ir,aux,o1,op)|=EX r:isr,([|r(S k)=true|] //\\ Aisr r) \\//
     ([|r(S k)=false|] //\\ Aisr r) **Aemp)in Flag.
     destruct Flag as[r[On|Off]].
     - destruct On as[_[_ Empty]];exact Empty.
     - apply astar_r_aemp_elim in Off;destruct Off as[_[_ Empty]];exact Empty. }
   specialize(IHn(S k)(ge,le,m2,ir,aux,o2,op)Rest).
   destruct Empty1 as[EM EO];cbn in EM;change(o1=(emp:osabst))in EO;subst m1 o1.
   apply map_join_comm in JM,JO;apply map_join_emp' in JM,JO;subst m2 o2;exact IHn.
Qed.

Lemma V293_interrupt_shared_empty : forall ge le Ms ir si ci Os,
 satp(ge,le,Ms,ir,(false,si,ci))Os(INV G) ->
 Ms=(emp:mem) /\Os=(emp:osabst).
Proof.
 intros ge le Ms ir si ci Os Held;specialize(Held(spec_done None)).
 change((ge,le,Ms,ir,(false,si,ci),Os,spec_done None)|=
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
   destruct Top as[Top[EM EO]];cbn in EM;change(o1=(emp:osabst))in EO;subst k m1 o1.
   apply map_join_comm in JM,JO;apply map_join_emp' in JM,JO;subst m2 o2.
   destruct Choice as[Less|Equal].
   + apply astar_l_apure_elim in Less;destruct Less as[Less Rest].
     unfold invlth_isr in Rest;cbn[gettopis getis gettaskst]in Rest.
     replace(gettopis si+1)with(S(gettopis si))in Rest by lia.
     exact(V293_interrupt_isr_tail_empty _ _ _ Rest).
   + destruct Equal as[_[EM EO]];split;[exact EM|exact EO].
Qed.

Lemma V293_interrupt_internal_TaskSim : forall pc po pi ip ph Ch Cl Cl'
 ge le M le' M' ir si ci ci' O li P t,
 (forall i,ir i=false) ->gettopis si<=INUM ->InOS Cl(pumerge po pi) ->
 ~IsEnd Cl ->~IsSwitch Cl ->~IsStkInit Cl ->~IsStkFree Cl ->
 (forall Mf Mall,join M Mf Mall ->exists Mall',
  join M' Mf Mall' /\
  loststep(pumerge po pi)Cl(ge,le,Mall,ir,(false,si,ci))
   Cl'(ge,le',Mall',ir,(false,si,ci')) /\
  forall Cf ofull,loststep(pumerge po pi)Cl(ge,le,Mall,ir,(false,si,ci))Cf ofull ->
   Cf=Cl' /\ofull=(ge,le',Mall',ir,(false,si,ci'))) ->
 satp(ge,le',M',ir,(false,si,ci'))O(CurLINV li t) ->
 TaskSim(pc,(po,pi,ip))Cl'(ge,le',M',ir,(false,si,ci'))ph Ch O li G P t ->
 TaskSim(pc,(po,pi,ip))Cl(ge,le,M,ir,(false,si,ci))ph Ch O li G P t.
Proof.
 intros pc po pi ip ph Ch Cl Cl' ge le M le' M' ir si ci ci' O li P t
 Clear Bound Inside End Switch Init Free Frames Local Post.
 apply task_sim.
 - intros Cf Ms Mf cst cst' ofull Os o2 OO Inv JM JO Step.
   destruct(V293_interrupt_shared_empty _ _ _ _ _ _ _ Inv)as[EM EO];subst Ms Os.
   apply map_join_emp' in JO;subst OO.
   destruct(V293_enabled_join_frames _ _ _ _ _ _ _ _ JM)as(mid&Mall&JE&Join&Eq);subst o2.
   apply map_join_emp' in JE;subst mid.
   destruct(Frames Mf Mall Join)as(Mall'&Join'&Progress&Unique).
   inversion Step;subst;
   match goal with E:(pc,(po,pi,ip))=(_,(_,_,_)) |- _ =>inversion E;subst;clear E end;try contradiction.
   match goal with H:loststep _ _ _ _ _ |- _ =>destruct(Unique _ _ H)as[EC ES];subst Cf ofull end.
   exists Ch;exists O;exists((ge,le',M',ir,(false,si,ci')):taskst);
   exists(emp:mem);exists O;exists(emp:osabst).
   split;[apply ht_starO| ];split.
   + exists((ge,le',M',ir,(false,si,ci')):taskst);split;unfold joinmem.
     * do 6 eexists;split;[reflexivity| ];split;[reflexivity|apply map_join_emp].
     * do 6 eexists;split;[reflexivity| ];split;[reflexivity|exact Join'].
   + split;[apply map_join_emp| ];split.
     * intro ab;eapply V293_return_disabled_INV_empty;[exact Clear|exact Bound].
     * split;assumption.
 - intros Cf Ms Mf cst cst' ofull Os o2 OO ev Inv JM JO Step.
   inversion Step;subst.
   match goal with E:(pc,(po,pi,ip))=(_,(_,_,_)) |- _ =>inversion E;subst;clear E end.
   contradiction.
 - intros Ms ks x Os OO Eq;exfalso;apply Switch;exists x;exists ks;exact Eq.
 - intros Ms Os OO H;contradiction.
 - intros cst o2 Ms Os Mf OO Of OOO NE NS NI NF Inv JM JO JO' Bad.
   destruct(V293_interrupt_shared_empty _ _ _ _ _ _ _ Inv)as[EM EO];subst Ms Os.
   destruct(V293_enabled_join_frames _ _ _ _ _ _ _ _ JM)as(mid&Mall&JE&Join&Eq);subst o2.
   apply map_join_emp' in JE;subst mid.
   destruct(Frames Mf Mall Join)as(Mall'&Join'&Progress&Unique).
   inversion Bad;subst;exfalso.
   match goal with H:~(_ \/ _) |- _ =>apply H;left end.
   exists Cl';exists((ge,le',Mall',ir,(false,si,ci')):taskst);exists cst.
   eapply inapi_step;[reflexivity|exact Progress|exact Inside].
 - intros Ms Os e1 e2 e3 ks OO Eq;exfalso;apply Init;do 4 eexists;exact Eq.
 - intros Ms Os e ks OO Eq;exfalso;apply Free;do 2 eexists;exact Eq.
Qed.


Lemma V293_interrupt_iret_successor : forall pu c ke caller ks ge le M ir ie i si ci Cf ofull,
 loststep pu(curs(sprim exint),(kenil,kint c ke caller ks))
 (ge,le,M,ir,(ie,i::si,ci))Cf ofull ->
 Cf=(c,(ke,ks)) /\ofull=(ge,caller,M,ir,(true,si,ci)).
Proof.
 intros pu c ke caller ks ge le M ir ie i si ci Cf ofull Step.
 inversion Step;subst;
 repeat match goal with H:(_,_) = (_,_) |- _=>inversion H;clear H;subst end;try discriminate.
 - exfalso;eapply V293_cstep_not_primitive;[eassumption|reflexivity].
 - repeat match goal with H:(_,_) = (_,_) |- _=>inversion H;clear H;subst end.
   cbn[intcont]in *;repeat match goal with H:Some _=Some _ |- _=>inversion H;clear H;subst end.
   split;reflexivity.
Qed.

(* The high-level client is already the interrupted continuation. The low
   level must actually execute exint, move the core back to shared INV,
   and reconstruct its successor TaskSim, not assume it. *)
Theorem V293_interrupt_iret_TaskSim : forall pc po pi ip A t ge le M ir i si ci O op
 c ke caller ks,
 V293_scalar_client_state(c,(ke,ks)) ->(forall j,ir j=false) ->
 (ge,le,M,ir,(false,i::si,ci),O,op)|=Core **CurTid t ->
 TaskSim(pc,(po,pi,ip))(curs(sprim exint),(kenil,kint c ke caller ks))
 (ge,le,M,ir,(false,i::si,ci))(pc,A)(c,(ke,ks))O V293_shared_li G
 (fun s=>satp(fst s)(snd s)(RDYINV G t **LINV V293_shared_li t nil))t.
Proof.
 intros pc po pi ip A t ge le M ir i si ci O op c ke caller ks Cases Clear Held.
 assert(Inside:InOS(curs(sprim exint),(kenil,kint c ke caller ks))(pumerge po pi)).
 { do 3 eexists;split;[reflexivity| ];right;right;discriminate. }
 assert(Good:GoodInvAsrt(Core **CurTid t)).
 { split;[apply V293_current_core_good|unfold CurTid,Agvarmapsto,Aptrmapsto;cbn[GoodInvAsrt];intros;repeat split;exact I]. }
 assert(After:(ge,caller,M,ir,(true,si,ci),O,op)|=
 Core **(CurTid t **(LINV V293_shared_li t nil **Aemp))).
 { assert(H:(ge,caller,M,ir,(true,si,ci),O,op)|=Core **CurTid t).
   { apply sat_split in Held;destruct Held as(mc&mt&oc&ot&JM&JO&CH&CT).
     apply sat_split';exists mc;exists mt;exists oc;exists ot.
     split;[exact JM| ];split;[exact JO| ];split;[ |exact CT].
     assert(CA:(ge,le,mc,ir,(true,si,ci),oc,op)|=Core).
     { eapply V293_current_core_aux;exact CH. }
     eapply good_inv_prop;[apply V293_current_core_good|exact CA]. }
   apply astar_r_aemp_intro in H.
   eapply astar_mono in H;[ |intros st X;exact X|apply V293_switch_local_empty].
   clear Held;sep auto. }
 destruct(V293_scalar_current_TaskSim br bg bp target tp cells cache pc po pi ip A
 (c,(ke,ks))V293_shared_li nil t Aemp ge caller M ir true si ci O op
 Cases Clear ltac:(discriminate)After)
 as(Ms&Mt&Mf&Mtail&Os&Ot&Of&Otail&JT&JM&JOT&JO&Shared&Ready&Empty&Client).
 destruct Empty as[EM EO];cbn in EM;change(Of=(emp:osabst))in EO;subst Mf Of.
 apply map_join_emp' in JT,JOT;subst Mtail Otail.
 assert(Local:satp(ge,caller,Mt,ir,(true,si,ci))Ot(CurLINV V293_shared_li t)).
 { eapply V293_return_ready_local;exact Ready. }
 apply task_sim.
 - intros Cf Mshared Frame cst cst' full Oshared o2 OO Inv JAll JAbs Step.
   destruct(V293_interrupt_shared_empty _ _ _ _ _ _ _ Inv)as[EM EO];subst Mshared Oshared.
   apply map_join_emp' in JAbs;subst OO.
   destruct(V293_enabled_join_frames _ _ _ _ _ _ _ _ JAll)as(mid&Mall&JE&JFrame&Eq);subst o2.
   apply map_join_emp' in JE;subst mid.
   inversion Step;subst;
   match goal with E:(pc,(po,pi,ip))=(_,(_,_,_)) |- _=>inversion E;subst;clear E end;try contradiction.
   match goal with H:loststep _ _ _ _ _ |- _=>
   destruct(V293_interrupt_iret_successor _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H)as[EC ES];subst Cf full end.
   exists(c,(ke,ks));exists O;exists((ge,caller,Mt,ir,(true,si,ci)):taskst);
   exists Ms;exists Ot;exists Os.
   split;[apply ht_starO| ];split.
   + exists((ge,caller,M,ir,(true,si,ci)):taskst);split;unfold joinmem.
     * do 6 eexists;split;[reflexivity| ];split;[reflexivity|apply map_join_comm;exact JM].
     * do 6 eexists;split;[reflexivity| ];split;[reflexivity|exact JFrame].
   + split;[apply map_join_comm;exact JO| ];split;[exact Shared| ];split;assumption.
 - intros Cf Mshared Frame cst cst' full Oshared o2 OO ev Inv JAll JAbs Step.
   inversion Step;subst;
   match goal with E:(pc,(po,pi,ip))=(_,(_,_,_)) |- _=>inversion E;subst;clear E end;contradiction.
 - intros Mshared k x Oshared OO Eq;discriminate.
 - intros Mshared Oshared OO(v&Eq);discriminate.
 - intros cst o2 Mshared Oshared Frame OO Of OOO NE NS NI NF Inv JAll JAbs JMore Bad.
   destruct(V293_interrupt_shared_empty _ _ _ _ _ _ _ Inv)as[EM EO];subst Mshared Oshared.
   destruct(V293_enabled_join_frames _ _ _ _ _ _ _ _ JAll)as(mid&Mall&JE&JFrame&Eq);subst o2.
   apply map_join_emp' in JE;subst mid.
   inversion Bad;subst;exfalso.
   match goal with H:~(_ \/ _) |- _=>apply H;left end.
   exists(c,(ke,ks));exists((ge,caller,Mall,ir,(true,si,ci)):taskst);exists cst.
   eapply inapi_step;[reflexivity|eapply exint_step;reflexivity|exact Inside].
 - intros Mshared Oshared e1 e2 e3 k OO Eq;discriminate.
 - intros Mshared Oshared e k OO Eq;discriminate.
Qed.

(* Pending source-bound Exit, with its actual saved interrupt context.
   No successor simulation or successful free result is an input. *)
Theorem V293_interrupt_pending_return_TaskSim : forall pc po pi ip A t ge M ir i si ci O op
 f body caller c ke interrupted_env ks tau d1 d2 saved b v,
 po f=Some(tau,d1,d2,body) ->i<INUM ->
 V293_scalar_client_state(c,(ke,ks)) ->(forall j,ir j=false) ->
 let tail:=kseq(sprim exint)(kint c ke interrupted_env ks)in
 (ge,V293_cpu_lenv saved b,M,ir,(false,i::si,false::ci),O,op)|=
 Amapsto(b,0%Z)Tint32 true v **(Core **CurTid t) ->
 TaskSim(pc,(po,pi,ip))
 (SKIP,(kenil,kseq(sprim excrit)(kseq sret(kcall f body caller tail))))
 (ge,V293_cpu_lenv saved b,M,ir,(false,i::si,false::ci))
 (pc,A)(c,(ke,ks))O V293_shared_li G
 (fun s=>satp(fst s)(snd s)(RDYINV G t **LINV V293_shared_li t nil))t.
Proof.
 intros pc po pi ip A t ge M ir i si ci O op f body caller c ke interrupted_env ks
 tau d1 d2 saved b v Bind Range Cases Clear tail Held.
 assert(Good:GoodInvAsrt(Core **CurTid t)).
 { split;[apply V293_current_core_good|unfold CurTid,Agvarmapsto,Aptrmapsto;cbn[GoodInvAsrt];intros;repeat split;exact I]. }
 assert(GoodCell:GoodInvAsrt(Amapsto(b,0%Z)Tint32 true v **(Core **CurTid t))).
 { split;[exact I|exact Good]. }
 assert(While:forall le' cs',satp(ge,le',M,ir,(false,i::si,cs'))O(CurLINV V293_shared_li t)).
 { intros le' cs';eapply V293_pending_local with(op:=op).
   assert(H:(ge,le',M,ir,(false,i::si,cs'),O,op)|=
    Amapsto(b,0%Z)Tint32 true v **(Core **CurTid t)).
   { eapply good_inv_prop;[exact GoodCell|exact Held]. }
   clear Held;sep auto. }
 destruct(V293_tick_free_owned _ _ _ _ _ _ _ _ _ _ _ Held)as(Mret&Freed&Rest).
 assert(After:forall le' cs',satp(ge,le',Mret,ir,(false,i::si,cs'))O(CurLINV V293_shared_li t)).
 { intros le' cs';eapply V293_pending_local with(op:=op).
   assert(H:(ge,le',Mret,ir,(false,i::si,cs'),O,op)|=Core **CurTid t).
   { eapply good_inv_prop;[exact Good|exact Rest]. }
   clear Held Rest;sep auto. }
 assert(Inside:InOS(SKIP,(kenil,kcall f body caller tail))(pumerge po pi)).
 { eapply V293_bound_call_inos;exact Bind. }
 assert(End:TaskSim(pc,(po,pi,ip))(SKIP,(kenil,tail))
 (ge,caller,Mret,ir,(false,i::si,ci))(pc,A)(c,(ke,ks))O V293_shared_li G
 (fun s=>satp(fst s)(snd s)(RDYINV G t **LINV V293_shared_li t nil))t).
 { eapply V293_interrupt_cstep_TaskSim;[ | | |apply After| ].
   - do 3 eexists;split;[reflexivity| ];right;right;unfold tail;discriminate.
   - intros(vv&Eq);discriminate.
   - intros Mf Mall Join;exists Mall;split;[exact Join| ];split.
     + unfold tail;eapply stmt_step;[reflexivity|apply sskip_step].
     + intros Cf mf Low.
       assert(Next:cstep(pumerge po pi)(SKIP,(kenil,tail))(ge,caller,Mall)
         (curs(sprim exint),(kenil,kint c ke interrupted_env ks))(ge,caller,Mall)).
       { unfold tail;eapply stmt_step;[reflexivity|apply sskip_step]. }
       destruct(cstep_idmove_deter _ _ _ _ _ _ Next Low)as[EC EM];split;symmetry;assumption.
   - eapply V293_interrupt_iret_TaskSim with(op:=op);[exact Cases|exact Clear| ].
     eapply good_inv_prop;[exact Good|exact Rest]. }
 assert(FreeEnd:TaskSim(pc,(po,pi,ip))(curs(sfree nil None),(kenil,kcall f body caller tail))
 (ge,V293_cpu_lenv saved b,Mret,ir,(false,i::si,ci))(pc,A)(c,(ke,ks))O V293_shared_li G
 (fun s=>satp(fst s)(snd s)(RDYINV G t **LINV V293_shared_li t nil))t).
 { eapply V293_interrupt_cstep_TaskSim;[ | | |apply After|exact End].
   - eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
   - intros[x E];discriminate E.
   - intros Mf Mall Join;exists Mall;split;[exact Join| ].
     split.
     + eapply stmt_step;[reflexivity| ];eapply sfreeend_step;reflexivity.
     + intros;eapply V293_free_end_successor;eassumption. }
 assert(FreeCell:TaskSim(pc,(po,pi,ip))(curs(sfree((b,Tint32)::nil)None),(kenil,kcall f body caller tail))
 (ge,V293_cpu_lenv saved b,M,ir,(false,i::si,ci))(pc,A)(c,(ke,ks))O V293_shared_li G
 (fun s=>satp(fst s)(snd s)(RDYINV G t **LINV V293_shared_li t nil))t).
 { eapply V293_interrupt_cstep_TaskSim;[ | | |apply After|exact FreeEnd].
   - eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
   - intros[x E];discriminate E.
   - intros Mf Mall Join;destruct(free_mono _ _ _ _ _ _ Join Freed)as(Mall'&Free').
     exists Mall';split;[eapply join_free;eassumption| ].
     split.
     + eapply stmt_step;[reflexivity| ];eapply sfree_step;[reflexivity|reflexivity|exact Free'].
     + intros;eapply V293_free_cell_successor;eassumption. }
 assert(Return:TaskSim(pc,(po,pi,ip))(curs sret,(kenil,kcall f body caller tail))
 (ge,V293_cpu_lenv saved b,M,ir,(false,i::si,ci))(pc,A)(c,(ke,ks))O V293_shared_li G
 (fun s=>satp(fst s)(snd s)(RDYINV G t **LINV V293_shared_li t nil))t).
 { eapply V293_interrupt_cstep_TaskSim;[ | | |apply While|exact FreeCell].
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
 (ge,V293_cpu_lenv saved b,M,ir,(false,i::si,ci))(pc,A)(c,(ke,ks))O V293_shared_li G
 (fun s=>satp(fst s)(snd s)(RDYINV G t **LINV V293_shared_li t nil))t).
 { eapply V293_interrupt_cstep_TaskSim;[ | | |apply While|exact Return].
   - eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
   - intros[x E];discriminate E.
   - intros Mf Mall Join;exists Mall;split;[exact Join| ].
     assert(Next:cstep(pumerge po pi)(SKIP,(kenil,kseq sret(kcall f body caller tail)))
      (ge,V293_cpu_lenv saved b,Mall)(curs sret,(kenil,kcall f body caller tail))(ge,V293_cpu_lenv saved b,Mall)).
     { eapply stmt_step;[reflexivity|apply sskip_step]. }
     split;[exact Next| ];intros Cf mf H.
     destruct(cstep_idmove_deter _ _ _ _ _ _ Next H)as[EC EM];split;symmetry;assumption. }
 assert(Exit:TaskSim(pc,(po,pi,ip))(curs(sprim excrit),(kenil,kseq sret(kcall f body caller tail)))
 (ge,V293_cpu_lenv saved b,M,ir,(false,i::si,false::ci))(pc,A)(c,(ke,ks))O V293_shared_li G
 (fun s=>satp(fst s)(snd s)(RDYINV G t **LINV V293_shared_li t nil))t).
 { eapply V293_interrupt_internal_TaskSim;[exact Clear|cbn[gettopis];lia| | | | | | |apply While|exact SkipReturn].
   - eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
   - intros[x E];discriminate E.
   - intros(x&ks0&E);discriminate E.
   - intros(e1&e2&e3&ks0&E);discriminate E.
   - intros(e&ks0&E);discriminate E.
   - intros Mf Mall Join;exists Mall;split;[exact Join| ];split.
     + apply excrit_step;reflexivity.
     + intros;eapply V293_excrit_successor;eassumption. }
 eapply V293_interrupt_cstep_TaskSim;[ | | |apply While|exact Exit].
 - eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
 - intros[x E];discriminate E.
 - intros Mf Mall Join;exists Mall;split;[exact Join| ].
   assert(Next:cstep(pumerge po pi)(SKIP,(kenil,kseq(sprim excrit)(kseq sret(kcall f body caller tail))))
    (ge,V293_cpu_lenv saved b,Mall)(curs(sprim excrit),(kenil,kseq sret(kcall f body caller tail)))(ge,V293_cpu_lenv saved b,Mall)).
   { eapply stmt_step;[reflexivity|apply sskip_step]. }
   split;[exact Next| ];intros Cf mf H.
   destruct(cstep_idmove_deter _ _ _ _ _ _ Next H)as[EC EM];split;symmetry;assumption.
Qed.
End InterruptReturn.

(* An actual eight-step suffix on every compatible heap frame.  Unlike a
   free-capability assertion this executes free, call return, and exint. *)
Theorem V293_interrupt_pending_return_execution : forall P f body caller c ke interrupted_env ks
 ge M ir i si ci saved b v O op R,
 (ge,V293_cpu_lenv saved b,M,ir,(false,i::si,false::ci),O,op)|=
 Amapsto(b,0%Z)Tint32 true v **R ->
 exists Mr,free Tint32 b M=Some Mr /\
 (ge,V293_cpu_lenv saved b,Mr,ir,(false,i::si,false::ci),O,op)|=R /\
 forall Mf Mall,join M Mf Mall ->exists Mall',join Mr Mf Mall' /\
 V293_local_steps P
 (SKIP,(kenil,kseq(sprim excrit)(kseq sret(kcall f body caller
  (kseq(sprim exint)(kint c ke interrupted_env ks))))))
 (ge,V293_cpu_lenv saved b,Mall,ir,(false,i::si,false::ci))
 (c,(ke,ks))(ge,interrupted_env,Mall',ir,(true,si,ci)).
Proof.
 intros P f body caller c ke interrupted_env ks ge M ir i si ci saved b v O op R Held.
 destruct(V293_tick_free_owned _ _ _ _ _ _ _ _ _ _ _ Held)as(Mr&Free&Rest).
 exists Mr;split;[exact Free| ];split;[exact Rest| ].
 intros Mf Mall Join;destruct(free_mono _ _ _ _ _ _ Join Free)as(Mall'&FreeAll).
 exists Mall';split;[eapply join_free;eassumption| ].
 eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sskip_step]| ].
 eapply V293_local_cons;[apply excrit_step;reflexivity| ].
 eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sskip_step]| ].
 eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity| ];
  eapply sret_step;[reflexivity|reflexivity|apply V293_cpu_layout]| ].
 eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity| ];
  eapply sfree_step;[reflexivity|reflexivity|exact FreeAll]| ].
 eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity| ];
  eapply sfreeend_step;reflexivity| ].
 eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sskip_step]| ].
 eapply V293_local_cons;[eapply exint_step;reflexivity|apply V293_local_refl].
Qed.
