Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Lia.
Require Import CertiOS.certiucos.v293.proofs.V293SwitchProgSim.
Require Import CertiOS.audit.probes.V293CurrentHandoffPrefixProbe.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyStorageInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293ReadySwitchStep.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCurrentInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293CurrentHandoffPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBoundarySwitch.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyHandoff.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.audit.probes.V293OSIntExitReadyHandoffProbe.
Require Import CertiOS.audit.probes.V293ReadyCriticalGlobalProbe.
Require Import CertiOS.audit.probes.V293ReadyFullCallProbe.
Require Import CertiOS.audit.probes.V293ReadyGlobalTraceProbe.
Require Import CertiOS.audit.probes.V293ReadySwitchStepProbe.
Require Import CertiOS.audit.probes.V293ReadySchedCallProbe.
Require Import CertiOS.audit.probes.V293TaskRecordInvariantProbe.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.certiucos.v293.proofs.V293HandoffProgSim.
Require Import CertiOS.audit.probes.V293SwitchProgSimProbe.
Require Import CertiOS.certiucos.v293.proofs.V293ClientSkipTaskSim.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.simulation.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.framework.proof.step_prop.
Require Import Coq.Lists.List.
Import ListNotations.

Section FiniteClient.
Variables pc po pi:progunit.
Variable ip:intunit.
Variables T:tasks.
Variables S:osstate.
Variable t:tid.
Variables C C':code.
Variables gc lc ge le:env.
Variable ces:cltenvs.
Variables mc M:mem.
Variable ir:isr.
Variable si:is.
Variable cs:cs.
Let P:lprog:=(pc,(po,pi,ip)).
Let cst:clientst:=(gc,ces,mc).
Hypothesis Code:get T t=Some C.
Hypothesis Projection:projS S t=Some((ge,le,M),ir,(false,si,cs)).
Hypothesis ClientLocal:get ces t=Some lc.
Hypothesis Outside:~InOS C(pumerge po pi).
Hypothesis Step:forall p m,cstep p C m C' m.
Hypothesis NoOutput:forall p m Cf mf ev,~cstepev p C m Cf mf ev.

Lemma HPclient_local :
 ltstep P t C cst((ge,le,M),ir,(false,si,cs))C' cst((ge,le,M),ir,(false,si,cs)).
Proof.
 assert(Same:set ces t lc=ces)by(apply CltEnvMod.get_set_same;exact ClientLocal).
 replace cst with(gc,set ces t lc,mc)at 2 by(unfold cst;rewrite Same;reflexivity).
 eapply clt_step with(m:=(gc,lc,mc))(m':=(gc,lc,mc));try reflexivity;try eassumption.
 apply Step.
Qed.

Lemma HPclient_all : forall Tf cf Sf tf,
 lpstep P T cst S t Tf cf Sf tf ->Tf=set T t C' /\ cf=cst /\ Sf=S /\ tf=t.
Proof.
 intros Tf cf Sf tf H;unfold P in H;inversion H;subst.
 - assert(C0=C)by congruence;subst C0.
   assert(tst=((ge,le,M),ir,(false,si,cs)))by congruence;subst tst.
   match goal with H:lintstep _ _ _ _ _ |- _ =>inversion H;subst;discriminate end.
 - assert(C0=C)by congruence;subst C0.
   assert(tst=((ge,le,M),ir,(false,si,cs)))by congruence;subst tst.
   match goal with H:ltstep _ _ _ _ _ _ _ _ |- _ =>unfold P in H;inversion H;subst;
    match goal with E:(pc,(po,pi,ip))=(_,(_,_,_))|-_ =>inversion E;subst;clear E end end.
   + match goal with H:cstep ?p C ?m _ _|-_ =>
      destruct(cstep_idmove_deter _ _ _ _ _ _(Step p m)H)as[EqC EqM];inversion EqM;subst end.
     repeat split;try reflexivity.
     * unfold cst in *;inversion H11;subst ge0 cenvs M'.
       change((gc,CltEnvMod.set ces tf le',mc)=(gc,ces,mc)).
       rewrite(CltEnvMod.get_set_same H10);reflexivity.
     * eapply V293_projection_ext;[eassumption|exact Projection| ].
       destruct Sf as [[[[g es] mm] ii] aa];destruct S as [[[[g' es'] mm'] ii'] aa'].
       unfold Steq,Dteq,Piteq in *;cbn in *.
       split;intros x Ne;[exact(eq_sym(proj1 H4 x Ne))|exact(eq_sym(proj2 H4 x Ne))].
   + contradiction.
 - change(get T t=Some((curs(sprim(switch x)),(kenil,ks)):code))in H4.
   rewrite Code in H4;inversion H4;subst C.
   exfalso;eapply V293_cstep_not_primitive;[apply(Step (pumerge po pi)(ge,le,M))|reflexivity].
 - change(get T tf=Some((curs(sprim(stkinit e1 e2 e3)),(kenil,ks)):code))in H1.
   rewrite Code in H1;inversion H1;subst C.
   exfalso;eapply V293_cstep_not_primitive;[apply(Step (pumerge po pi)(ge,le,M))|reflexivity].
 - change(get T tf=Some((curs(sprim(stkinit e1 e2 e3)),(kenil,ks)):code))in H1.
   rewrite Code in H1;inversion H1;subst C.
   exfalso;eapply V293_cstep_not_primitive;[apply(Step (pumerge po pi)(ge,le,M))|reflexivity].
 - change(get T tf=Some((curs(sprim(stkfree e)),(kenil,ks)):code))in H1.
   rewrite Code in H1;inversion H1;subst C.
   exfalso;eapply V293_cstep_not_primitive;[apply(Step (pumerge po pi)(ge,le,M))|reflexivity].
Qed.
Lemma HPclient_no_output : forall Tf cf Sf tf ev,~lpstepev P T cst S t Tf cf Sf tf ev.
Proof.
 intros Tf cf Sf tf ev H;inversion H;subst.
 assert(C0=C)by congruence;subst C0.
 match goal with H:ltstepev _ _ _ _ _ _ _ _ _|-_ =>inversion H;subst end.
 eapply NoOutput;eassumption.
Qed.
Lemma HPclient_no_abort : ~lpstepabt P T cst S t.
Proof.
 intro H;pose proof HPclient_local as LocalStep;inversion H;subst.
 - assert(C0=C)by congruence;subst C0.
   assert(tst=((ge,le,M),ir,(false,si,cs)))by congruence;subst tst.
   match goal with H:ltstepabt _ _ _ _ _|-_ =>inversion H;subst end.
   match goal with H:~(_ \/ _)|-_ =>apply H;left end.
   exists C';exists((ge,le,M),ir,(false,si,cs));exists cst;exact LocalStep.
 - change(get T t=Some((curs(sprim(stkinit e1 e2 e3)),(kenil,ks)):code))in H0.
   rewrite Code in H0;inversion H0;subst C.
   eapply V293_cstep_not_primitive;[apply(Step (pumerge po pi)(ge,le,M))|reflexivity].
 - change(get T t=Some((curs(sprim(stkfree e)),(kenil,ks)):code))in H0.
   rewrite Code in H0;inversion H0;subst C.
   eapply V293_cstep_not_primitive;[apply(Step (pumerge po pi)(ge,le,M))|reflexivity].
 - change(get T t=Some((curs(sprim(switch x)),(kenil,ks)):code))in H0.
   rewrite Code in H0;inversion H0;subst C.
   eapply V293_cstep_not_primitive;[apply(Step (pumerge po pi)(ge,le,M))|reflexivity].
Qed.
Lemma HPclient_pull : forall ph Th O,
 get O curtid=Some(oscurt t) ->
 ProgSim P(set T t C')S ph Th O cst t ->ProgSim P T S ph Th O cst t.
Proof.
 intros ph Th O Cur Post;apply simulation.prog_sim;[exact Cur| | | ].
 - intros Tf Sf cf tf H;destruct(HPclient_all _ _ _ _ H)as[A[B[D E]]].
   subst;exists Th;exists O;split;[constructor|exact Post].
 - intros Tf Sf cf ev tf H;exfalso;eapply HPclient_no_output;eassumption.
 - intro H;exfalso;apply HPclient_no_abort;exact H.
Qed.
End FiniteClient.

Lemma HPfinite_simulation : forall pc po pi ip T S t gc ces mc lc ge le M ir si cs ph Th O,
 get T t=Some V293_skip_client_code ->
 projS S t=Some((ge,le,M),ir,(false,si,cs)) ->
 get ces t=Some lc ->get O curtid=Some(oscurt t) ->
 ProgSim(pc,(po,pi,ip))T S ph Th O(gc,ces,mc)t.
Proof.
 intros pc po pi ip T S t gc ces mc lc ge le M ir si cs ph Th O Code Projection Local Cur.
 eapply HPclient_pull with(C:=V293_skip_client_code)(C':=V293_skip_client_next)
 (ge:=ge)(le:=le)(M:=M)(ir:=ir)(si:=si)(cs:=cs)(lc:=lc);try eassumption.
 - apply V293_skip_client_not_os;left;reflexivity.
 - intros;eapply stmt_step;[reflexivity|apply sseq_step].
 - intros;eapply V293_skip_client_no_event;left;reflexivity.
 - eapply HPclient_pull with(C:=V293_skip_client_next)(C':=(SKIP,(kenil,kstop)))
   (ge:=ge)(le:=le)(M:=M)(ir:=ir)(si:=si)(cs:=cs)(lc:=lc);try eassumption.
   + apply map_get_set.
   + apply V293_skip_client_not_os;right;left;reflexivity.
   + intros;eapply stmt_step;[reflexivity|apply sskip_step].
   + intros;eapply V293_skip_client_no_event;right;left;reflexivity.
   + eapply SPterminal;try eassumption;apply map_get_set.
Qed.

(* The enclosing binding is real; the inner pending is unchanged across the
   copy and switch. Unlike stage252, the resumed task has two pending skips. *)
Definition HPpending:=CGpending ## CGouter.
Definition HPcode:code:=(curs(V293_interrupt_handoff 103%Z 108%Z 106%Z),(kenil,HPpending)).
Definition HPbase:tasks:=set GSbase OwnershipReady V293_skip_client_code.
Definition HPtasks:tasks:=set HPbase OwnershipWaiting HPcode.
Definition HPfinal:tasks:=set HPtasks OwnershipWaiting(SKIP,(kenil,HPpending)).
Definition HPcst:clientst:=(emp,sig OwnershipReady emp,emp).
Definition HPTh:tasks:=set SPTh OwnershipReady V293_skip_client_code.
Definition HPThf:tasks:=set HPTh OwnershipWaiting
 (curs(hapi_code(spec_done None)),(kenil,FCpending)).

Lemma HPcontext : InOS(SKIP,(kenil,HPpending))CGprogram.
Proof.
 exists SKIP;exists kenil;exists HPpending;split;[reflexivity| ].
 right;left;exists 113%Z;exists CGle;exists kstop;exists Tvoid;exists dnil.
 exists(dcons 120%Z Tint32 dnil);exists CGbody;exists CGbody;split;reflexivity.
Qed.
Lemma HPschedule : hpstep SPph HPTh HPcst(RIabstract OwnershipWaiting)HPThf HPcst SPOf.
Proof.
 eapply hswi_step with(t:=OwnershipWaiting)(t':=OwnershipReady)
 (C:=(curs(hapi_code(sched;;spec_done None)),(kenil,FCpending)))
 (ke:=kenil)(ks:=FCpending)(s:=spec_done None);try reflexivity.
 - exists OwnershipTasks;split;[apply RIfixed_tasks|exact RIhighest].
Qed.
Lemma HPpost : forall Mf enabled ci ip,
 ProgSim(RCprogram,(CGpo,CGempty,ip))HPfinal(SPS Mf enabled ci)
 SPph HPThf SPOf HPcst OwnershipReady.
Proof.
 intros Mf enabled ci ip;eapply HPfinite_simulation with
 (gc:=emp)(ces:=sig OwnershipReady emp)(mc:=emp)(lc:=emp)
 (ge:=CGge)(le:=emp)(M:=Mf)(ir:=fun _=>false)(si:=nil)(cs:=nil).
 - unfold HPfinal,HPtasks,HPbase;rewrite !map_get_set' by discriminate;apply map_get_set.
 - unfold SPS,projS,projD,CGswitch_envs,GSenvs,CGswitch_aux,RSaux;cbn.
   rewrite !map_get_set' by discriminate;rewrite !map_get_sig;reflexivity.
 - apply map_get_sig.
 - unfold SPOf;apply map_get_set.
Qed.

Lemma HPbridge : forall M Mc Mf enabled ci ip,
 load Tint8 M(91%positive,0%Z)=Some(V293_byteval 4) ->
 store Tint8 M(94%positive,0%Z)(V293_byteval 4)=Some Mc ->
 load(Tptr V293_tcb_type)Mc(93%positive,0%Z)=Some(Vptr OwnershipReady) ->
 store(Tptr V293_tcb_type)Mc(1%positive,0%Z)(Vptr OwnershipReady)=Some Mf ->
 ProgSim(RCprogram,(CGpo,CGempty,ip))HPtasks(SPS M enabled ci)
 SPph HPTh(RIabstract OwnershipWaiting)HPcst OwnershipWaiting.
Proof.
 intros M Mc Mf enabled ci ip High Copy Target Store.
 eapply V293_handoff_progsim with(le:=CGle)(Mc:=Mc)(Mf:=Mf)(next:=OwnershipReady)
 (high:=103%Z)(current:=108%Z)(target:=106%Z)(ks:=HPpending)
 (b:=94%positive)(v:=V293_byteval 4)(bt:=93%positive)(bc:=1%positive)
 (tp:=V293_tcb_type)(si:=nil)(cs:=enabled::ci)(Thf:=HPThf)(Of:=SPOf);
 try reflexivity;try eassumption.
 - exact HPcontext.
 - eapply hp_stepS;[apply HPschedule|apply hp_stepO].
 - apply HPpost.
Qed.

(* Owned, typed heaps make the complete simulation premise nonempty. The
   same pending continuation is used before copying and at the switch. *)
Theorem HPactual_handoff_simulation : forall enabled ci ip,
 exists M Mc Mf,
 cstepstar CGprogram HPcode(CGge,CGle,M)
 (curs(sprim(switch 106%Z)),(kenil,HPpending))(CGge,CGle,Mc) /\
 (forall R,~CGstate OwnershipWaiting Mc(enabled::ci)|=SWINVt GHinv OwnershipWaiting ** R) /\
 store(Tptr V293_tcb_type)Mc(1%positive,0%Z)(Vptr OwnershipReady)=Some Mf /\
 lpstep(RCprogram,(CGpo,CGempty,ip))
 (set HPtasks OwnershipWaiting(curs(sprim(switch 106%Z)),(kenil,HPpending)))
 HPcst(SPS Mc enabled ci)OwnershipWaiting HPfinal HPcst(SPS Mf enabled ci)OwnershipReady /\
 hpstep SPph HPTh HPcst(RIabstract OwnershipWaiting)HPThf HPcst SPOf /\
 ProgSim(RCprogram,(CGpo,CGempty,ip))HPtasks(SPS M enabled ci)
 SPph HPTh(RIabstract OwnershipWaiting)HPcst OwnershipWaiting.
Proof.
 intros enabled ci ip.
 destruct(CGlocal_ready true enabled ci)as(M&Trace&Held&Target&Counter&Cache).
 assert(Old:CGstate OwnershipWaiting M(enabled::ci)|=
 SWINVt(V293ReadyTaskInvariant.V293_ready_inv 80%positive 81%positive 82%positive)OwnershipWaiting ** JHpost 6)by exact Held.
 assert(High:load Tint8 M(91%positive,0%Z)=Some(V293_byteval 4)).
 { eapply V293_record_star_load_l with(s:=CGstate OwnershipWaiting M(enabled::ci))
 (P:=V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval 4))(Q:=Atrue).
 - intros st K;apply V293_owned_record_cell_load;exact K.
 - unfold JHpost in Old;clear Held;sep auto. }
 assert(Raw:CGstate OwnershipWaiting M(enabled::ci)|=
 SWINVt(V293ReadyTaskInvariant.V293_ready_inv 80%positive 81%positive 82%positive)OwnershipWaiting **
 (V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval 6) **
 (V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval 4) **
 (V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady) **
 (V293_owned_record_cell((95%positive,0%Z),Tint32,Vint32 Int.zero) ** CGframe 0 0))))).
 { unfold JHpost in Old;clear Held;sep auto. }
 destruct(V293_handoff_copy_execution 80%positive 81%positive 82%positive CGprogram HPpending
 CGge CGle M(fun _=>false)(false,nil,enabled::ci)(RIabstract OwnershipWaiting)(spec_done None)
 OwnershipWaiting(V293_owned_record_cell((95%positive,0%Z),Tint32,Vint32 Int.zero) ** CGframe 0 0)
 103%Z 108%Z 106%Z 91%positive 94%positive 93%positive 4 6 OwnershipReady
 ltac:(lia)eq_refl eq_refl eq_refl eq_refl Raw)as(Mc&Copy&Store&Copied&OutsideCopy).
 assert(OldCopy:CGstate OwnershipWaiting Mc(enabled::ci)|=
 SWINVt(V293ReadyTaskInvariant.V293_ready_inv 80%positive 81%positive 82%positive)OwnershipWaiting ** JHpost 4).
 { unfold JHpost;clear Held Raw Old;sep auto. }
 assert(CacheCopy:load Tint8 Mc(94%positive,0%Z)=Some(V293_byteval 4)).
 { apply(GHbyte CGge CGle Mc (fun _=>false)(false,nil,enabled::ci)(RIabstract OwnershipWaiting)(spec_done None)4);
 [lia|clear Held Raw Old Copied;sep auto]. }
 assert(InvCopy:CGstate OwnershipWaiting Mc(enabled::ci)|=SWINVt JHinv OwnershipWaiting ** JHprivate).
 { apply JHclose with(n:=4);exact OldCopy. }
 assert(TargetCopy:load(Tptr V293_tcb_type)Mc(93%positive,0%Z)=Some(Vptr OwnershipReady)).
 { rewrite(V293_load_block_frame _ M Mc 93%positive 0%Z ltac:(intros;apply OutsideCopy;left;discriminate));exact Target. }
 destruct(V293_ready_storage_switch_step 80%positive 81%positive 82%positive 106%Z V293_tcb_type JHcells
 RCprogram CGpo CGempty ip
 (set HPtasks OwnershipWaiting(curs(sprim(switch 106%Z)),(kenil,HPpending)))HPcst HPpending OwnershipWaiting OwnershipReady
 93%positive 1%positive CGge CGle CGswitch_envs Mc(fun _=>false)(false,nil,enabled::ci)
 (CGswitch_aux enabled ci)(RIabstract OwnershipWaiting)(spec_done None)JHprivate
 (map_get_set _ _ _)(map_get_set _ _ _)(map_get_set _ _ _)eq_refl TargetCopy eq_refl InvCopy)
 as(Mf&Step&PhysicalStore&After&Current&Frame).
 exists M;exists Mc;exists Mf;split;[exact Copy| ];split;[apply GHrejected;exact CacheCopy| ];split;[exact PhysicalStore| ];split.
 - unfold HPfinal;rewrite tasks_set_a_set_a in Step;exact Step.
 - split;[apply HPschedule| ];eapply HPbridge;eassumption.
Qed.

Theorem HPtarget_not_ended :
 get HPtasks OwnershipReady=Some V293_skip_client_code /\ ~IsEnd V293_skip_client_code.
Proof.
 split.
 - unfold HPtasks,HPbase;rewrite map_get_set' by discriminate;apply map_get_set.
 - intros[v H];discriminate H.
Qed.

(* Keep every other post component fixed and omit only the high current update. *)
Theorem HPzero_high_match_rejected : forall Mf enabled ci ip,
 ~ProgSim(RCprogram,(CGpo,CGempty,ip))HPfinal(SPS Mf enabled ci)
 SPph HPThf(RIabstract OwnershipWaiting)HPcst OwnershipReady.
Proof.
 intros Mf enabled ci ip H;inversion H.
 assert(get(RIabstract OwnershipWaiting)curtid=Some(oscurt OwnershipWaiting))by reflexivity.
 assert(OwnershipReady=OwnershipWaiting)by congruence;discriminate.
Qed.

(* A separate entry boundary varies only IE, with both stacks empty. This
   is not a relaxation of the closed-interrupt interval in the bridge. *)
Definition HPinterrupts:intunit:=fun _=>Some(sskip None).
Definition HPboundary_aux enabled:ltaskstset:=
 set(CGswitch_aux false nil)OwnershipWaiting(enabled,nil,nil).
Theorem HPdisabled_no_interrupt : forall M Cf stf,
 ~lintstep HPinterrupts HPcode((CGge,CGle,M),(fun _=>false),(false,nil,nil))Cf stf.
Proof. intros M Cf stf H;inversion H;discriminate. Qed.
Theorem HPenabled_interrupt : forall M,
 lpstep(RCprogram,(CGpo,CGempty,HPinterrupts))HPtasks HPcst
 (CGge,CGswitch_envs,M,(fun _=>false),HPboundary_aux true)OwnershipWaiting
 (set HPtasks OwnershipWaiting(curs(sskip None),
 (kenil,kint(curs(V293_interrupt_handoff 103%Z 108%Z 106%Z))kenil CGle HPpending)))HPcst
 (CGge,set CGswitch_envs OwnershipWaiting emp,M,isrupd(fun _=>false)0 true,
 set(HPboundary_aux true)OwnershipWaiting(false,cons 0%nat nil,nil))OwnershipWaiting.
Proof.
 intro M;eapply pint_step.
 - reflexivity.
 - apply map_get_set.
 - reflexivity.
 - unfold projS,projD,HPboundary_aux;rewrite !map_get_set;reflexivity.
 - unfold projS,projD;rewrite !map_get_set;reflexivity.
 - split;[unfold Dteq|unfold Piteq];intros otherid Apart;cbn;
   rewrite map_get_set' by congruence;reflexivity.
 - unfold HPcode;eapply li_step with(i:=0).
   + exact 0.
   + reflexivity.
   + intros i Bound;reflexivity.
   + unfold INUM;lia.
   + reflexivity.
Qed.
