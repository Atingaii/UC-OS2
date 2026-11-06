(* Pull the original program simulation across a silent OS source step.
   This does not require an invariant at the transient cache-copy state. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.simulation.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.framework.proof.step_prop.
Require Import CertiOS.framework.auxlibs.MapLib.
Require Import CertiOS.certiucos.v293.proofs.V293SwitchProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBoundarySwitch.

Lemma V293_projection_ext : forall S S' t tst,
 projS S t=Some tst -> projS S' t=Some tst -> Steq S S' t -> S=S'.
Proof.
 intros [[[[ge les] M] ir] aus] [[[[ge' les'] M'] ir'] aus'] t tst A B [D E].
 unfold projS,projD in A,B;cbn in A,B.
 destruct(get les t)as [le | ]eqn:L;try discriminate.
 destruct(get aus t)as [au | ]eqn:U;try discriminate.
 destruct(get les' t)as [le' | ]eqn:L';try discriminate.
 destruct(get aus' t)as [au' | ]eqn:U';try discriminate.
 inversion A;subst tst;inversion B;subst ge' le' M' ir' au'.
 change(CltEnvMod.get les t=Some le)in L.
 change(CltEnvMod.get les' t=Some le)in L'.
 change(TaskLStMod.get aus t=Some au)in U.
 change(TaskLStMod.get aus' t=Some au)in U'.
 assert(les=les').
 { apply CltEnvMod.extensionality;intro x;destruct(tidspec.beq x t)eqn:N.
 - apply tidspec.beq_true_eq in N;subst;rewrite L,L';reflexivity.
 - apply tidspec.beq_false_neq in N;exact(D x N). }
 assert(aus=aus').
 { apply TaskLStMod.extensionality;intro x;destruct(tidspec.beq x t)eqn:N.
 - apply tidspec.beq_true_eq in N;subst;rewrite U,U';reflexivity.
 - apply tidspec.beq_false_neq in N;exact(E x N). }
 subst;reflexivity.
Qed.

Lemma V293_cstep_not_primitive : forall p C m C' m',
 cstep p C m C' m' -> forall prim ks,C<>(curs(sprim prim),(kenil,ks)).
Proof.
 intros p C m C' m' H prim ks Eq;subst C;inversion H;subst;
 match goal with
 | H:estep _ _ _ _ _ _ |- _ =>inversion H;subst;try discriminate
 | H:sstep _ _ _ _ _ _ _ |- _ =>inversion H;subst;try discriminate
 end.
Qed.

Section SilentOS.
Variables pc po pi:progunit.
Variable ip:intunit.
Variables T:tasks.
Variables cst:clientst.
Variable t:tid.
Variables C C':code.
Variables ge le:env.
Variable les:cltenvs.
Variables M M':mem.
Variable ir:isr.
Variable aus:ltaskstset.
Variable si:is.
Variable cs:cs.
Let P:lprog:=(pc,(po,pi,ip)).
Let S:osstate:=(ge,les,M,ir,aus).
Let S':osstate:=(ge,les,M',ir,aus).
Hypothesis Local:get les t=Some le.
Hypothesis Aux:get aus t=Some((false,si,cs):localst).
Hypothesis Code:get T t=Some C.
Hypothesis Inside:InOS C(pumerge po pi).
Hypothesis Step:cstep(pumerge po pi)C(ge,le,M)C'(ge,le,M').
Hypothesis Unique:forall Cf mf,cstep(pumerge po pi)C(ge,le,M)Cf mf ->
 Cf=C' /\ mf=(ge,le,M').

Lemma V293_os_projection : projS S t=Some((ge,le,M),ir,(false,si,cs)).
Proof. unfold S,projS,projD;cbn;rewrite Local;cbn;rewrite Aux;reflexivity. Qed.
Lemma V293_os_next_projection : projS S' t=Some((ge,le,M'),ir,(false,si,cs)).
Proof. unfold S',projS,projD;cbn;rewrite Local;cbn;rewrite Aux;reflexivity. Qed.
Lemma V293_os_local_step :
 ltstep P t C cst((ge,le,M),ir,(false,si,cs)) C' cst((ge,le,M'),ir,(false,si,cs)).
Proof. eapply inapi_step;[reflexivity|apply ostc_step;exact Step|exact Inside]. Qed.

Theorem V293_os_silent_progress : lpstep P T cst S t(set T t C')cst S' t.
Proof.
 eapply pt_step;try reflexivity;try eassumption.
 - exact V293_os_projection.
 - exact V293_os_next_projection.
 - split;intros x Ne;reflexivity.
 - exact V293_os_local_step.
Qed.

Theorem V293_os_silent_all_successors : forall Tf cf Sf tf,
 lpstep P T cst S t Tf cf Sf tf ->
 Tf=set T t C' /\ cf=cst /\ Sf=S' /\ tf=t.
Proof.
 intros Tf cf Sf tf H;unfold P in H;pose proof V293_os_projection as Projection;
 pose proof V293_os_next_projection as NextProjection;inversion H;subst.
 - assert(C0=C)by congruence;subst C0.
   assert(tst=((ge,le,M),ir,(false,si,cs)))by congruence;subst tst.
   match goal with H:lintstep _ _ _ _ _ |- _ =>inversion H;subst;discriminate end.
 - assert(C0=C)by congruence;subst C0.
   assert(tst=((ge,le,M),ir,(false,si,cs)))by congruence;subst tst.
   match goal with H:ltstep _ _ _ _ _ _ _ _ |- _ =>unfold P in H;inversion H;subst;
     match goal with E:(pc,(po,pi,ip))=(_,(_,_,_)) |- _ =>inversion E;subst;clear E end end.
   + contradiction.
   + match goal with H:loststep _ _ _ _ _ |- _ =>inversion H;subst end;
     try solve[exfalso;eapply V293_cstep_not_primitive;[exact Step|reflexivity]].
     * match goal with H:cstep _ C _ _ _ |- _ =>
       destruct(Unique _ _ H)as[EqC EqM];inversion EqM;subst end.
       repeat split;try reflexivity.
       eapply V293_projection_ext;[eassumption|exact NextProjection| ].
       destruct Sf as [[[[g evs] mm] ii] aa].
       unfold S,S',Steq,Dteq,Piteq in *;cbn in *.
       split;intros x Ne;[exact(eq_sym(proj1 H4 x Ne))|exact(eq_sym(proj2 H4 x Ne))].
 - change(get T t=Some((curs(sprim(switch x)),(kenil,ks)):code))in H4.
   rewrite Code in H4;inversion H4;subst C.
   exfalso;eapply V293_cstep_not_primitive;[exact Step|reflexivity].
 - change(get T tf=Some((curs(sprim(stkinit e1 e2 e3)),(kenil,ks)):code))in H1.
   rewrite Code in H1;inversion H1;subst C.
   exfalso;eapply V293_cstep_not_primitive;[exact Step|reflexivity].
 - change(get T tf=Some((curs(sprim(stkinit e1 e2 e3)),(kenil,ks)):code))in H1.
   rewrite Code in H1;inversion H1;subst C.
   exfalso;eapply V293_cstep_not_primitive;[exact Step|reflexivity].
 - change(get T tf=Some((curs(sprim(stkfree e)),(kenil,ks)):code))in H1.
   rewrite Code in H1;inversion H1;subst C.
   exfalso;eapply V293_cstep_not_primitive;[exact Step|reflexivity].
Qed.

Theorem V293_os_silent_no_output : forall Tf cf Sf tf ev,
 ~lpstepev P T cst S t Tf cf Sf tf ev.
Proof.
 intros Tf cf Sf tf ev H;inversion H;subst.
 assert(C0=C)by congruence;subst C0.
 match goal with H:ltstepev _ _ _ _ _ _ _ _ _ |- _ =>unfold P in H;inversion H;subst;
 match goal with E:(pc,(po,pi,ip))=(_,(_,_,_)) |- _ =>inversion E;subst;clear E end;
 contradiction end.
Qed.
Theorem V293_os_silent_no_abort : ~lpstepabt P T cst S t.
Proof.
 intro H;pose proof V293_os_projection as Projection;
 pose proof V293_os_local_step as LocalStep;inversion H;subst.
 - assert(C0=C)by congruence;subst C0.
   assert(tst=((ge,le,M),ir,(false,si,cs)))by congruence;subst tst.
   match goal with H:ltstepabt _ _ _ _ _ |- _ =>inversion H;subst end.
   match goal with H:~(_ \/ _) |- _ =>apply H;left end.
   exists C';exists((ge,le,M'),ir,(false,si,cs));exists cst.
   exact LocalStep.
 - change(get T t=Some((curs(sprim(stkinit e1 e2 e3)),(kenil,ks)):code))in H0.
   rewrite Code in H0;inversion H0;subst C.
   eapply V293_cstep_not_primitive;[exact Step|reflexivity].
 - change(get T t=Some((curs(sprim(stkfree e)),(kenil,ks)):code))in H0.
   rewrite Code in H0;inversion H0;subst C.
   eapply V293_cstep_not_primitive;[exact Step|reflexivity].
 - change(get T t=Some((curs(sprim(switch x)),(kenil,ks)):code))in H0.
   rewrite Code in H0;inversion H0;subst C.
   eapply V293_cstep_not_primitive;[exact Step|reflexivity].
Qed.

Theorem V293_os_silent_progsim : forall ph Th O,
 get O curtid=Some(oscurt t) ->
 ProgSim P(set T t C')S' ph Th O cst t ->
 ProgSim P T S ph Th O cst t.
Proof.
 intros ph Th O Cur Post;apply simulation.prog_sim;[exact Cur| | | ].
 - intros Tf Sf cf tf H.
   destruct(V293_os_silent_all_successors _ _ _ _ H)as[A[B[D E]]].
   subst;exists Th;exists O;split;[constructor|exact Post].
 - intros Tf Sf cf ev tf H;exfalso;eapply V293_os_silent_no_output;eassumption.
 - intro H;exfalso;apply V293_os_silent_no_abort;exact H.
Qed.
End SilentOS.

Lemma V293_context_inos : forall p ks ks' c ke,
 InOS(SKIP,(kenil,ks))p ->callcont ks'=callcont ks ->intcont ks'=intcont ks ->
 InOS(c,(ke,ks'))p.
Proof.
 intros p ks ks' c ke (c0&ke0&k0&Eq&Ctx) Call Interrupt.
 inversion Eq;subst c0 ke0 k0.
 exists c;exists ke;exists ks';split;[reflexivity| ].
 destruct Ctx as[(f&vl&fc&tl&Bad&Bind)|Ctx];[discriminate| ].
 right;rewrite Call,Interrupt;exact Ctx.
Qed.

Lemma V293_store_cstep_unique : forall p ge le M Mc b v tp ks Cf mf,
 store tp M(b,0%Z)v=Some Mc ->
 cstep p(curs(sskip(Some(Vptr(b,Int.zero)))),(kenil,kassignl v tp ks))(ge,le,M)Cf mf ->
 Cf=(SKIP,(kenil,ks)) /\ mf=(ge,le,Mc).
Proof.
 intros p ge le M Mc b v tp ks Cf mf Store H;inversion H;subst.
 - match goal with H:estep _ _ _ _ _ _ |- _ =>inversion H;subst;try discriminate end.
 - match goal with H:sstep _ _ _ _ _ _ _ |- _ =>inversion H;subst;try discriminate end.
   inversion H0;subst.
   cbn[addrval_to_addr]in *.
   inversion H2;subst ge0 le0 M0.
   change(store t M(b,0%Z)v0=Some M')in H4.
   rewrite Store in H4;inversion H4;subst M'.
   split;reflexivity.
Qed.

Section Copy.
Variables pc po pi:progunit.
Variable ip:intunit.
Variable T:tasks.
Variable cst:clientst.
Variable t:tid.
Variables high current target:var.
Variable ks:stmtcont.
Variables ge le:env.
Variable les:cltenvs.
Variables M Mc:mem.
Variable ir:isr.
Variable aus:ltaskstset.
Variable si:is.
Variable cs:cs.
Variable b:block.
Variable v:val.
Let P:lprog:=(pc,(po,pi,ip)).
Hypothesis Local:get les t=Some le.
Hypothesis Aux:get aus t=Some((false,si,cs):localst).
Hypothesis Context:InOS(SKIP,(kenil,ks))(pumerge po pi).
Hypothesis CurrentType:evaltype(evar current)(ge,le,M)=Some Tint8.
Hypothesis HighType:evaltype(evar high)(ge,le,M)=Some Tint8.
Hypothesis HighRead:evalval(evar high)(ge,le,M)=Some v.
Hypothesis CurrentAddress:evalval(eaddrof(evar current))(ge,le,M)=Some(Vptr(b,Int.zero)).
Hypothesis CopyStore:store Tint8 M(b,0%Z)v=Some Mc.
Let K:=kseq(sprim(switch target))ks.
Let C0:code:=(curs(V293_interrupt_handoff high current target),(kenil,ks)).
Let C1:code:=(curs(sassign(evar current)(evar high)),(kenil,K)).
Let C2:code:=(cure(evar high),(kenil,kassignr(evar current)Tint8 K)).
Let C3:code:=(curs(sskip(Some v)),(kenil,kassignr(evar current)Tint8 K)).
Let C4:code:=(cure(eaddrof(evar current)),(kenil,kassignl v Tint8 K)).
Let C5:code:=(curs(sskip(Some(Vptr(b,Int.zero)))),(kenil,kassignl v Tint8 K)).
Let C6:code:=(SKIP,(kenil,K)).
Let C7:code:=(curs(sprim(switch target)),(kenil,ks)).

Theorem V293_handoff_copy_progsim : forall ph Th O,
 get O curtid=Some(oscurt t) ->
 ProgSim P(set T t C7)(ge,les,Mc,ir,aus)ph Th O cst t ->
 ProgSim P(set T t C0)(ge,les,M,ir,aus)ph Th O cst t.
Proof.
 intros ph Th O Cur Post.
 assert(S0:cstep(pumerge po pi)C0(ge,le,M)C1(ge,le,M)).
 { eapply stmt_step;[reflexivity|apply sseq_step]. }
 assert(S1:cstep(pumerge po pi)C1(ge,le,M)C2(ge,le,M)).
 { eapply stmt_step;[reflexivity| ];eapply sassign_step;try eassumption;apply eq_int;auto. }
 assert(S2:cstep(pumerge po pi)C2(ge,le,M)C3(ge,le,M)).
 { eapply expr_step;[reflexivity|apply evar_step;exact HighRead]. }
 assert(S3:cstep(pumerge po pi)C3(ge,le,M)C4(ge,le,M)).
 { eapply stmt_step;[reflexivity|apply sassignrv_step]. }
 assert(S4:cstep(pumerge po pi)C4(ge,le,M)C5(ge,le,M)).
 { eapply expr_step;[reflexivity|apply eaddr_step;exact CurrentAddress]. }
 assert(S5:cstep(pumerge po pi)C5(ge,le,M)C6(ge,le,Mc)).
 { eapply stmt_step;[reflexivity| ];eapply sassignend_step;try reflexivity;exact CopyStore. }
 assert(S6:cstep(pumerge po pi)C6(ge,le,Mc)C7(ge,le,Mc)).
 { eapply stmt_step;[reflexivity|apply sskip_step]. }
 assert(Pull:forall Ci Cj Mi,
   InOS Ci(pumerge po pi) ->
   cstep(pumerge po pi)Ci(ge,le,Mi)Cj(ge,le,Mi) ->
   ProgSim P(set T t Cj)(ge,les,Mi,ir,aus)ph Th O cst t ->
   ProgSim P(set T t Ci)(ge,les,Mi,ir,aus)ph Th O cst t).
 { intros Ci Cj Mi Inside Step Rest.
   eapply V293_os_silent_progsim with(C':=Cj)(le:=le);try eassumption.
   - apply map_get_set.
   - intros Cf mf Other;destruct(cstep_idmove_deter _ _ _ _ _ _ Step Other)as[A B];split;symmetry;assumption.
   - rewrite tasks_set_a_set_a;exact Rest. }
 assert(I0:InOS C0(pumerge po pi))by(eapply V293_context_inos;[exact Context|reflexivity|reflexivity]).
 assert(I1:InOS C1(pumerge po pi))by(eapply V293_context_inos;[exact Context|reflexivity|reflexivity]).
 assert(I2:InOS C2(pumerge po pi))by(eapply V293_context_inos;[exact Context|reflexivity|reflexivity]).
 assert(I3:InOS C3(pumerge po pi))by(eapply V293_context_inos;[exact Context|reflexivity|reflexivity]).
 assert(I4:InOS C4(pumerge po pi))by(eapply V293_context_inos;[exact Context|reflexivity|reflexivity]).
 assert(I5:InOS C5(pumerge po pi))by(eapply V293_context_inos;[exact Context|reflexivity|reflexivity]).
 assert(I6:InOS C6(pumerge po pi))by(eapply V293_context_inos;[exact Context|reflexivity|reflexivity]).
 eapply Pull;[exact I0|exact S0| ].
 eapply Pull;[exact I1|exact S1| ].
 eapply Pull;[exact I2|exact S2| ].
 eapply Pull;[exact I3|exact S3| ].
 eapply Pull;[exact I4|exact S4| ].
 eapply V293_os_silent_progsim with(C:=C5)(C':=C6)(le:=le)(M':=Mc).
 - exact Local.
 - exact Aux.
 - apply map_get_set.
 - exact I5.
 - exact S5.
 - intros Cf mf Other;eapply V293_store_cstep_unique;[exact CopyStore|exact Other].
 - exact Cur.
 - rewrite tasks_set_a_set_a;eapply Pull;[exact I6|exact S6|exact Post].
Qed.
End Copy.

(* Stable interface: the original copy and switch share the exact pending
   continuation. The high matching and the post simulation stay explicit. *)
Theorem V293_handoff_progsim : forall pc po pi ip T cst t next
 high current target ks ge le les M Mc Mf ir aus si cs b v bt bc tp ph Th O Thf Of,
 get les t=Some le ->get aus t=Some((false,si,cs):localst) ->
 get T t=Some((curs(V293_interrupt_handoff high current target),(kenil,ks)):code) ->
 InOS(SKIP,(kenil,ks))(pumerge po pi) ->
 evaltype(evar current)(ge,le,M)=Some Tint8 ->
 evaltype(evar high)(ge,le,M)=Some Tint8 ->
 evalval(evar high)(ge,le,M)=Some v ->
 evalval(eaddrof(evar current))(ge,le,M)=Some(Vptr(b,Int.zero)) ->
 store Tint8 M(b,0%Z)v=Some Mc ->
 get ge target=Some(bt,Tptr tp) ->
 load(Tptr tp)Mc(bt,0%Z)=Some(Vptr next) ->
 get ge OSTCBCur=Some(bc,Tptr tp) ->
 store(Tptr tp)Mc(bc,0%Z)(Vptr next)=Some Mf ->
 get O curtid=Some(oscurt t) ->
 hpstepstar ph Th cst O Thf cst Of ->
 ProgSim(pc,(po,pi,ip))(set T t(SKIP,(kenil,ks)))(ge,les,Mf,ir,aus)ph Thf Of cst next ->
 ProgSim(pc,(po,pi,ip))T(ge,les,M,ir,aus)ph Th O cst t.
Proof.
 intros pc po pi ip T cst t next high current target ks ge le les M Mc Mf ir aus si cs
 b v bt bc tp ph Th O Thf Of Local Aux Code Context CurrentType HighType HighRead
 CurrentAddress CopyStore Target Read Current Store Cur Match Post.
 rewrite <- (TasksMod.get_set_same Code) at 1.
 eapply V293_handoff_copy_progsim with(le:=le)(Mc:=Mc)(b:=b)(v:=v)(si:=si)(cs:=cs);
 try eassumption.
 eapply V293_switch_progsim with(le:=le)(Mf:=Mf)(next:=next)(bt:=bt)(bc:=bc)(tp:=tp)
 (si:=si)(cs:=cs)(Thf:=Thf)(Of:=Of);try eassumption.
 - apply map_get_set.
 - rewrite tasks_set_a_set_a;exact Post.
Qed.
