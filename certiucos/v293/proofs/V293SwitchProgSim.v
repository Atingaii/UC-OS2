(* A semantic bridge for the original physical switch. No invariant transfer
   rule or new transition is introduced. Continuation simulation stays explicit. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.simulation.

Lemma V293_switch_no_cstep : forall P x ks m C m',
 ~cstep P (curs(sprim(switch x)),(kenil,ks)) m C m'.
Proof.
 intros P x ks m C m' H;inversion H;subst;
 match goal with
 | H:estep _ _ _ _ _ _ |- _ =>inversion H;subst;try discriminate
 | H:sstep _ _ _ _ _ _ _ |- _ =>inversion H;subst;try discriminate
 end.
Qed.
Lemma V293_switch_no_cstepev : forall P x ks m C m' ev,
 ~cstepev P (curs(sprim(switch x)),(kenil,ks)) m C m' ev.
Proof.
 intros P x ks m C m' ev H;inversion H;subst;
 match goal with H:sstepev _ _ _ _ _ _ _ _ |- _ =>inversion H;subst;try discriminate end.
Qed.
Lemma V293_switch_no_ltstep : forall P t x ks cst o C cst' o',
 ~ltstep P t (curs(sprim(switch x)),(kenil,ks)) cst o C cst' o'.
Proof.
 intros P t x ks cst o C cst' o' H;inversion H;subst.
 - eapply V293_switch_no_cstep;eassumption.
 - match goal with H:loststep _ _ _ _ _ |- _ =>inversion H;subst end;
   try discriminate;eapply V293_switch_no_cstep;eassumption.
Qed.
Lemma V293_switch_no_ltstepev : forall P t x ks cst o C cst' o' ev,
 ~ltstepev P t (curs(sprim(switch x)),(kenil,ks)) cst o C cst' o' ev.
Proof.
 intros P t x ks cst o C cst' o' ev H;inversion H;subst.
 eapply V293_switch_no_cstepev;eassumption.
Qed.

Section Switch.
Variables pc po pi:progunit.
Variable ip:intunit.
Variable T:tasks.
Variable cst:clientst.
Variables current next:tid.
Variable x:var.
Variable ks:stmtcont.
Variables ge le:env.
Variable les:cltenvs.
Variables M Mf:mem.
Variable ir:isr.
Variable aus:ltaskstset.
Variable si:is.
Variable cs:cs.
Variables bt bc:block.
Variable tp:type.
Let P:lprog:=(pc,(po,pi,ip)).
Let S:osstate:=(ge,les,M,ir,aus).
Let Sf:osstate:=(ge,les,Mf,ir,aus).
Let Tf:=set T current(SKIP,(kenil,ks)).
Hypothesis Local:get les current=Some le.
Hypothesis Aux:get aus current=Some((false,si,cs):localst).
Hypothesis Code:get T current=Some((curs(sprim(switch x)),(kenil,ks)):code).
Hypothesis Target:get ge x=Some(bt,Tptr tp).
Hypothesis Read:load(Tptr tp)M(bt,0%Z)=Some(Vptr next).
Hypothesis Current:get ge OSTCBCur=Some(bc,Tptr tp).
Hypothesis Store:store(Tptr tp)M(bc,0%Z)(Vptr next)=Some Mf.

Lemma V293_switch_projection : projS S current=Some((ge,le,M),ir,(false,si,cs)).
Proof. unfold S,projS,projD;cbn;rewrite Local;cbn;rewrite Aux;reflexivity. Qed.

Theorem V293_switch_progress : lpstep P T cst S current Tf cst Sf next.
Proof.
 eapply pswitch_step with(tst:=((ge,le,M),ir,(false,si,cs)))
 (l:=bt)(tp:=tp)(b:=bc);try reflexivity;try eassumption.
 exact V293_switch_projection.
Qed.

Theorem V293_switch_all_successors : forall T' cst' S' t',
 lpstep P T cst S current T' cst' S' t' ->
 T'=Tf /\ cst'=cst /\ S'=Sf /\ t'=next.
Proof.
 intros T' cst' S' t' H;pose proof V293_switch_projection as Projection;inversion H;subst.
 - assert(C=(curs(sprim(switch x)),(kenil,ks))) by congruence;subst C.
   assert(tst=((ge,le,M),ir,(false,si,cs))) by congruence;subst tst.
   match goal with H:lintstep _ _ _ _ _ |- _ =>inversion H;subst;discriminate end.
 - assert(C=(curs(sprim(switch x)),(kenil,ks))) by congruence;subst C.
   exfalso;eapply V293_switch_no_ltstep;eassumption.
 - change (get T current=Some((curs(sprim(switch x0)),(kenil,ks0)):code)) in H4.
   rewrite Code in H4;inversion H4;subst x0 ks0.
   assert(tst=((ge,le,M),ir,(false,si,cs))) by congruence;subst tst.
   unfold S in H6;inversion H6;subst ge0 les0 m ir0 au.
   change (get ge x=Some(l,Tptr tp0)) in H2.
   change (load(Tptr tp0)M(l,0%Z)=Some(Vptr t')) in H3.
   rewrite Target in H2;inversion H2;subst l tp0.
   rewrite Read in H3;inversion H3;subst t'.
   rewrite Current in H8;inversion H8;subst b.
   rewrite Store in H9;inversion H9;subst m'.
   repeat split;reflexivity.
 - change (get T t'=Some((curs(sprim(stkinit e1 e2 e3)),(kenil,ks0)):code)) in H1.
   rewrite Code in H1;discriminate.
 - change (get T t'=Some((curs(sprim(stkinit e1 e2 e3)),(kenil,ks0)):code)) in H1.
   rewrite Code in H1;discriminate.
 - change (get T t'=Some((curs(sprim(stkfree e)),(kenil,ks0)):code)) in H1.
   rewrite Code in H1;discriminate.
Qed.

Theorem V293_switch_no_output : forall T' cst' S' t' ev,
 ~lpstepev P T cst S current T' cst' S' t' ev.
Proof.
 intros T' cst' S' t' ev H;inversion H;subst.
 match goal with H:get T _=Some _ |- _ =>
 first[constr_eq H Code;fail 1|rewrite Code in H;inversion H;subst;clear H] end.
 eapply V293_switch_no_ltstepev;eassumption.
Qed.
Theorem V293_switch_no_abort : ~lpstepabt P T cst S current.
Proof.
 intro H;inversion H;subst;
 match goal with H:get T _=Some _ |- _ =>
 first[constr_eq H Code;fail 1|rewrite Code in H;inversion H;subst;clear H] end;
 try discriminate.
 - match goal with H:~IsSwitch _ |- _ =>apply H;exists x;exists ks;reflexivity end.
 - match goal with H:projS _ _=Some _ |- _ =>
   rewrite V293_switch_projection in H;inversion H;subst end.
   match goal with H:~(exists _ _ _,_) |- _ =>apply H end.
   exists bt;exists tp;exists next;split;assumption.
Qed.

(* Every low-level successor, output and abort is accounted for. The high
   matching execution and post-switch simulation are not inferred from an
   invariant: they are the remaining, independently checked obligations. *)
Theorem V293_switch_progsim : forall ph Th O Thf Of,
 get O curtid=Some(oscurt current) ->
 hpstepstar ph Th cst O Thf cst Of ->
 ProgSim P Tf Sf ph Thf Of cst next ->
 ProgSim P T S ph Th O cst current.
Proof.
 intros ph Th O Thf Of Cur Match Post;apply simulation.prog_sim.
 - exact Cur.
 - intros T' S' cst' t' Step.
   destruct(V293_switch_all_successors T' cst' S' t' Step)as[A[B[C D]]].
   subst T' cst' S' t';exists Thf;exists Of;split;assumption.
 - intros T' S' cst' ev t' Step.
   exfalso;eapply V293_switch_no_output;eassumption.
 - intro Bad;exfalso;apply V293_switch_no_abort;exact Bad.
Qed.
End Switch.
