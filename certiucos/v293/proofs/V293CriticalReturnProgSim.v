(* Original critical primitives: preserve all other tasks, memory and ISR.
   The final continuation is explicit; the entry interval has IE=false. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.simulation.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.framework.proof.step_prop.
Require Import CertiOS.framework.auxlibs.MapLib.
Require Import CertiOS.certiucos.v293.proofs.V293HandoffProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293ExitDispatchProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293ExitNestingProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293SchedCallProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293SchedCallEntryProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.code.V293OSIntExit.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import Coq.Lists.List Lia.
Local Open Scope nat_scope.

Lemma V293_encrit_successor : forall p ks m ir enabled si cs C' tst',
 loststep p(curs(sprim encrit),(kenil,ks))(m,ir,(enabled,si,cs))C' tst' ->
 C'=(SKIP,(kenil,ks)) /\ tst'=(m,ir,(false,si,enabled::cs)).
Proof.
 intros p ks m ir enabled si cs C' tst' H;inversion H;subst;try discriminate.
 - exfalso;eapply V293_cstep_not_primitive;[eassumption|reflexivity].
 - repeat match goal with E:(_,_) =(_,_) |- _ =>inversion E;subst;clear E
   | E:_::_=_::_ |- _ =>inversion E;subst;clear E end;split;reflexivity.
Qed.
Lemma V293_excrit_successor : forall p ks m ir enabled saved si cs C' tst',
 loststep p(curs(sprim excrit),(kenil,ks))(m,ir,(enabled,si,saved::cs))C' tst' ->
 C'=(SKIP,(kenil,ks)) /\ tst'=(m,ir,(saved,si,cs)).
Proof.
 intros p ks m ir enabled saved si cs C' tst' H;inversion H;subst;try discriminate.
 - exfalso;eapply V293_cstep_not_primitive;[eassumption|reflexivity].
 - repeat match goal with E:(_,_) =(_,_) |- _ =>inversion E;subst;clear E
   | E:_::_=_::_ |- _ =>inversion E;subst;clear E end;split;reflexivity.
Qed.

Section Critical.
Variables pc po pi:progunit.
Variable ip:intunit.
Variable T:tasks.
Variable cst:clientst.
Variable t:tid.
Variable pr:prim.
Variable ks:stmtcont.
Variables ge le:env.
Variable les:cltenvs.
Variable M:mem.
Variable ir:isr.
Variable aus:ltaskstset.
Variable si:is.
Variable cs:cs.
Variable after:localst.
Let P:lprog:=(pc,(po,pi,ip)).
Let C:code:=(curs(sprim pr),(kenil,ks)).
Let S:osstate:=(ge,les,M,ir,aus).
Let Sf:osstate:=(ge,les,M,ir,set aus t after).
Hypothesis Kind:pr=encrit \/ pr=excrit.
Hypothesis Local:get les t=Some le.
Hypothesis Aux:get aus t=Some((false,si,cs):localst).
Hypothesis Code:get T t=Some C.
Hypothesis Inside:InOS C(pumerge po pi).
Hypothesis Step:loststep(pumerge po pi)C((ge,le,M),ir,(false,si,cs))
 (SKIP,(kenil,ks))((ge,le,M),ir,after).
Hypothesis Unique:forall Cf st,loststep(pumerge po pi)C((ge,le,M),ir,(false,si,cs))Cf st ->
 Cf=(SKIP,(kenil,ks)) /\ st=((ge,le,M),ir,after).

Lemma V293_critical_projection : projS S t=Some((ge,le,M),ir,(false,si,cs)).
Proof. unfold S,projS,projD;cbn;rewrite Local;cbn;rewrite Aux;reflexivity. Qed.
Lemma V293_critical_next_projection : projS Sf t=Some((ge,le,M),ir,after).
Proof. unfold Sf,projS,projD;cbn;rewrite Local;cbn;rewrite map_get_set;reflexivity. Qed.
Lemma V293_critical_local_step :
 ltstep P t C cst((ge,le,M),ir,(false,si,cs))(SKIP,(kenil,ks))cst((ge,le,M),ir,after).
Proof. eapply inapi_step;[reflexivity|exact Step|exact Inside]. Qed.
Theorem V293_critical_progress : lpstep P T cst S t(set T t(SKIP,(kenil,ks)))cst Sf t.
Proof.
 eapply pt_step;try reflexivity;try eassumption.
 - exact V293_critical_projection.
 - exact V293_critical_next_projection.
 - split;intros x Ne;cbn;[reflexivity|rewrite map_get_set' by congruence;reflexivity].
 - exact V293_critical_local_step.
Qed.
Theorem V293_critical_all_successors : forall Tf cf S' tf,
 lpstep P T cst S t Tf cf S' tf ->
 Tf=set T t(SKIP,(kenil,ks)) /\ cf=cst /\ S'=Sf /\ tf=t.
Proof.
 intros Tf cf S' tf H;unfold P in H;pose proof V293_critical_projection as Projection;
 pose proof V293_critical_next_projection as Next;inversion H;subst.
 - assert(C0=C)by congruence;subst C0.
   assert(tst=((ge,le,M),ir,(false,si,cs)))by congruence;subst tst.
   match goal with H:lintstep _ _ _ _ _ |- _ =>inversion H;subst;discriminate end.
 - assert(C0=C)by congruence;subst C0.
   assert(tst=((ge,le,M),ir,(false,si,cs)))by congruence;subst tst.
   match goal with H:ltstep _ _ _ _ _ _ _ _ |- _ =>unfold P in H;inversion H;subst;
     match goal with E:(pc,(po,pi,ip))=(_,(_,_,_)) |- _ =>inversion E;subst;clear E end end.
   + contradiction.
   + match goal with H:loststep _ C _ _ _ |- _ =>destruct(Unique _ _ H)as[EqC EqS];inversion EqS;subst end.
     repeat split;try reflexivity.
     eapply V293_projection_ext;[eassumption|exact Next| ].
     destruct S' as[[[[g es]mm]ii]aa];unfold S,Sf,Steq,Dteq,Piteq in *;cbn in *.
     split;intros x Ne;[exact(eq_sym(proj1 H4 x Ne))| ].
     rewrite map_get_set' by congruence;exact(eq_sym(proj2 H4 x Ne)).
 - change(get T t=Some((curs(sprim(switch x)),(kenil,ks0)):code))in H4.
   rewrite Code in H4;unfold C in H4;destruct Kind as[E|E];subst pr;discriminate.
 - change(get T tf=Some((curs(sprim(stkinit e1 e2 e3)),(kenil,ks0)):code))in H1.
   rewrite Code in H1;unfold C in H1;destruct Kind as[E|E];subst pr;discriminate.
 - change(get T tf=Some((curs(sprim(stkinit e1 e2 e3)),(kenil,ks0)):code))in H1.
   rewrite Code in H1;unfold C in H1;destruct Kind as[E|E];subst pr;discriminate.
 - change(get T tf=Some((curs(sprim(stkfree e)),(kenil,ks0)):code))in H1.
   rewrite Code in H1;unfold C in H1;destruct Kind as[E|E];subst pr;discriminate.
Qed.
Theorem V293_critical_no_output : forall Tf cf S' tf ev,
 ~lpstepev P T cst S t Tf cf S' tf ev.
Proof.
 intros Tf cf S' tf ev H;inversion H;subst.
 assert(C0=C)by congruence;subst C0.
 match goal with H:ltstepev _ _ _ _ _ _ _ _ _ |- _ =>unfold P in H;inversion H;subst;
 match goal with E:(pc,(po,pi,ip))=(_,(_,_,_)) |- _ =>inversion E;subst;clear E end;contradiction end.
Qed.
Theorem V293_critical_no_abort : ~lpstepabt P T cst S t.
Proof.
 intro H;pose proof V293_critical_projection as Projection;
 pose proof V293_critical_local_step as LocalStep;inversion H;subst.
 - assert(C0=C)by congruence;subst C0.
   assert(tst=((ge,le,M),ir,(false,si,cs)))by congruence;subst tst.
   match goal with H:ltstepabt _ _ _ _ _ |- _ =>inversion H;subst end.
   match goal with H:~(_ \/ _) |- _ =>apply H;left end.
   exists(SKIP,(kenil,ks));exists((ge,le,M),ir,after);exists cst;exact LocalStep.
 - change(get T t=Some((curs(sprim(stkinit e1 e2 e3)),(kenil,ks0)):code))in H0.
   rewrite Code in H0;unfold C in H0;destruct Kind as[E|E];subst pr;discriminate.
 - change(get T t=Some((curs(sprim(stkfree e)),(kenil,ks0)):code))in H0.
   rewrite Code in H0;unfold C in H0;destruct Kind as[E|E];subst pr;discriminate.
 - change(get T t=Some((curs(sprim(switch x)),(kenil,ks0)):code))in H0.
   rewrite Code in H0;unfold C in H0;destruct Kind as[E|E];subst pr;discriminate.
Qed.
Theorem V293_critical_progsim : forall ph Th O,
 get O curtid=Some(oscurt t) ->
 ProgSim P(set T t(SKIP,(kenil,ks)))Sf ph Th O cst t ->
 ProgSim P T S ph Th O cst t.
Proof.
 intros ph Th O Cur Post;apply simulation.prog_sim;[exact Cur| | | ].
 - intros Tf S' cf tf H;destruct(V293_critical_all_successors _ _ _ _ H)as[A[B[D E]]].
   subst;exists Th;exists O;split;[constructor|exact Post].
 - intros Tf S' cf ev tf H;exfalso;eapply V293_critical_no_output;eassumption.
 - intro H;exfalso;apply V293_critical_no_abort;exact H.
Qed.
End Critical.

Lemma V293_encrit_progsim : forall pc po pi ip T cst t ks ge le les M ir aus si cs ph Th O,
 get les t=Some le ->get aus t=Some((false,si,cs):localst) ->
 InOS(SKIP,(kenil,ks))(pumerge po pi) ->get O curtid=Some(oscurt t) ->
 ProgSim(pc,(po,pi,ip))(set T t(SKIP,(kenil,ks)))
 (ge,les,M,ir,set aus t(false,si,false::cs))ph Th O cst t ->
 ProgSim(pc,(po,pi,ip))(set T t(curs(sprim encrit),(kenil,ks)))
 (ge,les,M,ir,aus)ph Th O cst t.
Proof.
 intros pc po pi ip T cst t ks ge le les M ir aus si cs ph Th O Local Aux Inside Cur Post.
 eapply V293_critical_progsim with(le:=le)(after:=(false,si,false::cs));try eassumption.
 - left;reflexivity.
 - apply map_get_set.
 - eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
 - apply encrit_step;reflexivity.
 - intros;eapply V293_encrit_successor;eassumption.
 - rewrite tasks_set_a_set_a;exact Post.
Qed.
Lemma V293_excrit_progsim : forall pc po pi ip T cst t ks ge le les M ir aus si cs saved ph Th O,
 get les t=Some le ->get aus t=Some((false,si,saved::cs):localst) ->
 InOS(SKIP,(kenil,ks))(pumerge po pi) ->get O curtid=Some(oscurt t) ->
 ProgSim(pc,(po,pi,ip))(set T t(SKIP,(kenil,ks)))
 (ge,les,M,ir,set aus t(saved,si,cs))ph Th O cst t ->
 ProgSim(pc,(po,pi,ip))(set T t(curs(sprim excrit),(kenil,ks)))
 (ge,les,M,ir,aus)ph Th O cst t.
Proof.
 intros pc po pi ip T cst t ks ge le les M ir aus si cs saved ph Th O Local Aux Inside Cur Post.
 eapply V293_critical_progsim with(le:=le)(after:=(saved,si,cs));try eassumption.
 - right;reflexivity.
 - apply map_get_set.
 - eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
 - apply excrit_step;reflexivity.
 - intros;eapply V293_excrit_successor;eassumption.
 - rewrite tasks_set_a_set_a;exact Post.
Qed.

Lemma V293_free_cell_successor : forall p ge le M Mf b tp ks C' m',
 free tp b M=Some Mf ->
 cstep p(curs(sfree((b,tp)::nil)None),(kenil,ks))(ge,le,M)C' m' ->
 C'=(curs(sfree nil None),(kenil,ks)) /\ m'=(ge,le,Mf).
Proof.
 intros p ge le M Mf b tp ks C' m' Free H;inversion H;subst.
 - match goal with H:estep _ _ _ _ _ _ |- _ =>inversion H;subst;try discriminate end.
 - match goal with H:sstep _ _ _ _ _ _ _ |- _ =>inversion H;subst;try discriminate end.
   inversion H0;subst.
   repeat match goal with E:(_,_,_)=(_,_,_) |- _ =>inversion E;subst;clear E end.
   split;[reflexivity|congruence].
Qed.

Lemma V293_one_local_return_progsim :
 forall pc po pi ip T cst t ge le caller les M Mf ir aus si cs f body ks b tp ph Th O,
 get les t=Some le ->get aus t=Some((false,si,cs):localst) ->
 InOS(SKIP,(kenil,kcall f body caller ks))(pumerge po pi) ->
 getaddr le=((b,tp)::nil) ->free tp b M=Some Mf ->
 get O curtid=Some(oscurt t) ->
 ProgSim(pc,(po,pi,ip))(set T t(SKIP,(kenil,ks)))(ge,set les t caller,Mf,ir,aus)ph Th O cst t ->
 ProgSim(pc,(po,pi,ip))(set T t(curs sret,(kenil,kcall f body caller ks)))
 (ge,les,M,ir,aus)ph Th O cst t.
Proof.
 intros pc po pi ip T cst t ge le caller les M Mf ir aus si cs f body ks b tp ph Th O
 Local Aux Inside Layout Free Cur Post.
 eapply V293_exit_pure_progsim with(ks:=kcall f body caller ks)
 (C':=(curs(sfree((b,tp)::nil)None),(kenil,kcall f body caller ks)))(le:=le);
 try eassumption;try reflexivity.
 - eapply stmt_step;[reflexivity| ];eapply sret_step;[reflexivity|reflexivity|exact Layout].
 - eapply V293_os_family_progsim with(le:=le)(si:=si)(cs:=cs)
   (C:=(curs(sfree((b,tp)::nil)None),(kenil,kcall f body caller ks)));try eassumption.
   + apply map_get_set.
   + eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
   + do 2 eexists;eapply stmt_step;[reflexivity| ];eapply sfree_step;try reflexivity;exact Free.
   + intros C1 g1 l1 M1 Step1.
     destruct(V293_free_cell_successor _ _ _ _ _ _ _ _ _ _ Free Step1)as[A B].
     inversion B;subst g1 l1 M1;subst C1;clear B.
     assert(Same:set les t le=les).
     { change(CltEnvMod.set les t le=les);apply CltEnvMod.get_set_same;exact Local. }
     change(ProgSim(pc,(po,pi,ip))(set(set T t(curs(sfree((b,tp)::nil)None),
      (kenil,kcall f body caller ks)))t(curs(sfree nil None),(kenil,kcall f body caller ks)))
      (ge,set les t le,Mf,ir,aus)ph Th O cst t).
     rewrite Same;repeat rewrite <-set_set_eq.
     eapply V293_os_family_progsim with(le:=le)(si:=si)(cs:=cs)
      (C:=(curs(sfree nil None),(kenil,kcall f body caller ks)));try eassumption.
     * apply map_get_set.
     * eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
     * do 2 eexists;eapply stmt_step;[reflexivity| ];eapply sfreeend_step;reflexivity.
     * intros C2 g2 l2 M2 Step2.
       destruct(V293_free_end_successor _ _ _ _ _ _ _ _ _ _ Step2)as[A B].
       inversion B;subst g2 l2 M2;subst C2;clear B.
       repeat rewrite tasks_set_a_set_a;exact Post.
Qed.


Lemma V293_critical_aux_roundtrip : forall aus t si cs,
 get aus t=Some((false,si,cs):localst) ->
 set(set aus t(false,si,false::cs))t(false,si,cs)=aus.
Proof.
 intros aus t si cs Aux;apply TaskLStMod.extensionality;intro x.
 change(get(set(set aus t(false,si,false::cs))t(false,si,cs))x=get aus x).
 destruct(tidspec.beq x t)eqn:E.
 - apply tidspec.beq_true_eq in E;subst x;rewrite map_get_set;exact(eq_sym Aux).
 - apply tidspec.beq_false_neq in E;repeat rewrite map_get_set' by congruence;reflexivity.
Qed.

(* Exact critical subtree of the normalized OSIntExit body. No dispatch
   binding is needed on the disabled path. The final state restores all aux. *)
Theorem V293_exit_quiet_critical_progsim :
 forall pc po pi ip T cst t ks ge le les M ir aus si cs nesting lock dispatch bn n locked ph Th O,
 get les t=Some le ->get aus t=Some((false,si,cs):localst) ->
 InOS(SKIP,(kenil,ks))(pumerge po pi) ->get O curtid=Some(oscurt t) ->
 n<256 ->locked<256 ->get le nesting=None ->get ge nesting=Some(bn,Tint8) ->
 load Tint8 M(bn,0%Z)=Some(V293_byteval n) ->
 (0<n ->exists raw,get M(bn,0%Z)=Some(true,raw)) ->
 (Nat.pred n=0 ->get le lock=None /\ exists bl,get ge lock=Some(bl,Tint8) /\
 load Tint8(V293_exit_decrement_memory M bn n)(bl,0%Z)=Some(V293_byteval locked)) ->
 (2<=n \/ 0<locked) ->
 ProgSim(pc,(po,pi,ip))(set T t(SKIP,(kenil,ks)))
 (ge,les,V293_exit_decrement_memory M bn n,ir,aus)ph Th O cst t ->
 ProgSim(pc,(po,pi,ip))(set T t(curs(sseq(sprim encrit)
 (sseq(V293_OSIntExit_nesting_dispatch nesting lock dispatch)(sprim excrit))),(kenil,ks)))
 (ge,les,M,ir,aus)ph Th O cst t.
Proof.
 intros pc po pi ip T cst t ks ge le les M ir aus si cs nesting lock dispatch bn n locked ph Th O
 Local Aux Inside Cur Bound LockBound NL G Read Writable Lock Disabled Post.
 set(A:=set aus t(false,si,false::cs)).
 assert(Pushed:get A t=Some((false,si,false::cs):localst))by(apply map_get_set).
 assert(Round:set A t(false,si,cs)=aus)by(apply V293_critical_aux_roundtrip;exact Aux).
 eapply V293_exit_pure_progsim with(ks:=ks)(le:=le)
 (C':=(curs(sprim encrit),(kenil,kseq(sseq(V293_OSIntExit_nesting_dispatch nesting lock dispatch)(sprim excrit))ks)));
 try eassumption;try reflexivity.
 - eapply stmt_step;[reflexivity|apply sseq_step].
 - eapply V293_encrit_progsim with(le:=le)(si:=si)(cs:=cs);try eassumption.
   + eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
   + change(ProgSim(pc,(po,pi,ip))
     (set T t(SKIP,(kenil,kseq(sseq(V293_OSIntExit_nesting_dispatch nesting lock dispatch)(sprim excrit))ks)))
     (ge,les,M,ir,A)ph Th O cst t).
     eapply V293_exit_pure_progsim with(ks:=ks)(le:=le)
     (C':=(curs(sseq(V293_OSIntExit_nesting_dispatch nesting lock dispatch)(sprim excrit)),(kenil,ks)));
     try eassumption;try reflexivity.
     * eapply stmt_step;[reflexivity|apply sskip_step].
     * eapply V293_exit_pure_progsim with(ks:=ks)(le:=le)
       (C':=(curs(V293_OSIntExit_nesting_dispatch nesting lock dispatch),(kenil,kseq(sprim excrit)ks)));
       try eassumption;try reflexivity.
       -- eapply stmt_step;[reflexivity|apply sseq_step].
       -- eapply V293_exit_nesting_disabled_progsim with(le:=le)(si:=si)(cs:=false::cs)
          (bn:=bn)(n:=n)(locked:=locked);try eassumption.
          ++ eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
          ++ eapply V293_exit_pure_progsim with(ks:=ks)(le:=le)
             (C':=(curs(sprim excrit),(kenil,ks)));try eassumption;try reflexivity.
             ** eapply stmt_step;[reflexivity|apply sskip_step].
             ** eapply V293_excrit_progsim with(le:=le)(si:=si)(cs:=cs)(saved:=false);try eassumption.
                change(ProgSim(pc,(po,pi,ip))(set T t(SKIP,(kenil,ks)))
                 (ge,les,V293_exit_decrement_memory M bn n,ir,set A t(false,si,cs))ph Th O cst t).
                rewrite Round;exact Post.
Qed.

(* Pull across the actual pending sret and single Tint32 saved local. This
   starts after the running guard; it is not a whole function-entry theorem. *)
Theorem V293_exit_quiet_return_progsim :
 forall pc po pi ip T cst t ge le caller les M Mf ir aus si cs f body ks bs
 nesting lock dispatch bn n locked ph Th O,
 get les t=Some le ->get aus t=Some((false,si,cs):localst) ->
 InOS(SKIP,(kenil,kcall f body caller ks))(pumerge po pi) ->
 get O curtid=Some(oscurt t) ->
 getaddr le=((bs,Tint32)::nil) ->
 free Tint32 bs(V293_exit_decrement_memory M bn n)=Some Mf ->
 n<256 ->locked<256 ->get le nesting=None ->get ge nesting=Some(bn,Tint8) ->
 load Tint8 M(bn,0%Z)=Some(V293_byteval n) ->
 (0<n ->exists raw,get M(bn,0%Z)=Some(true,raw)) ->
 (Nat.pred n=0 ->get le lock=None /\ exists bl,get ge lock=Some(bl,Tint8) /\
 load Tint8(V293_exit_decrement_memory M bn n)(bl,0%Z)=Some(V293_byteval locked)) ->
 (2<=n \/ 0<locked) ->
 ProgSim(pc,(po,pi,ip))(set T t(SKIP,(kenil,ks)))
 (ge,set les t caller,Mf,ir,aus)ph Th O cst t ->
 ProgSim(pc,(po,pi,ip))(set T t(curs(sseq(sprim encrit)
 (sseq(V293_OSIntExit_nesting_dispatch nesting lock dispatch)(sprim excrit))),
 (kenil,kseq sret(kcall f body caller ks))))(ge,les,M,ir,aus)ph Th O cst t.
Proof.
 intros pc po pi ip T cst t ge le caller les M Mf ir aus si cs f body ks bs
 nesting lock dispatch bn n locked ph Th O Local Aux Inside Cur Layout Free
 Bound LockBound NL G Read Writable Lock Disabled Post.
 eapply V293_exit_quiet_critical_progsim with(le:=le)(si:=si)(cs:=cs)
 (bn:=bn)(n:=n)(locked:=locked);try eassumption.
 - eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
 - eapply V293_exit_pure_progsim with(ks:=kcall f body caller ks)(le:=le)
   (C':=(curs sret,(kenil,kcall f body caller ks)));try eassumption;try reflexivity.
   + eapply stmt_step;[reflexivity|apply sskip_step].
   + eapply V293_one_local_return_progsim with(le:=le)(si:=si)(cs:=cs)(b:=bs)(tp:=Tint32);
     try eassumption.
Qed.
