(* Source call entry with all fresh allocation successors. The body contract
   remains universal in the chosen fresh block; no uniqueness is assumed. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.simulation.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.framework.proof.step_prop.
Require Import CertiOS.framework.proof.join_prop.
Require Import CertiOS.framework.auxlibs.MapLib.
Require Import CertiOS.certiucos.v293.proofs.V293HandoffProgSim.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCallGlobal.

Section Family.
Variables pc po pi:progunit.
Variable ip:intunit.
Variable T:tasks.
Variable cst:clientst.
Variable t:tid.
Variable C:code.
Variables ge le:env.
Variable les:cltenvs.
Variable M:mem.
Variable ir:isr.
Variable aus:ltaskstset.
Variable si:is.
Variable cs:cs.
Let P:lprog:=(pc,(po,pi,ip)).
Let S:osstate:=(ge,les,M,ir,aus).
Hypothesis Local:get les t=Some le.
Hypothesis Aux:get aus t=Some((false,si,cs):localst).
Hypothesis Code:get T t=Some C.
Hypothesis Inside:InOS C(pumerge po pi).
Hypothesis Progress:exists C' m',cstep(pumerge po pi)C(ge,le,M)C' m'.

Lemma V293_family_projection : projS S t=Some((ge,le,M),ir,(false,si,cs)).
Proof. unfold S,projS,projD;cbn;rewrite Local;cbn;rewrite Aux;reflexivity. Qed.

Theorem V293_os_family_progress : forall C' ge' le' M',
 cstep(pumerge po pi)C(ge,le,M)C'(ge',le',M') ->
 lpstep P T cst S t(set T t C')cst(ge',set les t le',M',ir,aus)t.
Proof.
 intros C' ge' le' M' Step;eapply pt_step;try reflexivity;try eassumption.
 - exact V293_family_projection.
 - unfold projS,projD;cbn;rewrite map_get_set;cbn;rewrite Aux;reflexivity.
 - split;intros x Ne;cbn;[rewrite map_get_set' by congruence| ];reflexivity.
 - eapply inapi_step;[reflexivity|apply ostc_step;exact Step|exact Inside].
Qed.

Theorem V293_os_family_all_successors : forall Tf cf Sf tf,
 lpstep P T cst S t Tf cf Sf tf ->
 exists C' ge' le' M',
 cstep(pumerge po pi)C(ge,le,M)C'(ge',le',M') /\
 Tf=set T t C' /\ cf=cst /\ Sf=(ge',set les t le',M',ir,aus) /\ tf=t.
Proof.
 intros Tf cf Sf tf H;unfold P in H;pose proof V293_family_projection as Projection.
 destruct Progress as(Cw&mw&Step);inversion H;subst.
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
     match goal with H:cstep _ C _ ?Cf ?m |- _ =>
      destruct m as[[gf lf]Mf];exists Cf;exists gf;exists lf;exists Mf end.
     split;[eassumption| ];split;[reflexivity| ];split;[reflexivity| ];split;[ |reflexivity].
     eapply V293_projection_ext;[eassumption| | ].
     * unfold projS,projD;cbn;rewrite map_get_set;cbn;rewrite Aux;reflexivity.
     * destruct Sf as[[[[g evs]mm]ii]aa];unfold S,Steq,Dteq,Piteq in *;cbn in *.
       split;intros x Ne;[rewrite map_get_set' by congruence| ];
       [exact(eq_sym(proj1 H4 x Ne))|exact(eq_sym(proj2 H4 x Ne))].
 - change(get T t=Some((curs(sprim(switch x)),(kenil,ks)):code))in H4.
   rewrite Code in H4;inversion H4;subst C;exfalso;
   eapply V293_cstep_not_primitive;[exact Step|reflexivity].
 - change(get T tf=Some((curs(sprim(stkinit e1 e2 e3)),(kenil,ks)):code))in H1.
   rewrite Code in H1;inversion H1;subst C;exfalso;
   eapply V293_cstep_not_primitive;[exact Step|reflexivity].
 - change(get T tf=Some((curs(sprim(stkinit e1 e2 e3)),(kenil,ks)):code))in H1.
   rewrite Code in H1;inversion H1;subst C;exfalso;
   eapply V293_cstep_not_primitive;[exact Step|reflexivity].
 - change(get T tf=Some((curs(sprim(stkfree e)),(kenil,ks)):code))in H1.
   rewrite Code in H1;inversion H1;subst C;exfalso;
   eapply V293_cstep_not_primitive;[exact Step|reflexivity].
Qed.

Theorem V293_os_family_no_output : forall Tf cf Sf tf ev,
 ~lpstepev P T cst S t Tf cf Sf tf ev.
Proof.
 intros Tf cf Sf tf ev H;inversion H;subst.
 assert(C0=C)by congruence;subst C0.
 match goal with H:ltstepev _ _ _ _ _ _ _ _ _ |- _ =>unfold P in H;inversion H;subst;
 match goal with E:(pc,(po,pi,ip))=(_,(_,_,_)) |- _ =>inversion E;subst;clear E end;
 contradiction end.
Qed.

Theorem V293_os_family_no_abort : ~lpstepabt P T cst S t.
Proof.
 intro H;pose proof V293_family_projection as Projection.
 destruct Progress as(Cw&[[gw lw]Mw]&Step).
 assert(LocalStep:ltstep P t C cst((ge,le,M),ir,(false,si,cs))Cw cst((gw,lw,Mw),ir,(false,si,cs))).
 { eapply inapi_step;[reflexivity|apply ostc_step;exact Step|exact Inside]. }
 inversion H;subst.
 - assert(C0=C)by congruence;subst C0.
   assert(tst=((ge,le,M),ir,(false,si,cs)))by congruence;subst tst.
   match goal with H:ltstepabt _ _ _ _ _ |- _ =>inversion H;subst end.
   match goal with H:~(_ \/ _) |- _ =>apply H;left end.
   exists Cw;exists((gw,lw,Mw),ir,(false,si,cs));exists cst;exact LocalStep.
 - change(get T t=Some((curs(sprim(stkinit e1 e2 e3)),(kenil,ks)):code))in H0.
   rewrite Code in H0;inversion H0;subst C;eapply V293_cstep_not_primitive;[exact Step|reflexivity].
 - change(get T t=Some((curs(sprim(stkfree e)),(kenil,ks)):code))in H0.
   rewrite Code in H0;inversion H0;subst C;eapply V293_cstep_not_primitive;[exact Step|reflexivity].
 - change(get T t=Some((curs(sprim(switch x)),(kenil,ks)):code))in H0.
   rewrite Code in H0;inversion H0;subst C;eapply V293_cstep_not_primitive;[exact Step|reflexivity].
Qed.

Theorem V293_os_family_progsim : forall ph Th O,
 get O curtid=Some(oscurt t) ->
 (forall C' ge' le' M',cstep(pumerge po pi)C(ge,le,M)C'(ge',le',M') ->
  ProgSim P(set T t C')(ge',set les t le',M',ir,aus)ph Th O cst t) ->
 ProgSim P T S ph Th O cst t.
Proof.
 intros ph Th O Cur Post;apply simulation.prog_sim;[exact Cur| | | ].
 - intros Tf Sf cf tf H.
   destruct(V293_os_family_all_successors _ _ _ _ H)as(Cf&gf&lf&Mf&Step&A&B&D&E).
   subst;exists Th;exists O;split;[constructor|apply Post;exact Step].
 - intros Tf Sf cf ev tf H;exfalso;eapply V293_os_family_no_output;eassumption.
 - intro H;exfalso;apply V293_os_family_no_abort;exact H.
Qed.
End Family.

Lemma V293_call_nil_successor : forall p f ks m C' m',
 cstep p(curs(scall f nil),(kenil,ks))m C' m' ->
 C'=(curs(sfexec f nil nil),(kenil,ks)) /\ m'=m.
Proof.
 intros p f ks m C' m' H;inversion H;subst.
 - match goal with H:estep _ _ _ _ _ _ |- _ =>inversion H;subst;try discriminate end.
 - match goal with H:sstep _ _ _ _ _ _ _ |- _ =>inversion H;subst;try discriminate end.
   inversion H0;subst.
   repeat match goal with E:(_,_,_)=(_,_,_) |- _ =>inversion E;subst;clear E end.
   split;reflexivity.
Qed.

Lemma V293_sched_exec_successor : forall p f unmap group rows high y ks ge caller M C' m',
 p f=Some(V293_OSSchedNew_function unmap group rows high y) ->
 cstep p(curs(sfexec f nil nil),(kenil,ks))(ge,caller,M)C' m' ->
 C'=(curs(salloc nil(dcons y Tint8 dnil)),
     (kenil,kcall f(V293_OSSchedNew_body unmap group rows high y)caller ks)) /\
 m'=(ge,(emp:env),M).
Proof.
 intros p f unmap group rows high y ks ge caller M C' m' Bind H;inversion H;subst.
 - match goal with H:estep _ _ _ _ _ _ |- _ =>inversion H;subst;try discriminate end.
 - match goal with H:sstep _ _ _ _ _ _ _ |- _ =>inversion H;subst;try discriminate end.
   inversion H0;subst.
   repeat match goal with E:(_,_,_)=(_,_,_) |- _ =>inversion E;subst;clear E end.
   unfold V293_OSSchedNew_function in Bind.
   match goal with H:p _=Some _ |- _ =>rewrite Bind in H;inversion H;subst end.
   split;reflexivity.
Qed.

Lemma V293_byte_alloc_successor : forall p y ks ge M C' m',
 cstep p(curs(salloc nil(dcons y Tint8 dnil)),(kenil,ks))(ge,(emp:env),M)C' m' ->
 exists b,fresh M b /\ C'=(curs(salloc nil dnil),(kenil,ks)) /\
 m'=(ge,(set emp y(b,Tint8):env),allocb M b 0%Z 1).
Proof.
 intros p y ks ge M C' m' H;inversion H;subst.
 - match goal with H:estep _ _ _ _ _ _ |- _ =>inversion H;subst;try discriminate end.
 - match goal with H:sstep _ _ _ _ _ _ _ |- _ =>inversion H;subst;try discriminate end.
   inversion H0;subst.
   repeat match goal with E:(_,_,_)=(_,_,_) |- _ =>inversion E;subst;clear E end.
   match goal with H:alloc _ _ _ _ _ _ |- _ =>destruct H as(b&F&EqM&N&EqL);subst end.
   exists b;split;[exact F|split;reflexivity].
Qed.

Lemma V293_alloc_end_successor : forall p f body caller ks m C' m',
 cstep p(curs(salloc nil dnil),(kenil,kcall f body caller ks))m C' m' ->
 C'=(curs body,(kenil,kcall f body caller ks)) /\ m'=m.
Proof.
 intros p f body caller ks m C' m' H;inversion H;subst.
 - match goal with H:estep _ _ _ _ _ _ |- _ =>inversion H;subst;try discriminate end.
 - match goal with H:sstep _ _ _ _ _ _ _ |- _ =>inversion H;subst;try discriminate end.
   inversion H0;subst.
   repeat match goal with E:(_,_,_)=(_,_,_) |- _ =>inversion E;subst;clear E end.
   split;reflexivity.
Qed.

Lemma V293_byte_alloc_step : forall p y ks ge M b,
 fresh M b ->
 cstep p(curs(salloc nil(dcons y Tint8 dnil)),(kenil,ks))(ge,(emp:env),M)
 (curs(salloc nil dnil),(kenil,ks))(ge,(set emp y(b,Tint8):env),allocb M b 0%Z 1).
Proof.
 intros p y ks ge M b F;eapply stmt_step;[reflexivity| ].
 eapply salloclv_step;[reflexivity|reflexivity| ].
 exists b;repeat split;try assumption;try reflexivity.
 intros [v E];rewrite map_emp_get in E;discriminate.
Qed.

(* The caller supplies the body simulation for every fresh allocation. *)
Theorem V293_sched_call_entry_progsim :
 forall pc po pi ip T cst t ge caller les M ir aus si cs
 f unmap group rows high y ks ph Th O,
 po f=Some(V293_OSSchedNew_function unmap group rows high y) ->
 get les t=Some caller -> get aus t=Some((false,si,cs):localst) ->
 get T t=Some(curs(scall f nil),(kenil,ks)) ->
 InOS(SKIP,(kenil,ks))(pumerge po pi) ->
 get O curtid=Some(oscurt t) ->
 (forall b,fresh M b ->
  ProgSim(pc,(po,pi,ip))
   (set T t(curs(V293_OSSchedNew_body unmap group rows high y),
    (kenil,kcall f(V293_OSSchedNew_body unmap group rows high y)caller ks)))
   (ge,set les t(set emp y(b,Tint8):env),allocb M b 0%Z 1,ir,aus)ph Th O cst t) ->
 ProgSim(pc,(po,pi,ip))T(ge,les,M,ir,aus)ph Th O cst t.
Proof.
 intros pc po pi ip T cst t ge caller les M ir aus si cs
 f unmap group rows high y ks ph Th O Bind Local Aux Code Inside Cur Post.
 assert (Merged:(pumerge po pi)f=Some(V293_OSSchedNew_function unmap group rows high y)).
 { unfold pumerge;rewrite Bind;reflexivity. }
 assert (Same:set les t caller=les).
 { change(CltEnvMod.set les t caller=les);apply CltEnvMod.get_set_same;exact Local. }
 eapply V293_os_family_progsim with(le:=caller)(si:=si)(cs:=cs)
  (C:=(curs(scall f nil),(kenil,ks)));try eassumption.
 - eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
 - do 2 eexists;eapply stmt_step;[reflexivity|apply snpcall_step].
 - intros C1 g1 l1 M1 Step1.
   destruct(V293_call_nil_successor _ _ _ _ _ _ Step1)as[A B];inversion B;subst g1 l1 M1;subst C1;clear B.
   change(ProgSim(pc,(po,pi,ip))(set T t(curs(sfexec f nil nil),(kenil,ks)))
    (ge,set les t caller,M,ir,aus)ph Th O cst t).
   rewrite Same.
   eapply V293_os_family_progsim with(le:=caller)(si:=si)(cs:=cs)
    (C:=(curs(sfexec f nil nil),(kenil,ks)));try eassumption.
   + apply map_get_set.
   + exists(curs(sfexec f nil nil));exists kenil;exists ks;split;[reflexivity| ].
     left;exists f;exists (nil:vallist);exists(V293_OSSchedNew_function unmap group rows high y);exists (nil:typelist).
     split;[reflexivity|exact Merged].
   + do 2 eexists;eapply stmt_step;[reflexivity| ].
     eapply sfexec_step with(d1:=dnil)(d2:=dcons y Tint8 dnil);
     [reflexivity|reflexivity|exact Merged|exact I|reflexivity].
   + intros C2 g2 l2 M2 Step2.
     destruct(V293_sched_exec_successor (pumerge po pi) f unmap group rows high y ks ge caller M C2 (g2,l2,M2) Merged Step2)as[A B].
     inversion B;subst g2 l2 M2;subst C2;clear B;repeat rewrite <-set_set_eq.
     eapply V293_os_family_progsim with(le:=(emp:env))(si:=si)(cs:=cs)
      (C:=(curs(salloc nil(dcons y Tint8 dnil)),
        (kenil,kcall f(V293_OSSchedNew_body unmap group rows high y)caller ks)));try eassumption.
     * apply map_get_set.
     * apply map_get_set.
     * eapply V293_bound_call_inos;exact Bind.
     * destruct(memory_has_fresh_block M)as[b F];do 2 eexists;apply V293_byte_alloc_step;exact F.
     * intros C3 g3 l3 M3 Step3.
       destruct(V293_byte_alloc_successor _ _ _ _ _ _ _ Step3)as(b&F&A&B).
       inversion B;subst g3 l3 M3;subst C3;clear B;repeat rewrite <-set_set_eq.
       eapply V293_os_family_progsim with(le:=(set emp y(b,Tint8):env))(si:=si)(cs:=cs)
        (C:=(curs(salloc nil dnil),
          (kenil,kcall f(V293_OSSchedNew_body unmap group rows high y)caller ks)));try eassumption.
       -- apply map_get_set.
       -- apply map_get_set.
       -- eapply V293_bound_call_inos;exact Bind.
       -- do 2 eexists;eapply stmt_step;[reflexivity|apply sallocend_step].
       -- intros C4 g4 l4 M4 Step4.
          destruct(V293_alloc_end_successor _ _ _ _ _ _ _ _ Step4)as[A B].
          inversion B;subst g4 l4 M4;subst C4;clear B.
          repeat rewrite <-set_set_eq;apply Post;exact F.
Qed.
