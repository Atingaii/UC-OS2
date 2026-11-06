Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitCallExecution.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.framework.include_frm.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition CLge : env := set(set emp 100%Z(51%positive,Tint8))101%Z(52%positive,Tint8).
(* Caller has the SAME saved identifier at a DIFFERENT type, and shadows the
   running global with a local zero. sfexec must replace, then restore it. *)
Definition CLcaller : env := set(sig 601%Z(54%positive,Tint8))100%Z(53%positive,Tint8).
Definition CLmem n := V293_put_byte(V293_put_byte(V293_put_byte(V293_put_byte emp
 (51%positive,0%Z)1)(52%positive,0%Z)n)(53%positive,0%Z)0)(54%positive,0%Z)23.
Definition CLfunction := V293_OSIntExit_abstract_function 100%Z 101%Z 102%Z 601%Z
 103%Z 104%Z 105%Z 106%Z 107%Z 200%Z 203%Z.
Definition CLprogram : progunit := fun f=>if Z.eq_dec f 300%Z then Some CLfunction else None.

Lemma CLentry_loads : forall n,n<256 ->
 load Tint8(CLmem n)(51%positive,0%Z)=Some(V293_byteval 1) /\
 load Tint8(CLmem n)(52%positive,0%Z)=Some(V293_byteval n) /\
 load Tint8(CLmem n)(53%positive,0%Z)=Some(V293_byteval 0) /\
 load Tint8(CLmem n)(54%positive,0%Z)=Some(V293_byteval 23).
Proof.
 intros n Bound;repeat split;unfold CLmem;
 repeat rewrite V293_put_byte_other_load by discriminate;apply V293_put_byte_load;lia.
Qed.

Theorem CLnested_call_witness : forall n ir enabled si ci,2<=n ->n<256 ->
 exists bs Mf,
 fresh(CLmem n)bs /\
 V293_local_steps CLprogram(curs(scall 300%Z nil),(kenil,kstop))
 ((CLge,CLcaller,CLmem n),ir,(enabled,si,ci))
 (curs(sskip None),(kenil,kstop))((CLge,CLcaller,Mf),ir,(enabled,si,ci)) /\
 load Tint8 Mf(52%positive,0%Z)=Some(V293_byteval(Nat.pred n)) /\
 load Tint8 Mf(51%positive,0%Z)=Some(V293_byteval 1) /\
 load Tint8 Mf(53%positive,0%Z)=Some(V293_byteval 0) /\
 load Tint8 Mf(54%positive,0%Z)=Some(V293_byteval 23) /\
 (forall k,k<4 ->get Mf(bs,Z.of_nat k)=None) /\
 (forall b i,b<>bs ->b<>52%positive ->get Mf(b,i)=get(CLmem n)(b,i)).
Proof.
 intros n ir enabled si ci Lower Bound.
 destruct(CLentry_loads n Bound)as[Run[Nest[LocalRun LocalSaved]]].
 assert(W:exists old,get(CLmem n)(52%positive,0%Z)=Some(true,old)).
 { unfold CLmem;repeat rewrite V293_put_byte_other by discriminate;eexists;apply V293_put_byte_get_same. }
 assert(Program:CLprogram 300%Z=Some CLfunction)by reflexivity.
 destruct(V293_OSIntExit_nested_call_execution CLprogram kstop CLge CLcaller(CLmem n)ir enabled si ci
 300%Z 100%Z 101%Z 102%Z 601%Z 103%Z 104%Z 105%Z 106%Z 107%Z 200%Z 203%Z
 51%positive 52%positive n Program ltac:(discriminate)ltac:(discriminate)
 Lower Bound eq_refl eq_refl Run Nest W)as[bs[Mf[Fresh[BR[BN[Exec[Load[Running[Removed Frame]]]]]]]]].
 assert(B53:bs<>53%positive)by(eapply V293_success_load_not_fresh;eassumption).
 assert(B54:bs<>54%positive)by(eapply V293_success_load_not_fresh;eassumption).
 exists bs;exists Mf;split;[exact Fresh | ];split;[exact Exec | ];split;[exact Load | ];split;[exact Running | ].
 split.
 - etransitivity;[apply V293_load_block_frame;intro i;apply Frame;congruence | exact LocalRun].
 - split.
   + etransitivity;[apply V293_load_block_frame;intro i;apply Frame;congruence | exact LocalSaved].
   + split;assumption.
Qed.

Corollary CLnest2 : forall ir enabled si ci,
 exists bs Mf,fresh(CLmem 2)bs /\
 V293_local_steps CLprogram(curs(scall 300%Z nil),(kenil,kstop))
 ((CLge,CLcaller,CLmem 2),ir,(enabled,si,ci))
 (curs(sskip None),(kenil,kstop))((CLge,CLcaller,Mf),ir,(enabled,si,ci)) /\
 load Tint8 Mf(52%positive,0%Z)=Some(V293_byteval 1).
Proof.
 intros;destruct(CLnested_call_witness 2 ir enabled si ci ltac:(lia)ltac:(lia))as[b[M[F[E[L Rest]]]]].
 exists b;exists M;repeat split;assumption.
Qed.
Corollary CLnest255 : forall ir enabled si ci,
 exists bs Mf,fresh(CLmem 255)bs /\
 V293_local_steps CLprogram(curs(scall 300%Z nil),(kenil,kstop))
 ((CLge,CLcaller,CLmem 255),ir,(enabled,si,ci))
 (curs(sskip None),(kenil,kstop))((CLge,CLcaller,Mf),ir,(enabled,si,ci)) /\
 load Tint8 Mf(52%positive,0%Z)=Some(V293_byteval 254).
Proof.
 intros;destruct(CLnested_call_witness 255 ir enabled si ci ltac:(lia)ltac:(lia))as[b[M[F[E[L Rest]]]]].
 exists b;exists M;repeat split;assumption.
Qed.

Theorem CLno_other_callee : forall f,f<>300%Z ->CLprogram f=None.
Proof. intros f Different;unfold CLprogram;destruct(Z.eq_dec f 300%Z);congruence. Qed.
Theorem CLcaller_shadow :
 get CLcaller 100%Z=Some(53%positive,Tint8) /\
 get CLcaller 601%Z=Some(54%positive,Tint8) /\
 get CLge 100%Z=Some(51%positive,Tint8).
Proof. repeat split;reflexivity. Qed.

(* A single-factor lookup deletion. This only tests the entry boundary;
   the independent complete positive trace tests all downstream mechanisms. *)
Theorem CLmissing_function_no_step : forall ks m ir au,
 ~exists C' st',loststep(fun _=>None)(curs(sfexec 300%Z nil nil),(kenil,ks))(m,ir,au)C' st'.
Proof. intros;apply V293_missing_port_has_no_step;reflexivity. Qed.

(* Actual sfexec rejects an extra typed runtime argument, not just a builder. *)
Theorem CLreject_extra_argument : forall ks m ir au,
 ~exists C' st',loststep CLprogram
 (curs(sfexec 300%Z(Vint32 Int.zero::nil)(Tint32::nil)),(kenil,ks))(m,ir,au)C' st'.
Proof.
 intros ks m ir au[C'[st' Step]].
 inversion Step;subst;try discriminate.
 match goal with H:cstep _ _ _ _ _ |- _=>inversion H;subst;try discriminate end.
 all:match goal with E:(curs(sfexec _ _ _),_)=(_,_) |- _=>inversion E;subst;clear E end.
 - match goal with H:estep _ _ _ _ _ _ |- _=>inversion H end.
 - match goal with H:sstep _ _ _ _ _ _ _ |- _=>inversion H;subst end.
   match goal with H:CLprogram 300%Z=Some _ |- _=>
     unfold CLprogram,CLfunction,V293_OSIntExit_abstract_function in H;cbn in H;inversion H;subst end.
   match goal with H:tlmatch _ dnil |- _=>cbn in H;contradiction end.
Qed.
