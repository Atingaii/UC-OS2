(* Preserve actual successful traces when adding disjoint function bindings,
   then globalize the delay prefix under its matching source call frame.
   No all-interleaving invariant or caller-entry reachability is asserted. *)
Require Import CertiOS.certiucos.v293.code.V293OSTimeDlyCall.
Require Import CertiOS.certiucos.v293.proofs.V293TimeDlySwitch.
Require Import CertiOS.certiucos.v293.proofs.V293LocalGlobalTrace.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCallGlobal.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyGlobalTrace.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.code.V293OSTimeDly.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.auxdef.
Require Import Coq.Relations.Relation_Operators.

Lemma V293_sstep_function_extension : forall P Q,
 (forall f fn, P f=Some fn ->Q f=Some fn) ->
 forall c ks m c' ks' m',sstep P c ks m c' ks' m' ->sstep Q c ks m c' ks' m'.
Proof.
 intros P Q Extension c ks m c' ks' m' Step.
 inversion Step;subst;econstructor;eauto.
Qed.

Lemma V293_cstep_function_extension : forall P Q,
 (forall f fn, P f=Some fn ->Q f=Some fn) ->
 forall C m C' m',cstep P C m C' m' ->cstep Q C m C' m'.
Proof.
 intros P Q Extension C m C' m' Step;inversion Step;subst.
 - eapply expr_step;eauto.
 - eapply stmt_step;[reflexivity| ];eapply V293_sstep_function_extension;eauto.
Qed.

Lemma V293_loststep_function_extension : forall P Q,
 (forall f fn, P f=Some fn ->Q f=Some fn) ->
 forall C st C' st',loststep P C st C' st' ->loststep Q C st C' st'.
Proof.
 intros P Q Extension C st C' st' Step;inversion Step;subst;
 try solve[econstructor;eauto].
 apply ostc_step;eapply V293_cstep_function_extension;eauto.
Qed.

Theorem V293_local_function_extension : forall P Q,
 (forall f fn, P f=Some fn ->Q f=Some fn) ->
 forall C st C' st',V293_local_steps P C st C' st' ->V293_local_steps Q C st C' st'.
Proof.
 intros P Q Extension C st C' st' Trace;unfold V293_local_steps in *.
 induction Trace;[apply rt1n_refl| ].
 eapply rt1n_trans;[eapply V293_loststep_function_extension;eauto|exact IHTrace].
Qed.

(* The input is an independently proved local prefix, not a supplied global
   trace or store. The selected pointer store is constructed from permission.
   Keeping the precise delay function binding prevents an unrelated OS frame
   from being used just to classify the body as kernel code. *)
Theorem V293_dly_trace_switch_global : forall P pc pi ip
 current rows group y ticks nesting lock sched saved f caller tail
 T les aus old next cst ge le M Mlast ir enabled si ci
 target bt bc tp inner lastle lastaux,
 P f=Some(V293_dly_function current rows group y ticks nesting lock sched saved) ->
 goodks(pc,(P,pi,ip))tail ->
 V293_local_steps P
  (curs(V293_dly_body current rows group y ticks nesting lock sched),(kenil,kstop))
  ((ge,le,M),ir,(enabled,si,ci))
  (curs(sprim(switch target)),(kenil,inner))((ge,lastle,Mlast),ir,lastaux) ->
 get ge target=Some(bt,Tptr tp) ->load(Tptr tp)Mlast(bt,0%Z)=Some(Vptr next) ->
 get ge OSTCBCur=Some(bc,Tptr tp) ->V293_bytes_writable Mlast bc 0%Z 4 ->
 let outer:=kcall f
  (V293_dly_full_body current rows group y ticks nesting lock sched saved)caller tail in
 let Tlast:=set T old(curs(sprim(switch target)),(kenil,inner##outer)) in
 let Llast:=set les old lastle in let Alast:=set aus old lastaux in
 exists Mf,
 V293_global_steps(pc,(P,pi,ip))cst
  (V293_local_global_at T les aus old
   (curs(V293_dly_body current rows group y ticks nesting lock sched),(kenil,outer))
   ((ge,le,M),ir,(enabled,si,ci)))
  (set Tlast old(SKIP,(kenil,inner##outer)),(ge,Llast,Mf,ir,Alast),next) /\
 lpstep(pc,(P,pi,ip))Tlast cst(ge,Llast,Mlast,ir,Alast)old
  (set Tlast old(SKIP,(kenil,inner##outer)))cst(ge,Llast,Mf,ir,Alast)next /\
 store(Tptr tp)Mlast(bc,0%Z)(Vptr next)=Some Mf /\
 load(Tptr tp)Mf(bc,0%Z)=Some(Vptr next) /\
 (forall b i,b<>bc \/(i<0)%Z \/(4<=i)%Z ->get Mf(b,i)=get Mlast(b,i)).
Proof.
 intros P pc pi ip current rows group y ticks nesting lock sched saved f caller tail
 T les aus old next cst ge le M Mlast ir enabled si ci target bt bc tp inner lastle lastaux
 Bind Good Trace Target Read Current Writable outer Tlast Llast Alast.
 assert(Extension:forall g fn,P g=Some fn ->pumerge P pi g=Some fn).
 { intros g fn Bound;unfold pumerge;rewrite Bound;reflexivity. }
 pose proof(V293_local_function_extension P(pumerge P pi)Extension _ _ _ _ Trace)as Extended.
 assert(Enclosing:goodks(pc,(P,pi,ip))
  (snd(snd(V293_enclose
   (curs(V293_dly_body current rows group y ticks nesting lock sched),(kenil,kstop))outer)))).
 { change (goodks(pc,(P,pi,ip))outer). unfold outer. cbn [goodks]. unfold pumerge;rewrite Bind;exact Good. }
 pose proof(V293_local_steps_global pc P pi ip _ _ _ _ Extended f
  (V293_dly_full_body current rows group y ticks nesting lock sched saved)caller tail
  Tvoid(dcons ticks Tint32 dnil)(dcons y Tint8(dcons saved Tint32 dnil))
  T les aus old cst Bind Enclosing)as Prefix.
 destruct(V293_sched_switch_commit pc P pi ip Tlast cst(inner##outer)old next target bt bc tp
  ge lastle Llast Mlast ir lastaux Alast
  (map_get_set _ _ _)(map_get_set _ _ _)(map_get_set _ _ _)
  Target Read Current Writable)as(Mf&Switch&Store&Loaded&Frame).
 exists Mf;split.
 - eapply V293_global_trans;[exact Prefix| ].
   unfold V293_global_steps.
   eapply rt1n_trans with(y:=(set Tlast old(SKIP,(kenil,inner##outer)),
     (ge,Llast,Mf,ir,Alast),next));[exact Switch|apply rt1n_refl].
 - split;[exact Switch| ];split;[exact Store| ];split;assumption.
Qed.
