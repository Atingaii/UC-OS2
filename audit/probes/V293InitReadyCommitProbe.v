(* Allocation/creation is inhabited independently of hooks and ready ownership.
   Physical closure remains conditional; no boot or caller simulation is claimed. *)
Require Import CertiOS.certiucos.v293.proofs.V293InitReadyCommit.
Require Import CertiOS.certiucos.v293.proofs.V293SharedStateWitness.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import Coq.Lists.List.
Import ListNotations.

Definition IRCcurrent : tid := (800%positive,Int.zero).
Definition IRCnew : tid := (801%positive,Int.zero).
Definition IRCtasks : TcbMod.map := sig IRCcurrent (Int.repr 12,rdy,Vnull).
Definition IRCupdated := set IRCtasks IRCnew (Int.repr 11,rdy,Vnull).
Definition IRCold := V293_shared_fixture_abs IRCcurrent IRCtasks (emp:EcbMod.map) Int.zero.
Definition IRCnewO := set IRCold abstcblsid(abstcblist IRCupdated).
Definition IRCprogram : progunit := fun f=>if Z.eq_dec f 900%Z then
 Some(Tvoid,dcons 901%Z(Tptr Tvoid)dnil,dnil,sskip None)else None.
Definition IRCstart := (curs(hapi_code(spec_seq(spec_crt(Vint32(Int.repr 900))Vnull
 (Vint32(Int.repr 11)))(spec_done None))),(kenil,kstop)).
Definition IRCthreads := sig IRCcurrent IRCstart.
Definition IRCend := set(set IRCthreads IRCcurrent(curs(hapi_code(spec_done None)),(kenil,kstop)))
 IRCnew(nilcont(sskip None)).

Lemma IRCslots : get IRCold curtid=Some(oscurt IRCcurrent) /\
 get IRCold abstcblsid=Some(abstcblist IRCtasks) /\
 get IRCold absecblsid=Some(absecblist(emp:EcbMod.map)) /\
 get IRCold ostmid=Some(ostm Int.zero).
Proof. repeat split;reflexivity. Qed.

Theorem IRCallocation : exists M',
 load(Tptr Tvoid)M'(802%positive,0%Z)=Some Vnull /\
 cstepstar IRCprogram(curs(sfexec 900%Z[Vnull][Tptr Tvoid]),(kenil,kstop))
 ((emp:env),(emp:env),(emp:mem))
 (curs(sskip None),(kenil,kcall 900%Z(sskip None)emp kstop))
 (emp,set emp 901%Z(802%positive,Tptr Tvoid),M').
Proof.
 destruct(V293_init_client_allocate IRCprogram 900%Z Tvoid 901%Z(sskip None)
 (emp:env)(emp:mem)802%positive Vnull eq_refl ltac:(intros l i E [v Lookup];rewrite map_emp_get in Lookup;discriminate)eq_refl)
 as(M'&Store&Read&Exec).
 exists M'. split;assumption.
Qed.

Theorem IRCcreation : forall A, exists M',
 hpstep(IRCprogram,A)IRCthreads(emp,emp,(emp:mem))IRCold
 IRCend(emp,set(emp:cltenvs)IRCnew(set emp 901%Z(802%positive,Tptr Tvoid)),M')IRCnewO /\
 load(Tptr Tvoid)M'(802%positive,0%Z)=Some Vnull /\
 get IRCend IRCnew=Some(nilcont(sskip None)) /\
 get IRCend IRCcurrent=Some(curs(hapi_code(spec_done None)),(kenil,kstop)).
Proof.
 intro A. destruct IRCallocation as(M'&Read&Allocation).
 exists M'. split.
 - eapply hpcrt_step with(t:=IRCcurrent)(t':=IRCnew)(f:=900%Z)(tls:=IRCtasks)
   (tls':=IRCupdated)(tau:=Tvoid)(d1:=dcons 901%Z(Tptr Tvoid)dnil)(d2:=dnil)
   (s:=sskip None)(le:=set emp 901%Z(802%positive,Tptr Tvoid));try reflexivity;try exact Allocation.
   unfold IRCupdated. apply TcbMod.join_sig_set. intros[v Lookup].
   change(TcbMod.get IRCtasks IRCnew=Some v)in Lookup. discriminate.
 - split;[exact Read | ]. split;[apply map_get_set | ].
   unfold IRCend. rewrite map_get_set' by discriminate. apply map_get_set.
Qed.

Theorem IRCstale : forall ge le M ir aux op br bg bp,
 ~(ge,le,M,ir,aux,IRCold,op) |=
 V293_shared_ready_records br bg bp IRCcurrent IRCupdated(emp:EcbMod.map)Int.zero ** Atrue.
Proof.
 intros. eapply V293_init_ready_stale_commit_rejected with(tasks:=IRCtasks)(new:=IRCnew).
 - reflexivity.
 - reflexivity.
Qed.

Theorem IRCnotPrimitive : ~eqdomO IRCold IRCnewO.
Proof. eapply V293_init_insert_not_ordinary_primitive;reflexivity. Qed.


Print Assumptions IRCslots.
Print Assumptions IRCallocation.
Print Assumptions IRCcreation.
Print Assumptions IRCstale.
Print Assumptions IRCnotPrimitive.
