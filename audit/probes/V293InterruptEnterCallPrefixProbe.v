(* Nonempty controls, a shadowing caller, a nontrivial interrupted expression,
   and an already active other ISR. No initialization reachability claim. *)
Require Import CertiOS.certiucos.v293.proofs.V293InterruptEnterCallPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptControlExecution.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptFixedControlSpec.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptControlRetention.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptSourceRoundtrip.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyGlobalTrace.
Require Import CertiOS.certiucos.v293.code.V293OSIntEnter.
Require Import CertiOS.audit.probes.V293InterruptControlExecutionProbe.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.framework.proof.join_prop.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition ECcaller:env:=set(set emp 801%Z(902%positive,Tint8))802%Z(901%positive,Tint8).
Definition ECprogram:progunit:=fun f=>if Z.eq_dec f 811%Z
 then Some(V293_OSIntEnter_function 801%Z 802%Z)else None.
Definition ECempty:progunit:=fun _=>None.
Definition ECwrapper:=V293_irq_source_wrapper 811%Z 812%Z Int.zero.
Definition ECip:intunit:=fun i=>if Nat.eq_dec i 0 then Some ECwrapper else None.
Definition ECprog:lprog:=(ECempty,(ECprogram,ECempty,ECip)).
Definition ECir:isr:=fun i=>Nat.eqb i 1.
Definition ECtid:tid:=(905%positive,Int.zero).
Definition ECcode:code:=(cure(econst32(Int.repr 7)),(keop1 negation Tint32 kenil,kseq(sskip None)kstop)).
Definition ECT:tasks:=set emp ECtid ECcode.
Definition ECles:cltenvs:=set emp ECtid ECcaller.
Definition ECaus:ltaskstset:=set emp ECtid((true,[1],nil):localst).
Definition ECcst:clientst:=(emp,emp,emp).

Lemma ECprogram_binding :
 ECprogram 811%Z=Some(V293_OSIntEnter_function 801%Z 802%Z) /\
 pumerge ECprogram ECempty 811%Z=Some(V293_OSIntEnter_function 801%Z 802%Z).
Proof. split;reflexivity. Qed.

Theorem ECfull_case : forall ks sd O r n l,r<256 ->n<256 ->l<256 ->
 exists Mf,
 cstepstar ECprogram(curs(scall 811%Z nil),(kenil,ks))(CEge,ECcaller,CEmemory r n l)
 (curs(sskip None),(kenil,ks))(CEge,ECcaller,Mf) /\
 V293_control_read 901%positive 902%positive 903%positive Mf=Some(V293_control_enter(V293_control r n l)) /\
 V293_control_step sd V293_control_Enter(O,V293_control r n l)
 (V293_control_Core(spec_done None))(O,V293_control_enter(V293_control r n l)) /\
 (forall a,a<>(902%positive,0%Z) ->get Mf a=get(CEmemory r n l)a).
Proof.
 intros ks sd O r n l R N L.
 destruct(CEloads r n l R N L)as[Run[Nest[Lock W]]].
 destruct(proj1 CEbindings)as[NR[GR[NN GN]]].
 eapply V293_control_enter_call_bridge with(f:=811%Z)(running:=801%Z)(nesting:=802%Z);
 try eassumption;try discriminate.
 - exact(proj1 ECprogram_binding).
 - unfold V293_control_valid;cbn;auto.
Qed.

Theorem ECglobal_case : forall sd O r n l,r<256 ->n<256 ->l<256 ->
 exists Mf,
 V293_global_steps ECprog ECcst
 (ECT,(CEge,ECles,CEmemory r n l,ECir,ECaus),ECtid)
 (set ECT ECtid(curs(scall 812%Z nil),
  (kenil,kseq(sprim exint)(kint(fst ECcode)(fst(snd ECcode))ECcaller(snd(snd ECcode))))),
  (CEge,set ECles ECtid emp,Mf,ECir,set ECaus ECtid((false,[0;1],nil):localst)),ECtid) /\
 V293_control_read 901%positive 902%positive 903%positive Mf=Some(V293_control_enter(V293_control r n l)) /\
 V293_control_step sd V293_control_Enter(O,V293_control r n l)
 (V293_control_Core(spec_done None))(O,V293_control_enter(V293_control r n l)) /\
 (forall a,a<>(902%positive,0%Z) ->get Mf a=get(CEmemory r n l)a).
Proof.
 intros sd O r n l R N L.
 destruct(CEloads r n l R N L)as[Run[Nest[Lock W]]].
 destruct(proj1 CEbindings)as[NR[GR[NN GN]]].
 eapply V293_control_enter_irq_global with(i:=0)(entry:=811%Z)(vector:=Int.zero)
 (running:=801%Z)(nesting:=802%Z);try eassumption;try discriminate.
 - unfold ECT;rewrite map_get_set;reflexivity.
 - unfold ECles;apply map_get_set.
 - unfold ECaus;apply map_get_set.
 - exact I.
 - unfold higherint,ECir;intros j Bound;assert(j=0)by lia;subst;reflexivity.
 - unfold INUM;lia.
 - reflexivity.
 - change(0<=0<2)%Z;lia.
 - reflexivity.
 - exact(proj2 ECprogram_binding).
 - unfold V293_control_valid;cbn;auto.
Qed.

(* All boundary instances contain a complete actual call, not just a reader. *)
Corollary ECboundary_calls : forall ks,
 (exists Mf,cstepstar ECprogram(curs(scall 811%Z nil),(kenil,ks))(CEge,ECcaller,CEmemory 0 254 7)
  (curs(sskip None),(kenil,ks))(CEge,ECcaller,Mf) /\
  V293_control_read 901%positive 902%positive 903%positive Mf=Some(V293_control 0 254 7)) /\
 (exists Mf,cstepstar ECprogram(curs(scall 811%Z nil),(kenil,ks))(CEge,ECcaller,CEmemory 1 254 7)
  (curs(sskip None),(kenil,ks))(CEge,ECcaller,Mf) /\
  V293_control_read 901%positive 902%positive 903%positive Mf=Some(V293_control 1 255 7)) /\
 (exists Mf,cstepstar ECprogram(curs(scall 811%Z nil),(kenil,ks))(CEge,ECcaller,CEmemory 1 255 7)
  (curs(sskip None),(kenil,ks))(CEge,ECcaller,Mf) /\
  V293_control_read 901%positive 902%positive 903%positive Mf=Some(V293_control 1 255 7)).
Proof.
 intros ks.
 destruct(ECfull_case ks(fun _ _=>True)emp 0 254 7 ltac:(lia)ltac:(lia)ltac:(lia))as[M0[T0[R0 _]]].
 destruct(ECfull_case ks(fun _ _=>True)emp 1 254 7 ltac:(lia)ltac:(lia)ltac:(lia))as[M1[T1[R1 _]]].
 destruct(ECfull_case ks(fun _ _=>True)emp 1 255 7 ltac:(lia)ltac:(lia)ltac:(lia))as[M2[T2[R2 _]]].
 split;[exists M0;split;assumption| ];split;[exists M1;split;assumption|exists M2;split;assumption].
Qed.

(* Isolated environment discriminators; they are not whole-trace mutations. *)
Lemma ECshadow_discriminator :
 evalval(V293_OSIntEnter_running 801%Z)(CEge,emp,CEmemory 1 0 7)=Some(Vint32 Int.one) /\
 evalval(V293_OSIntEnter_running 801%Z)(CEge,ECcaller,CEmemory 1 0 7)=Some(Vint32 Int.zero).
Proof.
 destruct(CEloads 1 0 7 ltac:(lia)ltac:(lia)ltac:(lia))as[Run[Nest _]].
 split;unfold V293_OSIntEnter_running;cbn [evalval evaltype get_lenv get_genv].
 - change(evalval(V293_OSIntEnter_running 801%Z)(CEge,emp,CEmemory 1 0 7)=Some(Vint32 Int.one)).
   destruct(V293_control_enter_eval CEge emp(CEmemory 1 0 7)801%Z 802%Z
    901%positive 902%positive 1 0 ltac:(lia)ltac:(lia)(proj1 CEbindings)Run Nest)as[H _].
   exact H.
 - assert(G:@get var(block*type)env EnvMap ECcaller 801%Z=Some(902%positive,Tint8))by reflexivity.
   rewrite G;cbn -[load].
   match goal with |- context [load ?T ?M ?A] =>
    let H:=fresh in assert(H:load T M A=Some(V293_byteval 0))by exact Nest;rewrite H end.
   reflexivity.
Qed.

Lemma ECcaller_discriminator :
 get ECcaller 801%Z=Some(902%positive,Tint8) /\get(emp:env)801%Z=None /\ECcaller<>emp.
Proof. split;[reflexivity| ];split;[apply map_emp_get|discriminate]. Qed.
