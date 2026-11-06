(* Nonempty original tick builders, with one common internal specification. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.toptheorem.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.certiucos.v293.proofs.V293TickFunctionEnvironment.
Require Import CertiOS.certiucos.v293.proofs.V293TimeNamesGood.
Require Import CertiOS.certiucos.v293.proofs.V293TimeReadyAPI.
Require Import CertiOS.certiucos.v293.proofs.V293TimeReadyShared.
Require Import CertiOS.certiucos.v293.proofs.V293TimeGetLink.
Require Import CertiOS.certiucos.v293.proofs.V293ComponentLink.
Require Import CertiOS.certiucos.v293.proofs.V293TimeSetAPI.
Require Import CertiOS.certiucos.v293.proofs.V293TimeGetAPI.
Require Import CertiOS.certiucos.v293.code.V293OSVersion.
Require Import CertiOS.certiucos.v293.proofs.V293OSVersionAPI.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickSharedSnapshot.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickBuilderLocals.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickPostHookHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.code.V293OSTimeTick.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.audit.probes.V293TimeTickSharedSnapshotProbe.
Require Import CertiOS.audit.probes.V293TimeTickBuilderLocalsProbe.
Require Import CertiOS.audit.probes.V293TimeTickCallContextProbe.
Require Import CertiOS.audit.probes.V293TimeTickWhileSharedProbe.
Require Import CertiOS.audit.probes.V293TimeTickBodyHoareProbe.
Require Import CertiOS.audit.probes.V293TimeTickWhileRecordsProbe.
Require Import CertiOS.audit.probes.V293TimeTickPostHookCoreProbe.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition ENli:=V293_time_names_li 1001%Z 96%positive.
Definition ENgood:=V293_time_names_local_good 1001%Z 96%positive.
Definition ENprogram:=V293_tick_scheduler_program 2001%Z 2000%Z 2002%Z
 901%Z 902%Z 903%Z 904%Z 1001%Z 1002%Z 1003%Z 1000%Z 1004%Z 900%Z.
Definition ENspec:=V293_tick_scheduler_spec WhileBindings WhileIdle Vnull
 93%positive 92%positive 94%positive 96%positive 98%positive 99%positive
 95%positive 97%positive BLrest BLrest_good 2001%Z 2000%Z 2002%Z
 902%Z 903%Z 1000%Z 1004%Z ENli ENgood.
Definition ENremaining:=V293_tick_hook_remaining WhileBindings WhileIdle Vnull
 93%positive 92%positive 94%positive 96%positive 98%positive 99%positive
 95%positive 97%positive BLrest BLrest_good 2001%Z 2000%Z 2002%Z
 901%Z 902%Z 903%Z 904%Z 1001%Z 1002%Z 1003%Z 1000%Z 1004%Z 900%Z
 ENli ENgood V293_scheduler.
Definition ENinv:=V293_time_ready_inv 93%positive 92%positive 94%positive 96%positive.

Lemma ENlocal : forall owner,(CurTid owner ** BLrest) ==> CurLINV ENli owner.
Proof.
 intros owner s Held.
 assert(Env:get(getgenv s)1001%Z=Some(96%positive,Tint32)).
 { eapply V293_star_env_r with(E:=fun ge le=>get ge 1001%Z=Some(96%positive,Tint32));[ |exact Held].
   intros st HR;unfold BLrest in HR.
   eapply V293_star_env_l with(E:=fun ge le=>get ge 1001%Z=Some(96%positive,Tint32));[ |exact HR].
   intros st' HG;unfold BLglobals in HG.
   destruct HG as[_[_[GN _]]];apply agvarenv_elim in GN;exact(proj2(proj1 GN)). }
 assert(Named:s |= Agvarenv 1001%Z Tint32(96%positive,0%Z) ** (CurTid owner ** BLrest)).
 { apply astar_l_agvarenv_intro;[exact Held|split;[reflexivity|exact Env]]. }
 exists([]:list logicvar);unfold ENli,V293_time_names_li,LINV.
 pose proof ENgood as Good;clear -Named Good;sep auto.
Qed.

Theorem ENknown : forall port f pre post tp tl,
 ENspec f=Some(pre,post,(tp,tl)) -> f<>2002%Z ->
 exists d1 d2 body,
 ENprogram port f=Some(tp,d1,d2,body) /\ tlmatch tl d1 /\
 good_decllist(revlcons d1 d2)=true /\
 forall vl p r lg tid,
 Some p=BuildPreI(ENprogram port)f vl lg pre tid ->
 Some r=BuildRetI(ENprogram port)f vl lg post tid ->
 InfRules ENspec V293_scheduler ENli ENinv r Afalse p body Afalse tid.
Proof.
 intros port f pre post tp tl Lookup Other.
 eapply V293_tick_scheduler_known_bodies;try exact Lookup;try exact Other;try discriminate.
 - apply V293_time_names_noabs.
 - exact WhileBindingsValid.
 - exact WhileKeysUnique.
 - exact BLenv.
 - exact ENlocal.
 - exact(proj1 BLframe).
 - exact(proj2 BLframe).
Qed.

Theorem ENenvironment : forall port,
 WFFunEnv(ENprogram port)ENspec V293_scheduler ENli ENinv <-> ENremaining port.
Proof.
 intro port;eapply V293_tick_scheduler_environment;try discriminate.
 - apply V293_time_names_noabs.
 - exact WhileBindingsValid.
 - exact WhileKeysUnique.
 - exact BLenv.
 - exact ENlocal.
 - exact(proj1 BLframe).
 - exact(proj2 BLframe).
Qed.

Theorem ENbuilders : forall port lg tid,
 Some(SNpre lg tid)=BuildPreI(ENprogram port)2001%Z nil lg SNfpre tid /\
 Some(SNpost lg tid)=BuildRetI(ENprogram port)2001%Z nil lg SNfpost tid.
Proof. intros;split;reflexivity. Qed.

Theorem ENtick_body : forall port tid vl lg pre post,
 Some pre=BuildPreI(ENprogram port)2001%Z vl lg SNfpre tid ->
 Some post=BuildRetI(ENprogram port)2001%Z vl lg SNfpost tid ->
 InfRules ENspec V293_scheduler ENli ENinv post Afalse pre BHbody Afalse tid.
Proof.
 intros port tid vl lg pre post Pre Post.
 destruct(ENknown port 2001%Z SNfpre SNfpost Tvoid nil eq_refl ltac:(discriminate))
  as(d1&d2&body&Code&Types&Decls&Checked).
 change(Some(V293_tick_function 901%Z 902%Z 903%Z 904%Z 1001%Z 1002%Z 1003%Z 2002%Z)=
 Some(Tvoid,d1,d2,body))in Code.
 inversion Code;subst body;eapply Checked;eassumption.
Qed.

(* The positive premise is the original nonempty physical tick state, not a
   resource made satisfiable by changing the code or the shared invariant. *)
Theorem ENnonempty : forall clock run,run<256 ->
 CCstate(BHmemory clock run)(PCabs clock)(PCcode run) |=
 SNpre(SNlogic clock run WhileReady ChainEvents [1][false])WhileReady.
Proof.
 intros clock run Range.
 rewrite(proj1(SNselected clock run WhileReady ChainEvents [1][false] Range ltac:(unfold INUM;cbn;lia))).
 exact(proj2(BLallocated clock run Range)).
Qed.

Theorem ENapi_same_spec : forall lg,
 GoodI ENinv V293_scheduler ENli /\
 WFAPI(V293_clock_api_unit 201%Z 202%Z 203%Z 1001%Z 1005%Z 1006%Z)
 (V293_clock_api_spec 201%Z 202%Z 203%Z)ENli ENspec V293_scheduler ENinv lg.
Proof.
 intro lg;split;[apply V293_time_ready_names_good| ].
 apply V293_ready_clock_WFAPI;try discriminate.
 - exact ENgood.
 - apply V293_time_names_noabs.
 - apply V293_time_names_global.
Qed.

Theorem ENmissing_hook :
 ~EqDom(ENprogram None)ENspec /\
 ~WFFunEnv(ENprogram None)ENspec V293_scheduler ENli ENinv.
Proof. apply V293_tick_scheduler_missing_hook;discriminate. Qed.

(* Presence alone is insufficient: the exact same common Spec rejects only
   changing the return type, with arbitrary declarations and body unchanged. *)
Theorem ENwrong_hook_type : forall d1 d2 body,
 EqDom(ENprogram(Some(Tint32,d1,d2,body)))ENspec /\
 ~WFFunEnv(ENprogram(Some(Tint32,d1,d2,body)))ENspec V293_scheduler ENli ENinv.
Proof. intros;apply V293_tick_scheduler_wrong_hook_type;discriminate. Qed.

Theorem ENsame_type_control : forall d1 d2 body,
 EqDom(ENprogram(Some(Tvoid,d1,d2,body)))ENspec /\
 (WFFunEnv(ENprogram(Some(Tvoid,d1,d2,body)))ENspec V293_scheduler ENli ENinv <->
 ENremaining(Some(Tvoid,d1,d2,body))).
Proof.
 intros;split;[apply V293_tick_scheduler_domain;try discriminate;eexists;reflexivity|apply ENenvironment].
Qed.

Theorem ENdisjoint : forall port,
 no_fun_same(V293_clock_api_unit 201%Z 202%Z 203%Z 1001%Z 1005%Z 1006%Z)(ENprogram port).
Proof.
 intro port;unfold no_fun_same,V293_clock_api_unit,V293_component_api_unit,pumerge,
 V293_OSVersion_api_unit,V293_TimeSet_api_unit,V293_TimeGet_api_unit,
 ENprogram,V293_tick_scheduler_program.
 split;intros f Bound;repeat destruct Z.eq_dec;congruence.
Qed.
