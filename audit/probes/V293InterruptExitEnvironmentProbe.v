(* Static linkage controls and real, independently inhabited exit builders. *)
Require Import CertiOS.certiucos.v293.proofs.V293InterruptExitEnvironment.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBoundarySwitch.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitExecution.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.audit.probes.V293OSIntExitInternalProbe.
Require Import CertiOS.audit.probes.V293OSIntExitBuildersProbe.
Require Import CertiOS.audit.probes.V293OSIntExitResourceCodecProbe.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.code.V293OSIntExit.
Require Import CertiOS.certiucos.v293.code.V293OSIntEnter.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
Require Import CertiOS.framework.include_frm.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope nat_scope.

Definition XEraw:=V293_OSIntExit_body 112%Z 108%Z 109%Z 120%Z 106%Z 103%Z 107%Z 110%Z 111%Z
 200%Z 201%Z 202%Z 203%Z.
Definition XEcritical:=V293_OSIntExit_abstract_body 112%Z 108%Z 109%Z 120%Z 106%Z 103%Z 107%Z 110%Z 111%Z
 200%Z 203%Z.
Definition XEbody:=V293_exit_boundary_body 112%Z 108%Z 109%Z 120%Z 106%Z 103%Z 107%Z 110%Z 111%Z
 200%Z(V293_interrupt_handoff 103%Z 110%Z 107%Z).
Definition XEP_with body:=V293_exit_env_unit 300%Z 301%Z 200%Z 112%Z 108%Z 100%Z 101%Z 102%Z 103%Z 104%Z 120%Z body.
Definition XEP:=XEP_with XEbody.
Definition XESpec:=V293_exit_env_spec 300%Z 301%Z 200%Z 112%Z 108%Z 100%Z 101%Z 102%Z 103%Z
 16%positive 11%positive 1%positive 2%positive 3%positive 4%positive V293_witness_li V293_witness_li_good UIfp UIfq.

Theorem XEnormalized :
 (match V293_port_normalize 201%Z 202%Z 120%Z XEraw with
 |Some s=>V293_intswitch_calls 203%Z(V293_interrupt_handoff 103%Z 110%Z 107%Z)s |None=>None end)=Some XEbody.
Proof. apply V293_OSIntExit_boundary_normalization;discriminate. Qed.
Theorem XEcritical_normalized : V293_port_normalize 201%Z 202%Z 120%Z XEraw=Some XEcritical.
Proof. apply V293_OSIntExit_abstract_normalization;discriminate. Qed.
Theorem XEswitch_only_mapping :
 V293_intswitch_calls 203%Z(V293_interrupt_handoff 103%Z 110%Z 107%Z)XEcritical=Some XEbody.
Proof. reflexivity. Qed.
Theorem XEexact_calls :
 V293_direct_calls XEraw=[201%Z;200%Z;203%Z;202%Z] /\
 V293_direct_calls XEcritical=[200%Z;203%Z] /\
 V293_direct_calls XEbody=[200%Z].
Proof. repeat split;reflexivity. Qed.
Theorem XEthree_entries :
 XEP 300%Z=Some(Tvoid,dnil,dcons 120%Z Tint32 dnil,XEbody) /\
 XEP 301%Z=Some(V293_OSIntEnter_function 112%Z 108%Z) /\
 XEP 200%Z=Some(V293_OSSchedNew_function 100%Z 101%Z 102%Z 103%Z 104%Z).
Proof. apply V293_exit_env_entries;discriminate. Qed.
Theorem XEdomain : EqDom XEP XESpec.
Proof. apply V293_exit_env_domains. Qed.
Theorem XEclosed_calls : V293_direct_calls_defined XEP.
Proof. apply V293_exit_env_calls_defined;discriminate. Qed.

(* This exposes, rather than assumes away, the still-open exit-body proof. *)
Theorem XEremaining_exact : forall sd inv,
 WFFunEnv XEP XESpec sd V293_witness_li inv <->
 (forall vl pre post lg tid,Some pre=BuildPreI XEP 300%Z vl lg UIfp tid ->
 Some post=BuildRetI XEP 300%Z vl lg UIfq tid ->
 InfRules XESpec sd V293_witness_li inv post Afalse pre XEbody Afalse tid).
Proof. intros;apply V293_exit_env_remaining_body;discriminate. Qed.
Theorem XEbuilders : forall lg t,
 BuildPreI XEP 300%Z nil lg UIfp t=Some(UIpre lg t) /\
 BuildRetI XEP 300%Z nil lg UIfq t=Some(UIpost lg t).
Proof. intros;split;reflexivity. Qed.
Theorem XEbuilders_preserve_original : forall vl lg t,
 BuildPreI XEP 300%Z vl lg UIfp t=BuildPreI BLprogram 300%Z vl lg UIfp t /\
 BuildRetI XEP 300%Z vl lg UIfq t=BuildRetI BLprogram 300%Z vl lg UIfq t.
Proof. intros;split;reflexivity. Qed.
Theorem XEnonempty_builder : forall run nc nest c value,
 run<256 ->nc<256 ->nest<256 ->
 exists pre post,BuildPreI XEP 300%Z nil(UIlogic run nc nest c)UIfp V293_idle_tid=Some pre /\
 BuildRetI XEP 300%Z nil(UIlogic run nc nest c)UIfq V293_idle_tid=Some post /\
 RCbigstate nc nest c run value |= pre.
Proof.
 intros;exists(UIpre(UIlogic run nc nest c)V293_idle_tid);
 exists(UIpost(UIlogic run nc nest c)V293_idle_tid).
 split;[reflexivity| ]. split;[reflexivity|apply UIpre_nonempty_all_running;assumption].
Qed.

(* Single factor: omit only the switch-call-site mapping, not critical normalization. *)
Theorem XEcritical_only_same_domain : EqDom(XEP_with XEcritical)XESpec.
Proof. apply V293_exit_env_domains. Qed.
Theorem XEcritical_only_unchanged_others : forall f,f<>300%Z ->XEP_with XEcritical f=XEP f.
Proof. intros f N;unfold XEP,XEP_with,V293_exit_env_unit;destruct Z.eq_dec;congruence. Qed.
Theorem XEcritical_only_rejected : ~V293_direct_calls_defined(XEP_with XEcritical).
Proof.
 intro Closed. destruct(Closed 300%Z Tvoid dnil(dcons 120%Z Tint32 dnil)XEcritical eq_refl
 203%Z(or_intror(or_introl eq_refl)))as(fd&Code). discriminate Code.
Qed.

(* Single factor: remove only the actual scheduler definition, leave Spec untouched. *)
Definition XEmissing(f:fid):option function:=if Z.eq_dec f 200%Z then None else XEP f.
Theorem XEmissing_unchanged_others : forall f,f<>200%Z ->XEmissing f=XEP f.
Proof. intros f N;unfold XEmissing;destruct Z.eq_dec;congruence. Qed.
Theorem XEmissing_exit_unchanged : XEmissing 300%Z=XEP 300%Z.
Proof. reflexivity. Qed.
Theorem XEmissing_calls_rejected : ~V293_direct_calls_defined XEmissing.
Proof.
 intro Closed. destruct(Closed 300%Z Tvoid dnil(dcons 120%Z Tint32 dnil)XEbody eq_refl
 200%Z(or_introl eq_refl))as(fd&Code). discriminate Code.
Qed.
Theorem XEmissing_WFFunEnv_rejected : forall sd inv,~WFFunEnv XEmissing XESpec sd V293_witness_li inv.
Proof.
 intros sd inv[Dom Body].
 assert(Bound:exists fs,XESpec 200%Z=Some fs)by(eexists;reflexivity).
 destruct((proj2(Dom 200%Z))Bound)as(fd&Code). discriminate Code.
Qed.
