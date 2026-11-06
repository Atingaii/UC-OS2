(* Concrete resource controls. These are assertions/Hoare proofs, not port executions. *)
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitIndexedPort.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitCriticalCalls.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitResourceBridge.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBuilders.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitDispatch.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterInternal.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.code.V293OSIntExit.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.audit.probes.V293OSIntExitBuildersProbe.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChangeWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPrefix.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitResourceCodec.

Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitSwitchCall.
Require Import CertiOS.audit.probes.V293OSIntExitResourceCodecProbe.
Require Import CertiOS.audit.probes.V293OSIntExitResourceBridgeProbe.
Require Import CertiOS.audit.probes.V293OSIntExitSwitchCallProbe.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitInternal.

Definition UIfp:=V293_exit_internal_fpre 100%Z 101%Z 102%Z 103%Z
 1%positive 2%positive 3%positive 4%positive V293_witness_li Tvoid
 8%positive 10%positive 13%positive 14%positive 11%positive 12%positive
 V293_witness_li_good 106%Z 107%Z 110%Z 111%Z 108%Z 109%Z 112%Z 16%positive Aemp I.
Definition UIfq:=V293_exit_internal_fpost 100%Z 101%Z 102%Z 103%Z
 1%positive 2%positive 3%positive 4%positive V293_witness_li Tvoid
 8%positive 10%positive 13%positive 14%positive 11%positive 12%positive SCout
 V293_witness_li_good SCout_good 106%Z 107%Z 110%Z 111%Z 108%Z 109%Z 112%Z 16%positive Aemp I.
Definition UIpre lg t:=V293_exit_builder_cells 120%Z ** getasrt(UIfp nil lg t) ** V293_exit_builder_domain 120%Z.
Definition UIpost lg t result:=V293_exit_builder_cells 120%Z ** getasrt(UIfq nil result lg t) ** V293_exit_builder_domain 120%Z.
Theorem UIbuilders : forall lg t,
 BuildPreI BLprogram 300%Z nil lg UIfp t=Some(UIpre lg t) /\
 BuildRetI BLprogram 300%Z nil lg UIfq t=Some(UIpost lg t).
Proof. intros;split;reflexivity. Qed.
Theorem UIchecked : forall sd I vl lg t pre post,
 Some pre=BuildPreI BLprogram 300%Z vl lg UIfp t ->
 Some post=BuildRetI BLprogram 300%Z vl lg UIfq t ->
 InfRules SCspec sd V293_witness_li I post Afalse pre
 (V293_OSIntExit_body 112%Z 108%Z 109%Z 120%Z 106%Z 103%Z 107%Z 110%Z 111%Z
 200%Z 201%Z 202%Z 203%Z)Afalse t.
Proof.
 intros sd I vl lg t pre post Pre Post.
 eapply V293_OSIntExit_internal_contract with(P:=BLprogram)(f:=300%Z)(vl:=vl)(lg:=lg)
 (unmap:=100%Z)(group:=101%Z)(rows:=102%Z)(bt:=1%positive)(bg:=2%positive)(br:=3%positive)(bh:=4%positive)
 (Out:=SCout)(Sw:=SCsw)(OG:=SCout_good)(SG:=SCsw_good)(extra:=Aemp)
 (Hli:=V293_witness_li_good)(brun:=16%positive)(EG:=Logic.I);
 try discriminate;try reflexivity;try assumption;try exact Logic.I;try exact Pre;try exact Post.
 - apply SCout_local.
 - intros x t0 address;unfold SCsw;apply V293_exit_snapshot_switch_pre_local.
Qed.
Definition UIlogic run nc nest c:=V293_exit_internal_encode run(SCsnapshot nc nest c).
Theorem UIenabled_different : forall sd I c,
 InfRules SCspec sd V293_witness_li I(UIpost(UIlogic 1 0 1 c)V293_idle_tid)Afalse
 (UIpre(UIlogic 1 0 1 c)V293_idle_tid)
 (V293_OSIntExit_body 112%Z 108%Z 109%Z 120%Z 106%Z 103%Z 107%Z 110%Z 111%Z
 200%Z 201%Z 202%Z 203%Z)Afalse V293_idle_tid.
Proof. intros;eapply UIchecked with(vl:=nil);reflexivity. Qed.
Theorem UIenabled_same : forall sd I c,
 InfRules SCspec sd V293_witness_li I(UIpost(UIlogic 1 12 1 c)V293_idle_tid)Afalse
 (UIpre(UIlogic 1 12 1 c)V293_idle_tid)
 (V293_OSIntExit_body 112%Z 108%Z 109%Z 120%Z 106%Z 103%Z 107%Z 110%Z 111%Z
 200%Z 201%Z 202%Z 203%Z)Afalse V293_idle_tid.
Proof. intros;eapply UIchecked with(vl:=nil);reflexivity. Qed.
Theorem UIdisabled_nested : forall sd I c,
 InfRules SCspec sd V293_witness_li I(UIpost(UIlogic 1 0 2 c)V293_idle_tid)Afalse
 (UIpre(UIlogic 1 0 2 c)V293_idle_tid)
 (V293_OSIntExit_body 112%Z 108%Z 109%Z 120%Z 106%Z 103%Z 107%Z 110%Z 111%Z
 200%Z 201%Z 202%Z 203%Z)Afalse V293_idle_tid.
Proof. intros;eapply UIchecked with(vl:=nil);reflexivity. Qed.
Theorem UInot_running : forall sd I run c,run<256 ->run<>1 ->
 InfRules SCspec sd V293_witness_li I(UIpost(UIlogic run 0 1 c)V293_idle_tid)Afalse
 (UIpre(UIlogic run 0 1 c)V293_idle_tid)
 (V293_OSIntExit_body 112%Z 108%Z 109%Z 120%Z 106%Z 103%Z 107%Z 110%Z 111%Z
 200%Z 201%Z 202%Z 203%Z)Afalse V293_idle_tid.
Proof. intros;eapply UIchecked with(vl:=nil);reflexivity. Qed.
Lemma UIvalid : forall run nc nest c,run<256 ->nc<256 ->nest<256 ->
 V293_exit_internal_valid run(SCsnapshot nc nest c).
Proof.
 intros run nc nest c Run NC Nest;split;[exact Run| ].
 split;[repeat split;cbn;lia| ].
 split;[exists 12;vm_compute;repeat split;lia|exact V293_idle_relations].
Qed.
Lemma UIencoded_pre : forall run nc nest c t,run<256 ->nc<256 ->nest<256 ->
 getasrt(UIfp nil(UIlogic run nc nest c)t)=
 [|V293_exit_internal_valid run(SCsnapshot nc nest c)|] **
 V293_exit_builder_external_pre 106%Z 107%Z 110%Z 111%Z 108%Z 109%Z 112%Z Tvoid
 8%positive 10%positive 13%positive 14%positive 11%positive 12%positive 16%positive
 (spec_done None)(SCshared(SCsnapshot nc nest c)t)Aemp run.
Proof.
 intros;unfold UIfp,UIlogic,V293_exit_internal_fpre,V293_exit_internal_pre_asrt;cbn[getasrt].
 rewrite V293_exit_internal_roundtrip by(repeat split;cbn;lia);reflexivity.
Qed.
Definition UIscalarpre run nc nest c:=V293_exit_builder_pre
 106%Z 107%Z 110%Z 111%Z 108%Z 109%Z 112%Z Tvoid 8%positive 10%positive
 13%positive 14%positive 11%positive 12%positive 16%positive
 (spec_done None)(RCshared(RCsnapshot nc nest c)V293_idle_tid)Aemp run 120%Z.
Lemma UIscalar_nonempty : forall run nc nest c value,
 RCbigstate nc nest c run value |= UIscalarpre run nc nest c.
Proof.
 intros run nc nest c value;pose proof(RCbig_owned nc nest c run value)as Held.
 apply astar_l_adomlenv_intro with(d:=cons(120%Z,Tint32)nil)in Held;[ |exact BLdomain].
 assert(U:RCbigstate nc nest c run value |=
 (BLbindings ** (Agvarenv 112%Z Tint8(16%positive,0%Z) //\\ A_notin_lenv 112%Z)) **
 ((PV(15%positive,Int.zero)@Tint32|->value ** Alvarenv 120%Z Tint32(15%positive,0%Z)) **
 ((RCshared(RCsnapshot nc nest c)V293_idle_tid) ** (Amapsto(16%positive,0%Z)Tint8 false(V293_byteval run) **
 V293_exit_builder_domain 120%Z)))).
 { unfold V293_exit_builder_domain,V293_guard_cell in *;clear -Held;sep auto. }
 eapply astar_mono in U.
 2:{ unfold BLbindings;apply V293_exit_builder_forget_names. }
 2:{ intros s0 H0;exact H0. }
 assert(Op:RCbigstate nc nest c run value |= <||spec_done None||> **
 (V293_exit_builder_globals 106%Z 107%Z 110%Z 111%Z 108%Z 109%Z 112%Z Tvoid 8%positive 10%positive 13%positive 14%positive 11%positive 12%positive 16%positive **
 ((PV(15%positive,Int.zero)@Tint32|->value ** Alvarenv 120%Z Tint32(15%positive,0%Z)) **
 ((RCshared(RCsnapshot nc nest c)V293_idle_tid) ** (Amapsto(16%positive,0%Z)Tint8 false(V293_byteval run) **
 V293_exit_builder_domain 120%Z))))).
 { apply astar_l_aop'_intro;[exact U|reflexivity]. }
 unfold UIscalarpre,V293_exit_builder_pre,V293_exit_builder_external_pre,
 V293_exit_builder_cells,Alvarmapsto,Alvarenv',Aptrmapsto;clear -Op;sep auto.
Qed.
Theorem UIpre_nonempty_all_running : forall run nc nest c value,
 run<256 ->nc<256 ->nest<256 ->
 RCbigstate nc nest c run value |= UIpre(UIlogic run nc nest c)V293_idle_tid.
Proof.
 intros run nc nest c value Run NC Nest;pose proof(UIscalar_nonempty run nc nest c value)as Held.
 unfold UIpre;rewrite UIencoded_pre by assumption.
 pose proof(UIvalid run nc nest c Run NC Nest)as Valid.
 unfold UIscalarpre,V293_exit_builder_pre in Held;clear -Held Valid;sep auto.
Qed.
Theorem UIpre_nonempty : forall nc nest c value,nc<256 ->nest<256 ->
 RCbigstate nc nest c 1 value |= UIpre(UIlogic 1 nc nest c)V293_idle_tid.
Proof. intros;apply UIpre_nonempty_all_running;lia. Qed.
(* The alternative logical inputs are independently inhabited too. *)
Theorem UIcontrol_inputs_nonempty :
 RCbigstate 0 1 Int.zero 2 Vundef |= UIpre(UIlogic 2 0 1 Int.zero)V293_idle_tid /\
 RCbigstate 0 1 Int.one 1 Vundef |= UIpre(UIlogic 1 0 1 Int.one)V293_idle_tid.
Proof. split;apply UIpre_nonempty_all_running;lia. Qed.
Lemma UIpre_running_load : forall run nc nest c t s,run<256 ->nc<256 ->nest<256 ->
 s |= UIpre(UIlogic run nc nest c)t ->
 load Tint8(getmem s)(16%positive,0%Z)=Some(V293_byteval run).
Proof.
 intros run nc nest c t s Run NC Nest H;unfold UIpre in H;rewrite UIencoded_pre in H by assumption.
 unfold V293_exit_builder_external_pre in H.
 eapply V293_star_load_r;[ |exact H]. intros s1 H1.
 eapply V293_star_load_l;[ |exact H1]. intros s2 H2.
 eapply V293_star_load_r;[ |exact H2]. intros s3 H3.
 eapply V293_star_load_r;[ |exact H3]. intros s4 H4.
 eapply V293_star_load_r;[ |exact H4]. intros s5 H5.
 eapply V293_star_load_r;[ |exact H5]. intros s6 H6.
 eapply V293_star_load_l;[ |exact H6]. intros s7[M _].
 eapply mapstoval_load;[apply V293_byte_type;exact Run|exact M].
Qed.
Lemma UIpre_counter_load : forall run nc nest c s,run<256 ->nc<256 ->nest<256 ->
 s |= UIpre(UIlogic run nc nest c)V293_idle_tid ->
 load Tint32(getmem s)(14%positive,0%Z)=Some(Vint32 c).
Proof.
 intros run nc nest c s Run NC Nest H;unfold UIpre in H;rewrite UIencoded_pre in H by assumption.
 assert(Shared:s |= RCshared(RCsnapshot nc nest c)V293_idle_tid ** Atrue).
 { unfold V293_exit_builder_external_pre in H;clear -H;sep auto. }
 exact(RCshared_counter_load _ _ _ Shared).
Qed.
Theorem UIrunning_control :
 V293_exit_internal_index(UIlogic 1 0 1 Int.zero)=Some(1,SCsnapshot 0 1 Int.zero) /\
 V293_exit_internal_index(UIlogic 2 0 1 Int.zero)=Some(2,SCsnapshot 0 1 Int.zero) /\
 RCbigstate 0 1 Int.zero 1 Vundef |= UIpre(UIlogic 1 0 1 Int.zero)V293_idle_tid /\
 ~(RCbigstate 0 1 Int.zero 1 Vundef |= UIpre(UIlogic 2 0 1 Int.zero)V293_idle_tid).
Proof.
 split;[apply V293_exit_internal_roundtrip;repeat split;cbn;lia| ].
 split;[apply V293_exit_internal_roundtrip;repeat split;cbn;lia| ].
 split;[apply UIpre_nonempty;lia| ]. intro Bad.
 pose proof(UIpre_nonempty 0 1 Int.zero Vundef ltac:(lia)ltac:(lia))as Good.
 pose proof(UIpre_running_load 1 0 1 Int.zero V293_idle_tid _ ltac:(lia)ltac:(lia)ltac:(lia)Good)as Actual.
 pose proof(UIpre_running_load 2 0 1 Int.zero V293_idle_tid _ ltac:(lia)ltac:(lia)ltac:(lia)Bad)as Wrong.
 rewrite Actual in Wrong;vm_compute in Wrong;discriminate.
Qed.
Theorem UIcounter_control :
 V293_exit_internal_index(UIlogic 1 0 1 Int.zero)=Some(1,SCsnapshot 0 1 Int.zero) /\
 V293_exit_internal_index(UIlogic 1 0 1 Int.one)=Some(1,SCsnapshot 0 1 Int.one) /\
 RCbigstate 0 1 Int.zero 1 Vundef |= UIpre(UIlogic 1 0 1 Int.zero)V293_idle_tid /\
 ~(RCbigstate 0 1 Int.zero 1 Vundef |= UIpre(UIlogic 1 0 1 Int.one)V293_idle_tid).
Proof.
 split;[apply V293_exit_internal_roundtrip;repeat split;cbn;lia| ].
 split;[apply V293_exit_internal_roundtrip;repeat split;cbn;lia| ].
 split;[apply UIpre_nonempty;lia| ]. intro Bad.
 pose proof(UIpre_nonempty 0 1 Int.zero Vundef ltac:(lia)ltac:(lia))as Good.
 pose proof(UIpre_counter_load 1 0 1 Int.zero _ ltac:(lia)ltac:(lia)ltac:(lia)Good)as Actual.
 pose proof(UIpre_counter_load 1 0 1 Int.one _ ltac:(lia)ltac:(lia)ltac:(lia)Bad)as Wrong.
 rewrite Actual in Wrong;vm_compute in Wrong;discriminate.
Qed.
Theorem UIrunning_frame : forall nc nest c r1 r2 value b i,b<>16%positive ->
 get(RCbigmemory nc nest c r1 value)(b,i)=get(RCbigmemory nc nest c r2 value)(b,i).
Proof.
 intros;unfold RCbigmemory,BLrun;repeat rewrite map_merge_semp by reflexivity.
 repeat rewrite V293_encoded_memory_outside by(left;assumption);reflexivity.
Qed.
Theorem UIreject_runtime_argument : forall lg t v vl,
 BuildPreI BLprogram 300%Z(v::vl)lg UIfp t=None.
Proof.
 intros lg t v vl;assert(E:dl_vl_match dnil(rev(v::vl))=false).
 { destruct(rev(v::vl))eqn:Rev;[ |reflexivity].
   apply(f_equal(@rev val))in Rev;rewrite rev_involutive in Rev;discriminate. }
 unfold BuildPreI;cbn -[dl_vl_match rev];rewrite E;reflexivity.
Qed.
Theorem UIreject_bad_logic : forall t,getasrt(UIfp nil nil t)=Afalse.
Proof. reflexivity. Qed.
Theorem UIno_full_environment : forall sd I,~WFFunEnv BLprogram SCspec sd V293_witness_li I.
Proof. apply SCno_full_function_environment. Qed.
