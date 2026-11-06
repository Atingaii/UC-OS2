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
Definition SCsnapshot nc nest c := V293_mk_exit_snapshot 0 16 nc nest 0 c Vnull
 (Vint32 Int.one)(Vint32 Int.one)V293_idle_entries V293_idle_tasks(spec_done None).
Definition SCshared := V293_exit_snapshot_pre 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive V293_witness_li Tvoid 8%positive 10%positive 13%positive 14%positive 11%positive 12%positive.
Definition SCtail x t c := V293_exit_physical_tail
 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive(V293_xlo x)(V293_xhi x)
 V293_witness_li t(V293_xaop x)Tvoid 8%positive 10%positive(V293_xentries x)(V293_xtasks x)
 13%positive 14%positive 11%positive 12%positive(V293_xcurrent x)
 (V293_exit_depth(V293_xnest x))(V293_xlocked x)c.
Definition SCout x t := if V293_exit_enabled(V293_xnest x)(V293_xlocked x)then
 SCtail x t(if Nat.eqb(V293_ready_select(V293_xlo x)(V293_xhi x)
  (V293_ready_group(V293_xlo x)(V293_xhi x)))(V293_xcurrent x)
  then V293_xcounter x else Int.add(V293_xcounter x)Int.one) else
 V293_exit_physical_pre
 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive(V293_xlo x)(V293_xhi x)
 V293_witness_li t(V293_xaop x)Tvoid 8%positive 10%positive(V293_xentries x)(V293_xtasks x)
 13%positive 14%positive 11%positive 12%positive(V293_xcurrent x)
 (V293_exit_depth(V293_xnest x))(V293_xlocked x)(V293_xold x)(V293_xcounter x).
(* Identity is a NON-PRODUCTION callee resource contract, not a switch implementation. *)
Definition SCsw:=V293_exit_snapshot_switch_pre
 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive
 V293_witness_li Tvoid 8%positive 10%positive 13%positive 14%positive 11%positive 12%positive.
Lemma SCout_good : forall x t,GoodFunAsrt(SCout x t).
Proof.
 intros x t;unfold SCout,SCtail;destruct(V293_exit_enabled(V293_xnest x)(V293_xlocked x));
 first[apply V293_exit_physical_tail_good|apply V293_exit_physical_pre_good];apply V293_witness_li_good.
Qed.
Lemma SCout_local : forall x t,SCout x t ==> CurLINV V293_witness_li t.
Proof.
 intros x t;unfold SCout,SCtail;destruct(V293_exit_enabled(V293_xnest x)(V293_xlocked x));
 first[apply V293_exit_physical_tail_local|apply V293_exit_physical_pre_local].
Qed.
Lemma SCsw_good : forall x t address,GoodFunAsrt(SCsw x t address).
Proof. apply V293_exit_snapshot_switch_pre_good;apply V293_witness_li_good. Defined.
Definition SCentS:=V293_exit_snapshot_entry 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive V293_witness_li Tvoid 8%positive 10%positive 13%positive 14%positive 11%positive 12%positive.
Definition SCacqS:=V293_exit_snapshot_acquired 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive V293_witness_li Tvoid 8%positive 10%positive 13%positive 14%positive 11%positive 12%positive.
Definition SCleaveS:=V293_exit_snapshot_leaving 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive V293_witness_li Tvoid 8%positive 10%positive 13%positive 14%positive 11%positive 12%positive SCsw.
Definition SCrestoreS:=V293_exit_snapshot_restored SCout.
Definition SCentF:=V293_exit_select SCentS.
Definition SCacqF:=V293_exit_select SCacqS.
Definition SCleaveF:=V293_exit_select SCleaveS.
Definition SCrestoreF:=V293_exit_select SCrestoreS.
Definition SCeg:forall lg t address,GoodFunAsrt(SCentF lg t address).
Proof. apply V293_exit_select_good;apply V293_exit_snapshot_entry_good;apply V293_witness_li_good. Defined.
Definition SCag:forall lg t address,GoodFunAsrt(SCacqF lg t address).
Proof. apply V293_exit_select_good;apply V293_exit_snapshot_acquired_good;apply V293_witness_li_good. Defined.
Definition SClg:forall lg t address,GoodFunAsrt(SCleaveF lg t address).
Proof. apply V293_exit_select_good;apply V293_exit_snapshot_leaving_good;[apply V293_witness_li_good|apply SCsw_good]. Defined.
Definition SCrg:forall lg t address,GoodFunAsrt(SCrestoreF lg t address).
Proof. apply V293_exit_select_good;apply V293_exit_snapshot_restored_good;apply SCout_good. Defined.
Definition SCswitchF:=V293_exit_switch_select SCsw.
Definition SCsg:forall lg t,GoodFunAsrt(SCswitchF lg t).
Proof. apply V293_exit_switch_select_good;apply SCsw_good. Defined.
Definition SCspec : funspec := fun f =>
 if Z.eq_dec f 200%Z then Some(V293_sched_fpre 100%Z 101%Z 102%Z 103%Z
 1%positive 2%positive 3%positive 4%positive V293_witness_li V293_witness_li_good,
 V293_sched_fpost 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive
 V293_witness_li V293_witness_li_good,(Tvoid,[]))else
 if Z.eq_dec f 201%Z then Some(V293_indexed_pointer_fpre SCentF SCeg,
 V293_indexed_pointer_fpost SCacqF SCag,(Tvoid,[Tptr Tint32]))else
 if Z.eq_dec f 202%Z then Some(V293_indexed_pointer_fpre SCleaveF SClg,
 V293_indexed_pointer_fpost SCrestoreF SCrg,(Tvoid,[Tptr Tint32]))else
 if Z.eq_dec f 203%Z then Some(V293_nullary_fpre SCswitchF SCsg,
 V293_nullary_fpost SCswitchF SCsg,(Tvoid,nil))else None.
Definition SCbuilderpre nc nest c := V293_exit_builder_pre
 106%Z 107%Z 110%Z 111%Z 108%Z 109%Z 112%Z Tvoid 8%positive 10%positive
 13%positive 14%positive 11%positive 12%positive 16%positive
 (spec_done None)(SCshared(SCsnapshot nc nest c)V293_idle_tid)Aemp 1 120%Z.
Definition SCbuilderpost nc nest c := V293_exit_builder_post
 106%Z 107%Z 110%Z 111%Z 108%Z 109%Z 112%Z Tvoid 8%positive 10%positive
 13%positive 14%positive 11%positive 12%positive 16%positive
 (spec_done None)(SCshared(SCsnapshot nc nest c)V293_idle_tid)(SCout(SCsnapshot nc nest c)V293_idle_tid)Aemp 1 120%Z.
Theorem SCbuilder : forall sd I nc nest c,nc<256 ->nest<256 ->
 InfRules SCspec sd V293_witness_li I(SCbuilderpost nc nest c)Afalse(SCbuilderpre nc nest c)
 (V293_OSIntExit_body 112%Z 108%Z 109%Z 120%Z 106%Z 103%Z 107%Z 110%Z 111%Z
 200%Z 201%Z 202%Z 203%Z)Afalse V293_idle_tid.
Proof.
 intros sd I nc nest c NC Nest.
 eapply V293_OSIntExit_port_lookup_builder_contract with(P:=BLprogram)(f:=300%Z)(vl:=nil)(lg:=nil)
 (unmap:=100%Z)(group:=101%Z)(rows:=102%Z)(bt:=1%positive)(bg:=2%positive)(br:=3%positive)(bh:=4%positive)
 (lo:=0)(hi:=16)(entries:=V293_idle_entries)(tasks:=V293_idle_tasks)(nc:=nc)
 (aop:=spec_done None)(Out:=SCout)(Sw:=SCsw)(OG:=SCout_good)(SG:=SCsw_good)
 (extra:=Aemp)(run:=1)(token:=Vint32 Int.one)(old:=Vnull)(c:=c)(nest:=nest)(locked:=0)
 (value:=Vint32 Int.one)(Hli:=V293_witness_li_good)
 (GP:=ltac:(apply(V293_exit_builder_pre_good 106%Z 107%Z 110%Z 111%Z 108%Z 109%Z 112%Z
 Tvoid 8%positive 10%positive 13%positive 14%positive 11%positive 12%positive 16%positive
 (spec_done None)(SCshared(SCsnapshot nc nest c)V293_idle_tid)Aemp 1);
 [unfold SCshared;apply V293_exit_physical_pre_good;apply V293_witness_li_good|exact Logic.I]))
 (GQ:=ltac:(intro result;apply(V293_exit_builder_post_good 106%Z 107%Z 110%Z 111%Z 108%Z 109%Z 112%Z
 Tvoid 8%positive 10%positive 13%positive 14%positive 11%positive 12%positive 16%positive
 (spec_done None)(SCshared(SCsnapshot nc nest c)V293_idle_tid)(SCout(SCsnapshot nc nest c)V293_idle_tid)Aemp 1 result);
 [unfold SCshared;apply V293_exit_physical_pre_good;apply V293_witness_li_good|apply SCout_good|exact Logic.I]));
 try discriminate;try reflexivity;try (intros;reflexivity);try assumption;try lia.
 - exists 12;vm_compute;repeat split;lia.
 - exact(proj1 V293_idle_relations).
 - exact(proj2 V293_idle_relations).
 - apply SCout_local.
 - intros bs;apply V293_exit_snapshot_switch_pre_local.
Qed.
Theorem SCenabled_same : forall sd I c,
 InfRules SCspec sd V293_witness_li I(SCbuilderpost 12 1 c)Afalse(SCbuilderpre 12 1 c)
 (V293_OSIntExit_body 112%Z 108%Z 109%Z 120%Z 106%Z 103%Z 107%Z 110%Z 111%Z
 200%Z 201%Z 202%Z 203%Z)Afalse V293_idle_tid.
Proof. intros;apply SCbuilder;try lia;reflexivity. Qed.
Theorem SCdisabled_nested : forall sd I c,
 InfRules SCspec sd V293_witness_li I(SCbuilderpost 0 2 c)Afalse(SCbuilderpre 0 2 c)
 (V293_OSIntExit_body 112%Z 108%Z 109%Z 120%Z 106%Z 103%Z 107%Z 110%Z 111%Z
 200%Z 201%Z 202%Z 203%Z)Afalse V293_idle_tid.
Proof. intros;apply SCbuilder;lia. Qed.
Theorem SCenabled_different : forall sd I c,
 InfRules SCspec sd V293_witness_li I(SCbuilderpost 0 1 c)Afalse(SCbuilderpre 0 1 c)
 (V293_OSIntExit_body 112%Z 108%Z 109%Z 120%Z 106%Z 103%Z 107%Z 110%Z 111%Z
 200%Z 201%Z 202%Z 203%Z)Afalse V293_idle_tid.
Proof. intros;apply SCbuilder;lia. Qed.
Theorem SCbuilder_pre_nonempty : forall nc nest c value,
 RCbigstate nc nest c 1 value |= SCbuilderpre nc nest c.
Proof. apply RCbuilder_pre_nonempty. Qed.

Definition SCswitchstate nc c := RBlestate(RBle false)
 (RBfullmemory 12(Vptr V293_idle_tid)0 0 nc(Int.add c Int.one)).
Theorem SCswitch_pre_nonempty : forall nc c,nc<256 ->
 SCswitchstate nc c |= SCswitchF
 (V293_exit_switch_encode(SCsnapshot nc 1 c)(15%positive,Int.zero))V293_idle_tid.
Proof.
 intros nc c NC;unfold SCswitchF;rewrite V293_exit_switch_select_encoded by(repeat split;cbn;lia).
 apply RBtailresource_owned.
Qed.
Lemma SCswitch_counter_load : forall x t address s,
 s |= SCsw x t address ->
 load Tint32(getmem s)(14%positive,0%Z)=Some(Vint32(Int.add(V293_xcounter x)Int.one)).
Proof.
 intros x t address s H;unfold SCsw,V293_exit_snapshot_switch_pre in H.
 eapply V293_star_load_l;[ |exact H]. intros s1[t0 H1].
 unfold V293_exit_physical_tail in H1.
 eapply V293_star_load_r;[ |exact H1]. intros s2 H2.
 eapply V293_star_load_r;[ |exact H2]. intros s3 H3.
 eapply V293_star_load_r;[ |exact H3]. intros s4 H4.
 eapply V293_star_load_r;[ |exact H4]. intros s5[M _].
 eapply mapstoval_load;[reflexivity|exact M].
Qed.
Lemma SCswitch_saved_load : forall x t address s,
 rule_type_val_match Tint32(V293_xtoken x)=true ->
 s |= SCsw x t address ->
 load Tint32(getmem s)(fst address,Int.unsigned(snd address))=Some(V293_xtoken x).
Proof.
 intros x t [b off] s Typed H;unfold SCsw,V293_exit_snapshot_switch_pre in H.
 eapply V293_star_load_r;[ |exact H]. intros s1[M _].
 eapply mapstoval_load;[exact Typed|exact M].
Qed.
Theorem SCcounter_control :
 V293_exit_decode(V293_exit_encode(SCsnapshot 0 1 Int.zero))=Some(SCsnapshot 0 1 Int.zero) /\
 V293_exit_decode(V293_exit_encode(SCsnapshot 0 1 Int.one))=Some(SCsnapshot 0 1 Int.one) /\
 SCswitchstate 0 Int.zero |= SCswitchF
 (V293_exit_switch_encode(SCsnapshot 0 1 Int.zero)(15%positive,Int.zero))V293_idle_tid /\
 ~ (SCswitchstate 0 Int.zero |= SCswitchF
 (V293_exit_switch_encode(SCsnapshot 0 1 Int.one)(15%positive,Int.zero))V293_idle_tid).
Proof.
 split;[apply V293_exit_codec_roundtrip;repeat split;cbn;lia| ].
 split;[apply V293_exit_codec_roundtrip;repeat split;cbn;lia| ].
 split;[apply SCswitch_pre_nonempty;lia| ]. intro Bad.
 pose proof(SCswitch_pre_nonempty 0 Int.zero ltac:(lia))as Good.
 unfold SCswitchF in Bad,Good;rewrite V293_exit_switch_select_encoded in Bad,Good by(repeat split;cbn;lia).
 pose proof(SCswitch_counter_load _ _ _ _ Good)as Actual.
 pose proof(SCswitch_counter_load _ _ _ _ Bad)as Wrong.
 rewrite Actual in Wrong;vm_compute in Wrong;discriminate.
Qed.
Theorem SCaddress_control :
 SCswitchstate 0 Int.one |= SCswitchF
 (V293_exit_switch_encode(SCsnapshot 0 1 Int.one)(15%positive,Int.zero))V293_idle_tid /\
 ~ (SCswitchstate 0 Int.one |= SCswitchF
 (V293_exit_switch_encode(SCsnapshot 0 1 Int.one)(14%positive,Int.zero))V293_idle_tid).
Proof.
 split;[apply SCswitch_pre_nonempty;lia| ]. intro Bad.
 pose proof(SCswitch_pre_nonempty 0 Int.one ltac:(lia))as Good.
 unfold SCswitchF in Bad,Good;rewrite V293_exit_switch_select_encoded in Bad,Good by(repeat split;cbn;lia).
 pose proof(SCswitch_counter_load _ _ _ _ Good)as Actual.
 pose proof(SCswitch_saved_load (SCsnapshot 0 1 Int.one) _ _ _ eq_refl Bad)as Wrong.
 change(load Tint32(getmem(SCswitchstate 0 Int.one))(14%positive,0%Z)=Some(Vint32 Int.one))in Wrong.
 rewrite Actual in Wrong;vm_compute in Wrong;discriminate.
Qed.
Theorem SCcounter_frame : forall nc c1 c2 b i,b<>14%positive ->
 get(RBfullmemory 12(Vptr V293_idle_tid)0 0 nc c1)(b,i)=
 get(RBfullmemory 12(Vptr V293_idle_tid)0 0 nc c2)(b,i).
Proof.
 intros;unfold RBfullmemory,RBmemory,RBextra,V293_change_extra,V293_counter_memory.
 repeat rewrite map_merge_semp by reflexivity.
 repeat rewrite V293_encoded_memory_outside by(left;assumption);reflexivity.
Qed.
Theorem SCreject_runtime_argument : forall lg t v,
 getasrt(V293_nullary_fpre SCswitchF SCsg [v]lg t)=Afalse.
Proof. reflexivity. Qed.
Theorem SCreject_bad_logical_address : forall x t,
 SCswitchF(logic_val Vnull::V293_exit_encode x)t=Afalse.
Proof. reflexivity. Qed.

(* The fixture deliberately supplies no callee code. A call-rule proof cannot
   be promoted to WFFunEnv by silently treating Spec entries as function bodies. *)
Theorem SCmissing_callee_environment :
 BLprogram 203%Z=None /\ ~EqDom BLprogram SCspec.
Proof.
 split;[reflexivity| ]. intro Domain.
 assert(S:exists fs,SCspec 203%Z=Some fs)by(eexists;reflexivity).
 destruct(proj2(Domain 203%Z)S)as[fd Bad].
 change(None=Some fd)in Bad;discriminate.
Qed.
Theorem SCno_full_function_environment : forall sd I,
 ~WFFunEnv BLprogram SCspec sd V293_witness_li I.
Proof. intros sd I[Domain _];exact(proj2 SCmissing_callee_environment Domain). Qed.
