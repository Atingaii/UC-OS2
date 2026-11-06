(* Actual builders of the accepted normalized function, not the raw CPU-call
   implementation. This probe checks quiet and same-priority builder paths. *)
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitSamePriority.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBuilders.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitResourceBridge.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCall.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitResourceCodec.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedISRContext.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.code.V293OSIntExit.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitNondispatch.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBody.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickDelayHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitDispatch.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBoundarySwitch.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptExitEnvironment.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptFunctionEnvironment.
Require Import CertiOS.certiucos.v293.code.V293OSIntEnter.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.framework.proof.toptheorem.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitSameInternal.
Require Import CertiOS.audit.probes.V293OSIntExitSamePriorityProbe.
Require Import CertiOS.audit.probes.V293OSIntExitResourceCodecProbe.
Require Import CertiOS.audit.probes.V293OSIntExitBuildersProbe.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.framework.proof.rulesoundlib.
(* Concrete builder witnesses; assertion controls are not whole executions. *)
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitUnifiedInternal.
Require Import CertiOS.audit.probes.V293OSIntExitSameInternalProbe.
Definition UBprogram := V293_exit_env_unit 300%Z 301%Z 200%Z
 112%Z 108%Z 100%Z 101%Z 102%Z 103%Z 104%Z 120%Z
 (V293_exit_boundary_body 112%Z 108%Z 109%Z 120%Z 106%Z 103%Z 107%Z 110%Z
 111%Z 200%Z(V293_interrupt_handoff 103%Z 110%Z 107%Z)).
Definition UBfp := V293_unified_exit_fpre
 100%Z 101%Z 102%Z 103%Z 106%Z 107%Z 110%Z 111%Z 108%Z 109%Z 112%Z
 1%positive 2%positive 3%positive 4%positive 8%positive 10%positive
 13%positive 14%positive 11%positive 12%positive 16%positive
 Tvoid V293_witness_li Atrue V293_witness_li_good Logic.I.
Definition UBfq := V293_unified_exit_fpost
 100%Z 101%Z 102%Z 103%Z 106%Z 107%Z 110%Z 111%Z 108%Z 109%Z 112%Z
 1%positive 2%positive 3%positive 4%positive 8%positive 10%positive
 13%positive 14%positive 11%positive 12%positive 16%positive
 Tvoid V293_witness_li Atrue V293_witness_li_good Logic.I.
Definition UBspec I := V293_unified_exit_env_spec
 100%Z 101%Z 102%Z 103%Z 106%Z 107%Z 110%Z 111%Z 108%Z 109%Z 112%Z
 1%positive 2%positive 3%positive 4%positive 8%positive 10%positive
 13%positive 14%positive 11%positive 12%positive 16%positive
 Tvoid V293_witness_li Atrue V293_witness_li_good Logic.I I 300%Z 301%Z 200%Z.
Definition UBpre lg t := V293_exit_builder_cells 120%Z **
 getasrt(UBfp nil lg t) ** V293_exit_builder_domain 120%Z.
Definition UBpost lg t r := V293_exit_builder_cells 120%Z **
 getasrt(UBfq nil r lg t) ** V293_exit_builder_domain 120%Z.
Lemma UBbuilders : forall lg t,
 BuildPreI UBprogram 300%Z nil lg UBfp t=Some(UBpre lg t) /\
 BuildRetI UBprogram 300%Z nil lg UBfq t=Some(UBpost lg t).
Proof. intros;split;reflexivity. Qed.
Theorem UBenvironment : forall sd I,
 WFFunEnv UBprogram(UBspec I)sd V293_witness_li I /\
 WFIFun UBprogram(UBspec I)sd I V293_witness_li.
Proof.
 intros;split;unfold UBprogram,UBspec.
 - apply V293_unified_exit_env_WFFunEnv;try discriminate;exact Logic.I.
 - apply V293_unified_exit_env_WFIFun;try discriminate;exact Logic.I.
Qed.
Definition UBbigjoined nc nest locked c value := merge(BLmemory 0 Vnull nest locked nc c)(BLsaved value).
Definition UBbigmemory nc nest locked c run value := merge(UBbigjoined nc nest locked c value)(BLrun run).
Definition UBbigstate nc nest locked c run value := V293_target_wstate BLge BLle(UBbigmemory nc nest locked c run value)V293_target_fixture_abs.
Lemma UBbig_saved_join : forall nc nest locked c value,
 join(BLmemory 0 Vnull nest locked nc c)(BLsaved value)(UBbigjoined nc nest locked c value).
Proof.
 intros. apply map_join_merge;apply map_disjoint;intros[b i].
 destruct(Pos.eq_dec b 15%positive);[subst b;left;unfold BLmemory;BLoutside| ].
 right;left;unfold BLsaved;apply V293_encoded_memory_outside;left;exact n.
Qed.
Lemma UBbig_run_join : forall nc nest locked c run value,
 join(UBbigjoined nc nest locked c value)(BLrun run)(UBbigmemory nc nest locked c run value).
Proof.
 intros. apply map_join_merge;apply map_disjoint;intros[b i].
 destruct(Pos.eq_dec b 16%positive);[subst b;left|right;left;unfold BLrun;apply V293_encoded_memory_outside;left;exact n].
 unfold UBbigjoined,BLsaved,BLmemory;BLoutside.
Qed.
Lemma UBbig_owned : forall nc nest locked c run value, UBbigstate nc nest locked c run value |=
 ((BLphysical nc nest locked Vnull c) ** PV(15%positive,Int.zero)@Tint32|->value) **
 (V293_guard_cell 112%Z 16%positive run **
  (Alvarenv 120%Z Tint32(15%positive,0%Z) ** (BLbindings ** Aemp))).
Proof.
 intros.
 assert(H:UBbigstate nc nest locked c run value |=
  (((BLphysical nc nest locked Vnull c) ** PV(15%positive,Int.zero)@Tint32|->value) **
   V293_guard_cell 112%Z 16%positive run) **
  (Alvarenv 120%Z Tint32(15%positive,0%Z) ** (BLbindings ** Aemp))).
 { unfold UBbigstate. eapply V293_target_wstate_star with
 (m1:=UBbigmemory nc nest locked c run value)(m2:=emp)(o1:=V293_target_fixture_abs)(o2:=emp);try apply map_join_emp.
 - eapply V293_target_wstate_star with(m1:=UBbigjoined nc nest locked c value)(m2:=BLrun run)
   (o1:=V293_target_fixture_abs)(o2:=emp).
   + apply UBbig_run_join.
   + apply map_join_emp.
   + eapply V293_target_wstate_star with(m1:=BLmemory 0 Vnull nest locked nc c)(m2:=BLsaved value)
     (o1:=V293_target_fixture_abs)(o2:=emp).
     * apply UBbig_saved_join.
     * apply map_join_emp.
     * eapply good_fun_asrt_absop with(p:=(BLphysical nc nest locked Vnull c))(le:=emp).
       -- unfold BLphysical;apply V293_exit_physical_pre_good;apply V293_witness_li_good.
       -- apply BLphysical_owned.
     * split;[apply V293_encoded_memory_mapsto|reflexivity].
   + apply BLrun_owned.
 - apply BLcaller_names. }
 clear -H;sep auto.
Qed.
Definition UBdata run nest locked :=
 V293_quiet_globals 112%Z 108%Z 109%Z 16%positive 11%positive 12%positive **
 (Amapsto(16%positive,0%Z)Tint8 false(V293_byteval run) **
 V293_rdy_raw_cells(V293_exit_cells 11%positive 12%positive nest locked)
 (CurLINV V293_witness_li V293_idle_tid ** Atrue)).
Definition UBstate enabled run nest locked : RstateOP :=
 (BLge,BLle,UBbigmemory 0 nest locked Int.zero run(Vint32 Int.one),
 (fun _=>false),(enabled,cons 0 nil,cons false nil),V293_target_fixture_abs,spec_done None).
Definition UBlogic enabled run nest locked := V293_exit_quiet_args
 (V293_quiet_exit_args run nest locked(spec_done None)enabled(fun _=>false)(cons 0 nil)(cons false nil)).
Lemma UBdata_good : forall run nest locked,GoodFrm(UBdata run nest locked).
Proof.
 intros;unfold UBdata,V293_quiet_globals,V293_exit_cells,V293_interrupt_cells.
 cbn[V293_rdy_raw_cells GoodFrm]. repeat split;try exact Logic.I;
 apply V293_current_inv_frame;exact V293_witness_li_good.
Qed.
Lemma UBglobals_empty : V293_target_wstate BLge BLle emp emp |=
 V293_quiet_globals 112%Z 108%Z 109%Z 16%positive 11%positive 12%positive.
Proof.
 unfold V293_quiet_globals;split;[ |split];
 (eexists;split;[vm_compute;reflexivity|repeat split;reflexivity]).
Qed.
Lemma UBowned : forall run nest locked,
 UBbigstate 0 nest locked Int.zero run(Vint32 Int.one) |=
 V293_exit_builder_cells 120%Z ** UBdata run nest locked ** V293_exit_builder_domain 120%Z.
Proof.
 intros run nest locked;pose proof(UBbig_owned 0 nest locked Int.zero run(Vint32 Int.one))as Held.
 apply astar_l_adomlenv_intro with(d:=cons(120%Z,Tint32)nil)in Held;[ |exact BLdomain].
 assert(WithNames: UBbigstate 0 nest locked Int.zero run(Vint32 Int.one) |=
 V293_quiet_globals 112%Z 108%Z 109%Z 16%positive 11%positive 12%positive **
 (A_dom_lenv(cons(120%Z,Tint32)nil) **
 (((BLphysical 0 nest locked Vnull Int.zero) ** PV(15%positive,Int.zero)@Tint32|->Vint32 Int.one) **
 (V293_guard_cell 112%Z 16%positive run **
  (Alvarenv 120%Z Tint32(15%positive,0%Z) ** (BLbindings ** Aemp)))))).
 { unfold UBbigstate in *;eapply V293_target_wstate_star with
   (m1:=emp)(m2:=UBbigmemory 0 nest locked Int.zero run(Vint32 Int.one))
   (o1:=emp)(o2:=V293_target_fixture_abs);try(apply map_join_comm;apply map_join_emp).
   - exact UBglobals_empty.
   - exact Held. }
 clear Held;rename WithNames into Held.
 unfold BLphysical,V293_exit_physical_pre,V293_sched_internal_pre,V293_sched_internal_resource in Held.
 unfold UBdata,V293_exit_builder_cells,V293_time_cell,V293_time_binding,
 Alvarmapsto,Alvarenv',Aptrmapsto,V293_guard_cell,V293_exit_builder_domain in *.
 unfold V293_exit_cells,V293_interrupt_cells in *;cbn[V293_rdy_raw_cells addrval_to_addr]in *.
 sep normal in Held;sep normal;exists(Vint32 Int.one);exists 15%positive.
 clear -Held;sep auto.
Qed.
Theorem UBquiet_pre_nonempty : forall enabled run nest locked,
 run<256 ->nest<256 ->locked<256 ->(run=1 ->2<=nest \/ 0<locked) ->
 UBstate enabled run nest locked |= UBpre(UBlogic enabled run nest locked)V293_idle_tid.
Proof.
 intros enabled run nest locked Run Nest Lock Off.
 assert(Data:UBstate enabled run nest locked |=
 V293_exit_builder_cells 120%Z ** UBdata run nest locked ** V293_exit_builder_domain 120%Z).
 { eapply goodfrm_prop.
   - cbn[GoodFrm]. repeat split;try exact Logic.I;apply UBdata_good.
   - exact(UBowned run nest locked). }
 apply astar_l_aop'_intro with(aop:=spec_done None)in Data;[ |reflexivity].
 apply astar_l_aie_intro with(i:=enabled)in Data;[ |reflexivity].
 apply astar_l_ais_intro with(i:=cons 0 nil)in Data;[ |reflexivity].
 apply astar_l_aisr_intro with(i:=fun _=>false)in Data;[ |reflexivity].
 apply astar_l_acs_intro with(i:=cons false nil)in Data;[ |reflexivity].
 unfold UBpre,UBfp,V293_unified_exit_fpre,UBlogic,V293_exit_quiet_args,V293_exit_path,
 V293_quiet_exit_fpre,getasrt,V293_quiet_exit_pre.
 rewrite V293_quiet_exit_roundtrip by assumption.
 assert(Valid:V293_quiet_exit_valid run nest locked(cons 0 nil)).
 { unfold V293_quiet_exit_valid;split;[cbn[gettopis];lia|repeat split;assumption]. }
 unfold V293_quiet_external,UBdata in *;clear -Data Valid;sep auto.
Qed.
Theorem UBquiet_three_causes : forall enabled,
 (UBstate enabled 1 2 0 |= UBpre(UBlogic enabled 1 2 0)V293_idle_tid) /\
 (UBstate enabled 1 1 1 |= UBpre(UBlogic enabled 1 1 1)V293_idle_tid) /\
 (UBstate enabled 0 1 0 |= UBpre(UBlogic enabled 0 1 0)V293_idle_tid).
Proof. intro;repeat split;apply UBquiet_pre_nonempty;lia. Qed.
Lemma UBquiet_decode : forall enabled,
 V293_quiet_exit_index(V293_quiet_exit_args 1 2 0(spec_done None)enabled
 (fun _=>false)(cons 0 nil)(cons false nil))=
 Some(1,2,0,spec_done None,enabled,(fun _=>false),(cons 0 nil),(cons false nil)).
Proof. intro;apply V293_quiet_exit_roundtrip;lia. Qed.
Lemma UBquiet_valid : V293_quiet_exit_valid 1 2 0(cons 0 nil).
Proof. unfold V293_quiet_exit_valid;cbn[gettopis];repeat split;lia. Qed.
(* Only logical IE changes; memory, physical IE, ISR and both stacks stay fixed.
   Both decoders succeed and the validity condition is identical on both sides.
   This checks assertion identity, not two complete program executions. *)
Theorem UBquiet_IE_control :
 (UBstate true 1 2 0 |= UBpre(UBlogic true 1 2 0)V293_idle_tid) /\
 ~(UBstate true 1 2 0 |= UBpre(UBlogic false 1 2 0)V293_idle_tid).
Proof.
 split;[apply UBquiet_pre_nonempty;lia| ]. intro Bad.
 unfold UBpre,UBfp,V293_unified_exit_fpre,UBlogic,V293_exit_quiet_args,V293_exit_path,
 V293_quiet_exit_fpre,getasrt,V293_quiet_exit_pre in Bad.
 rewrite UBquiet_decode in Bad.
 assert(IE:UBstate true 1 2 0 |= Aie false ** Atrue).
 { unfold V293_quiet_external in Bad;clear -Bad;sep auto. }
 apply astar_l_aie_elim in IE as[E _];discriminate.
Qed.
Theorem UBsame_pre_nonempty : forall enabled,
 QPstate enabled(cons 0 nil)(cons false nil)1 Int.one(Vint32 Int.one) |=
 UBpre(V293_exit_same_args(BIlogic enabled))V293_idle_tid.
Proof.
 intro enabled;pose proof(BIpre_nonempty enabled)as Held.
 unfold UBpre,UBfp,V293_unified_exit_fpre,V293_exit_same_args,V293_exit_path,
 BIpre,BIfp,V293_same_exit_fpre,getasrt,V293_same_exit_pre in *.
 rewrite BIdecode in *.
 sep normal in Held;sep normal;destruct Held as[hv Held];exists hv.
 unfold V293_same_exit_external in *;clear -Held;sep auto.
Qed.
Theorem UBsame_actual_program : UBprogram=BIprogram.
Proof. reflexivity. Qed.
