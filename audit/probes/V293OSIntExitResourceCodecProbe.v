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

Definition RCsnapshot nc nest c := V293_mk_exit_snapshot 0 16 nc nest 0 c Vnull
 (Vint32 Int.zero)(Vint32 Int.zero)V293_idle_entries V293_idle_tasks(spec_done None).
Definition RCshared := V293_exit_snapshot_pre 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive V293_witness_li Tvoid 8%positive 10%positive 13%positive 14%positive 11%positive 12%positive.
Definition RCtail x t := V293_exit_physical_tail
 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive(V293_xlo x)(V293_xhi x)
 V293_witness_li t(V293_xaop x)Tvoid 8%positive 10%positive(V293_xentries x)(V293_xtasks x)
 13%positive 14%positive 11%positive 12%positive(V293_xcurrent x)
 (V293_exit_depth(V293_xnest x))(V293_xlocked x)(V293_xcounter x).
Definition RCout x t := if V293_exit_enabled(V293_xnest x)(V293_xlocked x)then RCtail x t else
 V293_exit_physical_pre
 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive(V293_xlo x)(V293_xhi x)
 V293_witness_li t(V293_xaop x)Tvoid 8%positive 10%positive(V293_xentries x)(V293_xtasks x)
 13%positive 14%positive 11%positive 12%positive(V293_xcurrent x)
 (V293_exit_depth(V293_xnest x))(V293_xlocked x)(V293_xold x)(V293_xcounter x).
Definition RCsw (_:V293_exit_snapshot)(_:tid)(_:addrval):asrt:=Afalse.
Lemma RCout_good : forall x t,GoodFunAsrt(RCout x t).
Proof.
 intros x t;unfold RCout,RCtail;destruct(V293_exit_enabled(V293_xnest x)(V293_xlocked x));
 first[apply V293_exit_physical_tail_good|apply V293_exit_physical_pre_good];apply V293_witness_li_good.
Qed.
Lemma RCout_local : forall x t,RCout x t ==> CurLINV V293_witness_li t.
Proof.
 intros x t;unfold RCout,RCtail;destruct(V293_exit_enabled(V293_xnest x)(V293_xlocked x));
 first[apply V293_exit_physical_tail_local|apply V293_exit_physical_pre_local].
Qed.
Lemma RCsw_good : forall x t address,GoodFunAsrt(RCsw x t address).
Proof. intros;exact I. Qed.
Definition RCentS:=V293_exit_snapshot_entry 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive V293_witness_li Tvoid 8%positive 10%positive 13%positive 14%positive 11%positive 12%positive.
Definition RCacqS:=V293_exit_snapshot_acquired 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive V293_witness_li Tvoid 8%positive 10%positive 13%positive 14%positive 11%positive 12%positive.
Definition RCleaveS:=V293_exit_snapshot_leaving 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive V293_witness_li Tvoid 8%positive 10%positive 13%positive 14%positive 11%positive 12%positive RCsw.
Definition RCrestoreS:=V293_exit_snapshot_restored RCout.
Definition RCentF:=V293_exit_select RCentS.
Definition RCacqF:=V293_exit_select RCacqS.
Definition RCleaveF:=V293_exit_select RCleaveS.
Definition RCrestoreF:=V293_exit_select RCrestoreS.
Definition RCeg:forall lg t address,GoodFunAsrt(RCentF lg t address).
Proof. apply V293_exit_select_good;apply V293_exit_snapshot_entry_good;apply V293_witness_li_good. Defined.
Definition RCag:forall lg t address,GoodFunAsrt(RCacqF lg t address).
Proof. apply V293_exit_select_good;apply V293_exit_snapshot_acquired_good;apply V293_witness_li_good. Defined.
Definition RClg:forall lg t address,GoodFunAsrt(RCleaveF lg t address).
Proof. apply V293_exit_select_good;apply V293_exit_snapshot_leaving_good;[apply V293_witness_li_good|apply RCsw_good]. Defined.
Definition RCrg:forall lg t address,GoodFunAsrt(RCrestoreF lg t address).
Proof. apply V293_exit_select_good;apply V293_exit_snapshot_restored_good;apply RCout_good. Defined.
Definition RCspec : funspec := fun f =>
 if Z.eq_dec f 200%Z then Some(V293_sched_fpre 100%Z 101%Z 102%Z 103%Z
 1%positive 2%positive 3%positive 4%positive V293_witness_li V293_witness_li_good,
 V293_sched_fpost 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive
 V293_witness_li V293_witness_li_good,(Tvoid,[]))else
 if Z.eq_dec f 201%Z then Some(V293_indexed_pointer_fpre RCentF RCeg,
 V293_indexed_pointer_fpost RCacqF RCag,(Tvoid,[Tptr Tint32]))else
 if Z.eq_dec f 202%Z then Some(V293_indexed_pointer_fpre RCleaveF RClg,
 V293_indexed_pointer_fpost RCrestoreF RCrg,(Tvoid,[Tptr Tint32]))else None.
Definition RCbuilderpre nc nest c := V293_exit_builder_pre
 106%Z 107%Z 110%Z 111%Z 108%Z 109%Z 112%Z Tvoid 8%positive 10%positive
 13%positive 14%positive 11%positive 12%positive 16%positive
 (spec_done None)(RCshared(RCsnapshot nc nest c)V293_idle_tid)Aemp 1 120%Z.
Definition RCbuilderpost nc nest c := V293_exit_builder_post
 106%Z 107%Z 110%Z 111%Z 108%Z 109%Z 112%Z Tvoid 8%positive 10%positive
 13%positive 14%positive 11%positive 12%positive 16%positive
 (spec_done None)(RCshared(RCsnapshot nc nest c)V293_idle_tid)(RCout(RCsnapshot nc nest c)V293_idle_tid)Aemp 1 120%Z.
Theorem RCbuilder : forall sd I nc nest c,nc<256 ->nest<256 ->
 (V293_exit_depth nest=0 ->12=nc) ->
 InfRules RCspec sd V293_witness_li I(RCbuilderpost nc nest c)Afalse(RCbuilderpre nc nest c)
 (V293_OSIntExit_body 112%Z 108%Z 109%Z 120%Z 106%Z 103%Z 107%Z 110%Z 111%Z
 200%Z 201%Z 202%Z 203%Z)Afalse V293_idle_tid.
Proof.
 intros sd I nc nest c NC Nest Same.
 eapply V293_OSIntExit_encoded_builder_contract with(P:=BLprogram)(f:=300%Z)(vl:=nil)(lg:=nil)
 (unmap:=100%Z)(group:=101%Z)(rows:=102%Z)(bt:=1%positive)(bg:=2%positive)(br:=3%positive)(bh:=4%positive)
 (lo:=0)(hi:=16)(entries:=V293_idle_entries)(tasks:=V293_idle_tasks)(nc:=nc)
 (aop:=spec_done None)(Out:=RCout)(Sw:=RCsw)(OG:=RCout_good)(SG:=RCsw_good)
 (extra:=Aemp)(run:=1)(token:=Vint32 Int.zero)(old:=Vnull)(c:=c)(nest:=nest)(locked:=0)
 (value:=Vint32 Int.zero)(Hli:=V293_witness_li_good)
 (GP:=ltac:(apply(V293_exit_builder_pre_good 106%Z 107%Z 110%Z 111%Z 108%Z 109%Z 112%Z
 Tvoid 8%positive 10%positive 13%positive 14%positive 11%positive 12%positive 16%positive
 (spec_done None)(RCshared(RCsnapshot nc nest c)V293_idle_tid)Aemp 1);
 [unfold RCshared;apply V293_exit_physical_pre_good;apply V293_witness_li_good|exact Logic.I]))
 (GQ:=ltac:(intro result;apply(V293_exit_builder_post_good 106%Z 107%Z 110%Z 111%Z 108%Z 109%Z 112%Z
 Tvoid 8%positive 10%positive 13%positive 14%positive 11%positive 12%positive 16%positive
 (spec_done None)(RCshared(RCsnapshot nc nest c)V293_idle_tid)(RCout(RCsnapshot nc nest c)V293_idle_tid)Aemp 1 result);
 [unfold RCshared;apply V293_exit_physical_pre_good;apply V293_witness_li_good|apply RCout_good|exact Logic.I]));
 try discriminate;try reflexivity;try (intros;reflexivity);try assumption;try lia.
 - exists 12;vm_compute;repeat split;lia.
 - exact(proj1 V293_idle_relations).
 - exact(proj2 V293_idle_relations).
 - apply RCout_local.
 - intros bs s H;contradiction.
 - intros bs _ Depth _ Different;exfalso;apply Different.
   change(12=nc);apply Same;exact Depth.
Qed.
Theorem RCenabled_same_priority : forall sd I c,
 InfRules RCspec sd V293_witness_li I(RCbuilderpost 12 1 c)Afalse(RCbuilderpre 12 1 c)
 (V293_OSIntExit_body 112%Z 108%Z 109%Z 120%Z 106%Z 103%Z 107%Z 110%Z 111%Z
 200%Z 201%Z 202%Z 203%Z)Afalse V293_idle_tid.
Proof. intros;apply RCbuilder;try lia;reflexivity. Qed.
Theorem RCdisabled_nested : forall sd I c,
 InfRules RCspec sd V293_witness_li I(RCbuilderpost 0 2 c)Afalse(RCbuilderpre 0 2 c)
 (V293_OSIntExit_body 112%Z 108%Z 109%Z 120%Z 106%Z 103%Z 107%Z 110%Z 111%Z
 200%Z 201%Z 202%Z 203%Z)Afalse V293_idle_tid.
Proof. intros;apply RCbuilder;try lia;intro D;discriminate. Qed.
Theorem RCreject_empty : forall t address,RCentF nil t address=Afalse.
Proof. reflexivity. Qed.
Theorem RCreject_extra_field : forall x t address,
 RCentF(V293_exit_encode x++(logic_val Vundef)::nil)t address=Afalse.
Proof. intros [];reflexivity. Qed.
Theorem RCreject_out_of_byte : forall t address c,
 RCentF(V293_exit_encode(RCsnapshot 256 1 c))t address=Afalse.
Proof. intros;reflexivity. Qed.
Theorem RCcodec_full_payload : forall lo hi nc nest locked c old token value entries tasks aop,
 lo<256 ->hi<256 ->nc<256 ->nest<256 ->locked<256 ->
 V293_exit_decode(V293_exit_encode(V293_mk_exit_snapshot lo hi nc nest locked c old token value entries tasks aop))=
 Some(V293_mk_exit_snapshot lo hi nc nest locked c old token value entries tasks aop).
Proof. intros;apply V293_exit_codec_roundtrip;repeat split;assumption. Qed.
Definition RCbigjoined nc nest c value := merge(BLmemory 0 Vnull nest 0 nc c)(BLsaved value).
Definition RCbigmemory nc nest c run value := merge(RCbigjoined nc nest c value)(BLrun run).
Definition RCbigstate nc nest c run value := V293_target_wstate BLge BLle(RCbigmemory nc nest c run value)V293_target_fixture_abs.
Lemma RCbig_saved_join : forall nc nest c value,
 join(BLmemory 0 Vnull nest 0 nc c)(BLsaved value)(RCbigjoined nc nest c value).
Proof.
 intros. apply map_join_merge;apply map_disjoint;intros[b i].
 destruct(Pos.eq_dec b 15%positive);[subst b;left;unfold BLmemory;BLoutside| ].
 right;left;unfold BLsaved;apply V293_encoded_memory_outside;left;exact n.
Qed.
Lemma RCbig_run_join : forall nc nest c run value,
 join(RCbigjoined nc nest c value)(BLrun run)(RCbigmemory nc nest c run value).
Proof.
 intros. apply map_join_merge;apply map_disjoint;intros[b i].
 destruct(Pos.eq_dec b 16%positive);[subst b;left|right;left;unfold BLrun;apply V293_encoded_memory_outside;left;exact n].
 unfold RCbigjoined,BLsaved,BLmemory;BLoutside.
Qed.
Lemma RCbig_owned : forall nc nest c run value, RCbigstate nc nest c run value |=
 ((RCshared(RCsnapshot nc nest c)V293_idle_tid) ** PV(15%positive,Int.zero)@Tint32|->value) **
 (V293_guard_cell 112%Z 16%positive run **
  (Alvarenv 120%Z Tint32(15%positive,0%Z) ** (BLbindings ** Aemp))).
Proof.
 intros.
 assert(H:RCbigstate nc nest c run value |=
  (((RCshared(RCsnapshot nc nest c)V293_idle_tid) ** PV(15%positive,Int.zero)@Tint32|->value) **
   V293_guard_cell 112%Z 16%positive run) **
  (Alvarenv 120%Z Tint32(15%positive,0%Z) ** (BLbindings ** Aemp))).
 { unfold RCbigstate. eapply V293_target_wstate_star with
 (m1:=RCbigmemory nc nest c run value)(m2:=emp)(o1:=V293_target_fixture_abs)(o2:=emp);try apply map_join_emp.
 - eapply V293_target_wstate_star with(m1:=RCbigjoined nc nest c value)(m2:=BLrun run)
   (o1:=V293_target_fixture_abs)(o2:=emp).
   + apply RCbig_run_join.
   + apply map_join_emp.
   + eapply V293_target_wstate_star with(m1:=BLmemory 0 Vnull nest 0 nc c)(m2:=BLsaved value)
     (o1:=V293_target_fixture_abs)(o2:=emp).
     * apply RCbig_saved_join.
     * apply map_join_emp.
     * eapply good_fun_asrt_absop with(p:=(RCshared(RCsnapshot nc nest c)V293_idle_tid))(le:=emp).
       -- unfold RCshared;apply V293_exit_physical_pre_good;apply V293_witness_li_good.
       -- apply BLphysical_owned.
     * split;[apply V293_encoded_memory_mapsto|reflexivity].
   + apply BLrun_owned.
 - apply BLcaller_names. }
 clear -H;sep auto.
Qed.
Theorem RCbuilder_pre_nonempty : forall nc nest c value,RCbigstate nc nest c 1 value |= RCbuilderpre nc nest c.
Proof.
 intros nc nest c value;pose proof(RCbig_owned nc nest c 1 value)as Held.
 apply astar_l_adomlenv_intro with(d:=cons(120%Z,Tint32)nil)in Held;[ |exact BLdomain].
 assert(U:RCbigstate nc nest c 1 value |=
 (BLbindings ** (Agvarenv 112%Z Tint8(16%positive,0%Z) //\\ A_notin_lenv 112%Z)) **
 ((PV(15%positive,Int.zero)@Tint32|->value ** Alvarenv 120%Z Tint32(15%positive,0%Z)) **
 ((RCshared(RCsnapshot nc nest c)V293_idle_tid) ** (Amapsto(16%positive,0%Z)Tint8 false(V293_byteval 1) **
 V293_exit_builder_domain 120%Z)))).
 { unfold V293_exit_builder_domain,V293_guard_cell in *;clear -Held;sep auto. }
 eapply astar_mono in U.
 2:{ unfold BLbindings;apply V293_exit_builder_forget_names. }
 2:{ intros s0 H0;exact H0. }
 assert(Op:RCbigstate nc nest c 1 value |= <||spec_done None||> **
 (V293_exit_builder_globals 106%Z 107%Z 110%Z 111%Z 108%Z 109%Z 112%Z Tvoid 8%positive 10%positive 13%positive 14%positive 11%positive 12%positive 16%positive **
 ((PV(15%positive,Int.zero)@Tint32|->value ** Alvarenv 120%Z Tint32(15%positive,0%Z)) **
 ((RCshared(RCsnapshot nc nest c)V293_idle_tid) ** (Amapsto(16%positive,0%Z)Tint8 false(V293_byteval 1) **
 V293_exit_builder_domain 120%Z))))).
 { apply astar_l_aop'_intro;[exact U|reflexivity]. }
 unfold RCbuilderpre,V293_exit_builder_pre,V293_exit_builder_external_pre,
 V293_exit_builder_cells,Alvarmapsto,Alvarenv',Aptrmapsto;clear -Op;sep auto.
Qed.

(* Same heap, same names and same Spec: alter exactly one decoded field.
   These controls reach actual physical loads rather than decoder rejection. *)
Theorem RCentry_nonempty : forall nc nest c,nc<256 ->nest<256 ->
 RCbigstate nc nest c 1(Vint32 Int.zero) |=
 RCentF(V293_exit_encode(RCsnapshot nc nest c))V293_idle_tid(15%positive,Int.zero) ** Atrue.
Proof.
 intros nc nest c NC N.
 unfold RCentF;rewrite V293_exit_select_encoded by(repeat split;cbn;lia).
 assert(H:RCbigstate nc nest c 1(Vint32 Int.zero) |=
 <||spec_done None||> ** ((PV(15%positive,Int.zero)@Tint32|->Vint32 Int.zero **
 RCshared(RCsnapshot nc nest c)V293_idle_tid) ** Atrue)).
 { apply astar_l_aop'_intro;[ |reflexivity].
   pose proof(RCbig_owned nc nest c 1(Vint32 Int.zero))as Own;clear -Own;sep auto. }
 change(RCbigstate nc nest c 1(Vint32 Int.zero) |=
 (<||spec_done None||> ** (PV(15%positive,Int.zero)@Tint32|->Vint32 Int.zero **
 RCshared(RCsnapshot nc nest c)V293_idle_tid)) ** Atrue).
 clear -H;sep auto.
Qed.
Lemma RCentry_shared : forall nc nest c t address s,nc<256 ->nest<256 ->
 s |= RCentF(V293_exit_encode(RCsnapshot nc nest c))t address ** Atrue ->
 s |= RCshared(RCsnapshot nc nest c)t ** Atrue.
Proof.
 intros nc nest c t address s NC N H.
 unfold RCentF in H;rewrite V293_exit_select_encoded in H by(repeat split;cbn;lia).
 unfold RCentS,V293_exit_snapshot_entry,V293_saved_pointer_resource in H;unfold RCshared;clear -H;sep auto.
Qed.
Lemma RCshared_counter_load : forall x t s,
 s |= RCshared x t ** Atrue ->
 load Tint32(getmem s)(14%positive,0%Z)=Some(Vint32(V293_xcounter x)).
Proof.
 intros x t s H;unfold RCshared,V293_exit_snapshot_pre,V293_exit_physical_pre in H.
 eapply V293_star_load_l;[ |exact H]. intros s1 H1.
 eapply V293_star_load_r;[ |exact H1]. intros s2 H2.
 eapply V293_star_load_r;[ |exact H2]. intros s3 H3.
 eapply V293_star_load_r;[ |exact H3]. intros s4[M _].
 eapply mapstoval_load;[reflexivity|exact M].
Qed.
Lemma RCshared_nest_load : forall x t s,V293_xnest x<256 ->
 s |= RCshared x t ** Atrue ->
 load Tint8(getmem s)(11%positive,0%Z)=Some(V293_byteval(V293_xnest x)).
Proof.
 intros x t s N H.
 unfold RCshared,V293_exit_snapshot_pre,V293_exit_physical_pre,V293_exit_cells,V293_interrupt_cells in H.
 cbn[V293_rdy_raw_cells]in H.
 eapply V293_star_load_l;[ |exact H]. intros s1 H1.
 eapply V293_star_load_r;[ |exact H1]. intros s2 H2.
 eapply V293_star_load_l;[ |exact H2]. intros s3 H3.
 eapply V293_star_load_r;[ |exact H3]. intros s4 H4.
 eapply V293_star_load_r;[ |exact H4]. intros s5 H5.
 eapply V293_star_load_l;[ |exact H5]. intros s6[M _].
 eapply mapstoval_load;[apply V293_byte_type;exact N|exact M].
Qed.

Theorem RCcounter_control :
 (RCbigstate 12 1 Int.one 1(Vint32 Int.zero) |=
 RCentF(V293_exit_encode(RCsnapshot 12 1 Int.one))V293_idle_tid(15%positive,Int.zero) ** Atrue) /\
 ~(RCbigstate 12 1 Int.one 1(Vint32 Int.zero) |=
 RCentF(V293_exit_encode(RCsnapshot 12 1 Int.zero))V293_idle_tid(15%positive,Int.zero) ** Atrue).
Proof.
 split;[apply RCentry_nonempty;lia|intro H].
 pose proof(RCentry_shared 12 1 Int.zero V293_idle_tid (15%positive,Int.zero) _ ltac:(lia)ltac:(lia)H)as Wrong.
 pose proof(RCentry_shared 12 1 Int.one V293_idle_tid (15%positive,Int.zero) _ ltac:(lia)ltac:(lia)
 (RCentry_nonempty 12 1 Int.one ltac:(lia)ltac:(lia)))as Actual.
 pose proof(RCshared_counter_load _ _ _ Wrong)as W.
 pose proof(RCshared_counter_load _ _ _ Actual)as A.
 rewrite A in W;discriminate.
Qed.
Theorem RCnest_control :
 (RCbigstate 12 1 Int.zero 1(Vint32 Int.zero) |=
 RCentF(V293_exit_encode(RCsnapshot 12 1 Int.zero))V293_idle_tid(15%positive,Int.zero) ** Atrue) /\
 ~(RCbigstate 12 1 Int.zero 1(Vint32 Int.zero) |=
 RCentF(V293_exit_encode(RCsnapshot 12 2 Int.zero))V293_idle_tid(15%positive,Int.zero) ** Atrue).
Proof.
 split;[apply RCentry_nonempty;lia|intro H].
 pose proof(RCentry_shared 12 2 Int.zero V293_idle_tid (15%positive,Int.zero) _ ltac:(lia)ltac:(lia)H)as Wrong.
 pose proof(RCentry_shared 12 1 Int.zero V293_idle_tid (15%positive,Int.zero) _ ltac:(lia)ltac:(lia)
 (RCentry_nonempty 12 1 Int.zero ltac:(lia)ltac:(lia)))as Actual.
 pose proof(RCshared_nest_load (RCsnapshot 12 2 Int.zero) V293_idle_tid _ ltac:(cbn;lia)Wrong)as W.
 pose proof(RCshared_nest_load (RCsnapshot 12 1 Int.zero) V293_idle_tid _ ltac:(cbn;lia)Actual)as A.
 rewrite A in W;discriminate.
Qed.
Theorem RCcounter_frame : forall nc nest c1 c2 run value b i,b<>14%positive ->
 get(RCbigmemory nc nest c1 run value)(b,i)=get(RCbigmemory nc nest c2 run value)(b,i).
Proof.
 intros;unfold RCbigmemory,RCbigjoined,BLmemory,BLextra,V293_change_extra,V293_counter_memory;
 repeat rewrite map_merge_semp by reflexivity;
 repeat rewrite V293_encoded_memory_outside by(left;assumption);reflexivity.
Qed.
Theorem RCnest_frame : forall nc n1 n2 c run value b i,b<>11%positive ->
 get(RCbigmemory nc n1 c run value)(b,i)=get(RCbigmemory nc n2 c run value)(b,i).
Proof.
 intros;unfold RCbigmemory,RCbigjoined,BLmemory,BLextra,BLbyte;
 repeat rewrite map_merge_semp by reflexivity;
 repeat rewrite (V293_encoded_memory_outside _ 11%positive) by(left;assumption);reflexivity.
Qed.
