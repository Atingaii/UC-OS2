(* Independent physical witness construction; snapshots are not execution traces. *)
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitResourceBridge.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedGuardsWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPrefixWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitDispatch.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterInternal.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChangeWitness.
Require Import CertiOS.certiucos.v293.code.V293OSIntExit.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.code.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Import ListNotations.
Local Open Scope nat_scope.
Definition RBge := V293_change_fixture_ge.
Definition RBnames : asrt :=
 (Agvarenv 108%Z Tint8(11%positive,0%Z) //\\ A_notin_lenv 108%Z) **
 (Agvarenv 109%Z Tint8(12%positive,0%Z) //\\ A_notin_lenv 109%Z).
Definition RBbyte b n := V293_encoded_memory b 0 true(encode_val Tint8(V293_byteval n)).
Definition RBinternal hv := merge(merge V293_witness_inputs V293_witness_current)(RBbyte 4%positive hv).
Definition RBcaller out := merge V293_target_fixture_table
 (V293_encoded_memory 10%positive 0 true(encode_val(Tptr Tvoid)out)).
Definition RBbase hv out := merge(RBinternal hv)(RBcaller out).
Definition RBextra nest locked nc c := merge(RBbyte 11%positive nest)
 (merge(RBbyte 12%positive locked)(V293_change_extra nc c)).
Definition RBmemory hv out nest locked nc c := merge(RBbase hv out)(RBextra nest locked nc c).
Definition RBstate M := V293_target_wstate RBge emp M V293_target_fixture_abs.
Definition RBpre nc nest locked out c := V293_exit_ready_pre
 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive 0 16
 V293_witness_li V293_idle_tid(spec_done None)106%Z 107%Z Tvoid 8%positive 10%positive
 V293_idle_entries V293_idle_tasks 110%Z 111%Z 13%positive 14%positive 11%positive 12%positive
 nc RBnames nest locked out c.
Definition RBtail nc nest locked c := V293_OSSched_tail_state
 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive 0 16
 V293_witness_li V293_idle_tid(spec_done None)106%Z 107%Z Tvoid 8%positive 10%positive
 V293_idle_entries V293_idle_tasks 110%Z 111%Z 13%positive 14%positive nc
 (V293_rdy_raw_cells(V293_exit_cells 11%positive 12%positive nest locked)RBnames)c.
Ltac RBoutside :=
 unfold RBbase,RBinternal,RBcaller,RBextra,V293_change_extra,V293_guard_memory,V293_counter_memory,RBbyte;
 repeat first[rewrite map_merge_semp by reflexivity|
 rewrite V293_encoded_memory_outside by(left;congruence)];
 V293_prefix_outside.
Ltac RBjoin k := apply map_join_merge;apply map_disjoint;intros[b i];
 destruct(Pos.eq_dec b k);[subst b| ];
 first[solve[left;RBoutside]|solve[right;left;RBoutside]].
Lemma RBnames_owned : V293_wstate RBge emp emp |= RBnames.
Proof.
 unfold RBnames. eapply V293_wstate_star with(m1:=emp)(m2:=emp);[apply map_join_emp| | ];
 split;[eexists;split;[vm_compute;reflexivity|repeat split;reflexivity]|
 split;[intros[v H];discriminate|split;reflexivity]|
 eexists;split;[vm_compute;reflexivity|repeat split;reflexivity]|
 split;[intros[v H];discriminate|split;reflexivity]].
Qed.
Lemma RBenv : forall st,st |= RBnames ->
 V293_interrupt_env 108%Z 109%Z 11%positive 12%positive(getgenv st)(getlenv st).
Proof.
 intros st Hs.
 assert(EN: get(getgenv st)108%Z=Some(11%positive,Tint8) /\ get(getlenv st)108%Z=None).
 { eapply V293_star_env_l;[ |exact Hs]. intros s[G [N _]].
   apply agvarenv_elim in G. split;[exact(proj2(proj1 G))| ].
   destruct(get(getlenv s)108%Z)as[v| ]eqn:E;[exfalso;apply N;exists v;exact E|reflexivity]. }
 assert(EL: get(getgenv st)109%Z=Some(12%positive,Tint8) /\ get(getlenv st)109%Z=None).
 { eapply V293_star_env_r;[ |exact Hs]. intros s[G [N _]].
   apply agvarenv_elim in G. split;[exact(proj2(proj1 G))| ].
   destruct(get(getlenv s)109%Z)as[v| ]eqn:E;[exfalso;apply N;exists v;exact E|reflexivity]. }
 unfold V293_interrupt_env;tauto.
Qed.
Lemma RBinternal_owned : forall hv,
 V293_wstate RBge emp(RBinternal hv) |=
 <||spec_done None||> ** V293_sched_internal_resource
 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive 0 16
 V293_witness_li V293_idle_tid(V293_byteval hv).
Proof.
 intro hv. apply astar_l_aop'_intro;[ |reflexivity].
 unfold V293_sched_internal_resource.
 eapply V293_wstate_star;[RBjoin 4%positive| | ].
 - eapply V293_wstate_star;[RBjoin 6%positive| | ].
   + eapply V293_wstate_star with(m1:=emp)(m2:=V293_witness_inputs).
     * apply map_join_comm;apply map_join_emp.
     * apply V293_prefix_fixture_globals;vm_compute;reflexivity.
     * apply V293_prefix_fixture_inputs.
   + apply astar_comm. apply astar_l_aie_intro;[ |reflexivity].
     apply V293_prefix_fixture_current;vm_compute;reflexivity.
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Lemma RBcaller_owned : forall out,
 V293_target_wstate RBge emp(RBcaller out)V293_target_fixture_abs |=
 V293_prefix_frame 106%Z 103%Z 107%Z Tvoid 8%positive 10%positive V293_idle_entries V293_idle_tasks Aemp **
 V293_prefix_output Tvoid 10%positive out.
Proof.
 intro out. unfold RBcaller.
 eapply V293_target_wstate_star;[RBjoin 8%positive|apply map_join_emp| | ].
 - apply astar_r_aemp_intro.
   eapply V293_target_wstate_star with(m1:=emp)(m2:=V293_target_fixture_table)
    (o1:=emp)(o2:=V293_target_fixture_abs).
   + apply map_join_comm;apply map_join_emp.
   + apply map_join_comm;apply map_join_emp.
   + unfold V293_prefix_bindings. repeat split.
     * eexists;split;[vm_compute;reflexivity|repeat split;reflexivity].
     * eexists;split;[vm_compute;reflexivity|repeat split;reflexivity].
     * intros[v H];discriminate.
     * intros[v H];discriminate.
     * intros[v H];discriminate.
   + eapply V293_target_wstate_star with(m1:=V293_target_fixture_table)(m2:=emp)
      (o1:=emp)(o2:=V293_target_fixture_abs).
     * apply map_join_emp.
     * apply map_join_comm;apply map_join_emp.
     * apply V293_read_pointers_witness.
     * split;reflexivity.
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Lemma RBextra_owned : forall nest locked nc c,
 V293_wstate RBge emp(RBextra nest locked nc c) |=
 V293_rdy_raw_cells(V293_exit_cells 11%positive 12%positive nest locked)RBnames **
 (V293_guard_cell 110%Z 13%positive nc ** V293_counter_cell 111%Z 14%positive c).
Proof.
 intros. unfold V293_exit_cells,V293_interrupt_cells;cbn[V293_rdy_raw_cells].
 assert(H:V293_wstate RBge emp(RBextra nest locked nc c) |=
  PV(11%positive,Int.zero)@Tint8|->(V293_byteval nest) **
  (PV(12%positive,Int.zero)@Tint8|->(V293_byteval locked) **
  (V293_guard_cell 110%Z 13%positive nc ** V293_counter_cell 111%Z 14%positive c))).
 { unfold RBextra. eapply V293_wstate_star;[RBjoin 11%positive| | ].
   - split;[apply V293_encoded_memory_mapsto|reflexivity].
   - eapply V293_wstate_star;[RBjoin 12%positive| | ].
     + split;[apply V293_encoded_memory_mapsto|reflexivity].
     + apply V293_change_extra_witness. }
 assert(H':V293_wstate RBge emp(RBextra nest locked nc c) |= RBnames **
  (PV(11%positive,Int.zero)@Tint8|->(V293_byteval nest) **
  (PV(12%positive,Int.zero)@Tint8|->(V293_byteval locked) **
  (V293_guard_cell 110%Z 13%positive nc ** V293_counter_cell 111%Z 14%positive c)))).
 { eapply V293_wstate_star with(m1:=emp)(m2:=RBextra nest locked nc c).
   - apply map_join_comm;apply map_join_emp.
   - apply RBnames_owned.
   - exact H. }
 clear H. sep auto.
Qed.
Lemma RBjoint_owned : forall hv out nest locked nc c,
 RBstate(RBmemory hv out nest locked nc c) |=
 ((<||spec_done None||> ** V293_sched_internal_resource
 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive 0 16
 V293_witness_li V293_idle_tid(V293_byteval hv)) **
 (V293_prefix_frame 106%Z 103%Z 107%Z Tvoid 8%positive 10%positive V293_idle_entries V293_idle_tasks Aemp **
 V293_prefix_output Tvoid 10%positive out)) **
 (V293_rdy_raw_cells(V293_exit_cells 11%positive 12%positive nest locked)RBnames **
 (V293_guard_cell 110%Z 13%positive nc ** V293_counter_cell 111%Z 14%positive c)).
Proof.
 intros. eapply V293_target_wstate_star with(o1:=V293_target_fixture_abs)(o2:=emp).
 - apply map_join_merge;apply map_disjoint;intros[b i].
   destruct(Pos.eq_dec b 11%positive);[subst b;left;RBoutside| ].
   destruct(Pos.eq_dec b 12%positive);[subst b;left;RBoutside| ].
   destruct(Pos.eq_dec b 13%positive);[subst b;left;RBoutside| ].
   destruct(Pos.eq_dec b 14%positive);[subst b;left;RBoutside| ]. right;left;RBoutside.
 - apply map_join_emp.
 - eapply V293_target_wstate_star with(o1:=emp)(o2:=V293_target_fixture_abs).
   + apply map_join_merge;apply map_disjoint;intros[b i].
     destruct(Pos.eq_dec b 8%positive);[subst b;left;RBoutside| ].
     destruct(Pos.eq_dec b 10%positive);[subst b;left;RBoutside| ]. right;left;RBoutside.
   + apply map_join_comm;apply map_join_emp.
   + apply RBinternal_owned.
   + apply RBcaller_owned.
 - apply RBextra_owned.
Qed.
Theorem RBnonempty : forall hv out nest locked nc c,
 RBstate(RBmemory hv out nest locked nc c) |= RBpre nc nest locked out c.
Proof.
 intros. pose proof(RBjoint_owned hv out nest locked nc c)as Hs.
 unfold RBpre,V293_exit_ready_pre,V293_sched_internal_pre. sep normal. exists(V293_byteval hv).
 assert(B:0<256 /\ 16<256 /\ exists p,V293_bitmap_ready 0 16 p).
 { split;[lia| ]. split;[lia| ]. exists 12;vm_compute;intuition lia. }
 unfold V293_prefix_frame in *;sep auto;assumption.
Qed.
Theorem RBtail_nonempty : forall nest locked nc c,
 RBstate(RBmemory 12(Vptr V293_idle_tid)nest locked nc c) |= RBtail nc nest locked c.
Proof.
 intros. pose proof(RBjoint_owned 12(Vptr V293_idle_tid)nest locked nc c)as Hs.
 unfold RBtail,V293_OSSched_tail_state. exists V293_idle_tid.
 unfold V293_sched_internal_post,V293_prefix_frame in *. sep auto.
 - split;[reflexivity| ].
   exact(proj2(V293_ready_selection 0 16(V293_ready_group 0 16)ltac:(lia)ltac:(lia)eq_refl
    ltac:(exists 12;vm_compute;intuition lia))).
 - unfold V293_highest_ready. exists (Int.repr 12). exists Vnull.
   split;[apply map_get_sig| ]. intros t p msg G. unfold V293_idle_tasks in G.
   destruct(tid_eq_dec V293_idle_tid t)as[E|E].
   + subst t;rewrite map_get_sig in G;inversion G;subst;lia.
   + rewrite map_get_sig' in G by exact E;discriminate.
Qed.

Definition RBphysical nc nest locked out c := V293_exit_physical_pre
 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive 0 16
 V293_witness_li V293_idle_tid(spec_done None)Tvoid 8%positive 10%positive
 V293_idle_entries V293_idle_tasks 13%positive 14%positive 11%positive 12%positive
 nc nest locked out c.
Definition RBphysicaltail nc nest locked c := V293_exit_physical_tail
 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive 0 16
 V293_witness_li V293_idle_tid(spec_done None)Tvoid 8%positive 10%positive
 V293_idle_entries V293_idle_tasks 13%positive 14%positive 11%positive 12%positive
 nc nest locked c.
Definition RBbindings := V293_exit_caller_bindings 103%Z 106%Z 107%Z Tvoid 8%positive 10%positive
 110%Z 111%Z 108%Z 109%Z 13%positive 14%positive 11%positive 12%positive.
Lemma RBbindings_empty : RBbindings ==> Aemp.
Proof.
 assert(S:forall p q,(p ==> Aemp)->(q ==> Aemp)->p ** q ==> Aemp).
 { intros p q P Q s H. apply astar_l_aemp_elim.
   eapply astar_mono;[exact P|exact Q|exact H]. }
 unfold RBbindings,V293_exit_caller_bindings,V293_prefix_bindings,V293_counter_bindings,V293_exit_guard_bindings.
 repeat apply S;intros s H;destruct H as[G _];
 apply agvarenv_elim in G;exact(proj2 G).
Qed.
Lemma RBphysical_owned : forall hv out nest locked nc c,
 RBstate(RBmemory hv out nest locked nc c) |= RBphysical nc nest locked out c.
Proof.
 intros. pose proof(RBnonempty hv out nest locked nc c)as H.
 assert(H':RBstate(RBmemory hv out nest locked nc c) |= RBphysical nc nest locked out c ** (RBbindings ** Aemp)).
 { apply V293_exit_pre_split. unfold RBpre in H.
   unfold V293_exit_ready_pre,V293_prefix_frame,V293_exit_cells,V293_interrupt_cells in *.
   cbn[V293_rdy_raw_cells]in *;unfold RBnames,V293_exit_guard_bindings in *;sep auto. }
 apply astar_r_aemp_elim. eapply astar_mono;[intros st Hs;exact Hs| |exact H'].
 intros st Hs. apply astar_r_aemp_elim in Hs. apply RBbindings_empty;exact Hs.
Qed.
Lemma RBphysicaltail_owned : forall nest locked nc c,
 RBstate(RBmemory 12(Vptr V293_idle_tid)nest locked nc c) |= RBphysicaltail nc nest locked c.
Proof.
 intros. pose proof(RBtail_nonempty nest locked nc c)as H.
 assert(H':RBstate(RBmemory 12(Vptr V293_idle_tid)nest locked nc c) |= RBphysicaltail nc nest locked c ** (RBbindings ** Aemp)).
 { apply V293_exit_tail_split. unfold RBtail in H.
   unfold V293_OSSched_tail_state,V293_prefix_frame,V293_exit_cells,V293_interrupt_cells in *.
   cbn[V293_rdy_raw_cells]in *;unfold RBnames,V293_exit_guard_bindings in *.
   destruct H as[t H]. exists t;sep auto. }
 apply astar_r_aemp_elim. eapply astar_mono;[intros st Hs;exact Hs| |exact H'].
 intros st Hs. apply astar_r_aemp_elim in Hs. apply RBbindings_empty;exact Hs.
Qed.
Definition RBle (shadow:bool) : env := if shadow then
 set(sig 120%Z(15%positive,Tint32))108%Z(11%positive,Tint8)
 else sig 120%Z(15%positive,Tint32).
Definition RBlestate le M := V293_target_wstate RBge le M V293_target_fixture_abs.
Definition RBsaved := V293_encoded_memory 15%positive 0 true(encode_val Tint32(Vint32 Int.one)).
Definition RBfullmemory hv out nest locked nc c := merge(RBmemory hv out nest locked nc c)RBsaved.
Definition RBacquired nc nest locked out c := RBphysical nc nest locked out c **
 PV(15%positive,Int.zero)@Tint32|->Vint32 Int.one.
Definition RBtailresource nc nest locked c := RBphysicaltail nc nest locked c **
 PV(15%positive,Int.zero)@Tint32|->Vint32 Int.one.
Definition RBcaller_assert := Alvarenv 120%Z Tint32(15%positive,0%Z) ** (RBbindings ** Aemp).
Lemma RBsaved_join : forall hv out nest locked nc c,
 join(RBmemory hv out nest locked nc c)RBsaved(RBfullmemory hv out nest locked nc c).
Proof.
 intros. apply map_join_merge;apply map_disjoint;intros[b i].
 destruct(Pos.eq_dec b 15%positive);[subst b;left;unfold RBmemory;RBoutside| ].
 right;left;unfold RBsaved;apply V293_encoded_memory_outside;left;exact n.
Qed.
Lemma RBacquired_owned : forall le hv out nest locked nc c,
 RBlestate le(RBfullmemory hv out nest locked nc c) |= RBacquired nc nest locked out c.
Proof.
 intros. unfold RBacquired. eapply V293_target_wstate_star with
 (o1:=V293_target_fixture_abs)(o2:=emp).
 - apply RBsaved_join.
 - apply map_join_emp.
 - eapply good_fun_asrt_absop with(p:=RBphysical nc nest locked out c)(le:=emp).
   + unfold RBphysical;apply V293_exit_physical_pre_good;apply V293_witness_li_good.
   + apply RBphysical_owned.
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Lemma RBtailresource_owned : forall le nest locked nc c,
 RBlestate le(RBfullmemory 12(Vptr V293_idle_tid)nest locked nc c) |= RBtailresource nc nest locked c.
Proof.
 intros. unfold RBtailresource. eapply V293_target_wstate_star with
 (o1:=V293_target_fixture_abs)(o2:=emp).
 - apply RBsaved_join.
 - apply map_join_emp.
 - eapply good_fun_asrt_absop with(p:=RBphysicaltail nc nest locked c)(le:=emp).
   + unfold RBphysicaltail;apply V293_exit_physical_tail_good;apply V293_witness_li_good.
   + apply RBphysicaltail_owned.
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Lemma RBcaller_assert_owned_new : V293_wstate RBge(RBle false)emp |= RBcaller_assert.
Proof.
 unfold RBcaller_assert,RBbindings,V293_exit_caller_bindings,V293_prefix_bindings,V293_counter_bindings,V293_exit_guard_bindings.
 repeat(eapply V293_wstate_star with(m1:=emp)(m2:=emp);[apply map_join_emp| | ]).
 all:repeat split;try(intros[v H];vm_compute in H;discriminate);
 try(eexists;split;[vm_compute;reflexivity|repeat split;reflexivity]);try reflexivity.
Qed.
Theorem RBcomplete_acquired_nonempty : forall hv out nest locked nc c,
 RBlestate(RBle false)(RBfullmemory hv out nest locked nc c) |= RBacquired nc nest locked out c ** RBcaller_assert.
Proof.
 intros. eapply V293_target_wstate_star with
 (m1:=RBfullmemory hv out nest locked nc c)(m2:=emp)
 (o1:=V293_target_fixture_abs)(o2:=emp);try apply map_join_emp.
 - apply RBacquired_owned.
 - apply RBcaller_assert_owned_new.
Qed.
Theorem RBcomplete_tail_nonempty : forall nest locked nc c,
 RBlestate(RBle false)(RBfullmemory 12(Vptr V293_idle_tid)nest locked nc c) |= RBtailresource nc nest locked c ** RBcaller_assert.
Proof.
 intros. eapply V293_target_wstate_star with
 (m1:=RBfullmemory 12(Vptr V293_idle_tid)nest locked nc c)(m2:=emp)
 (o1:=V293_target_fixture_abs)(o2:=emp);try apply map_join_emp.
 - apply RBtailresource_owned.
 - apply RBcaller_assert_owned_new.
Qed.
Theorem RBshadow_control :
 (RBlestate(RBle false)(RBfullmemory 0 Vnull 1 0 0 Int.zero) |= RBacquired 0 1 0 Vnull Int.zero ** RBcaller_assert) /\
 (RBlestate(RBle true)(RBfullmemory 0 Vnull 1 0 0 Int.zero) |= RBacquired 0 1 0 Vnull Int.zero) /\
 ~(RBlestate(RBle true)(RBfullmemory 0 Vnull 1 0 0 Int.zero) |= RBacquired 0 1 0 Vnull Int.zero ** RBcaller_assert).
Proof.
 split;[apply RBcomplete_acquired_nonempty| ]. split;[apply RBacquired_owned| ]. intro H.
 assert(E:get(getlenv(RBlestate(RBle true)(RBfullmemory 0 Vnull 1 0 0 Int.zero)))108%Z=None).
 { eapply V293_star_env_r with(E:=fun _ le=>get le 108%Z=None);[ |exact H]. unfold RBcaller_assert.
   apply V293_star_env_r with(E:=fun _ le=>get le 108%Z=None). apply V293_star_env_l with(E:=fun _ le=>get le 108%Z=None).
   unfold RBbindings,V293_exit_caller_bindings.
   apply V293_star_env_r with(E:=fun _ le=>get le 108%Z=None). apply V293_star_env_r with(E:=fun _ le=>get le 108%Z=None). apply V293_star_env_r with(E:=fun _ le=>get le 108%Z=None).
   intros st Hs. exact(proj1(V293_exit_guard_bindings_env _ _ _ _ _ Hs)). }
 vm_compute in E;discriminate.
Qed.
Lemma RBcounter_load : forall nc nest locked out c s,
 s |= RBacquired nc nest locked out c ** RBcaller_assert ->
 load Tint32(getmem s)(14%positive,0%Z)=Some(Vint32 c).
Proof.
 intros nc nest locked out c s H.
 assert(P:s |= PV(14%positive,Int.zero)@Tint32|->Vint32 c ** Atrue).
 { unfold RBacquired,RBphysical,V293_exit_physical_pre in H;sep auto. }
 eapply V293_star_load_l;[ |exact P]. intros st[M _].
 eapply mapstoval_load;[reflexivity|exact M].
Qed.
Theorem RBcounter_control :
 (RBlestate(RBle false)(RBfullmemory 0 Vnull 1 0 0 Int.zero) |= RBacquired 0 1 0 Vnull Int.zero ** RBcaller_assert) /\
 (RBlestate(RBle false)(RBfullmemory 0 Vnull 1 0 0 Int.one) |= RBacquired 0 1 0 Vnull Int.one ** RBcaller_assert) /\
 ~(RBlestate(RBle false)(RBfullmemory 0 Vnull 1 0 0 Int.one) |= RBacquired 0 1 0 Vnull Int.zero ** RBcaller_assert).
Proof.
 split;[apply RBcomplete_acquired_nonempty| ]. split;[apply RBcomplete_acquired_nonempty| ]. intro H.
 pose proof(RBcounter_load _ _ _ _ _ _ H)as Wrong.
 pose proof(RBcounter_load _ _ _ _ _ _(RBcomplete_acquired_nonempty 0 Vnull 1 0 0 Int.one))as Actual.
 rewrite Actual in Wrong;vm_compute in Wrong;discriminate.
Qed.
Theorem RBcounter_frame : forall hv out nest locked nc c1 c2 b i,b<>14%positive ->
 get(RBfullmemory hv out nest locked nc c1)(b,i)=get(RBfullmemory hv out nest locked nc c2)(b,i).
Proof.
 intros. unfold RBfullmemory,RBmemory,RBextra,V293_change_extra,V293_counter_memory.
 repeat rewrite map_merge_semp by reflexivity.
 repeat rewrite V293_encoded_memory_outside by(left;assumption). reflexivity.
Qed.
(* Lookup removal is a contract-input check only. *)
Theorem RBlookup_ablation : forall (Spec:fid->option(fpre*fpost*(type*list type))) callee pre post signature,
 Spec callee=Some(pre,post,signature) ->
 (fun f=>if Z.eq_dec f callee then None else Spec f)callee<>Some(pre,post,signature).
Proof.
 intros Spec callee pre post signature H.
 change((if Z.eq_dec callee callee then None else Spec callee)<>Some(pre,post,signature)).
 destruct(Z.eq_dec callee callee);[discriminate|contradiction].
Qed.
