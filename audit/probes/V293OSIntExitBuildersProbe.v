(* Independent physical witness construction; snapshots are not execution traces. *)
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitResourceBridge.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBody.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitCriticalCalls.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.
Require Import CertiOS.certiucos.v293.code.V293OSIntEnter.
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
Definition BLge := set V293_change_fixture_ge 112%Z(16%positive,Tint8).
Definition BLnames : asrt :=
 (Agvarenv 108%Z Tint8(11%positive,0%Z) //\\ A_notin_lenv 108%Z) **
 (Agvarenv 109%Z Tint8(12%positive,0%Z) //\\ A_notin_lenv 109%Z).
Definition BLbyte b n := V293_encoded_memory b 0 true(encode_val Tint8(V293_byteval n)).
Definition BLinternal hv := merge(merge V293_witness_inputs V293_witness_current)(BLbyte 4%positive hv).
Definition BLcaller out := merge V293_target_fixture_table
 (V293_encoded_memory 10%positive 0 true(encode_val(Tptr Tvoid)out)).
Definition BLbase hv out := merge(BLinternal hv)(BLcaller out).
Definition BLextra nest locked nc c := merge(BLbyte 11%positive nest)
 (merge(BLbyte 12%positive locked)(V293_change_extra nc c)).
Definition BLmemory hv out nest locked nc c := merge(BLbase hv out)(BLextra nest locked nc c).
Definition BLstate M := V293_target_wstate BLge emp M V293_target_fixture_abs.
Definition BLpre nc nest locked out c := V293_exit_ready_pre
 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive 0 16
 V293_witness_li V293_idle_tid(spec_done None)106%Z 107%Z Tvoid 8%positive 10%positive
 V293_idle_entries V293_idle_tasks 110%Z 111%Z 13%positive 14%positive 11%positive 12%positive
 nc BLnames nest locked out c.
Ltac BLoutside :=
 unfold BLbase,BLinternal,BLcaller,BLextra,V293_change_extra,V293_guard_memory,V293_counter_memory,BLbyte;
 repeat first[rewrite map_merge_semp by reflexivity|
 rewrite V293_encoded_memory_outside by(left;congruence)];
 V293_prefix_outside.
Ltac BLjoin k := apply map_join_merge;apply map_disjoint;intros[b i];
 destruct(Pos.eq_dec b k);[subst b| ];
 first[solve[left;BLoutside]|solve[right;left;BLoutside]].
Lemma BLnames_owned : V293_wstate BLge emp emp |= BLnames.
Proof.
 unfold BLnames. eapply V293_wstate_star with(m1:=emp)(m2:=emp);[apply map_join_emp| | ];
 split;[eexists;split;[vm_compute;reflexivity|repeat split;reflexivity]|
 split;[intros[v H];discriminate|split;reflexivity]|
 eexists;split;[vm_compute;reflexivity|repeat split;reflexivity]|
 split;[intros[v H];discriminate|split;reflexivity]].
Qed.
Lemma BLenv : forall st,st |= BLnames ->
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
Lemma BLinternal_owned : forall hv,
 V293_wstate BLge emp(BLinternal hv) |=
 <||spec_done None||> ** V293_sched_internal_resource
 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive 0 16
 V293_witness_li V293_idle_tid(V293_byteval hv).
Proof.
 intro hv. apply astar_l_aop'_intro;[ |reflexivity].
 unfold V293_sched_internal_resource.
 eapply V293_wstate_star;[BLjoin 4%positive| | ].
 - eapply V293_wstate_star;[BLjoin 6%positive| | ].
   + eapply V293_wstate_star with(m1:=emp)(m2:=V293_witness_inputs).
     * apply map_join_comm;apply map_join_emp.
     * apply V293_prefix_fixture_globals;vm_compute;reflexivity.
     * apply V293_prefix_fixture_inputs.
   + apply astar_comm. apply astar_l_aie_intro;[ |reflexivity].
     apply V293_prefix_fixture_current;vm_compute;reflexivity.
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Lemma BLcaller_owned : forall out,
 V293_target_wstate BLge emp(BLcaller out)V293_target_fixture_abs |=
 V293_prefix_frame 106%Z 103%Z 107%Z Tvoid 8%positive 10%positive V293_idle_entries V293_idle_tasks Aemp **
 V293_prefix_output Tvoid 10%positive out.
Proof.
 intro out. unfold BLcaller.
 eapply V293_target_wstate_star;[BLjoin 8%positive|apply map_join_emp| | ].
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
Lemma BLextra_owned : forall nest locked nc c,
 V293_wstate BLge emp(BLextra nest locked nc c) |=
 V293_rdy_raw_cells(V293_exit_cells 11%positive 12%positive nest locked)BLnames **
 (V293_guard_cell 110%Z 13%positive nc ** V293_counter_cell 111%Z 14%positive c).
Proof.
 intros. unfold V293_exit_cells,V293_interrupt_cells;cbn[V293_rdy_raw_cells].
 assert(H:V293_wstate BLge emp(BLextra nest locked nc c) |=
  PV(11%positive,Int.zero)@Tint8|->(V293_byteval nest) **
  (PV(12%positive,Int.zero)@Tint8|->(V293_byteval locked) **
  (V293_guard_cell 110%Z 13%positive nc ** V293_counter_cell 111%Z 14%positive c))).
 { unfold BLextra. eapply V293_wstate_star;[BLjoin 11%positive| | ].
   - split;[apply V293_encoded_memory_mapsto|reflexivity].
   - eapply V293_wstate_star;[BLjoin 12%positive| | ].
     + split;[apply V293_encoded_memory_mapsto|reflexivity].
     + unfold V293_change_extra. eapply V293_wstate_star.
       * apply map_join_merge. apply map_disjoint. intros[b i].
         destruct(Pos.eq_dec b 13%positive);[subst b;right;left|left];
         apply V293_encoded_memory_outside;left;congruence.
       * apply V293_guard_cell_witness;vm_compute;reflexivity.
       * apply V293_counter_cell_witness;vm_compute;reflexivity. }
 assert(H':V293_wstate BLge emp(BLextra nest locked nc c) |= BLnames **
  (PV(11%positive,Int.zero)@Tint8|->(V293_byteval nest) **
  (PV(12%positive,Int.zero)@Tint8|->(V293_byteval locked) **
  (V293_guard_cell 110%Z 13%positive nc ** V293_counter_cell 111%Z 14%positive c)))).
 { eapply V293_wstate_star with(m1:=emp)(m2:=BLextra nest locked nc c).
   - apply map_join_comm;apply map_join_emp.
   - apply BLnames_owned.
   - exact H. }
 clear H. sep auto.
Qed.
Lemma BLjoint_owned : forall hv out nest locked nc c,
 BLstate(BLmemory hv out nest locked nc c) |=
 ((<||spec_done None||> ** V293_sched_internal_resource
 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive 0 16
 V293_witness_li V293_idle_tid(V293_byteval hv)) **
 (V293_prefix_frame 106%Z 103%Z 107%Z Tvoid 8%positive 10%positive V293_idle_entries V293_idle_tasks Aemp **
 V293_prefix_output Tvoid 10%positive out)) **
 (V293_rdy_raw_cells(V293_exit_cells 11%positive 12%positive nest locked)BLnames **
 (V293_guard_cell 110%Z 13%positive nc ** V293_counter_cell 111%Z 14%positive c)).
Proof.
 intros. eapply V293_target_wstate_star with(o1:=V293_target_fixture_abs)(o2:=emp).
 - apply map_join_merge;apply map_disjoint;intros[b i].
   destruct(Pos.eq_dec b 11%positive);[subst b;left;BLoutside| ].
   destruct(Pos.eq_dec b 12%positive);[subst b;left;BLoutside| ].
   destruct(Pos.eq_dec b 13%positive);[subst b;left;BLoutside| ].
   destruct(Pos.eq_dec b 14%positive);[subst b;left;BLoutside| ]. right;left;BLoutside.
 - apply map_join_emp.
 - eapply V293_target_wstate_star with(o1:=emp)(o2:=V293_target_fixture_abs).
   + apply map_join_merge;apply map_disjoint;intros[b i].
     destruct(Pos.eq_dec b 8%positive);[subst b;left;BLoutside| ].
     destruct(Pos.eq_dec b 10%positive);[subst b;left;BLoutside| ]. right;left;BLoutside.
   + apply map_join_comm;apply map_join_emp.
   + apply BLinternal_owned.
   + apply BLcaller_owned.
 - apply BLextra_owned.
Qed.
Theorem BLnonempty : forall hv out nest locked nc c,
 BLstate(BLmemory hv out nest locked nc c) |= BLpre nc nest locked out c.
Proof.
 intros. pose proof(BLjoint_owned hv out nest locked nc c)as Hs.
 unfold BLpre,V293_exit_ready_pre,V293_sched_internal_pre. sep normal. exists(V293_byteval hv).
 assert(B:0<256 /\ 16<256 /\ exists p,V293_bitmap_ready 0 16 p).
 { split;[lia| ]. split;[lia| ]. exists 12;vm_compute;intuition lia. }
 unfold V293_prefix_frame in *;sep auto;assumption.
Qed.

Definition BLphysical nc nest locked out c := V293_exit_physical_pre
 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive 0 16
 V293_witness_li V293_idle_tid(spec_done None)Tvoid 8%positive 10%positive
 V293_idle_entries V293_idle_tasks 13%positive 14%positive 11%positive 12%positive
 nc nest locked out c.
Definition BLbindings := V293_exit_caller_bindings 103%Z 106%Z 107%Z Tvoid 8%positive 10%positive
 110%Z 111%Z 108%Z 109%Z 13%positive 14%positive 11%positive 12%positive.
Lemma BLbindings_empty : BLbindings ==> Aemp.
Proof.
 assert(S:forall p q,(p ==> Aemp)->(q ==> Aemp)->p ** q ==> Aemp).
 { intros p q P Q s H. apply astar_l_aemp_elim.
   eapply astar_mono;[exact P|exact Q|exact H]. }
 unfold BLbindings,V293_exit_caller_bindings,V293_prefix_bindings,V293_counter_bindings,V293_exit_guard_bindings.
 repeat apply S;intros s H;destruct H as[G _];
 apply agvarenv_elim in G;exact(proj2 G).
Qed.
Lemma BLphysical_owned : forall hv out nest locked nc c,
 BLstate(BLmemory hv out nest locked nc c) |= BLphysical nc nest locked out c.
Proof.
 intros. pose proof(BLnonempty hv out nest locked nc c)as H.
 assert(H':BLstate(BLmemory hv out nest locked nc c) |= BLphysical nc nest locked out c ** (BLbindings ** Aemp)).
 { apply V293_exit_pre_split. unfold BLpre in H.
   unfold V293_exit_ready_pre,V293_prefix_frame,V293_exit_cells,V293_interrupt_cells in *.
   cbn[V293_rdy_raw_cells]in *;unfold BLnames,V293_exit_guard_bindings in *;sep auto. }
 apply astar_r_aemp_elim. eapply astar_mono;[intros st Hs;exact Hs| |exact H'].
 intros st Hs. apply astar_r_aemp_elim in Hs. apply BLbindings_empty;exact Hs.
Qed.


Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBuilders.
Definition BLle : env := sig 120%Z(15%positive,Tint32).
Definition BLsaved value := V293_encoded_memory 15%positive 0 true(encode_val Tint32 value).
Definition BLrun run := V293_encoded_memory 16%positive 0 false(encode_val Tint8(V293_byteval run)).
Definition BLjoined value := merge(BLmemory 0 Vnull 1 0 0 Int.zero)(BLsaved value).
Definition BLfullmemory run value := merge(BLjoined value)(BLrun run).
Definition BLfullstate run value := V293_target_wstate BLge BLle(BLfullmemory run value)V293_target_fixture_abs.
Definition BLshared := BLphysical 0 1 0 Vnull Int.zero.
Definition BLframe run := V293_guard_cell 112%Z 16%positive run ** (BLbindings ** Aemp).
Definition BLfullpre run value := V293_exit_body_pre(spec_done None)BLshared 120%Z 15%positive value(BLframe run).
Definition BLfullat run := V293_exit_body_at(spec_done None)BLshared 120%Z 15%positive(BLframe run).

Lemma BLcaller_names : V293_wstate BLge BLle emp |=
 Alvarenv 120%Z Tint32(15%positive,0%Z) ** (BLbindings ** Aemp).
Proof.
 unfold BLbindings,V293_exit_caller_bindings,V293_prefix_bindings,V293_counter_bindings,V293_exit_guard_bindings.
 repeat(eapply V293_wstate_star with(m1:=emp)(m2:=emp);[apply map_join_emp| | ]).
 all:repeat split;try(intros[v H];vm_compute in H;discriminate);
 try(eexists;split;[vm_compute;reflexivity|repeat split;reflexivity]);try reflexivity.
Qed.
Lemma BLsaved_join : forall value,
 join(BLmemory 0 Vnull 1 0 0 Int.zero)(BLsaved value)(BLjoined value).
Proof.
 intro value. apply map_join_merge;apply map_disjoint;intros[b i].
 destruct(Pos.eq_dec b 15%positive);[subst b;left;unfold BLmemory;BLoutside| ].
 right;left;unfold BLsaved;apply V293_encoded_memory_outside;left;exact n.
Qed.
Lemma BLrun_join : forall run value,join(BLjoined value)(BLrun run)(BLfullmemory run value).
Proof.
 intros. apply map_join_merge;apply map_disjoint;intros[b i].
 destruct(Pos.eq_dec b 16%positive);[subst b;left|right;left;unfold BLrun;apply V293_encoded_memory_outside;left;exact n].
 unfold BLjoined,BLsaved,BLmemory;BLoutside.
Qed.
Lemma BLrun_owned : forall run,
 V293_wstate BLge BLle(BLrun run) |= V293_guard_cell 112%Z 16%positive run.
Proof.
 intro run. unfold V293_guard_cell. eapply V293_wstate_star with(m1:=emp)(m2:=BLrun run).
 - apply map_join_comm;apply map_join_emp.
 - split.
   + eexists;split;[vm_compute;reflexivity|repeat split;reflexivity].
   + split;[intros[v H];vm_compute in H;discriminate|split;reflexivity].
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Lemma BLfull_owned : forall run value, BLfullstate run value |=
 (BLshared ** PV(15%positive,Int.zero)@Tint32|->value) **
 (V293_guard_cell 112%Z 16%positive run **
  (Alvarenv 120%Z Tint32(15%positive,0%Z) ** (BLbindings ** Aemp))).
Proof.
 intros.
 assert(H:BLfullstate run value |=
  ((BLshared ** PV(15%positive,Int.zero)@Tint32|->value) **
   V293_guard_cell 112%Z 16%positive run) **
  (Alvarenv 120%Z Tint32(15%positive,0%Z) ** (BLbindings ** Aemp))).
 { unfold BLfullstate. eapply V293_target_wstate_star with
 (m1:=BLfullmemory run value)(m2:=emp)(o1:=V293_target_fixture_abs)(o2:=emp);try apply map_join_emp.
 - eapply V293_target_wstate_star with(m1:=BLjoined value)(m2:=BLrun run)
   (o1:=V293_target_fixture_abs)(o2:=emp).
   + apply BLrun_join.
   + apply map_join_emp.
   + eapply V293_target_wstate_star with(m1:=BLmemory 0 Vnull 1 0 0 Int.zero)(m2:=BLsaved value)
     (o1:=V293_target_fixture_abs)(o2:=emp).
     * apply BLsaved_join.
     * apply map_join_emp.
     * eapply good_fun_asrt_absop with(p:=BLshared)(le:=emp).
       -- unfold BLshared,BLphysical;apply V293_exit_physical_pre_good;apply V293_witness_li_good.
       -- apply BLphysical_owned.
     * split;[apply V293_encoded_memory_mapsto|reflexivity].
   + apply BLrun_owned.
 - apply BLcaller_names. }
 clear -H;sep auto.
Qed.
Definition BMle : env := sig 120%Z(17%positive,Tint32).
Definition BMsaved value := V293_encoded_memory 17%positive 0 true(encode_val Tint32 value).
Definition BMrun run := V293_encoded_memory 16%positive 0 false(encode_val Tint8(V293_byteval run)).
Definition BMjoined value := merge(BLmemory 0 Vnull 1 0 0 Int.zero)(BMsaved value).
Definition BMfullmemory run value := merge(BMjoined value)(BMrun run).
Definition BMfullstate run value := V293_target_wstate BLge BMle(BMfullmemory run value)V293_target_fixture_abs.
Definition BMframe run := V293_guard_cell 112%Z 16%positive run ** (BLbindings ** Aemp).
Definition BMfullpre run value := V293_exit_body_pre(spec_done None)BLshared 120%Z 17%positive value(BMframe run).
Definition BMfullat run := V293_exit_body_at(spec_done None)BLshared 120%Z 17%positive(BMframe run).

Lemma BMcaller_names : V293_wstate BLge BMle emp |=
 Alvarenv 120%Z Tint32(17%positive,0%Z) ** (BLbindings ** Aemp).
Proof.
 unfold BLbindings,V293_exit_caller_bindings,V293_prefix_bindings,V293_counter_bindings,V293_exit_guard_bindings.
 repeat(eapply V293_wstate_star with(m1:=emp)(m2:=emp);[apply map_join_emp| | ]).
 all:repeat split;try(intros[v H];vm_compute in H;discriminate);
 try(eexists;split;[vm_compute;reflexivity|repeat split;reflexivity]);try reflexivity.
Qed.
Lemma BMsaved_join : forall value,
 join(BLmemory 0 Vnull 1 0 0 Int.zero)(BMsaved value)(BMjoined value).
Proof.
 intro value. apply map_join_merge;apply map_disjoint;intros[b i].
 destruct(Pos.eq_dec b 17%positive);[subst b;left;unfold BLmemory;BLoutside| ].
 right;left;unfold BMsaved;apply V293_encoded_memory_outside;left;exact n.
Qed.
Lemma BMrun_join : forall run value,join(BMjoined value)(BMrun run)(BMfullmemory run value).
Proof.
 intros. apply map_join_merge;apply map_disjoint;intros[b i].
 destruct(Pos.eq_dec b 16%positive);[subst b;left|right;left;unfold BMrun;apply V293_encoded_memory_outside;left;exact n].
 unfold BMjoined,BMsaved,BLmemory;BLoutside.
Qed.
Lemma BMrun_owned : forall run,
 V293_wstate BLge BMle(BMrun run) |= V293_guard_cell 112%Z 16%positive run.
Proof.
 intro run. unfold V293_guard_cell. eapply V293_wstate_star with(m1:=emp)(m2:=BMrun run).
 - apply map_join_comm;apply map_join_emp.
 - split.
   + eexists;split;[vm_compute;reflexivity|repeat split;reflexivity].
   + split;[intros[v H];vm_compute in H;discriminate|split;reflexivity].
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Lemma BMfull_owned : forall run value, BMfullstate run value |=
 (BLshared ** PV(17%positive,Int.zero)@Tint32|->value) **
 (V293_guard_cell 112%Z 16%positive run **
  (Alvarenv 120%Z Tint32(17%positive,0%Z) ** (BLbindings ** Aemp))).
Proof.
 intros.
 assert(H:BMfullstate run value |=
  ((BLshared ** PV(17%positive,Int.zero)@Tint32|->value) **
   V293_guard_cell 112%Z 16%positive run) **
  (Alvarenv 120%Z Tint32(17%positive,0%Z) ** (BLbindings ** Aemp))).
 { unfold BMfullstate. eapply V293_target_wstate_star with
 (m1:=BMfullmemory run value)(m2:=emp)(o1:=V293_target_fixture_abs)(o2:=emp);try apply map_join_emp.
 - eapply V293_target_wstate_star with(m1:=BMjoined value)(m2:=BMrun run)
   (o1:=V293_target_fixture_abs)(o2:=emp).
   + apply BMrun_join.
   + apply map_join_emp.
   + eapply V293_target_wstate_star with(m1:=BLmemory 0 Vnull 1 0 0 Int.zero)(m2:=BMsaved value)
     (o1:=V293_target_fixture_abs)(o2:=emp).
     * apply BMsaved_join.
     * apply map_join_emp.
     * eapply good_fun_asrt_absop with(p:=BLshared)(le:=emp).
       -- unfold BLshared,BLphysical;apply V293_exit_physical_pre_good;apply V293_witness_li_good.
       -- apply BLphysical_owned.
     * split;[apply V293_encoded_memory_mapsto|reflexivity].
   + apply BMrun_owned.
 - apply BMcaller_names. }
 clear -H;sep auto.
Qed.

Definition BLprogram : progunit := fun f =>
 if Z.eq_dec f 300%Z then Some(V293_OSIntExit_function 112%Z 108%Z 109%Z 120%Z
 106%Z 103%Z 107%Z 110%Z 111%Z 200%Z 201%Z 202%Z 203%Z)else None.
Definition BLbuilderpre run := V293_exit_builder_pre 106%Z 107%Z 110%Z 111%Z 108%Z 109%Z 112%Z Tvoid 8%positive 10%positive 13%positive 14%positive 11%positive 12%positive 16%positive
 (spec_done None)BLshared Aemp run 120%Z.
Definition BLbuilderpost run := V293_exit_builder_post 106%Z 107%Z 110%Z 111%Z 108%Z 109%Z 112%Z Tvoid 8%positive 10%positive 13%positive 14%positive 11%positive 12%positive 16%positive
 (spec_done None)BLshared BLshared Aemp run 120%Z.
Definition BLfp(run:nat) : fpre.
 refine(V293_exit_builder_fpre 106%Z 107%Z 110%Z 111%Z 108%Z 109%Z 112%Z Tvoid 8%positive 10%positive 13%positive 14%positive 11%positive 12%positive 16%positive(spec_done None)BLshared Aemp run _).
 apply V293_exit_builder_pre_good.
 - unfold BLshared,BLphysical;apply V293_exit_physical_pre_good;apply V293_witness_li_good.
 - exact I.
Defined.
Definition BLfq(run:nat) : fpost.
 refine(V293_exit_builder_fpost 106%Z 107%Z 110%Z 111%Z 108%Z 109%Z 112%Z Tvoid 8%positive 10%positive 13%positive 14%positive 11%positive 12%positive 16%positive(spec_done None)BLshared BLshared Aemp run _).
 intro result;apply V293_exit_builder_post_good;try exact I;
 unfold BLshared,BLphysical;apply V293_exit_physical_pre_good;apply V293_witness_li_good.
Defined.
Theorem BLactual_builders : forall run,
 BuildPreI BLprogram 300%Z nil nil(BLfp run)V293_idle_tid=Some(BLbuilderpre run) /\
 BuildRetI BLprogram 300%Z nil nil(BLfq run)V293_idle_tid=Some(BLbuilderpost run).
Proof. intros;split;reflexivity. Qed.
Theorem BLnonempty_arguments_rejected : forall run v vl,
 BuildPreI BLprogram 300%Z(v::vl)nil(BLfp run)V293_idle_tid=None.
Proof.
 intros run v vl.
 assert(E:dl_vl_match dnil(rev(v::vl))=false).
 { destruct(rev(v::vl))eqn:Rev;[ |reflexivity].
   apply(f_equal(@rev val))in Rev;rewrite rev_involutive in Rev;discriminate. }
 unfold BuildPreI.
 cbn -[dl_vl_match rev].
 rewrite E;reflexivity.
Qed.

Lemma BLdomain : eq_dom_env BLle(cons(120%Z,Tint32)nil).
Proof.
 unfold BLle,eq_dom_env;intros x t;destruct(Z.eq_dec x 120%Z)as[E|Ne].
 - subst x;rewrite map_get_sig;cbn;split.
   + intros[E|Bad];[inversion E;subst t;eexists;reflexivity|contradiction].
   + intros[b E];inversion E;left;reflexivity.
 - rewrite map_get_sig' by congruence;cbn;split.
   + intros[E|Bad];[inversion E;congruence|contradiction].
   + intros[b E];discriminate.
Qed.
Theorem BLbuilder_nonempty : forall run value,BLfullstate run value |= BLbuilderpre run.
Proof.
 intros run value;pose proof(BLfull_owned run value)as Held.
 apply astar_l_adomlenv_intro with(d:=cons(120%Z,Tint32)nil)in Held;[ |exact BLdomain].
 assert(U:BLfullstate run value |=
 (BLbindings ** (Agvarenv 112%Z Tint8(16%positive,0%Z) //\\ A_notin_lenv 112%Z)) **
 ((PV(15%positive,Int.zero)@Tint32|->value ** Alvarenv 120%Z Tint32(15%positive,0%Z)) **
 (BLshared ** (Amapsto(16%positive,0%Z)Tint8 false(V293_byteval run) **
 V293_exit_builder_domain 120%Z)))).
 { unfold V293_exit_builder_domain,V293_guard_cell in *;clear -Held;sep auto. }
 eapply astar_mono in U.
 2:{ unfold BLbindings;apply V293_exit_builder_forget_names. }
 2:{ intros s0 H0;exact H0. }
 assert(Op:BLfullstate run value |= <||spec_done None||> **
 (V293_exit_builder_globals 106%Z 107%Z 110%Z 111%Z 108%Z 109%Z 112%Z Tvoid 8%positive 10%positive 13%positive 14%positive 11%positive 12%positive 16%positive **
 ((PV(15%positive,Int.zero)@Tint32|->value ** Alvarenv 120%Z Tint32(15%positive,0%Z)) **
 (BLshared ** (Amapsto(16%positive,0%Z)Tint8 false(V293_byteval run) **
 V293_exit_builder_domain 120%Z))))).
 { apply astar_l_aop'_intro;[exact U|reflexivity]. }
 unfold BLbuilderpre,V293_exit_builder_pre,V293_exit_builder_external_pre,
 V293_exit_builder_cells,Alvarmapsto,Alvarenv',Aptrmapsto;clear -Op;sep auto.
Qed.

Lemma BMdomain : eq_dom_env BMle(cons(120%Z,Tint32)nil).
Proof.
 unfold BMle,eq_dom_env;intros x t;destruct(Z.eq_dec x 120%Z)as[E|Ne].
 - subst x;rewrite map_get_sig;cbn;split.
   + intros[E|Bad];[inversion E;subst t;eexists;reflexivity|contradiction].
   + intros[b E];inversion E;left;reflexivity.
 - rewrite map_get_sig' by congruence;cbn;split.
   + intros[E|Bad];[inversion E;congruence|contradiction].
   + intros[b E];discriminate.
Qed.
Theorem BMbuilder_nonempty : forall run value,BMfullstate run value |= BLbuilderpre run.
Proof.
 intros run value;pose proof(BMfull_owned run value)as Held.
 apply astar_l_adomlenv_intro with(d:=cons(120%Z,Tint32)nil)in Held;[ |exact BMdomain].
 assert(U:BMfullstate run value |=
 (BLbindings ** (Agvarenv 112%Z Tint8(16%positive,0%Z) //\\ A_notin_lenv 112%Z)) **
 ((PV(17%positive,Int.zero)@Tint32|->value ** Alvarenv 120%Z Tint32(17%positive,0%Z)) **
 (BLshared ** (Amapsto(16%positive,0%Z)Tint8 false(V293_byteval run) **
 V293_exit_builder_domain 120%Z)))).
 { unfold V293_exit_builder_domain,V293_guard_cell in *;clear -Held;sep auto. }
 eapply astar_mono in U.
 2:{ unfold BLbindings;apply V293_exit_builder_forget_names. }
 2:{ intros s0 H0;exact H0. }
 assert(Op:BMfullstate run value |= <||spec_done None||> **
 (V293_exit_builder_globals 106%Z 107%Z 110%Z 111%Z 108%Z 109%Z 112%Z Tvoid 8%positive 10%positive 13%positive 14%positive 11%positive 12%positive 16%positive **
 ((PV(17%positive,Int.zero)@Tint32|->value ** Alvarenv 120%Z Tint32(17%positive,0%Z)) **
 (BLshared ** (Amapsto(16%positive,0%Z)Tint8 false(V293_byteval run) **
 V293_exit_builder_domain 120%Z))))).
 { apply astar_l_aop'_intro;[exact U|reflexivity]. }
 unfold BLbuilderpre,V293_exit_builder_pre,V293_exit_builder_external_pre,
 V293_exit_builder_cells,Alvarmapsto,Alvarenv',Aptrmapsto;clear -Op;sep auto.
Qed.

Theorem BLold_value_control :
 (BLfullstate 0 Vundef |= BLbuilderpre 0) /\
 (BLfullstate 0(Vint32 Int.one) |= BLbuilderpre 0).
Proof. split;apply BLbuilder_nonempty. Qed.
Theorem BLlocal_address_control :
 (BLfullstate 1 Vundef |= BLbuilderpre 1) /\
 (BMfullstate 1 Vundef |= BLbuilderpre 1) /\
 evalval(eaddrof(evar 120%Z))(getsmem(BLfullstate 1 Vundef))=Some(Vptr(15%positive,Int.zero)) /\
 evalval(eaddrof(evar 120%Z))(getsmem(BMfullstate 1 Vundef))=Some(Vptr(17%positive,Int.zero)).
Proof. split;[apply BLbuilder_nonempty| ].
 split;[apply BMbuilder_nonempty| ].
 split;vm_compute;reflexivity. Qed.
Theorem BLold_value_frame : forall run v1 v2 b i,b<>15%positive ->
 get(BLfullmemory run v1)(b,i)=get(BLfullmemory run v2)(b,i).
Proof.
 intros;unfold BLfullmemory,BLjoined,BLsaved;repeat rewrite map_merge_semp by reflexivity;
 repeat rewrite V293_encoded_memory_outside by(left;assumption);reflexivity.
Qed.
Theorem BLbinding_domain_same :
 eq_dom_env BLle(cons(120%Z,Tint32)nil) /\ eq_dom_env BMle(cons(120%Z,Tint32)nil).
Proof. split;[apply BLdomain|apply BMdomain]. Qed.
Theorem BLno_lookup_builder : forall sd I run,run<256 ->run<>1 ->
 InfRules(fun _=>None)sd V293_witness_li I(BLbuilderpost run)Afalse(BLbuilderpre run)
 (V293_OSIntExit_body 112%Z 108%Z 109%Z 120%Z 106%Z 103%Z 107%Z 110%Z 111%Z
 200%Z 201%Z 202%Z 203%Z)Afalse V293_idle_tid.
Proof.
 intros sd I run Bound Off.
 eapply V293_OSIntExit_not_running_builder_contract with(P:=BLprogram)(f:=300%Z)(vl:=nil)(lg:=nil)
 (aop:=spec_done None)(shared:=BLshared)(output:=BLshared)(extra:=Aemp)(run:=run)
 (GP:=ltac:(apply(V293_exit_builder_pre_good 106%Z 107%Z 110%Z 111%Z 108%Z 109%Z 112%Z Tvoid 8%positive 10%positive 13%positive 14%positive 11%positive 12%positive 16%positive(spec_done None)BLshared Aemp run);
 [unfold BLshared,BLphysical;apply V293_exit_physical_pre_good;apply V293_witness_li_good|exact Logic.I]))
 (GQ:=ltac:(intro result;apply(V293_exit_builder_post_good 106%Z 107%Z 110%Z 111%Z 108%Z 109%Z 112%Z Tvoid 8%positive 10%positive 13%positive 14%positive 11%positive 12%positive 16%positive(spec_done None)BLshared BLshared Aemp run result);try exact Logic.I;
 unfold BLshared,BLphysical;apply V293_exit_physical_pre_good;apply V293_witness_li_good));
 try discriminate;try assumption;try reflexivity;try assumption;try discriminate.
 unfold BLshared,BLphysical;apply V293_exit_physical_pre_local.
Qed.

Theorem BLpost_nonempty : forall run value,
 BLfullstate run value |= BLbuilderpost run None.
Proof.
 intros run value;pose proof(BLbuilder_nonempty run value)as Held.
 unfold BLbuilderpost,V293_exit_builder_post,V293_exit_builder_external_post,
 BLbuilderpre,V293_exit_builder_pre,V293_exit_builder_external_pre in *.
 destruct(Nat.eqb run 1);clear -Held;sep auto.
Qed.
