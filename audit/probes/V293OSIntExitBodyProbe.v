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
Definition FBge := set V293_change_fixture_ge 112%Z(16%positive,Tint8).
Definition FBnames : asrt :=
 (Agvarenv 108%Z Tint8(11%positive,0%Z) //\\ A_notin_lenv 108%Z) **
 (Agvarenv 109%Z Tint8(12%positive,0%Z) //\\ A_notin_lenv 109%Z).
Definition FBbyte b n := V293_encoded_memory b 0 true(encode_val Tint8(V293_byteval n)).
Definition FBinternal hv := merge(merge V293_witness_inputs V293_witness_current)(FBbyte 4%positive hv).
Definition FBcaller out := merge V293_target_fixture_table
 (V293_encoded_memory 10%positive 0 true(encode_val(Tptr Tvoid)out)).
Definition FBbase hv out := merge(FBinternal hv)(FBcaller out).
Definition FBextra nest locked nc c := merge(FBbyte 11%positive nest)
 (merge(FBbyte 12%positive locked)(V293_change_extra nc c)).
Definition FBmemory hv out nest locked nc c := merge(FBbase hv out)(FBextra nest locked nc c).
Definition FBstate M := V293_target_wstate FBge emp M V293_target_fixture_abs.
Definition FBpre nc nest locked out c := V293_exit_ready_pre
 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive 0 16
 V293_witness_li V293_idle_tid(spec_done None)106%Z 107%Z Tvoid 8%positive 10%positive
 V293_idle_entries V293_idle_tasks 110%Z 111%Z 13%positive 14%positive 11%positive 12%positive
 nc FBnames nest locked out c.
Ltac FBoutside :=
 unfold FBbase,FBinternal,FBcaller,FBextra,V293_change_extra,V293_guard_memory,V293_counter_memory,FBbyte;
 repeat first[rewrite map_merge_semp by reflexivity|
 rewrite V293_encoded_memory_outside by(left;congruence)];
 V293_prefix_outside.
Ltac FBjoin k := apply map_join_merge;apply map_disjoint;intros[b i];
 destruct(Pos.eq_dec b k);[subst b| ];
 first[solve[left;FBoutside]|solve[right;left;FBoutside]].
Lemma FBnames_owned : V293_wstate FBge emp emp |= FBnames.
Proof.
 unfold FBnames. eapply V293_wstate_star with(m1:=emp)(m2:=emp);[apply map_join_emp| | ];
 split;[eexists;split;[vm_compute;reflexivity|repeat split;reflexivity]|
 split;[intros[v H];discriminate|split;reflexivity]|
 eexists;split;[vm_compute;reflexivity|repeat split;reflexivity]|
 split;[intros[v H];discriminate|split;reflexivity]].
Qed.
Lemma FBenv : forall st,st |= FBnames ->
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
Lemma FBinternal_owned : forall hv,
 V293_wstate FBge emp(FBinternal hv) |=
 <||spec_done None||> ** V293_sched_internal_resource
 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive 0 16
 V293_witness_li V293_idle_tid(V293_byteval hv).
Proof.
 intro hv. apply astar_l_aop'_intro;[ |reflexivity].
 unfold V293_sched_internal_resource.
 eapply V293_wstate_star;[FBjoin 4%positive| | ].
 - eapply V293_wstate_star;[FBjoin 6%positive| | ].
   + eapply V293_wstate_star with(m1:=emp)(m2:=V293_witness_inputs).
     * apply map_join_comm;apply map_join_emp.
     * apply V293_prefix_fixture_globals;vm_compute;reflexivity.
     * apply V293_prefix_fixture_inputs.
   + apply astar_comm. apply astar_l_aie_intro;[ |reflexivity].
     apply V293_prefix_fixture_current;vm_compute;reflexivity.
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Lemma FBcaller_owned : forall out,
 V293_target_wstate FBge emp(FBcaller out)V293_target_fixture_abs |=
 V293_prefix_frame 106%Z 103%Z 107%Z Tvoid 8%positive 10%positive V293_idle_entries V293_idle_tasks Aemp **
 V293_prefix_output Tvoid 10%positive out.
Proof.
 intro out. unfold FBcaller.
 eapply V293_target_wstate_star;[FBjoin 8%positive|apply map_join_emp| | ].
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
Lemma FBextra_owned : forall nest locked nc c,
 V293_wstate FBge emp(FBextra nest locked nc c) |=
 V293_rdy_raw_cells(V293_exit_cells 11%positive 12%positive nest locked)FBnames **
 (V293_guard_cell 110%Z 13%positive nc ** V293_counter_cell 111%Z 14%positive c).
Proof.
 intros. unfold V293_exit_cells,V293_interrupt_cells;cbn[V293_rdy_raw_cells].
 assert(H:V293_wstate FBge emp(FBextra nest locked nc c) |=
  PV(11%positive,Int.zero)@Tint8|->(V293_byteval nest) **
  (PV(12%positive,Int.zero)@Tint8|->(V293_byteval locked) **
  (V293_guard_cell 110%Z 13%positive nc ** V293_counter_cell 111%Z 14%positive c))).
 { unfold FBextra. eapply V293_wstate_star;[FBjoin 11%positive| | ].
   - split;[apply V293_encoded_memory_mapsto|reflexivity].
   - eapply V293_wstate_star;[FBjoin 12%positive| | ].
     + split;[apply V293_encoded_memory_mapsto|reflexivity].
     + unfold V293_change_extra. eapply V293_wstate_star.
       * apply map_join_merge. apply map_disjoint. intros[b i].
         destruct(Pos.eq_dec b 13%positive);[subst b;right;left|left];
         apply V293_encoded_memory_outside;left;congruence.
       * apply V293_guard_cell_witness;vm_compute;reflexivity.
       * apply V293_counter_cell_witness;vm_compute;reflexivity. }
 assert(H':V293_wstate FBge emp(FBextra nest locked nc c) |= FBnames **
  (PV(11%positive,Int.zero)@Tint8|->(V293_byteval nest) **
  (PV(12%positive,Int.zero)@Tint8|->(V293_byteval locked) **
  (V293_guard_cell 110%Z 13%positive nc ** V293_counter_cell 111%Z 14%positive c)))).
 { eapply V293_wstate_star with(m1:=emp)(m2:=FBextra nest locked nc c).
   - apply map_join_comm;apply map_join_emp.
   - apply FBnames_owned.
   - exact H. }
 clear H. sep auto.
Qed.
Lemma FBjoint_owned : forall hv out nest locked nc c,
 FBstate(FBmemory hv out nest locked nc c) |=
 ((<||spec_done None||> ** V293_sched_internal_resource
 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive 0 16
 V293_witness_li V293_idle_tid(V293_byteval hv)) **
 (V293_prefix_frame 106%Z 103%Z 107%Z Tvoid 8%positive 10%positive V293_idle_entries V293_idle_tasks Aemp **
 V293_prefix_output Tvoid 10%positive out)) **
 (V293_rdy_raw_cells(V293_exit_cells 11%positive 12%positive nest locked)FBnames **
 (V293_guard_cell 110%Z 13%positive nc ** V293_counter_cell 111%Z 14%positive c)).
Proof.
 intros. eapply V293_target_wstate_star with(o1:=V293_target_fixture_abs)(o2:=emp).
 - apply map_join_merge;apply map_disjoint;intros[b i].
   destruct(Pos.eq_dec b 11%positive);[subst b;left;FBoutside| ].
   destruct(Pos.eq_dec b 12%positive);[subst b;left;FBoutside| ].
   destruct(Pos.eq_dec b 13%positive);[subst b;left;FBoutside| ].
   destruct(Pos.eq_dec b 14%positive);[subst b;left;FBoutside| ]. right;left;FBoutside.
 - apply map_join_emp.
 - eapply V293_target_wstate_star with(o1:=emp)(o2:=V293_target_fixture_abs).
   + apply map_join_merge;apply map_disjoint;intros[b i].
     destruct(Pos.eq_dec b 8%positive);[subst b;left;FBoutside| ].
     destruct(Pos.eq_dec b 10%positive);[subst b;left;FBoutside| ]. right;left;FBoutside.
   + apply map_join_comm;apply map_join_emp.
   + apply FBinternal_owned.
   + apply FBcaller_owned.
 - apply FBextra_owned.
Qed.
Theorem FBnonempty : forall hv out nest locked nc c,
 FBstate(FBmemory hv out nest locked nc c) |= FBpre nc nest locked out c.
Proof.
 intros. pose proof(FBjoint_owned hv out nest locked nc c)as Hs.
 unfold FBpre,V293_exit_ready_pre,V293_sched_internal_pre. sep normal. exists(V293_byteval hv).
 assert(B:0<256 /\ 16<256 /\ exists p,V293_bitmap_ready 0 16 p).
 { split;[lia| ]. split;[lia| ]. exists 12;vm_compute;intuition lia. }
 unfold V293_prefix_frame in *;sep auto;assumption.
Qed.

Definition FBphysical nc nest locked out c := V293_exit_physical_pre
 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive 0 16
 V293_witness_li V293_idle_tid(spec_done None)Tvoid 8%positive 10%positive
 V293_idle_entries V293_idle_tasks 13%positive 14%positive 11%positive 12%positive
 nc nest locked out c.
Definition FBbindings := V293_exit_caller_bindings 103%Z 106%Z 107%Z Tvoid 8%positive 10%positive
 110%Z 111%Z 108%Z 109%Z 13%positive 14%positive 11%positive 12%positive.
Lemma FBbindings_empty : FBbindings ==> Aemp.
Proof.
 assert(S:forall p q,(p ==> Aemp)->(q ==> Aemp)->p ** q ==> Aemp).
 { intros p q P Q s H. apply astar_l_aemp_elim.
   eapply astar_mono;[exact P|exact Q|exact H]. }
 unfold FBbindings,V293_exit_caller_bindings,V293_prefix_bindings,V293_counter_bindings,V293_exit_guard_bindings.
 repeat apply S;intros s H;destruct H as[G _];
 apply agvarenv_elim in G;exact(proj2 G).
Qed.
Lemma FBphysical_owned : forall hv out nest locked nc c,
 FBstate(FBmemory hv out nest locked nc c) |= FBphysical nc nest locked out c.
Proof.
 intros. pose proof(FBnonempty hv out nest locked nc c)as H.
 assert(H':FBstate(FBmemory hv out nest locked nc c) |= FBphysical nc nest locked out c ** (FBbindings ** Aemp)).
 { apply V293_exit_pre_split. unfold FBpre in H.
   unfold V293_exit_ready_pre,V293_prefix_frame,V293_exit_cells,V293_interrupt_cells in *.
   cbn[V293_rdy_raw_cells]in *;unfold FBnames,V293_exit_guard_bindings in *;sep auto. }
 apply astar_r_aemp_elim. eapply astar_mono;[intros st Hs;exact Hs| |exact H'].
 intros st Hs. apply astar_r_aemp_elim in Hs. apply FBbindings_empty;exact Hs.
Qed.

Definition FBle : env := sig 120%Z(15%positive,Tint32).
Definition FBsaved value := V293_encoded_memory 15%positive 0 true(encode_val Tint32 value).
Definition FBrun run := V293_encoded_memory 16%positive 0 false(encode_val Tint8(V293_byteval run)).
Definition FBjoined value := merge(FBmemory 0 Vnull 1 0 0 Int.zero)(FBsaved value).
Definition FBfullmemory run value := merge(FBjoined value)(FBrun run).
Definition FBfullstate run value := V293_target_wstate FBge FBle(FBfullmemory run value)V293_target_fixture_abs.
Definition FBshared := FBphysical 0 1 0 Vnull Int.zero.
Definition FBframe run := V293_guard_cell 112%Z 16%positive run ** (FBbindings ** Aemp).
Definition FBfullpre run value := V293_exit_body_pre(spec_done None)FBshared 120%Z 15%positive value(FBframe run).
Definition FBfullat run := V293_exit_body_at(spec_done None)FBshared 120%Z 15%positive(FBframe run).

Lemma FBcaller_names : V293_wstate FBge FBle emp |=
 Alvarenv 120%Z Tint32(15%positive,0%Z) ** (FBbindings ** Aemp).
Proof.
 unfold FBbindings,V293_exit_caller_bindings,V293_prefix_bindings,V293_counter_bindings,V293_exit_guard_bindings.
 repeat(eapply V293_wstate_star with(m1:=emp)(m2:=emp);[apply map_join_emp| | ]).
 all:repeat split;try(intros[v H];vm_compute in H;discriminate);
 try(eexists;split;[vm_compute;reflexivity|repeat split;reflexivity]);try reflexivity.
Qed.
Lemma FBsaved_join : forall value,
 join(FBmemory 0 Vnull 1 0 0 Int.zero)(FBsaved value)(FBjoined value).
Proof.
 intro value. apply map_join_merge;apply map_disjoint;intros[b i].
 destruct(Pos.eq_dec b 15%positive);[subst b;left;unfold FBmemory;FBoutside| ].
 right;left;unfold FBsaved;apply V293_encoded_memory_outside;left;exact n.
Qed.
Lemma FBrun_join : forall run value,join(FBjoined value)(FBrun run)(FBfullmemory run value).
Proof.
 intros. apply map_join_merge;apply map_disjoint;intros[b i].
 destruct(Pos.eq_dec b 16%positive);[subst b;left|right;left;unfold FBrun;apply V293_encoded_memory_outside;left;exact n].
 unfold FBjoined,FBsaved,FBmemory;FBoutside.
Qed.
Lemma FBrun_owned : forall run,
 V293_wstate FBge FBle(FBrun run) |= V293_guard_cell 112%Z 16%positive run.
Proof.
 intro run. unfold V293_guard_cell. eapply V293_wstate_star with(m1:=emp)(m2:=FBrun run).
 - apply map_join_comm;apply map_join_emp.
 - split.
   + eexists;split;[vm_compute;reflexivity|repeat split;reflexivity].
   + split;[intros[v H];vm_compute in H;discriminate|split;reflexivity].
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Lemma FBfull_owned : forall run value, FBfullstate run value |=
 (FBshared ** PV(15%positive,Int.zero)@Tint32|->value) **
 (V293_guard_cell 112%Z 16%positive run **
  (Alvarenv 120%Z Tint32(15%positive,0%Z) ** (FBbindings ** Aemp))).
Proof.
 intros.
 assert(H:FBfullstate run value |=
  ((FBshared ** PV(15%positive,Int.zero)@Tint32|->value) **
   V293_guard_cell 112%Z 16%positive run) **
  (Alvarenv 120%Z Tint32(15%positive,0%Z) ** (FBbindings ** Aemp))).
 { unfold FBfullstate. eapply V293_target_wstate_star with
 (m1:=FBfullmemory run value)(m2:=emp)(o1:=V293_target_fixture_abs)(o2:=emp);try apply map_join_emp.
 - eapply V293_target_wstate_star with(m1:=FBjoined value)(m2:=FBrun run)
   (o1:=V293_target_fixture_abs)(o2:=emp).
   + apply FBrun_join.
   + apply map_join_emp.
   + eapply V293_target_wstate_star with(m1:=FBmemory 0 Vnull 1 0 0 Int.zero)(m2:=FBsaved value)
     (o1:=V293_target_fixture_abs)(o2:=emp).
     * apply FBsaved_join.
     * apply map_join_emp.
     * eapply good_fun_asrt_absop with(p:=FBshared)(le:=emp).
       -- unfold FBshared,FBphysical;apply V293_exit_physical_pre_good;apply V293_witness_li_good.
       -- apply FBphysical_owned.
     * split;[apply V293_encoded_memory_mapsto|reflexivity].
   + apply FBrun_owned.
 - apply FBcaller_names. }
 clear -H;sep auto.
Qed.
Theorem FBfull_pre_nonempty : forall run value,FBfullstate run value |= FBfullpre run value.
Proof.
 intros. pose proof(FBfull_owned run value)as H.
 unfold FBfullpre,V293_exit_body_pre,FBframe,V293_time_cell,V293_time_binding.
 apply astar_l_aop'_intro;[clear -H;sep auto|reflexivity].
Qed.
Theorem FBfull_initialized_nonempty : forall run,
 FBfullstate run(Vint32 Int.zero) |= FBfullat run.
Proof.
 intro run. pose proof(FBfull_owned run(Vint32 Int.zero))as H.
 unfold FBfullat,V293_exit_body_at,FBframe,V293_saved_pointer_resource.
 assert(A:FBfullstate run(Vint32 Int.zero) |= <||spec_done None||> **
  ((FBshared ** PV(15%positive,Int.zero)@Tint32|->Vint32 Int.zero) **
  (V293_guard_cell 112%Z 16%positive run **
   (Alvarenv 120%Z Tint32(15%positive,0%Z) ** (FBbindings ** Aemp))))).
 { apply astar_l_aop'_intro;[exact H|reflexivity]. }
 clear H;sep auto.
Qed.
Theorem FBrunning_read : forall run value,run<256 ->
 evalval(V293_OSIntEnter_running 112%Z)(getsmem(FBfullstate run value))=
 Some(Vint32(if Nat.eqb run 1 then Int.one else Int.zero)) /\ evaltype(V293_OSIntEnter_running 112%Z)(getsmem(FBfullstate run value))=Some Tint32.
Proof.
 intros run value B. eapply V293_exit_running_eval with(b:=16%positive)(rest:=Atrue);[exact B| ].
 pose proof(FBfull_owned run value)as H;clear -H;sep auto.
Qed.
Theorem FBrunning_control :
 (evalval(V293_OSIntEnter_running 112%Z)(getsmem(FBfullstate 0(Vint32 Int.one)))=Some(Vint32 Int.zero)) /\ (evalval(V293_OSIntEnter_running 112%Z)(getsmem(FBfullstate 1(Vint32 Int.one)))=Some(Vint32 Int.one)) /\ (evalval(V293_OSIntEnter_running 112%Z)(getsmem(FBfullstate 2(Vint32 Int.one)))=Some(Vint32 Int.zero)) /\ (evalval(V293_OSIntEnter_running 112%Z)(getsmem(FBfullstate 255(Vint32 Int.one)))=Some(Vint32 Int.zero)).
Proof.
 repeat split;first[exact(proj1(FBrunning_read 0(Vint32 Int.one)ltac:(lia)))|
 exact(proj1(FBrunning_read 1(Vint32 Int.one)ltac:(lia)))|
 exact(proj1(FBrunning_read 2(Vint32 Int.one)ltac:(lia)))|
 exact(proj1(FBrunning_read 255(Vint32 Int.one)ltac:(lia)))].
Qed.
Theorem FBrunning_frame : forall run1 run2 value b i,b<>16%positive ->
 get(FBfullmemory run1 value)(b,i)=get(FBfullmemory run2 value)(b,i).
Proof.
 intros. unfold FBfullmemory,FBrun. repeat rewrite map_merge_semp by reflexivity.
 repeat rewrite V293_encoded_memory_outside by(left;assumption). reflexivity.
Qed.
Lemma FBsaved_load : forall run value st,st |= FBfullpre run(Vint32 value) ->
 load Tint32(getmem st)(15%positive,0%Z)=Some(Vint32 value).
Proof.
 intros run value st H. assert(P:st |= PV(15%positive,Int.zero)@Tint32|->Vint32 value ** Atrue).
 { unfold FBfullpre,V293_exit_body_pre,V293_time_cell in H;clear -H;sep auto. }
 eapply V293_star_load_l;[ |exact P]. intros s[M _]. eapply mapstoval_load;[reflexivity|exact M].
Qed.
Theorem FBsaved_control :
 (FBfullstate 0(Vint32 Int.one) |= FBfullpre 0(Vint32 Int.one)) /\ (FBfullstate 0(Vint32 Int.zero) |= FBfullpre 0(Vint32 Int.zero)) /\ ~(FBfullstate 0(Vint32 Int.one) |= FBfullpre 0(Vint32 Int.zero)).
Proof.
 split;[apply FBfull_pre_nonempty| ]. split;[apply FBfull_pre_nonempty| ]. intro H.
 pose proof(FBsaved_load _ _ _ H)as Wrong.
 pose proof(FBsaved_load _ _ _(FBfull_pre_nonempty 0(Vint32 Int.one)))as Actual.
 rewrite Actual in Wrong;vm_compute in Wrong;discriminate.
Qed.
Theorem FBsaved_frame : forall run value1 value2 b i,b<>15%positive ->
 get(FBfullmemory run value1)(b,i)=get(FBfullmemory run value2)(b,i).
Proof.
 intros. unfold FBfullmemory,FBjoined,FBsaved. repeat rewrite map_merge_semp by reflexivity.
 repeat rewrite V293_encoded_memory_outside by(left;assumption). reflexivity.
Qed.
(* Entire real body on the non-running path, even with every lookup absent. *)
Theorem FBno_lookup_body : forall sd I run old,run<256 -> run<>1 ->
 InfRules(fun _=>None)sd V293_witness_li I
 (fun result=>[|result=None|] ** FBfullat run)Afalse(FBfullpre run old)
 (V293_OSIntExit_body 112%Z 108%Z 109%Z 120%Z 106%Z 103%Z 107%Z 110%Z 111%Z
   200%Z 201%Z 202%Z 203%Z)Afalse V293_idle_tid.
Proof.
 intros sd I run old Bound Off. unfold FBfullat,FBfullpre,FBframe.
 apply V293_OSIntExit_not_running_body;try assumption.
 unfold FBshared,FBphysical;apply V293_exit_physical_pre_local.
Qed.
