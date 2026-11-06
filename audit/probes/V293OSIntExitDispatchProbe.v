(* Joint physical resources; no execution trace or production ISR claim. *)
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
Definition JDge := V293_change_fixture_ge.
Definition JDnames : asrt :=
 (Agvarenv 108%Z Tint8(11%positive,0%Z) //\\ A_notin_lenv 108%Z) **
 (Agvarenv 109%Z Tint8(12%positive,0%Z) //\\ A_notin_lenv 109%Z).
Definition JDbyte b n := V293_encoded_memory b 0 true(encode_val Tint8(V293_byteval n)).
Definition JDinternal hv := merge(merge V293_witness_inputs V293_witness_current)(JDbyte 4%positive hv).
Definition JDcaller out := merge V293_target_fixture_table
 (V293_encoded_memory 10%positive 0 true(encode_val(Tptr Tvoid)out)).
Definition JDbase hv out := merge(JDinternal hv)(JDcaller out).
Definition JDextra nest locked nc c := merge(JDbyte 11%positive nest)
 (merge(JDbyte 12%positive locked)(V293_change_extra nc c)).
Definition JDmemory hv out nest locked nc c := merge(JDbase hv out)(JDextra nest locked nc c).
Definition JDstate M := V293_target_wstate JDge emp M V293_target_fixture_abs.
Definition JDpre nc nest locked out c := V293_exit_ready_pre
 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive 0 16
 V293_witness_li V293_idle_tid(spec_done None)106%Z 107%Z Tvoid 8%positive 10%positive
 V293_idle_entries V293_idle_tasks 110%Z 111%Z 13%positive 14%positive 11%positive 12%positive
 nc JDnames nest locked out c.
Definition JDtail nc nest locked c := V293_OSSched_tail_state
 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive 0 16
 V293_witness_li V293_idle_tid(spec_done None)106%Z 107%Z Tvoid 8%positive 10%positive
 V293_idle_entries V293_idle_tasks 110%Z 111%Z 13%positive 14%positive nc
 (V293_rdy_raw_cells(V293_exit_cells 11%positive 12%positive nest locked)JDnames)c.
Ltac JDoutside :=
 unfold JDbase,JDinternal,JDcaller,JDextra,V293_change_extra,V293_guard_memory,V293_counter_memory,JDbyte;
 repeat first[rewrite map_merge_semp by reflexivity|
 rewrite V293_encoded_memory_outside by(left;congruence)];
 V293_prefix_outside.
Ltac JDjoin k := apply map_join_merge;apply map_disjoint;intros[b i];
 destruct(Pos.eq_dec b k);[subst b| ];
 first[solve[left;JDoutside]|solve[right;left;JDoutside]].
Lemma JDnames_owned : V293_wstate JDge emp emp |= JDnames.
Proof.
 unfold JDnames. eapply V293_wstate_star with(m1:=emp)(m2:=emp);[apply map_join_emp| | ];
 split;[eexists;split;[vm_compute;reflexivity|repeat split;reflexivity]|
 split;[intros[v H];discriminate|split;reflexivity]|
 eexists;split;[vm_compute;reflexivity|repeat split;reflexivity]|
 split;[intros[v H];discriminate|split;reflexivity]].
Qed.
Lemma JDenv : forall st,st |= JDnames ->
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
Lemma JDinternal_owned : forall hv,
 V293_wstate JDge emp(JDinternal hv) |=
 <||spec_done None||> ** V293_sched_internal_resource
 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive 0 16
 V293_witness_li V293_idle_tid(V293_byteval hv).
Proof.
 intro hv. apply astar_l_aop'_intro;[ |reflexivity].
 unfold V293_sched_internal_resource.
 eapply V293_wstate_star;[JDjoin 4%positive| | ].
 - eapply V293_wstate_star;[JDjoin 6%positive| | ].
   + eapply V293_wstate_star with(m1:=emp)(m2:=V293_witness_inputs).
     * apply map_join_comm;apply map_join_emp.
     * apply V293_prefix_fixture_globals;vm_compute;reflexivity.
     * apply V293_prefix_fixture_inputs.
   + apply astar_comm. apply astar_l_aie_intro;[ |reflexivity].
     apply V293_prefix_fixture_current;vm_compute;reflexivity.
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Lemma JDcaller_owned : forall out,
 V293_target_wstate JDge emp(JDcaller out)V293_target_fixture_abs |=
 V293_prefix_frame 106%Z 103%Z 107%Z Tvoid 8%positive 10%positive V293_idle_entries V293_idle_tasks Aemp **
 V293_prefix_output Tvoid 10%positive out.
Proof.
 intro out. unfold JDcaller.
 eapply V293_target_wstate_star;[JDjoin 8%positive|apply map_join_emp| | ].
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
Lemma JDextra_owned : forall nest locked nc c,
 V293_wstate JDge emp(JDextra nest locked nc c) |=
 V293_rdy_raw_cells(V293_exit_cells 11%positive 12%positive nest locked)JDnames **
 (V293_guard_cell 110%Z 13%positive nc ** V293_counter_cell 111%Z 14%positive c).
Proof.
 intros. unfold V293_exit_cells,V293_interrupt_cells;cbn[V293_rdy_raw_cells].
 assert(H:V293_wstate JDge emp(JDextra nest locked nc c) |=
  PV(11%positive,Int.zero)@Tint8|->(V293_byteval nest) **
  (PV(12%positive,Int.zero)@Tint8|->(V293_byteval locked) **
  (V293_guard_cell 110%Z 13%positive nc ** V293_counter_cell 111%Z 14%positive c))).
 { unfold JDextra. eapply V293_wstate_star;[JDjoin 11%positive| | ].
   - split;[apply V293_encoded_memory_mapsto|reflexivity].
   - eapply V293_wstate_star;[JDjoin 12%positive| | ].
     + split;[apply V293_encoded_memory_mapsto|reflexivity].
     + apply V293_change_extra_witness. }
 assert(H':V293_wstate JDge emp(JDextra nest locked nc c) |= JDnames **
  (PV(11%positive,Int.zero)@Tint8|->(V293_byteval nest) **
  (PV(12%positive,Int.zero)@Tint8|->(V293_byteval locked) **
  (V293_guard_cell 110%Z 13%positive nc ** V293_counter_cell 111%Z 14%positive c)))).
 { eapply V293_wstate_star with(m1:=emp)(m2:=JDextra nest locked nc c).
   - apply map_join_comm;apply map_join_emp.
   - apply JDnames_owned.
   - exact H. }
 clear H. sep auto.
Qed.
Lemma JDjoint_owned : forall hv out nest locked nc c,
 JDstate(JDmemory hv out nest locked nc c) |=
 ((<||spec_done None||> ** V293_sched_internal_resource
 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive 0 16
 V293_witness_li V293_idle_tid(V293_byteval hv)) **
 (V293_prefix_frame 106%Z 103%Z 107%Z Tvoid 8%positive 10%positive V293_idle_entries V293_idle_tasks Aemp **
 V293_prefix_output Tvoid 10%positive out)) **
 (V293_rdy_raw_cells(V293_exit_cells 11%positive 12%positive nest locked)JDnames **
 (V293_guard_cell 110%Z 13%positive nc ** V293_counter_cell 111%Z 14%positive c)).
Proof.
 intros. eapply V293_target_wstate_star with(o1:=V293_target_fixture_abs)(o2:=emp).
 - apply map_join_merge;apply map_disjoint;intros[b i].
   destruct(Pos.eq_dec b 11%positive);[subst b;left;JDoutside| ].
   destruct(Pos.eq_dec b 12%positive);[subst b;left;JDoutside| ].
   destruct(Pos.eq_dec b 13%positive);[subst b;left;JDoutside| ].
   destruct(Pos.eq_dec b 14%positive);[subst b;left;JDoutside| ]. right;left;JDoutside.
 - apply map_join_emp.
 - eapply V293_target_wstate_star with(o1:=emp)(o2:=V293_target_fixture_abs).
   + apply map_join_merge;apply map_disjoint;intros[b i].
     destruct(Pos.eq_dec b 8%positive);[subst b;left;JDoutside| ].
     destruct(Pos.eq_dec b 10%positive);[subst b;left;JDoutside| ]. right;left;JDoutside.
   + apply map_join_comm;apply map_join_emp.
   + apply JDinternal_owned.
   + apply JDcaller_owned.
 - apply JDextra_owned.
Qed.
Theorem JDnonempty : forall hv out nest locked nc c,
 JDstate(JDmemory hv out nest locked nc c) |= JDpre nc nest locked out c.
Proof.
 intros. pose proof(JDjoint_owned hv out nest locked nc c)as Hs.
 unfold JDpre,V293_exit_ready_pre,V293_sched_internal_pre. sep normal. exists(V293_byteval hv).
 assert(B:0<256 /\ 16<256 /\ exists p,V293_bitmap_ready 0 16 p).
 { split;[lia| ]. split;[lia| ]. exists 12;vm_compute;intuition lia. }
 unfold V293_prefix_frame in *;sep auto;assumption.
Qed.
Theorem JDtail_nonempty : forall nest locked nc c,
 JDstate(JDmemory 12(Vptr V293_idle_tid)nest locked nc c) |= JDtail nc nest locked c.
Proof.
 intros. pose proof(JDjoint_owned 12(Vptr V293_idle_tid)nest locked nc c)as Hs.
 unfold JDtail,V293_OSSched_tail_state. exists V293_idle_tid.
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

Theorem JDactual_comparison : forall nest locked nc c,nc<256 ->
 evalval(V293_OSSched_different 103%Z 110%Z)
  (getsmem(JDstate(JDmemory 12(Vptr V293_idle_tid)nest locked nc c)))=
 Some(Vint32(if Nat.eqb 12 nc then Int.zero else Int.one)).
Proof.
 intros nest locked nc c B.
 exact(proj1(V293_OSSched_priority_comparison
 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive 0 16
 V293_witness_li V293_idle_tid(spec_done None)106%Z 107%Z Tvoid 8%positive 10%positive
 V293_idle_entries V293_idle_tasks 110%Z 111%Z 13%positive 14%positive nc
 (V293_rdy_raw_cells(V293_exit_cells 11%positive 12%positive nest locked)JDnames)c _
 ltac:(lia)ltac:(lia)ltac:(exists 12;vm_compute;intuition lia)B(JDtail_nonempty nest locked nc c))).
Qed.
Theorem JDpriority_control :
 JDstate(JDmemory 12(Vptr V293_idle_tid)0 0 12 Int.zero) |= JDtail 12 0 0 Int.zero /\
 JDstate(JDmemory 12(Vptr V293_idle_tid)0 0 0 Int.zero) |= JDtail 0 0 0 Int.zero /\
 evalval(V293_OSSched_different 103%Z 110%Z)
  (getsmem(JDstate(JDmemory 12(Vptr V293_idle_tid)0 0 12 Int.zero)))=Some(Vint32 Int.zero) /\
 evalval(V293_OSSched_different 103%Z 110%Z)
  (getsmem(JDstate(JDmemory 12(Vptr V293_idle_tid)0 0 0 Int.zero)))=Some(Vint32 Int.one).
Proof.
 split;[apply JDtail_nonempty| ]. split;[apply JDtail_nonempty| ].
 split;apply JDactual_comparison;lia.
Qed.
Theorem JDpriority_frame : forall hv out nest locked n1 n2 c b i,b<>13%positive ->
 get(JDmemory hv out nest locked n1 c)(b,i)=get(JDmemory hv out nest locked n2 c)(b,i).
Proof.
 intros. unfold JDmemory,JDextra,V293_change_extra,V293_guard_memory.
 repeat rewrite map_merge_semp by reflexivity.
 repeat rewrite V293_encoded_memory_outside by(left;assumption). reflexivity.
Qed.
Theorem JDcounter_frame : forall hv out nest locked nc c1 c2 b i,b<>14%positive ->
 get(JDmemory hv out nest locked nc c1)(b,i)=get(JDmemory hv out nest locked nc c2)(b,i).
Proof.
 intros. unfold JDmemory,JDextra,V293_change_extra,V293_counter_memory.
 repeat rewrite map_merge_semp by reflexivity.
 repeat rewrite V293_encoded_memory_outside by(left;assumption). reflexivity.
Qed.
Lemma JDtail_counter_load : forall nc nest locked c s,
 s |= JDtail nc nest locked c -> load Tint32(getmem s)(14%positive,0%Z)=Some(Vint32 c).
Proof.
 intros nc nest locked c s[t Hs].
 assert(H:s |= V293_counter_cell 111%Z 14%positive c ** Atrue).
 { unfold V293_prefix_frame in Hs;sep auto. }
 eapply V293_star_load_l;[ |exact H]. intros s0 H0.
 eapply V293_star_load_r;[ |exact H0]. intros s1[Hm _].
 eapply mapstoval_load;[reflexivity|exact Hm].
Qed.
Lemma JDcounter_variable : forall s x b c,
 get(getgenv s)x=Some(b,Tint32) -> get(getlenv s)x=None ->
 load Tint32(getmem s)(b,0%Z)=Some(Vint32 c) ->
 evalval(evar x)(getsmem s)=Some(Vint32 c) /\
 evaltype(evar x)(getsmem s)=Some Tint32 /\
 evalval(ebinop oplus(evar x)(econst32 Int.one))(getsmem s)=Some(Vint32(Int.add c Int.one)).
Proof.
 intros s x b c G N L. destruct s as [[[[[[ge le] M] ir] aux] O] op].
 cbn[getgenv getlenv getmem get_smem get_genv get_lenv get_mem]in G,N,L.
 cbn[getsmem get_smem evalval evaltype get_lenv get_genv]. rewrite N,G.
 cbn -[load]. rewrite L. repeat split;reflexivity.
Qed.
Lemma JDcounter_eval : forall nc nest locked c s,
 s |= JDtail nc nest locked c ->
 evalval(evar 111%Z)(getsmem s)=Some(Vint32 c) /\
 evaltype(evar 111%Z)(getsmem s)=Some Tint32 /\
 evalval(ebinop oplus(evar 111%Z)(econst32 Int.one))(getsmem s)=Some(Vint32(Int.add c Int.one)).
Proof.
 intros nc nest locked c s Hs.
 pose proof(JDtail_counter_load _ _ _ _ _ Hs)as L.
 assert(H:s |= V293_counter_cell 111%Z 14%positive c ** Atrue).
 { destruct Hs as[t Hs]. unfold V293_prefix_frame in Hs;sep auto. }
 assert(E:get(getgenv s)111%Z=Some(14%positive,Tint32) /\ get(getlenv s)111%Z=None).
 { eapply V293_star_env_l;[ |exact H]. intros s0 H0.
   eapply V293_star_env_l;[ |exact H0]. apply V293_counter_env. }
 destruct E as[G N]. eapply JDcounter_variable; eassumption.
Qed.
Definition JDincrement_expr := ebinop oplus(evar 111%Z)(econst32 Int.one).
Theorem JDcounter_boundary_control :
 JDstate(JDmemory 12(Vptr V293_idle_tid)0 0 0 Int.zero) |= JDtail 0 0 0 Int.zero /\
 JDstate(JDmemory 12(Vptr V293_idle_tid)0 0 0(Int.repr Int.max_unsigned)) |=
  JDtail 0 0 0(Int.repr Int.max_unsigned) /\
 evalval JDincrement_expr(getsmem(JDstate(JDmemory 12(Vptr V293_idle_tid)0 0 0 Int.zero)))=
 Some(Vint32 Int.one) /\
 evalval JDincrement_expr(getsmem(JDstate(JDmemory 12(Vptr V293_idle_tid)0 0 0(Int.repr Int.max_unsigned))))=
 Some(Vint32 Int.zero).
Proof.
 split;[apply JDtail_nonempty| ]. split;[apply JDtail_nonempty| ].
 split.
 - exact (proj2 (proj2 (JDcounter_eval _ _ _ _ _ (JDtail_nonempty 0 0 0 Int.zero)))).
 - assert(W:Int.add(Int.repr Int.max_unsigned)Int.one=Int.zero).
   { exact(Int.eq_spec (Int.add(Int.repr Int.max_unsigned)Int.one)Int.zero). }
   rewrite <-W.
   exact (proj2 (proj2 (JDcounter_eval _ _ _ _ _ (JDtail_nonempty 0 0 0 (Int.repr Int.max_unsigned))))).
Qed.
Theorem JDwrong_post_control :
 eq_dom_env(getlenv(JDstate(JDmemory 12(Vptr V293_idle_tid)0 0 0 Int.one)))nil /\
 JDstate(JDmemory 12(Vptr V293_idle_tid)0 0 0 Int.one) |= JDtail 0 0 0 Int.one /\
 ~(JDstate(JDmemory 12(Vptr V293_idle_tid)0 0 0 Int.one) |= JDtail 0 0 0 Int.zero).
Proof.
 split.
 - intros x tp. split;[contradiction|intros[b H];vm_compute in H;discriminate].
 - split;[apply JDtail_nonempty| ]. intro Bad.
   pose proof(JDtail_counter_load 0 0 0 Int.zero _ Bad)as Wrong.
   pose proof(JDtail_counter_load 0 0 0 Int.one _(JDtail_nonempty 0 0 0 Int.one))as Actual.
   rewrite Actual in Wrong. vm_compute in Wrong;discriminate.
Qed.
(* Neutralizing only the increment changes the call-entry counter. The two
   owned snapshots are not themselves a trace of the CPU switch. *)
Theorem JDincrement_ablation :
 JDstate(JDmemory 12(Vptr V293_idle_tid)0 0 0 Int.zero) |= JDtail 0 0 0 Int.zero /\
 JDstate(JDmemory 12(Vptr V293_idle_tid)0 0 0 Int.one) |= JDtail 0 0 0 Int.one /\
 evalval(evar 111%Z)(getsmem(JDstate(JDmemory 12(Vptr V293_idle_tid)0 0 0 Int.zero)))=Some(Vint32 Int.zero) /\
 evalval(evar 111%Z)(getsmem(JDstate(JDmemory 12(Vptr V293_idle_tid)0 0 0 Int.one)))=Some(Vint32 Int.one).
Proof.
 split;[apply JDtail_nonempty| ]. split;[apply JDtail_nonempty| ].
 split;[exact(proj1(JDcounter_eval _ _ _ _ _(JDtail_nonempty 0 0 0 Int.zero)))|
 exact(proj1(JDcounter_eval _ _ _ _ _(JDtail_nonempty 0 0 0 Int.one)))].
Qed.
Theorem JDsame_checked : forall Spec sd I r ri c nest locked int_switch,
 InfRules Spec sd V293_witness_li I r ri(JDtail 12 nest locked c)
 (sif(V293_OSSched_different 103%Z 110%Z)
  (sseq(V293_OSSched_increment 111%Z)(sseq(sskip None)(scall int_switch nil)))(sskip None))
 (JDtail 12 nest locked c)V293_idle_tid.
Proof.
 intros. eapply (V293_OSIntExit_dispatch_tail
 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive 0 16
 V293_witness_li V293_idle_tid(spec_done None)106%Z 107%Z Tvoid 8%positive 10%positive
 V293_idle_entries V293_idle_tasks 110%Z 111%Z 13%positive 14%positive 12
 (V293_rdy_raw_cells(V293_exit_cells 11%positive 12%positive nest locked)JDnames)
 Spec sd I r ri c int_switch (JDtail 12 nest locked c));try lia.
 - exists 12;vm_compute;intuition lia.
 - intro Bad;exfalso;apply Bad;reflexivity.
Qed.
Theorem JDdisabled_checked : forall Spec sd I r ri c nc out dispatch,
 InfRules Spec sd V293_witness_li I r ri(JDpre nc 2 0 out c)
 (V293_OSIntExit_nesting_dispatch 108%Z 109%Z dispatch)(JDpre nc 1 0 out c)V293_idle_tid.
Proof.
 intros. apply V293_OSIntExit_ready_disabled;try lia.
 - exists 12;vm_compute;intuition lia.
 - apply JDenv.
Qed.
