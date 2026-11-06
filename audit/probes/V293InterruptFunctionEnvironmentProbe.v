Require Import CertiOS.certiucos.v293.proofs.V293TimeGetAPI.
Require Import Coq.Logic.FunctionalExtensionality.
(* Independent nonempty bindings and a SATISFIABLE actual internal builder,
   using the SAME name-local invariant as the linked API component. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.toptheorem.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.certiucos.v293.proofs.V293ComponentLink.
Require Import CertiOS.certiucos.v293.proofs.V293TimeNamesGood.
Require Import CertiOS.certiucos.v293.proofs.V293TimeShared.
Require Import CertiOS.certiucos.v293.proofs.V293TimeSetAPI.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternalWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.certiucos.v293.code.V293OSVersion.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Local Open Scope nat_scope.

Require Import CertiOS.certiucos.v293.proofs.V293InterruptFunctionEnvironment.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterInternal.
Require Import CertiOS.certiucos.v293.code.V293OSIntEnter.
Require Import CertiOS.certiucos.v293.proofs.V293TimeGetLink.
Require Import CertiOS.audit.probes.V293OSIntEnterProbe.

Definition FELI := V293_time_names_li 1001%Z 80%positive.
Definition FEP := V293_irq_internal_unit 301%Z 200%Z 9101%Z 9102%Z
 100%Z 101%Z 102%Z 103%Z 104%Z.
Definition FESpec := V293_irq_internal_spec 301%Z 200%Z 9101%Z 9102%Z
 100%Z 101%Z 102%Z 103%Z 701%positive 702%positive 1%positive 2%positive 3%positive 4%positive
 FELI(V293_time_names_local_good 1001%Z 80%positive).
Definition FEAPI := V293_clock_api_unit 201%Z 202%Z 203%Z 1001%Z 1002%Z 1003%Z.
Definition FEGE := set(set(set V293_witness_ge 1001%Z (80%positive,Tint32))
 9101%Z (701%positive,Tint8))9102%Z (702%positive,Tint8).

Theorem FEchecked :
 GoodI(V293_time_shared_inv 80%positive)V293_scheduler FELI /\
 WFAPI FEAPI(V293_clock_api_spec 201%Z 202%Z 203%Z)FELI FESpec
 V293_scheduler(V293_time_shared_inv 80%positive)nil /\
 WFFunEnv FEP FESpec V293_scheduler FELI(V293_time_shared_inv 80%positive) /\
 WFIFun FEP FESpec V293_scheduler(V293_time_shared_inv 80%positive)FELI /\
 no_fun_same FEAPI FEP.
Proof. apply V293_irq_clock_components_checked;discriminate. Qed.

Theorem FEfive_entries :
 let P:=pumerge FEAPI FEP in
 P 201%Z=Some V293_OSVersion_function /\
 P 202%Z=Some(V293_TimeSet_function 1001%Z 1002%Z 1003%Z) /\
 P 203%Z=Some(V293_TimeGet_function 1001%Z 1002%Z 1003%Z) /\
 P 301%Z=Some(V293_OSIntEnter_function 9101%Z 9102%Z) /\
 P 200%Z=Some(V293_OSSchedNew_function 100%Z 101%Z 102%Z 103%Z 104%Z).
Proof. repeat split;reflexivity. Qed.
Lemma FEInputs : V293_wstate FEGE V293_witness_le V293_witness_inputs |=
  V293_sched_inputs 1%positive 2%positive 3%positive 0 16 2.
Proof.
  eapply V293_wstate_star; [V293_witness_join | apply V293_read_bytes_witness | ].
  eapply V293_wstate_star.
  - apply map_join_merge. apply map_disjoint. intros [b i].
    destruct (Pos.eq_dec b 3%positive); [subst b; right; left | left]; V293_outside.
  - apply V293_read_bytes_witness.
  - split; [apply V293_encoded_memory_mapsto | reflexivity].
Qed.

Lemma FECurrent : forall le, V293_wstate FEGE le V293_witness_current |=
  CurLINV FELI (7%positive,Int.zero).
Proof.
  intros le. exists (nil:list logicvar).
  eapply V293_wstate_star with (m1:=V293_witness_current) (m2:=emp).
  - apply map_join_emp.
  - exists Tvoid. exists 6%positive.
    eapply V293_wstate_star with (m1:=emp) (m2:=V293_witness_current).
    + apply map_join_comm;apply map_join_emp.
    + exists 6%positive. split; [vm_compute;reflexivity | repeat split;reflexivity].
    + split; [apply V293_encoded_memory_mapsto | reflexivity].
  - eapply V293_wstate_star with (m1:=emp) (m2:=emp).
    + apply map_join_emp.
    + unfold LINV,FELI,V293_time_names_li.
      eapply V293_wstate_star with (m1:=emp) (m2:=emp).
      * apply map_join_emp.
      * exists 80%positive. vm_compute;repeat split;reflexivity.
      * split; [apply V293_time_names_local_good | repeat split;reflexivity].
    + exact I.
Qed.

Lemma FEBindings : V293_wstate FEGE V293_witness_le emp |=
  V293_sched_bindings 100%Z 101%Z 102%Z 103%Z 104%Z
    1%positive 2%positive 3%positive 4%positive 5%positive.
Proof.
  unfold V293_sched_bindings. repeat split.
  - exists 1%positive. vm_compute;repeat split;reflexivity.
  - exists 2%positive. vm_compute;repeat split;reflexivity.
  - exists 3%positive. vm_compute;repeat split;reflexivity.
  - exists 4%positive. vm_compute;repeat split;reflexivity.
  - exists 5%positive. vm_compute;repeat split;reflexivity.
  - intros [v H]. vm_compute in H;discriminate.
  - intros [v H]. vm_compute in H;discriminate.
  - intros [v H]. vm_compute in H;discriminate.
  - intros [v H]. vm_compute in H;discriminate.
Qed.

Lemma FEBodyState : V293_wstate FEGE V293_witness_le V293_witness_memory |=
  <||spec_done None||> ** V293_sched_state
    (V293_sched_common 100%Z 101%Z 102%Z 103%Z 104%Z
      1%positive 2%positive 3%positive 4%positive 5%positive 0 16 2
      FELI (7%positive,Int.zero) (Aie false ** V293_sched_local_domain 104%Z))
    5%positive 4%positive (V293_byteval 0) (V293_byteval 0).
Proof.
  eapply V293_wstate_star with (m1:=emp) (m2:=V293_witness_memory).
  - apply map_join_comm;apply map_join_emp.
  - split; [reflexivity | repeat split;reflexivity].
  - eapply V293_wstate_star.
    + unfold V293_witness_memory. V293_single_join 4%positive.
    + eapply V293_wstate_star.
      * V293_single_join 5%positive.
      * eapply V293_wstate_star.
        -- V293_single_join 6%positive.
        -- eapply V293_wstate_star with (m1:=emp) (m2:=V293_witness_inputs).
           ++ apply map_join_comm;apply map_join_emp.
           ++ exact FEBindings.
           ++ exact FEInputs.
        -- eapply V293_wstate_star with (m1:=V293_witness_current) (m2:=emp).
           ++ apply map_join_emp.
           ++ apply FECurrent.
           ++ apply astar_l_aie_intro; [ | reflexivity].
              apply adomlenv_intro; [repeat split;reflexivity | apply V293_witness_local_domain].
      * split; [apply V293_encoded_memory_mapsto | reflexivity].
    + split; [apply V293_encoded_memory_mapsto | reflexivity].
Qed.

(* The builder has a satisfying state with the very same FELI/FESpec.
   This is a spatial witness, NOT initialization reachability or sat(INV). *)
Theorem FEsched_nonvacuous : exists fp fq pre post s,
  FESpec 200%Z = Some (fp,fq,(Tvoid,nil)) /\
  Some pre = BuildPreI FEP 200%Z nil V293_sched_fixture_lg fp (7%positive,Int.zero) /\
  Some post = BuildRetI FEP 200%Z nil V293_sched_fixture_lg fq (7%positive,Int.zero) /\
  s |= pre.
Proof.
  eexists. eexists. eexists. eexists.
  exists (V293_wstate FEGE V293_witness_le V293_witness_memory).
  split; [reflexivity | ]. split; [reflexivity | ]. split; [reflexivity | ].
  change (V293_wstate FEGE V293_witness_le V293_witness_memory |=
    ((EX v:val, LV 104%Z @ Tint8 |-> v) ** Aemp) **
    V293_sched_internal_pre 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive
      0 16 FELI (7%positive,Int.zero) (spec_done None) ** V293_sched_local_domain 104%Z).
  pose proof FEBodyState as H.
  change (V293_wstate FEGE V293_witness_le V293_witness_memory |=
    <||spec_done None||> ** V293_sched_state
      (V293_sched_common 100%Z 101%Z 102%Z 103%Z 104%Z
        1%positive 2%positive 3%positive 4%positive 5%positive 0 16
        (V293_ready_group 0 16) FELI (7%positive,Int.zero)
        (Aie false ** V293_sched_local_domain 104%Z))
      5%positive 4%positive (V293_byteval 0) (V293_byteval 0)) in H.
  apply V293_sched_return_resource in H.
  eapply astar_mono in H.
  2:{ intros st HS;exact HS. }
  2:{ apply astar_mono; [ | intros st HS;exact HS].
      apply V293_sched_insert_bounds. split; [lia | ]. split; [lia | ].
      exists 12. vm_compute;intuition lia. }
  exact H.
Qed.

Definition FEentrymemory run nest :=
 merge(IEbyte 701%positive run)(merge(IEbyte 702%positive nest)V293_witness_current).
Definition FEentrystate M := V293_wstate FEGE emp M.
Definition FEentrypre := Aemp **
 (V293_interrupt_pre 9101%Z 9102%Z 701%positive 702%positive 1 0 FELI
 (7%positive,Int.zero)(spec_done None) ** A_dom_lenv nil).

Lemma FEentry_owned : FEentrystate(FEentrymemory 1 0) |= FEentrypre.
Proof.
 unfold FEentrypre. apply astar_l_aemp_intro. apply astar_comm.
 apply astar_l_adomlenv_intro;[ |exact(IEdomain(IEmemory 1 0))].
 unfold V293_interrupt_pre. apply astar_l_apure_intro;[ |split;lia].
 apply astar_l_aop'_intro;[ |reflexivity].
 unfold V293_interrupt_resource,V293_interrupt_cells.
 eapply V293_wstate_star with(m1:=IEbyte 701%positive 1)
 (m2:=merge(IEbyte 702%positive 0)V293_witness_current).
 - apply map_join_merge;apply map_disjoint;intros[b j].
   destruct(Pos.eq_dec b 701%positive);[subst b;right;left|left];
   unfold IEbyte,V293_witness_current;
   repeat first[rewrite map_merge_semp by reflexivity|
     rewrite V293_encoded_memory_outside by(left;congruence)];reflexivity.
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
 - eapply V293_wstate_star with(m1:=IEbyte 702%positive 0)(m2:=V293_witness_current).
   + apply map_join_merge;apply map_disjoint;intros[b j].
     destruct(Pos.eq_dec b 702%positive);[subst b;right;left|left];
     unfold IEbyte,V293_witness_current;
     rewrite V293_encoded_memory_outside by(left;congruence);reflexivity.
   + split;[apply V293_encoded_memory_mapsto|reflexivity].
   + eapply V293_wstate_star with(m1:=emp)(m2:=V293_witness_current).
     * apply map_join_comm;apply map_join_emp.
     * unfold V293_interrupt_globals. split;
       [exists 701%positive|exists 702%positive];vm_compute;repeat split;reflexivity.
     * apply astar_comm. apply astar_l_aie_intro;[apply FECurrent|reflexivity].
Qed.

(* The two witnesses share FEP/FESpec/FELI/FEGE, but are distinct calls;
   they do not duplicate ownership or assert initialization reachability. *)
Theorem FEenter_nonvacuous : exists fp fq pre post s,
 FESpec 301%Z=Some(fp,fq,(Tvoid,nil)) /\
 Some pre=BuildPreI FEP 301%Z nil(IElogic 1 0)fp(7%positive,Int.zero) /\
 Some post=BuildRetI FEP 301%Z nil(IElogic 1 0)fq(7%positive,Int.zero) /\
 s=FEentrystate(FEentrymemory 1 0) /\ s |= pre.
Proof.
 eexists;eexists;eexists;eexists. exists(FEentrystate(FEentrymemory 1 0)).
 split;[reflexivity| ]. split;[reflexivity| ]. split;[reflexivity| ].
 split;[reflexivity| ]. exact FEentry_owned.
Qed.

Definition FEvariant (replacement:option function):progunit :=
 fun f=>if Z.eq_dec f 301%Z then replacement else FEP f.
Definition FEwrong := Some(Tint32,dnil,dnil,V293_OSIntEnter_body 9101%Z 9102%Z).
Theorem FEonly_entry_changed : forall replacement,
 FEvariant replacement 301%Z=replacement /\
 (forall f,f<>301%Z ->FEvariant replacement f=FEP f) /\
 FEvariant(Some(V293_OSIntEnter_function 9101%Z 9102%Z))=FEP.
Proof.
 intros. split;[reflexivity| ]. split.
 - intros f N;unfold FEvariant;destruct(Z.eq_dec f 301%Z);congruence.
 - apply functional_extensionality;intro f. unfold FEvariant.
   destruct(Z.eq_dec f 301%Z);[subst;reflexivity|reflexivity].
Qed.
Theorem FEmissing_rejected : forall sd inv,
 ~WFFunEnv(FEvariant None)FESpec sd FELI inv.
Proof.
 intros sd inv[Dom Bodies]. destruct(proj2(Dom 301%Z))as[fd Code].
 - eexists;reflexivity.
 - discriminate Code.
Qed.
Theorem FEwrong_domain_still_matches : EqDom(FEvariant FEwrong)FESpec.
Proof.
 intros f. unfold FEvariant. destruct(Z.eq_dec f 301%Z);[subst| ].
 - split;intros[x H];eexists;reflexivity.
 - apply V293_irq_internal_domains.
Qed.
Theorem FEwrong_type_rejected : forall sd inv,
 ~WFFunEnv(FEvariant FEwrong)FESpec sd FELI inv.
Proof.
 intros sd inv[Dom Bodies].
 assert(Lookup:FESpec 301%Z=Some
 (V293_interrupt_fpre 9101%Z 9102%Z 701%positive 702%positive FELI
 (V293_time_names_local_good 1001%Z 80%positive),
 V293_interrupt_fpost 9101%Z 9102%Z 701%positive 702%positive FELI
 (V293_time_names_local_good 1001%Z 80%positive),(Tvoid,nil)))by reflexivity.
 destruct(Bodies _ _ _ _ _ Lookup)as(d1&d2&s&Code&Rest).
 discriminate Code.
Qed.
