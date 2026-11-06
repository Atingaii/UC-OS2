(* Nonempty exact builders use the existing concrete scheduler byte fixture.
   Owned CI here is an empty tail of the existing invariant, not a production
   ISR invariant. Ambient RI is independent and may be the real ready Inv. *)
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedExactLocal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCritical.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternalWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitch.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickDelayHoare.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition ELCI:Inv:=fun k=>V293_shared_inv(S k).
Definition ELprogram:=V293_OSSchedNew_internal_unit 200%Z 100%Z 101%Z 102%Z 103%Z 104%Z.
Definition ELfp:=V293_sched_exact_fpre 100%Z 101%Z 102%Z 103%Z
 1%positive 2%positive 3%positive 4%positive V293_witness_li ELCI V293_witness_li_good.
Definition ELfq:=V293_sched_exact_fpost 100%Z 101%Z 102%Z 103%Z
 1%positive 2%positive 3%positive 4%positive V293_witness_li ELCI V293_witness_li_good.
Definition ELspec:=V293_sched_exact_spec 200%Z 100%Z 101%Z 102%Z 103%Z
 1%positive 2%positive 3%positive 4%positive V293_witness_li ELCI V293_witness_li_good.
Definition ELlg:=V293_critical_call_lg 0 16(spec_done None)nil nil.
Definition ELpre:=V293_sched_exact_pre 100%Z 101%Z 102%Z 103%Z
 1%positive 2%positive 3%positive 4%positive 0 16 V293_witness_li (7%positive,Int.zero)(spec_done None) **
 V293_sched_critical ELCI nil nil.
Definition ELpost result:=V293_sched_exact_post 100%Z 101%Z 102%Z 103%Z
 1%positive 2%positive 3%positive 4%positive 0 16 V293_witness_li (7%positive,Int.zero)(spec_done None) result **
 V293_sched_critical ELCI nil nil.

Lemma ELcurrent : V293_wstate V293_witness_ge V293_witness_le V293_witness_current |=
 p_local V293_witness_li (7%positive,Int.zero) nil.
Proof.
 unfold p_local; eapply V293_wstate_star with(m1:=V293_witness_current)(m2:=emp).
 - apply map_join_emp.
 - exists Tvoid;exists 6%positive.
   eapply V293_wstate_star with(m1:=emp)(m2:=V293_witness_current).
   + apply map_join_comm;apply map_join_emp.
   + exists 6%positive;split;[vm_compute;reflexivity| ];split;[reflexivity|split;reflexivity].
   + split;[apply V293_encoded_memory_mapsto|reflexivity].
 - unfold LINV,V293_witness_li; eapply V293_wstate_star with(m1:=emp)(m2:=emp).
   + apply map_join_emp.
   + split;reflexivity.
   + split;[apply V293_witness_li_good|split;reflexivity].
Qed.

Lemma ELbody_state :
  V293_wstate V293_witness_ge V293_witness_le V293_witness_memory |=
    <||spec_done None||> ** V293_sched_state
      (V293_sched_exact_common 100%Z 101%Z 102%Z 103%Z 104%Z
        1%positive 2%positive 3%positive 4%positive 5%positive 0 16 2
        V293_witness_li (7%positive, Int.zero) (Aie false ** V293_sched_local_domain 104%Z))
      5%positive 4%positive (V293_byteval 0) (V293_byteval 0).
Proof.
  eapply V293_wstate_star with (m1 := emp) (m2 := V293_witness_memory).
  - apply map_join_comm. apply map_join_emp.
  - split; [reflexivity | split; reflexivity].
  - eapply V293_wstate_star.
    + unfold V293_witness_memory. V293_single_join 4%positive.
    + eapply V293_wstate_star.
      * V293_single_join 5%positive.
      * eapply V293_wstate_star.
        -- V293_single_join 6%positive.
        -- eapply V293_wstate_star with (m1 := emp) (m2 := V293_witness_inputs).
           ++ apply map_join_comm. apply map_join_emp.
           ++ apply V293_witness_bindings_sat.
           ++ apply V293_witness_inputs_sat.
        -- eapply V293_wstate_star with (m1 := V293_witness_current) (m2 := emp).
           ++ apply map_join_emp.
           ++ apply ELcurrent.
           ++ apply V293_witness_internal_frame.
      * split; [apply V293_encoded_memory_mapsto | reflexivity].
    + split; [apply V293_encoded_memory_mapsto | reflexivity].
Qed.



Lemma ELtail : forall n low ge le,
 V293_wstate ge le emp |=starinv_isr ELCI low n.
Proof.
 induction n;intros low ge le;cbn[starinv_isr ELCI V293_shared_inv].
 - exists(fun _:hid=>false);right;apply astar_r_aemp_intro.
   repeat split;reflexivity.
 - eapply V293_wstate_star with(m1:=emp)(m2:=emp);[apply map_join_emp| |apply IHn].
   exists(fun _:hid=>false);right;apply astar_r_aemp_intro.
   repeat split;reflexivity.
Qed.
Lemma ELcritical : V293_wstate V293_witness_ge V293_witness_le emp |=V293_sched_critical ELCI nil nil.
Proof.
 unfold V293_sched_critical,SWINV.
 assert(H:V293_wstate V293_witness_ge V293_witness_le emp |=
 (isrclr ** Aie false) ** (EX k,ATopis k ** invlth_isr ELCI 0 k)).
 { eapply V293_wstate_star with(m1:=emp)(m2:=emp);[apply map_join_emp| | ].
   - apply astar_comm;apply astar_l_aie_intro;[ |reflexivity].
     exists(fun _:hid=>false);repeat split;reflexivity.
   - exists INUM;apply astar_l_atopis_intro;[ |reflexivity]. unfold invlth_isr;apply ELtail. }
 apply astar_l_ais_intro with(i:=nil) in H;[ |reflexivity].
 apply astar_l_acs_intro with(i:=nil) in H;[ |reflexivity].
 clear -H;sep auto.
Qed.
Lemma ELbounds : forall hold,
 <||spec_done None||> ** V293_sched_exact_resource 100%Z 101%Z 102%Z 103%Z
 1%positive 2%positive 3%positive 4%positive 0 16 V293_witness_li(7%positive,Int.zero) hold ==>
 V293_sched_exact_pre 100%Z 101%Z 102%Z 103%Z
 1%positive 2%positive 3%positive 4%positive 0 16 V293_witness_li(7%positive,Int.zero)(spec_done None).
Proof.
 intros hold s H;exists hold;apply astar_comm;apply astar_l_apure_intro.
 - exact H.
 - split;[lia|split;[lia|exists 12;vm_compute;intuition lia]].
Qed.
Theorem ELbuilders_nonempty : exists pre post,
 Some pre=BuildPreI ELprogram 200%Z nil ELlg ELfp(7%positive,Int.zero) /\
 Some post=BuildRetI ELprogram 200%Z nil ELlg ELfq(7%positive,Int.zero) /\
 V293_wstate V293_witness_ge V293_witness_le V293_witness_memory |=pre.
Proof.
 eexists;eexists;split;[reflexivity| ];split;[reflexivity| ].
 change(V293_wstate V293_witness_ge V293_witness_le V293_witness_memory |=
 ((EX v:val,LV 104%Z@Tint8|->v)**Aemp) ** ELpre ** V293_sched_local_domain 104%Z).
 pose proof ELbody_state as H.
 assert(H2:V293_wstate V293_witness_ge V293_witness_le V293_witness_memory |=
 <||spec_done None||> ** V293_sched_state
 (V293_sched_exact_common 100%Z 101%Z 102%Z 103%Z 104%Z
 1%positive 2%positive 3%positive 4%positive 5%positive 0 16(V293_ready_group 0 16)
 V293_witness_li (7%positive,Int.zero)((Aie false ** Aemp) ** V293_sched_local_domain 104%Z))
 5%positive 4%positive(V293_byteval 0)(V293_byteval 0)).
 { unfold V293_sched_state,V293_sched_exact_common in *;clear -H;sep auto. }
 clear H;rename H2 into H.
 apply V293_sched_exact_return in H.
 assert(P:V293_wstate V293_witness_ge V293_witness_le V293_witness_memory |=
 (((EX v:val,LV 104%Z@Tint8|->v)**Aemp) **
 V293_sched_exact_pre 100%Z 101%Z 102%Z 103%Z
 1%positive 2%positive 3%positive 4%positive 0 16 V293_witness_li(7%positive,Int.zero)(spec_done None)) **
 V293_sched_local_domain 104%Z).
 { eapply astar_mono in H.
   2: { intros s0 H0;exact H0. }
   2: { apply astar_mono;[ |intros s0 H0;exact H0].
        intros s0 H0;apply ELbounds with(hold:=V293_byteval 0);clear -H0;sep auto. }
   clear -H;sep auto. }
 assert(T:V293_wstate V293_witness_ge V293_witness_le V293_witness_memory |=
 V293_sched_critical ELCI nil nil **
 ((((EX v:val,LV 104%Z@Tint8|->v)**Aemp) **
 V293_sched_exact_pre 100%Z 101%Z 102%Z 103%Z
 1%positive 2%positive 3%positive 4%positive 0 16 V293_witness_li(7%positive,Int.zero)(spec_done None)) **
 V293_sched_local_domain 104%Z)).
 { eapply V293_wstate_star with(m1:=emp)(m2:=V293_witness_memory);
 [apply map_join_comm;apply map_join_emp|apply ELcritical|exact P]. }
 unfold ELpre;clear -T;sep auto.
Qed.
Theorem ELenvironment : forall sd RI,
 WFFunEnv ELprogram ELspec sd V293_witness_li RI.
Proof. intros;apply V293_OSSchedNew_exact_WFFunEnv;discriminate. Qed.
Theorem ELactual_call : forall sd RI r ri,
 InfRules ELspec sd V293_witness_li RI r ri (ELpre ** Aemp)
 (scall 200%Z nil)(EX result:option val,ELpost result ** Aemp)(7%positive,Int.zero).
Proof.
 intros;unfold ELpre,ELpost;apply V293_OSSchedNew_exact_call with(Hli:=V293_witness_li_good);
 try lia;try exact I;reflexivity.
Qed.
