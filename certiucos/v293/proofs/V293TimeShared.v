(* Shared getter checkpoint: physical time and abstract ostmid share one
   witness. Global-name/local-shadowing facts remain outside the IRQ Inv.
   This is not yet GoodI, initialization, a linked API, or setter refinement. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.memory_prop.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Local Open Scope nat_scope.

Definition V293_time_shared_fields n := EX t : tid, EX ts : TcbMod.map,
  EX es : EcbMod.map, CurTid t ** V293_shared_fields t ts es n.
Definition V293_time_shared_core bn := EX n : int32,
  V293_time_shared_fields n ** PV (bn,Int.zero) @ Tint32 |-> Vint32 n.

Lemma V293_time_fields_forget : forall n,
  V293_time_shared_fields n ==> V293_shared_core.
Proof. unfold V293_time_shared_fields,V293_shared_core. intros n s H;sep auto. Qed.
Lemma V293_time_fields_precise : forall n, precise (V293_time_shared_fields n).
Proof.
  intros n s M1 M2 O1 O2 H1 H2 M O HM1 HM2 HO1 HO2.
  apply (@V293_shared_core_precise s M1 M2 O1 O2
    (V293_time_fields_forget n _ H1) (V293_time_fields_forget n _ H2)
    M O HM1 HM2 HO1 HO2).
Qed.
Lemma V293_time_bytes_precise : forall b n,
  precise (PV (b,Int.zero) @ Tint32 |-> Vint32 n).
Proof.
  intros b n s M1 M2 O1 O2 H1 H2 M O HM1 HM2 HO1 HO2.
  destruct s as [[[[[[ge le] mem] ir] aux] oldO] op].
  change (mapstoval (b,0%Z) Tint32 true (Vint32 n) M1 /\ O1=emp) in H1.
  change (mapstoval (b,0%Z) Tint32 true (Vint32 n) M2 /\ O2=emp) in H2.
  destruct H1 as [[v1 [E1 P1]] Oe1]. destruct H2 as [[v2 [E2 P2]] Oe2].
  subst v1 v2. split; [eapply ptomvallist_mem_eq;eauto | congruence].
Qed.
Lemma V293_time_fields_clock : forall n s,
  s |= V293_time_shared_fields n -> get (getabst s) ostmid = Some (ostm n).
Proof.
  intros n s [t [ts [es H]]]. eapply V293_star_abst_get_r; [ | exact H].
  intros st Hf. exact (proj2 (proj2 (proj2 (V293_shared_fields_get _ _ _ _ st Hf)))).
Qed.
Lemma V293_time_core_precise : forall bn, precise (V293_time_shared_core bn).
Proof.
  intros bn s M1 M2 O1 O2 [n1 H1] [n2 H2] M O HM1 HM2 HO1 HO2.
  destruct s as [[[[[[ge le] mem] ir] aux] oldO] op].
  pose proof (@V293_star_abst_get_l _ _ ostmid _ (V293_time_fields_clock n1) _ H1) as N1.
  pose proof (@V293_star_abst_get_l _ _ ostmid _ (V293_time_fields_clock n2) _ H2) as N2.
  change (get O1 ostmid = Some (ostm n1)) in N1.
  change (get O2 ostmid = Some (ostm n2)) in N2.
  destruct HO1 as [F1 J1]. destruct HO2 as [F2 J2].
  assert (G1 : get O ostmid = Some (ostm n1)) by (eapply OSAbstMod.join_get_l;[exact J1 | exact N1]).
  assert (G2 : get O ostmid = Some (ostm n2)) by (eapply OSAbstMod.join_get_l;[exact J2 | exact N2]).
  assert (n1=n2) by congruence. subst n2.
  eapply precise_star; [apply V293_time_fields_precise | apply V293_time_bytes_precise |
    exact H1 | exact H2 | exact HM1 | exact HM2 | exists F1;exact J1 | exists F2;exact J2].
Qed.
Lemma V293_time_core_good : forall bn, GoodInvAsrt (V293_time_shared_core bn).
Proof.
  unfold V293_time_shared_core,V293_time_shared_fields,CurTid,Agvarmapsto,
    Aptrmapsto,V293_shared_fields. simpl. intros;repeat split;auto.
Qed.
Lemma V293_time_core_isr : forall bn, assertion.inv_isr_prop (V293_time_shared_core bn).
Proof.
  intro bn. unfold assertion.inv_isr_prop. repeat split;intros;
    destruct s as [[[[[[ge le] M] ir] [[ie si] cs]] O] op];exact H.
Qed.
Definition V293_time_shared_inv bn : Inv := fun k =>
  match k with
  | O => mkinvasrt (V293_time_core_good bn)
      (conj (V293_time_core_precise bn) (V293_time_core_isr bn))
  | S j => V293_shared_inv (S j)
  end.
Lemma V293_time_noisr_tail : forall bn n k,
  starinv_noisr (V293_time_shared_inv bn) (S k) n <==> Aemp.
Proof.
  intros bn. induction n;intros k s;simpl starinv_noisr;[reflexivity | ].
  change (s |= Aemp ** starinv_noisr (V293_time_shared_inv bn) (S (S k)) n <-> s |= Aemp).
  split;intro H.
  - apply astar_l_aemp_elim in H. apply IHn in H;exact H.
  - apply astar_l_aemp_intro. apply IHn;exact H.
Qed.
Lemma V293_time_noisr_core : forall bn n,
  starinv_noisr (V293_time_shared_inv bn) 0 n <==> V293_time_shared_core bn.
Proof.
  intros bn [ | n] s;[reflexivity | ].
  change (s |= V293_time_shared_core bn ** starinv_noisr (V293_time_shared_inv bn) 1 n <-> s |= V293_time_shared_core bn).
  split;intro H.
  - apply astar_r_aemp_elim. eapply astar_mono;[intros st H0;exact H0 |
      intros st H0;apply V293_time_noisr_tail in H0;exact H0 | exact H].
  - eapply astar_mono;[intros st H0;exact H0 |
      intros st H0;apply V293_time_noisr_tail;exact H0 | ].
    apply astar_r_aemp_intro;exact H.
Qed.
Lemma V293_time_irq_open : forall bn n ge le M ir aux O op,
  (forall i, ir i=false) ->
  (ge,le,M,ir,aux,O,op) |= invlth_isr (V293_time_shared_inv bn) 0 n ->
  (ge,le,M,ir,aux,O,op) |= V293_time_shared_core bn.
Proof.
  intros. unfold invlth_isr in H0. rewrite Nat.sub_0_r in H0.
  apply V293_time_noisr_core with (n:=n). eapply invisr_imply_noisr';eauto.
Qed.
Lemma V293_time_irq_close : forall bn n ge le M ir aux O op,
  (forall i, ir i=false) ->
  (ge,le,M,ir,aux,O,op) |= V293_time_shared_core bn ->
  (ge,le,M,ir,aux,O,op) |= invlth_isr (V293_time_shared_inv bn) 0 n.
Proof.
  intros. unfold invlth_isr. rewrite Nat.sub_0_r.
  apply V293_shared_clear_noisr_close;[exact H | ].
  apply V293_time_noisr_core;exact H0.
Qed.

Lemma V293_time_irq_open_asrt : forall bn n ir,
  (forall i, ir i=false) ->
  Aisr ir ** invlth_isr (V293_time_shared_inv bn) 0 n ==>
  Aisr ir ** V293_time_shared_core bn.
Proof.
  intros bn n ir Clear s H. destruct s as [[[[[[ge le] M] actual] aux] O] op].
  apply sat_split in H. destruct H as (m1 & m2 & o1 & o2 & JM & JO & H1 & H2).
  destruct H1 as [E Empty]. cbn in E. subst actual.
  apply sat_split'. exists m1. exists m2. exists o1. exists o2.
  repeat first [assumption | split]. eapply V293_time_irq_open; eauto.
Qed.
Lemma V293_time_irq_close_asrt : forall bn n ir,
  (forall i, ir i=false) ->
  Aisr ir ** V293_time_shared_core bn ==>
  Aisr ir ** invlth_isr (V293_time_shared_inv bn) 0 n.
Proof.
  intros bn n ir Clear s H. destruct s as [[[[[[ge le] M] actual] aux] O] op].
  apply sat_split in H. destruct H as (m1 & m2 & o1 & o2 & JM & JO & H1 & H2).
  destruct H1 as [E Empty]. cbn in E. subst actual.
  apply sat_split'. exists m1. exists m2. exists o1. exists o2.
  repeat first [assumption | split]. eapply V293_time_irq_close; eauto.
Qed.
Definition V293_time_shared_locals now ticks saved bn bt bs tmp save frame :=
  V293_time_binding false now bn ** (V293_time_cell true ticks bt tmp **
    (V293_time_cell true saved bs save ** frame)).
Lemma V293_time_locals_good : forall now ticks saved bn bt bs tmp save frame,
  GoodFrm frame -> GoodFrm (V293_time_shared_locals now ticks saved bn bt bs tmp save frame).
Proof.
  unfold V293_time_shared_locals,V293_time_binding,V293_time_cell.
  intros. cbn [V293_time_binding V293_counter_bindings GoodFrm Aptrmapsto];tauto.
Qed.
Lemma V293_time_locals_inv : forall now ticks saved bn bt bs tmp save frame li tid,
  (frame ==> CurLINV li tid) ->
  V293_time_shared_locals now ticks saved bn bt bs tmp save frame ==> CurLINV li tid.
Proof.
  unfold V293_time_shared_locals. intros. eapply V293_star_CurLINV_r;[ | exact H0].
  eapply V293_star_CurLINV_r. eapply V293_star_CurLINV_r;exact H.
Qed.
Theorem V293_time_shared_copy : forall Spec sd li r ri tid aop now ticks saved bn bt bs tmp save frame,
  (frame ==> CurLINV li tid) ->
  InfRules Spec sd li (V293_time_shared_inv bn) r ri
    (<||aop||> ** (V293_time_shared_core bn **
      V293_time_shared_locals now ticks saved bn bt bs tmp save frame))
    (sassign (evar ticks) (evar now))
    (EX clock : int32, <||aop||> ** (V293_time_shared_core bn **
      V293_time_shared_locals now ticks saved bn bt bs (Vint32 clock) save frame)) tid.
Proof.
  intros Spec sd li r ri tid aop now ticks saved bn bt bs tmp save frame Inv.
  eapply conseq_rule with
    (p:=EX clock : int32, <||aop||> ** ((V293_time_shared_fields clock **
      PV (bn,Int.zero) @ Tint32 |-> Vint32 clock) **
      V293_time_shared_locals now ticks saved bn bt bs tmp save frame)).
  - unfold V293_time_shared_core. intros s H;sep auto.
  - intros s H;exact H.
  - apply ex_intro_rule. intro clock.
    eapply conseq_rule with
      (p:=<||aop||> ** (V293_time_cell true ticks bt tmp **
        (V293_time_cell false now bn (Vint32 clock) **
          (V293_time_shared_fields clock **
            (V293_time_cell true saved bs save ** frame)))))
      (q:=<||aop||> ** (V293_time_cell true ticks bt (Vint32 clock) **
        (V293_time_cell false now bn (Vint32 clock) **
          (V293_time_shared_fields clock **
            (V293_time_cell true saved bs save ** frame))))).
    + unfold V293_time_shared_locals,V293_time_cell. intros s H;sep auto.
    + unfold V293_time_shared_core,V293_time_shared_locals,V293_time_cell.
      intros s H;sep auto.
    + apply V293_time_copy. eapply V293_star_CurLINV_r.
      eapply V293_star_CurLINV_r;exact Inv.
Qed.

Theorem V293_time_shared_critical_get : forall Spec sd li r ri tid aop ir si ci
    now ticks saved bn bt bs tmp save frame,
  (forall i, ir i=false) -> (gettopis si <= INUM)%nat ->
  GoodFrm frame -> (frame ==> CurLINV li tid) ->
  InfRules Spec sd li (V293_time_shared_inv bn) r ri
    (<||aop||> ** OS[ir,true,si,ci] **
      V293_time_shared_locals now ticks saved bn bt bs tmp save frame)
    (sseq (sprim encrit) (sseq (sassign (evar ticks) (evar now)) (sprim excrit)))
    (EX clock : int32, <||aop||> ** OS[ir,true,si,ci] **
      V293_time_shared_locals now ticks saved bn bt bs (Vint32 clock) save frame) tid.
Proof.
  intros Spec sd li r ri tid aop ir si ci now ticks saved bn bt bs tmp save frame Clear Bound GF Inv.
  eapply seq_rule with (p':=<||aop||> ** OS[ir,false,si,true::ci] **
    invlth_isr (V293_time_shared_inv bn) 0 (gettopis si) **
    V293_time_shared_locals now ticks saved bn bt bs tmp save frame).
  - eapply conseq_rule with
      (p:=<||aop||> ** OS[ir,true,si,ci] ** ATopis (gettopis si) **
        [| (gettopis si <= INUM)%nat |] ** V293_time_shared_locals now ticks saved bn bt bs tmp save frame).
    + intros s H. assert (S : s |= Ais si ** Atrue) by (sep auto).
      pose proof (V293_time_topis si Atrue s S) as Top.
      apply astar_l_atopis_elim in Top. destruct Top as [Top _].
      pose proof (@astar_l_atopis_intro s (gettopis si) _ H Top) as HT.
      clear H. rename HT into H. sep auto.
    + intros s H;exact H.
    + apply encrit1_rule. apply V293_time_locals_good;exact GF.
  - eapply seq_rule with (p':=EX clock : int32, <||aop||> ** OS[ir,false,si,true::ci] **
      V293_time_shared_core bn **
      V293_time_shared_locals now ticks saved bn bt bs (Vint32 clock) save frame).
    + eapply conseq_rule with
        (p:=<||aop||> ** (V293_time_shared_core bn **
          V293_time_shared_locals now ticks saved bn bt bs tmp save (frame ** OS[ir,false,si,true::ci])))
        (q:=EX clock : int32, <||aop||> ** (V293_time_shared_core bn **
          V293_time_shared_locals now ticks saved bn bt bs (Vint32 clock) save (frame ** OS[ir,false,si,true::ci]))).
      * intros s H.
        assert (P : s |= (Aisr ir ** invlth_isr (V293_time_shared_inv bn) 0 (gettopis si)) **
          (<||aop||> ** (Aie false ** (Ais si ** (Acs (true::ci) **
            V293_time_shared_locals now ticks saved bn bt bs tmp save frame))))) by (sep auto).
        eapply astar_mono in P;[ | apply V293_time_irq_open_asrt;exact Clear | intros st H0;exact H0].
        clear H. unfold V293_time_shared_locals in *. sep auto.
      * unfold V293_time_shared_locals. intros s H;sep auto.
      * apply V293_time_shared_copy. eapply V293_star_CurLINV_l;exact Inv.
    + eapply conseq_rule with
        (p:=EX clock : int32, <||aop||> ** OS[ir,false,si,true::ci] **
          V293_time_shared_core bn ** V293_time_shared_locals now ticks saved bn bt bs (Vint32 clock) save frame).
      * intros s H;exact H.
      * intros s H;exact H.
      * apply ex_intro_rule. intro clock.
        eapply conseq_rule with
          (p:=<||aop||> ** OS[ir,false,si,true::ci] ** ATopis (gettopis si) **
            invlth_isr (V293_time_shared_inv bn) 0 (gettopis si) **
            V293_time_shared_locals now ticks saved bn bt bs (Vint32 clock) save frame)
          (q:=<||aop||> ** OS[ir,true,si,ci] **
            V293_time_shared_locals now ticks saved bn bt bs (Vint32 clock) save frame).
        -- intros s H.
           assert (P : s |= (Aisr ir ** V293_time_shared_core bn) **
            (<||aop||> ** (Aie false ** (Ais si ** (Acs (true::ci) **
              V293_time_shared_locals now ticks saved bn bt bs (Vint32 clock) save frame))))) by (sep auto).
           eapply astar_mono in P;[ | apply V293_time_irq_close_asrt;exact Clear | intros st H0;exact H0].
           clear H. rename P into H.
           assert (S : s |= Ais si ** Atrue) by (sep auto).
           pose proof (V293_time_topis si Atrue s S) as Top.
           apply astar_l_atopis_elim in Top. destruct Top as [Top _].
           pose proof (@astar_l_atopis_intro s (gettopis si) _ H Top) as HT.
           clear H. rename HT into H. sep auto.
        -- intros s H;sep auto.
        -- apply excrit1_rule;[apply V293_time_locals_good;exact GF | apply V293_time_locals_inv;exact Inv].
Qed.

(* Stable getter body interface. Entry owns no clock byte and contains no
   fixed expected time. The snapshot is chosen only after IRQ ownership opens.
   IE=false/nested entry and abstract API result refinement remain open. *)
Theorem V293_OSTimeGet_shared_body : forall Spec sd li tid aop ir si ci
    now ticks saved bn bt bs tmp save frame,
  (forall i, ir i=false) -> (gettopis si <= INUM)%nat ->
  GoodFrm frame -> (frame ==> CurLINV li tid) ->
  InfRules Spec sd li (V293_time_shared_inv bn)
    (fun result => EX clock : int32, [| result = Some (Vint32 clock) |] **
      (<||aop||> ** OS[ir,true,si,ci] **
        V293_time_shared_locals now ticks saved bn bt bs (Vint32 clock) (Vint32 Int.zero) frame))
    Afalse
    (<||aop||> ** OS[ir,true,si,ci] **
      V293_time_shared_locals now ticks saved bn bt bs tmp save frame)
    (V293_TimeGet_body now ticks saved) Afalse tid.
Proof.
  intros Spec sd li tid aop ir si ci now ticks saved bn bt bs tmp save frame Clear Bound GF Inv.
  unfold V293_TimeGet_body.
  eapply seq_rule with (p':=<||aop||> ** OS[ir,true,si,ci] **
    V293_time_shared_locals now ticks saved bn bt bs tmp (Vint32 Int.zero) frame).
  - eapply conseq_rule;[ | | apply (V293_time_zero _ _ _ _ _ _ _ aop
      (V293_time_binding false now bn ** (V293_time_cell true ticks bt tmp **
        (frame ** OS[ir,true,si,ci]))) saved bs save)].
    + unfold V293_time_shared_locals. intros s H;sep auto.
    + unfold V293_time_shared_locals. intros s H;sep auto.
    + eapply V293_star_CurLINV_r. eapply V293_star_CurLINV_r.
      eapply V293_star_CurLINV_l;exact Inv.
  - eapply seq_rule with (p':=EX clock : int32, <||aop||> ** OS[ir,true,si,ci] **
      V293_time_shared_locals now ticks saved bn bt bs (Vint32 clock) (Vint32 Int.zero) frame).
    + apply V293_time_shared_critical_get;assumption.
    + apply ex_intro_rule. intro clock.
      eapply rete_rule with (v:=Vint32 clock) (t:=Tint32).
      intros s LocalSnapshot. split.
      * exists clock. apply astar_l_apure_intro;[exact LocalSnapshot | reflexivity].
      * assert (C : s |= V293_time_cell true ticks bt (Vint32 clock) ** Atrue).
        { unfold V293_time_shared_locals in LocalSnapshot. clear -LocalSnapshot. sep auto. }
        destruct (V293_time_cell_read true ticks bt clock Atrue s C) as [Value Ty].
        split;[exact Value | split;[exact Ty | discriminate]].
Qed.

(* The integrated witness is a real agreement, not two independent existentials. *)
Theorem V293_time_shared_clock_agreement : forall bn ge le M ir aux O op,
  (ge,le,M,ir,aux,O,op) |= V293_time_shared_core bn ->
  exists clock, get O ostmid = Some (ostm clock) /\
    load Tint32 M (bn,0%Z) = Some (Vint32 clock).
Proof.
  intros bn ge le M ir aux O op [clock H]. exists clock. split.
  - change (get (getabst (ge,le,M,ir,aux,O,op)) ostmid = Some (ostm clock)).
    eapply V293_star_abst_get_l;[apply V293_time_fields_clock | exact H].
  - change (load Tint32 (getmem (ge,le,M,ir,aux,O,op)) (bn,0%Z) = Some (Vint32 clock)).
    eapply V293_star_load_r;[ | exact H]. intros st [Points _].
    eapply mapstoval_load;[reflexivity | exact Points].
Qed.
Print Assumptions V293_time_core_precise.
Print Assumptions V293_OSTimeGet_shared_body.
Print Assumptions V293_time_shared_clock_agreement.
