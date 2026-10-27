(* Full-write physical storage is part of the switch invariant, not Px.
   Values are existential after resumption. This does NOT establish the ready
   bitmap/TCB relation or a port implementation for OSPrioCur. *)
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitchPre.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.sep_combine_lemmas.
Require Import Coq.Lists.List Lia Coq.Logic.Classical_Prop.
Local Open Scope nat_scope.

Require Import CertiOS.certiucos.v293.proofs.V293DispatchState.

Definition V293_storage_cell (a : addr) (tau : type) :=
  EX v : val, [|rule_type_val_match tau v = true|] ** Amapsto a tau true v.
Fixpoint V293_storage (cells : list (addr * type)) : asrt :=
  match cells with
  | nil => Aemp
  | (a, tau) :: rest => V293_storage_cell a tau ** V293_storage rest
  end.
Lemma V293_storage_cell_precise : forall a tau, precise (V293_storage_cell a tau).
Proof.
  intros a tau s M1 M2 O1 O2 [v1 H1] [v2 H2] M O HM1 HM2 HO1 HO2.
  apply astar_l_apure_elim in H1. destruct H1 as [T1 P1].
  apply astar_l_apure_elim in H2. destruct H2 as [T2 P2].
  destruct s as [[[[[[ge le] mem] ir] aux] o] op].
  change (mapstoval a tau true v1 M1 /\ O1 = emp) in P1.
  change (mapstoval a tau true v2 M2 /\ O2 = emp) in P2.
  destruct P1 as [P1 E1]. destruct P2 as [P2 E2].
  pose proof (@mapstoval_load _ _ _ _ _ T1 P1) as L1.
  pose proof (@mapstoval_load _ _ _ _ _ T2 P2) as L2.
  pose proof (@load_mem_mono _ _ _ _ _ L1 HM1) as LM1.
  pose proof (@load_mem_mono _ _ _ _ _ L2 HM2) as LM2.
  assert (v1 = v2) by congruence. subst v2. split; [ | congruence].
  destruct P1 as [vl1 [V1 P1]]. destruct P2 as [vl2 [V2 P2]].
  rewrite <- V1 in P1. rewrite <- V2 in P2. eapply ptomvallist_mem_eq; eauto.
Qed.
Lemma V293_storage_precise : forall cells, precise (V293_storage cells).
Proof.
  induction cells as [ | [a tau] rest IH]; simpl.
  - intros s M1 M2 O1 O2 H1 H2 M O HM1 HM2 HO1 HO2.
    destruct s as [[[[[[ge le] mem] ir] aux] o] op].
    change (M1 = emp /\ O1 = emp) in H1.
    change (M2 = emp /\ O2 = emp) in H2. intuition congruence.
  - apply precise_star; [apply V293_storage_cell_precise | exact IH].
Qed.
Lemma V293_storage_good : forall cells, GoodInvAsrt (V293_storage cells).
Proof.
  induction cells as [ | [a tau] rest IH]; simpl; [exact I | ].
  unfold V293_storage_cell. simpl. auto.
Qed.
Lemma V293_storage_aux_stable : forall cells ge le M ir aux O op ir' aux',
  (ge, le, M, ir, aux, O, op) |= V293_storage cells ->
  (ge, le, M, ir', aux', O, op) |= V293_storage cells.
Proof.
  induction cells as [ | [a tau] rest IH]; intros; [exact H | ].
  cbn [V293_storage] in H |- *.
  apply sat_split in H. destruct H as (m1 & m2 & o1 & o2 & JM & JO & HC & HR).
  apply sat_split'. exists m1. exists m2. exists o1. exists o2.
  split; [exact JM | ]. split; [exact JO | ]. split; [exact HC | ].
  eapply IH; exact HR.
Qed.
Section SharedStorage.
Variable cells : list (addr * type).
Lemma V293_storage_core_aux_stable : forall target tp ge le M ir aux O op ir' aux',
  (ge, le, M, ir, aux, O, op) |= V293_shared_core ** (V293_dispatch_cell target tp ** V293_storage cells) ->
  (ge, le, M, ir', aux', O, op) |= V293_shared_core ** (V293_dispatch_cell target tp ** V293_storage cells).
Proof.
  intros. apply sat_split in H. destruct H as (m1 & m2 & o1 & o2 & JM & JO & HC & HR).
  apply sat_split'. exists m1. exists m2. exists o1. exists o2.
  split; [exact JM | ]. split; [exact JO | ]. split; [exact HC | ].
  apply sat_split in HR. destruct HR as (m3 & m4 & o3 & o4 & JM2 & JO2 & HT & HS).
  apply sat_split'. exists m3. exists m4. exists o3. exists o4.
  split; [exact JM2 | ]. split; [exact JO2 | ]. split; [exact HT | ].
  eapply V293_storage_aux_stable; exact HS.
Qed.
Definition V293_storage_core target tp := V293_shared_core ** (V293_dispatch_cell target tp ** V293_storage cells).
Definition V293_storage_inv (target : var) (tp : type) : Inv.
Proof.
  intro k. destruct k.
  - refine (@mkinvasrt (V293_storage_core target tp) _ _).
    + unfold V293_storage_core, V293_shared_core, V293_shared_fields, V293_dispatch_cell,
        CurTid, Agvarmapsto, Aptrmapsto. simpl. intros. repeat split; auto using V293_storage_good.
    + split.
      * apply precise_star; [apply V293_shared_core_precise | apply precise_star; [apply V293_dispatch_cell_precise | apply V293_storage_precise]].
      * unfold assertion.inv_isr_prop. repeat split; intros;
          destruct s as [[[[[[ge le] M] ir] [[ie si] cs]] O] op];
          eapply V293_storage_core_aux_stable; exact H.
  - exact (V293_shared_inv (S k)).
Defined.
Lemma V293_storage_noisr_tail : forall target tp n k,
  starinv_noisr (V293_storage_inv target tp) (S k) n <==> Aemp.
Proof.
  intros target tp n. induction n; intros k s; simpl starinv_noisr; [reflexivity | ].
  split; intro Hs.
  - apply astar_l_aemp_elim in Hs. apply IHn in Hs. exact Hs.
  - apply astar_l_aemp_intro. apply IHn. exact Hs.
Qed.
Lemma V293_storage_noisr_core : forall target tp n,
  starinv_noisr (V293_storage_inv target tp) 0 n <==> V293_storage_core target tp.
Proof.
  intros target tp [ | n] s; [reflexivity | ].
  split; intro Hs.
  - apply astar_r_aemp_elim. eapply astar_mono; [intros st H; exact H | intros st H; apply V293_storage_noisr_tail in H; exact H | exact Hs].
  - eapply astar_mono; [intros st H; exact H | intros st H; apply V293_storage_noisr_tail; exact H | ].
    apply astar_r_aemp_intro. exact Hs.
Qed.
Lemma V293_storage_switch_open : forall target tp,
  SWINV (V293_storage_inv target tp) ==>
  V293_shared_flags ** V293_storage_core target tp.
Proof.
  intros target tp s Hs. destruct s as [[[[[[ge le] M] ir] aux] O] op].
  assert (HC : forall i, ir i = false).
  { eapply (V293_shared_clear_state ge le M ir aux O op). unfold SWINV in Hs. sep auto. }
  unfold SWINV in Hs. apply sat_split in Hs.
  destruct Hs as (m1 & m2 & o1 & o2 & JM & JO & HF & k & HK).
  apply sat_split in HK. destruct HK as (m3 & m4 & o3 & o4 & JM2 & JO2 & HT & HI).
  unfold invlth_isr in HI. rewrite Nat.sub_0_r in HI.
  apply invisr_imply_noisr' in HI; [ | intros; apply HC]. apply V293_storage_noisr_core in HI.
  assert (HP : (ge, le, M, ir, aux, O, op) |= (isrclr ** Aie false) ** (ATopis k ** V293_storage_core target tp)).
  { apply sat_split'. exists m1. exists m2. exists o1. exists o2.  repeat first [assumption | split].
    apply sat_split'. exists m3. exists m4. exists o3. exists o4.  repeat first [assumption | split]. }
  unfold V293_shared_flags. sep auto.
Qed.
Lemma V293_storage_switch_close : forall target tp,
  V293_shared_flags ** V293_storage_core target tp ==> SWINV (V293_storage_inv target tp).
Proof.
  intros target tp s Hs. destruct s as [[[[[[ge le] M] ir] aux] O] op].
  assert (HC : forall i, ir i = false).
  { eapply (V293_shared_clear_state ge le M ir aux O op). unfold V293_shared_flags in Hs. sep auto. }
  unfold V293_shared_flags in Hs. sep normal in Hs. sep destruct Hs.
  assert (HP : (ge, le, M, ir, aux, O, op) |= (isrclr ** Aie false) ** (ATopis x ** V293_storage_core target tp)) by (sep auto).
  apply sat_split in HP. destruct HP as (m1 & m2 & o1 & o2 & JM & JO & HF & HK).
  apply sat_split in HK. destruct HK as (m3 & m4 & o3 & o4 & JM2 & JO2 & HT & HI).
  apply (proj2 (V293_storage_noisr_core target tp x _)) in HI.
  apply V293_shared_clear_noisr_close in HI; [ | exact HC].
  unfold SWINV.
  apply sat_split'. exists m1. exists m2. exists o1. exists o2.  repeat first [assumption | split].
  exists x. unfold invlth_isr. rewrite Nat.sub_0_r. apply sat_split'. exists m3. exists m4. exists o3. exists o4.  repeat first [assumption | split].
Qed.
Definition V293_storage_full target tp t := EX ts : TcbMod.map, EX es : EcbMod.map, EX n : int32,
  (EX ct : type, GV OSTCBCur @ (Tptr ct) |-> (Vptr t)) **
    (V293_shared_fields t ts es n ** (V293_dispatch_cell target tp ** V293_storage cells)).
Lemma V293_storage_switch_full : forall target tp t,
  SWINVt (V293_storage_inv target tp) t ==> V293_shared_flags ** V293_storage_full target tp t.
Proof.
  intros target tp t s Hs. unfold SWINVt in Hs.
  eapply astar_mono in Hs; [ | apply V293_storage_switch_open | intros st H; exact H].
  unfold V293_storage_core, V293_shared_core in Hs. sep normal in Hs. sep destruct Hs.
  assert (HC : s |= CurTid t ** (CurTid x **
    (V293_shared_fields x x0 x1 x2 ** (V293_shared_flags ** (V293_dispatch_cell target tp ** V293_storage cells))))).
  { unfold CurTid at 1. apply astar_l_aexists_intro. exists x3. sep auto. }
  clear Hs. rename HC into Hs.
  assert (E : x = t).
  { eapply (V293_shared_current_agree x t (V293_shared_flags ** (V293_shared_fields x x0 x1 x2 ** (V293_dispatch_cell target tp ** V293_storage cells))) s). sep auto. } subst x.
  assert (HP : s |= (CurTid t ** CurTid t) **
    (V293_shared_flags ** (V293_shared_fields t x0 x1 x2 ** (V293_dispatch_cell target tp ** V293_storage cells)))) by (sep auto).
  eapply astar_mono in HP; [ | apply V293_current_halves_write | intros st H; exact H].
  unfold V293_storage_full. clear Hs. sep auto.
Qed.
Lemma V293_storage_switch_halves : forall target tp t,
  V293_shared_flags ** V293_storage_full target tp t ==> SWINVt (V293_storage_inv target tp) t.
Proof.
  intros target tp t s Hs. unfold V293_storage_full in Hs. sep normal in Hs. sep destruct Hs.
  assert (HP : s |= (GV OSTCBCur @ (Tptr x2) |-> (Vptr t)) **
    (V293_shared_flags ** (V293_shared_fields t x x0 x1 ** (V293_dispatch_cell target tp ** V293_storage cells)))) by (unfold CurTid in *; sep auto).
  eapply astar_mono in HP; [ | apply GV_separate_rw | intros st H; exact H].
  unfold SWINVt. apply astar_mono with (P := V293_shared_flags ** V293_storage_core target tp) (Q := CurTid t).
  - apply V293_storage_switch_close.
  - intros st H; exact H.
  - unfold V293_storage_core, V293_shared_core, CurTid. clear Hs. sep auto.
Qed.
Lemma V293_storage_store : forall target tq ct t ge le M M' ir aux O op b tp,
  (ge, le, M, ir, aux, O, op) |= SWINVt (V293_storage_inv target tq) ct ->
  get ge OSTCBCur = Some (b, Tptr tp) ->
  store (Tptr tp) M (b, 0%Z) (Vptr t) = Some M' ->
  (ge, le, M', ir, aux, set O curtid (oscurt t), op) |= SWINVt (V293_storage_inv target tq) t.
Proof.
  intros target tq ct t ge le M M' ir aux O op b tp Hs GE HS.
  apply V293_storage_switch_full in Hs. unfold V293_storage_full in Hs. sep normal in Hs. sep destruct Hs.
  assert (HP : (ge, le, M, ir, aux, O, op) |= (GV OSTCBCur @ (Tptr x2) |-> (Vptr ct)) **
    (V293_shared_flags ** (V293_shared_fields ct x x0 x1 ** (V293_dispatch_cell target tq ** V293_storage cells)))) by (sep auto).
  assert (ET : x2 = tp).
  { pose proof (@V293_star_env_l _ _ (fun ge _ => exists b, get ge OSTCBCur = Some (b, Tptr x2))
      (fun st H => V293_global_cell_type OSTCBCur (Tptr x2) true (Vptr ct) st H) _ HP) as [b0 G].
    change (get ge OSTCBCur = Some (b0, Tptr x2)) in G. congruence. } subst x2.
  pose proof (V293_shared_store_global _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP GE HS) as Hstored.
  assert (HN : (ge, le, M', ir, aux, O, op) |= Aabsdata curtid (oscurt ct) **
    ((GV OSTCBCur @ (Tptr tp) |-> (Vptr t)) ** (V293_shared_flags **
      ((Aabsdata abstcblsid (abstcblist x) **
        (Aabsdata absecblsid (absecblist x0) ** Aabsdata ostmid (ostm x1))) ** (V293_dispatch_cell target tq ** V293_storage cells))))).
  { unfold V293_shared_fields in Hstored. clear HP Hs. sep auto. }
  apply V293_shared_replace_slot with (new := oscurt t) in HN.
  apply V293_storage_switch_halves. unfold V293_storage_full, V293_shared_fields. clear Hs HP Hstored. sep auto.
Qed.
Theorem V293_storage_invariant_good : forall target tp,
  GoodI (V293_storage_inv target tp) V293_scheduler V293_shared_li.
Proof.
  intros target tp. split.
  - intros o O Of op OO Hs JO. apply V293_storage_noisr_core in Hs.
    eapply (V293_shared_no_abstract_frame (o, O, op) Of OO); [unfold V293_storage_core in Hs; sep auto | exact JO].
  - split.
    + intros o O op t Hs. destruct o as [[[[ge le] M] ir] aux].
      assert (HP : (ge, le, M, ir, aux, O, op) |= CurTid t ** Atrue).
      { change ((ge, le, M, ir, aux, O, op) |= SWINV (V293_storage_inv target tp) ** CurTid t) in Hs. sep auto. }
      destruct (V293_shared_current_read _ _ _ _ _ _ _ _ _ HP) as [b [ct [GE LD]]].
      exists b. exists ct.  split; [exact GE | ]. split; [exact LD | ].
      apply V293_storage_switch_full in Hs. unfold V293_storage_full in Hs. sep normal in Hs. sep destruct Hs.
      change (get (getabst (ge, le, M, ir, aux, O, op)) curtid = Some (oscurt t)).
      eapply V293_star_abst_get_l with (p := Aabsdata curtid (oscurt t)) (q := Atrue).
      * apply V293_shared_abs_get.
      * unfold V293_shared_fields in Hs. clear HP. sep auto.
    + split.
      * intros o O op t b ct M' current Hs Hhighest GE HS. destruct o as [[[[ge le] M] ir] aux].
        assert (HT : exists ts, get O abstcblsid = Some (abstcblist ts)).
        { apply V293_storage_switch_full in Hs. unfold V293_storage_full in Hs. sep normal in Hs. sep destruct Hs.
          exists x. change (get (getabst (ge, le, M, ir, aux, O, op)) abstcblsid = Some (abstcblist x)).
          eapply V293_star_abst_get_l with (p := Aabsdata abstcblsid (abstcblist x)) (q := Atrue).
          - apply V293_shared_abs_get.
          - unfold V293_shared_fields in Hs. sep auto. }
        destruct HT as [ts HT]. exists ts. split; [exact HT | ].
        pose proof (V293_storage_store _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hs GE HS) as Hnew.
        destruct (classic (indom ts current)) as [Hm | Hm].
        -- left. split; assumption.
        -- right. split; [exact Hm | ]. intros Mx Ox MM OO HL JM JO.
           specialize (HL op). destruct HL as [lg HL]. change (Mx = emp /\ Ox = emp) in HL.
           destruct HL as [EM EO]. subst Mx Ox. apply map_join_emp' in JM. apply map_join_emp' in JO. subst MM OO. exact Hnew.
      * apply V293_scheduler_good.
Qed.

End SharedStorage.
