(* Ownership checkpoint for the shared abstract-state/pointer core only.
   No ready bitmap, priority array, physical TCB/event layout or initialization
   is asserted here. The empty local invariant is an explicit fixture. *)
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitchPre.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.sep_combine_lemmas.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import Coq.Lists.List Lia Coq.Logic.Classical_Prop.
Local Open Scope nat_scope.

Definition V293_shared_fields (current : tid) (tasks : TcbMod.map) (events : EcbMod.map) (now : int32) :=
  Aabsdata curtid (oscurt current) **
  (Aabsdata abstcblsid (abstcblist tasks) **
    (Aabsdata absecblsid (absecblist events) ** Aabsdata ostmid (ostm now))).
Definition V293_shared_core := EX current : tid, EX tasks : TcbMod.map,
  EX events : EcbMod.map, EX now : int32,
  CurTid current ** V293_shared_fields current tasks events now.

Lemma V293_shared_abs_get : forall id v s, s |= Aabsdata id v -> get (getabst s) id = Some v.
Proof. intros id v s [E _]. rewrite <- E. apply map_get_sig. Qed.

Lemma V293_shared_fields_get : forall current tasks events now s,
  s |= V293_shared_fields current tasks events now ->
  get (getabst s) curtid = Some (oscurt current) /\
  get (getabst s) abstcblsid = Some (abstcblist tasks) /\
  get (getabst s) absecblsid = Some (absecblist events) /\
  get (getabst s) ostmid = Some (ostm now).
Proof.
  intros current tasks events now s Hs. unfold V293_shared_fields in Hs. repeat split.
  - eapply V293_star_abst_get_l; [apply V293_shared_abs_get | exact Hs].
  - eapply V293_star_abst_get_r; [ | exact Hs]. apply V293_star_abst_get_l. apply V293_shared_abs_get.
  - eapply V293_star_abst_get_r; [ | exact Hs]. apply V293_star_abst_get_r. apply V293_star_abst_get_l. apply V293_shared_abs_get.
  - eapply V293_star_abst_get_r; [ | exact Hs]. apply V293_star_abst_get_r. apply V293_star_abst_get_r. apply V293_shared_abs_get.
Qed.

Lemma V293_shared_abs_precise : forall id v, precise (Aabsdata id v).
Proof.
  intros id v s M1 M2 o1 o2 H1 H2 M O Hm1 Hm2 Ho1 Ho2.
  destruct s as [[[[[[ge le] mem] ir] aux] o] op].
  change (sig id v = o1 /\ M1 = emp) in H1.
  change (sig id v = o2 /\ M2 = emp) in H2. intuition congruence.
Qed.
Lemma V293_shared_fields_precise : forall current tasks events now,
  precise (V293_shared_fields current tasks events now).
Proof. intros. unfold V293_shared_fields. apply precise_star; [apply V293_shared_abs_precise | ]. apply precise_star; [apply V293_shared_abs_precise | ]. apply precise_star; apply V293_shared_abs_precise. Qed.
Lemma V293_shared_current_precise : forall t, precise (CurTid t).
Proof.
  intros t s M1 M2 o1 o2 H1 H2 M O Hm1 Hm2 Ho1 Ho2.
  destruct s as [[[[[[ge le] mem] ir] aux] o] op].
  eapply curtid_exact; eassumption.
Qed.
Lemma V293_shared_core_precise : precise V293_shared_core.
Proof.
  intros s M1 M2 O1 O2 [t1 [ts1 [es1 [n1 H1]]]] [t2 [ts2 [es2 [n2 H2]]]] M O HM1 HM2 HO1 HO2.
  destruct s as [[[[[[ge le] mem] ir] aux] oldO] op].
  assert (K1 : get O curtid = Some (oscurt t1) /\ get O abstcblsid = Some (abstcblist ts1) /\
    get O absecblsid = Some (absecblist es1) /\ get O ostmid = Some (ostm n1)).
  { pose proof (@V293_star_abst_get_r _ _ curtid _ (fun st H => proj1 (V293_shared_fields_get _ _ _ _ st H)) _ H1) as Hc.
    pose proof (@V293_star_abst_get_r _ _ abstcblsid _ (fun st H => proj1 (proj2 (V293_shared_fields_get _ _ _ _ st H))) _ H1) as Ht.
    pose proof (@V293_star_abst_get_r _ _ absecblsid _ (fun st H => proj1 (proj2 (proj2 (V293_shared_fields_get _ _ _ _ st H)))) _ H1) as He.
    pose proof (@V293_star_abst_get_r _ _ ostmid _ (fun st H => proj2 (proj2 (proj2 (V293_shared_fields_get _ _ _ _ st H)))) _ H1) as Hn.
    destruct HO1 as [F J]. repeat split; eapply OSAbstMod.join_get_l; eauto. }
  assert (K2 : get O curtid = Some (oscurt t2) /\ get O abstcblsid = Some (abstcblist ts2) /\
    get O absecblsid = Some (absecblist es2) /\ get O ostmid = Some (ostm n2)).
  { pose proof (@V293_star_abst_get_r _ _ curtid _ (fun st H => proj1 (V293_shared_fields_get _ _ _ _ st H)) _ H2) as Hc.
    pose proof (@V293_star_abst_get_r _ _ abstcblsid _ (fun st H => proj1 (proj2 (V293_shared_fields_get _ _ _ _ st H))) _ H2) as Ht.
    pose proof (@V293_star_abst_get_r _ _ absecblsid _ (fun st H => proj1 (proj2 (proj2 (V293_shared_fields_get _ _ _ _ st H)))) _ H2) as He.
    pose proof (@V293_star_abst_get_r _ _ ostmid _ (fun st H => proj2 (proj2 (proj2 (V293_shared_fields_get _ _ _ _ st H)))) _ H2) as Hn.
    destruct HO2 as [F J]. repeat split; eapply OSAbstMod.join_get_l; eauto. }
  destruct K1 as [C1 [T1 [E1 N1]]]. destruct K2 as [C2 [T2 [E2 N2]]].
  assert (t1 = t2) by congruence. assert (ts1 = ts2) by congruence.
  assert (es1 = es2) by congruence. assert (n1 = n2) by congruence. subst.
  eapply precise_star; [apply V293_shared_current_precise | apply V293_shared_fields_precise | exact H1 | exact H2 | exact HM1 | exact HM2 | exact HO1 | exact HO2].
Qed.
Lemma V293_shared_core_good : GoodInvAsrt V293_shared_core.
Proof. unfold V293_shared_core, CurTid, Agvarmapsto, Aptrmapsto, V293_shared_fields. simpl. intros. repeat split; auto. Qed.
Lemma V293_shared_core_isr : assertion.inv_isr_prop V293_shared_core.
Proof.
  unfold assertion.inv_isr_prop. repeat split; intros; destruct s as [[[[[[ge le] M] ir] [[ie si] cs]] O] op]; exact H.
Qed.
Definition V293_shared_inv : Inv.
Proof.
  intro k. destruct k.
  - exact (mkinvasrt V293_shared_core_good (conj V293_shared_core_precise V293_shared_core_isr)).
  - refine (@mkinvasrt Aemp Logic.I _). split.
    + intros s M1 M2 O1 O2 H1 H2 M O HM1 HM2 HO1 HO2.
      destruct s as [[[[[[ge le] mem] ir] aux] o] op].
      change (M1 = emp /\ O1 = emp) in H1. change (M2 = emp /\ O2 = emp) in H2. intuition congruence.
    + unfold assertion.inv_isr_prop. repeat split; intros; destruct s as [[[[[[ge le] M] ir] [[ie si] cs]] O] op]; exact H.
Defined.

Lemma V293_shared_noisr_tail : forall n k, starinv_noisr V293_shared_inv (S k) n <==> Aemp.
Proof.
  induction n; intros k s; simpl starinv_noisr; [reflexivity | ].
  change (s |= Aemp ** starinv_noisr V293_shared_inv (S (S k)) n <-> s |= Aemp).
  split; intro Hs.
  - apply astar_l_aemp_elim in Hs. apply IHn in Hs. exact Hs.
  - apply astar_l_aemp_intro. apply IHn. exact Hs.
Qed.
Lemma V293_shared_noisr_core : forall n, starinv_noisr V293_shared_inv 0 n <==> V293_shared_core.
Proof.
  intros [ | n] s; [reflexivity | ].
  change (s |= V293_shared_core ** starinv_noisr V293_shared_inv 1 n <-> s |= V293_shared_core).
  split; intro Hs.
  - apply astar_r_aemp_elim. eapply astar_mono; [intros st H; exact H | intros st H; apply V293_shared_noisr_tail in H; exact H | exact Hs].
  - eapply astar_mono; [intros st H; exact H | intros st H; apply V293_shared_noisr_tail; exact H | ]. apply astar_r_aemp_intro. exact Hs.
Qed.

Lemma V293_shared_clear_noisr_close : forall n low I ge le M ir aux O op,
  (forall i, ir i = false) ->
  (ge, le, M, ir, aux, O, op) |= starinv_noisr I low n ->
  (ge, le, M, ir, aux, O, op) |= starinv_isr I low n.
Proof.
  induction n; intros low I ge le M ir aux O op Hclear Hs.
  - exists ir. right.
    exists (emp : mem). exists M. exists M. exists (emp : osabst). exists O. exists O.
    repeat first [assumption | reflexivity | solve [apply map_join_comm; apply map_join_emp] | split | apply Hclear].
  - apply sat_split in Hs. destruct Hs as [m1 [m2 [o1 [o2 [JM [JO [H1 H2]]]]]]].
    apply sat_split'. exists m1. exists m2. exists o1. exists o2. repeat first [assumption | split].
    + exists ir. right. exists (emp : mem). exists m1. exists m1. exists (emp : osabst). exists o1. exists o1.
      repeat first [assumption | reflexivity | solve [apply map_join_comm; apply map_join_emp] | split | apply Hclear].
    + eapply IHn; eauto.
Qed.

Lemma V293_shared_clear_state : forall ge le M ir aux O op,
  (ge, le, M, ir, aux, O, op) |= isrclr ** Atrue -> forall i, ir i = false.
Proof.
  intros ge le M ir aux O op Hs. apply sat_split in Hs.
  destruct Hs as [m1 [m2 [o1 [o2 [JM [JO [[r [[E _] [HC _]]] Htrue]]]]]]].
  simpl in E. subst r. exact HC.
Qed.

Definition V293_shared_flags := (isrclr ** Aie false) ** (EX k : hid, ATopis k).
Lemma V293_shared_switch_open : SWINV V293_shared_inv ==> V293_shared_flags ** V293_shared_core.
Proof.
  intros s Hs. destruct s as [[[[[[ge le] M] ir] aux] O] op].
  assert (Hclear : forall i, ir i = false).
  { eapply (V293_shared_clear_state ge le M ir aux O op). unfold SWINV in Hs. sep auto. }
  unfold SWINV in Hs. apply sat_split in Hs.
  destruct Hs as [m1 [m2 [o1 [o2 [JM [JO [HC [k HK]]]]]]]].
  apply sat_split in HK. destruct HK as [m3 [m4 [o3 [o4 [JM2 [JO2 [HT HI]]]]]]].
  unfold invlth_isr in HI. rewrite Nat.sub_0_r in HI.
  apply invisr_imply_noisr' in HI; [ | intros; apply Hclear].
  apply V293_shared_noisr_core in HI.
  assert (Hpack : (ge, le, M, ir, aux, O, op) |=
    (isrclr ** Aie false) ** (ATopis k ** V293_shared_core)).
  { apply sat_split'. exists m1. exists m2. exists o1. exists o2. repeat first [assumption | split].
    apply sat_split'. exists m3. exists m4. exists o3. exists o4. repeat first [assumption | split]. }
  unfold V293_shared_flags. sep auto.
Qed.
Lemma V293_shared_switch_close : V293_shared_flags ** V293_shared_core ==> SWINV V293_shared_inv.
Proof.
  intros s Hs. destruct s as [[[[[[ge le] M] ir] aux] O] op].
  assert (Hclear : forall i, ir i = false).
  { eapply (V293_shared_clear_state ge le M ir aux O op). unfold V293_shared_flags in Hs. sep auto. }
  unfold V293_shared_flags in Hs. sep normal in Hs. sep destruct Hs.
  assert (Hpack : (ge, le, M, ir, aux, O, op) |=
    (isrclr ** Aie false) ** (ATopis x ** V293_shared_core)) by (sep auto).
  apply sat_split in Hpack. destruct Hpack as [m1 [m2 [o1 [o2 [JM [JO [HC HK]]]]]]].
  apply sat_split in HK. destruct HK as [m3 [m4 [o3 [o4 [JM2 [JO2 [HT HI]]]]]]].
  apply (proj2 (V293_shared_noisr_core x _)) in HI.
  apply V293_shared_clear_noisr_close in HI; [ | exact Hclear].
  unfold SWINV. apply sat_split'. exists m1. exists m2. exists o1. exists o2. repeat first [assumption | split].
  exists x. unfold invlth_isr. rewrite Nat.sub_0_r.
  apply sat_split'. exists m3. exists m4. exists o3. exists o4. repeat first [assumption | split].
Qed.

Lemma V293_shared_fields_core_get : forall t ts es n frame s,
  s |= (CurTid t ** V293_shared_fields t ts es n) ** frame ->
  get (getabst s) curtid = Some (oscurt t) /\
  get (getabst s) abstcblsid = Some (abstcblist ts) /\
  get (getabst s) absecblsid = Some (absecblist es) /\
  get (getabst s) ostmid = Some (ostm n).
Proof.
  intros t ts es n frame s Hs. repeat split.
  - eapply V293_star_abst_get_l; [ | exact Hs]. apply V293_star_abst_get_r. intros st H. exact (proj1 (V293_shared_fields_get _ _ _ _ st H)).
  - eapply V293_star_abst_get_l; [ | exact Hs]. apply V293_star_abst_get_r. intros st H. exact (proj1 (proj2 (V293_shared_fields_get _ _ _ _ st H))).
  - eapply V293_star_abst_get_l; [ | exact Hs]. apply V293_star_abst_get_r. intros st H. exact (proj1 (proj2 (proj2 (V293_shared_fields_get _ _ _ _ st H)))).
  - eapply V293_star_abst_get_l; [ | exact Hs]. apply V293_star_abst_get_r. intros st H. exact (proj2 (proj2 (proj2 (V293_shared_fields_get _ _ _ _ st H)))).
Qed.
Lemma V293_shared_no_abstract_frame : forall s Of OO,
  s |= V293_shared_core ** Atrue -> join (getabst s) Of OO -> Of = emp.
Proof.
  intros s Of OO Hs J. unfold V293_shared_core in Hs. sep normal in Hs. sep destruct Hs.
  assert (Hp : s |= (CurTid x ** V293_shared_fields x x0 x1 x2) ** Atrue) by (sep auto).
  pose proof (V293_shared_fields_core_get _ _ _ _ _ _ Hp) as [HC [HT [HE HN]]].
  apply OSAbstMod.extensionality. intro key. rewrite OSAbstMod.emp_sem. change (get Of key = None).
  destruct key; match goal with |- get Of ?key = _ => destruct (get Of key) eqn:G end.
  all: try assumption.
  all: exfalso; eapply OSAbstMod.map_join_get_some; [reflexivity | exact J | | exact G]; eassumption.
Qed.

Lemma V293_shared_current_read : forall t frame ge le M ir aux O op,
  (ge, le, M, ir, aux, O, op) |= CurTid t ** frame ->
  exists b tp, get ge OSTCBCur = Some (b, Tptr tp) /\ load (Tptr tp) M (b, 0%Z) = Some (Vptr t).
Proof.
  intros t frame ge le M ir aux O op Hs.
  assert (Hlocal : forall m o,
      (ge, le, m, ir, aux, o, op) |= CurTid t ->
      exists b tp, get ge OSTCBCur = Some (b, Tptr tp) /\ load (Tptr tp) m (b, 0%Z) = Some (Vptr t)).
  { intros m o [tp Hc]. unfold Agvarmapsto in Hc. destruct Hc as [b Hc].
    apply sat_split in Hc. destruct Hc as [m1 [m2 [o1 [o2 [JM [JO [[b0 [GE [EA [EM EO]]]] [HP HA]]]]]]]].
    simpl in *. subst m1. inversion EA; subst b0.
    exists b. exists tp. split; [exact GE | ].
    change (load (Tptr tp) m (b, 0%Z) = Some (Vptr t)).
    assert (LD : load (Tptr tp) m2 (b, 0%Z) = Some (Vptr t)).
    { eapply mapstoval_load; [reflexivity | exact HP]. }
    erewrite load_mono; [exact LD | apply map_join_comm; exact JM | exact LD]. }
  apply sat_split in Hs. destruct Hs as [m1 [m2 [o1 [o2 [JM [JO [Hc HF]]]]]]].
  destruct (Hlocal _ _ Hc) as [b [tp [GE LD]]].
  exists b. exists tp. split; [exact GE | ]. erewrite load_mono; eauto.
Qed.
Lemma V293_shared_current_agree : forall t1 t2 frame s,
  s |= (CurTid t1 ** CurTid t2) ** frame -> t1 = t2.
Proof.
  intros t1 t2 frame s Hs. destruct s as [[[[[[ge le] M] ir] aux] O] op].
  assert (H1 : (ge, le, M, ir, aux, O, op) |= CurTid t1 ** Atrue) by (sep auto).
  assert (H2 : (ge, le, M, ir, aux, O, op) |= CurTid t2 ** Atrue) by (clear H1; sep auto).
  destruct (V293_shared_current_read _ _ _ _ _ _ _ _ _ H1) as [b1 [tp1 [G1 L1]]].
  destruct (V293_shared_current_read _ _ _ _ _ _ _ _ _ H2) as [b2 [tp2 [G2 L2]]].
  assert (b1 = b2 /\ tp1 = tp2) by (split; congruence). destruct H. subst. congruence.
Qed.
Definition V293_shared_full t := EX ts : TcbMod.map, EX es : EcbMod.map, EX n : int32,
  (EX tp : type, GV OSTCBCur @ (Tptr tp) |-> (Vptr t)) ** V293_shared_fields t ts es n.
Lemma V293_shared_switch_full : forall t, SWINVt V293_shared_inv t ==> V293_shared_flags ** V293_shared_full t.
Proof.
  intros t s Hs. unfold SWINVt in Hs.
  assert (Ho : s |= (V293_shared_flags ** V293_shared_core) ** CurTid t).
  { eapply astar_mono; [apply V293_shared_switch_open | intros st H; exact H | exact Hs]. }
  clear Hs. rename Ho into Hs.
  unfold V293_shared_core in Hs. sep normal in Hs. sep destruct Hs.
  assert (E : x = t).
  { eapply (V293_shared_current_agree x t (V293_shared_flags ** V293_shared_fields x x0 x1 x2) s). sep auto. } subst x.
  assert (Hp : s |= V293_shared_flags ** ((CurTid t ** CurTid t) ** V293_shared_fields t x0 x1 x2)) by (sep auto).
  eapply astar_mono in Hp; [ | intros st H; exact H | apply astar_mono; [apply V293_current_halves_write | intros st H; exact H]].
  unfold V293_shared_full. sep auto.
Qed.
Lemma V293_shared_switch_halves : forall t, V293_shared_flags ** V293_shared_full t ==> SWINVt V293_shared_inv t.
Proof.
  intros t s Hs. unfold V293_shared_full in Hs. sep normal in Hs. sep destruct Hs.
  assert (Hp : s |= (GV OSTCBCur @ (Tptr x2) |-> (Vptr t)) **
    (V293_shared_flags ** V293_shared_fields t x x0 x1)) by (sep auto).
  eapply astar_mono in Hp; [ | apply GV_separate_rw | intros st H; exact H].
  unfold SWINVt. apply astar_mono with (P := V293_shared_flags ** V293_shared_core) (Q := CurTid t).
  - apply V293_shared_switch_close.
  - intros st H; exact H.
  - unfold V293_shared_core, CurTid. sep auto.
Qed.

Lemma V293_shared_replace_slot : forall id old new P ge le M ir aux O op,
  (ge, le, M, ir, aux, O, op) |= Aabsdata id old ** P ->
  (ge, le, M, ir, aux, set O id new, op) |= Aabsdata id new ** P.
Proof.
  intros id old new P ge le M ir aux O op Hs.
  apply sat_split in Hs. destruct Hs as (m1 & m2 & o1 & o2 & JM & JO & [E EM] & HP).
  change (sig id old = o1) in E. subst o1.
  assert (JN : join (sig id new) o2 (set O id new)).
  { change (OSAbstMod.join (OSAbstMod.sig id new) o2 (OSAbstMod.set O id new)).
    rewrite <- (OSAbstMod.set_sig id old new). eapply OSAbstMod.join_set_l; [exact JO | ]. exists old. apply OSAbstMod.get_sig_some. }
  apply sat_split'. exists m1. exists m2. exists (sig id new). exists o2.
  repeat first [assumption | split | reflexivity].
Qed.
Lemma V293_shared_store_global : forall x tp old new R ge le M M' ir aux O op b,
  (ge, le, M, ir, aux, O, op) |= (GV x @ (Tptr tp) |-> old) ** R ->
  get ge x = Some (b, Tptr tp) ->
  store (Tptr tp) M (b, 0%Z) new = Some M' ->
  (ge, le, M', ir, aux, O, op) |= (GV x @ (Tptr tp) |-> new) ** R.
Proof.
  intros x tp old new R ge le M M' ir aux O op b Hs GE HS.
  unfold Agvarmapsto in Hs. sep normal in Hs. sep destruct Hs.
  assert (EA : x0 = b).
  { apply sat_split in Hs. destruct Hs as [ma [mb [oa [ob [JM [JO [[b0 [G [E _]]] HP]]]]]]].
    simpl in *. assert (b0 = b) by congruence. subst b0. inversion E; reflexivity. }
  subst x0.
  change ((ge, le, M, ir, aux, O, op) |=
    Agvarenv x (Tptr tp) (b, 0%Z) ** (Amapsto (b, 0%Z) (Tptr tp) true old ** R)) in Hs.
  assert (Hp : (ge, le, M, ir, aux, O, op) |= Amapsto (b, 0%Z) (Tptr tp) true old **
    (Agvarenv x (Tptr tp) (b, 0%Z) ** R)) by (sep auto).
  apply sat_split in Hp. destruct Hp as (m1 & m2 & o1 & o2 & JM & JO & [HM HO] & HR).
  destruct (store_mapstoval_frame1 m1 m2 M M' (b, 0%Z) (Tptr tp) old new HM JM HS) as [m1' [HM' [HS' JM']]].
  assert (HN : (ge, le, M', ir, aux, O, op) |= Amapsto (b, 0%Z) (Tptr tp) true new **
    (Agvarenv x (Tptr tp) (b, 0%Z) ** R)).
  { apply sat_split'. exists m1'. exists m2. exists o1. exists o2.
    repeat first [assumption | split]. }
  unfold Agvarmapsto, Agvarenv', Aptrmapsto. clear Hs HR. sep auto.
Qed.

Lemma V293_shared_store : forall ct t ge le M M' ir aux O op b tp,
  (ge, le, M, ir, aux, O, op) |= SWINVt V293_shared_inv ct ->
  get ge OSTCBCur = Some (b, Tptr tp) ->
  store (Tptr tp) M (b, 0%Z) (Vptr t) = Some M' ->
  (ge, le, M', ir, aux, set O curtid (oscurt t), op) |= SWINVt V293_shared_inv t.
Proof.
  intros ct t ge le M M' ir aux O op b tp Hs GE HS.
  apply V293_shared_switch_full in Hs. unfold V293_shared_full in Hs. sep normal in Hs. sep destruct Hs.
  assert (Hpack : (ge, le, M, ir, aux, O, op) |=
    (GV OSTCBCur @ (Tptr x2) |-> (Vptr ct)) ** (V293_shared_flags ** V293_shared_fields ct x x0 x1)) by (sep auto).
  assert (ET : x2 = tp).
  { unfold Agvarmapsto in Hpack. sep normal in Hpack. sep destruct Hpack.
    apply sat_split in Hpack. destruct Hpack as [ma [mb [oa [ob [JM [JO [[b0 [G _]] HR]]]]]]].
    change (get ge OSTCBCur = Some (b0, Tptr x2)) in G. congruence. } subst x2.
  pose proof (V293_shared_store_global _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hpack GE HS) as Hstored.
  assert (Hhead : (ge, le, M', ir, aux, O, op) |= Aabsdata curtid (oscurt ct) **
    ((GV OSTCBCur @ (Tptr tp) |-> (Vptr t)) **
      (V293_shared_flags ** (Aabsdata abstcblsid (abstcblist x) **
        (Aabsdata absecblsid (absecblist x0) ** Aabsdata ostmid (ostm x1)))))).
  { clear Hs Hpack. unfold V293_shared_fields in Hstored. sep auto. }
  apply V293_shared_replace_slot with (new := oscurt t) in Hhead.
  apply V293_shared_switch_halves. unfold V293_shared_full, V293_shared_fields. clear Hs Hpack Hstored. sep auto.
Qed.

Definition V293_shared_li : LocalInv := fun _ _ => Aemp.
Theorem V293_shared_good : GoodI V293_shared_inv V293_scheduler V293_shared_li.
Proof.
  split.
  - intros o O Of op OO Hs JO. apply V293_shared_noisr_core in Hs.
    eapply (V293_shared_no_abstract_frame (o, O, op) Of OO); [sep auto | exact JO].
  - split.
    + intros o O op t Hs. destruct o as [[[[ge le] M] ir] aux].
      assert (HP : (ge, le, M, ir, aux, O, op) |= CurTid t ** Atrue).
      { change ((ge, le, M, ir, aux, O, op) |= SWINV V293_shared_inv ** CurTid t) in Hs. sep auto. }
      destruct (V293_shared_current_read _ _ _ _ _ _ _ _ _ HP) as [b [tp [GE LD]]].
      exists b. exists tp. split; [exact GE | ]. split; [exact LD | ].
      apply V293_shared_switch_full in Hs. unfold V293_shared_full in Hs. sep normal in Hs. sep destruct Hs.
      change (get (getabst (ge, le, M, ir, aux, O, op)) curtid = Some (oscurt t)).
      eapply V293_star_abst_get_l with (p := Aabsdata curtid (oscurt t)) (q := Atrue).
      * apply V293_shared_abs_get.
      * unfold V293_shared_fields in Hs. clear HP. sep auto.
    + split.
      * intros o O op t b tp M' ct Hs Hhighest GE HS.
        destruct o as [[[[ge le] M] ir] aux].
        assert (HT : exists ts, get O abstcblsid = Some (abstcblist ts)).
        { apply V293_shared_switch_full in Hs. unfold V293_shared_full in Hs. sep normal in Hs. sep destruct Hs.
          exists x. change (get (getabst (ge, le, M, ir, aux, O, op)) abstcblsid = Some (abstcblist x)).
          eapply V293_star_abst_get_l with (p := Aabsdata abstcblsid (abstcblist x)) (q := Atrue).
          - apply V293_shared_abs_get.
          - unfold V293_shared_fields in Hs. sep auto. }
        destruct HT as [ts HT]. exists ts. split; [exact HT | ].
        pose proof (V293_shared_store _ _ _ _ _ _ _ _ _ _ _ _ Hs GE HS) as Hnew.
        destruct (classic (indom ts ct)) as [Hm | Hm].
        -- left. split; assumption.
        -- right. split; [exact Hm | ]. intros Mx Ox MM OO HL JM JO.
           specialize (HL op). destruct HL as [lg HL].
           change (Mx = emp /\ Ox = emp) in HL. destruct HL as [EM EO]. subst Mx Ox.
           apply map_join_emp' in JM. apply map_join_emp' in JO. subst MM OO. exact Hnew.
      * apply V293_scheduler_good.
Qed.
