(* Runtime coupling of one task map to its selected TCB fields, actual ready
   bytes and actual priority pointers. Not initialization or API/ISR closure. *)
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitchPre.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.certiucos.v293.code.V293OSSchedDispatch.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.sep_combine_lemmas.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import Coq.Lists.List Lia Coq.Logic.Classical_Prop.
Import ListNotations.
Local Open Scope nat_scope.

Definition V293_ready_cells br bg bp lo hi entries : list V293_record_cell :=
  [((br,0%Z),Tint8,V293_byteval lo); ((br,1%Z),Tint8,V293_byteval hi);
   ((bg,0%Z),Tint8,V293_byteval (V293_ready_group lo hi))] ++
  V293_priority_cells bp 0%Z entries.
Definition V293_ready_rel lo hi entries tasks :=
  lo < 256 /\ hi < 256 /\ (exists p, V293_bitmap_ready lo hi p) /\
  V293_bitmap_tasks lo hi tasks /\ V293_priority_table entries tasks.
Definition V293_ready_owned br bg bp tasks := EX lo : nat, EX hi : nat, EX entries : list val,
  [|V293_ready_rel lo hi entries tasks|] **
  V293_owned_record_cells (V293_ready_cells br bg bp lo hi entries).
Definition V293_ready_payload br bg bp tasks :=
  V293_owned_task_records tasks ** V293_ready_owned br bg bp tasks.

Lemma V293_priority_types_length : forall entries b offset n,
  length entries=n ->
  V293_record_types (V293_priority_cells b offset entries)=
  V293_record_types (V293_priority_cells b offset (repeat Vnull n)).
Proof.
  induction entries as [ | v entries IH]; intros b offset [ | n] Len;
    try discriminate; [reflexivity | ].
  cbn [V293_priority_cells repeat V293_record_types map]. f_equal. apply IH. cbn in Len. lia.
Qed.
Lemma V293_ready_types_length : forall br bg bp lo hi entries,
  length entries=13 ->
  V293_record_types (V293_ready_cells br bg bp lo hi entries)=
  V293_record_types (V293_ready_cells br bg bp 0 0 (repeat Vnull 13)).
Proof.
  intros. unfold V293_record_types, V293_ready_cells. rewrite !map_app. cbn [map].
  f_equal. apply V293_priority_types_length. exact H.
Qed.
Lemma V293_ready_owned_precise : forall br bg bp tasks,
  precise (V293_ready_owned br bg bp tasks).
Proof.
  intros br bg bp tasks s M1 M2 O1 O2 [lo1 [hi1 [es1 H1]]] [lo2 [hi2 [es2 H2]]]
    M O HM1 HM2 HO1 HO2.
  apply astar_l_apure_elim in H1,H2. destruct H1 as [R1 H1]. destruct H2 as [R2 H2].
  apply V293_owned_cells_storage in H1,H2.
  rewrite V293_ready_types_length in H1 by exact (proj1 (proj2 (proj2 (proj2 (proj2 R1))))).
  rewrite V293_ready_types_length in H2 by exact (proj1 (proj2 (proj2 (proj2 (proj2 R2))))).
  eapply V293_storage_precise; eassumption.
Qed.
Lemma V293_ready_owned_good : forall br bg bp tasks,
  GoodInvAsrt (V293_ready_owned br bg bp tasks).
Proof. intros. change (forall lo hi entries, True /\ GoodInvAsrt
  (V293_owned_record_cells (V293_ready_cells br bg bp lo hi entries))).
  intros. split; [exact I | apply V293_owned_cells_good]. Qed.
Lemma V293_ready_payload_precise : forall br bg bp tasks,
  precise (V293_ready_payload br bg bp tasks).
Proof. intros. apply precise_star; [apply V293_task_list_precise | apply V293_ready_owned_precise]. Qed.
Lemma V293_ready_payload_good : forall br bg bp tasks,
  GoodInvAsrt (V293_ready_payload br bg bp tasks).
Proof. intros. split; [apply V293_task_list_good | apply V293_ready_owned_good]. Qed.
Lemma V293_ready_payload_context : forall br bg bp tasks ge le M ir aux O op ge' le' ir' aux' op',
  (ge,le,M,ir,aux,O,op) |= V293_ready_payload br bg bp tasks ->
  (ge',le',M,ir',aux',O,op') |= V293_ready_payload br bg bp tasks.
Proof.
  intros. apply sat_split in H. destruct H as (m1&m2&o1&o2&JM&JO&Records&lo&hi&entries&Ready).
  apply sat_split'. exists m1. exists m2. exists o1. exists o2.
  split; [exact JM | ]. split; [exact JO | ]. split.
  - eapply V293_task_list_context; exact Records.
  - exists lo. exists hi. exists entries. apply astar_l_apure_elim in Ready.
    destruct Ready as [Rel Cells]. apply astar_l_apure_intro.
    + eapply V293_owned_cells_context; exact Cells.
    + exact Rel.
Qed.

Section RuntimeReady.
Variables br bg bp : block.
Definition V293_shared_ready_records current tasks events now :=
  (CurTid current ** V293_shared_fields current tasks events now) ** V293_ready_payload br bg bp tasks.
Definition V293_ready_core := EX current : tid, EX tasks : TcbMod.map,
  EX events : EcbMod.map, EX now : int32,
  V293_shared_ready_records current tasks events now.
Lemma V293_ready_core_precise : precise V293_ready_core.
Proof.
  intros s M1 M2 O1 O2 [t1 [ts1 [es1 [n1 H1]]]] [t2 [ts2 [es2 [n2 H2]]]]
    M O HM1 HM2 HO1 HO2.
  destruct s as [[[[[[ge le] mem] ir] aux] oldO] op].
  unfold V293_shared_ready_records in H1,H2.
  pose proof (V293_shared_fields_core_get _ _ _ _ _ _ H1) as [C1 [T1 [E1 N1]]].
  pose proof (V293_shared_fields_core_get _ _ _ _ _ _ H2) as [C2 [T2 [E2 N2]]].
  change (get O1 curtid=Some (oscurt t1)) in C1.
  change (get O2 curtid=Some (oscurt t2)) in C2.
  change (get O1 abstcblsid=Some (abstcblist ts1)) in T1.
  change (get O2 abstcblsid=Some (abstcblist ts2)) in T2.
  change (get O1 absecblsid=Some (absecblist es1)) in E1.
  change (get O2 absecblsid=Some (absecblist es2)) in E2.
  change (get O1 ostmid=Some (ostm n1)) in N1.
  change (get O2 ostmid=Some (ostm n2)) in N2.
  destruct HO1 as [F1 J1]. destruct HO2 as [F2 J2].
  change (OSAbstMod.join O1 F1 O) in J1.
  change (OSAbstMod.join O2 F2 O) in J2.
  assert (C1' : get O curtid=Some (oscurt t1)) by (eapply OSAbstMod.join_get_l; [exact J1 | exact C1]).
  assert (C2' : get O curtid=Some (oscurt t2)) by (eapply OSAbstMod.join_get_l; [exact J2 | exact C2]).
  assert (T1' : get O abstcblsid=Some (abstcblist ts1)) by (eapply OSAbstMod.join_get_l; [exact J1 | exact T1]).
  assert (T2' : get O abstcblsid=Some (abstcblist ts2)) by (eapply OSAbstMod.join_get_l; [exact J2 | exact T2]).
  assert (E1' : get O absecblsid=Some (absecblist es1)) by (eapply OSAbstMod.join_get_l; [exact J1 | exact E1]).
  assert (E2' : get O absecblsid=Some (absecblist es2)) by (eapply OSAbstMod.join_get_l; [exact J2 | exact E2]).
  assert (N1' : get O ostmid=Some (ostm n1)) by (eapply OSAbstMod.join_get_l; [exact J1 | exact N1]).
  assert (N2' : get O ostmid=Some (ostm n2)) by (eapply OSAbstMod.join_get_l; [exact J2 | exact N2]).
  assert (t1=t2) by congruence. assert (ts1=ts2) by congruence.
  assert (es1=es2) by congruence. assert (n1=n2) by congruence. subst.
  eapply precise_star; [ | apply V293_ready_payload_precise | exact H1 | exact H2 |
    exact HM1 | exact HM2 | exists F1; exact J1 | exists F2; exact J2].
  apply precise_star; [apply V293_shared_current_precise | apply V293_shared_fields_precise].
Qed.
Lemma V293_ready_core_good : GoodInvAsrt V293_ready_core.
Proof.
  change (forall t tasks events now,
    GoodInvAsrt (CurTid t ** V293_shared_fields t tasks events now) /\
    GoodInvAsrt (V293_ready_payload br bg bp tasks)).
  intros. split; [ | apply V293_ready_payload_good].
  unfold V293_shared_fields, CurTid, Agvarmapsto, Aptrmapsto. simpl. repeat split; exact I.
Qed.
Lemma V293_ready_core_aux : forall ge le M ir aux O op ir' aux',
  (ge,le,M,ir,aux,O,op) |= V293_ready_core ->
  (ge,le,M,ir',aux',O,op) |= V293_ready_core.
Proof.
  intros ge le M ir aux O op ir' aux' [t [tasks [events [now H]]]].
  exists t. exists tasks. exists events. exists now. unfold V293_shared_ready_records in *.
  apply sat_split in H. destruct H as (m1&m2&o1&o2&JM&JO&Core&Records).
  apply sat_split'. exists m1. exists m2. exists o1. exists o2. split; [exact JM | ]. split; [exact JO | ].
  split; [exact Core | eapply V293_ready_payload_context; exact Records].
Qed.
Definition V293_ready_inv : Inv.
Proof.
  intro k. destruct k.
  - refine (@mkinvasrt V293_ready_core V293_ready_core_good _). split.
    + exact V293_ready_core_precise.
    + unfold assertion.inv_isr_prop. repeat split; intros;
        destruct s as [[[[[[ge le] M] ir] [[ie si] cs]] O] op];
        eapply V293_ready_core_aux; exact H.
  - exact (V293_shared_inv (S k)).
Defined.

Lemma V293_ready_noisr_tail : forall n k,
  starinv_noisr V293_ready_inv (S k) n <==> Aemp.
Proof.
  intros n. induction n; intros k s; simpl starinv_noisr; [reflexivity | ].
  split; intro Hs.
  - apply astar_l_aemp_elim in Hs. apply IHn in Hs. exact Hs.
  - apply astar_l_aemp_intro. apply IHn. exact Hs.
Qed.
Lemma V293_ready_noisr_core : forall n,
  starinv_noisr V293_ready_inv 0 n <==> V293_ready_core.
Proof.
  intros [ | n] s; [reflexivity | ].
  split; intro Hs.
  - apply astar_r_aemp_elim. eapply astar_mono; [intros st H; exact H | intros st H; apply V293_ready_noisr_tail in H; exact H | exact Hs].
  - eapply astar_mono; [intros st H; exact H | intros st H; apply V293_ready_noisr_tail; exact H | ].
    apply astar_r_aemp_intro. exact Hs.
Qed.
Lemma V293_ready_switch_open :   SWINV V293_ready_inv ==>
  V293_shared_flags ** V293_ready_core.
Proof.
  intros s Hs. destruct s as [[[[[[ge le] M] ir] aux] O] op].
  assert (HC : forall i, ir i = false).
  { eapply (V293_shared_clear_state ge le M ir aux O op). unfold SWINV in Hs. sep auto. }
  unfold SWINV in Hs. apply sat_split in Hs.
  destruct Hs as (m1 & m2 & o1 & o2 & JM & JO & HF & k & HK).
  apply sat_split in HK. destruct HK as (m3 & m4 & o3 & o4 & JM2 & JO2 & HT & HI).
  unfold invlth_isr in HI. rewrite Nat.sub_0_r in HI.
  apply invisr_imply_noisr' in HI; [ | intros; apply HC]. apply V293_ready_noisr_core in HI.
  assert (HP : (ge, le, M, ir, aux, O, op) |= (isrclr ** Aie false) ** (ATopis k ** V293_ready_core)).
  { apply sat_split'. exists m1. exists m2. exists o1. exists o2.  repeat first [assumption | split].
    apply sat_split'. exists m3. exists m4. exists o3. exists o4.  repeat first [assumption | split]. }
  unfold V293_shared_flags. sep auto.
Qed.
Lemma V293_ready_switch_close :   V293_shared_flags ** V293_ready_core ==> SWINV V293_ready_inv.
Proof.
  intros s Hs. destruct s as [[[[[[ge le] M] ir] aux] O] op].
  assert (HC : forall i, ir i = false).
  { eapply (V293_shared_clear_state ge le M ir aux O op). unfold V293_shared_flags in Hs. sep auto. }
  unfold V293_shared_flags in Hs. sep normal in Hs. sep destruct Hs.
  assert (HP : (ge, le, M, ir, aux, O, op) |= (isrclr ** Aie false) ** (ATopis x ** V293_ready_core)) by (sep auto).
  apply sat_split in HP. destruct HP as (m1 & m2 & o1 & o2 & JM & JO & HF & HK).
  apply sat_split in HK. destruct HK as (m3 & m4 & o3 & o4 & JM2 & JO2 & HT & HI).
  apply (proj2 (V293_ready_noisr_core x _)) in HI.
  apply V293_shared_clear_noisr_close in HI; [ | exact HC].
  unfold SWINV.
  apply sat_split'. exists m1. exists m2. exists o1. exists o2.  repeat first [assumption | split].
  exists x. unfold invlth_isr. rewrite Nat.sub_0_r. apply sat_split'. exists m3. exists m4. exists o3. exists o4.  repeat first [assumption | split].
Qed.
Definition V293_ready_full t := EX tasks : TcbMod.map, EX events : EcbMod.map, EX now : int32,
  (EX tp : type, GV OSTCBCur @ (Tptr tp) |-> (Vptr t)) **
  (V293_shared_fields t tasks events now ** V293_ready_payload br bg bp tasks).
Lemma V293_ready_switch_full : forall t,
  SWINVt V293_ready_inv t ==> V293_shared_flags ** V293_ready_full t.
Proof.
  intros t s Hs. unfold SWINVt in Hs.
  assert (Ho : s |= (V293_shared_flags ** V293_ready_core) ** CurTid t).
  { eapply astar_mono; [apply V293_ready_switch_open | intros st H; exact H | exact Hs]. }
  clear Hs. rename Ho into Hs.
  unfold V293_ready_core,V293_shared_ready_records in Hs. sep normal in Hs. sep destruct Hs.
  assert (E : x=t).
  { eapply (V293_shared_current_agree x t
      (V293_shared_flags ** (V293_shared_fields x x0 x1 x2 ** V293_ready_payload br bg bp x0)) s).
    sep auto. } subst x.
  assert (Hp : s |= V293_shared_flags ** ((CurTid t ** CurTid t) **
    (V293_shared_fields t x0 x1 x2 ** V293_ready_payload br bg bp x0))) by (sep auto).
  eapply astar_mono in Hp; [ | intros st H; exact H |
    apply astar_mono; [apply V293_current_halves_write | intros st H; exact H]].
  unfold V293_ready_full. clear Hs. sep auto.
Qed.
Lemma V293_ready_switch_halves : forall t,
  V293_shared_flags ** V293_ready_full t ==> SWINVt V293_ready_inv t.
Proof.
  intros t s Hs. unfold V293_ready_full in Hs. sep normal in Hs. sep destruct Hs.
  assert (Hp : s |= (GV OSTCBCur @ (Tptr x2) |-> (Vptr t)) **
    (V293_shared_flags ** (V293_shared_fields t x x0 x1 ** V293_ready_payload br bg bp x))) by (sep auto).
  eapply astar_mono in Hp; [ | apply GV_separate_rw | intros st H; exact H].
  unfold SWINVt. apply astar_mono with (P:=V293_shared_flags ** V293_ready_core) (Q:=CurTid t).
  - apply V293_ready_switch_close.
  - intros st H; exact H.
  - unfold V293_ready_core,V293_shared_ready_records,CurTid. clear Hs. sep auto.
Qed.
Lemma V293_ready_store : forall ct t ge le M M' ir aux O op b tp,
  (ge,le,M,ir,aux,O,op) |= SWINVt V293_ready_inv ct ->
  get ge OSTCBCur=Some (b,Tptr tp) ->
  store (Tptr tp) M (b,0%Z) (Vptr t)=Some M' ->
  (ge,le,M',ir,aux,set O curtid (oscurt t),op) |= SWINVt V293_ready_inv t.
Proof.
  intros ct t ge le M M' ir aux O op b tp Hs GE HS.
  apply V293_ready_switch_full in Hs. unfold V293_ready_full in Hs.
  sep normal in Hs. sep destruct Hs.
  assert (HP : (ge,le,M,ir,aux,O,op) |= (GV OSTCBCur @ (Tptr x2) |-> (Vptr ct)) **
    (V293_shared_flags ** (V293_shared_fields ct x x0 x1 ** V293_ready_payload br bg bp x))) by (sep auto).
  assert (ET : x2=tp).
  { unfold Agvarmapsto in HP. sep normal in HP. sep destruct HP.
    apply sat_split in HP. destruct HP as (ma&mb&oa&ob&JM&JO&[b0 [G _]]&HR).
    change (get ge OSTCBCur=Some (b0,Tptr x2)) in G. congruence. } subst x2.
  pose proof (V293_shared_store_global _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP GE HS) as Stored.
  assert (HN : (ge,le,M',ir,aux,O,op) |= Aabsdata curtid (oscurt ct) **
    ((GV OSTCBCur @ (Tptr tp) |-> (Vptr t)) ** (V293_shared_flags **
      ((Aabsdata abstcblsid (abstcblist x) **
        (Aabsdata absecblsid (absecblist x0) ** Aabsdata ostmid (ostm x1))) **
        V293_ready_payload br bg bp x)))).
  { unfold V293_shared_fields in Stored. clear HP Hs. sep auto. }
  apply V293_shared_replace_slot with (new:=oscurt t) in HN.
  apply V293_ready_switch_halves. unfold V293_ready_full,V293_shared_fields.
  clear Hs HP Stored. sep auto.
Qed.
Theorem V293_ready_invariant_good : GoodI V293_ready_inv V293_scheduler V293_shared_li.
Proof.
  split.
  - intros o O Of op OO Hs JO. apply V293_ready_noisr_core in Hs.
    eapply (V293_shared_no_abstract_frame (o,O,op) Of OO);
      [unfold V293_ready_core,V293_shared_ready_records,V293_shared_core in *; sep auto | exact JO].
  - split.
    + intros o O op t Hs. destruct o as [[[[ge le] M] ir] aux].
      assert (HP : (ge,le,M,ir,aux,O,op) |= CurTid t ** Atrue).
      { change ((ge,le,M,ir,aux,O,op) |= SWINV V293_ready_inv ** CurTid t) in Hs. sep auto. }
      destruct (V293_shared_current_read _ _ _ _ _ _ _ _ _ HP) as (b&tp&GE&LD).
      exists b. exists tp. split; [exact GE | ]. split; [exact LD | ].
      apply V293_ready_switch_full in Hs. unfold V293_ready_full in Hs.
      sep normal in Hs. sep destruct Hs.
      change (get (getabst (ge,le,M,ir,aux,O,op)) curtid=Some (oscurt t)).
      eapply V293_star_abst_get_l with (p:=Aabsdata curtid (oscurt t)) (q:=Atrue).
      * apply V293_shared_abs_get.
      * unfold V293_shared_fields in Hs. clear HP. sep auto.
    + split.
      * intros o O op t b tp M' ct Hs Highest GE HS. destruct o as [[[[ge le] M] ir] aux].
        assert (HT : exists ts, get O abstcblsid=Some (abstcblist ts)).
        { apply V293_ready_switch_full in Hs. unfold V293_ready_full in Hs.
          sep normal in Hs. sep destruct Hs. exists x.
          change (get (getabst (ge,le,M,ir,aux,O,op)) abstcblsid=Some (abstcblist x)).
          eapply V293_star_abst_get_l with (p:=Aabsdata abstcblsid (abstcblist x)) (q:=Atrue).
          - apply V293_shared_abs_get.
          - unfold V293_shared_fields in Hs. sep auto. }
        destruct HT as [ts HT]. exists ts. split; [exact HT | ].
        pose proof (V293_ready_store _ _ _ _ _ _ _ _ _ _ _ _ Hs GE HS) as Hnew.
        destruct (classic (indom ts ct)) as [Live | Dead].
        -- left. split; assumption.
        -- right. split; [exact Dead | ]. intros Mx Ox MM OO HL JM JO.
           specialize (HL op). destruct HL as [lg HL].
           change (Mx=emp /\ Ox=emp) in HL. destruct HL as [EM EO]. subst Mx Ox.
           apply map_join_emp' in JM. apply map_join_emp' in JO. subst MM OO. exact Hnew.
      * apply V293_scheduler_good.
Qed.



Definition V293_ready_loads M br bg bp lo hi entries :=
  load Tint8 M (br,0%Z)=Some (V293_byteval lo) /\
  load Tint8 M (br,1%Z)=Some (V293_byteval hi) /\
  load Tint8 M (bg,0%Z)=Some (V293_byteval (V293_ready_group lo hi)) /\
  V293_table_loads V293_tcb_type M bp entries.
Lemma V293_ready_cells_loads : forall lo hi entries s,
  length entries=13 ->
  s |= V293_owned_record_cells (V293_ready_cells br bg bp lo hi entries) ->
  V293_ready_loads (getmem s) br bg bp lo hi entries.
Proof.
  intros lo hi entries s Len Owned. unfold V293_ready_loads. repeat split.
  - eapply V293_owned_record_cells_load with (cells:=V293_ready_cells br bg bp lo hi entries);
      [unfold V293_ready_cells; simpl; tauto | exact Owned].
  - eapply V293_owned_record_cells_load with (cells:=V293_ready_cells br bg bp lo hi entries);
      [unfold V293_ready_cells; simpl; tauto | exact Owned].
  - eapply V293_owned_record_cells_load with (cells:=V293_ready_cells br bg bp lo hi entries);
      [unfold V293_ready_cells; simpl; tauto | exact Owned].
  - intros p Bound. eapply V293_owned_record_cells_load with (cells:=V293_ready_cells br bg bp lo hi entries); [ | exact Owned].
    unfold V293_ready_cells. apply in_or_app. right.
    replace (4*Z.of_nat p)%Z with (0+4*Z.of_nat p)%Z by lia.
    apply V293_priority_cells_nth. lia.
Qed.
Lemma V293_ready_loads_sub : forall M Mf lo hi entries,
  Maps.sub M Mf -> V293_ready_loads M br bg bp lo hi entries ->
  V293_ready_loads Mf br bg bp lo hi entries.
Proof.
  intros M Mf lo hi entries Sub [L [H [G T]]]. unfold V293_ready_loads.
  repeat split; try (eapply load_mem_mono; eassumption).
  intros p Bound. eapply load_mem_mono; [apply T; exact Bound | exact Sub].
Qed.
Lemma V293_ready_owned_observation : forall tasks R s,
  s |= V293_ready_owned br bg bp tasks ** R ->
  exists lo hi entries, V293_ready_rel lo hi entries tasks /\
    V293_ready_loads (getmem s) br bg bp lo hi entries.
Proof.
  intros tasks R s Held. destruct s as [[[[[[ge le] M] ir] aux] O] op].
  apply sat_split in Held. destruct Held as (m1&m2&o1&o2&JM&JO&(lo&hi&entries&Owned)&Frame).
  apply astar_l_apure_elim in Owned. destruct Owned as [Rel Cells].
  exists lo. exists hi. exists entries. split; [exact Rel | ].
  eapply V293_ready_loads_sub; [exists m2; exact JM | ].
  exact (V293_ready_cells_loads lo hi entries (ge,le,m1,ir,aux,o1,op)
    (proj1 (proj2 (proj2 (proj2 (proj2 Rel)))) ) Cells).
Qed.

(* The same full caller memory supplies both TCB records and ready/table
   observations, all tied to the single owned abstract task map. *)
Theorem V293_ready_switch_sound : forall t R s,
  s |= SWINVt V293_ready_inv t ** R ->
  exists tasks lo hi entries,
    get (getabst s) abstcblsid=Some (abstcblist tasks) /\
    V293_task_records (getmem s) tasks /\ V293_ready_rel lo hi entries tasks /\
    V293_ready_loads (getmem s) br bg bp lo hi entries.
Proof.
  intros t R s Held.
  assert (Open : s |= (V293_shared_flags ** V293_ready_full t) ** R).
  { eapply astar_mono; [apply V293_ready_switch_full | intros st H; exact H | exact Held]. }
  unfold V293_ready_full in Open. sep normal in Open. sep destruct Open.
  assert (Ready : s |= V293_ready_owned br bg bp x ** Atrue).
  { unfold V293_ready_payload in Open. clear Held. sep auto. }
  destruct (V293_ready_owned_observation _ _ _ Ready) as (lo&hi&entries&Rel&Loads).
  exists x. exists lo. exists hi. exists entries. split.
  - eapply V293_star_abst_get_l with (p:=Aabsdata abstcblsid (abstcblist x)) (q:=Atrue).
    + apply V293_shared_abs_get.
    + unfold V293_shared_fields in Open. clear Held Ready. sep auto.
  - split.
    + assert (Owned : s |= V293_owned_task_records x ** Atrue).
      { unfold V293_ready_payload in Open. clear Held Ready. sep auto. }
      destruct s as [[[[[[ge le] M] ir] aux] O] op].
      apply sat_split in Owned. destruct Owned as (m1&m2&o1&o2&JM&JO&Records&Rest).
      pose proof (V293_owned_task_records_sound _ _ Records) as Sound.
      intros target priority status message Lookup.
      eapply V293_task_record_sub; [exists m2; exact JM | apply Sound; exact Lookup].
    + split; assumption.
Qed.

Theorem V293_ready_switch_selected : forall current R s,
  s |= SWINVt V293_ready_inv current ** R ->
  exists tasks lo hi entries t message,
    get (getabst s) abstcblsid=Some (abstcblist tasks) /\
    V293_ready_rel lo hi entries tasks /\
    V293_ready_loads (getmem s) br bg bp lo hi entries /\
    get tasks t=Some (Int.repr (Z.of_nat
      (V293_ready_select lo hi (V293_ready_group lo hi))),rdy,message) /\
    load (Tptr V293_tcb_type) (getmem s)
      (bp,(4*Z.of_nat (V293_ready_select lo hi (V293_ready_group lo hi))))%Z=Some (Vptr t) /\
    V293_scheduler (getabst s) t.
Proof.
  intros current R s Held.
  destruct (V293_ready_switch_sound _ _ _ Held) as (tasks&lo&hi&entries&Lookup&Records&Rel&Loads).
  destruct Rel as [Lo [Hi [Nonempty [Bitmap Table]]]].
  destruct (V293_ready_selection_task lo hi entries tasks Lo Hi Nonempty Bitmap Table)
    as (t&message&Task&Slot&Highest).
  exists tasks. exists lo. exists hi. exists entries. exists t. exists message.
  split; [exact Lookup | ]. split; [exact (conj Lo (conj Hi (conj Nonempty (conj Bitmap Table)))) | ]. split; [exact Loads | ].
  split; [exact Task | ]. split.
  - rewrite <- Slot. apply (proj2 (proj2 (proj2 Loads))).
    apply V293_ready_selection_range; assumption || reflexivity.
  - exists tasks. split; assumption.
Qed.


(* Two original source assignments, with the ready invariant owned in their
   frame. Highest-task membership is an output, never an input oracle. *)
Theorem V293_ready_sched_updates : forall P ks ge le M ir aux O op current R
    unmap group rows high y table bt bh byblock oldy oldhigh,
  V293_sched_read_env ge le unmap group rows bt bg br ->
  get le y=Some (byblock,Tint8) ->
  get le high=None -> get ge high=Some (bh,Tint8) ->
  get le table=None -> get ge table=Some (bp,Tarray (Tptr V293_tcb_type) 13) ->
  byblock<>bt -> byblock<>bg -> byblock<>br -> byblock<>bh ->
  byblock<>bp -> bh<>bp ->
  (forall n, n<256 -> load Tint8 M (bt,Z.of_nat n)=Some (V293_byteval (V293_ready_lookup n))) ->
  (ge,le,M,ir,aux,O,op) |=
    (V293_owned_record_cell ((byblock,0%Z),Tint8,oldy) **
     V293_owned_record_cell ((bh,0%Z),Tint8,oldhigh)) **
    (SWINVt V293_ready_inv current ** R) ->
  exists tasks lo hi entries t message Mf,
    get O abstcblsid=Some (abstcblist tasks) /\
    V293_ready_rel lo hi entries tasks /\
    get tasks t=Some (Int.repr (Z.of_nat (V293_ready_select lo hi (V293_ready_group lo hi))),rdy,message) /\
    cstepstar P (curs (V293_OSSchedNew_updates unmap group rows high y),(kenil,ks)) (ge,le,M)
      (curs (sskip None),(kenil,ks)) (ge,le,Mf) /\
    (ge,le,Mf,ir,aux,O,op) |=
      (V293_owned_record_cell ((byblock,0%Z),Tint8,V293_byteval (V293_ready_lookup (V293_ready_group lo hi))) **
       V293_owned_record_cell ((bh,0%Z),Tint8,V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi)))) **
      (SWINVt V293_ready_inv current ** R) /\
    load Tint8 Mf (bh,0%Z)=Some (V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi))) /\
    evalval (V293_OSSched_target_expr table high) (ge,le,Mf)=Some (Vptr t) /\
    evaltype (V293_OSSched_target_expr table high) (ge,le,Mf)=Some (Tptr V293_tcb_type) /\
    V293_scheduler O t /\
    (forall a, a<>(byblock,0%Z) -> a<>(bh,0%Z) -> get Mf a=get M a).
Proof.
  intros P ks ge le M ir aux O op current R unmap group rows high y table bt bh byblock oldy oldhigh
    Env Y HN HG TN TG YT YG YR YH YP HP Lookup Held.
  assert (InvHeld : (ge,le,M,ir,aux,O,op) |= SWINVt V293_ready_inv current ** Atrue) by (sep auto).
  destruct (V293_ready_switch_selected _ _ _ InvHeld)
    as (tasks&lo&hi&entries&t&message&TaskMap&Rel&Loads&Task&Pointer&Sched).
  destruct Rel as [Lo [Hi [Nonempty [Bitmap Table]]]].
  set (g:=V293_ready_group lo hi). set (selected:=V293_ready_select lo hi g).
  assert (GB : g<256).
  { unfold g,V293_ready_group. destruct (lo=?0); destruct (hi=?0); lia. }
  assert (YB : V293_ready_lookup g<256).
  { pose proof (proj1 (V293_ready_row_spec g GB)). lia. }
  assert (SB : selected<13).
  { unfold selected,g. apply V293_ready_selection_range; assumption || reflexivity. }
  assert (First : (ge,le,M,ir,aux,O,op) |=
    V293_owned_record_cell ((byblock,0%Z),Tint8,oldy) **
    (V293_owned_record_cell ((bh,0%Z),Tint8,oldhigh) ** (SWINVt V293_ready_inv current ** R))) by (apply astar_assoc_elim; exact Held).
  destruct (V293_owned_byte_update _ _ _ _ _ _ _ _ _ _ _ YB First) as [WY UpdatedY].
  replace (V293_put_byte M (byblock,0%Z) (V293_ready_lookup g)) with
    (V293_write_byte M byblock (V293_ready_lookup g)) in UpdatedY by reflexivity.
  set (M1:=V293_write_byte M byblock (V293_ready_lookup g)) in *.
  assert (Second : (ge,le,M1,ir,aux,O,op) |=
    V293_owned_record_cell ((bh,0%Z),Tint8,oldhigh) **
    (V293_owned_record_cell ((byblock,0%Z),Tint8,V293_byteval (V293_ready_lookup g)) **
      (SWINVt V293_ready_inv current ** R))) by (clear First Held InvHeld; sep auto).
  destruct (V293_owned_byte_update _ _ selected _ _ _ _ _ _ _ _ ltac:(lia) Second) as [WH UpdatedH].
  replace (V293_put_byte M1 (bh,0%Z) selected) with
    (V293_write_byte M1 bh selected) in UpdatedH by reflexivity.
  set (Mf:=V293_write_byte M1 bh selected) in *.
  assert (HM : V293_sched_read_memory M bt bg br lo hi g).
  { destruct Loads as [L [H [G T]]]. unfold V293_sched_read_memory. auto. }
  destruct WY as [vy WY]. destruct WH as [vh WH].
  assert (WHold : get M (bh,0%Z)=Some (true,vh)).
  { unfold M1 in WH. rewrite V293_write_byte_other in WH by exact YH. exact WH. }
  assert (Execution : cstepstar P
    (curs (V293_OSSchedNew_updates unmap group rows high y),(kenil,ks)) (ge,le,M)
    (curs (sskip None),(kenil,ks)) (ge,le,Mf)).
  { unfold Mf,M1,selected. eapply V293_OSSchedNew_updates_execution; eassumption || reflexivity. }
  assert (HL : load Tint8 Mf (bh,0%Z)=Some (V293_byteval selected)).
  { unfold Mf. apply V293_write_byte_load. lia. }
  assert (PL : load (Tptr V293_tcb_type) Mf (bp,(4*Z.of_nat selected)%Z)=Some (Vptr t)).
  { unfold Mf,M1,load,loadm in *. cbn [typelen] in *.
    rewrite (V293_loadbytes_equal_range 4
      (V293_write_byte (V293_write_byte M byblock (V293_ready_lookup g)) bh selected)
      M bp (4*Z.of_nat selected)%Z).
    - exact Pointer.
    - intros k Bound. unfold V293_write_byte. repeat rewrite map_get_set' by (intro E; inversion E; congruence). reflexivity. }
  destruct (V293_eval_pointer_array ge le Mf table high V293_tcb_type bp bh selected (Vptr t)
    TN HN TG HG HL SB PL) as [Value TargetType].
  exists tasks. exists lo. exists hi. exists entries. exists t. exists message. exists Mf.
  split; [exact TaskMap | ]. split; [exact (conj Lo (conj Hi (conj Nonempty (conj Bitmap Table)))) | ].
  split; [exact Task | ]. split; [exact Execution | ]. split.
  - clear Held First Second UpdatedY InvHeld. sep auto.
  - split; [exact HL | ]. split; [exact Value | ]. split; [exact TargetType | ]. split; [exact Sched | ].
    intros a AY AH. unfold Mf,M1,selected,g. apply V293_OSSchedNew_updates_frame; assumption.
Qed.

End RuntimeReady.
