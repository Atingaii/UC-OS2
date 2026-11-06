(* A bounded semantic switch invariant: the abstract task map owns exactly
   its selected physical TCB fields. No ready bitmap/table, list/free-pool,
   API/ISR preservation or initialized reachability is claimed. *)
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitchPre.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
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

Definition V293_record_types (cells : list V293_record_cell) :=
  map (fun '(a,tp,_) => (a,tp)) cells.
Lemma V293_owned_cells_storage : forall cells,
  V293_owned_record_cells cells ==> V293_storage (V293_record_types cells).
Proof.
  induction cells as [ | [[a tp] v] rest IH]; intros s Owned; [exact Owned | ].
  cbn [V293_owned_record_cells V293_record_types map V293_storage] in *.
  eapply astar_mono; [ | exact IH | exact Owned].
  intros st Cell. exists v. exact Cell.
Qed.
Lemma V293_record_types_pend : forall t p status message pend,
  V293_record_types (V293_record_layout t p status message pend) =
  V293_record_types (V293_record_layout t p status message 0).
Proof. intros; destruct status as [ | reason delay]; [ | destruct reason]; reflexivity. Qed.
Lemma V293_task_record_precise : forall t priority status message,
  precise (V293_owned_task_record t priority status message).
Proof.
  intros t priority status message s M1 M2 O1 O2
    [p1 [pend1 H1]] [p2 [pend2 H2]] M O HM1 HM2 HO1 HO2.
  apply astar_l_apure_elim in H1. destruct H1 as [[R1 [P1 B1]] H1].
  apply astar_l_apure_elim in H2. destruct H2 as [[R2 [P2 B2]] H2].
  assert (E : p1=p2).
  { eapply V293_priority_repr_injective; [exact R1 | exact R2 | congruence]. } subst p2.
  apply V293_owned_cells_storage in H1. apply V293_owned_cells_storage in H2.
  rewrite V293_record_types_pend in H1,H2.
  eapply V293_storage_precise; eassumption.
Qed.
Lemma V293_task_list_precise : forall entries, precise (V293_owned_task_list entries).
Proof.
  induction entries as [ | [t [[p status] message]] rest IH]; simpl.
  - exact (V293_storage_precise nil).
  - apply precise_star; [apply V293_task_record_precise | exact IH].
Qed.
Lemma V293_owned_cells_good : forall cells, GoodInvAsrt (V293_owned_record_cells cells).
Proof.
  induction cells as [ | [[a tp] v] rest IH]; cbn [V293_owned_record_cells].
  - exact I.
  - split; [split; exact I | exact IH].
Qed.
Lemma V293_task_list_good : forall entries, GoodInvAsrt (V293_owned_task_list entries).
Proof.
  induction entries as [ | [t [[p status] message]] rest IH]; cbn [V293_owned_task_list].
  - exact I.
  - split; [ | exact IH].
    change (forall q pend : nat, True /\
      GoodInvAsrt (V293_owned_record_cells (V293_record_layout t q status message pend))).
    intros. split; [exact I | apply V293_owned_cells_good].
Qed.
Lemma V293_owned_cells_context : forall cells ge le M ir aux O op ge' le' ir' aux' op',
  (ge,le,M,ir,aux,O,op) |= V293_owned_record_cells cells ->
  (ge',le',M,ir',aux',O,op') |= V293_owned_record_cells cells.
Proof.
  induction cells as [ | [[a tp] v] rest IH]; intros; [exact H | ].
  cbn [V293_owned_record_cells] in *.
  apply sat_split in H. destruct H as (m1&m2&o1&o2&JM&JO&Cell&Rest).
  apply sat_split'. exists m1. exists m2. exists o1. exists o2. split; [exact JM | ]. split; [exact JO | ].
  split; [exact Cell | eapply IH; exact Rest].
Qed.
Lemma V293_task_list_context : forall entries ge le M ir aux O op ge' le' ir' aux' op',
  (ge,le,M,ir,aux,O,op) |= V293_owned_task_list entries ->
  (ge',le',M,ir',aux',O,op') |= V293_owned_task_list entries.
Proof.
  induction entries as [ | [t [[p status] message]] rest IH]; intros; [exact H | ].
  cbn [V293_owned_task_list] in *.
  apply sat_split in H. destruct H as (m1&m2&o1&o2&JM&JO&[q [pend Cell]]&Rest).
  apply sat_split'. exists m1. exists m2. exists o1. exists o2. split; [exact JM | ]. split; [exact JO | ]. split.
  - exists q. exists pend. apply astar_l_apure_elim in Cell. destruct Cell as [Bounds Cell].
    apply astar_l_apure_intro; [eapply V293_owned_cells_context; exact Cell | exact Bounds].
  - eapply IH; exact Rest.
Qed.

Definition V293_records_core := EX current : tid, EX tasks : TcbMod.map,
  EX events : EcbMod.map, EX now : int32,
  V293_shared_task_records current tasks events now.
Lemma V293_records_core_precise : precise V293_records_core.
Proof.
  intros s M1 M2 O1 O2 [t1 [ts1 [es1 [n1 H1]]]] [t2 [ts2 [es2 [n2 H2]]]]
    M O HM1 HM2 HO1 HO2.
  destruct s as [[[[[[ge le] mem] ir] aux] oldO] op].
  unfold V293_shared_task_records in H1,H2.
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
  eapply precise_star; [ | apply V293_task_list_precise | exact H1 | exact H2 |
    exact HM1 | exact HM2 | exists F1; exact J1 | exists F2; exact J2].
  apply precise_star; [apply V293_shared_current_precise | apply V293_shared_fields_precise].
Qed.
Lemma V293_records_core_good : GoodInvAsrt V293_records_core.
Proof.
  unfold V293_records_core,V293_shared_task_records,V293_shared_fields,CurTid,
    Agvarmapsto,Aptrmapsto,V293_owned_task_records.
  simpl. intros. repeat split; auto using V293_task_list_good.
Qed.
Lemma V293_records_core_aux : forall ge le M ir aux O op ir' aux',
  (ge,le,M,ir,aux,O,op) |= V293_records_core ->
  (ge,le,M,ir',aux',O,op) |= V293_records_core.
Proof.
  intros ge le M ir aux O op ir' aux' [t [tasks [events [now H]]]].
  exists t. exists tasks. exists events. exists now. unfold V293_shared_task_records in *.
  apply sat_split in H. destruct H as (m1&m2&o1&o2&JM&JO&Core&Records).
  apply sat_split'. exists m1. exists m2. exists o1. exists o2. split; [exact JM | ]. split; [exact JO | ].
  split; [exact Core | eapply V293_task_list_context; exact Records].
Qed.
Definition V293_records_inv : Inv.
Proof.
  intro k. destruct k.
  - refine (@mkinvasrt V293_records_core V293_records_core_good _). split.
    + exact V293_records_core_precise.
    + unfold assertion.inv_isr_prop. repeat split; intros;
        destruct s as [[[[[[ge le] M] ir] [[ie si] cs]] O] op];
        eapply V293_records_core_aux; exact H.
  - exact (V293_shared_inv (S k)).
Defined.

Lemma V293_records_noisr_tail : forall n k,
  starinv_noisr V293_records_inv (S k) n <==> Aemp.
Proof.
  intros n. induction n; intros k s; simpl starinv_noisr; [reflexivity | ].
  split; intro Hs.
  - apply astar_l_aemp_elim in Hs. apply IHn in Hs. exact Hs.
  - apply astar_l_aemp_intro. apply IHn. exact Hs.
Qed.
Lemma V293_records_noisr_core : forall n,
  starinv_noisr V293_records_inv 0 n <==> V293_records_core.
Proof.
  intros [ | n] s; [reflexivity | ].
  split; intro Hs.
  - apply astar_r_aemp_elim. eapply astar_mono; [intros st H; exact H | intros st H; apply V293_records_noisr_tail in H; exact H | exact Hs].
  - eapply astar_mono; [intros st H; exact H | intros st H; apply V293_records_noisr_tail; exact H | ].
    apply astar_r_aemp_intro. exact Hs.
Qed.
Lemma V293_records_switch_open :   SWINV V293_records_inv ==>
  V293_shared_flags ** V293_records_core.
Proof.
  intros s Hs. destruct s as [[[[[[ge le] M] ir] aux] O] op].
  assert (HC : forall i, ir i = false).
  { eapply (V293_shared_clear_state ge le M ir aux O op). unfold SWINV in Hs. sep auto. }
  unfold SWINV in Hs. apply sat_split in Hs.
  destruct Hs as (m1 & m2 & o1 & o2 & JM & JO & HF & k & HK).
  apply sat_split in HK. destruct HK as (m3 & m4 & o3 & o4 & JM2 & JO2 & HT & HI).
  unfold invlth_isr in HI. rewrite Nat.sub_0_r in HI.
  apply invisr_imply_noisr' in HI; [ | intros; apply HC]. apply V293_records_noisr_core in HI.
  assert (HP : (ge, le, M, ir, aux, O, op) |= (isrclr ** Aie false) ** (ATopis k ** V293_records_core)).
  { apply sat_split'. exists m1. exists m2. exists o1. exists o2.  repeat first [assumption | split].
    apply sat_split'. exists m3. exists m4. exists o3. exists o4.  repeat first [assumption | split]. }
  unfold V293_shared_flags. sep auto.
Qed.
Lemma V293_records_switch_close :   V293_shared_flags ** V293_records_core ==> SWINV V293_records_inv.
Proof.
  intros s Hs. destruct s as [[[[[[ge le] M] ir] aux] O] op].
  assert (HC : forall i, ir i = false).
  { eapply (V293_shared_clear_state ge le M ir aux O op). unfold V293_shared_flags in Hs. sep auto. }
  unfold V293_shared_flags in Hs. sep normal in Hs. sep destruct Hs.
  assert (HP : (ge, le, M, ir, aux, O, op) |= (isrclr ** Aie false) ** (ATopis x ** V293_records_core)) by (sep auto).
  apply sat_split in HP. destruct HP as (m1 & m2 & o1 & o2 & JM & JO & HF & HK).
  apply sat_split in HK. destruct HK as (m3 & m4 & o3 & o4 & JM2 & JO2 & HT & HI).
  apply (proj2 (V293_records_noisr_core x _)) in HI.
  apply V293_shared_clear_noisr_close in HI; [ | exact HC].
  unfold SWINV.
  apply sat_split'. exists m1. exists m2. exists o1. exists o2.  repeat first [assumption | split].
  exists x. unfold invlth_isr. rewrite Nat.sub_0_r. apply sat_split'. exists m3. exists m4. exists o3. exists o4.  repeat first [assumption | split].
Qed.
Definition V293_records_full t := EX tasks : TcbMod.map, EX events : EcbMod.map, EX now : int32,
  (EX tp : type, GV OSTCBCur @ (Tptr tp) |-> (Vptr t)) **
  (V293_shared_fields t tasks events now ** V293_owned_task_records tasks).
Lemma V293_records_switch_full : forall t,
  SWINVt V293_records_inv t ==> V293_shared_flags ** V293_records_full t.
Proof.
  intros t s Hs. unfold SWINVt in Hs.
  assert (Ho : s |= (V293_shared_flags ** V293_records_core) ** CurTid t).
  { eapply astar_mono; [apply V293_records_switch_open | intros st H; exact H | exact Hs]. }
  clear Hs. rename Ho into Hs.
  unfold V293_records_core,V293_shared_task_records in Hs. sep normal in Hs. sep destruct Hs.
  assert (E : x=t).
  { eapply (V293_shared_current_agree x t
      (V293_shared_flags ** (V293_shared_fields x x0 x1 x2 ** V293_owned_task_records x0)) s).
    sep auto. } subst x.
  assert (Hp : s |= V293_shared_flags ** ((CurTid t ** CurTid t) **
    (V293_shared_fields t x0 x1 x2 ** V293_owned_task_records x0))) by (sep auto).
  eapply astar_mono in Hp; [ | intros st H; exact H |
    apply astar_mono; [apply V293_current_halves_write | intros st H; exact H]].
  unfold V293_records_full. clear Hs. sep auto.
Qed.
Lemma V293_records_switch_halves : forall t,
  V293_shared_flags ** V293_records_full t ==> SWINVt V293_records_inv t.
Proof.
  intros t s Hs. unfold V293_records_full in Hs. sep normal in Hs. sep destruct Hs.
  assert (Hp : s |= (GV OSTCBCur @ (Tptr x2) |-> (Vptr t)) **
    (V293_shared_flags ** (V293_shared_fields t x x0 x1 ** V293_owned_task_records x))) by (sep auto).
  eapply astar_mono in Hp; [ | apply GV_separate_rw | intros st H; exact H].
  unfold SWINVt. apply astar_mono with (P:=V293_shared_flags ** V293_records_core) (Q:=CurTid t).
  - apply V293_records_switch_close.
  - intros st H; exact H.
  - unfold V293_records_core,V293_shared_task_records,CurTid. clear Hs. sep auto.
Qed.
Lemma V293_records_store : forall ct t ge le M M' ir aux O op b tp,
  (ge,le,M,ir,aux,O,op) |= SWINVt V293_records_inv ct ->
  get ge OSTCBCur=Some (b,Tptr tp) ->
  store (Tptr tp) M (b,0%Z) (Vptr t)=Some M' ->
  (ge,le,M',ir,aux,set O curtid (oscurt t),op) |= SWINVt V293_records_inv t.
Proof.
  intros ct t ge le M M' ir aux O op b tp Hs GE HS.
  apply V293_records_switch_full in Hs. unfold V293_records_full in Hs.
  sep normal in Hs. sep destruct Hs.
  assert (HP : (ge,le,M,ir,aux,O,op) |= (GV OSTCBCur @ (Tptr x2) |-> (Vptr ct)) **
    (V293_shared_flags ** (V293_shared_fields ct x x0 x1 ** V293_owned_task_records x))) by (sep auto).
  assert (ET : x2=tp).
  { unfold Agvarmapsto in HP. sep normal in HP. sep destruct HP.
    apply sat_split in HP. destruct HP as (ma&mb&oa&ob&JM&JO&[b0 [G _]]&HR).
    change (get ge OSTCBCur=Some (b0,Tptr x2)) in G. congruence. } subst x2.
  pose proof (V293_shared_store_global _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP GE HS) as Stored.
  assert (HN : (ge,le,M',ir,aux,O,op) |= Aabsdata curtid (oscurt ct) **
    ((GV OSTCBCur @ (Tptr tp) |-> (Vptr t)) ** (V293_shared_flags **
      ((Aabsdata abstcblsid (abstcblist x) **
        (Aabsdata absecblsid (absecblist x0) ** Aabsdata ostmid (ostm x1))) **
        V293_owned_task_records x)))).
  { unfold V293_shared_fields in Stored. clear HP Hs. sep auto. }
  apply V293_shared_replace_slot with (new:=oscurt t) in HN.
  apply V293_records_switch_halves. unfold V293_records_full,V293_shared_fields.
  clear Hs HP Stored. sep auto.
Qed.
Theorem V293_records_invariant_good : GoodI V293_records_inv V293_scheduler V293_shared_li.
Proof.
  split.
  - intros o O Of op OO Hs JO. apply V293_records_noisr_core in Hs.
    eapply (V293_shared_no_abstract_frame (o,O,op) Of OO);
      [unfold V293_records_core,V293_shared_task_records,V293_shared_core in *; sep auto | exact JO].
  - split.
    + intros o O op t Hs. destruct o as [[[[ge le] M] ir] aux].
      assert (HP : (ge,le,M,ir,aux,O,op) |= CurTid t ** Atrue).
      { change ((ge,le,M,ir,aux,O,op) |= SWINV V293_records_inv ** CurTid t) in Hs. sep auto. }
      destruct (V293_shared_current_read _ _ _ _ _ _ _ _ _ HP) as (b&tp&GE&LD).
      exists b. exists tp. split; [exact GE | ]. split; [exact LD | ].
      apply V293_records_switch_full in Hs. unfold V293_records_full in Hs.
      sep normal in Hs. sep destruct Hs.
      change (get (getabst (ge,le,M,ir,aux,O,op)) curtid=Some (oscurt t)).
      eapply V293_star_abst_get_l with (p:=Aabsdata curtid (oscurt t)) (q:=Atrue).
      * apply V293_shared_abs_get.
      * unfold V293_shared_fields in Hs. clear HP. sep auto.
    + split.
      * intros o O op t b tp M' ct Hs Highest GE HS. destruct o as [[[[ge le] M] ir] aux].
        assert (HT : exists ts, get O abstcblsid=Some (abstcblist ts)).
        { apply V293_records_switch_full in Hs. unfold V293_records_full in Hs.
          sep normal in Hs. sep destruct Hs. exists x.
          change (get (getabst (ge,le,M,ir,aux,O,op)) abstcblsid=Some (abstcblist x)).
          eapply V293_star_abst_get_l with (p:=Aabsdata abstcblsid (abstcblist x)) (q:=Atrue).
          - apply V293_shared_abs_get.
          - unfold V293_shared_fields in Hs. sep auto. }
        destruct HT as [ts HT]. exists ts. split; [exact HT | ].
        pose proof (V293_records_store _ _ _ _ _ _ _ _ _ _ _ _ Hs GE HS) as Hnew.
        destruct (classic (indom ts ct)) as [Live | Dead].
        -- left. split; assumption.
        -- right. split; [exact Dead | ]. intros Mx Ox MM OO HL JM JO.
           specialize (HL op). destruct HL as [lg HL].
           change (Mx=emp /\ Ox=emp) in HL. destruct HL as [EM EO]. subst Mx Ox.
           apply map_join_emp' in JM. apply map_join_emp' in JO. subst MM OO. exact Hnew.
      * apply V293_scheduler_good.
Qed.

(* The output relation is about the caller's full concrete memory and the
   very abstract map it owns, not a separately chosen physical witness. *)
Theorem V293_records_switch_sound : forall t R s,
  s |= SWINVt V293_records_inv t ** R ->
  exists tasks, get (getabst s) abstcblsid=Some (abstcblist tasks) /\
    V293_task_records (getmem s) tasks.
Proof.
  intros t R s Held.
  assert (Open : s |= (V293_shared_flags ** V293_records_full t) ** R).
  { eapply astar_mono; [apply V293_records_switch_full | intros st H; exact H | exact Held]. }
  unfold V293_records_full in Open. sep normal in Open. sep destruct Open.
  exists x. split.
  - eapply V293_star_abst_get_l with (p:=Aabsdata abstcblsid (abstcblist x)) (q:=Atrue).
    + apply V293_shared_abs_get.
    + unfold V293_shared_fields in Open. clear Held. sep auto.
  - assert (Owned : s |= V293_owned_task_records x ** Atrue) by (clear Held; sep auto).
    destruct s as [[[[[[ge le] M] ir] aux] O] op].
    apply sat_split in Owned. destruct Owned as (m1&m2&o1&o2&JM&JO&Records&Rest).
    pose proof (V293_owned_task_records_sound _ _ Records) as Sound.
    intros target priority status message Lookup.
    eapply V293_task_record_sub; [exists m2; exact JM | apply Sound; exact Lookup].
Qed.
