(* Shared physical clock AND ready/TCB/table resources, tied to the same
   existing abstract slots. This joins two prior ownership boundaries without
   duplicating task/time abstract data. It is not a complete kernel invariant. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeShared.
Require Import CertiOS.certiucos.v293.proofs.V293TimeSharedGood.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickShared.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitchPre.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.tactics.sepauto.sep_combine_lemmas.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.certiucos.v293.code.V293OSTimeTick.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.memory_prop.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.framework.proof.soundness.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Local Open Scope nat_scope.
Section TimeReady.
Variables br bg bp : block.

Definition V293_time_ready_fields n := EX t : tid, EX ts : TcbMod.map,
  EX es : EcbMod.map, (CurTid t ** V293_shared_fields t ts es n) ** V293_ready_payload br bg bp ts.
Definition V293_time_ready_core bn := EX n : int32,
  V293_time_ready_fields n ** PV (bn,Int.zero) @ Tint32 |-> Vint32 n.

Lemma V293_time_ready_fields_forget : forall n,
  V293_time_ready_fields n ==> V293_ready_core br bg bp.
Proof. unfold V293_time_ready_fields,V293_ready_core,V293_shared_ready_records. intros n s H;sep auto. Qed.
Lemma V293_time_ready_fields_precise : forall n, precise (V293_time_ready_fields n).
Proof.
  intros n s M1 M2 O1 O2 H1 H2 M O HM1 HM2 HO1 HO2.
  apply (@V293_ready_core_precise br bg bp s M1 M2 O1 O2
    (V293_time_ready_fields_forget n _ H1) (V293_time_ready_fields_forget n _ H2)
    M O HM1 HM2 HO1 HO2).
Qed.
Lemma V293_time_ready_bytes_precise : forall b n,
  precise (PV (b,Int.zero) @ Tint32 |-> Vint32 n).
Proof.
  apply V293_time_bytes_precise.
Qed.
Lemma V293_time_ready_fields_clock : forall n s,
  s |= V293_time_ready_fields n -> get (getabst s) ostmid = Some (ostm n).
Proof.
  intros n s [t [ts [es H]]]. eapply V293_star_abst_get_l; [ | exact H].
  intros st Hf. eapply V293_star_abst_get_r; [ | exact Hf].
  intros st0 H0. exact (proj2 (proj2 (proj2 (V293_shared_fields_get _ _ _ _ st0 H0)))).
Qed.
Lemma V293_time_ready_core_precise : forall bn, precise (V293_time_ready_core bn).
Proof.
  intros bn s M1 M2 O1 O2 [n1 H1] [n2 H2] M O HM1 HM2 HO1 HO2.
  destruct s as [[[[[[ge le] mem] ir] aux] oldO] op].
  pose proof (@V293_star_abst_get_l _ _ ostmid _ (V293_time_ready_fields_clock n1) _ H1) as N1.
  pose proof (@V293_star_abst_get_l _ _ ostmid _ (V293_time_ready_fields_clock n2) _ H2) as N2.
  change (get O1 ostmid = Some (ostm n1)) in N1.
  change (get O2 ostmid = Some (ostm n2)) in N2.
  destruct HO1 as [F1 J1]. destruct HO2 as [F2 J2].
  assert (G1 : get O ostmid = Some (ostm n1)) by (eapply OSAbstMod.join_get_l;[exact J1 | exact N1]).
  assert (G2 : get O ostmid = Some (ostm n2)) by (eapply OSAbstMod.join_get_l;[exact J2 | exact N2]).
  assert (n1=n2) by congruence. subst n2.
  eapply precise_star; [apply V293_time_ready_fields_precise | apply V293_time_ready_bytes_precise |
    exact H1 | exact H2 | exact HM1 | exact HM2 | exists F1;exact J1 | exists F2;exact J2].
Qed.
Lemma V293_time_ready_core_good : forall bn, GoodInvAsrt (V293_time_ready_core bn).
Proof.
  intro bn. change (forall n, (forall t ts es,
    GoodInvAsrt (CurTid t ** V293_shared_fields t ts es n) /\
    GoodInvAsrt (V293_ready_payload br bg bp ts)) /\ True).
  intros n. split;[ |exact I]. intros t ts es. split.
  - unfold CurTid,Agvarmapsto,Aptrmapsto,V293_shared_fields; simpl;repeat split;auto.
  - apply V293_ready_payload_good.
Qed.
Lemma V293_time_ready_core_aux : forall bn ge le M ir aux O op ir' aux',
  (ge,le,M,ir,aux,O,op) |= V293_time_ready_core bn ->
  (ge,le,M,ir',aux',O,op) |= V293_time_ready_core bn.
Proof.
  intros bn ge le M ir aux O op ir' aux' [n H]. exists n.
  apply sat_split in H. destruct H as (m1&m2&o1&o2&JM&JO&Fields&Clock).
  apply sat_split'. exists m1. exists m2. exists o1. exists o2.
  split;[exact JM| ]. split;[exact JO| ]. split;[ |exact Clock].
  destruct Fields as [t [ts [es Fields]]]. exists t. exists ts. exists es.
  apply sat_split in Fields. destruct Fields as (ma&mb&oa&ob&JM'&JO'&Core&Ready).
  apply sat_split'. exists ma. exists mb. exists oa. exists ob.
  split;[exact JM'| ]. split;[exact JO'| ]. split;[exact Core| ].
  eapply V293_ready_payload_context;exact Ready.
Qed.
Lemma V293_time_ready_core_isr : forall bn, assertion.inv_isr_prop (V293_time_ready_core bn).
Proof.
  intro bn. unfold assertion.inv_isr_prop. repeat split;intros;
    destruct s as [[[[[[ge le] M] ir] [[ie si] cs]] O] op];
    eapply V293_time_ready_core_aux;exact H.
Qed.
Definition V293_time_ready_inv bn : Inv := fun k =>
  match k with
  | O => mkinvasrt (V293_time_ready_core_good bn)
      (conj (V293_time_ready_core_precise bn) (V293_time_ready_core_isr bn))
  | S j => V293_shared_inv (S j)
  end.
Lemma V293_time_ready_noisr_tail : forall bn n k,
  starinv_noisr (V293_time_ready_inv bn) (S k) n <==> Aemp.
Proof.
  intros bn. induction n;intros k s;simpl starinv_noisr;[reflexivity | ].
  change (s |= Aemp ** starinv_noisr (V293_time_ready_inv bn) (S (S k)) n <-> s |= Aemp).
  split;intro H.
  - apply astar_l_aemp_elim in H. apply IHn in H;exact H.
  - apply astar_l_aemp_intro. apply IHn;exact H.
Qed.
Lemma V293_time_ready_noisr_core : forall bn n,
  starinv_noisr (V293_time_ready_inv bn) 0 n <==> V293_time_ready_core bn.
Proof.
  intros bn [ | n] s;[reflexivity | ].
  change (s |= V293_time_ready_core bn ** starinv_noisr (V293_time_ready_inv bn) 1 n <-> s |= V293_time_ready_core bn).
  split;intro H.
  - apply astar_r_aemp_elim. eapply astar_mono;[intros st H0;exact H0 |
      intros st H0;apply V293_time_ready_noisr_tail in H0;exact H0 | exact H].
  - eapply astar_mono;[intros st H0;exact H0 |
      intros st H0;apply V293_time_ready_noisr_tail;exact H0 | ].
    apply astar_r_aemp_intro;exact H.
Qed.
Lemma V293_time_ready_irq_open : forall bn n ge le M ir aux O op,
  (forall i, ir i=false) ->
  (ge,le,M,ir,aux,O,op) |= invlth_isr (V293_time_ready_inv bn) 0 n ->
  (ge,le,M,ir,aux,O,op) |= V293_time_ready_core bn.
Proof.
  intros. unfold invlth_isr in H0. rewrite Nat.sub_0_r in H0.
  apply V293_time_ready_noisr_core with (n:=n). eapply invisr_imply_noisr';eauto.
Qed.
Lemma V293_time_ready_irq_close : forall bn n ge le M ir aux O op,
  (forall i, ir i=false) ->
  (ge,le,M,ir,aux,O,op) |= V293_time_ready_core bn ->
  (ge,le,M,ir,aux,O,op) |= invlth_isr (V293_time_ready_inv bn) 0 n.
Proof.
  intros. unfold invlth_isr. rewrite Nat.sub_0_r.
  apply V293_shared_clear_noisr_close;[exact H | ].
  apply V293_time_ready_noisr_core;exact H0.
Qed.

Lemma V293_time_ready_irq_open_asrt : forall bn n ir,
  (forall i, ir i=false) ->
  Aisr ir ** invlth_isr (V293_time_ready_inv bn) 0 n ==>
  Aisr ir ** V293_time_ready_core bn.
Proof.
  intros bn n ir Clear s H. destruct s as [[[[[[ge le] M] actual] aux] O] op].
  apply sat_split in H. destruct H as (m1 & m2 & o1 & o2 & JM & JO & H1 & H2).
  destruct H1 as [E Empty]. cbn in E. subst actual.
  apply sat_split'. exists m1. exists m2. exists o1. exists o2.
  repeat first [assumption | split]. eapply V293_time_ready_irq_open; eauto.
Qed.
Lemma V293_time_ready_irq_close_asrt : forall bn n ir,
  (forall i, ir i=false) ->
  Aisr ir ** V293_time_ready_core bn ==>
  Aisr ir ** invlth_isr (V293_time_ready_inv bn) 0 n.
Proof.
  intros bn n ir Clear s H. destruct s as [[[[[[ge le] M] actual] aux] O] op].
  apply sat_split in H. destruct H as (m1 & m2 & o1 & o2 & JM & JO & H1 & H2).
  destruct H1 as [E Empty]. cbn in E. subst actual.
  apply sat_split'. exists m1. exists m2. exists o1. exists o2.
  repeat first [assumption | split]. eapply V293_time_ready_irq_close; eauto.
Qed.

Definition V293_time_ready_switch_fields bn t ts es n :=
  (V293_shared_fields t ts es n ** V293_ready_payload br bg bp ts) ** PV (bn,Int.zero) @ Tint32 |-> Vint32 n.
Definition V293_time_ready_switch_core bn := EX t : tid, EX ts : TcbMod.map,
  EX es : EcbMod.map, EX n : int32, CurTid t ** V293_time_ready_switch_fields bn t ts es n.
Lemma V293_time_ready_switch_core_equiv : forall bn,
  V293_time_ready_core bn <==> V293_time_ready_switch_core bn.
Proof.
  unfold V293_time_ready_core,V293_time_ready_fields,V293_time_ready_switch_core,V293_time_ready_switch_fields.
  intros bn s;split;intro H;sep auto.
Qed.
Lemma V293_time_ready_switch_open : forall bn, SWINV (V293_time_ready_inv bn) ==> V293_shared_flags ** (V293_time_ready_switch_core bn).
Proof.
  intros bn s Hs. destruct s as [[[[[[ge le] M] ir] aux] O] op].
  assert (Hclear : forall i, ir i = false).
  { eapply (V293_shared_clear_state ge le M ir aux O op). unfold SWINV in Hs. sep auto. }
  unfold SWINV in Hs. apply sat_split in Hs.
  destruct Hs as [m1 [m2 [o1 [o2 [JM [JO [HC [k HK]]]]]]]].
  apply sat_split in HK. destruct HK as [m3 [m4 [o3 [o4 [JM2 [JO2 [HT HI]]]]]]].
  unfold invlth_isr in HI. rewrite Nat.sub_0_r in HI.
  apply invisr_imply_noisr' in HI; [ | intros; apply Hclear].
  apply (V293_time_ready_noisr_core bn) in HI.
  apply V293_time_ready_switch_core_equiv in HI.
  assert (Hpack : (ge, le, M, ir, aux, O, op) |=
    (isrclr ** Aie false) ** (ATopis k ** (V293_time_ready_switch_core bn))).
  { apply sat_split'. exists m1. exists m2. exists o1. exists o2. repeat first [assumption | split].
    apply sat_split'. exists m3. exists m4. exists o3. exists o4. repeat first [assumption | split]. }
  unfold V293_shared_flags. sep auto.
Qed.
Lemma V293_time_ready_switch_close : forall bn, V293_shared_flags ** (V293_time_ready_switch_core bn) ==> SWINV (V293_time_ready_inv bn).
Proof.
  intros bn s Hs. destruct s as [[[[[[ge le] M] ir] aux] O] op].
  assert (Hclear : forall i, ir i = false).
  { eapply (V293_shared_clear_state ge le M ir aux O op). unfold V293_shared_flags in Hs. sep auto. }
  unfold V293_shared_flags in Hs. sep normal in Hs. sep destruct Hs.
  assert (Hpack : (ge, le, M, ir, aux, O, op) |=
    (isrclr ** Aie false) ** (ATopis x ** (V293_time_ready_switch_core bn))) by (sep auto).
  apply sat_split in Hpack. destruct Hpack as [m1 [m2 [o1 [o2 [JM [JO [HC HK]]]]]]].
  apply sat_split in HK. destruct HK as [m3 [m4 [o3 [o4 [JM2 [JO2 [HT HI]]]]]]].
  apply V293_time_ready_switch_core_equiv in HI.
  apply (proj2 (V293_time_ready_noisr_core bn x _)) in HI.
  apply V293_shared_clear_noisr_close in HI; [ | exact Hclear].
  unfold SWINV. apply sat_split'. exists m1. exists m2. exists o1. exists o2. repeat first [assumption | split].
  exists x. unfold invlth_isr. rewrite Nat.sub_0_r.
  apply sat_split'. exists m3. exists m4. exists o3. exists o4. repeat first [assumption | split].
Qed.

Definition V293_time_ready_switch_full bn t := EX ts : TcbMod.map, EX es : EcbMod.map, EX n : int32,
  (EX tp : type, GV OSTCBCur @ (Tptr tp) |-> (Vptr t)) ** (V293_time_ready_switch_fields bn) t ts es n.
Lemma V293_time_ready_switch_full_open : forall bn t, SWINVt (V293_time_ready_inv bn) t ==> V293_shared_flags ** V293_time_ready_switch_full bn t.
Proof.
  intros bn t s Hs. unfold SWINVt in Hs.
  assert (Ho : s |= (V293_shared_flags ** (V293_time_ready_switch_core bn)) ** CurTid t).
  { eapply astar_mono; [apply V293_time_ready_switch_open | intros st H; exact H | exact Hs]. }
  clear Hs. rename Ho into Hs.
  unfold V293_time_ready_switch_core in Hs. sep normal in Hs. sep destruct Hs.
  assert (E : x = t).
  { eapply (V293_shared_current_agree x t (V293_shared_flags ** (V293_time_ready_switch_fields bn) x x0 x1 x2) s). sep auto. } subst x.
  assert (Hp : s |= V293_shared_flags ** ((CurTid t ** CurTid t) ** (V293_time_ready_switch_fields bn) t x0 x1 x2)) by (sep auto).
  eapply astar_mono in Hp; [ | intros st H; exact H | apply astar_mono; [apply V293_current_halves_write | intros st H; exact H]].
  unfold V293_time_ready_switch_full. sep auto.
Qed.
Lemma V293_time_ready_switch_full_close : forall bn t, V293_shared_flags ** V293_time_ready_switch_full bn t ==> SWINVt (V293_time_ready_inv bn) t.
Proof.
  intros bn t s Hs. unfold V293_time_ready_switch_full in Hs. sep normal in Hs. sep destruct Hs.
  assert (Hp : s |= (GV OSTCBCur @ (Tptr x2) |-> (Vptr t)) **
    (V293_shared_flags ** (V293_time_ready_switch_fields bn) t x x0 x1)) by (sep auto).
  eapply astar_mono in Hp; [ | apply GV_separate_rw | intros st H; exact H].
  unfold SWINVt. apply astar_mono with (P := V293_shared_flags ** (V293_time_ready_switch_core bn)) (Q := CurTid t).
  - apply V293_time_ready_switch_close.
  - intros st H; exact H.
  - unfold V293_time_ready_switch_core, CurTid. sep auto.
Qed.

Lemma V293_time_ready_switch_store : forall bn ct t ge le M M' ir aux O op b tp,
  (ge, le, M, ir, aux, O, op) |= SWINVt (V293_time_ready_inv bn) ct ->
  get ge OSTCBCur = Some (b, Tptr tp) ->
  store (Tptr tp) M (b, 0%Z) (Vptr t) = Some M' ->
  (ge, le, M', ir, aux, set O curtid (oscurt t), op) |= SWINVt (V293_time_ready_inv bn) t.
Proof.
  intros bn ct t ge le M M' ir aux O op b tp Hs GE HS.
  apply V293_time_ready_switch_full_open in Hs. unfold V293_time_ready_switch_full in Hs. sep normal in Hs. sep destruct Hs.
  assert (Hpack : (ge, le, M, ir, aux, O, op) |=
    (GV OSTCBCur @ (Tptr x2) |-> (Vptr ct)) ** (V293_shared_flags ** (V293_time_ready_switch_fields bn) ct x x0 x1)) by (sep auto).
  assert (ET : x2 = tp).
  { unfold Agvarmapsto in Hpack. sep normal in Hpack. sep destruct Hpack.
    apply sat_split in Hpack. destruct Hpack as [ma [mb [oa [ob [JM [JO [[b0 [G _]] HR]]]]]]].
    change (get ge OSTCBCur = Some (b0, Tptr x2)) in G. congruence. } subst x2.
  pose proof (V293_shared_store_global _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hpack GE HS) as Hstored.
  assert (Hhead : (ge, le, M', ir, aux, O, op) |= Aabsdata curtid (oscurt ct) **
    ((GV OSTCBCur @ (Tptr tp) |-> (Vptr t)) **
      (V293_shared_flags ** (Aabsdata abstcblsid (abstcblist x) **
        ((Aabsdata absecblsid (absecblist x0) ** Aabsdata ostmid (ostm x1)) **
          (V293_ready_payload br bg bp x ** PV (bn,Int.zero) @ Tint32 |-> Vint32 x1)))))).
  { clear Hs Hpack. unfold V293_time_ready_switch_fields,V293_shared_fields in Hstored. sep auto. }
  apply V293_shared_replace_slot with (new := oscurt t) in Hhead.
  apply V293_time_ready_switch_full_close. unfold V293_time_ready_switch_full, V293_time_ready_switch_fields, V293_shared_fields. clear Hs Hpack Hstored. sep auto.
Qed.

Theorem V293_time_ready_good : forall bn, GoodI (V293_time_ready_inv bn) V293_scheduler V293_shared_li.
Proof.
  intro bn. split.
  - intros o O Of op OO Hs JO. apply V293_time_ready_noisr_core in Hs.
    assert (Forget : (o,O,op) |= V293_shared_core ** Atrue).
    { unfold V293_time_ready_core in Hs. sep normal in Hs. sep destruct Hs.
      unfold V293_time_ready_fields,V293_shared_core,V293_shared_fields in Hs |- *. sep auto. }
    eapply (V293_shared_no_abstract_frame (o, O, op) Of OO); [exact Forget | exact JO].
  - split.
    + intros o O op t Hs. destruct o as [[[[ge le] M] ir] aux].
      assert (HP : (ge, le, M, ir, aux, O, op) |= CurTid t ** Atrue).
      { change ((ge, le, M, ir, aux, O, op) |= SWINV (V293_time_ready_inv bn) ** CurTid t) in Hs. sep auto. }
      destruct (V293_shared_current_read _ _ _ _ _ _ _ _ _ HP) as [b [tp [GE LD]]].
      exists b. exists tp. split; [exact GE | ]. split; [exact LD | ].
      apply V293_time_ready_switch_full_open in Hs. unfold V293_time_ready_switch_full in Hs. sep normal in Hs. sep destruct Hs.
      change (get (getabst (ge, le, M, ir, aux, O, op)) curtid = Some (oscurt t)).
      eapply V293_star_abst_get_l with (p := Aabsdata curtid (oscurt t)) (q := Atrue).
      * apply V293_shared_abs_get.
      * unfold V293_time_ready_switch_fields,V293_shared_fields in Hs. clear HP. sep auto.
    + split.
      * intros o O op t b tp M' ct Hs Hhighest GE HS.
        destruct o as [[[[ge le] M] ir] aux].
        assert (HT : exists ts, get O abstcblsid = Some (abstcblist ts)).
        { apply V293_time_ready_switch_full_open in Hs. unfold V293_time_ready_switch_full in Hs. sep normal in Hs. sep destruct Hs.
          exists x. change (get (getabst (ge, le, M, ir, aux, O, op)) abstcblsid = Some (abstcblist x)).
          eapply V293_star_abst_get_l with (p := Aabsdata abstcblsid (abstcblist x)) (q := Atrue).
          - apply V293_shared_abs_get.
          - unfold V293_time_ready_switch_fields,V293_shared_fields in Hs. sep auto. }
        destruct HT as [ts HT]. exists ts. split; [exact HT | ].
        pose proof (V293_time_ready_switch_store bn _ _ _ _ _ _ _ _ _ _ _ _ Hs GE HS) as Hnew.
        destruct (Classical_Prop.classic (indom ts ct)) as [Hm | Hm].
        -- left. split; assumption.
        -- right. split; [exact Hm | ]. intros Mx Ox MM OO HL JM JO.
           specialize (HL op). destruct HL as [lg HL].
           change (Mx = emp /\ Ox = emp) in HL. destruct HL as [EM EO]. subst Mx Ox.
           apply map_join_emp' in JM. apply map_join_emp' in JO. subst MM OO. exact Hnew.
      * apply V293_scheduler_good.
Qed.


(* GoodInvAsrt rules exclude abstract actions. This implication is enough
   to reuse the existing clock action while retaining the ready payload. *)
Local Lemma V293_time_ready_change : forall P,
  GoodInvAsrt P -> can_change_aop P.
Proof. induction P;simpl;intuition eauto. Qed.

Lemma V293_tick_ready_clock_close : forall sd bn clock frame,
  can_change_aop frame ->
  absinfer sd
    (<||V293_tick_clock_action||> **
      ((V293_time_ready_fields clock **
        PV (bn,Int.zero) @ Tint32 |-> Vint32 (Int.add clock Int.one)) ** frame))
    (<||END None||> ** (V293_time_ready_core bn ** frame)).
Proof.
  intros sd bn clock frame Free.
  eapply absinfer_conseq with
    (p:=<||V293_tick_clock_action||> ** (Aabsdata ostmid (ostm clock) **
      ((EX t : tid, EX ts : TcbMod.map, EX es : EcbMod.map,
        CurTid t ** (Aabsdata curtid (oscurt t) **
          (Aabsdata abstcblsid (abstcblist ts) ** Aabsdata absecblsid (absecblist es))) **
        V293_ready_payload br bg bp ts) **
        (PV (bn,Int.zero) @ Tint32 |-> Vint32 (Int.add clock Int.one) ** frame))))
    (q:=<||END None||> ** (Aabsdata ostmid (ostm (Int.add clock Int.one)) **
      ((EX t : tid, EX ts : TcbMod.map, EX es : EcbMod.map,
        CurTid t ** (Aabsdata curtid (oscurt t) **
          (Aabsdata abstcblsid (abstcblist ts) ** Aabsdata absecblsid (absecblist es))) **
        V293_ready_payload br bg bp ts) **
        (PV (bn,Int.zero) @ Tint32 |-> Vint32 (Int.add clock Int.one) ** frame)))).
  - unfold V293_time_ready_core,V293_time_ready_fields,V293_shared_fields.
    intros s H;sep auto.
  - apply V293_tick_clock_absinfer.
    split.
    + intros t ts es. split.
      * unfold CurTid,Agvarmapsto,Aptrmapsto. simpl;auto.
      * split;[simpl;auto | exact (V293_time_ready_change _ (V293_ready_payload_good br bg bp ts))].
    + simpl;auto.
  - unfold V293_time_ready_fields,V293_shared_fields. intros s H;sep auto.
Qed.

(* Reuse the already proved unsigned increment rule, on the exact expression
   in the frozen tick AST, rather than assume evaluation or store success. *)
Theorem V293_tick_ready_clock_write : forall Spec sd li r ri tid now bn frame,
  NoAbs li -> can_change_aop frame -> (frame ==> CurLINV li tid) ->
  InfRules Spec sd li (V293_time_ready_inv bn) r ri
    (<||V293_tick_clock_action||> ** (V293_time_ready_core bn **
      (V293_time_binding false now bn ** frame)))
    (sassign (evar now) (ebinop oplus (evar now) (econst32 Int.one)))
    (<||END None||> ** (V293_time_ready_core bn **
      (V293_time_binding false now bn ** frame))) tid.
Proof.
  intros Spec sd li r ri tid now bn frame NA Free Inv.
  eapply conseq_rule with
    (p:=EX clock : int32, <||V293_tick_clock_action||> **
      ((V293_time_ready_fields clock ** PV (bn,Int.zero) @ Tint32 |-> Vint32 clock) **
        (V293_time_binding false now bn ** frame))).
  - unfold V293_time_ready_core. intros s H;sep auto.
  - intros s H;exact H.
  - apply ex_intro_rule. intro clock.
    eapply abscsq_rule with
      (p:=<||V293_tick_clock_action||> **
        ((V293_time_ready_fields clock ** PV (bn,Int.zero) @ Tint32 |-> Vint32 clock) **
          (V293_time_binding false now bn ** frame)))
      (q:=<||V293_tick_clock_action||> **
        ((V293_time_ready_fields clock ** PV (bn,Int.zero) @ Tint32 |-> Vint32 (Int.add clock Int.one)) **
          (V293_time_binding false now bn ** frame))).
    + exact NA.
    + apply absinfer_eq.
    + apply V293_tick_ready_clock_close.
      cbn [V293_time_binding V293_counter_bindings Aptrmapsto]. simpl. auto.
    + eapply conseq_rule with
        (p:=<||V293_tick_clock_action||> **
          ((V293_time_ready_fields clock ** frame) ** V293_counter_cell now bn clock))
        (q:=<||V293_tick_clock_action||> **
          ((V293_time_ready_fields clock ** frame) ** V293_counter_cell now bn (Int.add clock Int.one))).
      * unfold V293_time_binding,V293_counter_cell. intros s H;sep auto.
      * unfold V293_time_binding,V293_counter_cell. intros s H;sep auto.
      * apply V293_OSSched_counter_increment. eapply V293_star_CurLINV_r;exact Inv.
Qed.

(* This form preserves the original right-associated AST, including its tail.
   Tail is a separate continuation proof, never an assumed clock body. *)
Theorem V293_tick_ready_clock_with_tail : forall Spec sd li r ri tid ir si ci now bn frame tail q,
  NoAbs li -> (forall i, ir i=false) -> (gettopis si <= INUM)%nat ->
  GoodFrm frame -> (frame ==> CurLINV li tid) ->
  InfRules Spec sd li (V293_time_ready_inv bn) r ri
    (<||END None||> ** OS[ir,true,si,ci] ** (V293_time_binding false now bn ** frame)) tail q tid ->
  InfRules Spec sd li (V293_time_ready_inv bn) r ri
    (<||V293_tick_clock_action||> ** OS[ir,true,si,ci] ** (V293_time_binding false now bn ** frame))
    (sseq (sprim encrit)
      (sseq (sassign (evar now) (ebinop oplus (evar now) (econst32 Int.one)))
        (sseq (sprim excrit) tail))) q tid.
Proof.
  intros Spec sd li r ri tid ir si ci now bn frame tail q NA Clear Bound GF Inv Tail.
  assert (GP : GoodFrm (V293_time_binding false now bn ** frame)).
  { cbn [V293_time_binding V293_counter_bindings Aptrmapsto GoodFrm];tauto. }
  eapply seq_rule with (p':=<||V293_tick_clock_action||> ** OS[ir,false,si,true::ci] **
    invlth_isr (V293_time_ready_inv bn) 0 (gettopis si) ** (V293_time_binding false now bn ** frame)).
  - eapply conseq_rule with
      (p:=<||V293_tick_clock_action||> ** OS[ir,true,si,ci] ** ATopis (gettopis si) **
        [| (gettopis si <= INUM)%nat |] ** (V293_time_binding false now bn ** frame)).
    + intros s H. assert (S : s |= Ais si ** Atrue) by (sep auto).
      pose proof (V293_time_topis si Atrue s S) as Top.
      apply astar_l_atopis_elim in Top. destruct Top as [Top _].
      pose proof (@astar_l_atopis_intro s (gettopis si) _ H Top) as HT.
      clear H. rename HT into H. sep auto.
    + intros s H;exact H.
    + apply encrit1_rule;exact GP.
  - eapply seq_rule with (p':=<||END None||> ** OS[ir,false,si,true::ci] **
      V293_time_ready_core bn ** (V293_time_binding false now bn ** frame)).
    + eapply conseq_rule with
        (p:=<||V293_tick_clock_action||> ** (V293_time_ready_core bn **
          (V293_time_binding false now bn ** (frame ** OS[ir,false,si,true::ci]))))
        (q:=<||END None||> ** (V293_time_ready_core bn **
          (V293_time_binding false now bn ** (frame ** OS[ir,false,si,true::ci])))).
      * intros s H.
        assert (P : s |= (Aisr ir ** invlth_isr (V293_time_ready_inv bn) 0 (gettopis si)) **
          (<||V293_tick_clock_action||> ** (Aie false ** (Ais si ** (Acs (true::ci) **
            (V293_time_binding false now bn ** frame)))))) by (sep auto).
        eapply astar_mono in P;[ | apply V293_time_ready_irq_open_asrt;exact Clear | intros st H0;exact H0].
        clear H. sep auto.
      * intros s H;sep auto.
      * apply V293_tick_ready_clock_write;[exact NA | | ].
        -- simpl. split;[ | repeat split].
           clear -GF. induction frame;simpl in *;intuition eauto.
        -- eapply V293_star_CurLINV_l;exact Inv.
    + eapply seq_rule;[ | exact Tail].
      eapply conseq_rule with
        (p:=<||END None||> ** OS[ir,false,si,true::ci] ** ATopis (gettopis si) **
          invlth_isr (V293_time_ready_inv bn) 0 (gettopis si) ** (V293_time_binding false now bn ** frame)).
      * intros s H.
        assert (P : s |= (Aisr ir ** V293_time_ready_core bn) **
          (<||END None||> ** (Aie false ** (Ais si ** (Acs (true::ci) **
            (V293_time_binding false now bn ** frame)))))) by (sep auto).
        eapply astar_mono in P;[ | apply V293_time_ready_irq_close_asrt;exact Clear | intros st H0;exact H0].
        clear H. rename P into H.
        assert (S : s |= Ais si ** Atrue) by (sep auto).
        pose proof (V293_time_topis si Atrue s S) as Top.
        apply astar_l_atopis_elim in Top. destruct Top as [Top _].
        pose proof (@astar_l_atopis_intro s (gettopis si) _ H Top) as HT.
        clear H. rename HT into H. sep auto.
      * intros s H;exact H.
      * apply excrit1_rule;[exact GP | eapply V293_star_CurLINV_r;exact Inv].
Qed.


(* Closed clock prefix: no assumed continuation body. *)
Theorem V293_tick_ready_clock_prefix : forall Spec sd li r ri tid ir si ci now bn frame,
  NoAbs li -> (forall i, ir i=false) -> (gettopis si <= INUM)%nat ->
  GoodFrm frame -> (frame ==> CurLINV li tid) ->
  InfRules Spec sd li (V293_time_ready_inv bn) r ri
    (<||V293_tick_clock_action||> ** OS[ir,true,si,ci] ** (V293_time_binding false now bn ** frame))
    (sseq (sprim encrit)
      (sseq (sassign (evar now) (ebinop oplus (evar now) (econst32 Int.one)))
        (sprim excrit)))
    (<||END None||> ** OS[ir,true,si,ci] ** (V293_time_binding false now bn ** frame)) tid.
Proof.
  intros Spec sd li r ri tid ir si ci now bn frame NA Clear Bound GF Inv.
  assert (GP : GoodFrm (V293_time_binding false now bn ** frame)).
  { cbn [V293_time_binding V293_counter_bindings Aptrmapsto GoodFrm];tauto. }
  eapply seq_rule with (p':=<||V293_tick_clock_action||> ** OS[ir,false,si,true::ci] **
    invlth_isr (V293_time_ready_inv bn) 0 (gettopis si) ** (V293_time_binding false now bn ** frame)).
  - eapply conseq_rule with
      (p:=<||V293_tick_clock_action||> ** OS[ir,true,si,ci] ** ATopis (gettopis si) **
        [| (gettopis si <= INUM)%nat |] ** (V293_time_binding false now bn ** frame)).
    + intros s H. assert (S : s |= Ais si ** Atrue) by (sep auto).
      pose proof (V293_time_topis si Atrue s S) as Top.
      apply astar_l_atopis_elim in Top. destruct Top as [Top _].
      pose proof (@astar_l_atopis_intro s (gettopis si) _ H Top) as HT.
      clear H. rename HT into H. sep auto.
    + intros s H;exact H.
    + apply encrit1_rule;exact GP.
  - eapply seq_rule with (p':=<||END None||> ** OS[ir,false,si,true::ci] **
      V293_time_ready_core bn ** (V293_time_binding false now bn ** frame)).
    + eapply conseq_rule with
        (p:=<||V293_tick_clock_action||> ** (V293_time_ready_core bn **
          (V293_time_binding false now bn ** (frame ** OS[ir,false,si,true::ci]))))
        (q:=<||END None||> ** (V293_time_ready_core bn **
          (V293_time_binding false now bn ** (frame ** OS[ir,false,si,true::ci])))).
      * intros s H.
        assert (P : s |= (Aisr ir ** invlth_isr (V293_time_ready_inv bn) 0 (gettopis si)) **
          (<||V293_tick_clock_action||> ** (Aie false ** (Ais si ** (Acs (true::ci) **
            (V293_time_binding false now bn ** frame)))))) by (sep auto).
        eapply astar_mono in P;[ | apply V293_time_ready_irq_open_asrt;exact Clear | intros st H0;exact H0].
        clear H. sep auto.
      * intros s H;sep auto.
      * apply V293_tick_ready_clock_write;[exact NA | | ].
        -- simpl. split;[ | repeat split].
           clear -GF. induction frame;simpl in *;intuition eauto.
        -- eapply V293_star_CurLINV_l;exact Inv.
    + eapply conseq_rule with
        (p:=<||END None||> ** OS[ir,false,si,true::ci] ** ATopis (gettopis si) **
          invlth_isr (V293_time_ready_inv bn) 0 (gettopis si) ** (V293_time_binding false now bn ** frame)).
      * intros s H.
        assert (P : s |= (Aisr ir ** V293_time_ready_core bn) **
          (<||END None||> ** (Aie false ** (Ais si ** (Acs (true::ci) **
            (V293_time_binding false now bn ** frame)))))) by (sep auto).
        eapply astar_mono in P;[ | apply V293_time_ready_irq_close_asrt;exact Clear | intros st H0;exact H0].
        clear H. rename P into H.
        assert (S : s |= Ais si ** Atrue) by (sep auto).
        pose proof (V293_time_topis si Atrue s S) as Top.
        apply astar_l_atopis_elim in Top. destruct Top as [Top _].
        pose proof (@astar_l_atopis_intro s (gettopis si) _ H Top) as HT.
        clear H. rename HT into H. sep auto.
      * intros s H;exact H.
      * apply excrit1_rule;[exact GP | eapply V293_star_CurLINV_r;exact Inv].
Qed.


(* Observable agreement is derived from the owned core, not imposed as an
   additional premise. An arbitrary disjoint caller frame is retained. *)
Theorem V293_time_ready_clock_agreement : forall bn R s,
  s |= V293_time_ready_core bn ** R ->
  exists clock, get (getabst s) ostmid=Some (ostm clock) /\
    load Tint32 (getmem s) (bn,0%Z)=Some (Vint32 clock).
Proof.
  intros bn R s Held. unfold V293_time_ready_core in Held.
  sep normal in Held. sep destruct Held. exists x. split.
  - eapply V293_star_abst_get_l with (p:=V293_time_ready_fields x) (q:=Atrue).
    + apply V293_time_ready_fields_clock.
    + sep auto.
  - eapply V293_star_load_l with
      (p:=PV (bn,Int.zero) @ Tint32 |-> Vint32 x) (q:=Atrue).
    + intros st [P _]. eapply mapstoval_load;[reflexivity | exact P].
    + sep auto.
Qed.

Lemma V293_time_ready_switch_core_frame : forall bn t,
  SWINVt (V293_time_ready_inv bn) t ==> V293_time_ready_core bn ** Atrue.
Proof.
  intros bn t s H. unfold SWINVt in H.
  assert (Opened : s |= (V293_shared_flags ** V293_time_ready_switch_core bn) ** CurTid t).
  { eapply astar_mono;[apply V293_time_ready_switch_open | intros st H0;exact H0 | exact H]. }
  clear H. unfold V293_time_ready_switch_core,V293_time_ready_switch_fields,
    V293_time_ready_core,V293_time_ready_fields in Opened |- *. sep auto.
Qed.

Lemma V293_time_ready_switch_project : forall bn t,
  SWINVt (V293_time_ready_inv bn) t ==>
    SWINVt (V293_ready_inv br bg bp) t ** Atrue.
Proof.
  intros bn t s H. apply V293_time_ready_switch_full_open in H.
  unfold V293_time_ready_switch_full,V293_time_ready_switch_fields in H.
  sep normal in H. sep destruct H.
  eapply astar_mono with
    (P:=V293_shared_flags ** V293_ready_full br bg bp t)
    (Q:=PV (bn,Int.zero) @ Tint32 |-> Vint32 x1).
  - apply V293_ready_switch_halves.
  - intros st H0;exact I.
  - unfold V293_ready_full. sep auto.
Qed.

Theorem V293_tick_ready_clock_semantics : forall Spec sd li r ri tid ir si ci now bn frame tail q,
  NoAbs li -> (forall i, ir i=false) -> (gettopis si <= INUM)%nat ->
  GoodFrm frame -> (frame ==> CurLINV li tid) ->
  InfRules Spec sd li (V293_time_ready_inv bn) r ri
    (<||END None||> ** OS[ir,true,si,ci] ** (V293_time_binding false now bn ** frame)) tail q tid ->
  simulation.RuleSem Spec sd li (V293_time_ready_inv bn) r ri
    (<||V293_tick_clock_action||> ** OS[ir,true,si,ci] ** (V293_time_binding false now bn ** frame))
    (sseq (sprim encrit)
      (sseq (sassign (evar now) (ebinop oplus (evar now) (econst32 Int.one)))
        (sseq (sprim excrit) tail))) q tid.
Proof. intros. apply RuleSound. apply V293_tick_ready_clock_with_tail;assumption. Qed.

End TimeReady.
