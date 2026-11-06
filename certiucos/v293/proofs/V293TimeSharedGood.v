(* Switching preserves the integrated time invariant. LocalInv remains the
   explicit empty fixture: this is not task lifecycle or whole-kernel safety. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeShared.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitchPre.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.memory_prop.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.sep_combine_lemmas.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import Coq.Lists.List Lia.
Local Open Scope nat_scope.

Definition V293_time_switch_fields bn t ts es n :=
  V293_shared_fields t ts es n ** PV (bn,Int.zero) @ Tint32 |-> Vint32 n.
Definition V293_time_switch_core bn := EX t : tid, EX ts : TcbMod.map,
  EX es : EcbMod.map, EX n : int32, CurTid t ** V293_time_switch_fields bn t ts es n.
Lemma V293_time_switch_core_equiv : forall bn,
  V293_time_shared_core bn <==> V293_time_switch_core bn.
Proof.
  unfold V293_time_shared_core,V293_time_shared_fields,V293_time_switch_core,V293_time_switch_fields.
  intros bn s;split;intro H;sep auto.
Qed.
Lemma V293_time_switch_open : forall bn, SWINV (V293_time_shared_inv bn) ==> V293_shared_flags ** (V293_time_switch_core bn).
Proof.
  intros bn s Hs. destruct s as [[[[[[ge le] M] ir] aux] O] op].
  assert (Hclear : forall i, ir i = false).
  { eapply (V293_shared_clear_state ge le M ir aux O op). unfold SWINV in Hs. sep auto. }
  unfold SWINV in Hs. apply sat_split in Hs.
  destruct Hs as [m1 [m2 [o1 [o2 [JM [JO [HC [k HK]]]]]]]].
  apply sat_split in HK. destruct HK as [m3 [m4 [o3 [o4 [JM2 [JO2 [HT HI]]]]]]].
  unfold invlth_isr in HI. rewrite Nat.sub_0_r in HI.
  apply invisr_imply_noisr' in HI; [ | intros; apply Hclear].
  apply (V293_time_noisr_core bn) in HI.
  apply V293_time_switch_core_equiv in HI.
  assert (Hpack : (ge, le, M, ir, aux, O, op) |=
    (isrclr ** Aie false) ** (ATopis k ** (V293_time_switch_core bn))).
  { apply sat_split'. exists m1. exists m2. exists o1. exists o2. repeat first [assumption | split].
    apply sat_split'. exists m3. exists m4. exists o3. exists o4. repeat first [assumption | split]. }
  unfold V293_shared_flags. sep auto.
Qed.
Lemma V293_time_switch_close : forall bn, V293_shared_flags ** (V293_time_switch_core bn) ==> SWINV (V293_time_shared_inv bn).
Proof.
  intros bn s Hs. destruct s as [[[[[[ge le] M] ir] aux] O] op].
  assert (Hclear : forall i, ir i = false).
  { eapply (V293_shared_clear_state ge le M ir aux O op). unfold V293_shared_flags in Hs. sep auto. }
  unfold V293_shared_flags in Hs. sep normal in Hs. sep destruct Hs.
  assert (Hpack : (ge, le, M, ir, aux, O, op) |=
    (isrclr ** Aie false) ** (ATopis x ** (V293_time_switch_core bn))) by (sep auto).
  apply sat_split in Hpack. destruct Hpack as [m1 [m2 [o1 [o2 [JM [JO [HC HK]]]]]]].
  apply sat_split in HK. destruct HK as [m3 [m4 [o3 [o4 [JM2 [JO2 [HT HI]]]]]]].
  apply V293_time_switch_core_equiv in HI.
  apply (proj2 (V293_time_noisr_core bn x _)) in HI.
  apply V293_shared_clear_noisr_close in HI; [ | exact Hclear].
  unfold SWINV. apply sat_split'. exists m1. exists m2. exists o1. exists o2. repeat first [assumption | split].
  exists x. unfold invlth_isr. rewrite Nat.sub_0_r.
  apply sat_split'. exists m3. exists m4. exists o3. exists o4. repeat first [assumption | split].
Qed.

Definition V293_time_switch_full bn t := EX ts : TcbMod.map, EX es : EcbMod.map, EX n : int32,
  (EX tp : type, GV OSTCBCur @ (Tptr tp) |-> (Vptr t)) ** (V293_time_switch_fields bn) t ts es n.
Lemma V293_time_switch_full_open : forall bn t, SWINVt (V293_time_shared_inv bn) t ==> V293_shared_flags ** V293_time_switch_full bn t.
Proof.
  intros bn t s Hs. unfold SWINVt in Hs.
  assert (Ho : s |= (V293_shared_flags ** (V293_time_switch_core bn)) ** CurTid t).
  { eapply astar_mono; [apply V293_time_switch_open | intros st H; exact H | exact Hs]. }
  clear Hs. rename Ho into Hs.
  unfold V293_time_switch_core in Hs. sep normal in Hs. sep destruct Hs.
  assert (E : x = t).
  { eapply (V293_shared_current_agree x t (V293_shared_flags ** (V293_time_switch_fields bn) x x0 x1 x2) s). sep auto. } subst x.
  assert (Hp : s |= V293_shared_flags ** ((CurTid t ** CurTid t) ** (V293_time_switch_fields bn) t x0 x1 x2)) by (sep auto).
  eapply astar_mono in Hp; [ | intros st H; exact H | apply astar_mono; [apply V293_current_halves_write | intros st H; exact H]].
  unfold V293_time_switch_full. sep auto.
Qed.
Lemma V293_time_switch_full_close : forall bn t, V293_shared_flags ** V293_time_switch_full bn t ==> SWINVt (V293_time_shared_inv bn) t.
Proof.
  intros bn t s Hs. unfold V293_time_switch_full in Hs. sep normal in Hs. sep destruct Hs.
  assert (Hp : s |= (GV OSTCBCur @ (Tptr x2) |-> (Vptr t)) **
    (V293_shared_flags ** (V293_time_switch_fields bn) t x x0 x1)) by (sep auto).
  eapply astar_mono in Hp; [ | apply GV_separate_rw | intros st H; exact H].
  unfold SWINVt. apply astar_mono with (P := V293_shared_flags ** (V293_time_switch_core bn)) (Q := CurTid t).
  - apply V293_time_switch_close.
  - intros st H; exact H.
  - unfold V293_time_switch_core, CurTid. sep auto.
Qed.

Lemma V293_time_switch_store : forall bn ct t ge le M M' ir aux O op b tp,
  (ge, le, M, ir, aux, O, op) |= SWINVt (V293_time_shared_inv bn) ct ->
  get ge OSTCBCur = Some (b, Tptr tp) ->
  store (Tptr tp) M (b, 0%Z) (Vptr t) = Some M' ->
  (ge, le, M', ir, aux, set O curtid (oscurt t), op) |= SWINVt (V293_time_shared_inv bn) t.
Proof.
  intros bn ct t ge le M M' ir aux O op b tp Hs GE HS.
  apply V293_time_switch_full_open in Hs. unfold V293_time_switch_full in Hs. sep normal in Hs. sep destruct Hs.
  assert (Hpack : (ge, le, M, ir, aux, O, op) |=
    (GV OSTCBCur @ (Tptr x2) |-> (Vptr ct)) ** (V293_shared_flags ** (V293_time_switch_fields bn) ct x x0 x1)) by (sep auto).
  assert (ET : x2 = tp).
  { unfold Agvarmapsto in Hpack. sep normal in Hpack. sep destruct Hpack.
    apply sat_split in Hpack. destruct Hpack as [ma [mb [oa [ob [JM [JO [[b0 [G _]] HR]]]]]]].
    change (get ge OSTCBCur = Some (b0, Tptr x2)) in G. congruence. } subst x2.
  pose proof (V293_shared_store_global _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hpack GE HS) as Hstored.
  assert (Hhead : (ge, le, M', ir, aux, O, op) |= Aabsdata curtid (oscurt ct) **
    ((GV OSTCBCur @ (Tptr tp) |-> (Vptr t)) **
      (V293_shared_flags ** (Aabsdata abstcblsid (abstcblist x) **
        ((Aabsdata absecblsid (absecblist x0) ** Aabsdata ostmid (ostm x1)) **
          PV (bn,Int.zero) @ Tint32 |-> Vint32 x1))))).
  { clear Hs Hpack. unfold V293_time_switch_fields,V293_shared_fields in Hstored. sep auto. }
  apply V293_shared_replace_slot with (new := oscurt t) in Hhead.
  apply V293_time_switch_full_close. unfold V293_time_switch_full, V293_time_switch_fields, V293_shared_fields. clear Hs Hpack Hstored. sep auto.
Qed.

Theorem V293_time_shared_good : forall bn, GoodI (V293_time_shared_inv bn) V293_scheduler V293_shared_li.
Proof.
  intro bn. split.
  - intros o O Of op OO Hs JO. apply V293_time_noisr_core in Hs.
    assert (Forget : (o,O,op) |= V293_shared_core ** Atrue).
    { unfold V293_time_shared_core in Hs. sep normal in Hs. sep destruct Hs.
      eapply astar_mono with (Q':=Atrue) in Hs;[ | apply V293_time_fields_forget | intros st H;exact I].
      exact Hs. }
    eapply (V293_shared_no_abstract_frame (o, O, op) Of OO); [exact Forget | exact JO].
  - split.
    + intros o O op t Hs. destruct o as [[[[ge le] M] ir] aux].
      assert (HP : (ge, le, M, ir, aux, O, op) |= CurTid t ** Atrue).
      { change ((ge, le, M, ir, aux, O, op) |= SWINV (V293_time_shared_inv bn) ** CurTid t) in Hs. sep auto. }
      destruct (V293_shared_current_read _ _ _ _ _ _ _ _ _ HP) as [b [tp [GE LD]]].
      exists b. exists tp. split; [exact GE | ]. split; [exact LD | ].
      apply V293_time_switch_full_open in Hs. unfold V293_time_switch_full in Hs. sep normal in Hs. sep destruct Hs.
      change (get (getabst (ge, le, M, ir, aux, O, op)) curtid = Some (oscurt t)).
      eapply V293_star_abst_get_l with (p := Aabsdata curtid (oscurt t)) (q := Atrue).
      * apply V293_shared_abs_get.
      * unfold V293_time_switch_fields,V293_shared_fields in Hs. clear HP. sep auto.
    + split.
      * intros o O op t b tp M' ct Hs Hhighest GE HS.
        destruct o as [[[[ge le] M] ir] aux].
        assert (HT : exists ts, get O abstcblsid = Some (abstcblist ts)).
        { apply V293_time_switch_full_open in Hs. unfold V293_time_switch_full in Hs. sep normal in Hs. sep destruct Hs.
          exists x. change (get (getabst (ge, le, M, ir, aux, O, op)) abstcblsid = Some (abstcblist x)).
          eapply V293_star_abst_get_l with (p := Aabsdata abstcblsid (abstcblist x)) (q := Atrue).
          - apply V293_shared_abs_get.
          - unfold V293_time_switch_fields,V293_shared_fields in Hs. sep auto. }
        destruct HT as [ts HT]. exists ts. split; [exact HT | ].
        pose proof (V293_time_switch_store bn _ _ _ _ _ _ _ _ _ _ _ _ Hs GE HS) as Hnew.
        destruct (Classical_Prop.classic (indom ts ct)) as [Hm | Hm].
        -- left. split; assumption.
        -- right. split; [exact Hm | ]. intros Mx Ox MM OO HL JM JO.
           specialize (HL op). destruct HL as [lg HL].
           change (Mx = emp /\ Ox = emp) in HL. destruct HL as [EM EO]. subst Mx Ox.
           apply map_join_emp' in JM. apply map_join_emp' in JO. subst MM OO. exact Hnew.
      * apply V293_scheduler_good.
Qed.

(* The existence of the actual store is derived from reunited ownership,
   rather than supplied as a successful-store premise to this interface. *)
Theorem V293_time_owned_switch : forall bn ct t ts es n ge le M ir aux O op b tp,
  (ge,le,M,ir,aux,O,op) |= V293_shared_flags **
    ((GV OSTCBCur @ (Tptr tp) |-> Vptr ct) ** V293_time_switch_fields bn ct ts es n) ->
  get ge OSTCBCur = Some (b,Tptr tp) ->
  exists Mf,
    store (Tptr tp) M (b,0%Z) (Vptr t) = Some Mf /\
    (ge,le,Mf,ir,aux,set O curtid (oscurt t),op) |= SWINVt (V293_time_shared_inv bn) t /\
    get (set O curtid (oscurt t)) curtid = Some (oscurt t) /\
    get (set O curtid (oscurt t)) abstcblsid = Some (abstcblist ts) /\
    get (set O curtid (oscurt t)) absecblsid = Some (absecblist es) /\
    get (set O curtid (oscurt t)) ostmid = Some (ostm n) /\
    load (Tptr tp) Mf (b,0%Z) = Some (Vptr t) /\
    load Tint32 Mf (bn,0%Z) = Some (Vint32 n).
Proof.
  intros bn ct t ts es n ge le M ir aux O op b tp Owned GE.
  assert (Full : (ge,le,M,ir,aux,O,op) |=
    V293_shared_flags ** V293_time_switch_full bn ct).
  { unfold V293_time_switch_full. sep auto. }
  pose proof (V293_time_switch_full_close bn ct _ Full) as Entry.
  assert (Raw : (ge,le,M,ir,aux,O,op) |= Amapsto (b,0%Z) (Tptr tp) true (Vptr ct) ** Atrue).
  { assert (PointerOwned : (ge,le,M,ir,aux,O,op) |= (GV OSTCBCur @ (Tptr tp) |-> Vptr ct) ** Atrue) by (clear -Owned;sep auto).
    unfold Agvarmapsto in PointerOwned. sep normal in PointerOwned. sep destruct PointerOwned.
    assert (Same : x=b).
    { apply sat_split in PointerOwned. destruct PointerOwned as (ma & mb & oa & ob & JM & JO & [b0 [G [E _]]] & Rest).
      change (get ge OSTCBCur=Some(b0,Tptr tp)) in G.
      assert (b0=b) by congruence. subst b0. simpl in E. inversion E;reflexivity. }
    subst x. unfold Aptrmapsto in PointerOwned. change (addrval_to_addr (b,Int.zero)) with (b,0%Z) in PointerOwned. clear -PointerOwned;sep auto. }
  apply sat_split in Raw. destruct Raw as (m1 & m2 & o1 & o2 & JM & JO & [Points Empty] & Rest).
  destruct (store_exist_join' (b,0%Z) (Tptr tp) (Vptr ct) (Vptr t) m1 m2 M Points JM) as [Mf Store].
  pose proof (V293_time_switch_store bn _ _ _ _ _ _ _ _ _ _ _ _ Entry GE Store) as Reclosed.
  assert (Packed : (ge,le,M,ir,aux,O,op) |= (GV OSTCBCur @ (Tptr tp) |-> Vptr ct) **
    (V293_shared_flags ** V293_time_switch_fields bn ct ts es n)) by (clear -Owned;sep auto).
  pose proof (V293_shared_store_global _ _ _ _ _ _ _ _ _ _ _ _ _ _ Packed GE Store) as Stored.
  assert (Head : (ge,le,Mf,ir,aux,O,op) |= Aabsdata curtid (oscurt ct) **
    ((GV OSTCBCur @ (Tptr tp) |-> Vptr t) ** (V293_shared_flags **
      (Aabsdata abstcblsid (abstcblist ts) ** (Aabsdata absecblsid (absecblist es) **
        (Aabsdata ostmid (ostm n) ** PV (bn,Int.zero) @ Tint32 |-> Vint32 n)))))).
  { unfold V293_time_switch_fields,V293_shared_fields in Stored. clear -Stored. sep auto. }
  apply V293_shared_replace_slot with (new:=oscurt t) in Head.
  assert (Fields : (ge,le,Mf,ir,aux,set O curtid (oscurt t),op) |= V293_shared_fields t ts es n ** Atrue).
  { unfold V293_shared_fields. clear -Head. sep auto. }
  assert (Slots : get (set O curtid (oscurt t)) curtid=Some(oscurt t) /\
    get (set O curtid (oscurt t)) abstcblsid=Some(abstcblist ts) /\
    get (set O curtid (oscurt t)) absecblsid=Some(absecblist es) /\
    get (set O curtid (oscurt t)) ostmid=Some(ostm n)).
  { repeat split.
    - change (get (getabst (ge,le,Mf,ir,aux,set O curtid (oscurt t),op)) curtid=Some(oscurt t)).
      eapply V293_star_abst_get_l;[ | exact Fields]. intros st H.
      exact ((proj1) (V293_shared_fields_get _ _ _ _ st H)).
    - change (get (getabst (ge,le,Mf,ir,aux,set O curtid (oscurt t),op)) abstcblsid=Some(abstcblist ts)).
      eapply V293_star_abst_get_l;[ | exact Fields]. intros st H.
      exact ((fun Q => proj1 (proj2 Q)) (V293_shared_fields_get _ _ _ _ st H)).
    - change (get (getabst (ge,le,Mf,ir,aux,set O curtid (oscurt t),op)) absecblsid=Some(absecblist es)).
      eapply V293_star_abst_get_l;[ | exact Fields]. intros st H.
      exact ((fun Q => proj1 (proj2 (proj2 Q))) (V293_shared_fields_get _ _ _ _ st H)).
    - change (get (getabst (ge,le,Mf,ir,aux,set O curtid (oscurt t),op)) ostmid=Some(ostm n)).
      eapply V293_star_abst_get_l;[ | exact Fields]. intros st H.
      exact ((fun Q => proj2 (proj2 (proj2 Q))) (V293_shared_fields_get _ _ _ _ st H)).
  }
  assert (Current : load (Tptr tp) Mf (b,0%Z)=Some(Vptr t)).
  { assert (Half : (ge,le,Mf,ir,aux,set O curtid (oscurt t),op) |= CurTid t ** Atrue).
    { unfold SWINVt,CurTid in Reclosed |- *. clear -Reclosed;sep auto. }
    destruct (V293_shared_current_read _ _ _ _ _ _ _ _ _ Half) as [b' [tp' [G L]]].
    assert (b'=b /\ tp'=tp) by (split;congruence). destruct H;subst;exact L. }
  assert (Clock : load Tint32 Mf (bn,0%Z)=Some(Vint32 n)).
  { assert (Cell : (ge,le,Mf,ir,aux,set O curtid (oscurt t),op) |=
        (PV (bn,Int.zero) @ Tint32 |-> Vint32 n) ** Atrue).
    { clear -Head. sep auto. }
    change (load Tint32 (getmem (ge,le,Mf,ir,aux,set O curtid (oscurt t),op)) (bn,0%Z)=Some(Vint32 n)).
    eapply V293_star_load_l;[ | exact Cell]. intros st [P _]. eapply mapstoval_load;[reflexivity | exact P]. }
  exists Mf. destruct Slots as [C [T [E N]]]. repeat split;assumption.
Qed.
Print Assumptions V293_time_shared_good.
Print Assumptions V293_time_owned_switch.
