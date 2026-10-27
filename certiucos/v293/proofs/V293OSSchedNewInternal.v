(* Internal function contract for the same source-bound OS_SchedNew.
   Global storage is fixed by a future linker. Dynamic row snapshots and the
   caller's abstract operation travel through the framework's logic arguments.
   No local identifier or local address occurs in a funasrt. *)
Require Import Coq.Arith.Arith Coq.Lists.List Lia.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Local Open Scope nat_scope.

Definition V293_sched_globals unmap group rows high bt bg br bh : asrt :=
  Agvarenv unmap (Tarray Tint8 256) (bt, 0%Z) //\\
  Agvarenv group Tint8 (bg, 0%Z) //\\
  Agvarenv rows (Tarray Tint8 2) (br, 0%Z) //\\
  Agvarenv high Tint8 (bh, 0%Z).

Lemma V293_local_is_function_assertion : forall p,
  GoodLocalInvAsrt p -> GoodFunAsrt p.
Proof.
  induction p; simpl; intros Hgood; try exact I; try contradiction;
    try (destruct Hgood; split; auto); auto.
  destruct b; exact I.
Qed.

Lemma V293_CurLINV_function_assertion : forall li tid,
  GoodLInvAsrt li -> GoodFunAsrt (CurLINV li tid).
Proof.
  intros li tid H. unfold CurLINV, CurTid, LINV, Agvarmapsto, Agvarenv', Aptrmapsto.
  simpl. intros lg. repeat split; try exact I.
  apply V293_local_is_function_assertion. exact (proj1 (H tid lg)).
Qed.

Lemma V293_read_bytes_function_assertion : forall values b offset,
  GoodFunAsrt (V293_read_bytes b offset values).
Proof. induction values; intros; simpl; auto. Qed.

Definition V293_sched_internal_resource unmap group rows high bt bg br bh lo hi li tid hv :=
  ((V293_sched_globals unmap group rows high bt bg br bh **
    V293_sched_inputs bt bg br lo hi (V293_ready_group lo hi)) **
    (CurLINV li tid ** Aie false)) ** PV (bh, Int.zero) @ Tint8 |-> hv.

Definition V293_sched_internal_pre unmap group rows high bt bg br bh lo hi li tid aop :=
  EX hv : val,
    (<||aop||> ** V293_sched_internal_resource unmap group rows high bt bg br bh lo hi li tid hv) **
    [|lo < 256 /\ hi < 256 /\ (exists p, V293_bitmap_ready lo hi p)|].

Definition V293_sched_internal_post unmap group rows high bt bg br bh lo hi li tid aop (result : option val) :=
  [|result = None /\ V293_bitmap_ready lo hi (V293_ready_select lo hi (V293_ready_group lo hi)) /\
    (forall p, V293_bitmap_ready lo hi p -> V293_ready_select lo hi (V293_ready_group lo hi) <= p)|] **
  (<||aop||> ** V293_sched_internal_resource unmap group rows high bt bg br bh lo hi li tid
    (V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi)))).

Lemma V293_sched_internal_resource_good : forall unmap group rows high bt bg br bh lo hi li tid hv,
  GoodLInvAsrt li ->
  GoodFunAsrt (V293_sched_internal_resource unmap group rows high bt bg br bh lo hi li tid hv).
Proof.
  intros. unfold V293_sched_internal_resource, V293_sched_globals, V293_sched_inputs.
  repeat split; try exact I; try apply V293_read_bytes_function_assertion.
  apply V293_CurLINV_function_assertion. exact H.
Qed.

Lemma V293_sched_internal_pre_good : forall unmap group rows high bt bg br bh lo hi li tid aop,
  GoodLInvAsrt li ->
  GoodFunAsrt (V293_sched_internal_pre unmap group rows high bt bg br bh lo hi li tid aop).
Proof.
  intros. change (forall hv : val,
    (True /\ GoodFunAsrt (V293_sched_internal_resource unmap group rows high bt bg br bh lo hi li tid hv)) /\ True).
  intros hv. split; [split; [exact I | ] | exact I].
  apply V293_sched_internal_resource_good; exact H.
Qed.

Lemma V293_sched_internal_post_good : forall unmap group rows high bt bg br bh lo hi li tid aop result,
  GoodLInvAsrt li ->
  GoodFunAsrt (V293_sched_internal_post unmap group rows high bt bg br bh lo hi li tid aop result).
Proof.
  intros. change (True /\ (True /\ GoodFunAsrt
    (V293_sched_internal_resource unmap group rows high bt bg br bh lo hi li tid
      (V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi)))))).
  split; [exact I | ]. split; [exact I | ].
  apply V293_sched_internal_resource_good; exact H.
Qed.

Definition V293_sched_pre_asrt unmap group rows high bt bg br bh li tid (lg : list logicvar) :=
  match lg with
  | cons (logic_lv (cons (Vint32 low) (cons (Vint32 upper) nil)))
      (cons (logic_code aop) nil) =>
      V293_sched_internal_pre unmap group rows high bt bg br bh
        (Z.to_nat (Int.unsigned low)) (Z.to_nat (Int.unsigned upper)) li tid aop
  | _ => Afalse
  end.

Definition V293_sched_post_asrt unmap group rows high bt bg br bh li tid (lg : list logicvar) result :=
  match lg with
  | cons (logic_lv (cons (Vint32 low) (cons (Vint32 upper) nil)))
      (cons (logic_code aop) nil) =>
      V293_sched_internal_post unmap group rows high bt bg br bh
        (Z.to_nat (Int.unsigned low)) (Z.to_nat (Int.unsigned upper)) li tid aop result
  | _ => Afalse
  end.

Definition V293_sched_fpre (unmap group rows high : var) (bt bg br bh : block)
    (li : LocalInv) (Hli : GoodLInvAsrt li) : fpre.
Proof.
  intros vl lg tid. refine (@mkfunasrt (V293_sched_pre_asrt unmap group rows high bt bg br bh li tid lg) _).
  unfold V293_sched_pre_asrt.
  destruct lg as [ | snap lg]; [exact I | ].
  destruct snap; try exact I.
  destruct v as [ | low l]; [exact I | ].
  destruct low; try exact I.
  destruct l as [ | highbyte l]; [exact I | ].
  destruct highbyte; try exact I.
  destruct l; [ | exact I].
  destruct lg as [ | code lg]; [exact I | ].
  destruct code; try exact I.
  destruct lg; [ | exact I].
  apply V293_sched_internal_pre_good; exact Hli.
Defined.

Definition V293_sched_fpost (unmap group rows high : var) (bt bg br bh : block)
    (li : LocalInv) (Hli : GoodLInvAsrt li) : fpost.
Proof.
  intros vl result lg tid. refine (@mkfunasrt (V293_sched_post_asrt unmap group rows high bt bg br bh li tid lg result) _).
  unfold V293_sched_post_asrt.
  destruct lg as [ | snap lg]; [exact I | ].
  destruct snap; try exact I.
  destruct v as [ | low l]; [exact I | ].
  destruct low; try exact I.
  destruct l as [ | highbyte l]; [exact I | ].
  destruct highbyte; try exact I.
  destruct l; [ | exact I].
  destruct lg as [ | code lg]; [exact I | ].
  destruct code; try exact I.
  destruct lg; [ | exact I].
  apply V293_sched_internal_post_good; exact Hli.
Defined.

Lemma V293_single_local_not_shadow : forall le y x,
  x <> y -> eq_dom_env le (cons (y, Tint8) nil) -> get le x = None.
Proof.
  intros le y x Hxy Hd. destruct (get le x) as [[b t] | ] eqn:E; [ | reflexivity].
  exfalso. pose proof (proj2 (Hd x t) (ex_intro _ b E)) as Hin.
  simpl in Hin. destruct Hin as [Heq | Hfalse]; [inversion Heq; congruence | contradiction].
Qed.

Lemma V293_sched_entry_bindings : forall unmap group rows high y bt bg br bh byblock s,
  unmap <> y -> group <> y -> rows <> y -> high <> y ->
  eq_dom_env (getlenv s) (cons (y, Tint8) nil) ->
  s |= Alvarenv y Tint8 (byblock, 0%Z) ** V293_sched_globals unmap group rows high bt bg br bh ->
  s |= V293_sched_bindings unmap group rows high y bt bg br bh byblock.
Proof.
  intros unmap group rows high y bt bg br bh byblock s Hu Hg Hr Hh Hd Hs.
  assert (Eu : ~ indom (getlenv s) unmap).
  { intros [v E]. rewrite (@V293_single_local_not_shadow (getlenv s) y unmap Hu Hd) in E. discriminate. }
  assert (Eg : ~ indom (getlenv s) group).
  { intros [v E]. rewrite (@V293_single_local_not_shadow (getlenv s) y group Hg Hd) in E. discriminate. }
  assert (Er : ~ indom (getlenv s) rows).
  { intros [v E]. rewrite (@V293_single_local_not_shadow (getlenv s) y rows Hr Hd) in E. discriminate. }
  assert (Eh : ~ indom (getlenv s) high).
  { intros [v E]. rewrite (@V293_single_local_not_shadow (getlenv s) y high Hh Hd) in E. discriminate. }
  unfold V293_sched_bindings, V293_sched_globals in *.
  sep auto.
  destruct Hs as [Su [Sg [Sr Sh]]].
  pose proof Sh as HE. apply agvarenv_elim in HE. destruct HE as [_ HE].
  split; [exact Su | ]. split; [exact Sg | ]. split; [exact Sr | ]. split; [exact Sh | ].
  split; [apply alvarenv_intro; assumption | ].
  split; [apply anotinlenv_intro; assumption | ].
  split; [apply anotinlenv_intro; assumption | ].
  split; [apply anotinlenv_intro; assumption | ].
  apply anotinlenv_intro; assumption.
Qed.

Definition V293_sched_local_domain y := A_dom_lenv (cons (y, Tint8) nil).

Lemma V293_sched_entry_context : forall unmap group rows high y bt bg br bh byblock,
  unmap <> y -> group <> y -> rows <> y -> high <> y ->
  (Alvarenv y Tint8 (byblock, 0%Z) ** V293_sched_globals unmap group rows high bt bg br bh) **
    V293_sched_local_domain y ==>
  V293_sched_bindings unmap group rows high y bt bg br bh byblock ** V293_sched_local_domain y.
Proof.
  intros unmap group rows high y bt bg br bh byblock Hu Hg Hr Hh s Hs.
  unfold V293_sched_local_domain in *.
  apply astar_comm in Hs. apply astar_l_adomlenv_elim in Hs. destruct Hs as [Hd Hs].
  apply astar_comm. apply astar_l_adomlenv_intro; [ | exact Hd].
  eapply V293_sched_entry_bindings; eassumption.
Qed.

Lemma V293_entry_permute : forall L Y Op G R C E H D,
  (((L ** Y) ** Aemp) ** (Op ** (((G ** R) ** (C ** E)) ** H))) ** D ==>
  ((L ** G) ** D) ** (((Op ** R) ** (C ** E)) ** (Y ** H)).
Proof. intros. sep auto. Qed.

Lemma V293_sched_entry_resource : forall unmap group rows high y bt bg br bh byblock lo hi li tid aop yold hold,
  unmap <> y -> group <> y -> rows <> y -> high <> y ->
  (((Alvarenv y Tint8 (byblock, 0%Z) ** PV (byblock, Int.zero) @ Tint8 |-> yold) ** Aemp) **
    (<||aop||> ** V293_sched_internal_resource unmap group rows high bt bg br bh lo hi li tid hold)) **
    V293_sched_local_domain y ==>
  <||aop||> ** V293_sched_state
    (V293_sched_common unmap group rows high y bt bg br bh byblock lo hi (V293_ready_group lo hi)
      li tid (Aie false ** V293_sched_local_domain y)) byblock bh yold hold.
Proof.
  intros unmap group rows high y bt bg br bh byblock lo hi li tid aop yold hold Hu Hg Hr Hh s Hs.
  unfold V293_sched_internal_resource in Hs.
  apply V293_entry_permute in Hs.
  eapply astar_mono in Hs.
  2: { apply V293_sched_entry_context; assumption. }
  2: { intros s0 H0; exact H0. }
  unfold V293_sched_state, V293_sched_common.
  sep auto.
Qed.

Lemma V293_sched_return_bindings : forall unmap group rows high y bt bg br bh byblock,
  V293_sched_bindings unmap group rows high y bt bg br bh byblock ==>
  V293_sched_globals unmap group rows high bt bg br bh ** Alvarenv y Tint8 (byblock, 0%Z).
Proof.
  intros unmap group rows high y bt bg br bh byblock s Hs.
  unfold V293_sched_bindings in Hs.
  destruct Hs as [Su [Sg [Sr [Sh [Sl Hrest]]]]].
  pose proof Sl as El. apply alvarenv_elim in El. destruct El as [El _].
  apply astar_comm. apply astar_l_alvarenv_intro; [ | exact El].
  unfold V293_sched_globals. repeat split; assumption.
Qed.

Lemma V293_return_permute : forall Op B R C E D Y H,
  Op ** ((((B ** R) ** (C ** (E ** D))) ** Y) ** H) ==>
  B ** (Y ** (D ** (Op ** ((R ** (C ** E)) ** H)))).
Proof. intros. sep auto. Qed.

Lemma V293_return_pack : forall G L Y D Op R C E H,
  (G ** L) ** (Y ** (D ** (Op ** ((R ** (C ** E)) ** H)))) ==>
  (((L ** Y) ** Aemp) ** (Op ** (((G ** R) ** (C ** E)) ** H))) ** D.
Proof. intros. sep auto. Qed.

Lemma V293_local_return_pack : forall y byblock yv,
  (Alvarenv y Tint8 (byblock, 0%Z) ** PV (byblock, Int.zero) @ Tint8 |-> yv) ** Aemp ==>
  (EX v : val, LV y @ Tint8 |-> v) ** Aemp.
Proof.
  intros y byblock yv. apply astar_mono; [ | intros s H; exact H].
  intros s H. exists yv. unfold Alvarmapsto, Alvarenv'. exists byblock. exact H.
Qed.

Lemma V293_sched_return_resource : forall unmap group rows high y bt bg br bh byblock lo hi li tid aop yv hv,
  <||aop||> ** V293_sched_state
    (V293_sched_common unmap group rows high y bt bg br bh byblock lo hi (V293_ready_group lo hi)
      li tid (Aie false ** V293_sched_local_domain y)) byblock bh yv hv ==>
  ((EX v : val, LV y @ Tint8 |-> v) ** Aemp) **
    (<||aop||> ** V293_sched_internal_resource unmap group rows high bt bg br bh lo hi li tid hv) **
    V293_sched_local_domain y.
Proof.
  intros unmap group rows high y bt bg br bh byblock lo hi li tid aop yv hv s Hs.
  unfold V293_sched_state, V293_sched_common in Hs.
  apply V293_return_permute in Hs.
  eapply astar_mono in Hs.
  2: { apply V293_sched_return_bindings. }
  2: { intros s0 H0; exact H0. }
  apply V293_return_pack in Hs.
  eapply astar_mono in Hs.
  2: { apply astar_mono; [apply V293_local_return_pack | intros s0 H0; exact H0]. }
  2: { intros s0 H0; exact H0. }
  apply astar_assoc_elim in Hs. exact Hs.
Qed.

Lemma V293_entry_unpack : forall y (R : val -> asrt) Op D (pu : Prop),
  ((EX yv : val, LV y @ Tint8 |-> yv) ** Aemp) **
    ((EX hv : val, (Op ** R hv) ** [|pu|]) ** D) ==>
  EX hv : val, EX yv : val, EX byblock : block,
    (((((Alvarenv y Tint8 (byblock, 0%Z) ** PV (byblock, Int.zero) @ Tint8 |-> yv) ** Aemp) **
       (Op ** R hv)) ** D) ** [|pu|]).
Proof.
  intros y R Op D pu s Hs. unfold Alvarmapsto, Alvarenv' in Hs. sep auto.
Qed.

Lemma V293_pure_move : forall O Q (pu : Prop),
  O ** ([|pu|] ** Q) ==> [|pu|] ** (O ** Q).
Proof. intros. sep auto. Qed.

Lemma V293_sched_return_post : forall unmap group rows high y bt bg br bh byblock lo hi li tid aop result,
  <||aop||> ** V293_OSSchedNew_post
    (V293_sched_common unmap group rows high y bt bg br bh byblock lo hi (V293_ready_group lo hi)
      li tid (Aie false ** V293_sched_local_domain y)) byblock bh lo hi (V293_ready_group lo hi) result ==>
  ((EX v : val, LV y @ Tint8 |-> v) ** Aemp) **
    V293_sched_internal_post unmap group rows high bt bg br bh lo hi li tid aop result **
    V293_sched_local_domain y.
Proof.
  intros unmap group rows high y bt bg br bh byblock lo hi li tid aop result s Hs.
  unfold V293_OSSchedNew_post in Hs. apply V293_pure_move in Hs.
  apply astar_l_apure_elim in Hs. destruct Hs as [Hp Hs].
  apply V293_sched_return_resource in Hs.
  unfold V293_sched_internal_post. sep auto.
Qed.

Theorem V293_OSSchedNew_internal_resources : forall Spec sd li I tid aop
    unmap group rows high y bt bg br bh lo hi,
  unmap <> y -> group <> y -> rows <> y -> high <> y ->
  InfRules Spec sd li I
    (fun result => ((EX v : val, LV y @ Tint8 |-> v) ** Aemp) **
      V293_sched_internal_post unmap group rows high bt bg br bh lo hi li tid aop result **
      V293_sched_local_domain y) Afalse
    (((EX v : val, LV y @ Tint8 |-> v) ** Aemp) **
      V293_sched_internal_pre unmap group rows high bt bg br bh lo hi li tid aop **
      V293_sched_local_domain y)
    (V293_OSSchedNew_body unmap group rows high y) Afalse tid.
Proof.
  intros Spec sd li I tid aop unmap group rows high y bt bg br bh lo hi Hu Hg Hr Hh.
  eapply conseq_rule.
  - apply V293_entry_unpack.
  - intros s Hfalse; exact Hfalse.
  - apply ex_intro_rule. intros hold. apply ex_intro_rule. intros yold.
    apply ex_intro_rule. intros byblock. apply pure_split_rule.
    intros [Hlo [Hhi Hready]].
    eapply conseq_rule.
    + apply V293_sched_entry_resource; assumption.
    + intros s Hfalse; exact Hfalse.
    + eapply r_conseq_rule.
      3: { apply V293_OSSchedNew_body_hoare; auto. }
      * intros result. apply V293_sched_return_post.
      * intros s Hfalse; exact Hfalse.
Qed.

Lemma V293_sched_false_entry : forall Spec sd li I r tid y D body,
  InfRules Spec sd li I r Afalse
    (((EX v : val, LV y @ Tint8 |-> v) ** Aemp) ** Afalse ** D) body Afalse tid.
Proof.
  intros. eapply conseq_rule with (p := Afalse) (q := Afalse).
  - intros s H. apply astar_comm in H. apply astar_assoc_elim in H.
    apply astar_l_afalse_elim in H. exact H.
  - intros s H; exact H.
  - apply pfalse_rule.
Qed.

(* The stable contract uses the framework builders themselves, not aliases
   hiding an extra precondition or a stronger-than-declared local domain. *)
Theorem V293_OSSchedNew_internal_contract : forall P f Spec sd li I
    unmap group rows high y bt bg br bh (Hli : GoodLInvAsrt li)
    lg tid vl pre post,
  unmap <> y -> group <> y -> rows <> y -> high <> y ->
  P f = Some (V293_OSSchedNew_function unmap group rows high y) ->
  Some pre = BuildPreI P f vl lg (V293_sched_fpre unmap group rows high bt bg br bh li Hli) tid ->
  Some post = BuildRetI P f vl lg (V293_sched_fpost unmap group rows high bt bg br bh li Hli) tid ->
  InfRules Spec sd li I post Afalse pre
    (V293_OSSchedNew_body unmap group rows high y) Afalse tid.
Proof.
  intros P f Spec sd li I unmap group rows high y bt bg br bh Hli lg tid vl pre post
    Hu Hg Hr Hh Hcode Hpre Hpost.
  unfold BuildPreI in Hpre. rewrite Hcode in Hpre.
  destruct vl as [ | v vl].
  2: { assert (E : dl_vl_match dnil (rev (v :: vl)) = false).
       { destruct (rev (v :: vl)) eqn:Er; [ | reflexivity].
         apply (f_equal (@rev val)) in Er. rewrite rev_involutive in Er. discriminate. }
       unfold V293_OSSchedNew_function in Hpre. rewrite E in Hpre. discriminate. }
  change (Some pre = Some (((EX v : val, LV y @ Tint8 |-> v) ** Aemp) **
    V293_sched_pre_asrt unmap group rows high bt bg br bh li tid lg **
    V293_sched_local_domain y)) in Hpre.
  inversion Hpre; subst pre.
  unfold BuildRetI in Hpost. rewrite Hcode in Hpost.
  change (Some post = Some (fun result => ((EX v : val, LV y @ Tint8 |-> v) ** Aemp) **
    V293_sched_post_asrt unmap group rows high bt bg br bh li tid lg result **
    V293_sched_local_domain y)) in Hpost.
  inversion Hpost; subst post.
  destruct lg as [ | snap lg]; [apply V293_sched_false_entry | ].
  destruct snap; try apply V293_sched_false_entry.
  destruct v as [ | low l]; [apply V293_sched_false_entry | ].
  destruct low; try apply V293_sched_false_entry.
  destruct l as [ | upper l]; [apply V293_sched_false_entry | ].
  destruct upper; try apply V293_sched_false_entry.
  destruct l; [ | apply V293_sched_false_entry].
  destruct lg as [ | code lg]; [apply V293_sched_false_entry | ].
  destruct code; try apply V293_sched_false_entry.
  destruct lg; [ | apply V293_sched_false_entry].
  apply V293_OSSchedNew_internal_resources; assumption.
Qed.

Definition V293_OSSchedNew_internal_unit (sched_id : fid) (unmap group rows high y : var) : progunit :=
  fun f => if Z.eq_dec f sched_id then
    Some (V293_OSSchedNew_function unmap group rows high y) else None.

Definition V293_OSSchedNew_internal_spec sched_id unmap group rows high bt bg br bh
    li (Hli : GoodLInvAsrt li) : funspec :=
  fun f => if Z.eq_dec f sched_id then Some
    (V293_sched_fpre unmap group rows high bt bg br bh li Hli,
     V293_sched_fpost unmap group rows high bt bg br bh li Hli, (Tvoid, nil)) else None.

Lemma V293_OSSchedNew_internal_domains : forall sched_id unmap group rows high y bt bg br bh li Hli,
  EqDom (V293_OSSchedNew_internal_unit sched_id unmap group rows high y)
    (V293_OSSchedNew_internal_spec sched_id unmap group rows high bt bg br bh li Hli).
Proof.
  intros. intros f. unfold V293_OSSchedNew_internal_unit, V293_OSSchedNew_internal_spec.
  destruct (Z.eq_dec f sched_id); split; intros [a H]; try discriminate; eexists; reflexivity.
Qed.

Theorem V293_OSSchedNew_WFFunEnv : forall sched_id unmap group rows high y bt bg br bh li Hli sd I,
  unmap <> y -> group <> y -> rows <> y -> high <> y ->
  WFFunEnv (V293_OSSchedNew_internal_unit sched_id unmap group rows high y)
    (V293_OSSchedNew_internal_spec sched_id unmap group rows high bt bg br bh li Hli) sd li I.
Proof.
  intros sched_id unmap group rows high y bt bg br bh li Hli sd I Hu Hg Hr Hh. split.
  - apply V293_OSSchedNew_internal_domains.
  - intros f pre post t tl Hspec. unfold V293_OSSchedNew_internal_spec in Hspec.
    destruct (Z.eq_dec f sched_id); try discriminate. inversion Hspec; subst pre post t tl.
    exists dnil. exists (dcons y Tint8 dnil). exists (V293_OSSchedNew_body unmap group rows high y).
    split.
    + unfold V293_OSSchedNew_internal_unit. destruct (Z.eq_dec f sched_id); [reflexivity | contradiction].
    + split; [constructor | ]. split; [reflexivity | ].
      intros vl pre post lg tid Hpre Hpost.
      eapply V293_OSSchedNew_internal_contract; try eassumption.
      unfold V293_OSSchedNew_internal_unit. destruct (Z.eq_dec f sched_id); [reflexivity | contradiction].
Qed.

Theorem V293_OSSchedNew_internal_builders : forall sched_id unmap group rows high y bt bg br bh li Hli lg tid,
  exists pre post,
    Some pre = BuildPreI (V293_OSSchedNew_internal_unit sched_id unmap group rows high y) sched_id nil lg
      (V293_sched_fpre unmap group rows high bt bg br bh li Hli) tid /\
    Some post = BuildRetI (V293_OSSchedNew_internal_unit sched_id unmap group rows high y) sched_id nil lg
      (V293_sched_fpost unmap group rows high bt bg br bh li Hli) tid.
Proof.
  intros. unfold BuildPreI, BuildRetI, V293_OSSchedNew_internal_unit.
  destruct (Z.eq_dec sched_id sched_id); [ | contradiction]. eexists. eexists. split; reflexivity.
Qed.
