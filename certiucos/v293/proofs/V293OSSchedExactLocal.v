(* Exact scheduler resources. Weakening is used only for read/side conditions;
   the two real assignments and return keep p_local in their assertions. *)
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCritical.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Local Open Scope nat_scope.

Lemma V293_exact_local_weakens : forall li tid,
 p_local li tid nil ==> CurLINV li tid.
Proof. intros li tid s H;exists (@nil logicvar);unfold p_local in H;sep auto. Qed.
Lemma V293_exact_local_good : forall li tid,
 GoodLInvAsrt li -> GoodFunAsrt(p_local li tid nil).
Proof.
 intros li tid H;unfold p_local,LINV,CurTid,Agvarmapsto,Agvarenv',Aptrmapsto.
 cbn[GoodFunAsrt];repeat split;try exact I;try(intros;repeat split;exact I).
 apply V293_local_is_function_assertion;exact(proj1(H tid nil)).
Qed.
Definition V293_sched_exact_common unmap group rows high y bt bg br bh byblock lo hi g li tid frame :=
 (V293_sched_bindings unmap group rows high y bt bg br bh byblock **
  V293_sched_inputs bt bg br lo hi g) ** (p_local li tid nil ** frame).
Lemma V293_sched_exact_common_weakens : forall unmap group rows high y bt bg br bh byblock lo hi g li tid frame,
 V293_sched_exact_common unmap group rows high y bt bg br bh byblock lo hi g li tid frame ==>
 V293_sched_common unmap group rows high y bt bg br bh byblock lo hi g li tid frame.
Proof.
 intros unmap group rows high y bt bg br bh byblock lo hi g li tid frame s H;
 unfold V293_sched_exact_common,V293_sched_common in *.
 eapply astar_mono;[intros s0 H0;exact H0|apply astar_mono;[apply V293_exact_local_weakens|intros s0 H0;exact H0]|exact H].
Qed.
Lemma V293_sched_exact_common_env : forall unmap group rows high y bt bg br bh byblock lo hi g li tid frame s,
 s |=V293_sched_exact_common unmap group rows high y bt bg br bh byblock lo hi g li tid frame ->
 V293_sched_read_env(getgenv s)(getlenv s)unmap group rows bt bg br /\
 get(getlenv s)y=Some(byblock,Tint8) /\ get(getlenv s)high=None /\ get(getgenv s)high=Some(bh,Tint8).
Proof. intros;eapply V293_sched_common_env;apply V293_sched_exact_common_weakens;exact H. Qed.
Lemma V293_sched_exact_common_reads : forall unmap group rows high y bt bg br bh byblock lo hi g li tid frame,
 lo<256 ->hi<256 ->g<256 ->forall s,
 s |=V293_sched_exact_common unmap group rows high y bt bg br bh byblock lo hi g li tid frame ->
 V293_sched_read_memory(getmem s)bt bg br lo hi g.
Proof. intros;eapply V293_sched_common_reads;try eassumption;apply V293_sched_exact_common_weakens;exact H2. Qed.
Lemma V293_sched_exact_common_local : forall unmap group rows high y bt bg br bh byblock lo hi g li tid frame,
 V293_sched_exact_common unmap group rows high y bt bg br bh byblock lo hi g li tid frame ==>CurLINV li tid.
Proof. intros unmap group rows high y bt bg br bh byblock lo hi g li tid frame s H.
 eapply V293_sched_common_CurLINV;apply V293_sched_exact_common_weakens;exact H. Qed.

Theorem V293_OSSchedNew_exact_row : forall Spec sd li I r ri tid aop frame
    unmap group rows high y bt bg br bh byblock lo hi g yold hold,
  lo < 256 -> hi < 256 -> g < 256 ->
  let common := V293_sched_exact_common unmap group rows high y bt bg br bh byblock lo hi g li tid frame in
  InfRules Spec sd li I r ri
    (<||aop||> ** V293_sched_state common byblock bh yold hold)
    (sassign (evar y) (V293_OSSchedNew_row_expr unmap group))
    (<||aop||> ** V293_sched_state common byblock bh (V293_byteval (V293_ready_lookup g)) hold) tid.
Proof.
  intros Spec sd li I r ri tid aop frame unmap group rows high y bt bg br bh byblock lo hi g yold hold Hlo Hhi Hg common.
  unfold V293_sched_state. eapply conseq_rule.
  - apply astar_mono; [intros s H; exact H | apply V293_three_swap].
  - apply astar_mono; [intros s H; exact H | apply V293_three_swap].
  - eapply assign_rule with (tp2 := Tint8).
    + apply eq_int. auto.
    + intros s Hs.
      assert (He : V293_sched_read_env (getgenv s) (getlenv s) unmap group rows bt bg br /\
        get (getlenv s) y = Some (byblock, Tint8) /\
        get (getlenv s) high = None /\ get (getgenv s) high = Some (bh, Tint8)).
      { eapply V293_star_env_l; [ | exact Hs]. intros s0 H0.
        eapply V293_star_env_l; [ | exact H0]. apply V293_sched_exact_common_env. }
      assert (Hm : V293_sched_read_memory (getmem s) bt bg br lo hi g).
      { eapply V293_star_reads_l; [ | exact Hs]. intros s0 H0.
        eapply V293_star_reads_l; [ | exact H0]. apply V293_sched_exact_common_reads; assumption. }
      destruct He as [He [Ey _]].
      destruct s as [[[[[[ge le] M] irs] aux] O] op].
      cbn [getgenv getlenv getmem get_smem get_genv get_lenv get_mem] in He, Ey, Hm.
      destruct (V293_OSSchedNew_row_eval ge le M unmap group rows bt bg br lo hi g He Hm Hg) as [Ev Et].
      split.
      * cbn [sat evaladdr evaltype getsmem get_smem get_lenv]. rewrite Ey. auto.
      * cbn [sat getsmem]. split; [exact Ev | ]. split; [exact Et | unfold V293_byteval; discriminate].
    + intros s Hs. eapply V293_star_CurLINV_l; [ | exact Hs]. intros s0 H0.
      eapply V293_star_CurLINV_l; [ | exact H0]. apply V293_sched_exact_common_local.
Qed.

Theorem V293_OSSchedNew_exact_priority : forall Spec sd li I r ri tid aop frame
    unmap group rows high y bt bg br bh byblock lo hi g hold,
  lo < 256 -> hi < 256 -> g < 256 -> g = V293_ready_group lo hi ->
  (exists p, V293_bitmap_ready lo hi p) ->
  let common := V293_sched_exact_common unmap group rows high y bt bg br bh byblock lo hi g li tid frame in
  InfRules Spec sd li I r ri
    (<||aop||> ** V293_sched_state common byblock bh (V293_byteval (V293_ready_lookup g)) hold)
    (sassign (evar high) (V293_OSSchedNew_priority_expr unmap rows y))
    (<||aop||> ** V293_sched_state common byblock bh (V293_byteval (V293_ready_lookup g))
      (V293_byteval (V293_ready_select lo hi g))) tid.
Proof.
  intros Spec sd li I r ri tid aop frame unmap group rows high y bt bg br bh byblock lo hi g hold Hlo Hhi Hg Hgroup Hready common.
  unfold V293_sched_state. eapply assign_rule with (tp2 := Tint8).
  - apply eq_int. auto.
  - intros s Hs.
    assert (He : V293_sched_read_env (getgenv s) (getlenv s) unmap group rows bt bg br /\
      get (getlenv s) y = Some (byblock, Tint8) /\
      get (getlenv s) high = None /\ get (getgenv s) high = Some (bh, Tint8)).
    { eapply V293_star_env_l; [ | exact Hs]. intros s0 H0.
      eapply V293_star_env_l; [ | exact H0]. apply V293_sched_exact_common_env. }
    assert (Hm : V293_sched_read_memory (getmem s) bt bg br lo hi g).
    { eapply V293_star_reads_l; [ | exact Hs]. intros s0 H0.
      eapply V293_star_reads_l; [ | exact H0]. apply V293_sched_exact_common_reads; assumption. }
    assert (Yload : load Tint8 (getmem s) (byblock, 0%Z) = Some (V293_byteval (V293_ready_lookup g))).
    { eapply V293_star_load_l; [ | exact Hs]. intros s0 H0.
      eapply V293_star_load_r; [ | exact H0]. intros s1 H1.
      change (s1 |= Amapsto (byblock, 0%Z) Tint8 true (V293_byteval (V293_ready_lookup g))) in H1.
      eapply V293_mapsto_load; [ | exact H1].
      pose proof (proj1 (V293_ready_row_spec g Hg)). lia. }
    destruct He as [He [Ey [Eh Gh]]].
    destruct s as [[[[[[ge le] M] irs] aux] O] op].
    cbn [getgenv getlenv getmem get_smem get_genv get_lenv get_mem] in He, Ey, Eh, Gh, Hm, Yload.
    destruct (V293_OSSchedNew_priority_eval ge le M unmap group rows y bt bg br byblock lo hi g
      He Hm Ey Yload Hlo Hhi Hgroup Hready) as [Ev Et].
    split.
    + cbn [sat evaladdr evaltype getsmem get_smem get_lenv get_genv]. rewrite Eh, Gh. auto.
    + cbn [sat getsmem get_smem]. split; [exact Ev | ]. split; [exact Et | unfold V293_byteval; discriminate].
  - intros s Hs. eapply V293_star_CurLINV_l; [ | exact Hs]. intros s0 H0.
    eapply V293_star_CurLINV_l; [ | exact H0]. apply V293_sched_exact_common_local.
Qed.

(* Function body only: entry allocation, local-byte disposal and the internal
   function specification table remain separate component-linking obligations.
   The caller's exact p_local is kept; side-condition weakening does not
   replace the preserved resource or the ambient rule invariant. *)
Theorem V293_OSSchedNew_exact_body : forall Spec sd li I tid aop frame
    unmap group rows high y bt bg br bh byblock lo hi g yold hold,
  lo < 256 -> hi < 256 -> g = V293_ready_group lo hi ->
  (exists p, V293_bitmap_ready lo hi p) ->
  let common := V293_sched_exact_common unmap group rows high y bt bg br bh byblock lo hi g li tid frame in
  InfRules Spec sd li I
    (fun result => <||aop||> ** V293_OSSchedNew_post common byblock bh lo hi g result) Afalse
    (<||aop||> ** V293_sched_state common byblock bh yold hold)
    (V293_OSSchedNew_body unmap group rows high y) Afalse tid.
Proof.
  intros Spec sd li I tid aop frame unmap group rows high y bt bg br bh byblock lo hi g yold hold Hlo Hhi Hgroup Hready common.
  assert (Hg : g < 256).
  { rewrite Hgroup. unfold V293_ready_group. destruct (lo =? 0); destruct (hi =? 0); simpl; lia. }
  unfold V293_OSSchedNew_body, V293_OSSchedNew_updates. eapply seq_rule.
  - eapply seq_rule.
    + apply V293_OSSchedNew_exact_row; assumption.
    + apply V293_OSSchedNew_exact_priority; assumption.
  - apply ret_rule. apply astar_mono; [intros s H; exact H | ]. intros s Hs.
    unfold V293_OSSchedNew_post. apply astar_l_apure_intro; [exact Hs | ].
    split; [reflexivity | ]. exact (proj2 (V293_ready_selection lo hi g Hlo Hhi Hgroup Hready)).
Qed.

Definition V293_sched_exact_resource unmap group rows high bt bg br bh lo hi li tid hv :=
  ((V293_sched_globals unmap group rows high bt bg br bh **
    V293_sched_inputs bt bg br lo hi (V293_ready_group lo hi)) **
    (p_local li tid nil ** Aie false)) ** PV (bh, Int.zero) @ Tint8 |-> hv.

Definition V293_sched_exact_pre unmap group rows high bt bg br bh lo hi li tid aop :=
  EX hv : val,
    (<||aop||> ** V293_sched_exact_resource unmap group rows high bt bg br bh lo hi li tid hv) **
    [|lo < 256 /\ hi < 256 /\ (exists p, V293_bitmap_ready lo hi p)|].

Definition V293_sched_exact_post unmap group rows high bt bg br bh lo hi li tid aop (result : option val) :=
  [|result = None /\ V293_bitmap_ready lo hi (V293_ready_select lo hi (V293_ready_group lo hi)) /\
    (forall p, V293_bitmap_ready lo hi p -> V293_ready_select lo hi (V293_ready_group lo hi) <= p)|] **
  (<||aop||> ** V293_sched_exact_resource unmap group rows high bt bg br bh lo hi li tid
    (V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi)))).

Lemma V293_sched_exact_resource_good : forall unmap group rows high bt bg br bh lo hi li tid hv,
  GoodLInvAsrt li ->
  GoodFunAsrt (V293_sched_exact_resource unmap group rows high bt bg br bh lo hi li tid hv).
Proof.
  intros. unfold V293_sched_exact_resource, V293_sched_globals, V293_sched_inputs.
  repeat split; try exact I; try apply V293_read_bytes_function_assertion.
  apply V293_exact_local_good. exact H.
Qed.

Lemma V293_sched_exact_pre_good : forall unmap group rows high bt bg br bh lo hi li tid aop,
  GoodLInvAsrt li ->
  GoodFunAsrt (V293_sched_exact_pre unmap group rows high bt bg br bh lo hi li tid aop).
Proof.
  intros. change (forall hv : val,
    (True /\ GoodFunAsrt (V293_sched_exact_resource unmap group rows high bt bg br bh lo hi li tid hv)) /\ True).
  intros hv. split; [split; [exact I | ] | exact I].
  apply V293_sched_exact_resource_good; exact H.
Qed.

Lemma V293_sched_exact_post_good : forall unmap group rows high bt bg br bh lo hi li tid aop result,
  GoodLInvAsrt li ->
  GoodFunAsrt (V293_sched_exact_post unmap group rows high bt bg br bh lo hi li tid aop result).
Proof.
  intros. change (True /\ (True /\ GoodFunAsrt
    (V293_sched_exact_resource unmap group rows high bt bg br bh lo hi li tid
      (V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi)))))).
  split; [exact I | ]. split; [exact I | ].
  apply V293_sched_exact_resource_good; exact H.
Qed.


Lemma V293_sched_exact_entry : forall unmap group rows high y bt bg br bh byblock lo hi li tid aop yold hold (payload : asrt),
  unmap <> y -> group <> y -> rows <> y -> high <> y ->
  (((Alvarenv y Tint8 (byblock, 0%Z) ** PV (byblock, Int.zero) @ Tint8 |-> yold) ** Aemp) **
    (<||aop||> ** (V293_sched_exact_resource unmap group rows high bt bg br bh lo hi li tid hold ** payload))) **
    V293_sched_local_domain y ==>
  <||aop||> ** V293_sched_state
    (V293_sched_exact_common unmap group rows high y bt bg br bh byblock lo hi (V293_ready_group lo hi)
      li tid ((Aie false ** payload) ** V293_sched_local_domain y)) byblock bh yold hold.
Proof.
  intros unmap group rows high y bt bg br bh byblock lo hi li tid aop yold hold payload Hu Hg Hr Hh s Hs.
  unfold V293_sched_exact_resource in Hs.
  assert (Hs' : s |= ((Alvarenv y Tint8 (byblock, 0%Z) **
    V293_sched_globals unmap group rows high bt bg br bh) ** V293_sched_local_domain y) **
    (((<||aop||> ** V293_sched_inputs bt bg br lo hi (V293_ready_group lo hi)) **
       (p_local li tid nil ** (Aie false ** payload))) **
       (PV (byblock, Int.zero) @ Tint8 |-> yold ** PV (bh, Int.zero) @ Tint8 |-> hold))).
  { sep auto. }
  clear Hs. rename Hs' into Hs.
  eapply astar_mono in Hs.
  2: { apply V293_sched_entry_context; assumption. }
  2: { intros s0 H0; exact H0. }
  unfold V293_sched_state, V293_sched_exact_common.
  sep auto.
Qed.

Lemma V293_sched_exact_return : forall unmap group rows high y bt bg br bh byblock lo hi li tid aop yv hv (payload : asrt),
  <||aop||> ** V293_sched_state
    (V293_sched_exact_common unmap group rows high y bt bg br bh byblock lo hi (V293_ready_group lo hi)
      li tid ((Aie false ** payload) ** V293_sched_local_domain y)) byblock bh yv hv ==>
  ((EX v : val, LV y @ Tint8 |-> v) ** Aemp) **
    (<||aop||> ** (V293_sched_exact_resource unmap group rows high bt bg br bh lo hi li tid hv ** payload)) **
    V293_sched_local_domain y.
Proof.
  intros unmap group rows high y bt bg br bh byblock lo hi li tid aop yv hv payload s Hs.
  unfold V293_sched_state, V293_sched_exact_common in Hs.
  assert (Hs' : s |= V293_sched_bindings unmap group rows high y bt bg br bh byblock **
    (PV (byblock, Int.zero) @ Tint8 |-> yv ** (V293_sched_local_domain y **
      (<||aop||> ** ((V293_sched_inputs bt bg br lo hi (V293_ready_group lo hi) **
        (p_local li tid nil ** Aie false)) ** PV (bh, Int.zero) @ Tint8 |-> hv) ** payload)))).
  { sep auto. }
  clear Hs. rename Hs' into Hs.
  eapply astar_mono in Hs.
  2: { apply V293_sched_return_bindings. }
  2: { intros s0 H0; exact H0. }
  assert (Hs' : s |= (((Alvarenv y Tint8 (byblock, 0%Z) ** PV (byblock, Int.zero) @ Tint8 |-> yv) ** Aemp) **
    (<||aop||> ** (V293_sched_exact_resource unmap group rows high bt bg br bh lo hi li tid hv ** payload))) **
      V293_sched_local_domain y).
  { unfold V293_sched_exact_resource. sep auto. }
  apply astar_assoc_elim in Hs'.
  eapply astar_mono; [apply V293_local_return_pack | intros s0 H0; exact H0 | exact Hs'].
Qed.

(* The same two assignments and return prove preservation of payload. *)
Lemma V293_sched_exact_payload : forall Spec sd li I tid aop
    unmap group rows high y bt bg br bh lo hi payload,
  unmap <> y -> group <> y -> rows <> y -> high <> y ->
  InfRules Spec sd li I
    (fun result => ((EX v : val, LV y @ Tint8 |-> v) ** Aemp) **
      (V293_sched_exact_post unmap group rows high bt bg br bh lo hi li tid aop result ** payload) **
      V293_sched_local_domain y) Afalse
    (((EX v : val, LV y @ Tint8 |-> v) ** Aemp) **
      (V293_sched_exact_pre unmap group rows high bt bg br bh lo hi li tid aop ** payload) **
      V293_sched_local_domain y)
    (V293_OSSchedNew_body unmap group rows high y) Afalse tid.
Proof.
  intros Spec sd li I tid aop unmap group rows high y bt bg br bh lo hi payload Hu Hg Hr Hh.
  eapply conseq_rule with (p := EX hv : val, EX yv : val, EX byblock : block,
    (((((Alvarenv y Tint8 (byblock, 0%Z) ** PV (byblock, Int.zero) @ Tint8 |-> yv) ** Aemp) **
       (<||aop||> ** (V293_sched_exact_resource unmap group rows high bt bg br bh lo hi li tid hv ** payload))) **
       V293_sched_local_domain y) ** [|lo < 256 /\ hi < 256 /\ (exists p, V293_bitmap_ready lo hi p)|])).
  - unfold V293_sched_exact_pre, Alvarmapsto, Alvarenv'. intros s Hs. sep auto.
  - intros s Hfalse; exact Hfalse.
  - apply ex_intro_rule. intros hold. apply ex_intro_rule. intros yold.
    apply ex_intro_rule. intros byblock. apply pure_split_rule. intros [Hlo [Hhi Hready]].
    eapply conseq_rule.
    + apply V293_sched_exact_entry; assumption.
    + intros s Hfalse; exact Hfalse.
    + eapply r_conseq_rule.
      3: { apply V293_OSSchedNew_exact_body; auto. }
      * intros result s Hs. unfold V293_OSSchedNew_post in Hs.
        apply V293_pure_move in Hs. apply astar_l_apure_elim in Hs.
        destruct Hs as [Hp Hs]. apply V293_sched_exact_return in Hs.
        unfold V293_sched_exact_post. sep auto.
      * intros s Hfalse; exact Hfalse.
Qed.


Definition V293_sched_exact_critical_pre unmap group rows high bt bg br bh li I tid lg :=
  match V293_critical_args lg with
  | Some (lo, hi, aop, stack, critical) =>
      V293_sched_exact_pre unmap group rows high bt bg br bh lo hi li tid aop **
        V293_sched_critical I stack critical
  | None => Afalse
  end.
Definition V293_sched_exact_critical_post unmap group rows high bt bg br bh li I tid lg result :=
  match V293_critical_args lg with
  | Some (lo, hi, aop, stack, critical) =>
      V293_sched_exact_post unmap group rows high bt bg br bh lo hi li tid aop result **
        V293_sched_critical I stack critical
  | None => Afalse
  end.
Definition V293_sched_exact_fpre (unmap group rows high : var) (bt bg br bh : block) (li : LocalInv) (I : Inv)
    (Hli : GoodLInvAsrt li) : fpre.
Proof.
  intros vl lg tid. refine (@mkfunasrt
    (V293_sched_exact_critical_pre unmap group rows high bt bg br bh li I tid lg) _).
  unfold V293_sched_exact_critical_pre. destruct (V293_critical_args lg) as [[[[[lo hi] op] stack] critical] | ]; [ | exact Logic.I].
  split; [apply V293_sched_exact_pre_good; exact Hli | apply V293_sched_critical_good].
Defined.
Definition V293_sched_exact_fpost (unmap group rows high : var) (bt bg br bh : block) (li : LocalInv) (I : Inv)
    (Hli : GoodLInvAsrt li) : fpost.
Proof.
  intros vl result lg tid. refine (@mkfunasrt
    (V293_sched_exact_critical_post unmap group rows high bt bg br bh li I tid lg result) _).
  unfold V293_sched_exact_critical_post. destruct (V293_critical_args lg) as [[[[[lo hi] op] stack] critical] | ]; [ | exact Logic.I].
  split; [apply V293_sched_exact_post_good; exact Hli | apply V293_sched_critical_good].
Defined.

(* Resource ownership I and ambient rule invariant RI need not coincide. *)
Theorem V293_OSSchedNew_exact_contract : forall P f Spec sd li I RI
    unmap group rows high y bt bg br bh (Hli : GoodLInvAsrt li) lg tid vl pre post,
  unmap <> y -> group <> y -> rows <> y -> high <> y ->
  P f = Some (V293_OSSchedNew_function unmap group rows high y) ->
  Some pre = BuildPreI P f vl lg (V293_sched_exact_fpre unmap group rows high bt bg br bh li I Hli) tid ->
  Some post = BuildRetI P f vl lg (V293_sched_exact_fpost unmap group rows high bt bg br bh li I Hli) tid ->
  InfRules Spec sd li RI post Afalse pre (V293_OSSchedNew_body unmap group rows high y) Afalse tid.
Proof.
  intros P f Spec sd li I RI unmap group rows high y bt bg br bh Hli lg tid vl pre post
    Hu Hg Hr Hh Hcode Hpre Hpost.
  unfold BuildPreI in Hpre. rewrite Hcode in Hpre.
  destruct vl as [ | v vl].
  2: { assert (E : dl_vl_match dnil (rev (v :: vl)) = false).
       { destruct (rev (v :: vl)) eqn:Er; [ | reflexivity].
         apply (f_equal (@rev val)) in Er. rewrite rev_involutive in Er. discriminate. }
       unfold V293_OSSchedNew_function in Hpre. rewrite E in Hpre. discriminate. }
  change (Some pre = Some (((EX v : val, LV y @ Tint8 |-> v) ** Aemp) **
    V293_sched_exact_critical_pre unmap group rows high bt bg br bh li I tid lg ** V293_sched_local_domain y)) in Hpre.
  inversion Hpre; subst pre.
  unfold BuildRetI in Hpost. rewrite Hcode in Hpost.
  change (Some post = Some (fun result => ((EX v : val, LV y @ Tint8 |-> v) ** Aemp) **
    V293_sched_exact_critical_post unmap group rows high bt bg br bh li I tid lg result ** V293_sched_local_domain y)) in Hpost.
  inversion Hpost; subst post.
  unfold V293_sched_exact_critical_pre, V293_sched_exact_critical_post.
  destruct (V293_critical_args lg) as [[[[[lo hi] op] stack] critical] | ];
    [apply V293_sched_exact_payload; assumption | apply V293_sched_false_entry].
Qed.


Definition V293_sched_exact_spec sched_id unmap group rows high bt bg br bh li I
    (Hli : GoodLInvAsrt li) : funspec :=
  fun f => if Z.eq_dec f sched_id then Some
    (V293_sched_exact_fpre unmap group rows high bt bg br bh li I Hli,
     V293_sched_exact_fpost unmap group rows high bt bg br bh li I Hli, (Tvoid, nil)) else None.
(* Resource ownership I and ambient rule invariant RI need not coincide. *)
Theorem V293_OSSchedNew_exact_WFFunEnv : forall sched_id unmap group rows high y bt bg br bh li I RI Hli sd,
  unmap <> y -> group <> y -> rows <> y -> high <> y ->
  WFFunEnv (V293_OSSchedNew_internal_unit sched_id unmap group rows high y)
    (V293_sched_exact_spec sched_id unmap group rows high bt bg br bh li I Hli) sd li RI.
Proof.
  intros sched_id unmap group rows high y bt bg br bh li I RI Hli sd Hu Hg Hr Hh. split.
  - intros f. unfold V293_OSSchedNew_internal_unit, V293_sched_exact_spec.
    destruct (Z.eq_dec f sched_id); split; intros [a H]; try discriminate; eexists; reflexivity.
  - intros f pre post t tl Hspec. unfold V293_sched_exact_spec in Hspec.
    destruct (Z.eq_dec f sched_id); try discriminate. inversion Hspec; subst pre post t tl.
    exists dnil. exists (dcons y Tint8 dnil). exists (V293_OSSchedNew_body unmap group rows high y).
    split.
    + unfold V293_OSSchedNew_internal_unit. destruct (Z.eq_dec f sched_id); [reflexivity | contradiction].
    + split; [constructor | ]. split; [reflexivity | ].
      intros vl pre post lg tid Hpre Hpost.
      eapply V293_OSSchedNew_exact_contract; try eassumption.
      unfold V293_OSSchedNew_internal_unit. destruct (Z.eq_dec f sched_id); [reflexivity | contradiction].
Qed.


Lemma V293_sched_exact_resource_local : forall unmap group rows high bt bg br bh lo hi li tid hv,
  V293_sched_exact_resource unmap group rows high bt bg br bh lo hi li tid hv ==> CurLINV li tid.
Proof.
  intros unmap group rows high bt bg br bh lo hi li tid hv. unfold V293_sched_exact_resource.
  apply V293_star_CurLINV_l. apply V293_star_CurLINV_r.
  apply V293_star_CurLINV_l. apply V293_exact_local_weakens.
Qed.

Lemma V293_sched_exact_pre_local : forall unmap group rows high bt bg br bh lo hi li tid aop,
  V293_sched_exact_pre unmap group rows high bt bg br bh lo hi li tid aop ==> CurLINV li tid.
Proof.
  intros unmap group rows high bt bg br bh lo hi li tid aop s [hv Hs].
  eapply V293_star_CurLINV_l; [ | exact Hs].
  apply V293_star_CurLINV_r. apply V293_sched_exact_resource_local.
Qed.

Lemma V293_sched_exact_post_local : forall unmap group rows high bt bg br bh lo hi li tid aop result,
  V293_sched_exact_post unmap group rows high bt bg br bh lo hi li tid aop result ==> CurLINV li tid.
Proof.
  intros unmap group rows high bt bg br bh lo hi li tid aop result. unfold V293_sched_exact_post.
  apply V293_star_CurLINV_r. apply V293_star_CurLINV_r.
  apply V293_sched_exact_resource_local.
Qed.


Theorem V293_OSSchedNew_exact_call : forall Spec sd li I RI r ri tid aop frame
    sched_id unmap group rows high bt bg br bh lo hi stack critical (Hli : GoodLInvAsrt li),
  lo < 256 -> hi < 256 -> GoodFrm frame ->
  Spec sched_id = Some
    (V293_sched_exact_fpre unmap group rows high bt bg br bh li I Hli,
     V293_sched_exact_fpost unmap group rows high bt bg br bh li I Hli, (Tvoid, nil)) ->
  InfRules Spec sd li RI r ri
    ((V293_sched_exact_pre unmap group rows high bt bg br bh lo hi li tid aop **
       V293_sched_critical I stack critical) ** frame)
    (scall sched_id nil)
    (EX result : option val,
      (V293_sched_exact_post unmap group rows high bt bg br bh lo hi li tid aop result **
        V293_sched_critical I stack critical) ** frame) tid.
Proof.
  intros Spec sd li I RI r ri tid aop frame sched_id unmap group rows high bt bg br bh lo hi stack critical Hli
    Hlo Hhi Hframe Hspec.
  assert (Ep : getasrt (V293_sched_exact_fpre unmap group rows high bt bg br bh li I Hli nil
    (V293_critical_call_lg lo hi aop stack critical) tid) =
    V293_sched_exact_pre unmap group rows high bt bg br bh lo hi li tid aop ** V293_sched_critical I stack critical).
  { change (V293_sched_exact_critical_pre unmap group rows high bt bg br bh li I tid
      (V293_critical_call_lg lo hi aop stack critical) =
      V293_sched_exact_pre unmap group rows high bt bg br bh lo hi li tid aop ** V293_sched_critical I stack critical).
    unfold V293_sched_exact_critical_pre. rewrite V293_critical_args_roundtrip by assumption. reflexivity. }
  assert (Eq : forall result, getasrt (V293_sched_exact_fpost unmap group rows high bt bg br bh li I Hli nil result
    (V293_critical_call_lg lo hi aop stack critical) tid) =
    V293_sched_exact_post unmap group rows high bt bg br bh lo hi li tid aop result ** V293_sched_critical I stack critical).
  { intro. change (V293_sched_exact_critical_post unmap group rows high bt bg br bh li I tid
      (V293_critical_call_lg lo hi aop stack critical) result =
      V293_sched_exact_post unmap group rows high bt bg br bh lo hi li tid aop result ** V293_sched_critical I stack critical).
    unfold V293_sched_exact_critical_post. rewrite V293_critical_args_roundtrip by assumption. reflexivity. }
  eapply conseq_rule with (q := EX result : option val,
    getasrt (V293_sched_exact_fpost unmap group rows high bt bg br bh li I Hli nil result
      (V293_critical_call_lg lo hi aop stack critical) tid) ** frame).
  - intros s H; exact H.
  - intros s [result Hs]. exists result. rewrite Eq in Hs. exact Hs.
  - eapply call_rule with
      (pre := V293_sched_exact_fpre unmap group rows high bt bg br bh li I Hli)
      (post := V293_sched_exact_fpost unmap group rows high bt bg br bh li I Hli)
      (vl := nil) (logicl := V293_critical_call_lg lo hi aop stack critical) (tp := Tvoid) (tl := nil).
    + exact Hframe.
    + exact Hspec.
    + rewrite Ep. intros s H; exact H.
    + intros s H. reflexivity.
    + reflexivity.
    + rewrite Ep. eapply V293_star_CurLINV_l. apply V293_sched_exact_pre_local.
    + intros s [result Hs]. rewrite Eq in Hs.
      eapply V293_star_CurLINV_l; [ | exact Hs]. apply V293_sched_exact_post_local.
Qed.


Theorem V293_sched_exact_post_retains : forall unmap group rows high bt bg br bh lo hi li tid aop result,
 V293_sched_exact_post unmap group rows high bt bg br bh lo hi li tid aop result ==>
 [|result=None|] ** (p_local li tid nil **
 (<||aop||> ** ((V293_sched_globals unmap group rows high bt bg br bh **
 V293_sched_inputs bt bg br lo hi(V293_ready_group lo hi)) **
 (Aie false ** PV(bh,Int.zero)@Tint8|->
 V293_byteval(V293_ready_select lo hi(V293_ready_group lo hi)))))).
Proof.
 intros unmap group rows high bt bg br bh lo hi li tid aop result s H;
 unfold V293_sched_exact_post,V293_sched_exact_resource in H.
 apply astar_l_apure_elim in H;destruct H as [[E _] H].
 apply astar_l_apure_intro;[ |exact E];sep auto.
Qed.
