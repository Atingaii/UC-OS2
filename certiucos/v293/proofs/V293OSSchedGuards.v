Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.code.V293OSSchedDispatch.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Local Open Scope nat_scope.

Definition V293_guard_cell x b n : asrt :=
  (Agvarenv x Tint8 (b, 0%Z) //\\ A_notin_lenv x) **
    Amapsto (b, 0%Z) Tint8 false (V293_byteval n).

Lemma V293_guard_cell_good : forall x b n, GoodFrm (V293_guard_cell x b n).
Proof. intros; cbn [V293_guard_cell GoodFrm]; tauto. Qed.

Lemma V293_guard_eq_zero : forall n, n < 256 ->
  Int.eq (Int.repr (Z.of_nat n)) Int.zero = Nat.eqb n 0.
Proof.
  intros n Hn. destruct n as [  |  n]; [reflexivity | ]. simpl Nat.eqb. apply Int.eq_false.
  intro E. apply (f_equal Int.unsigned) in E.
  rewrite Int.unsigned_repr in E by
    (unfold Int.max_unsigned, Int.modulus, Int.wordsize; simpl; lia).
  change (Z.of_nat (S n) = 0)%Z in E. lia.
Qed.

(* The expression result is derived from byte ownership and environment
   lookup, not included as an evaluation oracle in the precondition. *)
Lemma V293_guard_eval : forall x b n rest s,
  n < 256 -> s |= V293_guard_cell x b n ** rest ->
  evalval (V293_OSSched_zero x) (getsmem s) =
    Some (Vint32 (if Nat.eqb n 0 then Int.one else Int.zero)) /\
  evaltype (V293_OSSched_zero x) (getsmem s) = Some Tint32.
Proof.
  intros x b n rest s Hn Hs.
  assert (E : get (getgenv s) x = Some (b, Tint8) /\ get (getlenv s) x = None).
  { eapply V293_star_env_l; [ | exact Hs]. intros s0 H0.
    eapply V293_star_env_l; [ | exact H0]. intros s1 [G N].
    destruct G as [b' [G [Eb _]]]. inversion Eb; subst b'.
    split; [exact G | ]. cbn [sat] in N.
    destruct (get (getlenv s1) x) as [v  |  ] eqn:Ev; [exfalso; apply N; exists v; exact Ev | reflexivity]. }
  assert (L : load Tint8 (getmem s) (b, 0%Z) = Some (V293_byteval n)).
  { eapply V293_star_load_l; [ | exact Hs]. intros s0 H0.
    eapply V293_star_load_r; [ | exact H0]. intros; eapply V293_mapsto_load; eauto. }
  destruct E as [G N]. destruct s as [[[[[[ge le] M] ir] aux] O] op].
  cbn [getgenv getlenv getmem get_smem get_genv get_lenv get_mem] in G, N, L.
  unfold V293_OSSched_zero. cbn [getsmem get_smem evalval evaltype get_lenv get_genv].
  rewrite N, G.
  cbn -[load].
  rewrite L. unfold V293_byteval.
  cbn [cast_eval bop_eval val_eq bop_type]. rewrite V293_guard_eq_zero by exact Hn.
  destruct (Nat.eqb n 0); split; reflexivity.
Qed.

Lemma V293_guard_defined : forall p x b n rest,
  n < 256 -> (p ==> V293_guard_cell x b n ** rest) ->
  p ==> EX v, Rv (V293_OSSched_zero x) @ Tint32 == v.
Proof.
  intros p x b n rest Hn Hp s Hs.
  destruct (V293_guard_eval x b n rest s Hn (Hp s Hs)) as [Ev Et].
  exists (Vint32 (if Nat.eqb n 0 then Int.one else Int.zero)).
  split; [exact Ev | ]. split; [exact Et | discriminate].
Qed.

Lemma V293_guard_true_zero : forall p x b n rest,
  n < 256 -> (p ==> V293_guard_cell x b n ** rest) ->
  forall s, s |= p //\\ Aistrue (V293_OSSched_zero x) -> n = 0.
Proof.
  intros p x b n rest Hn Hp s [Hs [v [Ev Hv]]].
  destruct (V293_guard_eval x b n rest s Hn (Hp s Hs)) as [E _].
  rewrite E in Ev. inversion Ev; subst v.
  destruct n; [reflexivity | ]. vm_compute in Hv; discriminate.
Qed.

Lemma V293_guard_false_nonzero : forall p x b n rest,
  n < 256 -> (p ==> V293_guard_cell x b n ** rest) ->
  forall s, s |= p //\\ Aisfalse (V293_OSSched_zero x) -> n <> 0.
Proof.
  intros p x b n rest Hn Hp s [Hs [v [Ev Hv]]] Ezero. subst n.
  destruct (V293_guard_eval x b 0 rest s Hn (Hp s Hs)) as [E _].
  rewrite E in Ev. inversion Ev; subst v. vm_compute in Hv; discriminate.
Qed.

(* No lock cell, lookup or body contract is needed on this path. *)
Theorem V293_OSSched_interrupt_skip : forall Spec sd li I r ri tid x lock b n rest body,
  n < 256 -> n <> 0 ->
  InfRules Spec sd li I r ri (V293_guard_cell x b n ** rest)
    (V293_OSSched_guards x lock body) (V293_guard_cell x b n ** rest) tid.
Proof.
  intros Spec sd li I r ri tid x lock b n rest body Hn Hnz.
  unfold V293_OSSched_guards. eapply ift_rule with (tp := Tint32).
  - eapply V293_guard_defined; [exact Hn | intros s Hs; exact Hs].
  - intros s [Hs _]; exact Hs.
  - eapply conseq_rule with (p := Afalse) (q := V293_guard_cell x b n ** rest).
    + intros s Hs. exfalso. apply Hnz. eapply V293_guard_true_zero; [exact Hn |   | exact Hs]. intros s0 H0; exact H0.
    + intros s Hs; exact Hs.
    + apply pfalse_rule.
Qed.

(* P is retained on either disabled branch; the enabled branch has the
   caller's explicit body proof. In particular, no context switch is assumed. *)
Theorem V293_OSSched_guards_rule : forall Spec sd li I r ri tid p q x lock bi bl ni nl ri_mem rl_mem body,
  ni < 256 -> nl < 256 ->
  (p ==> V293_guard_cell x bi ni ** ri_mem) ->
  (p ==> V293_guard_cell lock bl nl ** rl_mem) ->
  (ni = 0 -> nl = 0 -> InfRules Spec sd li I r ri p body q tid) ->
  InfRules Spec sd li I r ri p (V293_OSSched_guards x lock body)
    (if Nat.eqb ni 0 && Nat.eqb nl 0 then q else p) tid.
Proof.
  intros Spec sd li I r ri tid p q x lock bi bl ni nl ri_mem rl_mem body Hni Hnl Hi Hl Hb.
  destruct ni as [  |  ni].
  - unfold V293_OSSched_guards. eapply ift_rule with (tp := Tint32).
    + eapply V293_guard_defined; [exact Hni | exact Hi].
    + intros s Hs. exfalso. exact (V293_guard_false_nonzero p x bi 0 ri_mem Hni Hi s Hs eq_refl).
    + eapply conseq_rule with (p := p).
      * intros s [Hs _]; exact Hs.
      * intros s Hs; exact Hs.
      * eapply ift_rule with (tp := Tint32).
        -- eapply V293_guard_defined; [exact Hnl | exact Hl].
        -- intros s Hs. destruct nl as [  |  nl]; [exfalso; exact (V293_guard_false_nonzero p lock bl 0 rl_mem Hnl Hl s Hs eq_refl) | exact (proj1 Hs)].
        -- destruct nl as [  |  nl].
           ++ eapply conseq_rule; [ |   | apply Hb; reflexivity]; intros s Hs; [exact (proj1 Hs) | exact Hs].
           ++ eapply conseq_rule with (p := Afalse).
              ** intros s Hs. pose proof (V293_guard_true_zero p lock bl (S nl) rl_mem Hnl Hl s Hs). discriminate.
              ** intros s Hs; exact Hs.
              ** apply pfalse_rule.
  - unfold V293_OSSched_guards. eapply ift_rule with (tp := Tint32).
    + eapply V293_guard_defined; [exact Hni | exact Hi].
    + intros s [Hs _]; exact Hs.
    + eapply conseq_rule with (p := Afalse).
      * intros s Hs. pose proof (V293_guard_true_zero p x bi (S ni) ri_mem Hni Hi s Hs). discriminate.
      * intros s Hs; exact Hs.
      * apply pfalse_rule.
Qed.

(* Compose the existing two-statement proof with an explicitly OPEN suffix.
   The suffix proof is not supplied by this module. *)
Theorem V293_OSSched_guarded_prefix_continuation : forall Spec sd li I r ri tid aop frame
    sched_id unmap group rows high bt bg br bh lo hi table target tp bp bo entries tasks old
    interrupt lock bi bl ni nl suffix q (Hli : GoodLInvAsrt li),
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks -> GoodFrm frame ->
  ni < 256 -> nl < 256 ->
  Spec sched_id = Some
    (V293_sched_fpre unmap group rows high bt bg br bh li Hli,
     V293_sched_fpost unmap group rows high bt bg br bh li Hli, (Tvoid, nil)) ->
  let guardframe := V293_guard_cell interrupt bi ni ** (V293_guard_cell lock bl nl ** frame) in
  let pre := V293_sched_internal_pre unmap group rows high bt bg br bh lo hi li tid aop **
    (V293_prefix_frame table high target tp bp bo entries tasks guardframe ** V293_prefix_output tp bo old) in
  let mid := EX t : Modules.tid, [|V293_highest_ready tasks t|] **
    (V293_sched_internal_post unmap group rows high bt bg br bh lo hi li tid aop None **
      (V293_prefix_frame table high target tp bp bo entries tasks guardframe ** V293_prefix_output tp bo (Vptr t))) in
  (ni = 0 -> nl = 0 -> InfRules Spec sd li I r ri mid suffix q tid) ->
  InfRules Spec sd li I r ri pre
    (V293_OSSched_guards interrupt lock
      (sseq (V293_OSSched_unlocked_prefix sched_id table high target) suffix))
    (if Nat.eqb ni 0 && Nat.eqb nl 0 then q else pre) tid.
Proof.
  intros Spec sd li I r ri tid aop frame sched_id unmap group rows high bt bg br bh lo hi
    table target tp bp bo entries tasks old interrupt lock bi bl ni nl suffix q Hli
    Hlo Hhi Hr Hb Htable Hframe Hni Hnl Hspec guardframe pre mid Hsuffix.
  eapply V293_OSSched_guards_rule with
    (ri_mem := V293_sched_internal_pre unmap group rows high bt bg br bh lo hi li tid aop **
      ((V293_prefix_bindings table high target tp bp bo **
        (V293_read_pointers tp bp 0 entries ** Aabsdata abstcblsid (abstcblist tasks))) **
        ((V293_guard_cell lock bl nl ** frame) ** V293_prefix_output tp bo old)))
    (rl_mem := V293_sched_internal_pre unmap group rows high bt bg br bh lo hi li tid aop **
      ((V293_prefix_bindings table high target tp bp bo **
        (V293_read_pointers tp bp 0 entries ** Aabsdata abstcblsid (abstcblist tasks))) **
        ((V293_guard_cell interrupt bi ni ** frame) ** V293_prefix_output tp bo old)));
    try assumption.
  - unfold pre, guardframe, V293_prefix_frame. intros s Hs. sep auto.
  - unfold pre, guardframe, V293_prefix_frame. intros s Hs. sep auto.
  - intros Ei El. eapply seq_rule with (p' := mid).
    + apply V293_OSSched_unlocked_prefix_hoare with (Hli := Hli); try assumption.
      unfold guardframe. simpl GoodFrm.
      repeat split; try apply V293_guard_cell_good; assumption.
    + apply Hsuffix; assumption.
Qed.
