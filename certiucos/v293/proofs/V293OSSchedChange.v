Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.code.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCall.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.code.V293OSSchedDispatch.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import Coq.Lists.List Lia.
Local Open Scope nat_scope.

Definition V293_counter_bindings counter b : asrt :=
  Agvarenv counter Tint32 (b, 0%Z) //\\ A_notin_lenv counter.
Definition V293_counter_cell counter b c : asrt :=
  V293_counter_bindings counter b ** PV (b, Int.zero) @ Tint32 |-> (Vint32 c).

Lemma V293_counter_cell_good : forall x b c, GoodFrm (V293_counter_cell x b c).
Proof. intros; cbn [V293_counter_cell V293_counter_bindings Aptrmapsto GoodFrm]; tauto. Qed.

Lemma V293_counter_env : forall x b s,
  s |= V293_counter_bindings x b ->
  get (getgenv s) x = Some (b, Tint32) /\ get (getlenv s) x = None.
Proof.
  intros x b s [G [N _]]. destruct G as [b' [G [Eb _]]]. inversion Eb; subst b'.
  split; [exact G | ]. destruct (get (getlenv s) x) as [v | ] eqn:E; [ | reflexivity].
  exfalso. apply N. exists v; exact E.
Qed.

(* No no-overflow premise: every Int.int value, including max_unsigned. *)
Theorem V293_OSSched_counter_increment : forall Spec sd li I r ri tid aop frame counter b c,
  (frame ==> CurLINV li tid) ->
  InfRules Spec sd li I r ri (<||aop||> ** (frame ** V293_counter_cell counter b c))
    (V293_OSSched_increment counter)
    (<||aop||> ** (frame ** V293_counter_cell counter b (Int.add c Int.one))) tid.
Proof.
  intros Spec sd li I r ri tid aop frame counter b c Hinv.
  unfold V293_OSSched_increment, V293_counter_cell.
  eapply conseq_rule with
    (p := <||aop||> ** ((V293_counter_bindings counter b ** frame) ** PV (b, Int.zero) @ Tint32 |-> (Vint32 c)))
    (q := <||aop||> ** ((V293_counter_bindings counter b ** frame) ** PV (b, Int.zero) @ Tint32 |-> (Vint32 (Int.add c Int.one)))).
  - intros s Hs. sep auto.
  - intros s Hs. sep auto.
  - eapply assign_rule with (tp2 := Tint32).
    + apply eq_int. auto.
    + intros s Hs.
      assert (E : get (getgenv s) counter = Some (b, Tint32) /\ get (getlenv s) counter = None).
      { eapply V293_star_env_l; [ | exact Hs]. intros s0 H0.
        eapply V293_star_env_l; [ | exact H0]. apply V293_counter_env. }
      assert (L : load Tint32 (getmem s) (b, 0%Z) = Some (Vint32 c)).
      { eapply V293_star_load_r; [ | exact Hs]. intros s0 [Hm _].
        eapply mapstoval_load; [reflexivity | exact Hm]. }
      destruct E as [G N]. destruct s as [[[[[[ge le] M] irs] aux] O] op].
      cbn [getgenv getlenv getmem get_smem get_genv get_lenv get_mem] in G, N, L.
      split.
      * cbn [sat evaladdr evaltype getsmem get_smem get_lenv get_genv]. rewrite N, G. auto.
      * cbn [sat getsmem get_smem evalval evaltype get_lenv get_genv]. rewrite N, G.
        cbn -[load]. rewrite L. repeat split; try reflexivity; discriminate.
    + intros s Hs. eapply V293_star_CurLINV_l; [ | exact Hs].
      eapply V293_star_CurLINV_r; exact Hinv.
Qed.

Lemma V293_byte_variable : forall s x b n,
  get (getgenv s) x = Some (b, Tint8) -> get (getlenv s) x = None ->
  load Tint8 (getmem s) (b, 0%Z) = Some (V293_byteval n) ->
  evalval (ecast (evar x) Tint32) (getsmem s) = Some (V293_byteval n) /\
  evaltype (ecast (evar x) Tint32) (getsmem s) = Some Tint32.
Proof.
  intros s x b n G N L. destruct s as [[[[[[ge le] M] irs] aux] O] op].
  cbn [getgenv getlenv getmem get_smem get_genv get_lenv get_mem] in G, N, L.
  cbn [getsmem get_smem evalval evaltype get_lenv get_genv]. rewrite N, G.
  cbn -[load]. rewrite L. split; reflexivity.
Qed.

Lemma V293_current_variable : forall x b n rest s,
  n < 256 -> s |= V293_guard_cell x b n ** rest ->
  evalval (ecast (evar x) Tint32) (getsmem s) = Some (V293_byteval n) /\
  evaltype (ecast (evar x) Tint32) (getsmem s) = Some Tint32.
Proof.
  intros x b n rest s Hn Hs. eapply V293_byte_variable.
  - eapply V293_star_env_l with (E := fun ge _ => get ge x = Some (b, Tint8)); [ | exact Hs].
    intros s0 H0. eapply V293_star_env_l with (E := fun ge _ => get ge x = Some (b, Tint8)); [ | exact H0].
    intros s1 [G _]. destruct G as [b' [G [Eb _]]]. inversion Eb; subst; exact G.
  - eapply V293_star_env_l with (E := fun _ le => get le x = None); [ | exact Hs].
    intros s0 H0. eapply V293_star_env_l with (E := fun _ le => get le x = None); [ | exact H0].
    intros s1 [_ [N _]]. destruct (get (getlenv s1) x) as [v | ] eqn:E; [ | reflexivity].
    exfalso. apply N. exists v; exact E.
  - eapply V293_star_load_l; [ | exact Hs]. intros s0 H0.
    eapply V293_star_load_r; [ | exact H0]. intros; eapply V293_mapsto_load; eauto.
Qed.

Lemma V293_byte_eq : forall n m, n < 256 -> m < 256 ->
  Int.eq (Int.repr (Z.of_nat n)) (Int.repr (Z.of_nat m)) = Nat.eqb n m.
Proof.
  intros n m Hn Hm. destruct (Nat.eqb n m) eqn:E.
  - apply Nat.eqb_eq in E. subst m. apply Int.eq_true.
  - apply Int.eq_false. intro Eq. apply (f_equal Int.unsigned) in Eq.
    repeat rewrite Int.unsigned_repr in Eq by
      (unfold Int.max_unsigned, Int.modulus, Int.wordsize; simpl; lia).
    apply Nat.eqb_neq in E. apply E. lia.
Qed.

(* Same state and same task table as the prefix; current priority and the
   writable UINT32 counter are carried through its frame, not new oracles. *)
Section Tail.
Variables unmap group rows high : var.
Variables bt bg br bh : block.
Variables lo hi : nat.
Variable li : LocalInv.
Variable tid : Modules.tid.
Variable aop : spec_code.
Variables table target : var.
Variable tp : type.
Variables bp bo : block.
Variable entries : list val.
Variable tasks : TcbMod.map.
Variables current counter : var.
Variables bcur bcounter : block.
Variable nc : nat.
Variable frame : asrt.

Definition V293_OSSched_tail_state c : asrt :=
  EX t : Modules.tid, [|V293_highest_ready tasks t|] **
    (V293_sched_internal_post unmap group rows high bt bg br bh lo hi li tid aop None **
      (V293_prefix_frame table high target tp bp bo entries tasks
        (V293_guard_cell current bcur nc ** frame) **
        (V293_prefix_output tp bo (Vptr t) ** V293_counter_cell counter bcounter c))).

Lemma V293_tail_high : forall c s,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  s |= V293_OSSched_tail_state c ->
  evalval (ecast (evar high) Tint32) (getsmem s) =
    Some (V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi))) /\
  evaltype (ecast (evar high) Tint32) (getsmem s) = Some Tint32.
Proof.
  intros c s Hlo Hhi Hr [t Hs].
  assert (Hs' : s |= V293_sched_internal_resource unmap group rows high bt bg br bh lo hi li tid
      (V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi))) **
    (V293_prefix_bindings table high target tp bp bo ** Atrue)).
  { unfold V293_sched_internal_post, V293_prefix_frame in Hs. sep auto. }
  eapply V293_byte_variable.
  - eapply V293_star_env_l with (E := fun ge _ => get ge high = Some (bh, Tint8)); [ | exact Hs']. apply V293_prefix_high_global.
  - eapply V293_star_env_r with (E := fun _ le => get le high = None); [ | exact Hs'].
    intros s0 H0. eapply V293_star_env_l with (E := fun _ le => get le high = None); [ | exact H0].
    intros s1 H1. exact (proj1 (proj2 (proj2 (proj2 (V293_prefix_bindings_view _ _ _ _ _ _ _ H1))))).
  - eapply V293_star_load_l; [ | exact Hs']. intros s0 H0.
    eapply V293_prefix_selected_load; eauto.
Qed.

Theorem V293_OSSched_priority_comparison : forall c s,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) -> nc < 256 ->
  s |= V293_OSSched_tail_state c ->
  evalval (V293_OSSched_different high current) (getsmem s) =
    Some (Vint32 (if Nat.eqb (V293_ready_select lo hi (V293_ready_group lo hi)) nc then Int.zero else Int.one)) /\
  evaltype (V293_OSSched_different high current) (getsmem s) = Some Tint32.
Proof.
  intros c s Hlo Hhi Hr Hnc Hs.
  destruct (V293_tail_high c s Hlo Hhi Hr Hs) as [Eh Th].
  assert (Hs' : s |= V293_guard_cell current bcur nc ** Atrue).
  { destruct Hs as [t Hs]. unfold V293_prefix_frame in Hs. sep auto. }
  destruct (V293_current_variable current bcur nc Atrue s Hnc Hs') as [Ec Tc].
  unfold V293_OSSched_different. destruct s as [[[[[[ge le] M] irs] aux] O] op].
  cbn [getsmem get_smem evalval evaltype] in Eh, Th, Ec, Tc |- *. rewrite Eh, Ec, Th, Tc.
  unfold V293_byteval. cbn [bop_eval val_eq bop_type]. rewrite V293_byte_eq.
  - destruct (Nat.eqb (V293_ready_select lo hi (V293_ready_group lo hi)) nc); split; reflexivity.
  - pose proof (V293_ready_selection_range lo hi (V293_ready_group lo hi) Hlo Hhi eq_refl Hr). lia.
  - exact Hnc.
Qed.

Theorem V293_OSSched_tail_increment : forall Spec sd I r ri c,
  InfRules Spec sd li I r ri (V293_OSSched_tail_state c)
    (V293_OSSched_increment counter) (V293_OSSched_tail_state (Int.add c Int.one)) tid.
Proof.
  intros Spec sd I r ri c. unfold V293_OSSched_tail_state.
  apply ex_intro_rule. intro t.
  eapply conseq_rule with
    (p := <||aop||> **
      (([|V293_highest_ready tasks t|] **
        ([|(None : option val) = None /\ V293_bitmap_ready lo hi (V293_ready_select lo hi (V293_ready_group lo hi)) /\
          (forall p, V293_bitmap_ready lo hi p -> V293_ready_select lo hi (V293_ready_group lo hi) <= p)|] **
          (V293_sched_internal_resource unmap group rows high bt bg br bh lo hi li tid
            (V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi))) **
            (V293_prefix_frame table high target tp bp bo entries tasks
              (V293_guard_cell current bcur nc ** frame) ** V293_prefix_output tp bo (Vptr t))))) **
        V293_counter_cell counter bcounter c))
    (q := <||aop||> **
      (([|V293_highest_ready tasks t|] **
        ([|(None : option val) = None /\ V293_bitmap_ready lo hi (V293_ready_select lo hi (V293_ready_group lo hi)) /\
          (forall p, V293_bitmap_ready lo hi p -> V293_ready_select lo hi (V293_ready_group lo hi) <= p)|] **
          (V293_sched_internal_resource unmap group rows high bt bg br bh lo hi li tid
            (V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi))) **
            (V293_prefix_frame table high target tp bp bo entries tasks
              (V293_guard_cell current bcur nc ** frame) ** V293_prefix_output tp bo (Vptr t))))) **
        V293_counter_cell counter bcounter (Int.add c Int.one))).
  - unfold V293_sched_internal_post. intros s Hs. sep auto; assumption.
  - unfold V293_sched_internal_post. intros s Hs. exists t. sep auto; assumption.
  - apply V293_OSSched_counter_increment.
    intros s Hs. eapply V293_star_CurLINV_r; [ | exact Hs].
    intros s0 H0. eapply V293_star_CurLINV_r; [ | exact H0].
    intros s1 H1. eapply V293_star_CurLINV_l; [ | exact H1].
    apply V293_sched_internal_resource_CurLINV.
Qed.

(* The continuation is still the REAL switch obligation. It is deliberately
   not replaced by an assumed contract for an ordinary OSCtxSw call. *)
Theorem V293_OSSched_change_continuation : forall Spec sd I r ri c suffix q,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) -> nc < 256 ->
  (V293_ready_select lo hi (V293_ready_group lo hi) <> nc ->
    InfRules Spec sd li I r ri (V293_OSSched_tail_state (Int.add c Int.one)) suffix q tid) ->
  InfRules Spec sd li I r ri (V293_OSSched_tail_state c)
    (V293_OSSched_change high current counter suffix)
    (if Nat.eqb (V293_ready_select lo hi (V293_ready_group lo hi)) nc then V293_OSSched_tail_state c else q) tid.
Proof.
  intros Spec sd I r ri c suffix q Hlo Hhi Hr Hnc Hsuffix.
  unfold V293_OSSched_change. eapply ift_rule with (tp := Tint32).
  - intros s Hs. destruct (V293_OSSched_priority_comparison c s Hlo Hhi Hr Hnc Hs) as [Ev Et].
    eexists. split; [exact Ev | ]. split; [exact Et | discriminate].
  - intros s [Hs [v [Ev Hv]]].
    destruct (V293_OSSched_priority_comparison c s Hlo Hhi Hr Hnc Hs) as [E _].
    rewrite E in Ev. inversion Ev; subst v.
    destruct (Nat.eqb (V293_ready_select lo hi (V293_ready_group lo hi)) nc); [exact Hs | vm_compute in Hv; discriminate].
  - destruct (Nat.eqb (V293_ready_select lo hi (V293_ready_group lo hi)) nc) eqn:En.
    + eapply conseq_rule with (p := Afalse).
      * intros s [Hs [v [Ev Hv]]].
        destruct (V293_OSSched_priority_comparison c s Hlo Hhi Hr Hnc Hs) as [E _].
        rewrite En in E. rewrite E in Ev. inversion Ev; subst v. vm_compute in Hv; discriminate.
      * intros s Hs; exact Hs.
      * apply pfalse_rule.
    + eapply conseq_rule with (p := V293_OSSched_tail_state c).
      * intros s [Hs _]; exact Hs.
      * intros s Hs; exact Hs.
      * eapply seq_rule.
        -- apply V293_OSSched_tail_increment.
        -- apply Hsuffix. apply Nat.eqb_neq; exact En.
Qed.

(* Discharge the previous checkpoint's open suffix as far as the counter.
   Only the context-switch continuation remains a premise. *)
Theorem V293_OSSched_changed_prefix_continuation : forall Spec sd I r ri sched_id old c suffix q
    (Hli : GoodLInvAsrt li),
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) -> nc < 256 ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks -> GoodFrm frame ->
  Spec sched_id = Some
    (V293_sched_fpre unmap group rows high bt bg br bh li Hli,
     V293_sched_fpost unmap group rows high bt bg br bh li Hli, (Tvoid, nil)) ->
  (V293_ready_select lo hi (V293_ready_group lo hi) <> nc ->
    InfRules Spec sd li I r ri (V293_OSSched_tail_state (Int.add c Int.one)) suffix q tid) ->
  InfRules Spec sd li I r ri
    (V293_sched_internal_pre unmap group rows high bt bg br bh lo hi li tid aop **
      (V293_prefix_frame table high target tp bp bo entries tasks
        (V293_guard_cell current bcur nc ** frame) **
        (V293_prefix_output tp bo old ** V293_counter_cell counter bcounter c)))
    (sseq (V293_OSSched_unlocked_prefix sched_id table high target)
      (V293_OSSched_change high current counter suffix))
    (if Nat.eqb (V293_ready_select lo hi (V293_ready_group lo hi)) nc then V293_OSSched_tail_state c else q) tid.
Proof.
  intros Spec sd I r ri sched_id old c suffix q Hli Hlo Hhi Hr Hnc Hb Htable Hframe Hspec Hsuffix.
  eapply seq_rule with (p' := V293_OSSched_tail_state c).
  - eapply conseq_rule with
      (p := V293_sched_internal_pre unmap group rows high bt bg br bh lo hi li tid aop **
        (V293_prefix_frame table high target tp bp bo entries tasks
          (V293_guard_cell current bcur nc ** (V293_counter_cell counter bcounter c ** frame)) **
          V293_prefix_output tp bo old))
      (q := EX t : Modules.tid, [|V293_highest_ready tasks t|] **
        (V293_sched_internal_post unmap group rows high bt bg br bh lo hi li tid aop None **
          (V293_prefix_frame table high target tp bp bo entries tasks
            (V293_guard_cell current bcur nc ** (V293_counter_cell counter bcounter c ** frame)) **
            V293_prefix_output tp bo (Vptr t)))).
    + unfold V293_prefix_frame. intros s Hs. sep auto.
    + unfold V293_OSSched_tail_state, V293_prefix_frame. intros s [t Hs]. exists t. sep auto.
    + apply V293_OSSched_unlocked_prefix_hoare with (Hli := Hli); try assumption.
      repeat split; try apply V293_guard_cell_good; try apply V293_counter_cell_good; exact Hframe.
  - apply V293_OSSched_change_continuation; assumption.
Qed.
End Tail.

Theorem V293_OSSched_guarded_changed_prefix : forall Spec sd li I r ri tid aop frame
    sched_id unmap group rows high bt bg br bh lo hi table target tp bp bo entries tasks old
    interrupt lock bi bl ni nl current counter bcur bcounter nc c suffix q (Hli : GoodLInvAsrt li),
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks -> GoodFrm frame ->
  ni < 256 -> nl < 256 -> nc < 256 ->
  Spec sched_id = Some
    (V293_sched_fpre unmap group rows high bt bg br bh li Hli,
     V293_sched_fpost unmap group rows high bt bg br bh li Hli, (Tvoid, nil)) ->
  let guardframe := V293_guard_cell interrupt bi ni ** (V293_guard_cell lock bl nl ** frame) in
  let pre := V293_sched_internal_pre unmap group rows high bt bg br bh lo hi li tid aop **
    (V293_prefix_frame table high target tp bp bo entries tasks
      (V293_guard_cell current bcur nc ** guardframe) **
      (V293_prefix_output tp bo old ** V293_counter_cell counter bcounter c)) in
  let mid := V293_OSSched_tail_state unmap group rows high bt bg br bh lo hi li tid aop
    table target tp bp bo entries tasks current counter bcur bcounter nc guardframe in
  (ni = 0 -> nl = 0 -> V293_ready_select lo hi (V293_ready_group lo hi) <> nc ->
    InfRules Spec sd li I r ri (mid (Int.add c Int.one)) suffix q tid) ->
  InfRules Spec sd li I r ri pre
    (V293_OSSched_guards interrupt lock
      (sseq (V293_OSSched_unlocked_prefix sched_id table high target)
        (V293_OSSched_change high current counter suffix)))
    (if Nat.eqb ni 0 && Nat.eqb nl 0 then
      (if Nat.eqb (V293_ready_select lo hi (V293_ready_group lo hi)) nc then mid c else q) else pre) tid.
Proof.
  intros Spec sd li I r ri tid aop frame sched_id unmap group rows high bt bg br bh lo hi
    table target tp bp bo entries tasks old interrupt lock bi bl ni nl current counter bcur bcounter nc c suffix q
    Hli Hlo Hhi Hr Hb Htable Hframe Hni Hnl Hnc Hspec guardframe pre mid Hsuffix.
  eapply V293_OSSched_guards_rule with (ri_mem := Atrue) (rl_mem := Atrue); try assumption.
  - unfold pre, guardframe, V293_prefix_frame. intros s Hs. sep auto.
  - unfold pre, guardframe, V293_prefix_frame. intros s Hs. sep auto.
  - intros Ei El. apply V293_OSSched_changed_prefix_continuation with (Hli := Hli); try assumption.
    + unfold guardframe. repeat split; try apply V293_guard_cell_good; exact Hframe.
    + apply Hsuffix; assumption.
Qed.
