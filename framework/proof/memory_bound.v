(* A fresh block requires a bound on occupied block identifiers, not an axiom
   about every arbitrary partial function. This invariant is NOT yet threaded
   through the existing operational semantics and soundness proofs. *)
Require Import memory.
Local Open Scope Z_scope.

Definition blocks_below (m : mem) (upper : positive) : Prop :=
  forall b i v, get m (b, i) = Some v -> (b < upper)%positive.

Lemma blocks_below_monotone : forall m upper upper',
  blocks_below m upper -> (upper <= upper')%positive -> blocks_below m upper'.
Proof.
  intros m upper upper' Hbound Hle b i v Hget.
  eapply Pos.lt_le_trans; [eapply Hbound; exact Hget | exact Hle].
Qed.

Lemma blocks_below_empty : forall upper, blocks_below (emp : mem) upper.
Proof.
  intros upper b i v Hget.
  change (None = Some v) in Hget; discriminate.
Qed.

(* Stable allocation interface: the bound itself is an unused block. *)
Theorem blocks_below_fresh : forall m upper,
  blocks_below m upper -> fresh m upper.
Proof.
  intros m upper Hbound l i Heq [v Hget]; subst l.
  apply (Pos.lt_irrefl upper).
  eapply Hbound; exact Hget.
Qed.

Corollary bounded_memory_has_fresh_block : forall m,
  (exists upper, blocks_below m upper) -> exists b, fresh m b.
Proof.
  intros m [upper Hbound]; exists upper; apply blocks_below_fresh; exact Hbound.
Qed.

Lemma blocks_below_set : forall m upper b i v,
  blocks_below m upper -> (b < upper)%positive ->
  blocks_below (set m (b, i) v) upper.
Proof.
  intros m upper b i v Hbound Hlt b' i' v' Hget.
  destruct (addr_eq_dec (b, i) (b', i')) as [Heq | Hneq].
  - inversion Heq; subst; exact Hlt.
  - rewrite Maps.map_get_set' in Hget by exact Hneq.
    eapply Hbound; exact Hget.
Qed.

Lemma blocks_below_set_grow : forall m upper b i v,
  blocks_below m upper ->
  blocks_below (set m (b, i) v) (Pos.max upper (Pos.succ b)).
Proof.
  intros m upper b i v Hbound; apply blocks_below_set.
  - eapply blocks_below_monotone; [exact Hbound | apply Pos.le_max_l].
  - eapply Pos.lt_le_trans; [apply Pos.lt_succ_diag_r | apply Pos.le_max_r].
Qed.

Lemma blocks_below_del : forall m upper a,
  blocks_below m upper -> blocks_below (del m a) upper.
Proof.
  intros m upper a Hbound b i v Hget.
  rewrite Maps.map_del_sem in Hget.
  change ((if addr_eq_dec a (b, i) then None else get m (b, i)) = Some v) in Hget.
  destruct (addr_eq_dec a (b, i)); [discriminate | eapply Hbound; exact Hget].
Qed.

Lemma blocks_below_allocb : forall n m upper b i,
  blocks_below m upper -> (b < upper)%positive ->
  blocks_below (allocb m b i n) upper.
Proof.
  induction n as [|n IH]; intros m upper b i Hbound Hlt; simpl.
  - exact Hbound.
  - apply blocks_below_set; [apply IH; assumption | exact Hlt].
Qed.

Lemma blocks_below_allocb_grow : forall n m upper b i,
  blocks_below m upper ->
  blocks_below (allocb m b i n) (Pos.max upper (Pos.succ b)).
Proof.
  intros n m upper b i Hbound; apply blocks_below_allocb.
  - eapply blocks_below_monotone; [exact Hbound | apply Pos.le_max_l].
  - eapply Pos.lt_le_trans; [apply Pos.lt_succ_diag_r | apply Pos.le_max_r].
Qed.

Lemma blocks_below_storebytes : forall bytes m m' upper a,
  blocks_below m upper -> storebytes m a bytes = Some m' -> blocks_below m' upper.
Proof.
  induction bytes as [|v bytes IH]; intros m m' upper [b i] Hbound Hstore; simpl in Hstore.
  - inversion Hstore; subst; exact Hbound.
  - cbv beta iota zeta delta [Maps.get memMap HalfPermMap.get] in Hstore.
    destruct (m (b, i)) as [[permission old]|] eqn:Hget; try discriminate.
    destruct permission; try discriminate.
    destruct (storebytes m (b, i + 1) bytes) as [next|] eqn:Hnext; try discriminate.
    inversion Hstore; subst; apply blocks_below_set.
    + eapply IH; eauto.
    + eapply Hbound; exact Hget.
Qed.

Lemma blocks_below_freeb : forall n m m' upper b i,
  blocks_below m upper -> freeb m b i n = Some m' -> blocks_below m' upper.
Proof.
  induction n as [|n IH]; intros m m' upper b i Hbound Hfree; simpl in Hfree.
  - inversion Hfree; subst; exact Hbound.
  - cbv beta iota zeta delta [Maps.get memMap HalfPermMap.get] in Hfree.
    destruct (m (b, i)) as [[permission old]|] eqn:Hget; try discriminate.
    destruct permission; try discriminate.
    destruct (freeb m b (i + 1) n) as [next|] eqn:Hnext; try discriminate.
    inversion Hfree; subst; apply blocks_below_del; eapply IH; eauto.
Qed.
