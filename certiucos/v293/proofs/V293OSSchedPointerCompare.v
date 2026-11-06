(* A checked LOCAL normalization of OS_Sched's comparison, not a whole-C
   simulation. Source cache coherence is explicit. No byte write is inserted,
   and no cache-coherence preservation is inferred from the bare switch. *)
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrent.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.auxdef.
Require Import Coq.Lists.List Lia.
Local Open Scope nat_scope.

Definition V293_OSSched_pointer_different (target current : var) : expr :=
  eunop oppsite (ebinop oeq (evar target) (evar current)).

Lemma V293_pointer_value_eq : forall t u : Modules.tid,
  val_eq (Vptr t) (Vptr u) =
    Some (Vint32 (if tid_eq_dec t u then Int.one else Int.zero)).
Proof.
  intros [b i] [c j]. unfold val_eq.
  destruct (peq b c) as [Eb | Eb].
  - subst c. pose proof (Int.eq_spec i j) as E.
    destruct (Int.eq i j); destruct (tid_eq_dec (b, i) (b, j));
      try reflexivity; congruence.
  - destruct (tid_eq_dec (b, i) (c, j)); [congruence | reflexivity].
Qed.

(* Raw environment and loads, not an oracle for the composite comparison. *)
Theorem V293_OSSched_pointer_comparison_eval : forall ge le M target current bt bc tp tq next tid,
  get le target = None -> get le current = None ->
  get ge target = Some (bt, Tptr tp) -> get ge current = Some (bc, Tptr tq) ->
  load (Tptr tp) M (bt, 0%Z) = Some (Vptr next) ->
  load (Tptr tq) M (bc, 0%Z) = Some (Vptr tid) ->
  evalval (V293_OSSched_pointer_different target current) (ge, le, M) =
    Some (Vint32 (if tid_eq_dec next tid then Int.zero else Int.one)) /\
  evaltype (V293_OSSched_pointer_different target current) (ge, le, M) = Some Tint32.
Proof.
  intros ge le M target current bt bc tp tq next tid Nt Nc Gt Gc Lt Lc.
  unfold V293_OSSched_pointer_different.
  cbn [evalval evaltype get_lenv get_genv get_mem]. rewrite Nt, Nc, Gt, Gc.
  cbn [bop_type uop_type]. rewrite Lt, Lc.
  cbn [bop_eval]. rewrite V293_pointer_value_eq.
  destruct (tid_eq_dec next tid); split; reflexivity.
Qed.

Lemma V293_OSSched_byte_comparison_eval : forall ge le M high current bh bc nh nc,
  nh < 256 -> nc < 256 ->
  get le high = None -> get le current = None ->
  get ge high = Some (bh, Tint8) -> get ge current = Some (bc, Tint8) ->
  load Tint8 M (bh, 0%Z) = Some (V293_byteval nh) ->
  load Tint8 M (bc, 0%Z) = Some (V293_byteval nc) ->
  evalval (V293_OSSched_different high current) (ge, le, M) =
    Some (Vint32 (if Nat.eqb nh nc then Int.zero else Int.one)) /\
  evaltype (V293_OSSched_different high current) (ge, le, M) = Some Tint32.
Proof.
  intros ge le M high current bh bc nh nc Hh Hc Nh Nc Gh Gc Lh Lc.
  unfold V293_OSSched_different.
  cbn [evalval evaltype get_lenv get_genv get_mem]. rewrite Nh, Nc, Gh, Gc.
  cbn -[load]. rewrite Lh, Lc.
  unfold V293_byteval. cbn [cast_eval is_int_type bop_type uop_type bop_eval val_eq].
  rewrite V293_byte_eq by assumption.
  destruct (Nat.eqb nh nc); split; reflexivity.
Qed.

(* The two decisions agree because priority->task is unique in this SAME
   table. Current may be waiting; only next is required to be highest ready. *)
Theorem V293_OSSched_comparison_decision : forall lo hi entries tasks tid nc next,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks ->
  V293_current_task tasks tid nc -> V293_highest_ready tasks next ->
  (if Nat.eqb (V293_ready_select lo hi (V293_ready_group lo hi)) nc then Int.zero else Int.one) =
  (if tid_eq_dec next tid then Int.zero else Int.one).
Proof.
  intros lo hi entries tasks tid nc next Hl Hh Hr Hb Ht Hc Hn.
  pose proof (V293_OSSched_current_target lo hi entries tasks tid nc next
    Hl Hh Hr Hb Ht Hc Hn) as E.
  destruct (Nat.eqb (V293_ready_select lo hi (V293_ready_group lo hi)) nc) eqn:En;
    destruct (tid_eq_dec next tid); try reflexivity.
  - apply Nat.eqb_eq in En. exfalso. apply n. apply (proj2 E); exact En.
  - apply Nat.eqb_neq in En. exfalso. apply En. apply (proj1 E); exact e.
Qed.

(* Explicit local source/cache premise plus real source AND target reads.
   This does not establish the premise at all source-program entry points. *)
Theorem V293_OSSched_comparison_refinement : forall ge le M
    high cached target current bh bcache bt bc tp tq lo hi entries tasks tid nc next,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks ->
  V293_current_task tasks tid nc -> V293_highest_ready tasks next ->
  get le high = None -> get le cached = None -> get le target = None -> get le current = None ->
  get ge high = Some (bh, Tint8) -> get ge cached = Some (bcache, Tint8) ->
  get ge target = Some (bt, Tptr tp) -> get ge current = Some (bc, Tptr tq) ->
  load Tint8 M (bh, 0%Z) = Some (V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi))) ->
  load Tint8 M (bcache, 0%Z) = Some (V293_byteval nc) ->
  load (Tptr tp) M (bt, 0%Z) = Some (Vptr next) ->
  load (Tptr tq) M (bc, 0%Z) = Some (Vptr tid) ->
  evalval (V293_OSSched_different high cached) (ge, le, M) =
    evalval (V293_OSSched_pointer_different target current) (ge, le, M) /\
  evaltype (V293_OSSched_different high cached) (ge, le, M) = Some Tint32 /\
  evaltype (V293_OSSched_pointer_different target current) (ge, le, M) = Some Tint32.
Proof.
  intros ge le M high cached target current bh bcache bt bc tp tq lo hi entries tasks tid nc next
    Hl Hh Hr Hb Ht Hc Hn Nh Ncache Nt Nc Gh Gcache Gt Gc Lh Lcache Lt Lc.
  pose proof (V293_ready_selection_range lo hi (V293_ready_group lo hi) Hl Hh eq_refl Hr) as Hrange.
  assert (Hnc : nc < 256) by (destruct Hc; lia).
  destruct (V293_OSSched_byte_comparison_eval ge le M high cached bh bcache
    (V293_ready_select lo hi (V293_ready_group lo hi)) nc
    ltac:(lia) Hnc Nh Ncache Gh Gcache Lh Lcache) as [Es Ts].
  destruct (V293_OSSched_pointer_comparison_eval ge le M target current bt bc tp tq next tid
    Nt Nc Gt Gc Lt Lc) as [Et Tt].
  rewrite Es, Et, (V293_OSSched_comparison_decision lo hi entries tasks tid nc next Hl Hh Hr Hb Ht Hc Hn).
  auto.
Qed.

(* A two-memory source/normalized-state relation. Only ONE cache byte may
   differ; no other address or permission is erased. This does not define
   the missing OSCtxSw implementation or change the framework switch. *)
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Local Open Scope nat_scope.

Definition V293_same_except_cache (cache : block) (source normalized : mem) : Prop :=
  forall a, a <> (cache, 0%Z) -> get source a = get normalized a.

Definition V293_cache_correspondence (cache : block) (priority : nat)
    (source normalized : mem) : Prop :=
  load Tint8 source (cache, 0%Z) = Some (V293_byteval priority) /\
  V293_same_except_cache cache source normalized.

Lemma V293_cache_related_loadbytes : forall cache source normalized b i n,
  V293_same_except_cache cache source normalized -> b <> cache ->
  loadbytes source (b, i) n = loadbytes normalized (b, i) n.
Proof.
  intros cache source normalized b i n Hsame Hblock. revert i.
  induction n as [ | n IH]; intro i; [reflexivity | ].
  cbn [loadbytes]. rewrite Hsame by congruence. rewrite IH. reflexivity.
Qed.

Theorem V293_cache_related_load : forall cache source normalized tp b i,
  V293_same_except_cache cache source normalized -> b <> cache ->
  load tp source (b, i) = load tp normalized (b, i).
Proof.
  intros cache source normalized tp b i Hsame Hblock.
  unfold load, loadm. rewrite (V293_cache_related_loadbytes cache source normalized b i
    (typelen tp) Hsame Hblock). reflexivity.
Qed.

(* Identical writes away from the cache simulate in both memories. The
   existence of the source write is proved, not required as an oracle. *)
Lemma V293_cache_related_storebytes : forall bytes cache source normalized normalized' b i,
  V293_same_except_cache cache source normalized -> b <> cache ->
  storebytes normalized (b, i) bytes = Some normalized' ->
  exists source', storebytes source (b, i) bytes = Some source' /\
    V293_same_except_cache cache source' normalized'.
Proof.
  induction bytes as [ | v bytes IH]; intros cache source normalized normalized' b i Hsame Hb Hstore.
  - cbn [storebytes] in Hstore. inversion Hstore; subst normalized'.
    exists source. split; [reflexivity | exact Hsame].
  - cbn [storebytes] in Hstore. unfold addr, offset in *.
    destruct (get normalized (b, i)) as [[permission old] | ] eqn:Hget; try discriminate.
    destruct permission; try discriminate.
    destruct (storebytes normalized (b, (i + 1)%Z) bytes) as [tail | ] eqn:Htail; try discriminate.
    inversion Hstore; subst normalized'.
    destruct (IH cache source normalized tail b (i + 1)%Z Hsame Hb Htail)
      as (source_tail & Hsource_tail & Hrelated).
    exists (set source_tail (b, i) (true, v)). split.
    + cbn [storebytes]. rewrite Hsame by congruence. rewrite Hget, Hsource_tail. reflexivity.
    + intros a Ha. destruct (addr_eq_dec (b, i) a) as [E|E].
      * subst a. rewrite !map_get_set. reflexivity.
      * rewrite !map_get_set' by exact E. apply Hrelated; exact Ha.
Qed.

Lemma V293_storebytes_other_block : forall bytes M M' b i other off,
  b <> other -> storebytes M (b, i) bytes = Some M' ->
  get M' (other, off) = get M (other, off).
Proof.
  induction bytes as [ | v bytes IH]; intros M M' b i other off Hb HS.
  - cbn [storebytes] in HS. inversion HS; reflexivity.
  - cbn [storebytes] in HS. unfold addr, offset in *.
    destruct (get M (b, i)) as [[permission old] | ]; try discriminate.
    destruct permission; try discriminate.
    destruct (storebytes M (b, (i + 1)%Z) bytes) as [tail | ] eqn:HT; try discriminate.
    inversion HS; subst M'. rewrite map_get_set' by congruence.
    eapply IH; eauto.
Qed.

(* Required effect of a synchronized source boundary, not a claimed effect
   of bare switch: same pointer store, then an explicit source cache store.
   The normalized memory does ONLY the original pointer store. *)
Theorem V293_cache_synchronized_store_refinement :
  forall cache source normalized normalized' pointer tp next nc old,
  V293_same_except_cache cache source normalized -> pointer <> cache -> nc < 256 ->
  get source (cache, 0%Z) = Some (true, old) ->
  store (Tptr tp) normalized (pointer, 0%Z) (Vptr next) = Some normalized' ->
  exists source_pointer source',
    store (Tptr tp) source (pointer, 0%Z) (Vptr next) = Some source_pointer /\
    store Tint8 source_pointer (cache, 0%Z) (V293_byteval nc) = Some source' /\
    V293_cache_correspondence cache nc source' normalized'.
Proof.
  intros cache source normalized normalized' pointer tp next nc old Hsame Hb Hnc Hcache Hstore.
  destruct (V293_cache_related_storebytes (encode_val (Tptr tp) (Vptr next))
    cache source normalized normalized' pointer 0%Z Hsame Hb Hstore)
    as (source_pointer & Hpointer & Hrelated).
  exists source_pointer. exists (V293_write_byte source_pointer cache nc).
  split; [exact Hpointer | ]. split.
  - apply V293_write_byte_store with (old := old).
    exact (eq_trans (V293_storebytes_other_block
      (encode_val (Tptr tp) (Vptr next)) source source_pointer pointer 0%Z cache 0%Z Hb Hpointer) Hcache).
  - split; [apply V293_write_byte_load; exact Hnc | ].
    intros a Ha. unfold V293_write_byte. rewrite map_get_set' by congruence.
    apply Hrelated; exact Ha.
Qed.

(* The subsequent real source cache read is accounted for. Other inputs
   are read from the normalized memory and transported, not guessed.
   Current-task coherence remains an explicit source-side obligation. *)
Theorem V293_OSSched_cross_memory_comparison : forall ge le source normalized
    high cached target current bh bcache bt bc tp tq lo hi entries tasks tid nc next,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks ->
  V293_current_task tasks tid nc -> V293_highest_ready tasks next ->
  V293_cache_correspondence bcache nc source normalized -> bh <> bcache ->
  get le high = None -> get le cached = None -> get le target = None -> get le current = None ->
  get ge high = Some (bh, Tint8) -> get ge cached = Some (bcache, Tint8) ->
  get ge target = Some (bt, Tptr tp) -> get ge current = Some (bc, Tptr tq) ->
  load Tint8 normalized (bh, 0%Z) = Some (V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi))) ->
  load (Tptr tp) normalized (bt, 0%Z) = Some (Vptr next) ->
  load (Tptr tq) normalized (bc, 0%Z) = Some (Vptr tid) ->
  evalval (V293_OSSched_different high cached) (ge, le, source) =
    evalval (V293_OSSched_pointer_different target current) (ge, le, normalized) /\
  evalval (evar cached) (ge, le, source) = Some (V293_byteval nc) /\
  evaltype (V293_OSSched_different high cached) (ge, le, source) = Some Tint32 /\
  evaltype (V293_OSSched_pointer_different target current) (ge, le, normalized) = Some Tint32.
Proof.
  intros ge le source normalized high cached target current bh bcache bt bc tp tq lo hi entries tasks tid nc next
    Hl Hh Hr Hb Ht Hcurrent Hnext [Hcache Hsame] Hblock Nh Nc Nt Ncur Gh Gc Gt Gcur Lh Lt Lcur.
  assert (Lsource : load Tint8 source (bh, 0%Z) =
    Some (V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi)))).
  { exact (eq_trans (V293_cache_related_load bcache source normalized Tint8 bh 0%Z Hsame Hblock) Lh). }
  pose proof (V293_ready_selection_range lo hi (V293_ready_group lo hi) Hl Hh eq_refl Hr) as Hrange.
  assert (Hnc : nc < 256) by (destruct Hcurrent; lia).
  destruct (V293_OSSched_byte_comparison_eval ge le source high cached bh bcache
    (V293_ready_select lo hi (V293_ready_group lo hi)) nc ltac:(lia) Hnc
    Nh Nc Gh Gc Lsource Hcache) as [ES TS].
  destruct (V293_OSSched_pointer_comparison_eval ge le normalized target current bt bc tp tq next tid
    Nt Ncur Gt Gcur Lt Lcur) as [ET TT].
  split.
  - rewrite ES, ET, (V293_OSSched_comparison_decision lo hi entries tasks tid nc next
      Hl Hh Hr Hb Ht Hcurrent Hnext). reflexivity.
  - split.
    + cbn [evalval evaltype get_lenv get_genv get_mem]. rewrite Nc, Gc. exact Hcache.
    + split; assumption.
Qed.
