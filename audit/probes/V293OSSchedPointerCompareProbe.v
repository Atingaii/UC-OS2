(* Independently written literal interfaces and a real-memory single-byte
   ablation. None of these fixtures asserts full TCB layout or reachability. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPointerCompare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrent.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrentWitness.
Require Import CertiOS.certiucos.v293.proofs.V293SharedStateWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Local Open Scope nat_scope.

Definition checked_pointer_eval : forall ge le M target current bt bc tp tq next tid,
  get le target = None -> get le current = None ->
  get ge target = Some (bt, Tptr tp) -> get ge current = Some (bc, Tptr tq) ->
  load (Tptr tp) M (bt, 0%Z) = Some (Vptr next) ->
  load (Tptr tq) M (bc, 0%Z) = Some (Vptr tid) ->
  evalval (eunop oppsite (ebinop oeq (evar target) (evar current))) (ge, le, M) =
    Some (Vint32 (if tid_eq_dec next tid then Int.zero else Int.one)) /\
  evaltype (eunop oppsite (ebinop oeq (evar target) (evar current))) (ge, le, M) = Some Tint32 :=
  V293_OSSched_pointer_comparison_eval.

Definition checked_decision : forall lo hi entries tasks tid nc next,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks ->
  V293_current_task tasks tid nc -> V293_highest_ready tasks next ->
  (if Nat.eqb (V293_ready_select lo hi (V293_ready_group lo hi)) nc then Int.zero else Int.one) =
  (if tid_eq_dec next tid then Int.zero else Int.one) :=
  V293_OSSched_comparison_decision.

Definition checked_refinement : forall ge le M
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
  evalval (eunop oppsite (ebinop oeq (ecast (evar high) Tint32) (ecast (evar cached) Tint32))) (ge, le, M) =
    evalval (eunop oppsite (ebinop oeq (evar target) (evar current))) (ge, le, M) /\
  evaltype (eunop oppsite (ebinop oeq (ecast (evar high) Tint32) (ecast (evar cached) Tint32))) (ge, le, M) = Some Tint32 /\
  evaltype (eunop oppsite (ebinop oeq (evar target) (evar current))) (ge, le, M) = Some Tint32 :=
  V293_OSSched_comparison_refinement.

Definition compare_ge : env :=
  set (set (set (sig 200%Z (1%positive, Tint8)) 201%Z (2%positive, Tint8))
    202%Z (3%positive, Tptr Tvoid)) 203%Z (4%positive, Tptr Tvoid).
Definition compare_memory (bad_cache : bool) : mem :=
  merge (V293_encoded_memory 1%positive 0 true (encode_val Tint8 (V293_byteval 12)))
    (merge (V293_encoded_memory 2%positive 0 true
        (encode_val Tint8 (V293_byteval (if bad_cache then 12 else 4))))
      (merge (V293_encoded_memory 3%positive 0 true
          (encode_val (Tptr Tvoid) (Vptr (15%positive, Int.zero))))
        (V293_encoded_memory 4%positive 0 true
          (encode_val (Tptr Tvoid) (Vptr (7%positive, Int.zero)))))).
Local Ltac compare_compute :=
  lazymatch goal with |- load _ _ (?b, _) = _ =>
  cbv beta iota zeta delta [load loadm typelen loadbytes compare_memory];
  repeat rewrite map_merge_semp by reflexivity;
  repeat first [
    rewrite (V293_encoded_memory_outside _ 1%positive _ _ b _) by (left; congruence) |
    rewrite (V293_encoded_memory_outside _ 2%positive _ _ b _) by (left; congruence) |
    rewrite (V293_encoded_memory_outside _ 3%positive _ _ b _) by (left; congruence) |
    rewrite (V293_encoded_memory_outside _ 4%positive _ _ b _) by (left; congruence)];
  cbv beta iota zeta delta
    [V293_encoded_memory encode_val inj_pointer inj_bytes List.map encode_int V293_byteval];
  repeat first [rewrite map_merge_semp by reflexivity | rewrite map_get_sig |
    rewrite map_get_sig' by (intro E; inversion E; lia) | rewrite map_emp_get];
  reflexivity end.

(* Vary precisely one physical cache byte, keeping both pointers and the
   selected priority byte fixed. A wrong cache makes the decisions disagree. *)
Theorem checked_single_byte_ablation : forall bad_cache,
  evalval (V293_OSSched_different 200%Z 201%Z) (compare_ge, emp, compare_memory bad_cache) =
    Some (Vint32 (if bad_cache then Int.zero else Int.one)) /\
  evalval (V293_OSSched_pointer_different 202%Z 203%Z) (compare_ge, emp, compare_memory bad_cache) =
    Some (Vint32 Int.one).
Proof.
  intro bad_cache.
  destruct (V293_OSSched_byte_comparison_eval compare_ge emp (compare_memory bad_cache)
    200%Z 201%Z 1%positive 2%positive 12 (if bad_cache then 12 else 4)
    ltac:(lia) ltac:(destruct bad_cache; lia)
    ltac:(apply map_emp_get) ltac:(apply map_emp_get)
    ltac:(reflexivity) ltac:(reflexivity) ltac:(destruct bad_cache; compare_compute)
    ltac:(destruct bad_cache; compare_compute)) as [Es _].
  destruct (V293_OSSched_pointer_comparison_eval compare_ge emp (compare_memory bad_cache)
    202%Z 203%Z 3%positive 4%positive Tvoid Tvoid
    (15%positive, Int.zero) (7%positive, Int.zero)
    ltac:(apply map_emp_get) ltac:(apply map_emp_get)
    ltac:(unfold compare_ge; rewrite map_get_set' by discriminate; apply map_get_set)
    ltac:(unfold compare_ge; apply map_get_set)
    ltac:(destruct bad_cache; compare_compute)
    ltac:(destruct bad_cache; compare_compute)) as [Et _].
  split; [destruct bad_cache; exact Es | ].
  destruct (tid_eq_dec (15%positive, Int.zero) (7%positive, Int.zero)) as [E | E];
    [discriminate E | exact Et].
Qed.

(* The task assumptions used for the different-target decision are inhabited;
   they use the existing SAME table with waiting priority4 and ready priority12. *)
Theorem checked_instance_relations :
  V293_bitmap_tasks 0 16 V293_current_tasks /\
  V293_priority_table V293_current_entries V293_current_tasks /\
  V293_current_task V293_current_tasks (7%positive, Int.zero) 4 /\
  V293_highest_ready V293_current_tasks (15%positive, Int.zero).
Proof.
  destruct V293_current_relations as [Hb [Ht Hc]].
  split; [exact Hb | ]. split; [exact Ht | ]. split; [exact Hc | ].
  exact (V293_shared_case_highest true).
Qed.

Print Assumptions checked_pointer_eval.
Print Assumptions checked_decision.
Print Assumptions checked_refinement.
Print Assumptions checked_single_byte_ablation.
Print Assumptions checked_instance_relations.
