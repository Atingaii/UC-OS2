(* Independent literal interfaces for local two-memory source observations.
   Not a port implementation, complete C simulation, or GOOD_OS root. *)
Require Import CertiOS.certiucos.v293.proofs.V293SwitchPriorityBoundary.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPointerCompare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrent.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrentWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.framework.include_frm.
Local Open Scope nat_scope.

Definition checked_noncache_load : forall cache source normalized tp b i,
  (forall a, a <> (cache, 0%Z) -> get source a = get normalized a) -> b <> cache ->
  load tp source (b, i) = load tp normalized (b, i) := V293_cache_related_load.

Definition checked_boundary_store :
  forall cache source normalized normalized' pointer tp next nc old,
  (forall a, a <> (cache, 0%Z) -> get source a = get normalized a) ->
  pointer <> cache -> nc < 256 ->
  get source (cache, 0%Z) = Some (true, old) ->
  store (Tptr tp) normalized (pointer, 0%Z) (Vptr next) = Some normalized' ->
  exists source_pointer source',
    store (Tptr tp) source (pointer, 0%Z) (Vptr next) = Some source_pointer /\
    store Tint8 source_pointer (cache, 0%Z) (V293_byteval nc) = Some source' /\
    (load Tint8 source' (cache, 0%Z) = Some (V293_byteval nc) /\
      forall a, a <> (cache, 0%Z) -> get source' a = get normalized' a) :=
  V293_cache_synchronized_store_refinement.

Definition checked_cross_memory : forall ge le source normalized
    high cached target current bh bcache bt bc tp tq lo hi entries tasks tid nc next,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks ->
  V293_current_task tasks tid nc -> V293_highest_ready tasks next ->
  (load Tint8 source (bcache, 0%Z) = Some (V293_byteval nc) /\
    forall a, a <> (bcache, 0%Z) -> get source a = get normalized a) -> bh <> bcache ->
  get le high = None -> get le cached = None -> get le target = None -> get le current = None ->
  get ge high = Some (bh, Tint8) -> get ge cached = Some (bcache, Tint8) ->
  get ge target = Some (bt, Tptr tp) -> get ge current = Some (bc, Tptr tq) ->
  load Tint8 normalized (bh, 0%Z) = Some (V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi))) ->
  load (Tptr tp) normalized (bt, 0%Z) = Some (Vptr next) ->
  load (Tptr tq) normalized (bc, 0%Z) = Some (Vptr tid) ->
  evalval (eunop oppsite (ebinop oeq (ecast (evar high) Tint32) (ecast (evar cached) Tint32)))
    (ge, le, source) =
    evalval (eunop oppsite (ebinop oeq (evar target) (evar current))) (ge, le, normalized) /\
  evalval (evar cached) (ge, le, source) = Some (V293_byteval nc) /\
  evaltype (V293_OSSched_different high cached) (ge, le, source) = Some Tint32 /\
  evaltype (V293_OSSched_pointer_different target current) (ge, le, normalized) = Some Tint32 :=
  V293_OSSched_cross_memory_comparison.

Definition checked_fixture_stores :
  store (Tptr Tvoid) V293_cache_observation_before (1%positive, 0%Z) (Vptr V293_current_next) =
    Some V293_cache_observation_normalized /\
  store Tint8 V293_cache_observation_normalized (2%positive, 0%Z) (V293_byteval 12) =
    Some V293_cache_observation_source /\
  (load Tint8 V293_cache_observation_source (2%positive, 0%Z) = Some (V293_byteval 12) /\
    forall a, a <> (2%positive, 0%Z) ->
      get V293_cache_observation_source a = get V293_cache_observation_normalized a) /\
  load Tint8 V293_cache_observation_normalized (2%positive, 0%Z) = Some (V293_byteval 4) :=
  V293_cache_observation_stores.

Definition checked_fixture_decisions :
  evalval (V293_OSSched_different 109%Z 108%Z)
    (V293_cache_observation_ge, emp, V293_cache_observation_source) = Some (Vint32 Int.zero) /\
  evalval (V293_OSSched_pointer_different 110%Z OSTCBCur)
    (V293_cache_observation_ge, emp, V293_cache_observation_normalized) = Some (Vint32 Int.zero) /\
  evalval (V293_OSSched_different 109%Z 108%Z)
    (V293_cache_observation_ge, emp, V293_cache_observation_normalized) = Some (Vint32 Int.one) /\
  evalval (evar 108%Z) (V293_cache_observation_ge, emp, V293_cache_observation_source) =
    Some (V293_byteval 12) /\
  evalval (evar 108%Z) (V293_cache_observation_ge, emp, V293_cache_observation_normalized) =
    Some (V293_byteval 4) := V293_cache_observation_decisions.

Definition checked_fixture_refinement :
  evalval (V293_OSSched_different 109%Z 108%Z)
    (V293_cache_observation_ge, emp, V293_cache_observation_source) =
  evalval (V293_OSSched_pointer_different 110%Z OSTCBCur)
    (V293_cache_observation_ge, emp, V293_cache_observation_normalized) /\
  evalval (evar 108%Z) (V293_cache_observation_ge, emp, V293_cache_observation_source) =
    Some (V293_byteval 12) /\
  evaltype (V293_OSSched_different 109%Z 108%Z)
    (V293_cache_observation_ge, emp, V293_cache_observation_source) = Some Tint32 /\
  evaltype (V293_OSSched_pointer_different 110%Z OSTCBCur)
    (V293_cache_observation_ge, emp, V293_cache_observation_normalized) = Some Tint32 :=
  V293_cache_observation_refinement.

Print Assumptions checked_noncache_load.
Print Assumptions checked_boundary_store.
Print Assumptions checked_cross_memory.
Print Assumptions checked_fixture_stores.
Print Assumptions checked_fixture_decisions.
Print Assumptions checked_fixture_refinement.
