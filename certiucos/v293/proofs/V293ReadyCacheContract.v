(* Diagnostic source-boundary contract. No new transition, port body or C edit.
   The cache write below is a memory obligation, not code installed in OS_Sched. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.memory_prop.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.certiucos.v293.proofs.V293ReadySwitchStep.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrent.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import Lia.
Local Open Scope nat_scope.

Definition V293_cache_current tasks current M cache :=
  exists n, V293_current_task tasks current n /\
    load Tint8 M (cache,0%Z)=Some (V293_byteval n).

Lemma V293_cache_current_iff : forall tasks current M cache cached selected,
  cached<13 -> V293_current_task tasks current selected ->
  load Tint8 M (cache,0%Z)=Some (V293_byteval cached) ->
  (V293_cache_current tasks current M cache <-> cached=selected).
Proof.
  intros tasks current M cache cached selected Range Task Read. split.
  - intros (n & [Rn [st [msg Lookup]]] & Cache).
    destruct Task as [Rs [st' [msg' Lookup']]].
    assert (Eq : Int.repr (Z.of_nat n)=Int.repr (Z.of_nat selected)) by congruence.
    assert (N : n=selected) by (apply V293_priority_repr_injective;assumption).
    subst n. assert (Eq' : Int.repr (Z.of_nat cached)=Int.repr (Z.of_nat selected)).
    { unfold V293_byteval in Read,Cache. congruence. }
    apply V293_priority_repr_injective;assumption.
  - intro E. subst cached. exists selected. split;assumption.
Qed.

Lemma V293_cache_current_mismatch : forall tasks current M cache cached selected,
  cached<13 -> V293_current_task tasks current selected ->
  load Tint8 M (cache,0%Z)=Some (V293_byteval cached) -> cached<>selected ->
  ~V293_cache_current tasks current M cache.
Proof.
  intros tasks current M cache cached selected Range Task Read Different H.
  apply Different. exact (proj1 (V293_cache_current_iff tasks current M cache cached selected Range Task Read) H).
Qed.

(* Whole-state ownership, arbitrary physical/abstract frame; no assumed store.
   This does NOT claim that the declared external OSCtxSw executes this write. *)
Theorem V293_ready_cache_write : forall br bg bp current R ge le M ir aux O op cache old n,
  n<256 ->
  (ge,le,M,ir,aux,O,op) |= SWINVt (V293_ready_inv br bg bp) current **
    (V293_owned_record_cell ((cache,0%Z),Tint8,old) ** R) ->
  exists Mw, store Tint8 M (cache,0%Z) (V293_byteval n)=Some Mw /\
    (ge,le,Mw,ir,aux,O,op) |= SWINVt (V293_ready_inv br bg bp) current **
      (V293_owned_record_cell ((cache,0%Z),Tint8,V293_byteval n) ** R) /\
    load Tint8 Mw (cache,0%Z)=Some (V293_byteval n) /\
    (forall c i, c<>cache \/ i<>0%Z -> get Mw (c,i)=get M (c,i)).
Proof.
  intros br bg bp current R ge le M ir aux O op cache old n Range Held.
  assert (Owned : (ge,le,M,ir,aux,O,op) |=
    V293_owned_record_cell ((cache,0%Z),Tint8,old) **
      (SWINVt (V293_ready_inv br bg bp) current ** R)) by (sep auto).
  destruct (V293_owned_record_cell_update _ _ _ (V293_byteval n) _ _ _ _ _ _ _ _
    (V293_byte_type n Range) Owned) as (Mw & Store & After).
  exists Mw. split;[exact Store| ]. split;[clear Held Owned;sep auto| ]. split.
  - change (load Tint8 (getmem (ge,le,Mw,ir,aux,O,op)) (cache,0%Z)=Some (V293_byteval n)).
    eapply V293_record_star_load_l;[apply V293_owned_record_cell_load|exact After].
  - intros c i Outside. eapply V293_storebytes_outside;[exact Store| ].
    change (c<>cache \/ (i<0)%Z \/ (1<=i)%Z). destruct Outside as [Apart|Apart];[left;exact Apart|right;lia].
Qed.

(* One actual original switch. Separation already enforces disjoint ownership.
   'tasks' is coupled explicitly through current_task, not a new oracle/Inv. *)
Theorem V293_ready_switch_cache :
  forall br bg bp pc po pi ip T cst ks (current next:tid) target bt bc cache
    ge le les M ir aux au O op R tp tasks cached selected,
  get les current=Some le -> get au current=Some aux ->
  get T current=Some (curs (sprim (switch target)),(kenil,ks)) ->
  get ge target=Some (bt,Tptr tp) ->
  load (Tptr tp) M (bt,0%Z)=Some (Vptr next) ->
  get ge OSTCBCur=Some (bc,Tptr tp) -> cached<13 ->
  get O abstcblsid=Some (abstcblist tasks) ->
  V293_current_task tasks next selected ->
  (ge,le,M,ir,aux,O,op) |= SWINVt (V293_ready_inv br bg bp) current **
    (V293_owned_record_cell ((cache,0%Z),Tint8,V293_byteval cached) ** R) ->
  exists Mf,
    lpstep (pc,(po,pi,ip)) T cst (ge,les,M,ir,au) current
      (set T current (SKIP,(kenil,ks))) cst (ge,les,Mf,ir,au) next /\
    store (Tptr tp) M (bc,0%Z) (Vptr next)=Some Mf /\
    (ge,le,Mf,ir,aux,set O curtid (oscurt next),op) |=
      SWINVt (V293_ready_inv br bg bp) next **
        (V293_owned_record_cell ((cache,0%Z),Tint8,V293_byteval cached) ** R) /\
    load (Tptr tp) Mf (bc,0%Z)=Some (Vptr next) /\
    load Tint8 Mf (cache,0%Z)=Some (V293_byteval cached) /\
    (V293_cache_current tasks next Mf cache <-> cached=selected) /\
    get (set O curtid (oscurt next)) abstcblsid=Some (abstcblist tasks) /\
    (forall c i, c<>bc \/ (i<0)%Z \/ (4<=i)%Z -> get Mf (c,i)=get M (c,i)).
Proof.
  intros br bg bp pc po pi ip T cst ks current next target bt bc cache
    ge le les M ir aux au O op R tp tasks cached selected Local Aux Code Target Read Cur Range Map Task Held.
  destruct (V293_ready_switch_step br bg bp pc po pi ip T cst ks current next target bt bc
    ge le les M ir aux au O op
    (V293_owned_record_cell ((cache,0%Z),Tint8,V293_byteval cached) ** R) tp
    Local Aux Code Target Read Cur Held)
    as (Mf & Step & Store & After & Current & Skipped & Other & Outside).
  assert (Cache : load Tint8 Mf (cache,0%Z)=Some (V293_byteval cached)).
  { assert (Cell : (ge,le,Mf,ir,aux,set O curtid (oscurt next),op) |=
      V293_owned_record_cell ((cache,0%Z),Tint8,V293_byteval cached) ** Atrue)
      by (clear Held;sep auto).
    change (load Tint8 (getmem (ge,le,Mf,ir,aux,set O curtid (oscurt next),op))
      (cache,0%Z)=Some (V293_byteval cached)).
    eapply V293_record_star_load_l;[apply V293_owned_record_cell_load|exact Cell]. }
  exists Mf. split;[exact Step| ]. split;[exact Store| ]. split;[exact After| ].
  split;[exact Current| ]. split;[exact Cache| ]. split.
  - apply V293_cache_current_iff;assumption.
  - split;[rewrite map_get_set' by discriminate;exact Map|exact Outside].
Qed.
