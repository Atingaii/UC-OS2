(* Selected TCB fields, with full byte permissions.  The task-map enumeration
   is canonical; this is neither a complete TCB layout nor a proved API/ISR
   preservation theorem.  In particular, raw loads never create ownership. *)
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition V293_record_cell := (addr * type * val)%type.
Definition V293_owned_record_cell (cell : V293_record_cell) : asrt :=
  let '(a,tp,v) := cell in
  [| rule_type_val_match tp v = true |] ** Amapsto a tp true v.

Fixpoint V293_owned_record_cells (cells : list V293_record_cell) : asrt :=
  match cells with
  | [] => Aemp
  | cell :: rest => V293_owned_record_cell cell ** V293_owned_record_cells rest
  end.

Definition V293_record_layout (t : tid) (p : nat) (status : taskstatus)
    (message : val) (pend : nat) : list V293_record_cell :=
  let a := fun delta => (fst t,(Int.unsigned (snd t)+delta)%Z) in
  [ (a 50%Z,Tint8,V293_byteval p);
    (a 52%Z,Tint8,V293_byteval (V293_prio_row p));
    (a 51%Z,Tint8,V293_byteval (V293_prio_bit p));
    (a 54%Z,Tint8,V293_byteval (2 ^ V293_prio_row p));
    (a 53%Z,Tint8,V293_byteval (2 ^ V293_prio_bit p));
    (a 32%Z,Tptr Tvoid,message) ] ++
  match status with
  | rdy => [(a 48%Z,Tint8,V293_byteval 0)]
  | wait os_stat_time delay =>
      [(a 48%Z,Tint8,V293_byteval 0); (a 44%Z,Tint32,Vint32 delay)]
  | wait reason delay =>
      let '(stat,eid) := match reason with
        | os_stat_sem eid => (1,eid) | os_stat_q eid => (4,eid)
        | os_stat_mbox eid => (2,eid) | os_stat_mutexsem eid => (16,eid)
        | os_stat_time => (0,t)
        end in
      [(a 48%Z,Tint8,V293_byteval stat); (a 44%Z,Tint32,Vint32 delay);
       (a 49%Z,Tint8,V293_byteval pend); (a 28%Z,Tcom_ptr 411%Z,Vptr eid)]
  end.

Definition V293_owned_task_record (t : tid) (priority : int32)
    (status : taskstatus) (message : val) : asrt :=
  EX p : nat, EX pend : nat,
    [| p < 13 /\ priority = Int.repr (Z.of_nat p) /\ pend < 256 |] **
    V293_owned_record_cells (V293_record_layout t p status message pend).

Fixpoint V293_owned_task_list (entries : list (tid * abstcb.B)) : asrt :=
  match entries with
  | [] => Aemp
  | (t,(priority,status,message)) :: rest =>
      V293_owned_task_record t priority status message ** V293_owned_task_list rest
  end.

Definition V293_owned_task_records (tasks : TcbMod.map) : asrt :=
  V293_owned_task_list (TcbMod.lst tasks).

(* These lifting lemmas inspect actual fragments and the framework join.
   They make no assumption that a readable byte is writable. *)
Lemma V293_record_star_load_l : forall P Q tp a v,
  (forall s, s |= P -> load tp (getmem s) a = Some v) ->
  forall s, s |= P ** Q -> load tp (getmem s) a = Some v.
Proof.
  intros P Q tp a v Read s Hs.
  destruct s as [[[[[[ge le] M] ir] aux] O] op].
  apply sat_split in Hs.
  destruct Hs as (m1 & m2 & o1 & o2 & JM & JO & H1 & H2).
  eapply load_mem_mono; [exact (Read _ H1) | exists m2; exact JM].
Qed.

Lemma V293_record_star_load_r : forall P Q tp a v,
  (forall s, s |= Q -> load tp (getmem s) a = Some v) ->
  forall s, s |= P ** Q -> load tp (getmem s) a = Some v.
Proof.
  intros P Q tp a v Read s Hs.
  destruct s as [[[[[[ge le] M] ir] aux] O] op].
  apply sat_split in Hs.
  destruct Hs as (m1 & m2 & o1 & o2 & JM & JO & H1 & H2).
  eapply load_mem_mono; [exact (Read _ H2) | exists m1; apply map_join_comm; exact JM].
Qed.

Lemma V293_owned_record_cell_load : forall a tp v s,
  s |= V293_owned_record_cell (a,tp,v) ->
  load tp (getmem s) a = Some v.
Proof.
  intros a tp v s Hs. unfold V293_owned_record_cell in Hs.
  apply astar_l_apure_elim in Hs. destruct Hs as [Valid Owned].
  destruct s as [[[[[[ge le] M] ir] aux] O] op].
  destruct Owned as [Owned Empty].
  exact (@mapstoval_load _ _ _ _ _ Valid Owned).
Qed.

Lemma V293_owned_record_cell_store : forall a tp v replacement s,
  s |= V293_owned_record_cell (a,tp,v) ->
  exists Mf, store tp (getmem s) a replacement = Some Mf.
Proof.
  intros a tp v replacement s Hs. unfold V293_owned_record_cell in Hs.
  apply astar_l_apure_elim in Hs. destruct Hs as [Valid Owned].
  destruct s as [[[[[[ge le] M] ir] aux] O] op].
  destruct Owned as [Owned Empty].
  exact (store_exist_join' a tp v replacement M emp M Owned (map_join_emp M)).
Qed.

Lemma V293_owned_record_cells_load : forall cells a tp v,
  In (a,tp,v) cells -> forall s, s |= V293_owned_record_cells cells ->
  load tp (getmem s) a = Some v.
Proof.
  induction cells as [ | cell rest IH]; intros a tp v Member s Owned.
  - inversion Member.
  - destruct Member as [Same | Member].
    + subst cell. eapply V293_record_star_load_l; [apply V293_owned_record_cell_load | exact Owned].
    + eapply V293_record_star_load_r; [apply IH; exact Member | exact Owned].
Qed.

Lemma V293_record_layout_sound : forall M t p priority status message pend,
  p < 13 -> priority = Int.repr (Z.of_nat p) -> pend < 256 ->
  (forall a tp v, In (a,tp,v) (V293_record_layout t p status message pend) ->
    load tp M a = Some v) ->
  V293_task_record M t priority status message.
Proof.
  intros M t p priority status message pend Range Priority Pend Loads.
  exists p. split; [exact Range | ]. split; [exact Priority | ]. split.
  - unfold V293_tcb_updated_loads.
    repeat split; apply Loads; unfold V293_record_layout; simpl; tauto.
  - destruct status as [ | reason delay]; [ | destruct reason];
      cbn -[load loadm loadbytes];
      try (exists pend); unfold V293_wait_payload;
      repeat split; try exact Pend;
      apply Loads; unfold V293_record_layout; simpl; tauto.
Qed.

Theorem V293_owned_task_record_sound : forall t priority status message s,
  s |= V293_owned_task_record t priority status message ->
  V293_task_record (getmem s) t priority status message.
Proof.
  intros t priority status message s [p [pend Owned]].
  apply astar_l_apure_elim in Owned.
  destruct Owned as [[Range [Priority Pend]] Cells].
  eapply V293_record_layout_sound; [exact Range | exact Priority | exact Pend | ].
  intros a tp v Member. eapply V293_owned_record_cells_load; eauto.
Qed.

Lemma V293_task_record_sub : forall M Mf t priority status message,
  Maps.sub M Mf -> V293_task_record M t priority status message ->
  V293_task_record Mf t priority status message.
Proof.
  intros M Mf t priority status message Sub (p & Range & Priority & Fields & Status).
  exists p. split; [exact Range | ]. split; [exact Priority | ]. split.
  - unfold V293_tcb_updated_loads in *. destruct Fields as [A [B [C [D E]]]].
    repeat split; eapply load_mem_mono; eauto.
  - destruct status as [ | reason delay]; [ | destruct reason];
      cbn -[load loadm loadbytes] in *; unfold V293_wait_payload in *;
      repeat match goal with H : exists _, _ |- _ => destruct H end;
      repeat match goal with H : _ /\ _ |- _ => destruct H end;
      try (eexists); repeat split; try eassumption; eapply load_mem_mono; eauto.
Qed.

Lemma V293_owned_task_list_sound : forall entries t priority status message,
  In (t,(priority,status,message)) entries -> forall s,
  s |= V293_owned_task_list entries ->
  V293_task_record (getmem s) t priority status message.
Proof.
  induction entries as [ | [head [[p st] msg]] rest IH];
    intros t priority status message Member s Owned; [inversion Member | ].
  destruct s as [[[[[[ge le] M] ir] aux] O] op].
  apply sat_split in Owned.
  destruct Owned as (m1 & m2 & o1 & o2 & JM & JO & H1 & H2).
  destruct Member as [Same | Member].
  - inversion Same; subst. eapply V293_task_record_sub.
    + exists m2. exact JM.
    + exact (V293_owned_task_record_sound _ _ _ _ _ H1).
  - eapply V293_task_record_sub.
    + exists m1. apply map_join_comm; exact JM.
    + exact (IH _ _ _ _ Member _ H2).
Qed.

Lemma V293_task_lookup_list : forall entries t value,
  TcbMod.get' entries t = Some value -> In (t,value) entries.
Proof.
  induction entries as [ | [head value] rest IH]; intros t v Lookup; [discriminate | ].
  simpl in Lookup. destruct (tidspec.beq t head) eqn:Same.
  - apply tidspec.beq_true_eq in Same. subst head. inversion Lookup; subst value. left; reflexivity.
  - right. apply IH. exact Lookup.
Qed.

Theorem V293_owned_task_records_sound : forall tasks s,
  s |= V293_owned_task_records tasks -> V293_task_records (getmem s) tasks.
Proof.
  intros tasks s Owned t priority status message Lookup.
  eapply V293_owned_task_list_sound; [ | exact Owned].
  apply V293_task_lookup_list. exact Lookup.
Qed.

(* A spatial strengthening, not a replacement for the weak existing core.
   The same task map is used both in the abstract slot and in the physical
   resource assertion; there is no detached pure memory witness. *)
Definition V293_shared_task_records current tasks events now : asrt :=
  (CurTid current ** V293_shared_fields current tasks events now) **
  V293_owned_task_records tasks.

Theorem V293_shared_task_records_sound : forall current tasks events now s,
  s |= V293_shared_task_records current tasks events now ->
  get (getabst s) abstcblsid = Some (abstcblist tasks) /\
  V293_task_records (getmem s) tasks.
Proof.
  intros current tasks events now s Owned. split.
  - exact (proj1 (proj2 (V293_shared_fields_core_get _ _ _ _ _ _ Owned))).
  - destruct s as [[[[[[ge le] M] ir] aux] O] op].
    apply sat_split in Owned.
    destruct Owned as (m1 & m2 & o1 & o2 & JM & JO & Core & Records).
    pose proof (V293_owned_task_records_sound _ _ Records) as Fields.
    intros t priority status message Lookup.
    eapply V293_task_record_sub; [ | apply Fields; exact Lookup].
    exists m1. apply map_join_comm; exact JM.
Qed.

Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.

(* A store consumes no frame: the returned assertion is about the very memory
   produced by the framework store, not a separately chosen successor. *)
Lemma V293_owned_record_cell_update :
  forall a tp old replacement R ge le M ir aux O op,
  rule_type_val_match tp replacement = true ->
  (ge,le,M,ir,aux,O,op) |= V293_owned_record_cell (a,tp,old) ** R ->
  exists Mf, store tp M a replacement = Some Mf /\
    (ge,le,Mf,ir,aux,O,op) |= V293_owned_record_cell (a,tp,replacement) ** R.
Proof.
  intros a tp old replacement R ge le M ir aux O op Valid Owned.
  apply sat_split in Owned.
  destruct Owned as (m1 & m2 & o1 & o2 & JM & JO & Cell & Frame).
  unfold V293_owned_record_cell in Cell. apply astar_l_apure_elim in Cell.
  destruct Cell as [OldValid [Mapsto Empty]].
  destruct (store_exist_join' a tp old replacement m1 m2 M Mapsto JM) as [Mf Store].
  destruct (store_mapstoval_frame1 _ _ _ _ _ _ _ _ Mapsto JM Store)
    as (m1' & Mapsto' & LocalStore & JM').
  exists Mf. split; [exact Store | ].
  exists m1'. exists m2. exists Mf. exists o1. exists o2. exists O.
  split; [reflexivity | ]. split; [exact JM' | ].
  split; [reflexivity | ]. split; [exact JO | ]. split; [ | exact Frame].
  unfold V293_owned_record_cell. apply astar_l_apure_intro.
  - split; assumption.
  - exact Valid.
Qed.

Lemma V293_owned_byte_update : forall a old n R ge le M ir aux O op,
  n < 256 ->
  (ge,le,M,ir,aux,O,op) |= V293_owned_record_cell (a,Tint8,old) ** R ->
  (exists v, get M a = Some (true,v)) /\
  (ge,le,V293_put_byte M a n,ir,aux,O,op) |=
    V293_owned_record_cell (a,Tint8,V293_byteval n) ** R.
Proof.
  intros [b i] old n R ge le M ir aux O op Range Owned.
  destruct (V293_owned_record_cell_update _ _ _ (V293_byteval n) _ _ _ _ _ _ _ _
    (V293_byte_type n Range) Owned) as [Mf [Store Updated]].
  assert (Writable : exists v, get M (b,i) = Some (true,v)).
  { change (match get M (b,i) with
      | Some (true,_) => Some (V293_put_byte M (b,i) n)
      | _ => None end = Some Mf) in Store.
    destruct (get M (b,i)) as [[permission v] | ] eqn:Cell in Store; try discriminate.
    destruct permission; [eexists; exact Cell | discriminate]. }
  destruct Writable as [v Writable]. split; [eexists; exact Writable | ].
  pose proof (V293_put_byte_store M (b,i) n v Writable) as Same.
  rewrite Same in Store. inversion Store; subst Mf. exact Updated.
Qed.

(* Select a byte in a finite spatial list without forgetting the prefix,
   suffix, or an arbitrary physical/abstract frame. *)
Lemma V293_owned_cells_byte_update : forall prefix a old suffix n R ge le M ir aux O op,
  n < 256 ->
  (ge,le,M,ir,aux,O,op) |=
    V293_owned_record_cells (prefix ++ (a,Tint8,old) :: suffix) ** R ->
  (exists v, get M a = Some (true,v)) /\
  (ge,le,V293_put_byte M a n,ir,aux,O,op) |=
    V293_owned_record_cells (prefix ++ (a,Tint8,V293_byteval n) :: suffix) ** R.
Proof.
  induction prefix as [ | head rest IH];
    intros a old suffix n R ge le M ir aux O op Range Owned.
  - cbn [app V293_owned_record_cells] in Owned |- *.
    apply astar_assoc_elim in Owned.
    destruct (V293_owned_byte_update _ _ _ _ _ _ _ _ _ _ _ Range Owned) as [W Updated].
    split; [exact W | apply astar_assoc_intro; exact Updated].
  - cbn [app V293_owned_record_cells] in Owned |- *.
    apply astar_assoc_elim in Owned. apply astar_comm in Owned.
    apply astar_assoc_elim in Owned.
    destruct (IH _ _ _ _ _ _ _ _ _ _ _ _ Range Owned) as [W Updated].
    split; [exact W | ].
    apply astar_assoc_intro in Updated. apply astar_comm in Updated.
    apply astar_assoc_intro. exact Updated.
Qed.

Lemma V293_owned_cells_byte_writable : forall cells a old R ge le M ir aux O op,
  In (a,Tint8,old) cells ->
  (ge,le,M,ir,aux,O,op) |= V293_owned_record_cells cells ** R ->
  exists v, get M a = Some (true,v).
Proof.
  intros cells a old R ge le M ir aux O op Member Owned.
  apply in_split in Member. destruct Member as (prefix & suffix & Same). subst cells.
  exact (proj1 (V293_owned_cells_byte_update prefix a old suffix 0 R
    ge le M ir aux O op ltac:(lia) Owned)).
Qed.

Theorem V293_owned_task_record_update :
  forall t priority status message new R ge le M ir aux O op,
  new < 13 ->
  (ge,le,M,ir,aux,O,op) |= V293_owned_task_record t priority status message ** R ->
  V293_tcb_update_writable M (fst t) (Int.unsigned (snd t)) /\
  (ge,le,V293_tcb_update_memory M (fst t) (Int.unsigned (snd t)) new,ir,aux,O,op) |=
    V293_owned_task_record t (Int.repr (Z.of_nat new)) status message ** R.
Proof.
  intros t priority status message new R ge le M ir aux O op Range Owned.
  unfold V293_owned_task_record in Owned.
  apply astar_l_aexists_elim in Owned. destruct Owned as [old Owned].
  apply astar_l_aexists_elim in Owned. destruct Owned as [pend Owned].
  apply astar_assoc_elim in Owned. apply astar_l_apure_elim in Owned.
  destruct Owned as [[OldRange [Priority Pend]] Cells].
  assert (Writable : V293_tcb_update_writable M (fst t) (Int.unsigned (snd t))).
  { intros delta D.
    assert (delta = 50 \/ delta = 51 \/ delta = 52 \/ delta = 53 \/ delta = 54)%Z by lia.
    destruct H as [H | [H | [H | [H | H]]]]; subst delta.
    - eapply V293_owned_cells_byte_writable with
        (cells := V293_record_layout t old status message pend) (old := V293_byteval old);
        [left; reflexivity | exact Cells].
    - eapply V293_owned_cells_byte_writable with
        (cells := V293_record_layout t old status message pend) (old := V293_byteval (V293_prio_bit old));
        [right; right; left; reflexivity | exact Cells].
    - eapply V293_owned_cells_byte_writable with
        (cells := V293_record_layout t old status message pend) (old := V293_byteval (V293_prio_row old));
        [right; left; reflexivity | exact Cells].
    - eapply V293_owned_cells_byte_writable with
        (cells := V293_record_layout t old status message pend) (old := V293_byteval (2 ^ V293_prio_bit old));
        [right; right; right; right; left; reflexivity | exact Cells].
    - eapply V293_owned_cells_byte_writable with
        (cells := V293_record_layout t old status message pend) (old := V293_byteval (2 ^ V293_prio_row old));
        [right; right; right; left; reflexivity | exact Cells]. }
  split; [exact Writable | ].
  set (a := fun delta => (fst t,(Int.unsigned (snd t)+delta)%Z)).
  set (tail := skipn 5 (V293_record_layout t old status message pend)).
  change ((ge,le,M,ir,aux,O,op) |= V293_owned_record_cells
    ([(a 50%Z,Tint8,V293_byteval old);
      (a 52%Z,Tint8,V293_byteval (V293_prio_row old));
      (a 51%Z,Tint8,V293_byteval (V293_prio_bit old));
      (a 54%Z,Tint8,V293_byteval (2 ^ V293_prio_row old));
      (a 53%Z,Tint8,V293_byteval (2 ^ V293_prio_bit old))] ++ tail) ** R) in Cells.
  assert (Bounds : new < 256 /\ V293_prio_row new < 256 /\
    V293_prio_bit new < 256 /\ 2 ^ V293_prio_row new < 256 /\
    2 ^ V293_prio_bit new < 256).
  { unfold V293_prio_row, V293_prio_bit.
    do 13 (destruct new as [ | new]; [cbn; lia | ]). lia. }
  destruct Bounds as [B1 [B2 [B3 [B4 B5]]]].
  pose proof (proj2 (V293_owned_cells_byte_update nil (a 50%Z) _ _ new R
    ge le M ir aux O op B1 Cells)) as C1.
  pose proof (proj2 (V293_owned_cells_byte_update
    ([(a 50%Z,Tint8,V293_byteval new)]) (a 52%Z) _ _ (V293_prio_row new) R
    ge le _ ir aux O op B2 C1)) as C2.
  pose proof (proj2 (V293_owned_cells_byte_update
    ([(a 50%Z,Tint8,V293_byteval new); (a 52%Z,Tint8,V293_byteval (V293_prio_row new))])
    (a 51%Z) _ _ (V293_prio_bit new) R ge le _ ir aux O op B3 C2)) as C3.
  pose proof (proj2 (V293_owned_cells_byte_update
    ([(a 50%Z,Tint8,V293_byteval new); (a 52%Z,Tint8,V293_byteval (V293_prio_row new));
     (a 51%Z,Tint8,V293_byteval (V293_prio_bit new))])
    (a 54%Z) _ _ (2 ^ V293_prio_row new) R ge le _ ir aux O op B4 C3)) as C4.
  pose proof (proj2 (V293_owned_cells_byte_update
    ([(a 50%Z,Tint8,V293_byteval new); (a 52%Z,Tint8,V293_byteval (V293_prio_row new));
     (a 51%Z,Tint8,V293_byteval (V293_prio_bit new));
     (a 54%Z,Tint8,V293_byteval (2 ^ V293_prio_row new))])
    (a 53%Z) _ _ (2 ^ V293_prio_bit new) R ge le _ ir aux O op B5 C4)) as C5.
  apply astar_l_aexists_intro. exists new.
  apply astar_l_aexists_intro. exists pend.
  apply astar_assoc_intro. apply astar_l_apure_intro.
  - exact C5.
  - repeat split; assumption || reflexivity.
Qed.

(* The same five assignments as the existing C-fragment execution theorem.
   Writable permissions now follow from the spatial entry, and the returned
   ownership and every old observation refer to that very execution's M'. *)
Theorem V293_task_prio_tcb_owned_execution :
  forall P ks ge le M ir aux O op ptcb newprio yn xi byn xn bc bt base
    priority status message new R,
  new < 13 -> (0 <= base)%Z -> (base+55 <= Int.max_unsigned)%Z ->
  get le ptcb = Some (bc,Tptr V293_tcb_type) -> bc <> bt ->
  load (Tptr V293_tcb_type) M (bc,0%Z) = Some (Vptr (bt,Int.repr base)) ->
  V293_rekey_locals ge le M bt bt (V293_tcb_update_bindings newprio yn xi byn xn new) ->
  (ge,le,M,ir,aux,O,op) |=
    V293_owned_task_record (bt,Int.repr base) priority status message ** R ->
  let M' := V293_tcb_update_memory M bt base new in
  (cstepstar P
    (curs (V293_task_prio_tcb_update ptcb newprio yn xi byn xn),(kenil,ks)) (ge,le,M)
    (curs (sskip None),(kenil,ks)) (ge,le,M') /\
   V293_tcb_updated_loads M' bt base new /\
   load (Tptr V293_tcb_type) M' (bc,0%Z) = Some (Vptr (bt,Int.repr base)) /\
   V293_rekey_locals ge le M' bt bt (V293_tcb_update_bindings newprio yn xi byn xn new) /\
   V293_tcb_update_writable M' bt base /\
   (forall c i, c <> bt \/ (i < base+50)%Z \/ (base+54 < i)%Z ->
     get M' (c,i) = get M (c,i))) /\
  (ge,le,M',ir,aux,O,op) |=
    V293_owned_task_record (bt,Int.repr base) (Int.repr (Z.of_nat new)) status message ** R.
Proof.
  intros P ks ge le M ir aux O op ptcb newprio yn xi byn xn bc bt base
    priority status message new R Range Base End Bind Apart Pointer Locals Owned.
  destruct (V293_owned_task_record_update _ _ _ _ _ _ _ _ _ _ _ _ _ Range Owned)
    as [Writable Updated].
  cbn [fst snd] in Writable, Updated.
  rewrite Int.unsigned_repr in Writable, Updated by lia.
  cbn zeta. split.
  - exact (V293_task_prio_tcb_update_execution P ks ge le M ptcb newprio yn xi byn xn
      bc bt base new Range Base End Bind Apart Pointer Locals Writable).
  - exact Updated.
Qed.

Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import Coq.Relations.Relation_Operators.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.certiucos.v293.code.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.code.V293OSSchedDispatch.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.basetac.join_lib.

(* Strengthened full success-path return: actual bytes AND permissions of the
   target block agree with the five-store model; other writes and local free
   prevent claiming that an arbitrary spatial frame survives. *)
Theorem V293_critical_event_return_tcb_owned_block :
  forall P ks ge le caller M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp be ebase elo ehi xi bi ny nby nbx
    current reserved bcur bct curbase rb curprio
    running runblock run sched saved interrupt lock schednew high target schedcurrent counter f body next,
  initial < 256 -> (initial < 12 \/ initial = 255) -> new < 12 ->
  let old := if initial =? 255 then curprio else initial in
  old < 13 -> lo < 256 -> hi < 256 -> br <> bg ->
  (0 <= base)%Z -> (base+55 <= Int.max_unsigned)%Z ->
  get le table = None -> get ge table = Some (b,Tarray (Tptr V293_tcb_type) 13) ->
  get le oldprio = Some (bo,Tint8) -> get le newprio = Some (bn,Tint8) ->
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  b <> bo -> b <> bn -> b <> bc -> b <> bt ->
  b <> dy -> b <> dby -> b <> dx -> b <> br -> b <> bg ->
  load Tint8 M (bo,0%Z) = Some (V293_byteval initial) ->
  load Tint8 M (bn,0%Z) = Some (V293_byteval new) ->
  V293_bytes_writable M b (4*Z.of_nat old)%Z 4 ->
  V293_bytes_writable M b (4*Z.of_nat new)%Z 4 ->
  length entries = 13 -> V293_table_loads V293_tcb_type M b entries ->
  get le yo = Some (dy,Tint8) -> get le byo = Some (dby,Tint8) -> get le xo = Some (dx,Tint8) ->
  get le rows = None -> get ge rows = Some (br,Tarray Tint8 2) ->
  get le group = None -> get ge group = Some (bg,Tint8) ->
  dy <> dby -> dy <> dx -> dby <> dx ->
  (forall c, c = dy \/ c = dby \/ c = dx -> c <> bc /\ c <> bt /\ c <> br /\ c <> bg) ->
  V293_tcb_old_loads M bt base (V293_prio_row old)
    (2 ^ V293_prio_row old) (2 ^ V293_prio_bit old) ->
  (exists v, get M (dy,0%Z) = Some (true,v)) ->
  (exists v, get M (dby,0%Z) = Some (true,v)) ->
  (exists v, get M (dx,0%Z) = Some (true,v)) ->
  V293_rekey_bitmap_loads M br bg lo hi (V293_ready_group lo hi) ->
  V293_rekey_bitmap_writable M br bg ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> b /\ c <> dy /\ c <> dby /\ c <> dx) ->
  get le pevent = Some (bp,Tptr V293_event_type) ->
  V293_bytes_writable M bp 0%Z 4 ->
  load (Tcom_ptr 411%Z) M (bt,(base+28)%Z) = Some (Vptr (be,Int.repr ebase)) ->
  bc <> br -> bc <> bg -> bt <> br -> bt <> bg ->
  bp <> b -> bp <> dy -> bp <> dby -> bp <> dx -> bp <> br -> bp <> bg ->
  bp <> be ->
  be <> b -> be <> dy -> be <> dby -> be <> dx -> be <> br -> be <> bg ->
  elo < 256 -> ehi < 256 -> (0 <= ebase)%Z -> (ebase+12 <= Int.max_unsigned)%Z ->
  V293_event_bitmap_loads M be ebase elo ehi (V293_ready_group elo ehi) ->
  V293_event_bitmap_writable M be ebase ->
  (forall x v c, In (x,v) (V293_rekey_ready_bindings yo yn xo xn byo byn old new) ->
    get le x = Some (c,Tint8) -> c <> bp /\ c <> be) ->
  bc <> bt -> bc <> bp -> bc <> be -> bt <> bp -> bt <> be ->
  get le xi = Some (bi,Tint8) ->
  (forall c, c = bn \/ c = bi ->
    c <> b /\ c <> dy /\ c <> dby /\ c <> dx /\ c <> br /\ c <> bg /\ c <> bp /\ c <> be /\ c <> bt) ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> bt) ->
  V293_tcb_update_writable M bt base ->
  get le yn = Some (ny,Tint8) -> get le byn = Some (nby,Tint8) ->
  get le xn = Some (nbx,Tint8) ->
  ny <> bi -> ny <> nby -> ny <> nbx -> bi <> nby -> bi <> nbx -> nby <> nbx ->
  (forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->
    c <> b /\ c <> bo /\ c <> bn /\ c <> bc /\ c <> bt /\
    c <> dy /\ c <> dby /\ c <> dx /\ c <> br /\ c <> bg /\ c <> bp /\ c <> be) ->
  (forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->
    exists v, get M (c,0%Z) = Some (true,v)) ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat new)%Z) = Some Vnull ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat old)%Z) = Some (Vptr (bt,Int.repr base)) ->
  bo <> bn -> bc <> bn -> bc <> bo ->
  (initial = 255 ->
    get le current = None /\ get ge current = Some (bcur,Tptr V293_tcb_type) /\
    load (Tptr V293_tcb_type) M (bcur,0%Z) = Some (Vptr (bct,Int.repr curbase)) /\
    (0 <= curbase)%Z /\ (curbase+50 <= Int.max_unsigned)%Z /\
    load Tint8 M (bct,(curbase+50)%Z) = Some (V293_byteval curprio) /\
    (exists v, get M (bo,0%Z) = Some (true,v))) ->
  get le reserved = None -> get ge reserved = Some (rb,Tint8) ->
  (bt,Int.repr base) <> (rb,Int.zero) ->
  V293_bytes_writable M bc 0%Z 4 ->
  (forall c, In c [b;bn;bt;dy;dby;dx;br;bg;bp;be;ny;bi;nby;nbx] ->
    c <> bo /\ c <> bc) ->
  run < 256 -> get le running = None -> get ge running = Some (runblock,Tint8) ->
  load Tint8 M (runblock,0%Z) = Some (V293_byteval run) ->
  (run = 1 ->
    P sched = Some (V293_OSSched_success_function saved interrupt lock schednew table high target schedcurrent counter) /\
    saved <> interrupt /\ saved <> lock /\ V293_success_sched_blocked ge M interrupt lock) ->
  V293_success_globals_away ge [running;interrupt;lock] [bo;bc;b;dy;dby;dx;br;bg;bp;bt;ny;bi;nby;nbx;be] ->
  callcont ks = Some (kcall f body caller next) ->
  NoDup (map fst (getaddr le)) ->
  (forall c t, In (c,t) (getaddr le) -> V293_bytes_writable M c 0%Z (typelen t)) ->
  (forall c, In c [b;bt;br;bg;be] -> ~ In c (map fst (getaddr le))) ->
  exists Mf,
  let old := if initial =? 255 then curprio else initial in
  let fr := V293_ready_branch_rows lo hi old new in
  V293_local_steps P
    (curs (sseq (V293_primitive_success_update table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent xi current reserved)
      (V293_task_prio_success_tail running sched)),(kenil,ks))
    ((ge,le,M),ir,(enabled,si,ci))
    (curs (sskip (Some (Vint32 Int.zero))),(kenil,next))
    ((ge,caller,Mf),ir,(enabled,si,ci)) /\
  V293_tcb_updated_loads Mf bt base new /\
  V293_rekey_bitmap_loads Mf br bg (fst fr) (snd fr) (V293_ready_group (fst fr) (snd fr)) /\
  V293_table_loads V293_tcb_type Mf b
    (update_nth_val new (update_nth_val old entries Vnull) (Vptr (bt,Int.repr base))) /\
  (let er := V293_ready_rekey_rows elo ehi old new in
    V293_event_bitmap_loads Mf be ebase (fst er) (snd er) (V293_ready_group (fst er) (snd er))) /\
  load (Tcom_ptr 411%Z) Mf (bt,(base+28)%Z) = Some (Vptr (be,Int.repr ebase)) /\
  (forall c i, ~ In c (map fst (getaddr le)) -> ~ In c [bo;bc;b;dy;dby;dx;br;bg;bp;be;bt;ny;bi;nby;nbx] ->
    get Mf (c,i) = get M (c,i)) /\
  (forall c t k, In (c,t) (getaddr le) -> k < typelen t ->
    get Mf (c,Z.of_nat k) = None) /\
  (forall i, (i < base+50 \/ base+54 < i)%Z -> get Mf (bt,i) = get M (bt,i)) /\
  (forall i, (i < ebase+10 \/ ebase+12 < i)%Z -> get Mf (be,i) = get M (be,i)) /\
  (forall i, get Mf (bt,i) = get (V293_tcb_update_memory M bt base new) (bt,i)).
Proof.
  intros P ks ge le caller M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp be ebase elo ehi xi bi ny nby nbx current reserved bcur bct curbase rb curprio running runblock run sched saved interrupt lock schednew high target schedcurrent counter f body next
    Input Valid N old O L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg Lo Ln Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields Wy Wby Wx Loads W NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg PE Eb Ey Eby Ex Er Eg EL EH EB ELimit ELoads EW LocalApart CT CP CE TP TE Bi ExtraApart NewTcbApart TW NBy NBby NBx NYI NYBY NYBX NIBY NIBX NBYBX CoordApart CoordW Empty Slot Onew Cnew CO Self Nreserved Greserved Token CW EntryApart
    RunRange NoRun GlobalRun LoadRun WhenRunning Away Call ND InitialWritable HeapApart.
  pose proof (V293_critical_event_update_execution_writable_event_frame P (kseq (V293_task_prio_success_tail running sched) ks) ge le M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp be ebase elo ehi xi bi ny nby nbx current reserved bcur bct curbase rb curprio Input Valid N O L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg Lo Ln Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields Wy Wby Wx Loads W NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg PE Eb Ey Eby Ex Er Eg EL EH EB ELimit ELoads EW LocalApart CT CP CE TP TE Bi ExtraApart NewTcbApart TW NBy NBby NBx NYI NYBY NYBX NIBY NIBX NBYBX CoordApart CoordW Empty Slot Onew Cnew CO Self Nreserved Greserved Token CW EntryApart) as Original.
  destruct Original as [Mg Result]. cbn zeta in Result |- *.
  destruct Result as [UpdateWritable [Exec Rest]].
  set (Mh := V293_tcb_update_memory Mg bt base new) in *.
  assert (Frame : forall c i, ~ In c [bo;bc;b;dy;dby;dx;br;bg;bp;bt;ny;bi;nby;nbx;be] -> get Mh (c,i) = get M (c,i)).
  { intros c i NotWritten. destruct Rest as (Updated & Ready & Table & OldSlot & NewSlot & EventLoads & Read & Pointer & Writable & Internal & Untouched & Frame & EventHeader). apply Frame; clear - NotWritten; simpl in NotWritten;intuition congruence. }
  assert (RunLoad : load Tint8 Mh (runblock,0%Z) = Some (V293_byteval run)).
  { etransitivity; [apply V293_load_block_frame;intro i;apply Frame;eapply Away with (x:=running);simpl;eauto | exact LoadRun]. }
  assert (Running : run = 1 ->
    P sched = Some (V293_OSSched_success_function saved interrupt lock schednew table high target schedcurrent counter) /\
    saved <> interrupt /\ saved <> lock /\ V293_success_sched_blocked ge Mh interrupt lock).
  { intro One. destruct (WhenRunning One) as (Program & SI & SL & Blocked).
    split; [exact Program | ]. split; [exact SI | ]. split; [exact SL | ].
    eapply V293_success_sched_blocked_frame; [ | exact Frame | exact Blocked].
    intros x c X G. eapply Away with (x:=x); [simpl in X |- *;tauto | exact G]. }
  assert (FinalWritable : forall c t, In (c,t) (getaddr le) ->
    V293_bytes_writable Mh c 0%Z (typelen t)).
  { intros c t I k K. destruct (InitialWritable c t I k K) as [v W0].
    eapply UpdateWritable;exact W0. }
  destruct (V293_success_tail_return_execution P ks ge le caller Mh ir enabled si ci
    running runblock run sched saved interrupt lock schednew table high target schedcurrent counter
    f body next RunRange NoRun GlobalRun RunLoad Running Call ND FinalWritable)
    as (Mf & Return & FreeFrame & Removed).
  assert (FinalLoad : forall tp c i, In c [b;bt;br;bg;be] ->
    load tp Mf (c,i) = load tp Mh (c,i)).
  { intros tp c i I. apply V293_load_block_frame. intro j.
    apply FreeFrame. apply HeapApart;exact I. }
  exists Mf. cbn zeta. fold old. split.
  - eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sseq_step]. }
    eapply V293_local_trans; [exact Exec | ].
    eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sskip_step]. }
    exact Return.
  - destruct Rest as (Updated & Ready & Table & OldSlot & NewSlot & EventReady & Read & Pointer & FinalEW & Internal & Untouched & UFrame & EventHeader).
    split. { unfold V293_tcb_updated_loads in *. repeat rewrite FinalLoad by (simpl;tauto). exact Updated. }
    split. { unfold V293_rekey_bitmap_loads in *. repeat rewrite FinalLoad by (simpl;tauto). exact Ready. }
    split. { intros p R. rewrite FinalLoad by (simpl;tauto). exact (Table p R). }
    split. { unfold V293_event_bitmap_loads in *. repeat rewrite FinalLoad by (simpl;tauto). exact EventReady. }
    split. { rewrite FinalLoad by (simpl;tauto). exact Internal. }
    split.
    + intros c i NotLocal NotWritten. rewrite FreeFrame by exact NotLocal.
      apply UFrame; clear -NotWritten; simpl in NotWritten;intuition congruence.
    + split; [exact Removed | ]. split.
      * intros i Outside. rewrite FreeFrame by (apply HeapApart; simpl;tauto).
        apply Untouched. exact Outside.
      * split.
        -- intros i Outside. rewrite FreeFrame by (apply HeapApart; simpl;tauto).
           apply EventHeader. exact Outside.
        -- intro i. rewrite FreeFrame by (apply HeapApart; simpl;tauto).
           destruct (Z_lt_dec i (base+50)) as [Low | Low].
           { rewrite Untouched by (clear -Low; lia). symmetry.
             unfold V293_tcb_update_memory.
             repeat rewrite V293_put_byte_other by (intro E; injection E as Offset; clear -Low Offset; lia).
             reflexivity. }
           destruct (Z_lt_dec (base+54) i) as [High | High].
           { rewrite Untouched by (clear -Low High; lia). symmetry.
             unfold V293_tcb_update_memory.
             repeat rewrite V293_put_byte_other by (intro E; injection E as Offset; clear -High Offset; lia).
             reflexivity. }
           assert (ByteOffset : (i=base+50 \/ i=base+51 \/ i=base+52 \/ i=base+53 \/ i=base+54)%Z) by (clear -Low High; lia).
           destruct ByteOffset as [-> | [-> | [-> | [-> | ->]]]];
             unfold Mh,V293_tcb_update_memory;
             repeat first [rewrite V293_put_byte_get_same |
               rewrite V293_put_byte_other by (intro E; injection E as Offset; clear -Offset; lia)];
             reflexivity.
Qed.

(* A record fragment has no abstract resource and no bytes outside its block.
   These facts are about owned fragments, not about whole-memory load results. *)
Lemma V293_owned_cells_block_local : forall cells b,
  (forall a tp v, In (a,tp,v) cells -> fst a = b) ->
  forall ge le M ir aux O op,
  (ge,le,M,ir,aux,O,op) |= V293_owned_record_cells cells ->
  O = emp /\ (forall c i, c <> b -> get M (c,i) = None) /\
  (forall ge' le' ir' aux' op',
    (ge',le',M,ir',aux',emp,op') |= V293_owned_record_cells cells).
Proof.
  induction cells as [ | [[a tp] v] rest IH]; intros b Support ge le M ir aux O op Owned.
  - destruct Owned as [EM EO]. change (M=emp) in EM. change (O=emp) in EO. subst M O.
    split; [reflexivity | ]. split; [intros; apply map_emp_get | ].
    intros; split; reflexivity.
  - apply sat_split in Owned.
    destruct Owned as (mh & mt & oh & ot & JM & JO & Head & Tail).
    destruct (IH b ltac:(intros aa tt vv Member; apply Support with tt vv; right; exact Member)
      ge le mt ir aux ot op Tail) as [ET [ST RT]].
    assert (AB : fst a = b) by (apply Support with tp v; left; reflexivity).
    unfold V293_owned_record_cell in Head. apply astar_l_apure_elim in Head.
    destruct Head as [Valid [Points EH]]. change (oh=emp) in EH. subst oh ot.
    apply map_join_comm in JO. apply map_join_emp' in JO. subst O.
    split; [reflexivity | ]. split.
    + intros c i Apart.
      erewrite map_join_get_none; [apply ST; exact Apart | exact JM | ].
      destruct Points as (bytes & Enc & Bytes). destruct a as [ba offset]. cbn in AB. subst ba.
      eapply V293_ptomvallist_other_block; eauto.
    + intros ge' le' ir' aux' op'.
      apply sat_split'. exists mh. exists mt. exists (emp:osabst). exists (emp:osabst).
      split; [exact JM | ]. split; [apply map_join_emp | ]. split; [ | apply RT].
      unfold V293_owned_record_cell. apply astar_l_apure_intro.
      * split; [exact Points | reflexivity].
      * exact Valid.
Qed.

Lemma V293_owned_task_record_block_local : forall t priority status message ge le M ir aux O op,
  (ge,le,M,ir,aux,O,op) |= V293_owned_task_record t priority status message ->
  O = emp /\ (forall c i, c <> fst t -> get M (c,i) = None) /\
  (forall ge' le' ir' aux' op',
    (ge',le',M,ir',aux',emp,op') |= V293_owned_task_record t priority status message).
Proof.
  intros t priority status message ge le M ir aux O op [p [pend Owned]].
  apply astar_l_apure_elim in Owned. destruct Owned as [Bounds Cells].
  assert (Support : forall a tp v, In (a,tp,v) (V293_record_layout t p status message pend) -> fst a = fst t).
  { intros a tp v Member. unfold V293_record_layout in Member.
    apply in_app_or in Member. destruct Member as [Member | Member].
    - cbn [In] in Member.
      destruct Member as [E | [E | [E | [E | [E | [E | F]]]]]];
        [ | | | | | | contradiction]; inversion E; reflexivity.
    - destruct status as [ | reason delay]; [ | destruct reason]; cbn [In] in Member;
        repeat match goal with H : _ \/ _ |- _ => destruct H end; try contradiction;
        match goal with H : _ = (a,tp,v) |- _ => inversion H; reflexivity end. }
  destruct (V293_owned_cells_block_local _ _ Support _ _ _ _ _ _ _ Cells)
    as [Empty [SupportM Rebase]].
  split; [exact Empty | ]. split; [exact SupportM | ].
  intros. exists p. exists pend. apply astar_l_apure_intro; [apply Rebase | exact Bounds].
Qed.

(* The same owned fragment is transported using byte AND permission equality.
   The final abstract resource/environment may change and R may be freed. *)
Theorem V293_owned_task_record_block_frame : forall t priority status message R
    ge le M ir aux O op ge' le' Mf ir' aux' O' op',
  (ge,le,M,ir,aux,O,op) |= V293_owned_task_record t priority status message ** R ->
  (forall i, get Mf (fst t,i) = get M (fst t,i)) ->
  (ge',le',Mf,ir',aux',O',op') |= V293_owned_task_record t priority status message ** Atrue.
Proof.
  intros t priority status message R ge le M ir aux O op ge' le' Mf ir' aux' O' op' Owned Frame.
  apply sat_split in Owned.
  destruct Owned as (mr & mf & ore & ofr & JM & JO & Record & Rest).
  destruct (V293_owned_task_record_block_local _ _ _ _ _ _ _ _ _ _ _ Record)
    as [Empty [Support Rebase]]. subst ore.
  assert (Sub : Maps.sub mr Mf).
  { eapply V293_owned_block_frame with (before:=M) (b:=fst t).
    - exists mf. exact JM.
    - exact Support.
    - exact Frame. }
  destruct Sub as [remaining Joined].
  apply sat_split'. exists mr. exists remaining. exists (emp:osabst). exists O'.
  split; [exact Joined | ]. split; [apply map_join_comm; apply map_join_emp | ].
  split; [apply Rebase | exact I].
Qed.

Lemma V293_owned_task_fields_reconstruct : forall current tasks events now t priority status message
    ge le M ir aux O op,
  (ge,le,M,ir,aux,O,op) |= V293_owned_task_record t priority status message ** Atrue ->
  (ge,le,M,ir,aux,O,op) |= V293_shared_fields current tasks events now ** Atrue ->
  (ge,le,M,ir,aux,O,op) |=
    (V293_owned_task_record t priority status message ** V293_shared_fields current tasks events now) ** Atrue.
Proof.
  intros current tasks events now t priority status message ge le M ir aux O op HR HF.
  apply sat_split in HR. destruct HR as (mr & mrr & ore & orr & JMR & JOR & Record & _).
  destruct (V293_owned_task_record_block_local _ _ _ _ _ _ _ _ _ _ _ Record)
    as [Empty _]. subst ore.
  apply sat_split in HF. destruct HF as (mf & mrf & ofields & orest & JMF & JOF & Fields & _).
  pose proof (V293_shared_fields_empty_heap _ _ _ _ _ _ _ _ _ _ _ Fields) as EmptyM. subst mf.
  apply sat_split'. exists mr. exists mrr. exists ofields. exists orest.
  split; [exact JMR | ]. split; [exact JOF | ]. split; [ | exact I].
  apply sat_split'. exists mr. exists (emp:mem). exists (emp:osabst). exists ofields.
  split; [apply map_join_emp | ]. split; [apply map_join_comm; apply map_join_emp | ].
  split; assumption.
Qed.

(* Joint physical/abstract success return. The selected owned record is
   tied to the very task map changed by the abstract step. This is not all
   task records, a full shared invariant, or the unrestricted scheduler. *)
Theorem V293_critical_wait_record_owned_execution :
  forall P ks ge le caller M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp be ebase elo ehi xi bi ny nby nbx
    current reserved bcur bct curbase rb curprio
    running runblock run sched saved interrupt lock schednew high target schedcurrent counter f body next
    sc abstract_current tasks events now Os Of OO op R reason delay message,
  initial < 256 -> (initial < 12 \/ initial = 255) -> new < 12 ->
  let old := if initial =? 255 then curprio else initial in
  old < 13 -> lo < 256 -> hi < 256 -> br <> bg ->
  (0 <= base)%Z -> (base+55 <= Int.max_unsigned)%Z ->
  get le table = None -> get ge table = Some (b,Tarray (Tptr V293_tcb_type) 13) ->
  get le oldprio = Some (bo,Tint8) -> get le newprio = Some (bn,Tint8) ->
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  b <> bo -> b <> bn -> b <> bc -> b <> bt ->
  b <> dy -> b <> dby -> b <> dx -> b <> br -> b <> bg ->
  load Tint8 M (bo,0%Z) = Some (V293_byteval initial) ->
  load Tint8 M (bn,0%Z) = Some (V293_byteval new) ->
  V293_bytes_writable M b (4*Z.of_nat old)%Z 4 ->
  V293_bytes_writable M b (4*Z.of_nat new)%Z 4 ->
  length entries = 13 -> V293_table_loads V293_tcb_type M b entries ->
  get le yo = Some (dy,Tint8) -> get le byo = Some (dby,Tint8) -> get le xo = Some (dx,Tint8) ->
  get le rows = None -> get ge rows = Some (br,Tarray Tint8 2) ->
  get le group = None -> get ge group = Some (bg,Tint8) ->
  dy <> dby -> dy <> dx -> dby <> dx ->
  (forall c, c = dy \/ c = dby \/ c = dx -> c <> bc /\ c <> bt /\ c <> br /\ c <> bg) ->
  V293_tcb_old_loads M bt base (V293_prio_row old)
    (2 ^ V293_prio_row old) (2 ^ V293_prio_bit old) ->
  (exists v, get M (dy,0%Z) = Some (true,v)) ->
  (exists v, get M (dby,0%Z) = Some (true,v)) ->
  (exists v, get M (dx,0%Z) = Some (true,v)) ->
  V293_rekey_bitmap_loads M br bg lo hi (V293_ready_group lo hi) ->
  V293_rekey_bitmap_writable M br bg ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> b /\ c <> dy /\ c <> dby /\ c <> dx) ->
  get le pevent = Some (bp,Tptr V293_event_type) ->
  V293_bytes_writable M bp 0%Z 4 ->
  load (Tcom_ptr 411%Z) M (bt,(base+28)%Z) = Some (Vptr (be,Int.repr ebase)) ->
  bc <> br -> bc <> bg -> bt <> br -> bt <> bg ->
  bp <> b -> bp <> dy -> bp <> dby -> bp <> dx -> bp <> br -> bp <> bg ->
  bp <> be ->
  be <> b -> be <> dy -> be <> dby -> be <> dx -> be <> br -> be <> bg ->
  elo < 256 -> ehi < 256 -> (0 <= ebase)%Z -> (ebase+12 <= Int.max_unsigned)%Z ->
  V293_event_bitmap_loads M be ebase elo ehi (V293_ready_group elo ehi) ->
  V293_event_bitmap_writable M be ebase ->
  (forall x v c, In (x,v) (V293_rekey_ready_bindings yo yn xo xn byo byn old new) ->
    get le x = Some (c,Tint8) -> c <> bp /\ c <> be) ->
  bc <> bt -> bc <> bp -> bc <> be -> bt <> bp -> bt <> be ->
  get le xi = Some (bi,Tint8) ->
  (forall c, c = bn \/ c = bi ->
    c <> b /\ c <> dy /\ c <> dby /\ c <> dx /\ c <> br /\ c <> bg /\ c <> bp /\ c <> be /\ c <> bt) ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> bt) ->
  get le yn = Some (ny,Tint8) -> get le byn = Some (nby,Tint8) ->
  get le xn = Some (nbx,Tint8) ->
  ny <> bi -> ny <> nby -> ny <> nbx -> bi <> nby -> bi <> nbx -> nby <> nbx ->
  (forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->
    c <> b /\ c <> bo /\ c <> bn /\ c <> bc /\ c <> bt /\
    c <> dy /\ c <> dby /\ c <> dx /\ c <> br /\ c <> bg /\ c <> bp /\ c <> be) ->
  (forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->
    exists v, get M (c,0%Z) = Some (true,v)) ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat new)%Z) = Some Vnull ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat old)%Z) = Some (Vptr (bt,Int.repr base)) ->
  bo <> bn -> bc <> bn -> bc <> bo ->
  (initial = 255 ->
    get le current = None /\ get ge current = Some (bcur,Tptr V293_tcb_type) /\
    load (Tptr V293_tcb_type) M (bcur,0%Z) = Some (Vptr (bct,Int.repr curbase)) /\
    (0 <= curbase)%Z /\ (curbase+50 <= Int.max_unsigned)%Z /\
    load Tint8 M (bct,(curbase+50)%Z) = Some (V293_byteval curprio) /\
    (exists v, get M (bo,0%Z) = Some (true,v))) ->
  get le reserved = None -> get ge reserved = Some (rb,Tint8) ->
  (bt,Int.repr base) <> (rb,Int.zero) ->
  V293_bytes_writable M bc 0%Z 4 ->
  (forall c, In c [b;bn;bt;dy;dby;dx;br;bg;bp;be;ny;bi;nby;nbx] ->
    c <> bo /\ c <> bc) ->
  run < 256 -> get le running = None -> get ge running = Some (runblock,Tint8) ->
  load Tint8 M (runblock,0%Z) = Some (V293_byteval run) ->
  (run = 1 ->
    P sched = Some (V293_OSSched_success_function saved interrupt lock schednew table high target schedcurrent counter) /\
    saved <> interrupt /\ saved <> lock /\ V293_success_sched_blocked ge M interrupt lock) ->
  V293_success_globals_away ge [running;interrupt;lock] [bo;bc;b;dy;dby;dx;br;bg;bp;bt;ny;bi;nby;nbx;be] ->
  callcont ks = Some (kcall f body caller next) ->
  NoDup (map fst (getaddr le)) ->
  (forall c t, In (c,t) (getaddr le) -> V293_bytes_writable M c 0%Z (typelen t)) ->
  (forall c, In c [b;bt;br;bg;be] -> ~ In c (map fst (getaddr le))) ->
  V293_priority_table entries tasks -> V293_bitmap_tasks lo hi tasks ->
  V293_event_wait_tasks elo ehi tasks reason ->
  (reason = os_stat_sem (be,Int.repr ebase) \/ reason = os_stat_q (be,Int.repr ebase) \/
    reason = os_stat_mbox (be,Int.repr ebase) \/ reason = os_stat_mutexsem (be,Int.repr ebase)) ->
  get tasks (bt,Int.repr base) = Some (Int.repr (Z.of_nat old),wait reason delay,message) ->
  (ge,le,M,ir,(enabled,si,ci),Os,op) |=
    V293_shared_fields abstract_current tasks events now **
      (V293_owned_task_record (bt,Int.repr base) (Int.repr (Z.of_nat old)) (wait reason delay) message ** R) ->
  join Os Of OO ->
  exists Mf Os' OO',
  let old := if initial =? 255 then curprio else initial in
  Os' = set Os abstcblsid (abstcblist
    (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message))) /\
  join Os' Of OO' /\
  spec_step sc (spec_prim nil (V293_wait_prio_step (bt,Int.repr base) old new)) OO
    (spec_done (Some (Vint32 Int.zero))) OO' /\
  (let old := if initial =? 255 then curprio else initial in
  let fr := V293_ready_branch_rows lo hi old new in
  V293_local_steps P
    (curs (sseq (V293_primitive_success_update table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent xi current reserved)
      (V293_task_prio_success_tail running sched)),(kenil,ks))
    ((ge,le,M),ir,(enabled,si,ci))
    (curs (sskip (Some (Vint32 Int.zero))),(kenil,next))
    ((ge,caller,Mf),ir,(enabled,si,ci)) /\
  V293_tcb_updated_loads Mf bt base new /\
  V293_rekey_bitmap_loads Mf br bg (fst fr) (snd fr) (V293_ready_group (fst fr) (snd fr)) /\
  V293_table_loads V293_tcb_type Mf b
    (update_nth_val new (update_nth_val old entries Vnull) (Vptr (bt,Int.repr base))) /\
  (let er := V293_ready_rekey_rows elo ehi old new in
    V293_event_bitmap_loads Mf be ebase (fst er) (snd er) (V293_ready_group (fst er) (snd er))) /\
  load (Tcom_ptr 411%Z) Mf (bt,(base+28)%Z) = Some (Vptr (be,Int.repr ebase)) /\
  (forall c i, ~ In c (map fst (getaddr le)) -> ~ In c [bo;bc;b;dy;dby;dx;br;bg;bp;be;bt;ny;bi;nby;nbx] ->
    get Mf (c,i) = get M (c,i)) /\
  (forall c t k, In (c,t) (getaddr le) -> k < typelen t ->
    get Mf (c,Z.of_nat k) = None) /\
  (forall i, (i < base+50 \/ base+54 < i)%Z -> get Mf (bt,i) = get M (bt,i)) /\
  (forall i, (i < ebase+10 \/ ebase+12 < i)%Z -> get Mf (be,i) = get M (be,i)) /\
  (forall i, get Mf (bt,i) = get (V293_tcb_update_memory M bt base new) (bt,i))) /\
  (ge,caller,Mf,ir,(enabled,si,ci),OO',op) |=
    (V293_owned_task_record (bt,Int.repr base) (Int.repr (Z.of_nat new)) (wait reason delay) message **
      V293_shared_fields abstract_current
        (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) events now) ** Atrue /\
  V293_bitmap_tasks lo hi (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) /\
  V293_priority_table
    (update_nth_val new (update_nth_val old entries Vnull) (Vptr (bt,Int.repr base)))
    (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) /\
  (let er := V293_ready_rekey_rows elo ehi old new in
    V293_event_wait_tasks (fst er) (snd er)
      (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) reason).
Proof.
  intros P ks ge le caller M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp be ebase elo ehi xi bi ny nby nbx current reserved bcur bct curbase rb curprio running runblock run sched saved interrupt lock schednew high target schedcurrent counter f body next
    sc abstract_current tasks events now Os Of OO op R reason delay message
    Input Valid N old O L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg Lo Ln Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields Wy Wby Wx Loads W NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg PE Eb Ey Eby Ex Er Eg EL EH EB ELimit ELoads EW LocalApart CT CP CE TP TE Bi ExtraApart NewTcbApart NBy NBby NBx NYI NYBY NYBX NIBY NIBX NBYBX CoordApart CoordW Empty Slot Onew Cnew CO Self Nreserved Greserved Token CW EntryApart
    RunRange NoRun GlobalRun LoadRun WhenRunning Away Call ND InitialWritable HeapApart
    TaskTable Bitmap EventBitmap Reason Task Owned Frame.
  assert (EmptyEntry : nth new entries Vnull = Vnull).
  { pose proof (View new ltac:(clear -N; lia)) as Loaded.
    rewrite Empty in Loaded. inversion Loaded. reflexivity. }
  assert (Fresh : forall t status msg,
      get tasks t <> Some (Int.repr (Z.of_nat new),status,msg)).
  { intros t status msg Member. pose proof
      (V293_rekey_task_entry entries tasks t new status msg TaskTable ltac:(clear -N; lia) Member) as Entry.
    rewrite EmptyEntry in Entry. discriminate. }
  destruct (V293_wait_prio_owned_step sc abstract_current tasks events now
    (bt,Int.repr base) old new reason delay message ge le M ir (enabled,si,ci) Os op
    (V293_owned_task_record (bt,Int.repr base) (Int.repr (Z.of_nat old)) (wait reason delay) message ** R)
    Of OO O N Task Fresh Owned Frame)
    as (Os' & OO' & Identity & Frame' & Abstract & UpdatedOwned).
  pose proof UpdatedOwned as EntryPhysical.
  apply astar_comm in EntryPhysical. apply astar_assoc_elim in EntryPhysical.
  destruct (V293_owned_task_record_update _ _ _ _ new _ _ _ _ _ _ _ _
    ltac:(clear -N; lia) EntryPhysical) as [TW ModelOwned].
  cbn [fst snd] in TW,ModelOwned. rewrite Int.unsigned_repr in TW,ModelOwned by lia.
  destruct (V293_critical_event_return_tcb_owned_block P ks ge le caller M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp be ebase elo ehi xi bi ny nby nbx current reserved bcur bct curbase rb curprio running runblock run sched saved interrupt lock schednew high target schedcurrent counter f body next Input Valid N O L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg Lo Ln Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields Wy Wby Wx Loads W NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg PE Eb Ey Eby Ex Er Eg EL EH EB ELimit ELoads EW LocalApart CT CP CE TP TE Bi ExtraApart NewTcbApart TW NBy NBby NBx NYI NYBY NYBX NIBY NIBX NBYBX CoordApart CoordW Empty Slot Onew Cnew CO Self Nreserved Greserved Token CW EntryApart
    RunRange NoRun GlobalRun LoadRun WhenRunning Away Call ND InitialWritable HeapApart)
    as (Mf & Result).
  cbn zeta in Result. fold old in Result.
  pose proof Result as Observations.
  destruct Observations as (Exec & Updated & Ready & Table & EventReady & Pointer
    & Outside & Removed & TcbFrame & EventFrame & ExactBlock).
  assert (FinalRecord : (ge,caller,Mf,ir,(enabled,si,ci),OO',op) |=
      V293_owned_task_record (bt,Int.repr base) (Int.repr (Z.of_nat new)) (wait reason delay) message ** Atrue).
  { eapply V293_owned_task_record_block_frame; [exact ModelOwned | exact ExactBlock]. }
  assert (FinalFields : (ge,caller,Mf,ir,(enabled,si,ci),OO',op) |=
      V293_shared_fields abstract_current
        (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) events now ** Atrue).
  { eapply V293_shared_fields_owned_transport; [exact UpdatedOwned | exact Frame']. }
  destruct (V293_wait_prio_branch_relations lo hi elo ehi entries tasks
    (bt,Int.repr base) old new reason delay message O N TaskTable Bitmap EventBitmap Task EmptyEntry)
    as (Branch & FinalBitmap & FinalTable & FinalEvent).
  exists Mf. exists Os'. exists OO'. cbn zeta. fold old.
  split; [exact Identity | ]. split; [exact Frame' | ]. split; [exact Abstract | ].
  split; [exact Result | ]. split.
  - eapply V293_owned_task_fields_reconstruct; [exact FinalRecord | exact FinalFields].
  - split; [exact FinalBitmap | ]. split; assumption.
Qed.

(* Canonical enumeration is updated in place.  Framing the rest of the
   spatial list, rather than reconstructing records from loads, prevents
   duplication of permissions, including distinct records in one block. *)
Lemma V293_owned_task_list_update : forall entries t priority status message new R ge le M ir aux O op,
  TcbMod.is_orderset entries ->
  TcbMod.get' entries t = Some (priority,status,message) -> new < 13 ->
  (ge,le,M,ir,aux,O,op) |= V293_owned_task_list entries ** R ->
  (ge,le,V293_tcb_update_memory M (fst t) (Int.unsigned (snd t)) new,ir,aux,O,op) |=
    V293_owned_task_list (TcbMod.set' t (Int.repr (Z.of_nat new),status,message) entries) ** R.
Proof.
  induction entries as [ | [head [[hp hs] hm]] rest IH];
    intros t priority status message new R ge le M ir aux O op Order Lookup Range Owned;
    [discriminate | ].
  destruct Order as [Lower Order]. cbn [TcbMod.get'] in Lookup.
  cbn [TcbMod.set']. destruct (tidspec.blt t head) eqn:Before.
  - destruct (tidspec.beq t head) eqn:Same.
    + apply tidspec.beq_true_eq in Same. subst head.
      rewrite tidspec.blt_irrefl in Before. discriminate.
    + rewrite (@TcbMod.lb_notin rest t (@TcbMod.lb_trans rest t head Lower Before)) in Lookup.
      discriminate.
  - destruct (tidspec.beq t head) eqn:Same.
    + apply tidspec.beq_true_eq in Same. subst head. inversion Lookup; subst hp hs hm.
      cbn [V293_owned_task_list] in Owned |- *.
      apply astar_assoc_elim in Owned. apply astar_assoc_intro.
      exact (proj2 (V293_owned_task_record_update _ _ _ _ new _ _ _ _ _ _ _ _ Range Owned)).
    + cbn [V293_owned_task_list] in Owned |- *.
      apply astar_assoc_elim in Owned. apply astar_comm in Owned.
      apply astar_assoc_elim in Owned.
      specialize (IH t priority status message new (R ** V293_owned_task_record head hp hs hm)
        ge le M ir aux O op Order Lookup Range Owned).
      apply astar_assoc_intro in IH. apply astar_comm in IH. apply astar_assoc_intro in IH.
      exact IH.
Qed.

Theorem V293_owned_task_records_update : forall tasks t priority status message new R ge le M ir aux O op,
  get tasks t = Some (priority,status,message) -> new < 13 ->
  (ge,le,M,ir,aux,O,op) |= V293_owned_task_records tasks ** R ->
  (ge,le,V293_tcb_update_memory M (fst t) (Int.unsigned (snd t)) new,ir,aux,O,op) |=
    V293_owned_task_records (set tasks t (Int.repr (Z.of_nat new),status,message)) ** R.
Proof.
  intros tasks t priority status message new R ge le M ir aux O op Lookup Range Owned.
  unfold V293_owned_task_records in *.
  eapply V293_owned_task_list_update; [apply TcbMod.prf | exact Lookup | exact Range | exact Owned].
Qed.

Lemma V293_owned_task_list_select : forall entries t priority status message R s,
  In (t,(priority,status,message)) entries ->
  s |= V293_owned_task_list entries ** R ->
  s |= V293_owned_task_record t priority status message ** Atrue.
Proof.
  induction entries as [ | [head [[hp hs] hm]] rest IH];
    intros t priority status message R s Member Owned; [contradiction | ].
  cbn [V293_owned_task_list] in Owned. destruct Member as [Same | Member].
  - inversion Same; subst head hp hs hm. apply astar_assoc_elim in Owned.
    eapply astar_mono; [ | | exact Owned]; [intros ? H; exact H | intros; exact I].
  - apply astar_assoc_elim in Owned. apply astar_comm in Owned. apply astar_assoc_elim in Owned.
    eapply IH; eauto.
Qed.

Lemma V293_owned_task_list_local : forall entries ge le M ir aux O op,
  (ge,le,M,ir,aux,O,op) |= V293_owned_task_list entries ->
  O = emp /\
  (forall c i, (forall t value, In (t,value) entries -> c <> fst t) -> get M (c,i) = None) /\
  (forall ge' le' ir' aux' op', (ge',le',M,ir',aux',emp,op') |= V293_owned_task_list entries).
Proof.
  induction entries as [ | [t [[priority status] message]] rest IH];
    intros ge le M ir aux O op Owned.
  - destruct Owned as [EM EO]. change (M=emp) in EM. change (O=emp) in EO. subst M O.
    split; [reflexivity | ]. split; [intros; apply map_emp_get | ]. intros; split; reflexivity.
  - apply sat_split in Owned. destruct Owned as (mh & mt & oh & ot & JM & JO & Head & Tail).
    destruct (V293_owned_task_record_block_local _ _ _ _ _ _ _ _ _ _ _ Head) as [EH [SH RH]].
    destruct (IH _ _ _ _ _ _ _ Tail) as [ET [ST RT]]. subst oh ot.
    apply map_join_emp' in JO. subst O. split; [reflexivity | ]. split.
    + intros c i Apart. erewrite map_join_get_none; [ | exact JM | apply SH; apply Apart with (priority,status,message); left; reflexivity].
      apply ST. intros tt vv Member. apply Apart with vv. right; exact Member.
    + intros. apply sat_split'. exists mh. exists mt. exists (emp:osabst). exists (emp:osabst).
      split; [exact JM | ]. split; [apply map_join_emp | ]. split; [apply RH | apply RT].
Qed.

Lemma V293_task_list_member_lookup : forall entries t value,
  TcbMod.is_orderset entries -> In (t,value) entries -> TcbMod.get' entries t = Some value.
Proof.
  induction entries as [ | [head hv] rest IH]; intros t value Order Member; [contradiction | ].
  destruct Order as [Lower Order]. cbn [TcbMod.get'].
  destruct Member as [Same | Member].
  - inversion Same; subst head hv. rewrite TcbMod.beq_refl. reflexivity.
  - destruct (tidspec.beq t head) eqn:Same.
    + apply tidspec.beq_true_eq in Same. subst head.
      pose proof (IH _ _ Order Member) as Lookup.
      rewrite (@TcbMod.lb_notin rest t Lower) in Lookup. discriminate.
    + apply IH; assumption.
Qed.

Theorem V293_owned_task_records_block_frame : forall tasks R ge le M ir aux O op ge' le' Mf ir' aux' O' op',
  (ge,le,M,ir,aux,O,op) |= V293_owned_task_records tasks ** R ->
  (forall t value, get tasks t = Some value -> forall i, get Mf (fst t,i) = get M (fst t,i)) ->
  (ge',le',Mf,ir',aux',O',op') |= V293_owned_task_records tasks ** Atrue.
Proof.
  intros tasks R ge le M ir aux O op ge' le' Mf ir' aux' O' op' Owned Frame.
  apply sat_split in Owned. destruct Owned as (mr & mf & ore & ofr & JM & JO & Records & Rest).
  destruct (V293_owned_task_list_local _ _ _ _ _ _ _ _ Records) as [Empty [Support Rebase]]. subst ore.
  assert (Sub : Maps.sub mr Mf).
  { unfold addr in *. apply sub_semp; [reflexivity | ]. intros [c i].
    destruct (Classical_Prop.classic (exists t value, get tasks t = Some value /\ c = fst t)) as [[t [value [Member Same]]] | Apart].
    - subst c. rewrite (Frame t value Member i).
      destruct (get mr (fst t,i)) as [[permission byte] | ] eqn:Cell.
      + destruct (@sub_semp1 (block*offset) (bool*memval) mem memMap mr M (fst t,i)
          (permission,byte) eq_refl ltac:(exists mf; exact JM) Cell) as [Same | [Split Read]].
        * rewrite Same; destruct permission; reflexivity.
        * rewrite Split; destruct permission; cbn in *; try discriminate; reflexivity.
      + destruct (get M (fst t,i)); exact I.
    - rewrite Support.
      + destruct (get Mf (c,i)); exact I.
      + intros t value InList Same. apply Apart. exists t. exists value. split; [ | exact Same].
        (* Sorted canonical membership implies the actual map lookup. *)
        eapply V293_task_list_member_lookup; [apply TcbMod.prf | exact InList]. }
  destruct Sub as [remaining Joined]. apply sat_split'.
  exists mr. exists remaining. exists (emp:osabst). exists O'.
  split; [exact Joined | ]. split; [apply map_join_comm; apply map_join_emp | ]. split; [apply Rebase | exact I].
Qed.

Lemma V293_owned_tasks_fields_reconstruct : forall current tasks events now
    ge le M ir aux O op,
  (ge,le,M,ir,aux,O,op) |= V293_owned_task_records tasks ** Atrue ->
  (ge,le,M,ir,aux,O,op) |= V293_shared_fields current tasks events now ** Atrue ->
  (ge,le,M,ir,aux,O,op) |=
    (V293_owned_task_records tasks ** V293_shared_fields current tasks events now) ** Atrue.
Proof.
  intros current tasks events now ge le M ir aux O op HR HF.
  apply sat_split in HR. destruct HR as (mr & mrr & ore & orr & JMR & JOR & Record & _).
  destruct (V293_owned_task_list_local _ _ _ _ _ _ _ _ Record)
    as [Empty _]. subst ore.
  apply sat_split in HF. destruct HF as (mf & mrf & ofields & orest & JMF & JOF & Fields & _).
  pose proof (V293_shared_fields_empty_heap _ _ _ _ _ _ _ _ _ _ _ Fields) as EmptyM. subst mf.
  apply sat_split'. exists mr. exists mrr. exists ofields. exists orest.
  split; [exact JMR | ]. split; [exact JOF | ]. split; [ | exact I].
  apply sat_split'. exists mr. exists (emp:mem). exists (emp:osabst). exists ofields.
  split; [apply map_join_emp | ]. split; [apply map_join_comm; apply map_join_emp | ].
  split; assumption.
Qed.

(* All canonical task records, from the same execution and abstract update. *)
Theorem V293_critical_wait_all_records_owned_execution :
  forall P ks ge le caller M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp be ebase elo ehi xi bi ny nby nbx
    current reserved bcur bct curbase rb curprio
    running runblock run sched saved interrupt lock schednew high target schedcurrent counter f body next
    sc abstract_current tasks events now Os Of OO op R reason delay message,
  initial < 256 -> (initial < 12 \/ initial = 255) -> new < 12 ->
  let old := if initial =? 255 then curprio else initial in
  old < 13 -> lo < 256 -> hi < 256 -> br <> bg ->
  (0 <= base)%Z -> (base+55 <= Int.max_unsigned)%Z ->
  get le table = None -> get ge table = Some (b,Tarray (Tptr V293_tcb_type) 13) ->
  get le oldprio = Some (bo,Tint8) -> get le newprio = Some (bn,Tint8) ->
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  b <> bo -> b <> bn -> b <> bc -> b <> bt ->
  b <> dy -> b <> dby -> b <> dx -> b <> br -> b <> bg ->
  load Tint8 M (bo,0%Z) = Some (V293_byteval initial) ->
  load Tint8 M (bn,0%Z) = Some (V293_byteval new) ->
  V293_bytes_writable M b (4*Z.of_nat old)%Z 4 ->
  V293_bytes_writable M b (4*Z.of_nat new)%Z 4 ->
  length entries = 13 -> V293_table_loads V293_tcb_type M b entries ->
  get le yo = Some (dy,Tint8) -> get le byo = Some (dby,Tint8) -> get le xo = Some (dx,Tint8) ->
  get le rows = None -> get ge rows = Some (br,Tarray Tint8 2) ->
  get le group = None -> get ge group = Some (bg,Tint8) ->
  dy <> dby -> dy <> dx -> dby <> dx ->
  (forall c, c = dy \/ c = dby \/ c = dx -> c <> bc /\ c <> bt /\ c <> br /\ c <> bg) ->
  V293_tcb_old_loads M bt base (V293_prio_row old)
    (2 ^ V293_prio_row old) (2 ^ V293_prio_bit old) ->
  (exists v, get M (dy,0%Z) = Some (true,v)) ->
  (exists v, get M (dby,0%Z) = Some (true,v)) ->
  (exists v, get M (dx,0%Z) = Some (true,v)) ->
  V293_rekey_bitmap_loads M br bg lo hi (V293_ready_group lo hi) ->
  V293_rekey_bitmap_writable M br bg ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> b /\ c <> dy /\ c <> dby /\ c <> dx) ->
  get le pevent = Some (bp,Tptr V293_event_type) ->
  V293_bytes_writable M bp 0%Z 4 ->
  load (Tcom_ptr 411%Z) M (bt,(base+28)%Z) = Some (Vptr (be,Int.repr ebase)) ->
  bc <> br -> bc <> bg -> bt <> br -> bt <> bg ->
  bp <> b -> bp <> dy -> bp <> dby -> bp <> dx -> bp <> br -> bp <> bg ->
  bp <> be ->
  be <> b -> be <> dy -> be <> dby -> be <> dx -> be <> br -> be <> bg ->
  elo < 256 -> ehi < 256 -> (0 <= ebase)%Z -> (ebase+12 <= Int.max_unsigned)%Z ->
  V293_event_bitmap_loads M be ebase elo ehi (V293_ready_group elo ehi) ->
  V293_event_bitmap_writable M be ebase ->
  (forall x v c, In (x,v) (V293_rekey_ready_bindings yo yn xo xn byo byn old new) ->
    get le x = Some (c,Tint8) -> c <> bp /\ c <> be) ->
  bc <> bt -> bc <> bp -> bc <> be -> bt <> bp -> bt <> be ->
  get le xi = Some (bi,Tint8) ->
  (forall c, c = bn \/ c = bi ->
    c <> b /\ c <> dy /\ c <> dby /\ c <> dx /\ c <> br /\ c <> bg /\ c <> bp /\ c <> be /\ c <> bt) ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> bt) ->
  get le yn = Some (ny,Tint8) -> get le byn = Some (nby,Tint8) ->
  get le xn = Some (nbx,Tint8) ->
  ny <> bi -> ny <> nby -> ny <> nbx -> bi <> nby -> bi <> nbx -> nby <> nbx ->
  (forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->
    c <> b /\ c <> bo /\ c <> bn /\ c <> bc /\ c <> bt /\
    c <> dy /\ c <> dby /\ c <> dx /\ c <> br /\ c <> bg /\ c <> bp /\ c <> be) ->
  (forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->
    exists v, get M (c,0%Z) = Some (true,v)) ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat new)%Z) = Some Vnull ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat old)%Z) = Some (Vptr (bt,Int.repr base)) ->
  bo <> bn -> bc <> bn -> bc <> bo ->
  (initial = 255 ->
    get le current = None /\ get ge current = Some (bcur,Tptr V293_tcb_type) /\
    load (Tptr V293_tcb_type) M (bcur,0%Z) = Some (Vptr (bct,Int.repr curbase)) /\
    (0 <= curbase)%Z /\ (curbase+50 <= Int.max_unsigned)%Z /\
    load Tint8 M (bct,(curbase+50)%Z) = Some (V293_byteval curprio) /\
    (exists v, get M (bo,0%Z) = Some (true,v))) ->
  get le reserved = None -> get ge reserved = Some (rb,Tint8) ->
  (bt,Int.repr base) <> (rb,Int.zero) ->
  V293_bytes_writable M bc 0%Z 4 ->
  (forall c, In c [b;bn;bt;dy;dby;dx;br;bg;bp;be;ny;bi;nby;nbx] ->
    c <> bo /\ c <> bc) ->
  run < 256 -> get le running = None -> get ge running = Some (runblock,Tint8) ->
  load Tint8 M (runblock,0%Z) = Some (V293_byteval run) ->
  (run = 1 ->
    P sched = Some (V293_OSSched_success_function saved interrupt lock schednew table high target schedcurrent counter) /\
    saved <> interrupt /\ saved <> lock /\ V293_success_sched_blocked ge M interrupt lock) ->
  V293_success_globals_away ge [running;interrupt;lock] [bo;bc;b;dy;dby;dx;br;bg;bp;bt;ny;bi;nby;nbx;be] ->
  callcont ks = Some (kcall f body caller next) ->
  NoDup (map fst (getaddr le)) ->
  (forall c t, In (c,t) (getaddr le) -> V293_bytes_writable M c 0%Z (typelen t)) ->
  (forall c, In c [b;bt;br;bg;be] -> ~ In c (map fst (getaddr le))) ->
  V293_priority_table entries tasks -> V293_bitmap_tasks lo hi tasks ->
  V293_event_wait_tasks elo ehi tasks reason ->
  (reason = os_stat_sem (be,Int.repr ebase) \/ reason = os_stat_q (be,Int.repr ebase) \/
    reason = os_stat_mbox (be,Int.repr ebase) \/ reason = os_stat_mutexsem (be,Int.repr ebase)) ->
  get tasks (bt,Int.repr base) = Some (Int.repr (Z.of_nat old),wait reason delay,message) ->
  (ge,le,M,ir,(enabled,si,ci),Os,op) |=
    V293_shared_fields abstract_current tasks events now **
      (V293_owned_task_records tasks ** R) ->
  join Os Of OO ->
  (forall t value, get tasks t = Some value -> fst t <> bt ->
    ~ In (fst t) (map fst (getaddr le)) /\
    ~ In (fst t) [bo;bc;b;dy;dby;dx;br;bg;bp;be;ny;bi;nby;nbx]) ->
  exists Mf Os' OO',
  let old := if initial =? 255 then curprio else initial in
  Os' = set Os abstcblsid (abstcblist
    (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message))) /\
  join Os' Of OO' /\
  spec_step sc (spec_prim nil (V293_wait_prio_step (bt,Int.repr base) old new)) OO
    (spec_done (Some (Vint32 Int.zero))) OO' /\
  (let old := if initial =? 255 then curprio else initial in
  let fr := V293_ready_branch_rows lo hi old new in
  V293_local_steps P
    (curs (sseq (V293_primitive_success_update table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent xi current reserved)
      (V293_task_prio_success_tail running sched)),(kenil,ks))
    ((ge,le,M),ir,(enabled,si,ci))
    (curs (sskip (Some (Vint32 Int.zero))),(kenil,next))
    ((ge,caller,Mf),ir,(enabled,si,ci)) /\
  V293_tcb_updated_loads Mf bt base new /\
  V293_rekey_bitmap_loads Mf br bg (fst fr) (snd fr) (V293_ready_group (fst fr) (snd fr)) /\
  V293_table_loads V293_tcb_type Mf b
    (update_nth_val new (update_nth_val old entries Vnull) (Vptr (bt,Int.repr base))) /\
  (let er := V293_ready_rekey_rows elo ehi old new in
    V293_event_bitmap_loads Mf be ebase (fst er) (snd er) (V293_ready_group (fst er) (snd er))) /\
  load (Tcom_ptr 411%Z) Mf (bt,(base+28)%Z) = Some (Vptr (be,Int.repr ebase)) /\
  (forall c i, ~ In c (map fst (getaddr le)) -> ~ In c [bo;bc;b;dy;dby;dx;br;bg;bp;be;bt;ny;bi;nby;nbx] ->
    get Mf (c,i) = get M (c,i)) /\
  (forall c t k, In (c,t) (getaddr le) -> k < typelen t ->
    get Mf (c,Z.of_nat k) = None) /\
  (forall i, (i < base+50 \/ base+54 < i)%Z -> get Mf (bt,i) = get M (bt,i)) /\
  (forall i, (i < ebase+10 \/ ebase+12 < i)%Z -> get Mf (be,i) = get M (be,i)) /\
  (forall i, get Mf (bt,i) = get (V293_tcb_update_memory M bt base new) (bt,i))) /\
  (ge,caller,Mf,ir,(enabled,si,ci),OO',op) |=
    (V293_owned_task_records
      (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) **
      V293_shared_fields abstract_current
        (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) events now) ** Atrue /\
  V293_bitmap_tasks lo hi (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) /\
  V293_priority_table
    (update_nth_val new (update_nth_val old entries Vnull) (Vptr (bt,Int.repr base)))
    (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) /\
  (let er := V293_ready_rekey_rows elo ehi old new in
    V293_event_wait_tasks (fst er) (snd er)
      (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) reason).
Proof.
  intros P ks ge le caller M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp be ebase elo ehi xi bi ny nby nbx current reserved bcur bct curbase rb curprio running runblock run sched saved interrupt lock schednew high target schedcurrent counter f body next
    sc abstract_current tasks events now Os Of OO op R reason delay message
    Input Valid N old O L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg Lo Ln Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields Wy Wby Wx Loads W NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg PE Eb Ey Eby Ex Er Eg EL EH EB ELimit ELoads EW LocalApart CT CP CE TP TE Bi ExtraApart NewTcbApart NBy NBby NBx NYI NYBY NYBX NIBY NIBX NBYBX CoordApart CoordW Empty Slot Onew Cnew CO Self Nreserved Greserved Token CW EntryApart
    RunRange NoRun GlobalRun LoadRun WhenRunning Away Call ND InitialWritable HeapApart
    TaskTable Bitmap EventBitmap Reason Task Owned Frame OtherTaskFrame.
  assert (AllEntry : (ge,le,M,ir,(enabled,si,ci),Os,op) |=
    V293_owned_task_records tasks ** (R ** V293_shared_fields abstract_current tasks events now)).
  { pose proof Owned as HAll. apply astar_comm in HAll. apply astar_assoc_elim in HAll. exact HAll. }
  assert (Selected : (ge,le,M,ir,(enabled,si,ci),Os,op) |=
    V293_owned_task_record (bt,Int.repr base) (Int.repr (Z.of_nat old)) (wait reason delay) message ** Atrue).
  { eapply V293_owned_task_list_select; [apply V293_task_lookup_list; exact Task | exact AllEntry]. }
  assert (EntryFields : (ge,le,M,ir,(enabled,si,ci),Os,op) |=
    V293_shared_fields abstract_current tasks events now ** Atrue).
  { eapply astar_mono; [intros ? Held; exact Held | intros; exact I | exact Owned]. }
  pose proof (V293_owned_task_fields_reconstruct _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Selected EntryFields) as EntryJoint.
  assert (EntrySelected : (ge,le,M,ir,(enabled,si,ci),Os,op) |=
    V293_shared_fields abstract_current tasks events now **
      (V293_owned_task_record (bt,Int.repr base) (Int.repr (Z.of_nat old)) (wait reason delay) message ** Atrue)).
  { apply astar_assoc_elim. eapply astar_mono;
      [intros ? Held; apply astar_comm; exact Held | intros ? Held; exact Held | exact EntryJoint]. }
  destruct (V293_critical_wait_record_owned_execution P ks ge le caller M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp be ebase elo ehi xi bi ny nby nbx current reserved bcur bct curbase rb curprio running runblock run sched saved interrupt lock schednew high target schedcurrent counter f body next sc abstract_current tasks events now Os Of OO op Atrue reason delay message
    Input Valid N  O L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg Lo Ln Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields Wy Wby Wx Loads W NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg PE Eb Ey Eby Ex Er Eg EL EH EB ELimit ELoads EW LocalApart CT CP CE TP TE Bi ExtraApart NewTcbApart NBy NBby NBx NYI NYBY NYBX NIBY NIBX NBYBX CoordApart CoordW Empty Slot Onew Cnew CO Self Nreserved Greserved Token CW EntryApart
    RunRange NoRun GlobalRun LoadRun WhenRunning Away Call ND InitialWritable HeapApart TaskTable Bitmap EventBitmap Reason Task EntrySelected Frame)
    as (Mf & Os' & OO' & Identity & AbstractFrame & Abstract & Physical & FinalSelected & FinalBitmap & FinalTable & FinalEvent).
  pose proof (V293_owned_task_records_update _ _ _ _ _ new _ _ _ _ _ _ _ _
    Task ltac:(clear -N; lia) AllEntry) as ModelAll.
  cbn [fst snd] in ModelAll. rewrite Int.unsigned_repr in ModelAll by lia.
  pose proof Physical as Observations. cbn zeta in Observations. fold old in Observations.
  destruct Observations as (Exec & Updated & Ready & Table & EventReady & Pointer
    & Outside & Removed & TcbFrame & EventFrame & ExactBlock).
  assert (FinalAll : (ge,caller,Mf,ir,(enabled,si,ci),OO',op) |=
    V293_owned_task_records
      (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) ** Atrue).
  { eapply V293_owned_task_records_block_frame; [exact ModelAll | ].
    intros t value Member i. destruct (Pos.eq_dec (fst t) bt) as [Same | Different].
    - rewrite Same. exact (ExactBlock i).
    - rewrite map_get_set' in Member by (intro Equal; subst t; cbn in Different; contradiction).
      destruct (OtherTaskFrame t value Member Different) as [NotLocal NotWritten].
      rewrite Outside.
      + unfold V293_tcb_update_memory. repeat rewrite V293_put_byte_other by
          (intro Equal; inversion Equal; congruence). reflexivity.
      + exact NotLocal.
      + cbn [In] in NotWritten |- *. intuition congruence. }
  assert (FinalFields : (ge,caller,Mf,ir,(enabled,si,ci),OO',op) |=
    V293_shared_fields abstract_current
      (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) events now ** Atrue).
  { apply astar_assoc_elim in FinalSelected. apply astar_comm in FinalSelected.
    apply astar_assoc_elim in FinalSelected.
    eapply astar_mono; [intros ? Held; exact Held | intros; exact I | exact FinalSelected]. }
  exists Mf. exists Os'. exists OO'. cbn zeta. fold old.
  split; [exact Identity | ]. split; [exact AbstractFrame | ]. split; [exact Abstract | ].
  split; [exact Physical | ]. split.
  - eapply V293_owned_tasks_fields_reconstruct; [exact FinalAll | exact FinalFields].
  - split; [exact FinalBitmap | ]. split; assumption.
Qed.

(* Keep the current-pointer and task fragments together: two independent
   weakened ownership postconditions do not justify a separating conjunction. *)
Lemma V293_current_fragment_local : forall current ge le M ir aux O op,
  (ge,le,M,ir,aux,O,op) |= CurTid current ->
  exists b tp, get ge OSTCBCur = Some (b,Tptr tp) /\ O = emp /\
    (forall c i, c <> b -> get M (c,i) = None) /\
    (forall le' ir' aux' op', (ge,le',M,ir',aux',emp,op') |= CurTid current).
Proof.
  intros current ge le M ir aux O op [tp Current]. unfold Agvarmapsto in Current.
  destruct Current as [b Current]. apply sat_split in Current.
  destruct Current as (me & mp & oe & oa & JM & JO & Env & Pointer).
  destruct Env as (bound & Binding & Address & EmptyM & EmptyO).
  cbn in Address, EmptyM, EmptyO, Binding. inversion Address; subst bound.
  change (me = emp) in EmptyM. change (oe = emp) in EmptyO. subst me oe.
  destruct Pointer as [Pointer EmptyA]. change (oa = emp) in EmptyA. subst oa.
  apply map_join_comm in JM. apply map_join_emp' in JM. subst M.
  apply map_join_comm in JO. apply map_join_emp' in JO. subst O.
  exists b. exists tp. split; [exact Binding | ]. split; [reflexivity | ]. split.
  - destruct Pointer as (bytes & Encoding & Cells). intros c i Apart.
    eapply V293_ptomvallist_other_block; eauto.
  - intros. exists tp. unfold Agvarmapsto. exists b.
    apply sat_split'. exists (emp:mem). exists mp. exists (emp:osabst). exists (emp:osabst).
    split; [apply map_join_comm; apply map_join_emp | ]. split; [apply map_join_emp | ].
    split; [exists b; repeat split; assumption || reflexivity | ]. split; [exact Pointer | reflexivity].
Qed.

Theorem V293_current_task_records_block_frame : forall current tasks R ge le M ir aux O op
    le' Mf ir' aux' O' op',
  (ge,le,M,ir,aux,O,op) |= (CurTid current ** V293_owned_task_records tasks) ** R ->
  (forall b tp, get ge OSTCBCur = Some (b,Tptr tp) ->
    forall i, get Mf (b,i) = get M (b,i)) ->
  (forall t value, get tasks t = Some value ->
    forall i, get Mf (fst t,i) = get M (fst t,i)) ->
  (ge,le',Mf,ir',aux',O',op') |= (CurTid current ** V293_owned_task_records tasks) ** Atrue.
Proof.
  intros current tasks R ge le M ir aux O op le' Mf ir' aux' O' op' Owned CF TF.
  apply sat_split in Owned. destruct Owned as (mh & rest & oh & ore & JM & JO & Held & Rest).
  apply sat_split in Held. destruct Held as (mc & mt & oc & ot & JMT & JOT & Current & Tasks).
  destruct (V293_current_fragment_local _ _ _ _ _ _ _ _ Current)
    as (b & tp & Binding & EC & SC & RC).
  destruct (V293_owned_task_list_local _ _ _ _ _ _ _ _ Tasks) as [ET [ST RT]].
  subst oc ot. apply map_join_emp' in JOT. subst oh.
  assert (Support : forall c i, c <> b ->
    (forall t value, get tasks t = Some value -> c <> fst t) -> get mh (c,i) = None).
  { intros c i NC NT. erewrite map_join_get_none; [ | exact JMT | apply SC; exact NC].
    apply ST. intros t value Member. apply NT with value.
    eapply V293_task_list_member_lookup; [apply TcbMod.prf | exact Member]. }
  assert (Exact : forall c i, get mh (c,i) <> None -> get Mf (c,i) = get M (c,i)).
  { intros c i Occupied. destruct (Pos.eq_dec c b) as [Same | Apart].
    - subst c. apply CF with tp; exact Binding.
    - destruct (Classical_Prop.classic (exists t value, get tasks t = Some value /\ c = fst t))
        as [[t [value [Member Same]]] | Away].
      + subst c. apply TF with value; exact Member.
      + exfalso. apply Occupied. apply Support; [exact Apart | ].
        intros t value Member Same. apply Away. exists t. exists value. split; assumption. }
  assert (Sub : Maps.sub mh Mf).
  { unfold addr in *. apply sub_semp; [reflexivity | ]. intros [c i].
    destruct (get mh (c,i)) as [[permission byte] | ] eqn:Cell.
    - rewrite Exact by (rewrite Cell; discriminate).
      destruct (@sub_semp1 (block*offset) (bool*memval) mem memMap mh M (c,i)
        (permission,byte) eq_refl ltac:(exists rest; exact JM) Cell) as [Same | [Split Read]].
      + rewrite Same. destruct permission; reflexivity.
      + rewrite Split. destruct permission; cbn in *; try discriminate; reflexivity.
    - destruct (get Mf (c,i)); exact I. }
  destruct Sub as [remaining Joined]. apply sat_split'.
  exists mh. exists remaining. exists (emp:osabst). exists O'.
  split; [exact Joined | ]. split; [apply map_join_comm; apply map_join_emp | ]. split; [ | exact I].
  apply sat_split'. exists mc. exists mt. exists (emp:osabst). exists (emp:osabst).
  split; [exact JMT | ]. split; [apply map_join_emp | ]. split; [apply RC | apply RT].
Qed.

Lemma V293_current_tasks_fields_reconstruct : forall current tasks events now ge le M ir aux O op,
  (ge,le,M,ir,aux,O,op) |= (CurTid current ** V293_owned_task_records tasks) ** Atrue ->
  (ge,le,M,ir,aux,O,op) |= V293_shared_fields current tasks events now ** Atrue ->
  (ge,le,M,ir,aux,O,op) |=
    ((CurTid current ** V293_owned_task_records tasks) ** V293_shared_fields current tasks events now) ** Atrue.
Proof.
  intros current tasks events now ge le M ir aux O op HP HF.
  apply sat_split in HP. destruct HP as (mp & mr & opair & orest & JMP & JOP & Pair & _).
  assert (Empty : opair = emp).
  { apply sat_split in Pair. destruct Pair as (mc & mt & oc & ot & JM & JO & Current & Tasks).
    destruct (V293_current_fragment_local _ _ _ _ _ _ _ _ Current) as (b & tp & B & EC & _).
    destruct (V293_owned_task_list_local _ _ _ _ _ _ _ _ Tasks) as [ET _].
    subst oc ot. apply map_join_emp' in JO. symmetry; exact JO. }
  subst opair. apply sat_split in HF. destruct HF as (mf & mrf & ofields & ofrest & JMF & JOF & Fields & _).
  pose proof (V293_shared_fields_empty_heap _ _ _ _ _ _ _ _ _ _ _ Fields) as EM. subst mf.
  apply sat_split'. exists mp. exists mr. exists ofields. exists ofrest.
  split; [exact JMP | ]. split; [exact JOF | ]. split; [ | exact I].
  apply sat_split'. exists mp. exists (emp:mem). exists (emp:osabst). exists ofields.
  split; [apply map_join_emp | ]. split; [apply map_join_comm; apply map_join_emp | ]. split; assumption.
Qed.

Require Import CertiOS.tactics.sepauto.seplog_tactics.
Theorem V293_critical_wait_current_all_owned_execution :
  forall P ks ge le caller M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp be ebase elo ehi xi bi ny nby nbx
    current reserved bcur bct curbase rb curprio
    running runblock run sched saved interrupt lock schednew high target schedcurrent counter f body next
    sc abstract_current tasks events now Os Of OO op R reason delay message,
  initial < 256 -> (initial < 12 \/ initial = 255) -> new < 12 ->
  let old := if initial =? 255 then curprio else initial in
  old < 13 -> lo < 256 -> hi < 256 -> br <> bg ->
  (0 <= base)%Z -> (base+55 <= Int.max_unsigned)%Z ->
  get le table = None -> get ge table = Some (b,Tarray (Tptr V293_tcb_type) 13) ->
  get le oldprio = Some (bo,Tint8) -> get le newprio = Some (bn,Tint8) ->
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  b <> bo -> b <> bn -> b <> bc -> b <> bt ->
  b <> dy -> b <> dby -> b <> dx -> b <> br -> b <> bg ->
  load Tint8 M (bo,0%Z) = Some (V293_byteval initial) ->
  load Tint8 M (bn,0%Z) = Some (V293_byteval new) ->
  V293_bytes_writable M b (4*Z.of_nat old)%Z 4 ->
  V293_bytes_writable M b (4*Z.of_nat new)%Z 4 ->
  length entries = 13 -> V293_table_loads V293_tcb_type M b entries ->
  get le yo = Some (dy,Tint8) -> get le byo = Some (dby,Tint8) -> get le xo = Some (dx,Tint8) ->
  get le rows = None -> get ge rows = Some (br,Tarray Tint8 2) ->
  get le group = None -> get ge group = Some (bg,Tint8) ->
  dy <> dby -> dy <> dx -> dby <> dx ->
  (forall c, c = dy \/ c = dby \/ c = dx -> c <> bc /\ c <> bt /\ c <> br /\ c <> bg) ->
  V293_tcb_old_loads M bt base (V293_prio_row old)
    (2 ^ V293_prio_row old) (2 ^ V293_prio_bit old) ->
  (exists v, get M (dy,0%Z) = Some (true,v)) ->
  (exists v, get M (dby,0%Z) = Some (true,v)) ->
  (exists v, get M (dx,0%Z) = Some (true,v)) ->
  V293_rekey_bitmap_loads M br bg lo hi (V293_ready_group lo hi) ->
  V293_rekey_bitmap_writable M br bg ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> b /\ c <> dy /\ c <> dby /\ c <> dx) ->
  get le pevent = Some (bp,Tptr V293_event_type) ->
  V293_bytes_writable M bp 0%Z 4 ->
  load (Tcom_ptr 411%Z) M (bt,(base+28)%Z) = Some (Vptr (be,Int.repr ebase)) ->
  bc <> br -> bc <> bg -> bt <> br -> bt <> bg ->
  bp <> b -> bp <> dy -> bp <> dby -> bp <> dx -> bp <> br -> bp <> bg ->
  bp <> be ->
  be <> b -> be <> dy -> be <> dby -> be <> dx -> be <> br -> be <> bg ->
  elo < 256 -> ehi < 256 -> (0 <= ebase)%Z -> (ebase+12 <= Int.max_unsigned)%Z ->
  V293_event_bitmap_loads M be ebase elo ehi (V293_ready_group elo ehi) ->
  V293_event_bitmap_writable M be ebase ->
  (forall x v c, In (x,v) (V293_rekey_ready_bindings yo yn xo xn byo byn old new) ->
    get le x = Some (c,Tint8) -> c <> bp /\ c <> be) ->
  bc <> bt -> bc <> bp -> bc <> be -> bt <> bp -> bt <> be ->
  get le xi = Some (bi,Tint8) ->
  (forall c, c = bn \/ c = bi ->
    c <> b /\ c <> dy /\ c <> dby /\ c <> dx /\ c <> br /\ c <> bg /\ c <> bp /\ c <> be /\ c <> bt) ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> bt) ->
  get le yn = Some (ny,Tint8) -> get le byn = Some (nby,Tint8) ->
  get le xn = Some (nbx,Tint8) ->
  ny <> bi -> ny <> nby -> ny <> nbx -> bi <> nby -> bi <> nbx -> nby <> nbx ->
  (forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->
    c <> b /\ c <> bo /\ c <> bn /\ c <> bc /\ c <> bt /\
    c <> dy /\ c <> dby /\ c <> dx /\ c <> br /\ c <> bg /\ c <> bp /\ c <> be) ->
  (forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->
    exists v, get M (c,0%Z) = Some (true,v)) ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat new)%Z) = Some Vnull ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat old)%Z) = Some (Vptr (bt,Int.repr base)) ->
  bo <> bn -> bc <> bn -> bc <> bo ->
  (initial = 255 ->
    get le current = None /\ get ge current = Some (bcur,Tptr V293_tcb_type) /\
    load (Tptr V293_tcb_type) M (bcur,0%Z) = Some (Vptr (bct,Int.repr curbase)) /\
    (0 <= curbase)%Z /\ (curbase+50 <= Int.max_unsigned)%Z /\
    load Tint8 M (bct,(curbase+50)%Z) = Some (V293_byteval curprio) /\
    (exists v, get M (bo,0%Z) = Some (true,v))) ->
  get le reserved = None -> get ge reserved = Some (rb,Tint8) ->
  (bt,Int.repr base) <> (rb,Int.zero) ->
  V293_bytes_writable M bc 0%Z 4 ->
  (forall c, In c [b;bn;bt;dy;dby;dx;br;bg;bp;be;ny;bi;nby;nbx] ->
    c <> bo /\ c <> bc) ->
  run < 256 -> get le running = None -> get ge running = Some (runblock,Tint8) ->
  load Tint8 M (runblock,0%Z) = Some (V293_byteval run) ->
  (run = 1 ->
    P sched = Some (V293_OSSched_success_function saved interrupt lock schednew table high target schedcurrent counter) /\
    saved <> interrupt /\ saved <> lock /\ V293_success_sched_blocked ge M interrupt lock) ->
  V293_success_globals_away ge [running;interrupt;lock] [bo;bc;b;dy;dby;dx;br;bg;bp;bt;ny;bi;nby;nbx;be] ->
  callcont ks = Some (kcall f body caller next) ->
  NoDup (map fst (getaddr le)) ->
  (forall c t, In (c,t) (getaddr le) -> V293_bytes_writable M c 0%Z (typelen t)) ->
  (forall c, In c [b;bt;br;bg;be] -> ~ In c (map fst (getaddr le))) ->
  V293_priority_table entries tasks -> V293_bitmap_tasks lo hi tasks ->
  V293_event_wait_tasks elo ehi tasks reason ->
  (reason = os_stat_sem (be,Int.repr ebase) \/ reason = os_stat_q (be,Int.repr ebase) \/
    reason = os_stat_mbox (be,Int.repr ebase) \/ reason = os_stat_mutexsem (be,Int.repr ebase)) ->
  get tasks (bt,Int.repr base) = Some (Int.repr (Z.of_nat old),wait reason delay,message) ->
  (ge,le,M,ir,(enabled,si,ci),Os,op) |=
    V293_shared_fields abstract_current tasks events now **
      ((CurTid abstract_current ** V293_owned_task_records tasks) ** R) ->
  join Os Of OO ->
  (forall t value, get tasks t = Some value -> fst t <> bt ->
    ~ In (fst t) (map fst (getaddr le)) /\
    ~ In (fst t) [bo;bc;b;dy;dby;dx;br;bg;bp;be;ny;bi;nby;nbx]) ->
  (forall pointer_block tp, get ge OSTCBCur = Some (pointer_block,Tptr tp) -> pointer_block <> bt ->
    ~ In pointer_block (map fst (getaddr le)) /\
    ~ In pointer_block [bo;bc;b;dy;dby;dx;br;bg;bp;be;ny;bi;nby;nbx]) ->
  exists Mf Os' OO',
  let old := if initial =? 255 then curprio else initial in
  Os' = set Os abstcblsid (abstcblist
    (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message))) /\
  join Os' Of OO' /\
  spec_step sc (spec_prim nil (V293_wait_prio_step (bt,Int.repr base) old new)) OO
    (spec_done (Some (Vint32 Int.zero))) OO' /\
  (let old := if initial =? 255 then curprio else initial in
  let fr := V293_ready_branch_rows lo hi old new in
  V293_local_steps P
    (curs (sseq (V293_primitive_success_update table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent xi current reserved)
      (V293_task_prio_success_tail running sched)),(kenil,ks))
    ((ge,le,M),ir,(enabled,si,ci))
    (curs (sskip (Some (Vint32 Int.zero))),(kenil,next))
    ((ge,caller,Mf),ir,(enabled,si,ci)) /\
  V293_tcb_updated_loads Mf bt base new /\
  V293_rekey_bitmap_loads Mf br bg (fst fr) (snd fr) (V293_ready_group (fst fr) (snd fr)) /\
  V293_table_loads V293_tcb_type Mf b
    (update_nth_val new (update_nth_val old entries Vnull) (Vptr (bt,Int.repr base))) /\
  (let er := V293_ready_rekey_rows elo ehi old new in
    V293_event_bitmap_loads Mf be ebase (fst er) (snd er) (V293_ready_group (fst er) (snd er))) /\
  load (Tcom_ptr 411%Z) Mf (bt,(base+28)%Z) = Some (Vptr (be,Int.repr ebase)) /\
  (forall c i, ~ In c (map fst (getaddr le)) -> ~ In c [bo;bc;b;dy;dby;dx;br;bg;bp;be;bt;ny;bi;nby;nbx] ->
    get Mf (c,i) = get M (c,i)) /\
  (forall c t k, In (c,t) (getaddr le) -> k < typelen t ->
    get Mf (c,Z.of_nat k) = None) /\
  (forall i, (i < base+50 \/ base+54 < i)%Z -> get Mf (bt,i) = get M (bt,i)) /\
  (forall i, (i < ebase+10 \/ ebase+12 < i)%Z -> get Mf (be,i) = get M (be,i)) /\
  (forall i, get Mf (bt,i) = get (V293_tcb_update_memory M bt base new) (bt,i))) /\
  (ge,caller,Mf,ir,(enabled,si,ci),OO',op) |=
    ((CurTid abstract_current ** V293_owned_task_records
      (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message))) **
      V293_shared_fields abstract_current
        (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) events now) ** Atrue /\
  V293_bitmap_tasks lo hi (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) /\
  V293_priority_table
    (update_nth_val new (update_nth_val old entries Vnull) (Vptr (bt,Int.repr base)))
    (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) /\
  (let er := V293_ready_rekey_rows elo ehi old new in
    V293_event_wait_tasks (fst er) (snd er)
      (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) reason).
Proof.
  intros P ks ge le caller M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp be ebase elo ehi xi bi ny nby nbx current reserved bcur bct curbase rb curprio running runblock run sched saved interrupt lock schednew high target schedcurrent counter f body next
    sc abstract_current tasks events now Os Of OO op R reason delay message
    Input Valid N old O L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg Lo Ln Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields Wy Wby Wx Loads W NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg PE Eb Ey Eby Ex Er Eg EL EH EB ELimit ELoads EW LocalApart CT CP CE TP TE Bi ExtraApart NewTcbApart NBy NBby NBx NYI NYBY NYBX NIBY NIBX NBYBX CoordApart CoordW Empty Slot Onew Cnew CO Self Nreserved Greserved Token CW EntryApart
    RunRange NoRun GlobalRun LoadRun WhenRunning Away Call ND InitialWritable HeapApart
    TaskTable Bitmap EventBitmap Reason Task Owned Frame OtherTaskFrame CurrentSafety.
  assert (EntryOld : (ge,le,M,ir,(enabled,si,ci),Os,op) |=
    V293_shared_fields abstract_current tasks events now **
      (V293_owned_task_records tasks ** (CurTid abstract_current ** R))) by (clear -Owned; sep auto).
  assert (AllEntry : (ge,le,M,ir,(enabled,si,ci),Os,op) |=
    V293_owned_task_records tasks ** (CurTid abstract_current ** (R ** V293_shared_fields abstract_current tasks events now))) by (clear -Owned; sep auto).
  destruct (V293_critical_wait_all_records_owned_execution P ks ge le caller M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp be ebase elo ehi xi bi ny nby nbx current reserved bcur bct curbase rb curprio running runblock run sched saved interrupt lock schednew high target schedcurrent counter f body next sc abstract_current tasks events now Os Of OO op (CurTid abstract_current ** R) reason delay message
    Input Valid N  O L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg Lo Ln Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields Wy Wby Wx Loads W NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg PE Eb Ey Eby Ex Er Eg EL EH EB ELimit ELoads EW LocalApart CT CP CE TP TE Bi ExtraApart NewTcbApart NBy NBby NBx NYI NYBY NYBX NIBY NIBX NBYBX CoordApart CoordW Empty Slot Onew Cnew CO Self Nreserved Greserved Token CW EntryApart
    RunRange NoRun GlobalRun LoadRun WhenRunning Away Call ND InitialWritable HeapApart TaskTable Bitmap EventBitmap Reason Task EntryOld Frame OtherTaskFrame)
    as (Mf & Os' & OO' & Identity & AbstractFrame & Abstract & Physical & FinalAllOld & FinalBitmap & FinalTable & FinalEvent).
  pose proof (V293_owned_task_records_update _ _ _ _ _ new _ _ _ _ _ _ _ _
    Task ltac:(clear -N; lia) AllEntry) as ModelAll.
  cbn [fst snd] in ModelAll. rewrite Int.unsigned_repr in ModelAll by lia.
  assert (ModelPair : (ge,le,V293_tcb_update_memory M bt base new,ir,(enabled,si,ci),Os,op) |=
    (CurTid abstract_current ** V293_owned_task_records
      (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message))) **
      (R ** V293_shared_fields abstract_current tasks events now)) by (clear -ModelAll; sep auto).
  pose proof Physical as Observations. cbn zeta in Observations. fold old in Observations.
  destruct Observations as (Exec & Updated & Ready & Table & EventReady & Pointer
    & Outside & Removed & TcbFrame & EventFrame & ExactBlock).
  assert (FinalPair : (ge,caller,Mf,ir,(enabled,si,ci),OO',op) |=
    (CurTid abstract_current ** V293_owned_task_records
      (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message))) ** Atrue).
  { eapply V293_current_task_records_block_frame; [exact ModelPair | | ].
    - intros pointer_block tp Binding i.
      destruct (Pos.eq_dec pointer_block bt) as [Same | Different].
      + subst pointer_block. exact (ExactBlock i).
      + destruct (CurrentSafety pointer_block tp Binding Different) as [NotLocal NotWritten].
        rewrite Outside.
        * unfold V293_tcb_update_memory. repeat rewrite V293_put_byte_other by
            (intro Equal; inversion Equal; congruence). reflexivity.
        * exact NotLocal.
        * clear -NotWritten Different. cbn [In] in NotWritten |- *. intuition congruence.
    - intros t value Member i. destruct (Pos.eq_dec (fst t) bt) as [Same | Different].
      + rewrite Same. exact (ExactBlock i).
      + rewrite map_get_set' in Member by (intro Equal; subst t; cbn in Different; contradiction).
        destruct (OtherTaskFrame t value Member Different) as [NotLocal NotWritten].
        rewrite Outside.
        * unfold V293_tcb_update_memory. repeat rewrite V293_put_byte_other by
            (intro Equal; inversion Equal; congruence). reflexivity.
        * exact NotLocal.
        * clear -NotWritten Different. cbn [In] in NotWritten |- *. intuition congruence. }
  assert (FinalFields : (ge,caller,Mf,ir,(enabled,si,ci),OO',op) |=
    V293_shared_fields abstract_current
      (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) events now ** Atrue).
  { apply astar_assoc_elim in FinalAllOld. apply astar_comm in FinalAllOld.
    apply astar_assoc_elim in FinalAllOld.
    eapply astar_mono; [intros ? Held; exact Held | intros; exact I | exact FinalAllOld]. }
  exists Mf. exists Os'. exists OO'. cbn zeta. fold old.
  split; [exact Identity | ]. split; [exact AbstractFrame | ]. split; [exact Abstract | ].
  split; [exact Physical | ]. split.
  - eapply V293_current_tasks_fields_reconstruct; [exact FinalPair | exact FinalFields].
  - split; [exact FinalBitmap | ]. split; assumption.
Qed.

(* A typed read identifies the byte value, but only the independent full
   permission premise can justify constructing a writable spatial cell. *)
Lemma V293_full_byte_load_encoding : forall M a n raw,
  get M a = Some (true,raw) ->
  load Tint8 M a = Some (V293_byteval n) ->
  get M a = Some (true,Byte (Byte.repr (Int.unsigned (Int.repr (Z.of_nat n))))).
Proof.
  intros M [b i] n raw Full Read.
  unfold load, loadm in Read. cbn [typelen loadbytes] in Read.
  unfold addr, offset in *. rewrite Full in Read.
  destruct raw as [ | byte | pb off k | ];
    cbn [decode_val proj_bytes decode_int] in Read; try discriminate.
  injection Read as Value.
  assert (Decode : Int.unsigned (Int.zero_ext 8 (Int.repr (Byte.unsigned byte + 0))) = Byte.unsigned byte).
  { rewrite Int.zero_ext_mod by (unfold Int.zwordsize, Int.wordsize; simpl; lia).
    rewrite Z.add_0_r. rewrite Int.unsigned_repr.
    - apply Z.mod_small. pose proof (Byte.unsigned_range byte).
      change (0 <= Byte.unsigned byte < 256)%Z in H. exact H.
    - pose proof (Byte.unsigned_range byte).
      change (0 <= Byte.unsigned byte < 256)%Z in H.
      change (0 <= Byte.unsigned byte <= 4294967295)%Z. lia. }
  change (Int.unsigned (Int.zero_ext 8 (Int.repr (Byte.unsigned byte + 0))) =
    Int.unsigned (Int.repr (Z.of_nat n))) in Value.
  rewrite Full. rewrite <- Value, Decode, Byte.repr_unsigned. reflexivity.
Qed.

Lemma V293_full_byte_cell_owned : forall M a n raw,
  n < 256 ->
  get M a = Some (true,raw) ->
  load Tint8 M a = Some (V293_byteval n) ->
  forall ge le ir aux O op,
  (ge,le,M,ir,aux,O,op) |= V293_owned_record_cell (a,Tint8,V293_byteval n) ** Atrue.
Proof.
  intros M [b i] n raw Range Full Read ge le ir aux O op.
  pose proof (V293_full_byte_load_encoding M (b,i) n raw Full Read) as Encoded.
  destruct (map_join_get_sig Encoded) as [rest Join].
  exists (sig (b,i) (true,Byte (Byte.repr (Int.unsigned (Int.repr (Z.of_nat n)))))).
  exists rest. exists M. exists (emp : osabst). exists O. exists O.
  split; [reflexivity | ]. split; [exact Join | ]. split; [reflexivity | ].
  split; [apply map_join_comm; apply map_join_emp | ]. split; [ | exact I].
  unfold V293_owned_record_cell. apply astar_l_apure_intro.
  - split; [ | reflexivity]. exists (encode_val Tint8 (V293_byteval n)).
    split; [reflexivity | ]. cbn [encode_val V293_byteval inj_bytes encode_int List.map ptomvallist].
    exists (sig (b,i) (true,Byte (Byte.repr (Int.unsigned (Int.repr (Z.of_nat n)))))).
    exists (emp : mem). split; [apply map_join_emp | ]. split; reflexivity.
  - apply V293_byte_type; exact Range.
Qed.

(* Distinct byte addresses are essential: independent cell ** Atrue
   assertions cannot be conjoined into one separating resource. *)
Lemma V293_full_byte_cells_owned : forall cells : list (addr * nat),
  NoDup (map fst cells) -> forall M,
  (forall a n, In (a,n) cells -> n < 256 /\
    load Tint8 M a = Some (V293_byteval n) /\
    exists raw, get M a = Some (true,raw)) ->
  forall ge le ir aux O op,
  (ge,le,M,ir,aux,O,op) |=
    V293_owned_record_cells (map (fun cell => (fst cell,Tint8,V293_byteval (snd cell))) cells) ** Atrue.
Proof.
  induction cells as [ | [[b i] n] cells IH]; intros ND M Values ge le ir aux O op.
  - exists (emp : mem). exists M. exists M.
    exists (emp : osabst). exists O. exists O.
    split; [reflexivity | ]. split; [apply map_join_comm; apply map_join_emp | ].
    split; [reflexivity | ]. split; [apply map_join_comm; apply map_join_emp | ].
    split; [split; reflexivity | exact I].
  - inversion ND as [ | a rest Outside RestND]; subst a rest.
    destruct (Values (b,i) n (or_introl eq_refl)) as (Range & Read & raw & Full).
    pose proof (V293_full_byte_load_encoding M (b,i) n raw Full Read) as Encoded.
    destruct (map_join_get_sig Encoded) as [other Join].
    assert (Other : forall a n', In (a,n') cells -> n' < 256 /\
      load Tint8 other a = Some (V293_byteval n') /\
      exists raw', get other a = Some (true,raw')).
    { intros [c j] n' Member.
      destruct (Values (c,j) n' (or_intror Member)) as (Bound & Load & raw' & Permission).
      assert (Different : (b,i) <> (c,j)).
      { intro Same. apply Outside. rewrite Same. apply in_map with (f:=@fst addr nat) in Member. exact Member. }
      assert (Frame : get other (c,j) = get M (c,j)).
      { symmetry. eapply map_join_get_none; [exact Join | apply map_get_sig'; exact Different]. }
      split; [exact Bound | ]. split.
      - unfold load, loadm in *. cbn [typelen loadbytes] in *.
        unfold addr, offset in *. rewrite Frame. exact Load.
      - exists raw'. exact (eq_trans Frame Permission). }
    pose proof (IH RestND other Other ge le ir aux O op) as Rest.
    cbn [map V293_owned_record_cells]. apply astar_assoc_intro.
    exists (sig (b,i) (true,Byte (Byte.repr (Int.unsigned (Int.repr (Z.of_nat n)))))).
    exists other. exists M. exists (emp : osabst). exists O. exists O.
    split; [reflexivity | ]. split; [exact Join | ]. split; [reflexivity | ].
    split; [apply map_join_comm; apply map_join_emp | ]. split; [ | exact Rest].
    unfold V293_owned_record_cell. apply astar_l_apure_intro.
    + split; [ | reflexivity]. exists (encode_val Tint8 (V293_byteval n)).
      split; [reflexivity | ]. cbn [encode_val V293_byteval inj_bytes encode_int List.map ptomvallist].
      exists (sig (b,i) (true,Byte (Byte.repr (Int.unsigned (Int.repr (Z.of_nat n)))))).
      exists (emp : mem). split; [apply map_join_emp | ]. split; reflexivity.
    + apply V293_byte_type; exact Range.
Qed.

(* Ready rows/group and the three bitmap bytes of one event object. *)
Definition V293_bitmap_layout br bg be (base : Z) lo hi elo ehi : list V293_record_cell :=
  map (fun cell => (fst cell,Tint8,V293_byteval (snd cell)))
    [ ((br,0%Z),lo); ((br,1%Z),hi); ((bg,0%Z),V293_ready_group lo hi);
      ((be,(base+11)%Z),elo); ((be,(base+12)%Z),ehi);
      ((be,(base+10)%Z),V293_ready_group elo ehi) ].


Theorem V293_critical_event_return_bitmap_owned :
  forall P ks ge le caller M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp be ebase elo ehi xi bi ny nby nbx
    current reserved bcur bct curbase rb curprio
    running runblock run sched saved interrupt lock schednew high target schedcurrent counter f body next,
  initial < 256 -> (initial < 12 \/ initial = 255) -> new < 12 ->
  let old := if initial =? 255 then curprio else initial in
  old < 13 -> lo < 256 -> hi < 256 -> br <> bg ->
  (0 <= base)%Z -> (base+55 <= Int.max_unsigned)%Z ->
  get le table = None -> get ge table = Some (b,Tarray (Tptr V293_tcb_type) 13) ->
  get le oldprio = Some (bo,Tint8) -> get le newprio = Some (bn,Tint8) ->
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  b <> bo -> b <> bn -> b <> bc -> b <> bt ->
  b <> dy -> b <> dby -> b <> dx -> b <> br -> b <> bg ->
  load Tint8 M (bo,0%Z) = Some (V293_byteval initial) ->
  load Tint8 M (bn,0%Z) = Some (V293_byteval new) ->
  V293_bytes_writable M b (4*Z.of_nat old)%Z 4 ->
  V293_bytes_writable M b (4*Z.of_nat new)%Z 4 ->
  length entries = 13 -> V293_table_loads V293_tcb_type M b entries ->
  get le yo = Some (dy,Tint8) -> get le byo = Some (dby,Tint8) -> get le xo = Some (dx,Tint8) ->
  get le rows = None -> get ge rows = Some (br,Tarray Tint8 2) ->
  get le group = None -> get ge group = Some (bg,Tint8) ->
  dy <> dby -> dy <> dx -> dby <> dx ->
  (forall c, c = dy \/ c = dby \/ c = dx -> c <> bc /\ c <> bt /\ c <> br /\ c <> bg) ->
  V293_tcb_old_loads M bt base (V293_prio_row old)
    (2 ^ V293_prio_row old) (2 ^ V293_prio_bit old) ->
  (exists v, get M (dy,0%Z) = Some (true,v)) ->
  (exists v, get M (dby,0%Z) = Some (true,v)) ->
  (exists v, get M (dx,0%Z) = Some (true,v)) ->
  V293_rekey_bitmap_loads M br bg lo hi (V293_ready_group lo hi) ->
  V293_rekey_bitmap_writable M br bg ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> b /\ c <> dy /\ c <> dby /\ c <> dx) ->
  get le pevent = Some (bp,Tptr V293_event_type) ->
  V293_bytes_writable M bp 0%Z 4 ->
  load (Tcom_ptr 411%Z) M (bt,(base+28)%Z) = Some (Vptr (be,Int.repr ebase)) ->
  bc <> br -> bc <> bg -> bt <> br -> bt <> bg ->
  bp <> b -> bp <> dy -> bp <> dby -> bp <> dx -> bp <> br -> bp <> bg ->
  bp <> be ->
  be <> b -> be <> dy -> be <> dby -> be <> dx -> be <> br -> be <> bg ->
  elo < 256 -> ehi < 256 -> (0 <= ebase)%Z -> (ebase+12 <= Int.max_unsigned)%Z ->
  V293_event_bitmap_loads M be ebase elo ehi (V293_ready_group elo ehi) ->
  V293_event_bitmap_writable M be ebase ->
  (forall x v c, In (x,v) (V293_rekey_ready_bindings yo yn xo xn byo byn old new) ->
    get le x = Some (c,Tint8) -> c <> bp /\ c <> be) ->
  bc <> bt -> bc <> bp -> bc <> be -> bt <> bp -> bt <> be ->
  get le xi = Some (bi,Tint8) ->
  (forall c, c = bn \/ c = bi ->
    c <> b /\ c <> dy /\ c <> dby /\ c <> dx /\ c <> br /\ c <> bg /\ c <> bp /\ c <> be /\ c <> bt) ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> bt) ->
  V293_tcb_update_writable M bt base ->
  get le yn = Some (ny,Tint8) -> get le byn = Some (nby,Tint8) ->
  get le xn = Some (nbx,Tint8) ->
  ny <> bi -> ny <> nby -> ny <> nbx -> bi <> nby -> bi <> nbx -> nby <> nbx ->
  (forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->
    c <> b /\ c <> bo /\ c <> bn /\ c <> bc /\ c <> bt /\
    c <> dy /\ c <> dby /\ c <> dx /\ c <> br /\ c <> bg /\ c <> bp /\ c <> be) ->
  (forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->
    exists v, get M (c,0%Z) = Some (true,v)) ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat new)%Z) = Some Vnull ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat old)%Z) = Some (Vptr (bt,Int.repr base)) ->
  bo <> bn -> bc <> bn -> bc <> bo ->
  (initial = 255 ->
    get le current = None /\ get ge current = Some (bcur,Tptr V293_tcb_type) /\
    load (Tptr V293_tcb_type) M (bcur,0%Z) = Some (Vptr (bct,Int.repr curbase)) /\
    (0 <= curbase)%Z /\ (curbase+50 <= Int.max_unsigned)%Z /\
    load Tint8 M (bct,(curbase+50)%Z) = Some (V293_byteval curprio) /\
    (exists v, get M (bo,0%Z) = Some (true,v))) ->
  get le reserved = None -> get ge reserved = Some (rb,Tint8) ->
  (bt,Int.repr base) <> (rb,Int.zero) ->
  V293_bytes_writable M bc 0%Z 4 ->
  (forall c, In c [b;bn;bt;dy;dby;dx;br;bg;bp;be;ny;bi;nby;nbx] ->
    c <> bo /\ c <> bc) ->
  run < 256 -> get le running = None -> get ge running = Some (runblock,Tint8) ->
  load Tint8 M (runblock,0%Z) = Some (V293_byteval run) ->
  (run = 1 ->
    P sched = Some (V293_OSSched_success_function saved interrupt lock schednew table high target schedcurrent counter) /\
    saved <> interrupt /\ saved <> lock /\ V293_success_sched_blocked ge M interrupt lock) ->
  V293_success_globals_away ge [running;interrupt;lock] [bo;bc;b;dy;dby;dx;br;bg;bp;bt;ny;bi;nby;nbx;be] ->
  callcont ks = Some (kcall f body caller next) ->
  NoDup (map fst (getaddr le)) ->
  (forall c t, In (c,t) (getaddr le) -> V293_bytes_writable M c 0%Z (typelen t)) ->
  (forall c, In c [b;bt;br;bg;be] -> ~ In c (map fst (getaddr le))) ->
  exists Mf,
  let old := if initial =? 255 then curprio else initial in
  let fr := V293_ready_branch_rows lo hi old new in
  (forall c i v, ~ In c (map fst (getaddr le)) ->
    get M (c,i) = Some (true,v) ->
    exists w, get Mf (c,i) = Some (true,w)) /\
  (forall OO op, (ge,caller,Mf,ir,(enabled,si,ci),OO,op) |=
    V293_owned_record_cells (V293_bitmap_layout br bg be ebase (fst fr) (snd fr)
      (fst (V293_ready_rekey_rows elo ehi old new))
      (snd (V293_ready_rekey_rows elo ehi old new))) ** Atrue) /\
  V293_local_steps P
    (curs (sseq (V293_primitive_success_update table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent xi current reserved)
      (V293_task_prio_success_tail running sched)),(kenil,ks))
    ((ge,le,M),ir,(enabled,si,ci))
    (curs (sskip (Some (Vint32 Int.zero))),(kenil,next))
    ((ge,caller,Mf),ir,(enabled,si,ci)) /\
  V293_tcb_updated_loads Mf bt base new /\
  V293_rekey_bitmap_loads Mf br bg (fst fr) (snd fr) (V293_ready_group (fst fr) (snd fr)) /\
  V293_table_loads V293_tcb_type Mf b
    (update_nth_val new (update_nth_val old entries Vnull) (Vptr (bt,Int.repr base))) /\
  (let er := V293_ready_rekey_rows elo ehi old new in
    V293_event_bitmap_loads Mf be ebase (fst er) (snd er) (V293_ready_group (fst er) (snd er))) /\
  load (Tcom_ptr 411%Z) Mf (bt,(base+28)%Z) = Some (Vptr (be,Int.repr ebase)) /\
  (forall c i, ~ In c (map fst (getaddr le)) -> ~ In c [bo;bc;b;dy;dby;dx;br;bg;bp;be;bt;ny;bi;nby;nbx] ->
    get Mf (c,i) = get M (c,i)) /\
  (forall c t k, In (c,t) (getaddr le) -> k < typelen t ->
    get Mf (c,Z.of_nat k) = None) /\
  (forall i, (i < base+50 \/ base+54 < i)%Z -> get Mf (bt,i) = get M (bt,i)) /\
  (forall i, (i < ebase+10 \/ ebase+12 < i)%Z -> get Mf (be,i) = get M (be,i)) /\
  (forall i, get Mf (bt,i) = get (V293_tcb_update_memory M bt base new) (bt,i)).
Proof.
  intros P ks ge le caller M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp be ebase elo ehi xi bi ny nby nbx current reserved bcur bct curbase rb curprio running runblock run sched saved interrupt lock schednew high target schedcurrent counter f body next
    Input Valid N old O L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg Lo Ln Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields Wy Wby Wx Loads W NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg PE Eb Ey Eby Ex Er Eg EL EH EB ELimit ELoads EW LocalApart CT CP CE TP TE Bi ExtraApart NewTcbApart TW NBy NBby NBx NYI NYBY NYBX NIBY NIBX NBYBX CoordApart CoordW Empty Slot Onew Cnew CO Self Nreserved Greserved Token CW EntryApart
    RunRange NoRun GlobalRun LoadRun WhenRunning Away Call ND InitialWritable HeapApart.
  pose proof (V293_critical_event_update_execution_writable_event_frame P (kseq (V293_task_prio_success_tail running sched) ks) ge le M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp be ebase elo ehi xi bi ny nby nbx current reserved bcur bct curbase rb curprio Input Valid N O L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg Lo Ln Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields Wy Wby Wx Loads W NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg PE Eb Ey Eby Ex Er Eg EL EH EB ELimit ELoads EW LocalApart CT CP CE TP TE Bi ExtraApart NewTcbApart TW NBy NBby NBx NYI NYBY NYBX NIBY NIBX NBYBX CoordApart CoordW Empty Slot Onew Cnew CO Self Nreserved Greserved Token CW EntryApart) as Original.
  destruct Original as [Mg Result]. cbn zeta in Result |- *.
  destruct Result as [UpdateWritable [Exec Rest]].
  set (Mh := V293_tcb_update_memory Mg bt base new) in *.
  assert (Frame : forall c i, ~ In c [bo;bc;b;dy;dby;dx;br;bg;bp;bt;ny;bi;nby;nbx;be] -> get Mh (c,i) = get M (c,i)).
  { intros c i NotWritten. destruct Rest as (Updated & Ready & Table & OldSlot & NewSlot & EventLoads & Read & Pointer & Writable & Internal & Untouched & Frame & EventHeader). apply Frame; clear - NotWritten; simpl in NotWritten;intuition congruence. }
  assert (RunLoad : load Tint8 Mh (runblock,0%Z) = Some (V293_byteval run)).
  { etransitivity; [apply V293_load_block_frame;intro i;apply Frame;eapply Away with (x:=running);simpl;eauto | exact LoadRun]. }
  assert (Running : run = 1 ->
    P sched = Some (V293_OSSched_success_function saved interrupt lock schednew table high target schedcurrent counter) /\
    saved <> interrupt /\ saved <> lock /\ V293_success_sched_blocked ge Mh interrupt lock).
  { intro One. destruct (WhenRunning One) as (Program & SI & SL & Blocked).
    split; [exact Program | ]. split; [exact SI | ]. split; [exact SL | ].
    eapply V293_success_sched_blocked_frame; [ | exact Frame | exact Blocked].
    intros x c X G. eapply Away with (x:=x); [simpl in X |- *;tauto | exact G]. }
  assert (FinalWritable : forall c t, In (c,t) (getaddr le) ->
    V293_bytes_writable Mh c 0%Z (typelen t)).
  { intros c t I k K. destruct (InitialWritable c t I k K) as [v W0].
    eapply UpdateWritable;exact W0. }
  destruct (V293_success_tail_return_execution P ks ge le caller Mh ir enabled si ci
    running runblock run sched saved interrupt lock schednew table high target schedcurrent counter
    f body next RunRange NoRun GlobalRun RunLoad Running Call ND FinalWritable)
    as (Mf & Return & FreeFrame & Removed).
  assert (FinalLoad : forall tp c i, In c [b;bt;br;bg;be] ->
    load tp Mf (c,i) = load tp Mh (c,i)).
  { intros tp c i I. apply V293_load_block_frame. intro j.
    apply FreeFrame. apply HeapApart;exact I. }
  assert (Surviving : forall c i v, ~ In c (map fst (getaddr le)) ->
    get M (c,i) = Some (true,v) -> exists w, get Mf (c,i) = Some (true,w)).
  { intros c i v NotLocal Full. rewrite FreeFrame by exact NotLocal.
    exact (UpdateWritable c i v Full). }
  exists Mf. cbn zeta. fold old. split; [exact Surviving | ]. split.
  { intros OO op.
    set (fr := V293_ready_branch_rows lo hi old new).
    set (er := V293_ready_rekey_rows elo ehi old new).
    assert (FR : fst fr < 256 /\ snd fr < 256).
    { unfold fr,V293_ready_branch_rows. destruct (V293_ready_test_flag lo hi old).
      - apply V293_ready_rekey_bounds; try assumption; clear -N; lia.
      - cbn [fst snd]. split; assumption. }
    assert (ER : fst er < 256 /\ snd er < 256).
    { apply V293_ready_rekey_bounds; try assumption; clear -N; lia. }
    assert (GroupRange : forall l h, V293_ready_group l h < 256).
    { intros. unfold V293_ready_group. destruct (l =? 0); destruct (h =? 0); cbn; lia. }
    destruct Rest as (Updated & Ready & Table & OldSlot & NewSlot & EventReady & Read & Pointer & FinalEW & Internal & Untouched & UFrame & EventHeader).
    assert (ReadyFinal : V293_rekey_bitmap_loads Mf br bg (fst fr) (snd fr)
      (V293_ready_group (fst fr) (snd fr))).
    { unfold V293_rekey_bitmap_loads in *. repeat rewrite FinalLoad by (simpl;tauto). exact Ready. }
    assert (EventFinal : V293_event_bitmap_loads Mf be ebase (fst er) (snd er)
      (V293_ready_group (fst er) (snd er))).
    { unfold V293_event_bitmap_loads in *. repeat rewrite FinalLoad by (simpl;tauto). exact EventReady. }
    destruct ReadyFinal as (RL & RH & RGroup).
    destruct EventFinal as (ELoad & EHLoad & EGroup).
    destruct W as (WL & WH & WG). destruct EW as (EWL & EWH & EWG).
    change ((ge,caller,Mf,ir,(enabled,si,ci),OO,op) |=
      V293_owned_record_cells (V293_bitmap_layout br bg be ebase
        (fst fr) (snd fr) (fst er) (snd er)) ** Atrue).
    unfold V293_bitmap_layout.
    apply V293_full_byte_cells_owned.
    - cbn [map fst]. repeat constructor; cbn; intuition
        (try congruence; try (match goal with H : (_,_) = (_,_) |- _ => inversion H; lia end)).
    - intros [c i] n Member. cbn [In] in Member.
      destruct Member as [Same | [Same | [Same | [Same | [Same | [Same | Falsehood]]]]]];
        [ | | | | | | contradiction]; inversion Same; subst c i n.
      all: split; [first [exact (proj1 FR) | exact (proj2 FR) | exact (proj1 ER) | exact (proj2 ER) | apply GroupRange] | ].
      all: split; [assumption | ].
      all: first
        [destruct WL as [v Permission]; eapply Surviving; [apply HeapApart; simpl;tauto | exact Permission]
        |destruct WH as [v Permission]; eapply Surviving; [apply HeapApart; simpl;tauto | exact Permission]
        |destruct WG as [v Permission]; eapply Surviving; [apply HeapApart; simpl;tauto | exact Permission]
        |destruct EWL as [v Permission]; eapply Surviving; [apply HeapApart; simpl;tauto | exact Permission]
        |destruct EWH as [v Permission]; eapply Surviving; [apply HeapApart; simpl;tauto | exact Permission]
        |destruct EWG as [v Permission]; eapply Surviving; [apply HeapApart; simpl;tauto | exact Permission]]. }
  split.
  - eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sseq_step]. }
    eapply V293_local_trans; [exact Exec | ].
    eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sskip_step]. }
    exact Return.
  - destruct Rest as (Updated & Ready & Table & OldSlot & NewSlot & EventReady & Read & Pointer & FinalEW & Internal & Untouched & UFrame & EventHeader).
    split. { unfold V293_tcb_updated_loads in *. repeat rewrite FinalLoad by (simpl;tauto). exact Updated. }
    split. { unfold V293_rekey_bitmap_loads in *. repeat rewrite FinalLoad by (simpl;tauto). exact Ready. }
    split. { intros p R. rewrite FinalLoad by (simpl;tauto). exact (Table p R). }
    split. { unfold V293_event_bitmap_loads in *. repeat rewrite FinalLoad by (simpl;tauto). exact EventReady. }
    split. { rewrite FinalLoad by (simpl;tauto). exact Internal. }
    split.
    + intros c i NotLocal NotWritten. rewrite FreeFrame by exact NotLocal.
      apply UFrame; clear -NotWritten; simpl in NotWritten;intuition congruence.
    + split; [exact Removed | ]. split.
      * intros i Outside. rewrite FreeFrame by (apply HeapApart; simpl;tauto).
        apply Untouched. exact Outside.
      * split.
        -- intros i Outside. rewrite FreeFrame by (apply HeapApart; simpl;tauto).
           apply EventHeader. exact Outside.
        -- intro i. rewrite FreeFrame by (apply HeapApart; simpl;tauto).
           destruct (Z_lt_dec i (base+50)) as [Low | Low].
           { rewrite Untouched by (clear -Low; lia). symmetry.
             unfold V293_tcb_update_memory.
             repeat rewrite V293_put_byte_other by (intro E; injection E as Offset; clear -Low Offset; lia).
             reflexivity. }
           destruct (Z_lt_dec (base+54) i) as [High | High].
           { rewrite Untouched by (clear -Low High; lia). symmetry.
             unfold V293_tcb_update_memory.
             repeat rewrite V293_put_byte_other by (intro E; injection E as Offset; clear -High Offset; lia).
             reflexivity. }
           assert (ByteOffset : (i=base+50 \/ i=base+51 \/ i=base+52 \/ i=base+53 \/ i=base+54)%Z) by (clear -Low High; lia).
           destruct ByteOffset as [-> | [-> | [-> | [-> | ->]]]];
             unfold Mh,V293_tcb_update_memory;
             repeat first [rewrite V293_put_byte_get_same |
               rewrite V293_put_byte_other by (intro E; injection E as Offset; clear -Offset; lia)];
             reflexivity.
Qed.

(* Separate fresh full byte cells from the residual of the actual joint
   current/task fragment. Independent weak assertions are not conjoined. *)
Lemma V293_current_tasks_bytes_joint : forall current tasks cells ge le M ir aux O op,
  (ge,le,M,ir,aux,O,op) |= (CurTid current ** V293_owned_task_records tasks) ** Atrue ->
  NoDup (map fst cells) ->
  (forall a n, In (a,n) cells -> n < 256 /\
    load Tint8 M a = Some (V293_byteval n) /\ exists raw, get M a = Some (true,raw)) ->
  (forall a n b tp, In (a,n) cells -> get ge OSTCBCur = Some (b,Tptr tp) -> fst a <> b) ->
  (forall a n t value, In (a,n) cells -> get tasks t = Some value -> fst a <> fst t) ->
  (ge,le,M,ir,aux,O,op) |=
    ((CurTid current ** V293_owned_task_records tasks) **
      V293_owned_record_cells (map (fun cell => (fst cell,Tint8,V293_byteval (snd cell))) cells)) ** Atrue.
Proof.
  intros current tasks cells ge le M ir aux O op Held ND Values PointerApart TasksApart.
  apply sat_split in Held. destruct Held as (mp & rest & opair & ore & JMP & JOP & Pair & _).
  pose proof Pair as PairParts. apply sat_split in PairParts.
  destruct PairParts as (mc & mt & oc & ot & JMT & JOT & Current & Tasks).
  destruct (V293_current_fragment_local _ _ _ _ _ _ _ _ Current)
    as (b & tp & Binding & EC & SC & RC).
  destruct (V293_owned_task_list_local _ _ _ _ _ _ _ _ Tasks) as [ET [ST RT]].
  subst oc ot. apply map_join_emp' in JOT. subst opair.
  assert (ResidualValues : forall a n, In (a,n) cells -> n < 256 /\
    load Tint8 rest a = Some (V293_byteval n) /\ exists raw, get rest a = Some (true,raw)).
  { intros [c i] n Member. destruct (Values (c,i) n Member) as (Range & Read & raw & Full).
    assert (Empty : get mp (c,i) = None).
    { erewrite map_join_get_none; [ | exact JMT | apply SC; exact (PointerApart (c,i) n b tp Member Binding)].
      apply ST. intros t value InList. apply (TasksApart (c,i) n t value Member).
      eapply V293_task_list_member_lookup; [apply TcbMod.prf | exact InList]. }
    assert (Same : get M (c,i) = get rest (c,i)).
    { eapply map_join_get_none; eauto. }
    split; [exact Range | ]. split.
    - unfold load,loadm in *. cbn [typelen loadbytes] in *.
      unfold addr,offset in *. rewrite <- Same. exact Read.
    - exists raw. exact (eq_trans (eq_sym Same) Full). }
  pose proof (V293_full_byte_cells_owned cells ND rest ResidualValues ge le ir aux ore op) as Bytes.
  apply astar_assoc_intro. apply sat_split'.
  exists mp. exists rest. exists (emp:osabst). exists ore.
  split; [exact JMP | ]. split; [exact JOP | ]. split; assumption.
Qed.

Lemma V293_owned_cells_abstract_empty : forall cells ge le M ir aux O op,
  (ge,le,M,ir,aux,O,op) |= V293_owned_record_cells cells -> O = emp.
Proof.
  induction cells as [ | [[a tp] v] cells IH]; intros ge le M ir aux O op Held.
  - exact (proj2 Held).
  - apply sat_split in Held. destruct Held as (mh & mt & oh & ot & JM & JO & Head & Tail).
    unfold V293_owned_record_cell in Head. apply astar_l_apure_elim in Head.
    destruct Head as [_ [_ Empty]]. change (oh=emp) in Empty. subst oh.
    specialize (IH _ _ _ _ _ _ _ Tail). subst ot.
    apply map_join_emp' in JO. symmetry; exact JO.
Qed.

Lemma V293_current_tasks_bytes_fields_reconstruct : forall current tasks cells events now ge le M ir aux O op,
  (ge,le,M,ir,aux,O,op) |=
    ((CurTid current ** V293_owned_task_records tasks) ** V293_owned_record_cells cells) ** Atrue ->
  (ge,le,M,ir,aux,O,op) |= V293_shared_fields current tasks events now ** Atrue ->
  (ge,le,M,ir,aux,O,op) |=
    (((CurTid current ** V293_owned_task_records tasks) ** V293_owned_record_cells cells) **
      V293_shared_fields current tasks events now) ** Atrue.
Proof.
  intros current tasks cells events now ge le M ir aux O op HP HF.
  apply sat_split in HP. destruct HP as (mp & mr & ophysical & orest & JMP & JOP & Physical & _).
  assert (Empty : ophysical = emp).
  { apply sat_split in Physical. destruct Physical as (mpair & mb & opair & ob & JM & JO & Pair & Bytes).
    pose proof (V293_owned_cells_abstract_empty _ _ _ _ _ _ _ _ Bytes) as EB.
    apply sat_split in Pair. destruct Pair as (mc & mt & oc & ot & JMT & JOT & Current & Tasks).
    destruct (V293_current_fragment_local _ _ _ _ _ _ _ _ Current) as (b & tp & Binding & EC & _).
    destruct (V293_owned_task_list_local _ _ _ _ _ _ _ _ Tasks) as [ET _].
    subst oc ot. apply map_join_emp' in JOT. subst opair ob.
    apply map_join_emp' in JO. symmetry; exact JO. }
  subst ophysical.
  apply sat_split in HF. destruct HF as (mf & mrf & ofields & ofrest & JMF & JOF & Fields & _).
  pose proof (V293_shared_fields_empty_heap _ _ _ _ _ _ _ _ _ _ _ Fields) as EM. subst mf.
  apply sat_split'. exists mp. exists mr. exists ofields. exists ofrest.
  split; [exact JMP | ]. split; [exact JOF | ]. split; [ | exact I].
  apply sat_split'. exists mp. exists (emp:mem). exists (emp:osabst). exists ofields.
  split; [apply map_join_emp | ]. split; [apply map_join_comm; apply map_join_emp | ]. split; assumption.
Qed.
Theorem V293_critical_wait_joint_owned_execution :
  forall P ks ge le caller M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp be ebase elo ehi xi bi ny nby nbx
    current reserved bcur bct curbase rb curprio
    running runblock run sched saved interrupt lock schednew high target schedcurrent counter f body next
    sc abstract_current tasks events now Os Of OO op R reason delay message,
  initial < 256 -> (initial < 12 \/ initial = 255) -> new < 12 ->
  let old := if initial =? 255 then curprio else initial in
  old < 13 -> lo < 256 -> hi < 256 -> br <> bg ->
  (0 <= base)%Z -> (base+55 <= Int.max_unsigned)%Z ->
  get le table = None -> get ge table = Some (b,Tarray (Tptr V293_tcb_type) 13) ->
  get le oldprio = Some (bo,Tint8) -> get le newprio = Some (bn,Tint8) ->
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  b <> bo -> b <> bn -> b <> bc -> b <> bt ->
  b <> dy -> b <> dby -> b <> dx -> b <> br -> b <> bg ->
  load Tint8 M (bo,0%Z) = Some (V293_byteval initial) ->
  load Tint8 M (bn,0%Z) = Some (V293_byteval new) ->
  V293_bytes_writable M b (4*Z.of_nat old)%Z 4 ->
  V293_bytes_writable M b (4*Z.of_nat new)%Z 4 ->
  length entries = 13 -> V293_table_loads V293_tcb_type M b entries ->
  get le yo = Some (dy,Tint8) -> get le byo = Some (dby,Tint8) -> get le xo = Some (dx,Tint8) ->
  get le rows = None -> get ge rows = Some (br,Tarray Tint8 2) ->
  get le group = None -> get ge group = Some (bg,Tint8) ->
  dy <> dby -> dy <> dx -> dby <> dx ->
  (forall c, c = dy \/ c = dby \/ c = dx -> c <> bc /\ c <> bt /\ c <> br /\ c <> bg) ->
  V293_tcb_old_loads M bt base (V293_prio_row old)
    (2 ^ V293_prio_row old) (2 ^ V293_prio_bit old) ->
  (exists v, get M (dy,0%Z) = Some (true,v)) ->
  (exists v, get M (dby,0%Z) = Some (true,v)) ->
  (exists v, get M (dx,0%Z) = Some (true,v)) ->
  V293_rekey_bitmap_loads M br bg lo hi (V293_ready_group lo hi) ->
  V293_rekey_bitmap_writable M br bg ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> b /\ c <> dy /\ c <> dby /\ c <> dx) ->
  get le pevent = Some (bp,Tptr V293_event_type) ->
  V293_bytes_writable M bp 0%Z 4 ->
  load (Tcom_ptr 411%Z) M (bt,(base+28)%Z) = Some (Vptr (be,Int.repr ebase)) ->
  bc <> br -> bc <> bg -> bt <> br -> bt <> bg ->
  bp <> b -> bp <> dy -> bp <> dby -> bp <> dx -> bp <> br -> bp <> bg ->
  bp <> be ->
  be <> b -> be <> dy -> be <> dby -> be <> dx -> be <> br -> be <> bg ->
  elo < 256 -> ehi < 256 -> (0 <= ebase)%Z -> (ebase+12 <= Int.max_unsigned)%Z ->
  V293_event_bitmap_loads M be ebase elo ehi (V293_ready_group elo ehi) ->
  V293_event_bitmap_writable M be ebase ->
  (forall x v c, In (x,v) (V293_rekey_ready_bindings yo yn xo xn byo byn old new) ->
    get le x = Some (c,Tint8) -> c <> bp /\ c <> be) ->
  bc <> bt -> bc <> bp -> bc <> be -> bt <> bp -> bt <> be ->
  get le xi = Some (bi,Tint8) ->
  (forall c, c = bn \/ c = bi ->
    c <> b /\ c <> dy /\ c <> dby /\ c <> dx /\ c <> br /\ c <> bg /\ c <> bp /\ c <> be /\ c <> bt) ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> bt) ->
  get le yn = Some (ny,Tint8) -> get le byn = Some (nby,Tint8) ->
  get le xn = Some (nbx,Tint8) ->
  ny <> bi -> ny <> nby -> ny <> nbx -> bi <> nby -> bi <> nbx -> nby <> nbx ->
  (forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->
    c <> b /\ c <> bo /\ c <> bn /\ c <> bc /\ c <> bt /\
    c <> dy /\ c <> dby /\ c <> dx /\ c <> br /\ c <> bg /\ c <> bp /\ c <> be) ->
  (forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->
    exists v, get M (c,0%Z) = Some (true,v)) ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat new)%Z) = Some Vnull ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat old)%Z) = Some (Vptr (bt,Int.repr base)) ->
  bo <> bn -> bc <> bn -> bc <> bo ->
  (initial = 255 ->
    get le current = None /\ get ge current = Some (bcur,Tptr V293_tcb_type) /\
    load (Tptr V293_tcb_type) M (bcur,0%Z) = Some (Vptr (bct,Int.repr curbase)) /\
    (0 <= curbase)%Z /\ (curbase+50 <= Int.max_unsigned)%Z /\
    load Tint8 M (bct,(curbase+50)%Z) = Some (V293_byteval curprio) /\
    (exists v, get M (bo,0%Z) = Some (true,v))) ->
  get le reserved = None -> get ge reserved = Some (rb,Tint8) ->
  (bt,Int.repr base) <> (rb,Int.zero) ->
  V293_bytes_writable M bc 0%Z 4 ->
  (forall c, In c [b;bn;bt;dy;dby;dx;br;bg;bp;be;ny;bi;nby;nbx] ->
    c <> bo /\ c <> bc) ->
  run < 256 -> get le running = None -> get ge running = Some (runblock,Tint8) ->
  load Tint8 M (runblock,0%Z) = Some (V293_byteval run) ->
  (run = 1 ->
    P sched = Some (V293_OSSched_success_function saved interrupt lock schednew table high target schedcurrent counter) /\
    saved <> interrupt /\ saved <> lock /\ V293_success_sched_blocked ge M interrupt lock) ->
  V293_success_globals_away ge [running;interrupt;lock] [bo;bc;b;dy;dby;dx;br;bg;bp;bt;ny;bi;nby;nbx;be] ->
  callcont ks = Some (kcall f body caller next) ->
  NoDup (map fst (getaddr le)) ->
  (forall c t, In (c,t) (getaddr le) -> V293_bytes_writable M c 0%Z (typelen t)) ->
  (forall c, In c [b;bt;br;bg;be] -> ~ In c (map fst (getaddr le))) ->
  V293_priority_table entries tasks -> V293_bitmap_tasks lo hi tasks ->
  V293_event_wait_tasks elo ehi tasks reason ->
  (reason = os_stat_sem (be,Int.repr ebase) \/ reason = os_stat_q (be,Int.repr ebase) \/
    reason = os_stat_mbox (be,Int.repr ebase) \/ reason = os_stat_mutexsem (be,Int.repr ebase)) ->
  get tasks (bt,Int.repr base) = Some (Int.repr (Z.of_nat old),wait reason delay,message) ->
  (ge,le,M,ir,(enabled,si,ci),Os,op) |=
    V293_shared_fields abstract_current tasks events now **
      ((CurTid abstract_current ** V293_owned_task_records tasks) ** R) ->
  join Os Of OO ->
  (forall t value, get tasks t = Some value -> fst t <> bt ->
    ~ In (fst t) (map fst (getaddr le)) /\
    ~ In (fst t) [bo;bc;b;dy;dby;dx;br;bg;bp;be;ny;bi;nby;nbx]) ->
  (forall pointer_block tp, get ge OSTCBCur = Some (pointer_block,Tptr tp) -> pointer_block <> bt ->
    ~ In pointer_block (map fst (getaddr le)) /\
    ~ In pointer_block [bo;bc;b;dy;dby;dx;br;bg;bp;be;ny;bi;nby;nbx]) ->
  exists Mf Os' OO',
  let old := if initial =? 255 then curprio else initial in
  Os' = set Os abstcblsid (abstcblist
    (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message))) /\
  join Os' Of OO' /\
  spec_step sc (spec_prim nil (V293_wait_prio_step (bt,Int.repr base) old new)) OO
    (spec_done (Some (Vint32 Int.zero))) OO' /\
  (let old := if initial =? 255 then curprio else initial in
  let fr := V293_ready_branch_rows lo hi old new in
  V293_local_steps P
    (curs (sseq (V293_primitive_success_update table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent xi current reserved)
      (V293_task_prio_success_tail running sched)),(kenil,ks))
    ((ge,le,M),ir,(enabled,si,ci))
    (curs (sskip (Some (Vint32 Int.zero))),(kenil,next))
    ((ge,caller,Mf),ir,(enabled,si,ci)) /\
  V293_tcb_updated_loads Mf bt base new /\
  V293_rekey_bitmap_loads Mf br bg (fst fr) (snd fr) (V293_ready_group (fst fr) (snd fr)) /\
  V293_table_loads V293_tcb_type Mf b
    (update_nth_val new (update_nth_val old entries Vnull) (Vptr (bt,Int.repr base))) /\
  (let er := V293_ready_rekey_rows elo ehi old new in
    V293_event_bitmap_loads Mf be ebase (fst er) (snd er) (V293_ready_group (fst er) (snd er))) /\
  load (Tcom_ptr 411%Z) Mf (bt,(base+28)%Z) = Some (Vptr (be,Int.repr ebase)) /\
  (forall c i, ~ In c (map fst (getaddr le)) -> ~ In c [bo;bc;b;dy;dby;dx;br;bg;bp;be;bt;ny;bi;nby;nbx] ->
    get Mf (c,i) = get M (c,i)) /\
  (forall c t k, In (c,t) (getaddr le) -> k < typelen t ->
    get Mf (c,Z.of_nat k) = None) /\
  (forall i, (i < base+50 \/ base+54 < i)%Z -> get Mf (bt,i) = get M (bt,i)) /\
  (forall i, (i < ebase+10 \/ ebase+12 < i)%Z -> get Mf (be,i) = get M (be,i)) /\
  (forall i, get Mf (bt,i) = get (V293_tcb_update_memory M bt base new) (bt,i))) /\
  (ge,caller,Mf,ir,(enabled,si,ci),OO',op) |=
    (((CurTid abstract_current ** V293_owned_task_records
      (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message))) **
      V293_owned_record_cells (V293_bitmap_layout br bg be ebase
        (fst (V293_ready_branch_rows lo hi old new)) (snd (V293_ready_branch_rows lo hi old new))
        (fst (V293_ready_rekey_rows elo ehi old new)) (snd (V293_ready_rekey_rows elo ehi old new)))) **
      V293_shared_fields abstract_current
        (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) events now) ** Atrue /\
  V293_bitmap_tasks lo hi (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) /\
  V293_priority_table
    (update_nth_val new (update_nth_val old entries Vnull) (Vptr (bt,Int.repr base)))
    (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) /\
  (let er := V293_ready_rekey_rows elo ehi old new in
    V293_event_wait_tasks (fst er) (snd er)
      (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) reason).
Proof.
  intros P ks ge le caller M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp be ebase elo ehi xi bi ny nby nbx current reserved bcur bct curbase rb curprio running runblock run sched saved interrupt lock schednew high target schedcurrent counter f body next
    sc abstract_current tasks events now Os Of OO op R reason delay message
    Input Valid N old O L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg Lo Ln Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields Wy Wby Wx Loads W NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg PE Eb Ey Eby Ex Er Eg EL EH EB ELimit ELoads EW LocalApart CT CP CE TP TE Bi ExtraApart NewTcbApart NBy NBby NBx NYI NYBY NYBX NIBY NIBX NBYBX CoordApart CoordW Empty Slot Onew Cnew CO Self Nreserved Greserved Token CW EntryApart
    RunRange NoRun GlobalRun LoadRun WhenRunning Away Call ND InitialWritable HeapApart
    TaskTable Bitmap EventBitmap Reason Task Owned Frame OtherTaskFrame CurrentSafety.
  assert (AllEntry : (ge,le,M,ir,(enabled,si,ci),Os,op) |=
    V293_owned_task_records tasks ** (CurTid abstract_current ** (R ** V293_shared_fields abstract_current tasks events now))) by (clear -Owned; sep auto).
  assert (EmptyEntry : nth new entries Vnull = Vnull).
  { pose proof (View new ltac:(clear -N; lia)) as Loaded.
    rewrite Empty in Loaded. inversion Loaded. reflexivity. }
  assert (Fresh : forall t status msg,
      get tasks t <> Some (Int.repr (Z.of_nat new),status,msg)).
  { intros t status msg Member. pose proof
      (V293_rekey_task_entry entries tasks t new status msg TaskTable ltac:(clear -N; lia) Member) as Entry.
    rewrite EmptyEntry in Entry. discriminate. }
  destruct (V293_wait_prio_owned_step sc abstract_current tasks events now
    (bt,Int.repr base) old new reason delay message ge le M ir (enabled,si,ci) Os op
    ((CurTid abstract_current ** V293_owned_task_records tasks) ** R)
    Of OO O N Task Fresh Owned Frame)
    as (Os' & OO' & Identity & Frame' & Abstract & UpdatedOwned).
  assert (Selected : (ge,le,M,ir,(enabled,si,ci),Os,op) |=
    V293_owned_task_record (bt,Int.repr base) (Int.repr (Z.of_nat old)) (wait reason delay) message ** Atrue).
  { eapply V293_owned_task_list_select; [apply V293_task_lookup_list; exact Task | exact AllEntry]. }
  destruct (V293_owned_task_record_update _ _ _ _ new _ _ _ _ _ _ _ _
    ltac:(clear -N; lia) Selected) as [TW UnusedModel].
  cbn [fst snd] in TW. rewrite Int.unsigned_repr in TW by lia.
  destruct (V293_critical_event_return_bitmap_owned P ks ge le caller M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp be ebase elo ehi xi bi ny nby nbx current reserved bcur bct curbase rb curprio running runblock run sched saved interrupt lock schednew high target schedcurrent counter f body next Input Valid N O L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg Lo Ln Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields Wy Wby Wx Loads W NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg PE Eb Ey Eby Ex Er Eg EL EH EB ELimit ELoads EW LocalApart CT CP CE TP TE Bi ExtraApart NewTcbApart TW NBy NBby NBx NYI NYBY NYBX NIBY NIBX NBYBX CoordApart CoordW Empty Slot Onew Cnew CO Self Nreserved Greserved Token CW EntryApart
    RunRange NoRun GlobalRun LoadRun WhenRunning Away Call ND InitialWritable HeapApart)
    as (Mf & Surviving & BitmapOwned & Result).
  cbn zeta in Result. fold old in Result.
  pose proof Result as Observations.
  destruct Observations as (Exec & Updated & Ready & Table & EventReady & Pointer
    & Outside & Removed & TcbFrame & EventFrame & ExactBlock).
  pose proof (V293_owned_task_records_update _ _ _ _ _ new _ _ _ _ _ _ _ _
    Task ltac:(clear -N; lia) AllEntry) as ModelAll.
  cbn [fst snd] in ModelAll. rewrite Int.unsigned_repr in ModelAll by lia.
  assert (ModelPair : (ge,le,V293_tcb_update_memory M bt base new,ir,(enabled,si,ci),Os,op) |=
    (CurTid abstract_current ** V293_owned_task_records
      (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message))) **
      (R ** V293_shared_fields abstract_current tasks events now)) by (clear -ModelAll; sep auto).
  assert (FinalPair : (ge,caller,Mf,ir,(enabled,si,ci),OO',op) |=
    (CurTid abstract_current ** V293_owned_task_records
      (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message))) ** Atrue).
  { eapply V293_current_task_records_block_frame; [exact ModelPair | | ].
    - intros pointer_block tp Binding i.
      destruct (Pos.eq_dec pointer_block bt) as [Same | Different].
      + subst pointer_block. exact (ExactBlock i).
      + destruct (CurrentSafety pointer_block tp Binding Different) as [NotLocal NotWritten].
        rewrite Outside.
        * unfold V293_tcb_update_memory. repeat rewrite V293_put_byte_other by
            (intro Equal; inversion Equal; congruence). reflexivity.
        * exact NotLocal.
        * clear -NotWritten Different. cbn [In] in NotWritten |- *. intuition congruence.
    - intros t value Member i. destruct (Pos.eq_dec (fst t) bt) as [Same | Different].
      + rewrite Same. exact (ExactBlock i).
      + rewrite map_get_set' in Member by (intro Equal; subst t; cbn in Different; contradiction).
        destruct (OtherTaskFrame t value Member Different) as [NotLocal NotWritten].
        rewrite Outside.
        * unfold V293_tcb_update_memory. repeat rewrite V293_put_byte_other by
            (intro Equal; inversion Equal; congruence). reflexivity.
        * exact NotLocal.
        * clear -NotWritten Different. cbn [In] in NotWritten |- *. intuition congruence. }
  assert (FinalFields : (ge,caller,Mf,ir,(enabled,si,ci),OO',op) |=
      V293_shared_fields abstract_current
        (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) events now ** Atrue).
  { eapply V293_shared_fields_owned_transport; [exact UpdatedOwned | exact Frame']. }
  destruct (V293_wait_prio_branch_relations lo hi elo ehi entries tasks
    (bt,Int.repr base) old new reason delay message O N TaskTable Bitmap EventBitmap Task EmptyEntry)
    as (Branch & FinalBitmap & FinalTable & FinalEvent).
  set (fr := V293_ready_branch_rows lo hi old new).
  set (er := V293_ready_rekey_rows elo ehi old new).
  assert (FR : fst fr < 256 /\ snd fr < 256).
  { unfold fr,V293_ready_branch_rows. destruct (V293_ready_test_flag lo hi old).
    - apply V293_ready_rekey_bounds; try assumption; clear -N; lia.
    - cbn [fst snd]. split; assumption. }
  assert (ER : fst er < 256 /\ snd er < 256).
  { apply V293_ready_rekey_bounds; try assumption; clear -N; lia. }
  assert (GroupRange : forall l h, V293_ready_group l h < 256).
  { intros. unfold V293_ready_group. destruct (l =? 0); destruct (h =? 0); cbn; lia. }
  assert (FinalJoint : (ge,caller,Mf,ir,(enabled,si,ci),OO',op) |=
    ((CurTid abstract_current ** V293_owned_task_records
      (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message))) **
      V293_owned_record_cells (V293_bitmap_layout br bg be ebase (fst fr) (snd fr) (fst er) (snd er))) ** Atrue).
  { unfold V293_bitmap_layout. eapply V293_current_tasks_bytes_joint.
    - exact FinalPair.
    - clear -RG Er Eg. cbn [map fst]. repeat constructor; cbn; intuition
        (try congruence; try (match goal with H : (_,_) = (_,_) |- _ => inversion H; lia end)).
    - destruct Ready as (RL & RH & RGroup). destruct EventReady as (ELoad & EHLoad & EGroup).
      destruct W as (WL & WH & WG). destruct EW as (EWL & EWH & EWG).
      intros [c i] n Member. cbn [In] in Member.
      destruct Member as [Same | [Same | [Same | [Same | [Same | [Same | Falsehood]]]]]];
        [ | | | | | | contradiction]; inversion Same; subst c i n.
      all: split; [first [exact (proj1 FR) | exact (proj2 FR) | exact (proj1 ER) | exact (proj2 ER) | apply GroupRange] | ].
      all: split; [assumption | ].
      all: first
        [destruct WL as [v Permission]; eapply Surviving; [apply HeapApart; clear -b bt br bg be; simpl;tauto | exact Permission]
        |destruct WH as [v Permission]; eapply Surviving; [apply HeapApart; clear -b bt br bg be; simpl;tauto | exact Permission]
        |destruct WG as [v Permission]; eapply Surviving; [apply HeapApart; clear -b bt br bg be; simpl;tauto | exact Permission]
        |destruct EWL as [v Permission]; eapply Surviving; [apply HeapApart; clear -b bt br bg be; simpl;tauto | exact Permission]
        |destruct EWH as [v Permission]; eapply Surviving; [apply HeapApart; clear -b bt br bg be; simpl;tauto | exact Permission]
        |destruct EWG as [v Permission]; eapply Surviving; [apply HeapApart; clear -b bt br bg be; simpl;tauto | exact Permission]].
    - intros [c i] n pointer_block tp Member Binding.
      destruct (Pos.eq_dec pointer_block bt) as [Same | Different].
      + subst pointer_block. clear -Member Br Bg TE. cbn [In] in Member.
        repeat destruct Member as [Same | Member]; try contradiction;
          inversion Same; subst c; cbn; congruence.
      + destruct (CurrentSafety pointer_block tp Binding Different) as [_ NotWritten].
        clear -Member NotWritten. cbn [In] in Member. repeat destruct Member as [Same | Member]; try contradiction;
          inversion Same; subst c; cbn in *; intuition congruence.
    - intros [c i] n t value Member Lookup.
      destruct (TcbMod.eq_dec t (bt,Int.repr base)) as [Same | Different].
      + subst t. clear -Member Br Bg TE. cbn [In] in Member.
        repeat destruct Member as [Same | Member]; try contradiction;
          inversion Same; subst c; cbn; congruence.
      + rewrite map_get_set' in Lookup by congruence.
        destruct (Pos.eq_dec (fst t) bt) as [SameBlock | DifferentBlock].
        * rewrite SameBlock. clear -Member Br Bg TE. cbn [In] in Member.
          repeat destruct Member as [Same | Member]; try contradiction;
            inversion Same; subst c; cbn; congruence.
        * destruct (OtherTaskFrame t value Lookup DifferentBlock) as [_ NotWritten].
          clear -Member NotWritten. cbn [In] in Member. repeat destruct Member as [Same | Member]; try contradiction;
            inversion Same; subst c; cbn in *; intuition congruence. }
  exists Mf. exists Os'. exists OO'. cbn zeta. fold old.
  split; [exact Identity | ]. split; [exact Frame' | ]. split; [exact Abstract | ].
  split; [exact Result | ]. split.
  - eapply V293_current_tasks_bytes_fields_reconstruct; [exact FinalJoint | exact FinalFields].
  - split; [exact FinalBitmap | ]. split; assumption.
Qed.

(* Full priority-table ownership: all 13 slots, not just the two touched
   slots. These are entry/store lemmas, not yet a joint API-return theorem. *)
Lemma V293_pointer_check_encoding : forall n b off bytes,
  check_pointer n b off bytes = true -> bytes = inj_pointer n b off.
Proof.
  induction n as [ | n IH]; intros b off bytes Check.
  - destruct bytes; [reflexivity | discriminate].
  - destruct bytes as [ | raw bytes]; [discriminate | ].
    destruct raw; try discriminate.
    cbn [check_pointer] in Check.
    repeat rewrite Bool.andb_true_iff in Check.
    destruct Check as [[[Block Offset] Index] Tail].
    destruct (peq b b0); [subst b0 | discriminate].
    destruct (Int.eq_dec off i); [subst i | discriminate].
    apply Nat.eqb_eq in Index. subst n0.
    cbn [inj_pointer]. f_equal. apply IH. exact Tail.
Qed.

Lemma V293_pointer_decode_encoding : forall tp bytes v,
  length bytes = 4 -> rule_type_val_match (Tptr tp) v = true ->
  decode_val (Tptr tp) bytes = v -> encode_val (Tptr tp) v = bytes.
Proof.
  intros tp bytes v Len Valid Read.
  unfold decode_val in Read.
  destruct (proj_bytes bytes) as [bl | ] eqn:Raw.
  - destruct (list_eq_dec Byte.eq_dec bl (list_repeat 4 Byte.zero)) as [Zero | Nonzero].
    + apply inj_proj_bytes in Raw. subst bl bytes. inversion Read. reflexivity.
    + destruct v; cbn in Valid; congruence.
  - change (proj_pointer bytes = v) in Read. unfold proj_pointer in Read.
    destruct bytes as [ | raw tail]; [destruct v; cbn in Valid; congruence | ].
    destruct raw; try (destruct v; cbn in Valid; congruence).
    destruct (check_pointer 4 b i (Pointer b i n :: tail)) eqn:Check;
      [ | destruct v; cbn in Valid; congruence].
    inversion Read; subst v. cbn [encode_val].
    symmetry. apply V293_pointer_check_encoding. exact Check.
Qed.

Lemma V293_writable_freeb_exists : forall n M b i,
  V293_bytes_writable M b i n -> exists rest, freeb M b i n = Some rest.
Proof.
  induction n as [ | n IH]; intros M b i W.
  - exists M. reflexivity.
  - destruct (W 0 ltac:(lia)) as [raw Full].
    replace (i + Z.of_nat 0)%Z with i in Full by lia.
    destruct (IH M b (i+1)%Z) as [rest Free].
    { intros k K. specialize (W (S k) ltac:(lia)).
      replace (i+1+Z.of_nat k)%Z with (i+Z.of_nat (S k))%Z by lia. exact W. }
    cbn [freeb]. rewrite Full, Free. eauto.
Qed.

Lemma V293_full_pointer_cell_owned : forall M b i tp v,
  V293_bytes_writable M b i 4 ->
  rule_type_val_match (Tptr tp) v = true ->
  load (Tptr tp) M (b,i) = Some v ->
  forall ge le ir aux O op,
  (ge,le,M,ir,aux,O,op) |= V293_owned_record_cell ((b,i),Tptr tp,v) ** Atrue.
Proof.
  intros M b i tp v W Valid Read ge le ir aux O op.
  destruct (V293_writable_freeb_exists 4 M b i W) as [rest Free].
  destruct (freeb_join _ _ _ _ _ Free) as (bytes & part & Len & Points & Join).
  pose proof (ptomvallist_loadbytes _ _ _ _ Points) as RawRead.
  rewrite Len in RawRead.
  assert (JoinPart : join part rest M) by (apply map_join_comm; exact Join).
  pose proof (@loadbytes_mono _ _ _ _ _ _ JoinPart RawRead) as InWhole.
  rewrite RawRead in InWhole.
  unfold load,loadm in Read. cbn [typelen] in Read. rewrite InWhole in Read.
  injection Read as Decoded.
  pose proof (V293_pointer_decode_encoding tp bytes v Len Valid Decoded) as Encoding.
  exists part. exists rest. exists M. exists (emp:osabst). exists O. exists O.
  split; [reflexivity | ].
  split; [apply map_join_comm; exact Join | ].
  split; [reflexivity | ].
  split; [apply map_join_comm; apply map_join_emp | ]. split; [ | exact I].
  unfold V293_owned_record_cell. apply astar_l_apure_intro.
  - split; [exists bytes; split; assumption | reflexivity].
  - exact Valid.
Qed.

Lemma V293_raw_cells_above : forall bytes b i permission M,
  ptomvallist (b,i) permission bytes M ->
  forall j, (i + Z.of_nat (length bytes) <= j)%Z -> get M (b,j) = None.
Proof.
  induction bytes as [ | raw bytes IH]; intros b i permission M Points j Above.
  - cbn [ptomvallist] in Points. subst M. apply map_emp_get.
  - cbn [ptomvallist] in Points.
    destruct Points as (head & tail & Join & Head & Tail).
    unfold ptomval in Head. subst head.
    assert (Absent : get (sig (b,i) (permission,raw)) (b,j) = None).
    { apply map_get_sig'. intro Same. inversion Same. cbn in Above. lia. }
    erewrite map_join_get_none; [ | exact Join | exact Absent].
    apply (IH _ _ _ _ Tail). change (i + Z.of_nat (S (length bytes)) <= j)%Z in Above. rewrite Nat2Z.inj_succ in Above. lia.
Qed.

Lemma V293_loadbytes_equal_range : forall n M1 M2 b i,
  (forall k, k < n -> get M1 (b,(i+Z.of_nat k)%Z) = get M2 (b,(i+Z.of_nat k)%Z)) ->
  loadbytes M1 (b,i) n = loadbytes M2 (b,i) n.
Proof.
  induction n as [ | n IH]; intros M1 M2 b i Same; [reflexivity | ].
  cbn [loadbytes]. unfold addr,offset.
  pose proof (Same 0 ltac:(lia)) as Head.
  replace (i+Z.of_nat 0)%Z with i in Head by lia. rewrite Head.
  assert (Tail : loadbytes M1 (b,(i+1)%Z) n = loadbytes M2 (b,(i+1)%Z) n).
  { apply IH. intros k Bound.
    replace (i+1+Z.of_nat k)%Z with (i+Z.of_nat (S k))%Z by lia.
    apply Same. lia. }
  rewrite Tail. reflexivity.
Qed.

Fixpoint V293_priority_cells (b : block) (offset : Z) (entries : list val) : list V293_record_cell :=
  match entries with
  | nil => nil
  | v :: rest => ((b,offset),Tptr V293_tcb_type,v) :: V293_priority_cells b (offset+4)%Z rest
  end.

(* Every slot is justified by its own four writable bytes.  Validity is
   separate: the task-to-table pure relation alone does not imply it. *)
Theorem V293_priority_cells_from_full_bytes : forall entries b offset M,
  Forall (fun v => rule_type_val_match (Tptr V293_tcb_type) v = true) entries ->
  V293_bytes_writable M b offset (4 * length entries) ->
  (forall p, p < length entries ->
    load (Tptr V293_tcb_type) M (b,(offset+4*Z.of_nat p)%Z) = Some (nth p entries Vnull)) ->
  forall ge le ir aux O op,
  (ge,le,M,ir,aux,O,op) |= V293_owned_record_cells (V293_priority_cells b offset entries) ** Atrue.
Proof.
  induction entries as [ | v entries IH]; intros b offset M Valid W Reads ge le ir aux O op.
  - cbn [V293_priority_cells V293_owned_record_cells].
    exists (emp:mem). exists M. exists M. exists (emp:osabst). exists O. exists O.
    split; [reflexivity | ]. split; [apply map_join_comm; apply map_join_emp | ].
    split; [reflexivity | ]. split; [apply map_join_comm; apply map_join_emp | ].
    split; [split; reflexivity | exact I].
  - inversion Valid as [ | v' rest HeadValid RestValid]; subst v' rest.
    assert (HeadW : V293_bytes_writable M b offset 4).
    { intros k Bound. apply W. cbn. lia. }
    assert (HeadRead : load (Tptr V293_tcb_type) M (b,offset) = Some v).
    { specialize (Reads 0 ltac:(cbn;lia)).
      replace (offset+4*Z.of_nat 0)%Z with offset in Reads by lia. exact Reads. }
    pose proof (V293_full_pointer_cell_owned M b offset V293_tcb_type v
      HeadW HeadValid HeadRead ge le ir aux O op) as Owned.
    apply sat_split in Owned.
    destruct Owned as (part & rest & o1 & o2 & Join & JO & Cell & Frame).
    unfold V293_owned_record_cell in Cell. apply astar_l_apure_elim in Cell.
    destruct Cell as [HV [[bytes [Encoding Points]] Empty]].
    assert (Len : length bytes = 4).
    { rewrite <- Encoding. apply encode_val_length. }
    assert (Same : forall j, (offset+4 <= j)%Z -> get M (b,j) = get rest (b,j)).
    { intros j Bound. eapply map_join_get_none; [exact Join | ].
      eapply V293_raw_cells_above; [exact Points | rewrite Len; lia]. }
    assert (TailW : V293_bytes_writable rest b (offset+4)%Z (4*length entries)).
    { intros k Bound. destruct (W (4+k) ltac:(cbn;lia)) as [raw Full].
      exists raw. rewrite <- Same by lia.
      replace (offset+4+Z.of_nat k)%Z with (offset+Z.of_nat (4+k))%Z by lia. exact Full. }
    assert (TailReads : forall p, p < length entries ->
      load (Tptr V293_tcb_type) rest (b,(offset+4+4*Z.of_nat p)%Z) = Some (nth p entries Vnull)).
    { intros p Bound. specialize (Reads (S p) ltac:(cbn;lia)).
      cbn [nth] in Reads.
      replace (offset+4+4*Z.of_nat p)%Z with (offset+4*Z.of_nat (S p))%Z by lia.
      unfold load,loadm in Reads |- *. cbn [typelen] in Reads |- *.
      rewrite (V293_loadbytes_equal_range 4 rest M b (offset+4*Z.of_nat (S p))%Z).
      - exact Reads.
      - intros k K. symmetry. apply Same. lia. }
    pose proof (IH _ _ _ RestValid TailW TailReads ge le ir aux o2 op) as TailOwned.
    cbn [V293_priority_cells V293_owned_record_cells]. apply astar_assoc_intro.
    exists part. exists rest. exists M. exists o1. exists o2. exists O.
    split; [reflexivity | ]. split; [exact Join | ]. split; [reflexivity | ].
    split; [exact JO | ]. split; [ | exact TailOwned].
    unfold V293_owned_record_cell. apply astar_l_apure_intro.
    + split; [exists bytes; split; assumption | exact Empty].
    + exact HV.
Qed.

Definition V293_owned_priority_table b entries :=
  V293_owned_record_cells (V293_priority_cells b 0%Z entries).

Theorem V293_full_priority_table_entry : forall entries b M,
  length entries = 13 ->
  Forall (fun v => rule_type_val_match (Tptr V293_tcb_type) v = true) entries ->
  V293_bytes_writable M b 0%Z 52 ->
  V293_table_loads V293_tcb_type M b entries ->
  forall ge le ir aux O op,
  (ge,le,M,ir,aux,O,op) |= V293_owned_priority_table b entries ** Atrue.
Proof.
  intros entries b M Len Valid W Reads ge le ir aux O op.
  apply V293_priority_cells_from_full_bytes; [exact Valid | rewrite Len; exact W | ].
  intros p Bound. replace (0+4*Z.of_nat p)%Z with (4*Z.of_nat p)%Z by lia.
  apply Reads. lia.
Qed.

Lemma V293_priority_cells_store : forall entries p b offset replacement R ge le M ir aux O op,
  p < length entries ->
  rule_type_val_match (Tptr V293_tcb_type) replacement = true ->
  (ge,le,M,ir,aux,O,op) |= V293_owned_record_cells (V293_priority_cells b offset entries) ** R ->
  exists Mf,
  store (Tptr V293_tcb_type) M (b,(offset+4*Z.of_nat p)%Z) replacement = Some Mf /\
  (ge,le,Mf,ir,aux,O,op) |=
    V293_owned_record_cells (V293_priority_cells b offset (update_nth_val p entries replacement)) ** R.
Proof.
  induction entries as [ | v entries IH]; intros p b offset replacement R ge le M ir aux O op Bound Valid Owned;
    [cbn in Bound; lia | ].
  destruct p as [ | p].
  - cbn [V293_priority_cells V293_owned_record_cells update_nth_val] in Owned |- *.
    apply astar_assoc_elim in Owned.
    destruct (V293_owned_record_cell_update _ _ _ _ _ _ _ _ _ _ _ _ Valid Owned) as [Mf [Store Result]].
    exists Mf. replace (offset+4*Z.of_nat 0)%Z with offset by lia.
    split; [exact Store | apply astar_assoc_intro; exact Result].
  - cbn [V293_priority_cells V293_owned_record_cells update_nth_val] in Owned |- *.
    apply astar_assoc_elim in Owned. apply astar_comm in Owned. apply astar_assoc_elim in Owned.
    destruct (IH p b (offset+4)%Z replacement _ ge le M ir aux O op ltac:(cbn in Bound;lia) Valid Owned)
      as [Mf [Store Result]].
    exists Mf. replace (offset+4*Z.of_nat (S p))%Z with (offset+4+4*Z.of_nat p)%Z by lia.
    split; [exact Store | ].
    apply astar_assoc_intro in Result. apply astar_comm in Result.
    apply astar_assoc_intro. exact Result.
Qed.

Lemma V293_priority_update_length : forall entries p v,
  length (update_nth_val p entries v) = length entries.
Proof.
  induction entries as [ | x xs IH]; intros [ | p] v; cbn; auto.
Qed.

(* The two store results are inputs, not separately chosen final memories.
   An arbitrary frame is preserved for these stores, not across local free. *)
Theorem V293_full_priority_table_two_stores :
  forall entries b old new next R ge le M M1 M2 ir aux O op,
  length entries = 13 -> old < 13 -> new < 13 ->
  (ge,le,M,ir,aux,O,op) |= V293_owned_priority_table b entries ** R ->
  store (Tptr V293_tcb_type) M (b,(4*Z.of_nat old)%Z) Vnull = Some M1 ->
  store (Tptr V293_tcb_type) M1 (b,(4*Z.of_nat new)%Z) (Vptr next) = Some M2 ->
  (ge,le,M2,ir,aux,O,op) |= V293_owned_priority_table b
    (update_nth_val new (update_nth_val old entries Vnull) (Vptr next)) ** R.
Proof.
  intros entries b old new next R ge le M M1 M2 ir aux O op Len Old New Owned S1 S2.
  unfold V293_owned_priority_table in Owned |- *.
  destruct (V293_priority_cells_store entries old b 0%Z Vnull R ge le M ir aux O op
    ltac:(lia) eq_refl Owned) as [First [StoreFirst AfterFirst]].
  replace (0+4*Z.of_nat old)%Z with (4*Z.of_nat old)%Z in StoreFirst by lia.
  rewrite S1 in StoreFirst. injection StoreFirst as E1. subst First.
  destruct (V293_priority_cells_store (update_nth_val old entries Vnull) new b 0%Z (Vptr next) R
    ge le M1 ir aux O op ltac:(rewrite V293_priority_update_length;lia) eq_refl AfterFirst)
    as [Final [StoreFinal AfterFinal]].
  replace (0+4*Z.of_nat new)%Z with (4*Z.of_nat new)%Z in StoreFinal by lia.
  rewrite S2 in StoreFinal. injection StoreFinal as E2. subst Final. exact AfterFinal.
Qed.

Lemma V293_priority_cells_nth : forall entries p b offset,
  p < length entries ->
  In ((b,(offset+4*Z.of_nat p)%Z),Tptr V293_tcb_type,nth p entries Vnull)
    (V293_priority_cells b offset entries).
Proof.
  induction entries as [ | v entries IH]; intros p b offset Bound; [cbn in Bound;lia | ].
  destruct p as [ | p].
  - replace (offset+4*Z.of_nat 0)%Z with offset by lia. left. reflexivity.
  - cbn [V293_priority_cells nth]. right.
    replace (offset+4*Z.of_nat (S p))%Z with (offset+4+4*Z.of_nat p)%Z by lia.
    apply IH. cbn in Bound. lia.
Qed.

Theorem V293_full_priority_table_loads : forall entries b R ge le M ir aux O op,
  length entries = 13 ->
  (ge,le,M,ir,aux,O,op) |= V293_owned_priority_table b entries ** R ->
  V293_table_loads V293_tcb_type M b entries.
Proof.
  intros entries b R ge le M ir aux O op Len Owned p Bound.
  change (load (Tptr V293_tcb_type) (getmem (ge,le,M,ir,aux,O,op)) (b,(4*Z.of_nat p)%Z) = Some (nth p entries Vnull)).
  eapply V293_record_star_load_l; [ | exact Owned].
  unfold V293_owned_priority_table. apply V293_owned_record_cells_load.
  replace (4*Z.of_nat p)%Z with (0+4*Z.of_nat p)%Z by lia.
  apply V293_priority_cells_nth. lia.
Qed.

Theorem V293_full_priority_table_any_slot_store :
  forall entries b R ge le M ir aux O op,
  length entries = 13 ->
  (ge,le,M,ir,aux,O,op) |= V293_owned_priority_table b entries ** R ->
  forall p replacement, p < 13 ->
  rule_type_val_match (Tptr V293_tcb_type) replacement = true ->
  exists Mf,
    store (Tptr V293_tcb_type) M (b,(4*Z.of_nat p)%Z) replacement = Some Mf /\
    (ge,le,Mf,ir,aux,O,op) |=
      V293_owned_priority_table b (update_nth_val p entries replacement) ** R.
Proof.
  intros entries b R ge le M ir aux O op Len Owned p replacement Bound Valid.
  unfold V293_owned_priority_table in *.
  destruct (V293_priority_cells_store entries p b 0%Z replacement R ge le M ir aux O op
    ltac:(lia) Valid Owned) as [Mf [Store Result]].
  replace (0+4*Z.of_nat p)%Z with (4*Z.of_nat p)%Z in Store by lia.
  exists Mf. split; assumption.
Qed.

(* Joint full-table ownership at the same actual blocked API return. *)
Lemma V293_owned_cells_away : forall cells b,
  (forall a tp v, In (a,tp,v) cells -> b <> fst a) ->
  forall ge le M ir aux O op,
  (ge,le,M,ir,aux,O,op) |= V293_owned_record_cells cells ->
  forall i, get M (b,i) = None.
Proof.
  induction cells as [ | [[a tp] v] rest IH]; intros b Away ge le M ir aux O op Owned i.
  - destruct Owned as [Empty _]. change (M=emp) in Empty. subst M. apply map_emp_get.
  - apply sat_split in Owned. destruct Owned as (mh & mt & oh & ot & JM & JO & Head & Tail).
    erewrite map_join_get_none; [ | exact JM | ].
    + eapply IH; [ | exact Tail]. intros aa tt vv Member. apply Away with tt vv. right; exact Member.
    + unfold V293_owned_record_cell in Head. apply astar_l_apure_elim in Head.
      destruct Head as [_ [[bytes [Enc Points]] _]].
      destruct a as [ba off]. eapply V293_ptomvallist_other_block; [exact Points | ].
      exact (Away (ba,off) tp v (or_introl eq_refl)).
Qed.

(* Actual fragment support, not independent whole-memory read assertions. *)
Lemma V293_current_tasks_cells_local : forall current tasks cells b ge le M ir aux O op,
  (forall pointer_block tp, get ge OSTCBCur = Some (pointer_block,Tptr tp) -> b <> pointer_block) ->
  (forall t value, get tasks t = Some value -> b <> fst t) ->
  (forall a tp v, In (a,tp,v) cells -> b <> fst a) ->
  (ge,le,M,ir,aux,O,op) |=
    (CurTid current ** V293_owned_task_records tasks) ** V293_owned_record_cells cells ->
  O = emp /\ (forall i, get M (b,i) = None).
Proof.
  intros current tasks cells b ge le M ir aux O op PointerAway TasksAway CellsAway Owned.
  apply sat_split in Owned. destruct Owned as (mp & mb & opair & ob & JM & JO & Pair & Bytes).
  pose proof (V293_owned_cells_abstract_empty _ _ _ _ _ _ _ _ Bytes) as EB.
  apply sat_split in Pair. destruct Pair as (mc & mt & oc & ot & JMT & JOT & Current & Tasks).
  destruct (V293_current_fragment_local _ _ _ _ _ _ _ _ Current)
    as (bc & tp & Binding & EC & SC & RC).
  destruct (V293_owned_task_list_local _ _ _ _ _ _ _ _ Tasks) as [ET [ST RT]].
  subst oc ot ob. apply map_join_emp' in JOT. subst opair.
  apply map_join_emp' in JO. subst O. split; [reflexivity | ].
  intro i. erewrite map_join_get_none; [ | exact JM | ].
  - eapply V293_owned_cells_away; eauto.
  - erewrite map_join_get_none; [ | exact JMT | apply SC; apply PointerAway with tp; exact Binding].
    apply ST. intros t value Member. apply TasksAway with value.
    eapply V293_task_list_member_lookup; [apply TcbMod.prf | exact Member].
Qed.

Lemma V293_spatial_priority_table_joint : forall P entries b ge le M ir aux O op,
  length entries = 13 ->
  Forall (fun v => rule_type_val_match (Tptr V293_tcb_type) v = true) entries ->
  V293_bytes_writable M b 0%Z 52 ->
  V293_table_loads V293_tcb_type M b entries ->
  (forall part apart, (ge,le,part,ir,aux,apart,op) |= P ->
    forall i, get part (b,i) = None) ->
  (ge,le,M,ir,aux,O,op) |= P ** Atrue ->
  (ge,le,M,ir,aux,O,op) |= (P ** V293_owned_priority_table b entries) ** Atrue.
Proof.
  intros P entries b ge le M ir aux O op Len Valid W Reads Support Owned.
  apply sat_split in Owned. destruct Owned as (part & rest & apart & arest & JM & JO & Physical & _).
  assert (Same : forall i, get M (b,i) = get rest (b,i)).
  { intro i. eapply map_join_get_none; [exact JM | apply Support with apart; exact Physical]. }
  assert (RestW : V293_bytes_writable rest b 0%Z 52).
  { intros k Bound. destruct (W k Bound) as [raw Full]. exists raw. rewrite <- Same. exact Full. }
  assert (RestReads : V293_table_loads V293_tcb_type rest b entries).
  { intros p Bound. rewrite (V293_load_block_frame _ _ _ _ _ ltac:(intro i; symmetry; apply Same)).
    exact (Reads p Bound). }
  pose proof (V293_full_priority_table_entry entries b rest Len Valid RestW RestReads
    ge le ir aux arest op) as Table.
  apply astar_assoc_intro. apply sat_split'. exists part. exists rest. exists apart. exists arest.
  split; [exact JM | ]. split; [exact JO | ]. split; assumption.
Qed.

(* Shared fields own only abstract state. Attach them to a single already
   combined physical fragment, rather than conjoining weak postconditions. *)
Lemma V293_physical_shared_fields_joint : forall P current tasks events now ge le M ir aux O op,
  (forall m o, (ge,le,m,ir,aux,o,op) |= P -> o = emp) ->
  (ge,le,M,ir,aux,O,op) |= P ** Atrue ->
  (ge,le,M,ir,aux,O,op) |= V293_shared_fields current tasks events now ** Atrue ->
  (ge,le,M,ir,aux,O,op) |= (P ** V293_shared_fields current tasks events now) ** Atrue.
Proof.
  intros P current tasks events now ge le M ir aux O op Empty HP HF.
  apply sat_split in HP. destruct HP as (mp & mr & opart & orest & JM & JO & Physical & _).
  specialize (Empty _ _ Physical). subst opart.
  apply sat_split in HF. destruct HF as (mf & mrf & ofields & ofrest & JMF & JOF & Fields & _).
  pose proof (V293_shared_fields_empty_heap _ _ _ _ _ _ _ _ _ _ _ Fields) as EM. subst mf.
  apply sat_split'. exists mp. exists mr. exists ofields. exists ofrest.
  split; [exact JM | ]. split; [exact JOF | ]. split; [ | exact I].
  apply sat_split'. exists mp. exists (emp:mem). exists (emp:osabst). exists ofields.
  split; [apply map_join_emp | ]. split; [apply map_join_comm; apply map_join_emp | ]. split; assumption.
Qed.

Lemma V293_priority_update_valid : forall entries p v,
  Forall (fun x => rule_type_val_match (Tptr V293_tcb_type) x = true) entries ->
  rule_type_val_match (Tptr V293_tcb_type) v = true ->
  Forall (fun x => rule_type_val_match (Tptr V293_tcb_type) x = true) (update_nth_val p entries v).
Proof.
  induction entries as [ | x xs IH]; intros [ | p] v Valid New; cbn; try constructor;
    inversion Valid; subst; auto.
Qed.

Theorem V293_critical_wait_table_joint_owned_execution :
  forall P ks ge le caller M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp be ebase elo ehi xi bi ny nby nbx
    current reserved bcur bct curbase rb curprio
    running runblock run sched saved interrupt lock schednew high target schedcurrent counter f body next
    sc abstract_current tasks events now Os Of OO op R reason delay message,
  initial < 256 -> (initial < 12 \/ initial = 255) -> new < 12 ->
  let old := if initial =? 255 then curprio else initial in
  old < 13 -> lo < 256 -> hi < 256 -> br <> bg ->
  (0 <= base)%Z -> (base+55 <= Int.max_unsigned)%Z ->
  get le table = None -> get ge table = Some (b,Tarray (Tptr V293_tcb_type) 13) ->
  get le oldprio = Some (bo,Tint8) -> get le newprio = Some (bn,Tint8) ->
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  b <> bo -> b <> bn -> b <> bc -> b <> bt ->
  b <> dy -> b <> dby -> b <> dx -> b <> br -> b <> bg ->
  load Tint8 M (bo,0%Z) = Some (V293_byteval initial) ->
  load Tint8 M (bn,0%Z) = Some (V293_byteval new) ->
  V293_bytes_writable M b (4*Z.of_nat old)%Z 4 ->
  V293_bytes_writable M b (4*Z.of_nat new)%Z 4 ->
  length entries = 13 -> V293_table_loads V293_tcb_type M b entries ->
  get le yo = Some (dy,Tint8) -> get le byo = Some (dby,Tint8) -> get le xo = Some (dx,Tint8) ->
  get le rows = None -> get ge rows = Some (br,Tarray Tint8 2) ->
  get le group = None -> get ge group = Some (bg,Tint8) ->
  dy <> dby -> dy <> dx -> dby <> dx ->
  (forall c, c = dy \/ c = dby \/ c = dx -> c <> bc /\ c <> bt /\ c <> br /\ c <> bg) ->
  V293_tcb_old_loads M bt base (V293_prio_row old)
    (2 ^ V293_prio_row old) (2 ^ V293_prio_bit old) ->
  (exists v, get M (dy,0%Z) = Some (true,v)) ->
  (exists v, get M (dby,0%Z) = Some (true,v)) ->
  (exists v, get M (dx,0%Z) = Some (true,v)) ->
  V293_rekey_bitmap_loads M br bg lo hi (V293_ready_group lo hi) ->
  V293_rekey_bitmap_writable M br bg ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> b /\ c <> dy /\ c <> dby /\ c <> dx) ->
  get le pevent = Some (bp,Tptr V293_event_type) ->
  V293_bytes_writable M bp 0%Z 4 ->
  load (Tcom_ptr 411%Z) M (bt,(base+28)%Z) = Some (Vptr (be,Int.repr ebase)) ->
  bc <> br -> bc <> bg -> bt <> br -> bt <> bg ->
  bp <> b -> bp <> dy -> bp <> dby -> bp <> dx -> bp <> br -> bp <> bg ->
  bp <> be ->
  be <> b -> be <> dy -> be <> dby -> be <> dx -> be <> br -> be <> bg ->
  elo < 256 -> ehi < 256 -> (0 <= ebase)%Z -> (ebase+12 <= Int.max_unsigned)%Z ->
  V293_event_bitmap_loads M be ebase elo ehi (V293_ready_group elo ehi) ->
  V293_event_bitmap_writable M be ebase ->
  (forall x v c, In (x,v) (V293_rekey_ready_bindings yo yn xo xn byo byn old new) ->
    get le x = Some (c,Tint8) -> c <> bp /\ c <> be) ->
  bc <> bt -> bc <> bp -> bc <> be -> bt <> bp -> bt <> be ->
  get le xi = Some (bi,Tint8) ->
  (forall c, c = bn \/ c = bi ->
    c <> b /\ c <> dy /\ c <> dby /\ c <> dx /\ c <> br /\ c <> bg /\ c <> bp /\ c <> be /\ c <> bt) ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> bt) ->
  get le yn = Some (ny,Tint8) -> get le byn = Some (nby,Tint8) ->
  get le xn = Some (nbx,Tint8) ->
  ny <> bi -> ny <> nby -> ny <> nbx -> bi <> nby -> bi <> nbx -> nby <> nbx ->
  (forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->
    c <> b /\ c <> bo /\ c <> bn /\ c <> bc /\ c <> bt /\
    c <> dy /\ c <> dby /\ c <> dx /\ c <> br /\ c <> bg /\ c <> bp /\ c <> be) ->
  (forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->
    exists v, get M (c,0%Z) = Some (true,v)) ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat new)%Z) = Some Vnull ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat old)%Z) = Some (Vptr (bt,Int.repr base)) ->
  bo <> bn -> bc <> bn -> bc <> bo ->
  (initial = 255 ->
    get le current = None /\ get ge current = Some (bcur,Tptr V293_tcb_type) /\
    load (Tptr V293_tcb_type) M (bcur,0%Z) = Some (Vptr (bct,Int.repr curbase)) /\
    (0 <= curbase)%Z /\ (curbase+50 <= Int.max_unsigned)%Z /\
    load Tint8 M (bct,(curbase+50)%Z) = Some (V293_byteval curprio) /\
    (exists v, get M (bo,0%Z) = Some (true,v))) ->
  get le reserved = None -> get ge reserved = Some (rb,Tint8) ->
  (bt,Int.repr base) <> (rb,Int.zero) ->
  V293_bytes_writable M bc 0%Z 4 ->
  (forall c, In c [b;bn;bt;dy;dby;dx;br;bg;bp;be;ny;bi;nby;nbx] ->
    c <> bo /\ c <> bc) ->
  run < 256 -> get le running = None -> get ge running = Some (runblock,Tint8) ->
  load Tint8 M (runblock,0%Z) = Some (V293_byteval run) ->
  (run = 1 ->
    P sched = Some (V293_OSSched_success_function saved interrupt lock schednew table high target schedcurrent counter) /\
    saved <> interrupt /\ saved <> lock /\ V293_success_sched_blocked ge M interrupt lock) ->
  V293_success_globals_away ge [running;interrupt;lock] [bo;bc;b;dy;dby;dx;br;bg;bp;bt;ny;bi;nby;nbx;be] ->
  callcont ks = Some (kcall f body caller next) ->
  NoDup (map fst (getaddr le)) ->
  (forall c t, In (c,t) (getaddr le) -> V293_bytes_writable M c 0%Z (typelen t)) ->
  (forall c, In c [b;bt;br;bg;be] -> ~ In c (map fst (getaddr le))) ->
  V293_priority_table entries tasks -> V293_bitmap_tasks lo hi tasks ->
  V293_event_wait_tasks elo ehi tasks reason ->
  (reason = os_stat_sem (be,Int.repr ebase) \/ reason = os_stat_q (be,Int.repr ebase) \/
    reason = os_stat_mbox (be,Int.repr ebase) \/ reason = os_stat_mutexsem (be,Int.repr ebase)) ->
  get tasks (bt,Int.repr base) = Some (Int.repr (Z.of_nat old),wait reason delay,message) ->
  (ge,le,M,ir,(enabled,si,ci),Os,op) |=
    V293_shared_fields abstract_current tasks events now **
      ((CurTid abstract_current ** V293_owned_task_records tasks) ** R) ->
  join Os Of OO ->
  (forall t value, get tasks t = Some value -> fst t <> bt ->
    ~ In (fst t) (map fst (getaddr le)) /\
    ~ In (fst t) [bo;bc;b;dy;dby;dx;br;bg;bp;be;ny;bi;nby;nbx]) ->
  (forall pointer_block tp, get ge OSTCBCur = Some (pointer_block,Tptr tp) -> pointer_block <> bt ->
    ~ In pointer_block (map fst (getaddr le)) /\
    ~ In pointer_block [bo;bc;b;dy;dby;dx;br;bg;bp;be;ny;bi;nby;nbx]) ->
  V293_bytes_writable M b 0%Z 52 ->
  Forall (fun v => rule_type_val_match (Tptr V293_tcb_type) v = true) entries ->
  exists Mf Os' OO',
  let old := if initial =? 255 then curprio else initial in
  Os' = set Os abstcblsid (abstcblist
    (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message))) /\
  join Os' Of OO' /\
  spec_step sc (spec_prim nil (V293_wait_prio_step (bt,Int.repr base) old new)) OO
    (spec_done (Some (Vint32 Int.zero))) OO' /\
  (let old := if initial =? 255 then curprio else initial in
  let fr := V293_ready_branch_rows lo hi old new in
  V293_local_steps P
    (curs (sseq (V293_primitive_success_update table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent xi current reserved)
      (V293_task_prio_success_tail running sched)),(kenil,ks))
    ((ge,le,M),ir,(enabled,si,ci))
    (curs (sskip (Some (Vint32 Int.zero))),(kenil,next))
    ((ge,caller,Mf),ir,(enabled,si,ci)) /\
  V293_tcb_updated_loads Mf bt base new /\
  V293_rekey_bitmap_loads Mf br bg (fst fr) (snd fr) (V293_ready_group (fst fr) (snd fr)) /\
  V293_table_loads V293_tcb_type Mf b
    (update_nth_val new (update_nth_val old entries Vnull) (Vptr (bt,Int.repr base))) /\
  (let er := V293_ready_rekey_rows elo ehi old new in
    V293_event_bitmap_loads Mf be ebase (fst er) (snd er) (V293_ready_group (fst er) (snd er))) /\
  load (Tcom_ptr 411%Z) Mf (bt,(base+28)%Z) = Some (Vptr (be,Int.repr ebase)) /\
  (forall c i, ~ In c (map fst (getaddr le)) -> ~ In c [bo;bc;b;dy;dby;dx;br;bg;bp;be;bt;ny;bi;nby;nbx] ->
    get Mf (c,i) = get M (c,i)) /\
  (forall c t k, In (c,t) (getaddr le) -> k < typelen t ->
    get Mf (c,Z.of_nat k) = None) /\
  (forall i, (i < base+50 \/ base+54 < i)%Z -> get Mf (bt,i) = get M (bt,i)) /\
  (forall i, (i < ebase+10 \/ ebase+12 < i)%Z -> get Mf (be,i) = get M (be,i)) /\
  (forall i, get Mf (bt,i) = get (V293_tcb_update_memory M bt base new) (bt,i))) /\
  (ge,caller,Mf,ir,(enabled,si,ci),OO',op) |=
    ((((CurTid abstract_current ** V293_owned_task_records
      (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message))) **
      V293_owned_record_cells (V293_bitmap_layout br bg be ebase
        (fst (V293_ready_branch_rows lo hi old new)) (snd (V293_ready_branch_rows lo hi old new))
        (fst (V293_ready_rekey_rows elo ehi old new)) (snd (V293_ready_rekey_rows elo ehi old new)))) **
      V293_owned_priority_table b
        (update_nth_val new (update_nth_val old entries Vnull) (Vptr (bt,Int.repr base)))) **
      V293_shared_fields abstract_current
        (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) events now) ** Atrue /\
  V293_bitmap_tasks lo hi (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) /\
  V293_priority_table
    (update_nth_val new (update_nth_val old entries Vnull) (Vptr (bt,Int.repr base)))
    (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) /\
  (let er := V293_ready_rekey_rows elo ehi old new in
    V293_event_wait_tasks (fst er) (snd er)
      (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) reason).
Proof.
  intros P ks ge le caller M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp be ebase elo ehi xi bi ny nby nbx current reserved bcur bct curbase rb curprio running runblock run sched saved interrupt lock schednew high target schedcurrent counter f body next
    sc abstract_current tasks events now Os Of OO op R reason delay message
    Input Valid N old O L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg Lo Ln Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields Wy Wby Wx Loads W NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg PE Eb Ey Eby Ex Er Eg EL EH EB ELimit ELoads EW LocalApart CT CP CE TP TE Bi ExtraApart NewTcbApart NBy NBby NBx NYI NYBY NYBX NIBY NIBX NBYBX CoordApart CoordW Empty Slot Onew Cnew CO Self Nreserved Greserved Token CW EntryApart
    RunRange NoRun GlobalRun LoadRun WhenRunning Away Call ND InitialWritable HeapApart
    TaskTable Bitmap EventBitmap Reason Task Owned Frame OtherTaskFrame CurrentSafety FullTableWritable TableValuesValid.
  assert (AllEntry : (ge,le,M,ir,(enabled,si,ci),Os,op) |=
    V293_owned_task_records tasks ** (CurTid abstract_current ** (R ** V293_shared_fields abstract_current tasks events now))) by (clear -Owned; sep auto).
  assert (EmptyEntry : nth new entries Vnull = Vnull).
  { pose proof (View new ltac:(clear -N; lia)) as Loaded.
    rewrite Empty in Loaded. inversion Loaded. reflexivity. }
  assert (Fresh : forall t status msg,
      get tasks t <> Some (Int.repr (Z.of_nat new),status,msg)).
  { intros t status msg Member. pose proof
      (V293_rekey_task_entry entries tasks t new status msg TaskTable ltac:(clear -N; lia) Member) as Entry.
    rewrite EmptyEntry in Entry. discriminate. }
  destruct (V293_wait_prio_owned_step sc abstract_current tasks events now
    (bt,Int.repr base) old new reason delay message ge le M ir (enabled,si,ci) Os op
    ((CurTid abstract_current ** V293_owned_task_records tasks) ** R)
    Of OO O N Task Fresh Owned Frame)
    as (Os' & OO' & Identity & Frame' & Abstract & UpdatedOwned).
  assert (Selected : (ge,le,M,ir,(enabled,si,ci),Os,op) |=
    V293_owned_task_record (bt,Int.repr base) (Int.repr (Z.of_nat old)) (wait reason delay) message ** Atrue).
  { eapply V293_owned_task_list_select; [apply V293_task_lookup_list; exact Task | exact AllEntry]. }
  destruct (V293_owned_task_record_update _ _ _ _ new _ _ _ _ _ _ _ _
    ltac:(clear -N; lia) Selected) as [TW UnusedModel].
  cbn [fst snd] in TW. rewrite Int.unsigned_repr in TW by lia.
  destruct (V293_critical_event_return_bitmap_owned P ks ge le caller M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp be ebase elo ehi xi bi ny nby nbx current reserved bcur bct curbase rb curprio running runblock run sched saved interrupt lock schednew high target schedcurrent counter f body next Input Valid N O L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg Lo Ln Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields Wy Wby Wx Loads W NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg PE Eb Ey Eby Ex Er Eg EL EH EB ELimit ELoads EW LocalApart CT CP CE TP TE Bi ExtraApart NewTcbApart TW NBy NBby NBx NYI NYBY NYBX NIBY NIBX NBYBX CoordApart CoordW Empty Slot Onew Cnew CO Self Nreserved Greserved Token CW EntryApart
    RunRange NoRun GlobalRun LoadRun WhenRunning Away Call ND InitialWritable HeapApart)
    as (Mf & Surviving & BitmapOwned & Result).
  cbn zeta in Result. fold old in Result.
  pose proof Result as Observations.
  destruct Observations as (Exec & Updated & Ready & Table & EventReady & Pointer
    & Outside & Removed & TcbFrame & EventFrame & ExactBlock).
  pose proof (V293_owned_task_records_update _ _ _ _ _ new _ _ _ _ _ _ _ _
    Task ltac:(clear -N; lia) AllEntry) as ModelAll.
  cbn [fst snd] in ModelAll. rewrite Int.unsigned_repr in ModelAll by lia.
  assert (ModelPair : (ge,le,V293_tcb_update_memory M bt base new,ir,(enabled,si,ci),Os,op) |=
    (CurTid abstract_current ** V293_owned_task_records
      (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message))) **
      (R ** V293_shared_fields abstract_current tasks events now)) by (clear -ModelAll; sep auto).
  assert (FinalPair : (ge,caller,Mf,ir,(enabled,si,ci),OO',op) |=
    (CurTid abstract_current ** V293_owned_task_records
      (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message))) ** Atrue).
  { eapply V293_current_task_records_block_frame; [exact ModelPair | | ].
    - intros pointer_block tp Binding i.
      destruct (Pos.eq_dec pointer_block bt) as [Same | Different].
      + subst pointer_block. exact (ExactBlock i).
      + destruct (CurrentSafety pointer_block tp Binding Different) as [NotLocal NotWritten].
        rewrite Outside.
        * unfold V293_tcb_update_memory. repeat rewrite V293_put_byte_other by
            (intro Equal; inversion Equal; congruence). reflexivity.
        * exact NotLocal.
        * clear -NotWritten Different. cbn [In] in NotWritten |- *. intuition congruence.
    - intros t value Member i. destruct (Pos.eq_dec (fst t) bt) as [Same | Different].
      + rewrite Same. exact (ExactBlock i).
      + rewrite map_get_set' in Member by (intro Equal; subst t; cbn in Different; contradiction).
        destruct (OtherTaskFrame t value Member Different) as [NotLocal NotWritten].
        rewrite Outside.
        * unfold V293_tcb_update_memory. repeat rewrite V293_put_byte_other by
            (intro Equal; inversion Equal; congruence). reflexivity.
        * exact NotLocal.
        * clear -NotWritten Different. cbn [In] in NotWritten |- *. intuition congruence. }
  assert (FinalFields : (ge,caller,Mf,ir,(enabled,si,ci),OO',op) |=
      V293_shared_fields abstract_current
        (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) events now ** Atrue).
  { eapply V293_shared_fields_owned_transport; [exact UpdatedOwned | exact Frame']. }
  destruct (V293_wait_prio_branch_relations lo hi elo ehi entries tasks
    (bt,Int.repr base) old new reason delay message O N TaskTable Bitmap EventBitmap Task EmptyEntry)
    as (Branch & FinalBitmap & FinalTable & FinalEvent).
  set (fr := V293_ready_branch_rows lo hi old new).
  set (er := V293_ready_rekey_rows elo ehi old new).
  assert (FR : fst fr < 256 /\ snd fr < 256).
  { unfold fr,V293_ready_branch_rows. destruct (V293_ready_test_flag lo hi old).
    - apply V293_ready_rekey_bounds; try assumption; clear -N; lia.
    - cbn [fst snd]. split; assumption. }
  assert (ER : fst er < 256 /\ snd er < 256).
  { apply V293_ready_rekey_bounds; try assumption; clear -N; lia. }
  assert (GroupRange : forall l h, V293_ready_group l h < 256).
  { intros. unfold V293_ready_group. destruct (l =? 0); destruct (h =? 0); cbn; lia. }
  assert (FinalJoint : (ge,caller,Mf,ir,(enabled,si,ci),OO',op) |=
    ((CurTid abstract_current ** V293_owned_task_records
      (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message))) **
      V293_owned_record_cells (V293_bitmap_layout br bg be ebase (fst fr) (snd fr) (fst er) (snd er))) ** Atrue).
  { unfold V293_bitmap_layout. eapply V293_current_tasks_bytes_joint.
    - exact FinalPair.
    - clear -RG Er Eg. cbn [map fst]. repeat constructor; cbn; intuition
        (try congruence; try (match goal with H : (_,_) = (_,_) |- _ => inversion H; lia end)).
    - destruct Ready as (RL & RH & RGroup). destruct EventReady as (ELoad & EHLoad & EGroup).
      destruct W as (WL & WH & WG). destruct EW as (EWL & EWH & EWG).
      intros [c i] n Member. cbn [In] in Member.
      destruct Member as [Same | [Same | [Same | [Same | [Same | [Same | Falsehood]]]]]];
        [ | | | | | | contradiction]; inversion Same; subst c i n.
      all: split; [first [exact (proj1 FR) | exact (proj2 FR) | exact (proj1 ER) | exact (proj2 ER) | apply GroupRange] | ].
      all: split; [assumption | ].
      all: first
        [destruct WL as [v Permission]; eapply Surviving; [apply HeapApart; clear -b bt br bg be; simpl;tauto | exact Permission]
        |destruct WH as [v Permission]; eapply Surviving; [apply HeapApart; clear -b bt br bg be; simpl;tauto | exact Permission]
        |destruct WG as [v Permission]; eapply Surviving; [apply HeapApart; clear -b bt br bg be; simpl;tauto | exact Permission]
        |destruct EWL as [v Permission]; eapply Surviving; [apply HeapApart; clear -b bt br bg be; simpl;tauto | exact Permission]
        |destruct EWH as [v Permission]; eapply Surviving; [apply HeapApart; clear -b bt br bg be; simpl;tauto | exact Permission]
        |destruct EWG as [v Permission]; eapply Surviving; [apply HeapApart; clear -b bt br bg be; simpl;tauto | exact Permission]].
    - intros [c i] n pointer_block tp Member Binding.
      destruct (Pos.eq_dec pointer_block bt) as [Same | Different].
      + subst pointer_block. clear -Member Br Bg TE. cbn [In] in Member.
        repeat destruct Member as [Same | Member]; try contradiction;
          inversion Same; subst c; cbn; congruence.
      + destruct (CurrentSafety pointer_block tp Binding Different) as [_ NotWritten].
        clear -Member NotWritten. cbn [In] in Member. repeat destruct Member as [Same | Member]; try contradiction;
          inversion Same; subst c; cbn in *; intuition congruence.
    - intros [c i] n t value Member Lookup.
      destruct (TcbMod.eq_dec t (bt,Int.repr base)) as [Same | Different].
      + subst t. clear -Member Br Bg TE. cbn [In] in Member.
        repeat destruct Member as [Same | Member]; try contradiction;
          inversion Same; subst c; cbn; congruence.
      + rewrite map_get_set' in Lookup by congruence.
        destruct (Pos.eq_dec (fst t) bt) as [SameBlock | DifferentBlock].
        * rewrite SameBlock. clear -Member Br Bg TE. cbn [In] in Member.
          repeat destruct Member as [Same | Member]; try contradiction;
            inversion Same; subst c; cbn; congruence.
        * destruct (OtherTaskFrame t value Lookup DifferentBlock) as [_ NotWritten].
          clear -Member NotWritten. cbn [In] in Member. repeat destruct Member as [Same | Member]; try contradiction;
            inversion Same; subst c; cbn in *; intuition congruence. }
  assert (TableWritableFinal : V293_bytes_writable Mf b 0%Z 52).
  { intros k Bound. destruct (FullTableWritable k Bound) as [raw Full].
    eapply Surviving; [apply HeapApart; clear -b bt br bg be; cbn;tauto | exact Full]. }
  assert (TableValuesFinal : Forall
    (fun v => rule_type_val_match (Tptr V293_tcb_type) v = true)
    (update_nth_val new (update_nth_val old entries Vnull) (Vptr (bt,Int.repr base)))).
  { apply V293_priority_update_valid; [apply V293_priority_update_valid; [exact TableValuesValid | reflexivity] | reflexivity]. }
  assert (PointerTableApart : forall pointer_block tp,
    get ge OSTCBCur = Some (pointer_block,Tptr tp) -> b <> pointer_block).
  { intros pointer_block tp Binding. destruct (Pos.eq_dec pointer_block bt) as [Same | Different].
    - subst pointer_block. exact Tbt.
    - destruct (CurrentSafety pointer_block tp Binding Different) as [_ NotWritten].
      clear -NotWritten. cbn [In] in NotWritten. intuition congruence. }
  assert (TasksTableApart : forall t value,
    get (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) t = Some value ->
    b <> fst t).
  { intros t value Lookup. destruct (Pos.eq_dec (fst t) bt) as [Same | Different].
    - rewrite Same. exact Tbt.
    - rewrite map_get_set' in Lookup by (intro Equal;subst t;cbn in Different;contradiction).
      destruct (OtherTaskFrame t value Lookup Different) as [_ NotWritten].
      clear -NotWritten. cbn [In] in NotWritten. intuition congruence. }
  assert (CellsTableApart : forall a tp v,
    In (a,tp,v) (V293_bitmap_layout br bg be ebase (fst fr) (snd fr) (fst er) (snd er)) -> b <> fst a).
  { intros [c i] tp v Member. unfold V293_bitmap_layout in Member. cbn [In map] in Member.
    clear -Member Tr Tg Eb. repeat destruct Member as [Same | Member]; try contradiction;
      inversion Same; subst c; cbn; congruence. }
  assert (FinalFullJoint : (ge,caller,Mf,ir,(enabled,si,ci),OO',op) |=
    (((CurTid abstract_current ** V293_owned_task_records
      (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message))) **
      V293_owned_record_cells (V293_bitmap_layout br bg be ebase (fst fr) (snd fr) (fst er) (snd er))) **
      V293_owned_priority_table b
        (update_nth_val new (update_nth_val old entries Vnull) (Vptr (bt,Int.repr base)))) ** Atrue).
  { eapply V293_spatial_priority_table_joint.
    - repeat rewrite V293_priority_update_length. exact Len.
    - exact TableValuesFinal.
    - exact TableWritableFinal.
    - exact Table.
    - intros part apart Held i.
      exact (proj2 (V293_current_tasks_cells_local _ _ _ _ _ _ _ _ _ _ _
        PointerTableApart TasksTableApart CellsTableApart Held) i).
    - exact FinalJoint. }
  exists Mf. exists Os'. exists OO'. cbn zeta. fold old.
  split; [exact Identity | ]. split; [exact Frame' | ]. split; [exact Abstract | ].
  split; [exact Result | ]. split.
  - eapply V293_physical_shared_fields_joint; [ | exact FinalFullJoint | exact FinalFields].
    intros m o Held. apply sat_split in Held.
    destruct Held as (mpart & mtable & opart & otable & JM & JO & Physical & TablePart).
    pose proof (V293_owned_cells_abstract_empty _ _ _ _ _ _ _ _ TablePart) as ET.
    pose proof (proj1 (V293_current_tasks_cells_local _ _ _ _ _ _ _ _ _ _ _
      PointerTableApart TasksTableApart CellsTableApart Physical)) as EP.
    subst opart otable. apply map_join_emp' in JO. symmetry; exact JO.
  - split; [exact FinalBitmap | ]. split; assumption.
Qed.
