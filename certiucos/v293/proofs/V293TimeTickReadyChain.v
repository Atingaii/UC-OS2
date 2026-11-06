(* Lift the existing ready/task/table relation through the ORIGINAL complete
   tick while. This reuses ready_payload, not a parallel production invariant. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickWhileShared.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickWhileRecords.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickTaskBridge.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLoop.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.code.V293OSTimeTick.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.basetac.join_lib.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Lemma V293_tick_binding_ready_rel : forall binding tasks lo hi entries,
  V293_tick_binding_valid binding ->
  get tasks (V293_tick_task_pointer (fst binding))=Some (V293_tick_binding_value false binding) ->
  V293_ready_rel lo hi entries tasks ->
  let node:=fst binding in
  let updated:=match fst (snd binding) with
    | rdy => tasks
    | wait _ _ => set tasks (V293_tick_task_pointer node) (V293_tick_binding_value true binding)
    end in
  V293_tick_next_group node (V293_ready_group lo hi)=
    V293_ready_group (V293_tick_next_lo node lo) (V293_tick_next_hi node hi) /\
  V293_ready_rel (V293_tick_next_lo node lo) (V293_tick_next_hi node hi) entries updated.
Proof.
  intros [node [status msg]] tasks lo hi entries [Valid [P Shape]] Task Rel.
  cbn [fst snd]. pose proof Rel as [Lo [Hi [Nonempty [Bitmap Table]]]].
  destruct status as [ | reason delay].
  - assert (Values : V293_tick_next_group node (V293_ready_group lo hi)=V293_ready_group lo hi /\
      V293_tick_next_lo node lo=lo /\ V293_tick_next_hi node hi=hi).
    { cbn in Shape. rewrite Shape.
      unfold V293_tick_next_group,V293_tick_next_lo,V293_tick_next_hi,V293_tick_wait_node.
      cbn [V293_tick_delay_value V293_tick_stat_value V293_tick_y V293_tick_x].
      unfold V293_tick_after_group,V293_tick_after_row. cbn.
      destruct (V293_prio_row (V293_tick_prio node)=?0);
        destruct (V293_prio_row (V293_tick_prio node)=?1); repeat split;reflexivity. }
    destruct Values as [Group [Low High]]. rewrite Group,Low,High. split;[reflexivity|exact Rel].
  - destruct Shape as [Shape Delay]. cbn in Shape,Delay. subst delay.
    change (get tasks (V293_tick_task_pointer node)=Some
      (Int.repr (Z.of_nat (V293_tick_prio node)),
        wait reason (Int.repr (V293_tick_delay_value node)),msg)) in Task.
    pose proof (V293_tick_wait_bitmap_values (V293_tick_block node) (V293_tick_base node)
      (V293_tick_delay_value node) reason (V293_tick_pend_value node) (V293_tick_prio node) lo hi)
      as [Low [High Group]]. cbn zeta in Low,High,Group. rewrite <- Shape in Low,High,Group.
    pose proof (V293_tick_next_bitmap_bounds node (V293_ready_group lo hi) lo hi Valid
      ltac:(unfold V293_ready_group;destruct (lo=?0);destruct (hi=?0);lia) Lo Hi) as [_ [LowBound HighBound]].
    split;[rewrite Low,High;exact Group| ].
    unfold V293_ready_rel. split;[exact LowBound| ]. split;[exact HighBound| ]. split.
    + destruct Nonempty as [q Ready]. exists q. rewrite Low,High.
      unfold V293_tick_wait_rows. destruct (Z.eqb (V293_tick_delay_value node) 1);[ |exact Ready].
      apply V293_ready_set_membership;[exact P| |right;exact Ready].
      destruct Ready as [[Q _]|[_ [Q _]]];lia.
    + split.
      * rewrite Low,High. apply V293_tick_wait_bitmap_tasks;assumption.
      * eapply V293_tick_priority_table;[exact Table|exact Task].
Qed.

Theorem V293_tick_chain_ready_rel : forall bindings idle tasks lo hi entries,
  Forall V293_tick_binding_valid bindings -> NoDup (V293_tick_record_keys bindings idle) ->
  (forall b, In b bindings -> get tasks (V293_tick_task_pointer (fst b))=
    Some (V293_tick_binding_value false b)) ->
  V293_ready_rel lo hi entries tasks ->
  let '(gf,(lof,hif)):=V293_tick_chain_bitmap (map fst bindings) (V293_ready_group lo hi) lo hi in
  gf=V293_ready_group lof hif /\
  V293_ready_rel lof hif entries (V293_tick_bindings_run bindings tasks).
Proof.
  induction bindings as [ |[node [status msg]] rest IH];intros idle tasks lo hi entries Valid Unique Inputs Rel.
  - cbn [map V293_tick_chain_bitmap V293_tick_bindings_run]. split;[reflexivity|exact Rel].
  - inversion Valid as [ |head tail HeadValid TailValid];subst head tail.
    change (NoDup (V293_tick_task_pointer node::V293_tick_record_keys rest idle)) in Unique.
    inversion Unique as [ |key keys Fresh TailUnique];subst key keys.
    assert (Apart : forall b, In b rest -> V293_tick_task_pointer node<>V293_tick_task_pointer (fst b)).
    { intros b Member Same. apply Fresh. unfold V293_tick_record_keys. apply in_or_app. left.
      rewrite Same. apply in_map_iff. exists b. split;[reflexivity|exact Member]. }
    pose proof (V293_tick_binding_ready_rel (node,(status,msg)) tasks lo hi entries HeadValid
      (Inputs _ (or_introl eq_refl)) Rel) as Head.
    cbn [fst snd] in Head. destruct Head as [Group NextRel].
    cbn [map V293_tick_chain_bitmap V293_tick_bindings_run fst snd]. rewrite Group.
    apply IH with (idle:=idle);try assumption.
    intros b Member. destruct status as [ |reason delay];[apply Inputs;right;exact Member| ].
    rewrite map_get_set' by (apply Apart;exact Member). apply Inputs;right;exact Member.
Qed.

Theorem V293_tick_record_chain_ready_rel : forall bindings idle message lo hi entries,
  Forall V293_tick_binding_valid bindings -> NoDup (V293_tick_record_keys bindings idle) ->
  V293_ready_rel lo hi entries (V293_tick_record_map false bindings idle message) ->
  let '(gf,(lof,hif)):=V293_tick_chain_bitmap (map fst bindings) (V293_ready_group lo hi) lo hi in
  gf=V293_ready_group lof hif /\
  V293_ready_rel lof hif entries (V293_tick_record_map true bindings idle message).
Proof.
  intros bindings idle message lo hi entries Valid Unique Rel.
  pose proof (V293_tick_chain_ready_rel bindings idle
    (V293_tick_record_map false bindings idle message) lo hi entries Valid Unique
    ltac:(intros b Member;apply V293_tick_record_map_member;assumption) Rel) as Result.
  rewrite V293_tick_bindings_run_map in Result by exact Unique. exact Result.
Qed.

(* Stable endpoint interface: original while and ordered abstract steps,
   with the EXISTING ready_payload closed in the single actual output Mf.
   Priority bytes are framed exactly once; no complete tick/ISR is claimed. *)
Theorem V293_tick_while_ready_payload :
  forall bindings idle message current events now entries sd P ks ge le M ir enabled si ci O op
    ptcb rows group bc bg br bp lo hi R,
  get le ptcb=Some (bc,Tptr V293_tcb_type) ->
  get le rows=None -> get ge rows=Some (br,Tarray Tint8 2) ->
  get le group=None -> get ge group=Some (bg,Tint8) ->
  (Int.unsigned (snd idle)+50<=Int.max_unsigned)%Z ->
  Forall V293_tick_binding_valid bindings -> NoDup (V293_tick_record_keys bindings idle) ->
  V293_ready_rel lo hi entries (V293_tick_record_map false bindings idle message) ->
  (ge,le,M,ir,(enabled,si,ci),O,op) |=
    V293_tick_loop_owned bc (V293_tick_head (map fst bindings) idle) (map fst bindings)
      idle bg br (V293_ready_group lo hi) lo hi
      (V293_owned_record_cells (concat (map V293_tick_binding_extra bindings)) **
        (V293_owned_record_cells (V293_tick_idle_extra idle message) **
          (V293_shared_fields current (V293_tick_record_map false bindings idle message) events now **
            (V293_owned_record_cells (V293_priority_cells bp 0%Z entries) ** R)))) ->
  V293_task_records M (V293_tick_record_map false bindings idle message) /\
  spec_stepstar sd (V293_tick_chain_code bindings) O (END None)
    (set O abstcblsid (abstcblist (V293_tick_record_map true bindings idle message))) /\
  (forall id, id<>abstcblsid ->
    get (set O abstcblsid (abstcblist (V293_tick_record_map true bindings idle message))) id=get O id) /\
  let '(gf,(lof,hif)):=V293_tick_chain_bitmap (map fst bindings) (V293_ready_group lo hi) lo hi in
  exists Mf,
  V293_local_steps P
    (curs (swhile (V293_tick_guard ptcb) (V293_tick_iteration ptcb rows group)),(kenil,ks))
    ((ge,le,M),ir,(enabled,si,ci))
    (curs (sskip None),(kenil,ks)) ((ge,le,Mf),ir,(enabled,si,ci)) /\
  load (Tptr V293_tcb_type) Mf (bc,0%Z)=Some (Vptr idle) /\
  V293_task_records Mf (V293_tick_record_map true bindings idle message) /\
  gf=V293_ready_group lof hif /\
  V293_ready_rel lof hif entries (V293_tick_record_map true bindings idle message) /\
  V293_ready_loads Mf br bg bp lof hif entries /\
  (ge,le,Mf,ir,(enabled,si,ci),
    set O abstcblsid (abstcblist (V293_tick_record_map true bindings idle message)),op) |=
    V293_ready_payload br bg bp (V293_tick_record_map true bindings idle message) **
    ((V293_owned_record_cell (V293_tick_pointer_cell bc idle) **
      (V293_shared_fields current (V293_tick_record_map true bindings idle message) events now ** R)) ** Atrue).
Proof.
  intros bindings idle message current events now entries sd P ks ge le M ir enabled si ci O op
    ptcb rows group bc bg br bp lo hi R Bind Nr Gr Ng Gg IdleLimit Valid Unique Rel Owned.
  pose proof Rel as [Lo [Hi _]].
  pose proof (V293_tick_while_shared_records bindings idle message current events now sd P ks
    ge le M ir enabled si ci O op ptcb rows group bc bg br (V293_ready_group lo hi) lo hi
    (V293_owned_record_cells (V293_priority_cells bp 0%Z entries) ** R)
    Bind Nr Gr Ng Gg IdleLimit Valid Unique
    ltac:(unfold V293_ready_group;destruct (lo=?0);destruct (hi=?0);lia) Lo Hi Owned) as Run.
  destruct Run as (Old & Abstract & Slots & Run).
  split;[exact Old| ]. split;[exact Abstract| ]. split;[exact Slots| ].
  pose proof (V293_tick_record_chain_ready_rel bindings idle message lo hi entries Valid Unique Rel) as Pure.
  destruct (V293_tick_chain_bitmap (map fst bindings) (V293_ready_group lo hi) lo hi)
    as [gf [lof hif]] eqn:Bitmap.
  destruct Pure as [Group NewRel]. destruct Run as (Mf & Exec & Pointer & Records & Returned).
  exists Mf. split;[exact Exec| ]. split;[exact Pointer| ]. split;[exact Records| ].
  split;[exact Group| ]. split;[exact NewRel| ].
  rewrite Group in Returned.
  assert (Combined : (ge,le,Mf,ir,(enabled,si,ci),
    set O abstcblsid (abstcblist (V293_tick_record_map true bindings idle message)),op) |=
    (V293_owned_task_records (V293_tick_record_map true bindings idle message) **
      V293_owned_record_cells (V293_ready_cells br bg bp lof hif entries)) **
    ((V293_owned_record_cell (V293_tick_pointer_cell bc idle) **
      (V293_shared_fields current (V293_tick_record_map true bindings idle message) events now ** R)) ** Atrue)).
  { unfold V293_tick_bitmap_cells,V293_ready_cells in Returned |- *.
    cbn [app V293_owned_record_cells] in Returned |- *. clear -Returned. sep auto. }
  assert (Cells : (ge,le,Mf,ir,(enabled,si,ci),
    set O abstcblsid (abstcblist (V293_tick_record_map true bindings idle message)),op) |=
    V293_owned_record_cells (V293_ready_cells br bg bp lof hif entries) ** Atrue)
    by (clear -Combined;sep auto).
  split.
  - apply sat_split in Cells. destruct Cells as (m1&m2&o1&o2&JM&JO&Cells&Frame).
    eapply V293_ready_loads_sub;[exists m2;exact JM| ].
    exact (V293_ready_cells_loads br bg bp lof hif entries
      (ge,le,m1,ir,(enabled,si,ci),o1,op)
      (proj1 (proj2 (proj2 (proj2 (proj2 NewRel))))) Cells).
  - unfold V293_ready_payload.
    eapply astar_mono;[ |intros st H;exact H|exact Combined].
    intros st H. eapply astar_mono;[intros st0 H0;exact H0| |exact H].
    intros st0 H0. exists lof. exists hif. exists entries.
    apply astar_l_apure_intro;[exact H0|exact NewRel].
Qed.
