(* Ordered abstract updates for the ORIGINAL tick while. Ready tasks are
   skipped; each waiting task takes the existing original primitive once.
   No new execution relation or arbitrary post-state oracle is introduced. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickWhileRecords.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickTaskBridge.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLoop.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.code.V293OSTimeTick.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.basetac.join_lib.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickRecordReassembly.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Fixpoint V293_tick_bindings_run (bindings : list (V293_tick_task * (taskstatus * val)))
  (tasks : TcbMod.map) : TcbMod.map :=
  match bindings with
  | [] => tasks
  | binding::rest => V293_tick_bindings_run rest
      (match fst (snd binding) with
       | rdy => tasks
       | wait _ _ => set tasks (V293_tick_task_pointer (fst binding))
           (V293_tick_binding_value true binding)
       end)
  end.
Fixpoint V293_tick_chain_code (bindings : list (V293_tick_task * (taskstatus * val))) : spec_code :=
  match bindings with
  | [] => END None
  | binding::rest =>
      match fst (snd binding) with
      | rdy => V293_tick_chain_code rest
      | wait _ _ => spec_seq
          (spec_prim nil (V293_tick_wait_step (V293_tick_task_pointer (fst binding))))
          (V293_tick_chain_code rest)
      end
  end.

Lemma V293_tick_record_map_member : forall bindings idle message after binding,
  NoDup (V293_tick_record_keys bindings idle) -> In binding bindings ->
  get (V293_tick_record_map after bindings idle message)
      (V293_tick_task_pointer (fst binding))=Some (V293_tick_binding_value after binding).
Proof.
  induction bindings as [ | head rest IH]; intros idle message after binding Unique Member;
    [contradiction | ].
  change (NoDup (V293_tick_task_pointer (fst head)::V293_tick_record_keys rest idle)) in Unique.
  inversion Unique as [ | key keys Fresh TailUnique]; subst key keys.
  destruct Member as [Same|Member].
  - subst head. apply map_get_set.
  - cbn [V293_tick_record_map]. rewrite map_get_set'.
    + apply IH; assumption.
    + intro Same. apply Fresh. unfold V293_tick_record_keys.
      apply in_or_app. left. rewrite Same. apply in_map_iff. exists binding. split; [reflexivity | exact Member].
Qed.

Lemma V293_tick_task_sets_commute : forall (tasks : TcbMod.map) t u a b,
  t<>u -> set (set tasks t a) u b=set (set tasks u b) t a.
Proof.
  intros tasks t u a b Apart. apply TcbMod.extensionality. intro v.
  change (get (set (set tasks t a) u b) v=get (set (set tasks u b) t a) v).
  destruct (TcbMod.eq_dec v t) as [Same|Nt]; [subst v | ].
  - rewrite map_get_set' by congruence. rewrite !map_get_set. reflexivity.
  - destruct (TcbMod.eq_dec v u) as [Same|Nu]; [subst v | ].
    + rewrite map_get_set. rewrite map_get_set' by congruence. symmetry;apply map_get_set.
    + rewrite !map_get_set' by congruence. reflexivity.
Qed.

Lemma V293_tick_bindings_run_fresh : forall bindings tasks t value,
  ~ In t (map (fun b => V293_tick_task_pointer (fst b)) bindings) ->
  V293_tick_bindings_run bindings (set tasks t value)=
    set (V293_tick_bindings_run bindings tasks) t value.
Proof.
  induction bindings as [ | [node [status msg]] rest IH]; intros tasks t value Fresh;
    [reflexivity | ].
  cbn [map fst snd] in Fresh. cbn [V293_tick_bindings_run fst snd].
  destruct status as [ | reason delay].
  - apply IH. intro Member. apply Fresh. right;exact Member.
  - rewrite V293_tick_task_sets_commute by (intro Same;apply Fresh;left;congruence).
    apply IH. intro Member. apply Fresh. right;exact Member.
Qed.

Theorem V293_tick_bindings_run_map : forall bindings idle message,
  NoDup (V293_tick_record_keys bindings idle) ->
  V293_tick_bindings_run bindings (V293_tick_record_map false bindings idle message)=
    V293_tick_record_map true bindings idle message.
Proof.
  induction bindings as [ | [node [status msg]] rest IH]; intros idle message Unique;
    [reflexivity | ].
  change (NoDup (V293_tick_task_pointer node::V293_tick_record_keys rest idle)) in Unique.
  inversion Unique as [ | key keys Fresh TailUnique]; subst key keys.
  assert (FreshRest : ~ In (V293_tick_task_pointer node)
    (map (fun b => V293_tick_task_pointer (fst b)) rest)).
  { intro Member. apply Fresh. unfold V293_tick_record_keys. apply in_or_app. left;exact Member. }
  cbn [V293_tick_bindings_run V293_tick_record_map fst snd].
  destruct status as [ | reason delay].
  - rewrite V293_tick_bindings_run_fresh by exact FreshRest.
    rewrite IH by exact TailUnique. reflexivity.
  - assert (Shadow : set (set (V293_tick_record_map false rest idle message)
        (V293_tick_task_pointer node) (V293_tick_binding_value false (node,(wait reason delay,msg))))
        (V293_tick_task_pointer node) (V293_tick_binding_value true (node,(wait reason delay,msg)))=
      set (V293_tick_record_map false rest idle message)
        (V293_tick_task_pointer node) (V293_tick_binding_value true (node,(wait reason delay,msg)))).
    { apply TcbMod.extensionality. intro t. match goal with |- TcbMod.get ?l t=TcbMod.get ?r t => change (get l t=get r t) end.
      destruct (TcbMod.eq_dec t (V293_tick_task_pointer node)) as [Same|Apart];
        [subst t;rewrite !map_get_set | rewrite !map_get_set' by congruence]; reflexivity. }
    rewrite Shadow. rewrite V293_tick_bindings_run_fresh by exact FreshRest.
    rewrite IH by exact TailUnique. reflexivity.
Qed.

Theorem V293_tick_chain_transition : forall bindings idle sd O tasks,
  Forall V293_tick_binding_valid bindings -> NoDup (V293_tick_record_keys bindings idle) ->
  get O abstcblsid=Some (abstcblist tasks) ->
  (forall b, In b bindings -> get tasks (V293_tick_task_pointer (fst b))=
    Some (V293_tick_binding_value false b)) ->
  spec_stepstar sd (V293_tick_chain_code bindings) O (END None)
    (set O abstcblsid (abstcblist (V293_tick_bindings_run bindings tasks))).
Proof.
  induction bindings as [ | [node [status msg]] rest IH];
    intros idle sd O tasks Valid Unique Slot Inputs.
  - cbn [V293_tick_bindings_run V293_tick_chain_code].
    assert (Identity : set O abstcblsid (abstcblist tasks)=O) by (apply get_set_same;exact Slot).
    rewrite Identity. apply spec_stepO.
  - inversion Valid as [ | head tail HeadValid TailValid]; subst head tail.
    change (NoDup (V293_tick_task_pointer node::V293_tick_record_keys rest idle)) in Unique.
    inversion Unique as [ | key keys Fresh TailUnique]; subst key keys.
    assert (Apart : forall b, In b rest -> V293_tick_task_pointer (fst b)<>V293_tick_task_pointer node).
    { intros b Member Same. apply Fresh. unfold V293_tick_record_keys. apply in_or_app. left.
      rewrite <- Same. apply in_map_iff. exists b. split; [reflexivity | exact Member]. }
    cbn [V293_tick_chain_code V293_tick_bindings_run fst snd].
    destruct status as [ | reason delay].
    + apply IH with (idle:=idle); try assumption. intros b Member. apply Inputs. right;exact Member.
    + destruct HeadValid as [NodeValid [P [Shape Delay]]].
      cbn in Delay. subst delay.
      assert (D : (0<=V293_tick_delay_value node<=Int.max_unsigned)%Z).
      { exact (proj1 (proj2 NodeValid)). }
      assert (Task : get tasks (V293_tick_task_pointer node)=
        Some (Int.repr (Z.of_nat (V293_tick_prio node)),
          wait reason (Int.repr (V293_tick_delay_value node)),msg)).
      { apply (Inputs (node,(wait reason (Int.repr (V293_tick_delay_value node)),msg))). left;reflexivity. }
      eapply spec_stepS.
      * apply spec_seq_step2. apply V293_tick_wait_transition; eauto.
      * eapply spec_stepS; [apply spec_seq_step1 | ].
        pose proof (IH idle sd
          (set O abstcblsid (abstcblist (set tasks (V293_tick_task_pointer node)
            (V293_tick_binding_value true (node,(wait reason (Int.repr (V293_tick_delay_value node)),msg))))))
          (set tasks (V293_tick_task_pointer node)
            (V293_tick_binding_value true (node,(wait reason (Int.repr (V293_tick_delay_value node)),msg))))
          TailValid TailUnique ltac:(apply map_get_set)
          ltac:(intros b Member;rewrite map_get_set' by (intro Same;apply (Apart b Member);congruence);
            apply Inputs;right;exact Member)) as Tail.
        assert (Overwrite : forall value, set (set O abstcblsid
          (abstcblist (set tasks (V293_tick_task_pointer node)
            (V293_tick_binding_value true (node,(wait reason (Int.repr (V293_tick_delay_value node)),msg))))))
          abstcblsid value=set O abstcblsid value).
        { intro value. apply OSAbstMod.extensionality. intro id. match goal with |- OSAbstMod.get ?l id=OSAbstMod.get ?r id => change (get l id=get r id) end.
          destruct (OSAbstMod.eq_dec id abstcblsid) as [Same|Different];
            [subst id;rewrite !map_get_set | rewrite !map_get_set' by congruence];reflexivity. }
        rewrite Overwrite in Tail. exact Tail.
Qed.

Theorem V293_tick_record_chain_transition : forall bindings idle message sd O,
  Forall V293_tick_binding_valid bindings -> NoDup (V293_tick_record_keys bindings idle) ->
  get O abstcblsid=Some (abstcblist (V293_tick_record_map false bindings idle message)) ->
  spec_stepstar sd (V293_tick_chain_code bindings) O (END None)
    (set O abstcblsid (abstcblist (V293_tick_record_map true bindings idle message))).
Proof.
  intros bindings idle message sd O Valid Unique Slot.
  rewrite <- (V293_tick_bindings_run_map bindings idle message Unique).
  apply V293_tick_chain_transition with (idle:=idle); try assumption.
  intros b Member. apply V293_tick_record_map_member; assumption.
Qed.

(* Recover the OLD logical value from the very same raw entry resources.
   This conversion is a logical consequence, not an additional writable frame. *)
Lemma V293_tick_binding_record_before : forall binding next R s,
  V293_tick_binding_valid binding ->
  s |= V293_owned_record_cells (V293_tick_task_cells (fst binding) next) **
    (V293_owned_record_cells (V293_tick_binding_extra binding) ** R) ->
  s |= V293_owned_task_record (V293_tick_task_pointer (fst binding))
    (Int.repr (Z.of_nat (V293_tick_prio (fst binding))))
    (V293_tick_binding_status false binding) (snd (snd binding)) ** (R ** Atrue).
Proof.
  intros [t [status message]] next R s [Valid [P Shape]] Owned.
  destruct t as [b base d stat pend y x p].
  change (p<13) in P.
  unfold V293_tick_task_valid in Valid; cbn in Valid.
  destruct Valid as ([Base Limit] & D & Stat & Pend & Y & X & Prio & Nonidle).
  assert (U : Int.unsigned (Int.repr base)=base)
    by (apply Int.unsigned_repr;change (0<=base<=4294967295)%Z;lia).
  destruct status as [ | reason delay].
  - cbn in Shape. inversion Shape; subst d stat y x.
    assert (Cells : s |= V293_owned_record_cells
      (V293_record_layout (b,Int.repr base) p rdy message 0) ** (R ** Atrue)).
    { unfold V293_record_layout;cbn [fst snd];rewrite U.
      cbn [V293_tick_task_cells V293_tick_binding_extra V293_tick_record_extra
        V293_tick_block V293_tick_base V293_tick_delay_value V293_tick_stat_value
        V293_tick_pend_value V293_tick_y V293_tick_x V293_tick_prio fst snd
        app V293_owned_record_cells] in Owned |- *.
      clear -Owned. sep auto. }
    eapply astar_mono; [ | | exact Cells]; [ | intros;assumption].
    intros st Held. unfold V293_owned_task_record.
    exists p. exists 0. apply astar_l_apure_intro; [exact Held | repeat split;try reflexivity;lia].
  - destruct Shape as [Shape Delay]. cbn in Shape,Delay.
    inversion Shape; subst stat y x. subst delay.
    assert (Cells : s |= V293_owned_record_cells
      (V293_record_layout (b,Int.repr base) p (wait reason (Int.repr d)) message pend) ** (R ** Atrue)).
    { destruct reason;unfold V293_record_layout;cbn [fst snd];rewrite U;
      cbn [V293_tick_task_cells V293_tick_binding_extra V293_tick_record_extra
        V293_tick_reason_stat V293_tick_block V293_tick_base V293_tick_delay_value V293_tick_stat_value
        V293_tick_pend_value V293_tick_y V293_tick_x V293_tick_prio fst snd
        app V293_owned_record_cells] in Owned |- *;
      clear -Owned;sep auto. }
    eapply astar_mono; [ | | exact Cells]; [ | intros;assumption].
    intros st Held. unfold V293_owned_task_record.
    exists p. exists pend. apply astar_l_apure_intro; [exact Held | repeat split;try reflexivity;lia].
Qed.

Theorem V293_tick_chain_records_before : forall bindings idle message R s,
  Forall V293_tick_binding_valid bindings -> NoDup (V293_tick_record_keys bindings idle) ->
  s |= V293_owned_record_cells
      (V293_tick_chain_cells (map fst bindings) idle) **
    (V293_owned_record_cells (concat (map V293_tick_binding_extra bindings)) **
    (V293_owned_record_cell (V293_tick_idle_cell idle) **
    (V293_owned_record_cells (V293_tick_idle_extra idle message) ** R))) ->
  s |= V293_owned_task_records (V293_tick_record_map false bindings idle message) ** (R ** Atrue).
Proof.
  induction bindings as [ | [t [status msg]] rest IH]; intros idle message R s Valid Unique Owned.
  - cbn [map concat V293_tick_chain_cells V293_owned_record_cells V293_tick_record_map] in Owned |- *.
    assert (Idle : s |= V293_owned_task_record idle (Int.repr 12) rdy message ** R).
    { apply V293_tick_idle_record. clear -Owned. sep auto. }
    unfold V293_owned_task_records. change (s |= V293_owned_task_list ((idle,(Int.repr 12,rdy,message))::nil) ** (R ** Atrue)).
    cbn [V293_owned_task_list]. clear -Idle. sep auto.
  - inversion Valid as [ | head tail HeadValid TailValid]; subst head tail.
    change (NoDup (V293_tick_task_pointer t::V293_tick_record_keys rest idle)) in Unique.
    inversion Unique as [ | key keys Fresh TailUnique]; subst key keys.
    assert (Absent : get (V293_tick_record_map false rest idle message) (V293_tick_task_pointer t)=None).
    { apply V293_tick_record_map_absent. exact Fresh. }
    assert (Opened : s |=
      V293_owned_record_cells (V293_tick_task_cells t
        (V293_tick_head (map fst rest) idle)) **
      (V293_owned_record_cells (V293_tick_binding_extra (t,(status,msg))) **
      (V293_owned_record_cells (V293_tick_chain_cells (map fst rest) idle) **
      (V293_owned_record_cells (concat (map V293_tick_binding_extra rest)) **
      (V293_owned_record_cell (V293_tick_idle_cell idle) **
      (V293_owned_record_cells (V293_tick_idle_extra idle message) ** R)))))).
    { cbn [map concat V293_tick_chain_cells] in Owned.
      assert (Split : s |=
        (V293_owned_record_cells (V293_tick_task_cells t
          (V293_tick_head (map fst rest) idle)) **
         V293_owned_record_cells (V293_tick_chain_cells (map fst rest) idle)) **
        ((V293_owned_record_cells (V293_tick_binding_extra (t,(status,msg))) **
          V293_owned_record_cells (concat (map V293_tick_binding_extra rest))) **
         (V293_owned_record_cell (V293_tick_idle_cell idle) **
          (V293_owned_record_cells (V293_tick_idle_extra idle message) ** R)))).
      { eapply astar_mono; [ | | exact Owned].
        - intros st H. apply V293_tick_cells_append. exact H.
        - intros st H. eapply astar_mono; [ | | exact H].
          + intros st0 H0. apply V293_tick_cells_append. exact H0.
          + intros st0 H0. exact H0. }
      clear -Split. sep auto. }
    pose proof (V293_tick_binding_record_before (t,(status,msg)) _ _ _ HeadValid Opened) as HeadRecord.
    assert (TailEntry : s |=
      V293_owned_record_cells (V293_tick_chain_cells (map fst rest) idle) **
      (V293_owned_record_cells (concat (map V293_tick_binding_extra rest)) **
      (V293_owned_record_cell (V293_tick_idle_cell idle) **
      (V293_owned_record_cells (V293_tick_idle_extra idle message) **
      (V293_owned_task_record (V293_tick_task_pointer t) (Int.repr (Z.of_nat (V293_tick_prio t)))
        (V293_tick_binding_status false (t,(status,msg))) msg ** (R ** Atrue)))))).
    { cbn [fst snd] in HeadRecord. clear -HeadRecord. sep auto. }
    pose proof (IH _ _ _ _ TailValid TailUnique TailEntry) as TailRecords.
    cbn [V293_tick_record_map].
    eapply V293_owned_task_records_reassemble.
    rewrite V293_tick_delete_absent by exact Absent.
    unfold V293_tick_binding_value. cbn [fst snd]. clear -TailRecords. sep auto.
Qed.

(* One source-level fragment, one real Mf and one ordered abstract execution.
   The full shared fields are owned jointly, including the OLD task slot.
   This is not a production invariant, a complete tick call, or an ISR proof. *)
Theorem V293_tick_while_shared_records :
  forall bindings idle message current events now sd P ks ge le M ir enabled si ci O op
    ptcb rows group bc bg br g lo hi R,
  get le ptcb=Some (bc,Tptr V293_tcb_type) ->
  get le rows=None -> get ge rows=Some (br,Tarray Tint8 2) ->
  get le group=None -> get ge group=Some (bg,Tint8) ->
  (Int.unsigned (snd idle)+50<=Int.max_unsigned)%Z ->
  Forall V293_tick_binding_valid bindings -> NoDup (V293_tick_record_keys bindings idle) ->
  g<256 -> lo<256 -> hi<256 ->
  (ge,le,M,ir,(enabled,si,ci),O,op) |=
    V293_tick_loop_owned bc (V293_tick_head (map fst bindings) idle) (map fst bindings)
      idle bg br g lo hi
      (V293_owned_record_cells (concat (map V293_tick_binding_extra bindings)) **
        (V293_owned_record_cells (V293_tick_idle_extra idle message) **
          (V293_shared_fields current (V293_tick_record_map false bindings idle message) events now ** R))) ->
  V293_task_records M (V293_tick_record_map false bindings idle message) /\
  spec_stepstar sd (V293_tick_chain_code bindings) O (END None)
    (set O abstcblsid (abstcblist (V293_tick_record_map true bindings idle message))) /\
  (forall id, id<>abstcblsid ->
    get (set O abstcblsid (abstcblist (V293_tick_record_map true bindings idle message))) id=get O id) /\
  let '(gf,(lof,hif)) := V293_tick_chain_bitmap (map fst bindings) g lo hi in
  exists Mf,
  V293_local_steps P
    (curs (swhile (V293_tick_guard ptcb) (V293_tick_iteration ptcb rows group)),(kenil,ks))
    ((ge,le,M),ir,(enabled,si,ci))
    (curs (sskip None),(kenil,ks)) ((ge,le,Mf),ir,(enabled,si,ci)) /\
  load (Tptr V293_tcb_type) Mf (bc,0%Z)=Some (Vptr idle) /\
  V293_task_records Mf (V293_tick_record_map true bindings idle message) /\
  (ge,le,Mf,ir,(enabled,si,ci),
    set O abstcblsid (abstcblist (V293_tick_record_map true bindings idle message)),op) |=
    V293_owned_task_records (V293_tick_record_map true bindings idle message) **
    ((V293_owned_record_cell (V293_tick_pointer_cell bc idle) **
      (V293_owned_record_cells (V293_tick_bitmap_cells bg br gf lof hif) **
        (V293_shared_fields current (V293_tick_record_map true bindings idle message) events now ** R))) ** Atrue).
Proof.
  intros bindings idle message current events now sd P ks ge le M ir enabled si ci O op
    ptcb rows group bc bg br g lo hi R Bind Nr Gr Ng Gg IdleLimit Valid Unique G Lo Hi Owned.
  assert (OldJoint : (ge,le,M,ir,(enabled,si,ci),O,op) |=
    V293_owned_task_records (V293_tick_record_map false bindings idle message) ** Atrue).
  { assert (Converted : (ge,le,M,ir,(enabled,si,ci),O,op) |=
      V293_owned_task_records (V293_tick_record_map false bindings idle message) ** (Atrue ** Atrue)).
    { apply V293_tick_chain_records_before; [exact Valid | exact Unique | ].
      unfold V293_tick_loop_owned in Owned. clear -Owned. sep auto. }
    clear -Converted. sep auto. }
  assert (Old : V293_task_records M (V293_tick_record_map false bindings idle message)).
  { apply sat_split in OldJoint.
    destruct OldJoint as (m1 & m2 & o1 & o2 & JM & JO & Records & Frame).
    pose proof (V293_owned_task_records_sound _ _ Records) as All.
    intros t p st msg Lookup. eapply V293_task_record_sub; [exists m2;exact JM | ].
    apply All. exact Lookup. }
  assert (Slot : get O abstcblsid=Some (abstcblist (V293_tick_record_map false bindings idle message))).
  { assert (Held : (ge,le,M,ir,(enabled,si,ci),O,op) |=
      Aabsdata abstcblsid (abstcblist (V293_tick_record_map false bindings idle message)) ** Atrue).
    { unfold V293_tick_loop_owned,V293_shared_fields in Owned. clear -Owned. sep auto. }
    exact (V293_star_abst_get_l _ _ _ _ (V293_shared_abs_get _ _) _ Held). }
  split; [exact Old | ]. split.
  - apply V293_tick_record_chain_transition; assumption.
  - split.
    + intros id Apart. apply map_get_set'. congruence.
    + destruct (V293_tick_chain_bitmap (map fst bindings) g lo hi) as [gf [lof hif]] eqn:Bitmap.
      pose proof (V293_tick_while_owned_records bindings idle message P ks ge le M ir enabled si ci O op
        ptcb rows group bc bg br g lo hi
        (V293_shared_fields current (V293_tick_record_map false bindings idle message) events now ** R)
        Bind Nr Gr Ng Gg IdleLimit Valid Unique G Lo Hi Owned) as Run.
      rewrite Bitmap in Run. destruct Run as (Mf & Exec & Pointer & Records & Returned).
      exists Mf. split; [exact Exec | ]. split; [exact Pointer | ]. split; [exact Records | ].
      assert (Opened : (ge,le,Mf,ir,(enabled,si,ci),O,op) |=
        Aabsdata abstcblsid (abstcblist (V293_tick_record_map false bindings idle message)) **
        (V293_owned_task_records (V293_tick_record_map true bindings idle message) **
        ((V293_owned_record_cell (V293_tick_pointer_cell bc idle) **
          (V293_owned_record_cells (V293_tick_bitmap_cells bg br gf lof hif) **
          ((Aabsdata curtid (oscurt current) **
            (Aabsdata absecblsid (absecblist events) ** Aabsdata ostmid (ostm now))) ** R))) ** Atrue))).
      { unfold V293_shared_fields in Returned. clear -Returned. sep auto. }
      apply V293_shared_replace_slot with
        (new:=abstcblist (V293_tick_record_map true bindings idle message)) in Opened.
      unfold V293_shared_fields. clear -Opened. sep auto.
Qed.
