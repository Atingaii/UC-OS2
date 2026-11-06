Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordInvariant.
(* One endpoint for the ORIGINAL post-hook running path: clock increment,
   exact OSRunning=1 test, head assignment, and the complete original while.
   Raw Vundef entry. CPU hook, interference and ISR installation remain open. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickPostHookReady.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickReadyChain.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickWhileShared.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickWhileRecords.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickShared.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickSuffix.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLoop.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.code.V293OSTimeTick.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

(* Stable interface. Initial scan is raw Vundef, NOT a typed pointer or prewritten head.
   Old record ownership is derived from the SAME entry, not duplicated.
   Abstract steps and concrete steps share endpoints, not per-step simulation. *)
Theorem V293_tick_raw_ready_payload :
  forall bindings idle message current events now entries sd P ks ge le M ir enabled si ci O op
    ptcb rows group clock running head bc bn bu bh bg br bp lo hi R,
  get le ptcb=Some (bc,Tptr V293_tcb_type) ->
  get le rows=None -> get ge rows=Some (br,Tarray Tint8 2) ->
  get le group=None -> get ge group=Some (bg,Tint8) ->
  get le clock=None -> get ge clock=Some (bn,Tint32) ->
  get le running=None -> get ge running=Some (bu,Tint8) ->
  get le head=None -> get ge head=Some (bh,Tptr V293_tcb_type) ->
  (Int.unsigned (snd idle)+50<=Int.max_unsigned)%Z ->
  Forall V293_tick_binding_valid bindings -> NoDup (V293_tick_record_keys bindings idle) ->
  V293_ready_rel lo hi entries (V293_tick_record_map false bindings idle message) ->
  (ge,le,M,ir,(enabled,si,ci),O,op) |=
    V293_tick_storage_owned bn now bu 1 bh (V293_tick_head (map fst bindings) idle)
      bc Vundef (map fst bindings) idle bg br (V293_ready_group lo hi) lo hi
      (V293_owned_record_cells (concat (map V293_tick_binding_extra bindings)) **
        (V293_owned_record_cells (V293_tick_idle_extra idle message) **
          (V293_shared_fields current (V293_tick_record_map false bindings idle message) events now **
            (V293_owned_record_cells (V293_priority_cells bp 0%Z entries) ** R)))) ->
  V293_task_records M (V293_tick_record_map false bindings idle message) /\
  spec_stepstar sd (spec_seq V293_tick_clock_action (V293_tick_chain_code bindings)) O (END None)
    (set (set O ostmid (ostm (Int.add now Int.one))) abstcblsid
      (abstcblist (V293_tick_record_map true bindings idle message))) /\
  (forall id, id<>ostmid -> id<>abstcblsid ->
    get (set (set O ostmid (ostm (Int.add now Int.one))) abstcblsid
      (abstcblist (V293_tick_record_map true bindings idle message))) id=get O id) /\
  let '(gf,(lof,hif)):=V293_tick_chain_bitmap (map fst bindings) (V293_ready_group lo hi) lo hi in
  exists Mf,
  V293_local_steps P
    (curs (V293_tick_post_hook ptcb rows group clock running head),(kenil,ks))
    ((ge,le,M),ir,(enabled,si,ci))
    (curs (sskip None),(kenil,ks)) ((ge,le,Mf),ir,(enabled,si,ci)) /\
  load Tint32 Mf (bn,0%Z)=Some (Vint32 (Int.add now Int.one)) /\
  load (Tptr V293_tcb_type) Mf (bc,0%Z)=Some (Vptr idle) /\
  V293_task_records Mf (V293_tick_record_map true bindings idle message) /\
  gf=V293_ready_group lof hif /\
  V293_ready_rel lof hif entries (V293_tick_record_map true bindings idle message) /\
  V293_ready_loads Mf br bg bp lof hif entries /\
  (ge,le,Mf,ir,(enabled,si,ci),
    set (set O ostmid (ostm (Int.add now Int.one))) abstcblsid
      (abstcblist (V293_tick_record_map true bindings idle message)),op) |=
    V293_ready_payload br bg bp (V293_tick_record_map true bindings idle message) **
    ((V293_owned_record_cell ((bn,0%Z),Tint32,Vint32 (Int.add now Int.one)) **
      (V293_owned_record_cell ((bu,0%Z),Tint8,V293_byteval 1) **
        (V293_owned_record_cell ((bh,0%Z),Tptr V293_tcb_type,Vptr (V293_tick_head (map fst bindings) idle)) **
          (V293_owned_record_cell (V293_tick_pointer_cell bc idle) **
            (V293_shared_fields current (V293_tick_record_map true bindings idle message) events
              (Int.add now Int.one) ** R))))) ** Atrue).
Proof.
  intros bindings idle message current events now entries sd P ks ge le M ir enabled si ci O op
    ptcb rows group clock running head bc bn bu bh bg br bp lo hi R
    Bind Nr Gr Ng Gg Nn Gn Nu Gu Nh Gh IdleLimit Valid Unique Rel Owned.
  pose proof Rel as [Lo [Hi _]].
  assert (OldJoint : (ge,le,M,ir,(enabled,si,ci),O,op) |=
    V293_owned_task_records (V293_tick_record_map false bindings idle message) ** (Atrue ** Atrue)).
  { apply V293_tick_chain_records_before;[exact Valid|exact Unique| ].
    unfold V293_tick_storage_owned in Owned. clear -Owned. sep auto. }
  assert (Old : V293_task_records M (V293_tick_record_map false bindings idle message)).
  { apply sat_split in OldJoint. destruct OldJoint as (m1&m2&o1&o2&JM&JO&Records&Frame).
    pose proof (V293_owned_task_records_sound _ _ Records) as All.
    intros t p st msg Lookup. eapply V293_task_record_sub;[exists m2;exact JM| ].
    apply All. exact Lookup. }
  assert (Fields : (ge,le,M,ir,(enabled,si,ci),O,op) |=
    V293_shared_fields current (V293_tick_record_map false bindings idle message) events now ** Atrue)
    by (unfold V293_tick_storage_owned in Owned;clear -Owned;sep auto).
  assert (Clock : get O ostmid=Some (ostm now)).
  { exact (V293_star_abst_get_l _ _ _ _
      (fun st H => proj2 (proj2 (proj2 (V293_shared_fields_get _ _ _ _ st H)))) _ Fields). }
  assert (Tasks : get O abstcblsid=Some (abstcblist (V293_tick_record_map false bindings idle message))).
  { exact (V293_star_abst_get_l _ _ _ _
      (fun st H => proj1 (proj2 (V293_shared_fields_get _ _ _ _ st H))) _ Fields). }
  split;[exact Old| ]. split;[apply V293_tick_post_hook_transition;assumption| ]. split.
  - intros id NotClock NotTasks. rewrite !map_get_set' by congruence. reflexivity.
  - assert (RawValid : Forall V293_tick_task_valid (map fst bindings)).
    { apply Forall_forall. intros t Member. apply in_map_iff in Member.
      destruct Member as (b&Same&Member). subst t. rewrite Forall_forall in Valid.
      specialize (Valid b Member). destruct b as [t [status msg]]. exact (proj1 Valid). }
    pose proof (V293_tick_uninitialized_suffix_execution (map fst bindings) P ks ge le M ir enabled si ci O op
      ptcb rows group clock running head bc bn bu bh idle bg br now 1 (V293_ready_group lo hi) lo hi _
      Bind Nr Gr Ng Gg Nn Gn Nu Gu Nh Gh IdleLimit RawValid ltac:(lia)
      ltac:(unfold V293_ready_group;destruct (lo=?0);destruct (hi=?0);lia) Lo Hi Owned) as Run.
    cbn [Nat.eqb] in Run.
    pose proof (V293_tick_record_chain_ready_rel bindings idle message lo hi entries Valid Unique Rel) as Pure.
    destruct (V293_tick_chain_bitmap (map fst bindings) (V293_ready_group lo hi) lo hi)
      as [gf [lof hif]] eqn:Bitmap.
    destruct Pure as [Group NewRel]. destruct Run as (Mf&Exec&Time&Pointer&Returned).
    assert (TypedReturned : (ge,le,Mf,ir,(enabled,si,ci),O,op) |=
      V293_tick_suffix_owned bn (Int.add now Int.one) bu 1 bh
        (V293_tick_head (map fst bindings) idle) bc idle
        (map V293_tick_task_after (map fst bindings)) idle bg br gf lof hif
        (V293_owned_record_cells (concat (map V293_tick_binding_extra bindings)) **
          (V293_owned_record_cells (V293_tick_idle_extra idle message) **
            (V293_shared_fields current (V293_tick_record_map false bindings idle message) events now **
              (V293_owned_record_cells (V293_priority_cells bp 0%Z entries) ** R))))).
    { unfold V293_tick_storage_owned in Returned.
      unfold V293_tick_suffix_owned,V293_tick_loop_owned,V293_tick_pointer_cell.
      eapply astar_mono;[intros st H;exact H| |exact Returned].
      intros st1 H1. eapply astar_mono;[intros st H;exact H| |exact H1].
      intros st2 H2. eapply astar_mono;[intros st H;exact H| |exact H2].
      intros st3 H3. eapply astar_mono;[ |intros st H;exact H|exact H3].
      intros st H. unfold V293_owned_record_cell. apply astar_l_apure_intro;[exact H|reflexivity]. }
    assert (Joint : (ge,le,Mf,ir,(enabled,si,ci),O,op) |=
      V293_owned_task_records (V293_tick_record_map true bindings idle message) **
      ((V293_owned_record_cell ((bn,0%Z),Tint32,Vint32 (Int.add now Int.one)) **
        (V293_owned_record_cell ((bu,0%Z),Tint8,V293_byteval 1) **
          (V293_owned_record_cell ((bh,0%Z),Tptr V293_tcb_type,Vptr (V293_tick_head (map fst bindings) idle)) **
            (V293_owned_record_cell (V293_tick_pointer_cell bc idle) **
              (V293_owned_record_cells (V293_tick_bitmap_cells bg br gf lof hif) **
                (V293_shared_fields current (V293_tick_record_map false bindings idle message) events now **
                  (V293_owned_record_cells (V293_priority_cells bp 0%Z entries) ** R))))))) ** Atrue)).
    { apply V293_tick_chain_records_after;[exact Valid|exact Unique| ].
      unfold V293_tick_suffix_owned,V293_tick_loop_owned in TypedReturned. clear -TypedReturned. sep auto. }
    assert (Records : V293_task_records Mf (V293_tick_record_map true bindings idle message)).
    { apply sat_split in Joint. destruct Joint as (m1&m2&o1&o2&JM&JO&Held&Frame).
      pose proof (V293_owned_task_records_sound _ _ Held) as All.
      intros t p st msg Lookup. eapply V293_task_record_sub;[exists m2;exact JM| ].
      apply All. exact Lookup. }
    assert (Opened : (ge,le,Mf,ir,(enabled,si,ci),O,op) |=
      Aabsdata ostmid (ostm now) **
      (Aabsdata abstcblsid (abstcblist (V293_tick_record_map false bindings idle message)) **
        (V293_owned_task_records (V293_tick_record_map true bindings idle message) **
          ((V293_owned_record_cell ((bn,0%Z),Tint32,Vint32 (Int.add now Int.one)) **
            (V293_owned_record_cell ((bu,0%Z),Tint8,V293_byteval 1) **
              (V293_owned_record_cell ((bh,0%Z),Tptr V293_tcb_type,Vptr (V293_tick_head (map fst bindings) idle)) **
                (V293_owned_record_cell (V293_tick_pointer_cell bc idle) **
                  (V293_owned_record_cells (V293_tick_bitmap_cells bg br gf lof hif) **
                    ((Aabsdata curtid (oscurt current) ** Aabsdata absecblsid (absecblist events)) **
                      (V293_owned_record_cells (V293_priority_cells bp 0%Z entries) ** R))))))) ** Atrue)))).
    { unfold V293_shared_fields in Joint. clear -Joint. sep auto. }
    apply V293_shared_replace_slot with (new:=ostm (Int.add now Int.one)) in Opened.
    assert (ToTasks : (ge,le,Mf,ir,(enabled,si,ci),set O ostmid (ostm (Int.add now Int.one)),op) |=
      Aabsdata abstcblsid (abstcblist (V293_tick_record_map false bindings idle message)) **
      (Aabsdata ostmid (ostm (Int.add now Int.one)) **
        (V293_owned_task_records (V293_tick_record_map true bindings idle message) **
          ((V293_owned_record_cell ((bn,0%Z),Tint32,Vint32 (Int.add now Int.one)) **
            (V293_owned_record_cell ((bu,0%Z),Tint8,V293_byteval 1) **
              (V293_owned_record_cell ((bh,0%Z),Tptr V293_tcb_type,Vptr (V293_tick_head (map fst bindings) idle)) **
                (V293_owned_record_cell (V293_tick_pointer_cell bc idle) **
                  (V293_owned_record_cells (V293_tick_bitmap_cells bg br gf lof hif) **
                    ((Aabsdata curtid (oscurt current) ** Aabsdata absecblsid (absecblist events)) **
                      (V293_owned_record_cells (V293_priority_cells bp 0%Z entries) ** R))))))) ** Atrue)))).
    { clear -Opened. sep auto. }
    apply V293_shared_replace_slot with
      (new:=abstcblist (V293_tick_record_map true bindings idle message)) in ToTasks.
    rewrite Group in ToTasks.
    assert (Combined : (ge,le,Mf,ir,(enabled,si,ci),
      set (set O ostmid (ostm (Int.add now Int.one))) abstcblsid
        (abstcblist (V293_tick_record_map true bindings idle message)),op) |=
      (V293_owned_task_records (V293_tick_record_map true bindings idle message) **
        V293_owned_record_cells (V293_ready_cells br bg bp lof hif entries)) **
      ((V293_owned_record_cell ((bn,0%Z),Tint32,Vint32 (Int.add now Int.one)) **
        (V293_owned_record_cell ((bu,0%Z),Tint8,V293_byteval 1) **
          (V293_owned_record_cell ((bh,0%Z),Tptr V293_tcb_type,Vptr (V293_tick_head (map fst bindings) idle)) **
            (V293_owned_record_cell (V293_tick_pointer_cell bc idle) **
              (V293_shared_fields current (V293_tick_record_map true bindings idle message) events
                (Int.add now Int.one) ** R))))) ** Atrue)).
    { unfold V293_tick_bitmap_cells,V293_ready_cells,V293_shared_fields in ToTasks |- *.
      cbn [app V293_owned_record_cells] in ToTasks |- *. clear -ToTasks. sep auto. }
    exists Mf. split;[exact Exec| ]. split;[exact Time| ]. split;[exact Pointer| ].
    split;[exact Records| ]. split;[exact Group| ]. split;[exact NewRel| ]. split.
    + assert (Cells : (ge,le,Mf,ir,(enabled,si,ci),
        set (set O ostmid (ostm (Int.add now Int.one))) abstcblsid
          (abstcblist (V293_tick_record_map true bindings idle message)),op) |=
        V293_owned_record_cells (V293_ready_cells br bg bp lof hif entries) ** Atrue)
        by (clear -Combined;sep auto).
      apply sat_split in Cells. destruct Cells as (m1&m2&o1&o2&JM&JO&Cells&Frame).
      eapply V293_ready_loads_sub;[exists m2;exact JM| ].
      exact (V293_ready_cells_loads br bg bp lof hif entries
        (ge,le,m1,ir,(enabled,si,ci),o1,op)
        (proj1 (proj2 (proj2 (proj2 (proj2 NewRel))))) Cells).
    + unfold V293_ready_payload.
      eapply astar_mono;[ |intros st H;exact H|exact Combined].
      intros st H. eapply astar_mono;[intros st0 H0;exact H0| |exact H].
      intros st0 H0. exists lof. exists hif. exists entries.
      apply astar_l_apure_intro;[exact H0|exact NewRel].
Qed.

(* Exact byte-footprint release, including a raw Vundef slot. R remains in
   the SAME environment here; no arbitrary assertion changes its context. *)
Lemma V293_tick_release_slot : forall ge le M ir aux O op b tp v R,
  (ge,le,M,ir,aux,O,op) |= Amapsto (b,0%Z) tp true v ** R ->
  exists Mf, free tp b M=Some Mf /\ (ge,le,Mf,ir,aux,O,op) |= R.
Proof.
  intros ge le M ir aux O op b tp v R Held.
  apply sat_split in Held. destruct Held as (local&rest&ol&orest&JM&JO&[Slot Empty]&Rest).
  change (ol=emp) in Empty. subst ol. apply map_join_comm in JO. apply map_join_emp' in JO. subst orest.
  destruct Slot as (bytes&Encoding&Points).
  exists rest. split;[ |exact Rest]. unfold free.
  rewrite <- (encode_val_length tp v),Encoding.
  apply free_locality2' with (M1:=local);assumption.
Qed.

Lemma V293_tick_release_two : forall P ks ge le caller M ir aux O op f body b1 t1 v1 b2 t2 v2 R,
  getaddr le=[(b1,t1);(b2,t2)] -> b1<>b2 ->
  (ge,le,M,ir,aux,O,op) |=
    Amapsto (b1,0%Z) t1 true v1 ** (Amapsto (b2,0%Z) t2 true v2 ** R) ->
  exists Mf,
    V293_local_steps P (curs sret,(kenil,kcall f body caller ks)) ((ge,le,M),ir,aux)
      (curs (sskip None),(kenil,ks)) ((ge,caller,Mf),ir,aux) /\
    (ge,le,Mf,ir,aux,O,op) |= R /\
    (forall b i, b<>b1 -> b<>b2 -> get Mf (b,i)=get M (b,i)) /\
    (forall k, k<typelen t1 -> get Mf (b1,Z.of_nat k)=None) /\
    (forall k, k<typelen t2 -> get Mf (b2,Z.of_nat k)=None).
Proof.
  intros P ks ge le caller M ir aux O op f body b1 t1 v1 b2 t2 v2 R Layout Different Held.
  destruct (V293_tick_release_slot _ _ _ _ _ _ _ _ _ _ _ Held) as (M1&Free1&Held1).
  destruct (V293_tick_release_slot _ _ _ _ _ _ _ _ _ _ _ Held1) as (Mf&Free2&Rest).
  exists Mf. split.
  - eapply V293_local_cons.
    { apply ostc_step. eapply stmt_step;[reflexivity| ].
      eapply sret_step with (al:=[(b1,t1);(b2,t2)]);[reflexivity|reflexivity|exact Layout]. }
    eapply V293_local_cons.
    { apply ostc_step. eapply stmt_step;[reflexivity| ]. eapply sfree_step;[reflexivity|reflexivity|exact Free1]. }
    eapply V293_local_cons.
    { apply ostc_step. eapply stmt_step;[reflexivity| ]. eapply sfree_step;[reflexivity|reflexivity|exact Free2]. }
    eapply V293_local_cons.
    { apply ostc_step. eapply stmt_step;[reflexivity| ]. eapply sfreeend_step;reflexivity. }
    apply V293_local_refl.
  - split;[exact Rest| ]. split.
    + intros b i D1 D2. etransitivity;
        eapply V293_freeb_outside;[exact Free2|left;exact D2|exact Free1|left;exact D1].
    + split.
      * intros k K. rewrite (V293_freeb_outside _ _ _ _ _ _ _ Free2 (or_introl Different)).
        replace (Z.of_nat k) with (0+Z.of_nat k)%Z by lia. eapply V293_freeb_removed;[exact Free1|exact K].
      * intros k K. replace (Z.of_nat k) with (0+Z.of_nat k)%Z by lia.
        eapply V293_freeb_removed;[exact Free2|exact K].
Qed.

Lemma V293_tick_release_locals : forall P ks ge caller M ir aux O op f body ptcb saved bc bs scan value R,
  ptcb<>saved -> bc<>bs ->
  (ge,V293_tick_locals ptcb saved bc bs,M,ir,aux,O,op) |=
    Amapsto (bc,0%Z) (Tptr V293_tcb_type) true scan ** (Amapsto (bs,0%Z) Tint32 true value ** R) ->
  exists Mf,
    V293_local_steps P (curs sret,(kenil,kcall f body caller ks))
      ((ge,V293_tick_locals ptcb saved bc bs,M),ir,aux)
      (curs (sskip None),(kenil,ks)) ((ge,caller,Mf),ir,aux) /\
    (ge,V293_tick_locals ptcb saved bc bs,Mf,ir,aux,O,op) |= R /\
    (forall b i, b<>bc -> b<>bs -> get Mf (b,i)=get M (b,i)) /\
    (forall k, k<4 -> get Mf (bc,Z.of_nat k)=None /\ get Mf (bs,Z.of_nat k)=None).
Proof.
  intros P ks ge caller M ir aux O op f body ptcb saved bc bs scan value R Different Blocks Held.
  assert (Layouts : getaddr (V293_tick_locals ptcb saved bc bs)=[(bc,Tptr V293_tcb_type);(bs,Tint32)] \/
    getaddr (V293_tick_locals ptcb saved bc bs)=[(bs,Tint32);(bc,Tptr V293_tcb_type)]).
  { unfold V293_tick_locals.
    change (getaddr (EnvMod.set (EnvMod.set EnvMod.emp ptcb (bc,Tptr V293_tcb_type)) saved (bs,Tint32))=[(bc,Tptr V293_tcb_type);(bs,Tint32)] \/
      getaddr (EnvMod.set (EnvMod.set EnvMod.emp ptcb (bc,Tptr V293_tcb_type)) saved (bs,Tint32))=[(bs,Tint32);(bc,Tptr V293_tcb_type)]).
    cbn [EnvMod.set EnvMod.lst EnvMod.set' EnvMod.emp EnvMod.emp' getaddr getaddrlist].
    destruct (identspec.blt saved ptcb);[right;reflexivity| ].
    rewrite identspec.neq_beq_false by congruence. left;reflexivity. }
  destruct Layouts as [Layout|Layout].
  - destruct (V293_tick_release_two P ks _ _ caller _ _ _ _ _ f body _ _ _ _ _ _ R Layout Blocks Held)
      as (Mf&Exec&Rest&Frame&Gone1&Gone2).
    exists Mf. split;[exact Exec| ]. split;[exact Rest| ]. split;[exact Frame| ]. intros k K. split;auto.
  - assert (Reordered : (ge,V293_tick_locals ptcb saved bc bs,M,ir,aux,O,op) |=
      Amapsto (bs,0%Z) Tint32 true value ** (Amapsto (bc,0%Z) (Tptr V293_tcb_type) true scan ** R))
      by (clear -Held;sep auto).
    destruct (V293_tick_release_two P ks _ _ caller _ _ _ _ _ f body _ _ _ _ _ _ R Layout ltac:(congruence) Reordered)
      as (Mf&Exec&Rest&Frame&Gone1&Gone2).
    exists Mf. split;[exact Exec| ]. split;[exact Rest| ]. split.
    + intros b i D1 D2. apply Frame;assumption.
    + intros k K. split;auto.
Qed.

Definition V293_tick_return_payload br bg bp tasks bn now bu bh head current events cells :=
  (V293_ready_payload br bg bp tasks **
    (V293_owned_record_cells
      ([((bn,0%Z),Tint32,Vint32 now);((bu,0%Z),Tint8,V293_byteval 1);
        ((bh,0%Z),Tptr V293_tcb_type,Vptr head)] ++ cells) **
      V293_shared_fields current tasks events now)) ** Atrue.

Lemma V293_tick_return_payload_context : forall br bg bp tasks bn now bu bh head current events cells
  ge le M ir aux O op ge' le',
  (ge,le,M,ir,aux,O,op) |= V293_tick_return_payload br bg bp tasks bn now bu bh head current events cells ->
  (ge',le',M,ir,aux,O,op) |= V293_tick_return_payload br bg bp tasks bn now bu bh head current events cells.
Proof.
  intros br bg bp tasks bn now bu bh head current events cells ge le M ir aux O op ge' le' Held.
  unfold V293_tick_return_payload in *.
  apply sat_split in Held. destruct Held as (m1&m2&o1&o2&JM&JO&Core&Rest).
  apply sat_split'. exists m1. exists m2. exists o1. exists o2.
  split;[exact JM| ]. split;[exact JO| ]. split;[ |exact I].
  apply sat_split in Core. destruct Core as (m3&m4&o3&o4&JM1&JO1&Ready&Fields).
  apply sat_split'. exists m3. exists m4. exists o3. exists o4.
  split;[exact JM1| ]. split;[exact JO1| ]. split;[eapply V293_ready_payload_context;exact Ready| ].
  apply sat_split in Fields. destruct Fields as (m5&m6&o5&o6&JM2&JO2&Cells&Fields).
  apply sat_split'. exists m5. exists m6. exists o5. exists o6.
  split;[exact JM2| ]. split;[exact JO2| ]. split.
  - eapply V293_owned_cells_context;exact Cells.
  - eapply V293_shared_fields_rebase;exact Fields.
Qed.

(* Stable post-hook return interface; the CPU hook is not bypassed or modeled as skip. *)
Theorem V293_tick_raw_ready_return :
  forall bindings idle message current events now entries sd P ks ge caller M ir enabled si ci O op
    ptcb saved rows group clock running head bc bs bn bu bh bg br bp lo hi f body cells,
  ptcb<>saved -> bc<>bs ->
  get (V293_tick_locals ptcb saved bc bs) ptcb=Some (bc,Tptr V293_tcb_type) ->
  get (V293_tick_locals ptcb saved bc bs) rows=None -> get ge rows=Some (br,Tarray Tint8 2) ->
  get (V293_tick_locals ptcb saved bc bs) group=None -> get ge group=Some (bg,Tint8) ->
  get (V293_tick_locals ptcb saved bc bs) clock=None -> get ge clock=Some (bn,Tint32) ->
  get (V293_tick_locals ptcb saved bc bs) running=None -> get ge running=Some (bu,Tint8) ->
  get (V293_tick_locals ptcb saved bc bs) head=None -> get ge head=Some (bh,Tptr V293_tcb_type) ->
  (Int.unsigned (snd idle)+50<=Int.max_unsigned)%Z ->
  Forall V293_tick_binding_valid bindings -> NoDup (V293_tick_record_keys bindings idle) ->
  V293_ready_rel lo hi entries (V293_tick_record_map false bindings idle message) ->
  (ge,V293_tick_locals ptcb saved bc bs,M,ir,(enabled,si,ci),O,op) |=
    V293_tick_storage_owned bn now bu 1 bh (V293_tick_head (map fst bindings) idle)
      bc Vundef (map fst bindings) idle bg br (V293_ready_group lo hi) lo hi
      (V293_owned_record_cells (concat (map V293_tick_binding_extra bindings)) **
        (V293_owned_record_cells (V293_tick_idle_extra idle message) **
          (V293_shared_fields current (V293_tick_record_map false bindings idle message) events now **
            (V293_owned_record_cells (V293_priority_cells bp 0%Z entries) **
              (V293_owned_record_cell ((bs,0%Z),Tint32,Vint32 Int.zero) ** V293_owned_record_cells cells))))) ->
  V293_task_records M (V293_tick_record_map false bindings idle message) /\
  spec_stepstar sd (spec_seq V293_tick_clock_action (V293_tick_chain_code bindings)) O (END None)
    (set (set O ostmid (ostm (Int.add now Int.one))) abstcblsid
      (abstcblist (V293_tick_record_map true bindings idle message))) /\
  (forall id, id<>ostmid -> id<>abstcblsid ->
    get (set (set O ostmid (ostm (Int.add now Int.one))) abstcblsid
      (abstcblist (V293_tick_record_map true bindings idle message))) id=get O id) /\
  let '(gf,(lof,hif)):=V293_tick_chain_bitmap (map fst bindings) (V293_ready_group lo hi) lo hi in
  exists Ms Mf,
  V293_local_steps P
    (curs (sskip None),(kenil,kseq (V293_tick_post_hook ptcb rows group clock running head)
      (kseq sret (kcall f body caller ks))))
    ((ge,V293_tick_locals ptcb saved bc bs,M),ir,(enabled,si,ci))
    (curs (sskip None),(kenil,ks)) ((ge,caller,Mf),ir,(enabled,si,ci)) /\
  load Tint32 Ms (bn,0%Z)=Some (Vint32 (Int.add now Int.one)) /\
  load (Tptr V293_tcb_type) Ms (bc,0%Z)=Some (Vptr idle) /\
  V293_task_records Ms (V293_tick_record_map true bindings idle message) /\
  gf=V293_ready_group lof hif /\
  V293_ready_rel lof hif entries (V293_tick_record_map true bindings idle message) /\
  V293_ready_loads Ms br bg bp lof hif entries /\
  (ge,caller,Mf,ir,(enabled,si,ci),
    set (set O ostmid (ostm (Int.add now Int.one))) abstcblsid
      (abstcblist (V293_tick_record_map true bindings idle message)),op) |=
    V293_tick_return_payload br bg bp (V293_tick_record_map true bindings idle message)
      bn (Int.add now Int.one) bu bh (V293_tick_head (map fst bindings) idle) current events cells /\
  (forall b i, b<>bc -> b<>bs -> get Mf (b,i)=get Ms (b,i)) /\
  (forall k, k<4 -> get Mf (bc,Z.of_nat k)=None /\ get Mf (bs,Z.of_nat k)=None).
Proof.
  intros bindings idle message current events now entries sd P ks ge caller M ir enabled si ci O op
    ptcb saved rows group clock running head bc bs bn bu bh bg br bp lo hi f body cells
    Different Blocks Bind Nr Gr Ng Gg Nn Gn Nu Gu Nh Gh IdleLimit Valid Unique Rel Owned.
  pose proof (V293_tick_raw_ready_payload bindings idle message current events now entries sd P
    (kseq sret (kcall f body caller ks)) ge (V293_tick_locals ptcb saved bc bs) M ir enabled si ci O op
    ptcb rows group clock running head bc bn bu bh bg br bp lo hi _
    Bind Nr Gr Ng Gg Nn Gn Nu Gu Nh Gh IdleLimit Valid Unique Rel Owned) as Run.
  destruct Run as (Old&Abstract&Slots&Run).
  split;[exact Old| ]. split;[exact Abstract| ]. split;[exact Slots| ].
  destruct (V293_tick_chain_bitmap (map fst bindings) (V293_ready_group lo hi) lo hi) as [gf [lof hif]].
  destruct Run as (Ms&Exec&Time&Pointer&Records&Group&NewRel&Loads&Joint).
  assert (ForFree : (ge,V293_tick_locals ptcb saved bc bs,Ms,ir,(enabled,si,ci),
    set (set O ostmid (ostm (Int.add now Int.one))) abstcblsid
      (abstcblist (V293_tick_record_map true bindings idle message)),op) |=
    Amapsto (bc,0%Z) (Tptr V293_tcb_type) true (Vptr idle) **
    (Amapsto (bs,0%Z) Tint32 true (Vint32 Int.zero) **
      V293_tick_return_payload br bg bp (V293_tick_record_map true bindings idle message)
        bn (Int.add now Int.one) bu bh (V293_tick_head (map fst bindings) idle) current events cells)).
  { unfold V293_tick_return_payload. cbn [app V293_owned_record_cells].
    unfold V293_tick_pointer_cell,V293_owned_record_cell in Joint |- *.
    clear -Joint. sep auto. }
  destruct (V293_tick_release_locals P ks ge caller Ms ir (enabled,si,ci) _ op f body
    ptcb saved bc bs (Vptr idle) (Vint32 Int.zero) _ Different Blocks ForFree)
    as (Mf&Return&After&Frame&Gone).
  exists Ms. exists Mf. split.
  - eapply V293_local_cons. { apply ostc_step. eapply stmt_step;[reflexivity|apply sskip_step]. }
    eapply V293_local_trans;[exact Exec| ].
    eapply V293_local_cons. { apply ostc_step. eapply stmt_step;[reflexivity|apply sskip_step]. }
    exact Return.
  - split;[exact Time| ]. split;[exact Pointer| ]. split;[exact Records| ].
    split;[exact Group| ]. split;[exact NewRel| ]. split;[exact Loads| ]. split.
    + eapply V293_tick_return_payload_context;exact After.
    + split;assumption.
Qed.
