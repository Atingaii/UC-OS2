(* Raw, writable exit resources for another tick. Alternative packaging to
   canonical records: NEVER assert both copies of the same permission. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickReentry.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickWhileRecords.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickSuffix.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLoop.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickRawReadyReturn.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickPostHookReady.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickReadyChain.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.code.V293OSTimeTick.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickWhileShared.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickShared.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.
Local Open Scope list_scope.

Definition V293_tick_reentry_payload bindings idle message current events now entries
  bn bu bh bg br bp lo hi cells :=
  V293_owned_record_cells
    (((bn,0%Z),Tint32,Vint32 now) :: ((bu,0%Z),Tint8,V293_byteval 1) :: ((bh,0%Z),Tptr V293_tcb_type,Vptr (V293_tick_head (map fst bindings) idle)) :: nil) **
  (V293_owned_record_cells (V293_tick_chain_cells (map fst bindings) idle) **
    (V293_owned_record_cells (V293_tick_bitmap_cells bg br (V293_ready_group lo hi) lo hi) **
      (V293_owned_record_cell (V293_tick_idle_cell idle) **
        (V293_owned_record_cells (concat (map V293_tick_binding_extra bindings)) **
          (V293_owned_record_cells (V293_tick_idle_extra idle message) **
            (V293_owned_record_cells (V293_priority_cells bp 0%Z entries) **
              (V293_owned_record_cells cells **
                (CurTid current ** V293_shared_fields current
                  (V293_tick_record_map false bindings idle message) events now)))))))).

Lemma V293_tick_reentry_payload_context : forall bindings idle message current events now entries
  bn bu bh bg br bp lo hi cells ge le M ir aux O op caller,
  (ge,le,M,ir,aux,O,op) |= V293_tick_reentry_payload bindings idle message current events now entries
    bn bu bh bg br bp lo hi cells ->
  (ge,caller,M,ir,aux,O,op) |= V293_tick_reentry_payload bindings idle message current events now entries
    bn bu bh bg br bp lo hi cells.
Proof.
  intros bindings idle message current events now entries bn bu bh bg br bp lo hi cells
    ge le M ir aux O op caller Held.
  unfold V293_tick_reentry_payload in *.
  let rec transport H :=
    lazymatch goal with
    | |- _ |= V293_owned_record_cells _ => eapply V293_owned_cells_context;exact H
    | |- _ |= V293_shared_fields _ _ _ _ => eapply V293_shared_fields_rebase;exact H
    | |- _ |= V293_owned_record_cell _ => exact H
    | |- _ |= CurTid _ => exact H
    | |- _ |= _ ** _ =>
      let m1:=fresh "m1" in let m2:=fresh "m2" in
      let o1:=fresh "o1" in let o2:=fresh "o2" in
      let JM:=fresh "JM" in let JO:=fresh "JO" in
      let HL:=fresh "Left" in let HR:=fresh "Right" in
      apply sat_split in H;destruct H as (m1 & m2 & o1 & o2 & JM & JO & HL & HR);
      apply sat_split';exists m1;exists m2;exists o1;exists o2;
      split;[exact JM| ];split;[exact JO| ];split;[transport HL|transport HR]
    end
  in transport Held.

Qed.

(* Opening this payload with two ACTUALLY allocated local cells gives the
   original raw entry; no store/fresh allocation or second execution premise. *)
Lemma V293_tick_reentry_entry : forall bindings idle message current events now entries
  bn bu bh bg br bp lo hi cells bc bs ge le M ir aux O op,
  (ge,le,M,ir,aux,O,op) |=
    Amapsto (bc,0%Z) (Tptr V293_tcb_type) true Vundef **
      (V293_owned_record_cell ((bs,0%Z),Tint32,Vint32 Int.zero) **
        V293_tick_reentry_payload bindings idle message current events now entries
          bn bu bh bg br bp lo hi cells) ->
  (ge,le,M,ir,aux,O,op) |=
    V293_tick_storage_owned bn now bu 1 bh (V293_tick_head (map fst bindings) idle)
      bc Vundef (map fst bindings) idle bg br (V293_ready_group lo hi) lo hi
      (V293_owned_record_cells (concat (map V293_tick_binding_extra bindings)) **
        (V293_owned_record_cells (V293_tick_idle_extra idle message) **
          (V293_shared_fields current (V293_tick_record_map false bindings idle message) events now **
            (V293_owned_record_cells (V293_priority_cells bp 0%Z entries) **
              (V293_owned_record_cell ((bs,0%Z),Tint32,Vint32 Int.zero) **
                (V293_owned_record_cells cells ** CurTid current)))))).
Proof.
  intros. unfold V293_tick_reentry_payload,V293_tick_storage_owned in *.
  cbn [V293_owned_record_cells] in H. clear -H. sep auto.
Qed.

Theorem V293_tick_raw_reentry_return :
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
    Amapsto (bc,0%Z) (Tptr V293_tcb_type) true Vundef **
      (V293_owned_record_cell ((bs,0%Z),Tint32,Vint32 Int.zero) **
        V293_tick_reentry_payload bindings idle message current events now entries
          bn bu bh bg br bp lo hi cells) ->
  spec_stepstar sd (spec_seq V293_tick_clock_action (V293_tick_chain_code bindings)) O (END None)
    (set (set O ostmid (ostm (Int.add now Int.one))) abstcblsid
      (abstcblist (V293_tick_record_map false (map V293_tick_reentry_binding bindings) idle message))) /\
  Forall V293_tick_binding_valid (map V293_tick_reentry_binding bindings) /\
  NoDup (V293_tick_record_keys (map V293_tick_reentry_binding bindings) idle) /\
  let '(gf,(lof,hif)):=V293_tick_chain_bitmap (map fst bindings) (V293_ready_group lo hi) lo hi in
  V293_ready_rel lof hif entries
    (V293_tick_record_map false (map V293_tick_reentry_binding bindings) idle message) /\
  exists Ms Mf,
  V293_local_steps P
    (curs (sskip None),(kenil,kseq (V293_tick_post_hook ptcb rows group clock running head)
      (kseq sret (kcall f body caller ks))))
    ((ge,V293_tick_locals ptcb saved bc bs,M),ir,(enabled,si,ci))
    (curs (sskip None),(kenil,ks)) ((ge,caller,Mf),ir,(enabled,si,ci)) /\
  load Tint32 Ms (bn,0%Z)=Some (Vint32 (Int.add now Int.one)) /\
  load (Tptr V293_tcb_type) Ms (bc,0%Z)=Some (Vptr idle) /\
  (ge,caller,Mf,ir,(enabled,si,ci),
    set (set O ostmid (ostm (Int.add now Int.one))) abstcblsid
      (abstcblist (V293_tick_record_map false (map V293_tick_reentry_binding bindings) idle message)),op) |=
    V293_tick_reentry_payload (map V293_tick_reentry_binding bindings) idle message current events
      (Int.add now Int.one) entries bn bu bh bg br bp lof hif
      (concat (map V293_tick_reentry_orphan bindings) ++ cells) /\
  (forall b i, b<>bc -> b<>bs -> get Mf (b,i)=get Ms (b,i)) /\
  (forall k, k<4 -> get Mf (bc,Z.of_nat k)=None /\ get Mf (bs,Z.of_nat k)=None).
Proof.
  intros bindings idle message current events now entries sd P ks ge caller M ir enabled si ci O op
    ptcb saved rows group clock running head bc bs bn bu bh bg br bp lo hi f body cells
    Different Blocks Bind Nr Gr Ng Gg Nn Gn Nu Gu Nh Gh IdleLimit Valid Unique Rel Held.
  pose proof (V293_tick_reentry_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Held) as Owned.
  pose proof Rel as [Lo [Hi _]].
  assert (Fields : (ge,V293_tick_locals ptcb saved bc bs,M,ir,(enabled,si,ci),O,op) |=
    V293_shared_fields current (V293_tick_record_map false bindings idle message) events now ** Atrue)
    by (unfold V293_tick_reentry_payload in Held;clear -Held;sep auto).
  assert (Clock : get O ostmid=Some (ostm now)).
  { exact (V293_star_abst_get_l _ _ _ _
      (fun st H=>proj2 (proj2 (proj2 (V293_shared_fields_get _ _ _ _ st H)))) _ Fields). }
  assert (Tasks : get O abstcblsid=Some (abstcblist (V293_tick_record_map false bindings idle message))).
  { exact (V293_star_abst_get_l _ _ _ _
      (fun st H=>proj1 (proj2 (V293_shared_fields_get _ _ _ _ st H))) _ Fields). }
  split.
  - rewrite V293_tick_reentry_record_map. apply V293_tick_post_hook_transition;assumption.
  - split;[apply V293_tick_reentry_valid;exact Valid| ].
    split;[rewrite V293_tick_reentry_keys;exact Unique| ].
    assert (RawValid : Forall V293_tick_task_valid (map fst bindings)).
    { apply Forall_forall. intros t Member. apply in_map_iff in Member.
      destruct Member as (binding&Same&Member). subst t. rewrite Forall_forall in Valid.
      specialize (Valid binding Member). destruct binding as [t [status msg]]. exact (proj1 Valid). }
    pose proof (V293_tick_uninitialized_suffix_execution (map fst bindings) P
      (kseq sret (kcall f body caller ks)) ge (V293_tick_locals ptcb saved bc bs) M ir enabled si ci O op
      ptcb rows group clock running head bc bn bu bh idle bg br now 1 (V293_ready_group lo hi) lo hi _
      Bind Nr Gr Ng Gg Nn Gn Nu Gu Nh Gh IdleLimit RawValid ltac:(lia)
      ltac:(unfold V293_ready_group;destruct (lo=?0);destruct (hi=?0);lia) Lo Hi Owned) as Run.
    cbn [Nat.eqb] in Run.
    pose proof (V293_tick_record_chain_ready_rel bindings idle message lo hi entries Valid Unique Rel) as Pure.
    destruct (V293_tick_chain_bitmap (map fst bindings) (V293_ready_group lo hi) lo hi)
      as [gf [lof hif]] eqn:Bitmap.
    destruct Pure as [Group NewRel]. split;[rewrite V293_tick_reentry_record_map;exact NewRel| ].
    destruct Run as (Ms&Exec&Time&Pointer&Returned).
    assert (ExtraFirst : (ge,V293_tick_locals ptcb saved bc bs,Ms,ir,(enabled,si,ci),O,op) |=
      V293_owned_record_cells (concat (map V293_tick_binding_extra bindings)) **
      (V293_tick_storage_owned bn (Int.add now Int.one) bu 1 bh (V293_tick_head (map fst bindings) idle)
        bc (Vptr idle) (map V293_tick_task_after (map fst bindings)) idle bg br gf lof hif
        (V293_owned_record_cells (V293_tick_idle_extra idle message) **
          (V293_shared_fields current (V293_tick_record_map false bindings idle message) events now **
            (V293_owned_record_cells (V293_priority_cells bp 0%Z entries) **
              (V293_owned_record_cell ((bs,0%Z),Tint32,Vint32 Int.zero) **
                (V293_owned_record_cells cells ** CurTid current))))))).
    { unfold V293_tick_storage_owned in Returned |- *. clear -Returned. sep auto. }
    apply V293_tick_reentry_extras_owned in ExtraFirst.
    assert (SharedFirst : (ge,V293_tick_locals ptcb saved bc bs,Ms,ir,(enabled,si,ci),O,op) |=
      V293_shared_fields current (V293_tick_record_map false bindings idle message) events now **
      (Amapsto (bc,0%Z) (Tptr V293_tcb_type) true (Vptr idle) **
        (V293_owned_record_cell ((bs,0%Z),Tint32,Vint32 Int.zero) **
          (V293_owned_record_cells
            (((bn,0%Z),Tint32,Vint32 (Int.add now Int.one)) :: ((bu,0%Z),Tint8,V293_byteval 1) :: ((bh,0%Z),Tptr V293_tcb_type,Vptr (V293_tick_head (map fst bindings) idle)) :: nil) **
            (V293_owned_record_cells (V293_tick_chain_cells (map V293_tick_task_after (map fst bindings)) idle) **
              (V293_owned_record_cells (V293_tick_bitmap_cells bg br gf lof hif) **
                (V293_owned_record_cell (V293_tick_idle_cell idle) **
                  (V293_owned_record_cells (concat (map V293_tick_binding_extra (map V293_tick_reentry_binding bindings))) **
                    (V293_owned_record_cells (V293_tick_idle_extra idle message) **
                      (V293_owned_record_cells (V293_priority_cells bp 0%Z entries) **
                        ((V293_owned_record_cells (concat (map V293_tick_reentry_orphan bindings)) **
                          V293_owned_record_cells cells) ** CurTid current))))))))))).
    { unfold V293_tick_storage_owned in ExtraFirst. cbn [V293_owned_record_cells].
      clear -ExtraFirst. sep auto. }
    apply V293_tick_reentry_shared with
      (newtasks:=V293_tick_record_map false (map V293_tick_reentry_binding bindings) idle message)
      (newnow:=Int.add now Int.one) in SharedFirst.
    assert (ForFree : (ge,V293_tick_locals ptcb saved bc bs,Ms,ir,(enabled,si,ci),
      set (set O ostmid (ostm (Int.add now Int.one))) abstcblsid
        (abstcblist (V293_tick_record_map false (map V293_tick_reentry_binding bindings) idle message)),op) |=
      Amapsto (bc,0%Z) (Tptr V293_tcb_type) true (Vptr idle) **
        (Amapsto (bs,0%Z) Tint32 true (Vint32 Int.zero) **
          V293_tick_reentry_payload (map V293_tick_reentry_binding bindings) idle message current events
            (Int.add now Int.one) entries bn bu bh bg br bp lof hif
            (concat (map V293_tick_reentry_orphan bindings) ++ cells))).
    { unfold V293_tick_reentry_payload. rewrite V293_tick_reentry_head,V293_tick_reentry_nodes,<- Group.
      assert (Combined : (ge,V293_tick_locals ptcb saved bc bs,Ms,ir,(enabled,si,ci),
        set (set O ostmid (ostm (Int.add now Int.one))) abstcblsid
          (abstcblist (V293_tick_record_map false (map V293_tick_reentry_binding bindings) idle message)),op) |=
        V293_owned_record_cells (concat (map V293_tick_reentry_orphan bindings) ++ cells) **
          (V293_shared_fields current (V293_tick_record_map false (map V293_tick_reentry_binding bindings) idle message)
            events (Int.add now Int.one) **
            (Amapsto (bc,0%Z) (Tptr V293_tcb_type) true (Vptr idle) **
              (V293_owned_record_cell ((bs,0%Z),Tint32,Vint32 Int.zero) **
                (V293_owned_record_cells
                  (((bn,0%Z),Tint32,Vint32 (Int.add now Int.one)) :: ((bu,0%Z),Tint8,V293_byteval 1) :: ((bh,0%Z),Tptr V293_tcb_type,Vptr (V293_tick_head (map fst bindings) idle)) :: nil) **
                  (V293_owned_record_cells (V293_tick_chain_cells (map V293_tick_task_after (map fst bindings)) idle) **
                    (V293_owned_record_cells (V293_tick_bitmap_cells bg br gf lof hif) **
                      (V293_owned_record_cell (V293_tick_idle_cell idle) **
                        (V293_owned_record_cells (concat (map V293_tick_binding_extra (map V293_tick_reentry_binding bindings))) **
                          (V293_owned_record_cells (V293_tick_idle_extra idle message) **
                            (V293_owned_record_cells (V293_priority_cells bp 0%Z entries) ** CurTid current))))))))))).
      { eapply astar_mono;[ |intros st H;exact H| ].
        - intros st H. apply V293_tick_cells_append. exact H.
        - clear -SharedFirst. sep auto. }
      unfold V293_owned_record_cell in Combined |- *. clear -Combined. sep auto. }
    destruct (V293_tick_release_locals P ks ge caller Ms ir (enabled,si,ci) _ op f body
      ptcb saved bc bs (Vptr idle) (Vint32 Int.zero) _ Different Blocks ForFree)
      as (Mf&Return&After&Frame&Gone).
    exists Ms. exists Mf. split.
    + eapply V293_local_cons. { apply ostc_step. eapply stmt_step;[reflexivity|apply sskip_step]. }
      eapply V293_local_trans;[exact Exec| ].
      eapply V293_local_cons. { apply ostc_step. eapply stmt_step;[reflexivity|apply sskip_step]. }
      exact Return.
    + split;[exact Time| ]. split;[exact Pointer| ]. split.
      * eapply V293_tick_reentry_payload_context;exact After.
      * split;assumption.
Qed.
