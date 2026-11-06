Require Import CertiOS.certiucos.v293.proofs.V293TimeTickReentry.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickReentryReturn.
Require Import CertiOS.audit.probes.V293TimeTickLosslessReturnProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickTaskBridge.
Require Import CertiOS.audit.probes.V293TimeTickRawReadyReturnProbe.
Require Import CertiOS.tactics.basetac.perm_map_lemmas_part4.
Require Import CertiOS.tactics.basetac.perm_map_lemmas_part1.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLosslessFields.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLosslessReturn.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
(* Real allocation/initialization and a separate post-hook return checkpoint.
   These traces are NOT joined across the still-open CPU hook. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickRawReadyReturn.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordInvariant.
Require Import CertiOS.audit.probes.V293TimeTickPostHookReadyProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickPostHookReady.
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
Require Import CertiOS.certiucos.v293.proofs.V293SharedStateWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.code.V293OSTimeTick.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.audit.probes.V293TimeTickReadyChainProbe.
Require Import CertiOS.audit.probes.V293TimeTickWhileSharedProbe.
Require Import CertiOS.audit.probes.V293TimeTickWhileRecordsProbe.
Require Import CertiOS.audit.probes.V293TimeTickTraversalProbe.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

(* Exact heap support: freshness is derived from the FIRST actual result. *)
Lemma RPbytes_outside : forall bytes b off permission M b' i,
  b'<>b -> ptomvallist (b,off) permission bytes M -> get M (b',i)=None.
Proof.
  induction bytes as [ |v bytes IH];intros b off permission M b' i Different Held.
  - cbn in Held. subst M. apply map_emp_get.
  - cbn in Held. destruct Held as (m0&mt&JM&Byte&Rest).
    unfold ptomval in Byte. subst m0.
    eapply mem_join_get_none;[ |eapply IH;[exact Different|exact Rest]|exact JM].
    apply map_get_sig'. intro E. inversion E. congruence.
Qed.
Lemma RPcell_outside : forall cell ge le M ir aux O op b i,
  b<>fst (fst (fst cell)) ->
  (ge,le,M,ir,aux,O,op) |= V293_owned_record_cell cell -> get M (b,i)=None.
Proof.
  intros [[a tp] v] ge le M ir aux O op b i Different Held.
  unfold V293_owned_record_cell in Held. apply astar_l_apure_elim in Held.
  destruct Held as [_ [Points Empty]].
  destruct Points as (bytes&Encoding&Bytes). destruct a as [ab off].
  eapply RPbytes_outside;[exact Different|exact Bytes].
Qed.
Lemma RPcells_outside : forall cells ge le M ir aux O op b i,
  Forall (fun cell=>b<>fst (fst (fst cell))) cells ->
  (ge,le,M,ir,aux,O,op) |= V293_owned_record_cells cells -> get M (b,i)=None.
Proof.
  induction cells as [ |cell cells IH];intros ge le M ir aux O op b i Outside Held.
  - cbn in Held. destruct Held as [Empty _]. subst M. apply map_emp_get.
  - inversion Outside;subst. apply sat_split in Held.
    destruct Held as (m1&m2&o1&o2&JM&JO&HC&HT).
    eapply mem_join_get_none;[eapply RPcell_outside; eassumption|eapply IH;eassumption|exact JM].
Qed.
Lemma RPcurrent_outside : forall le M ir aux O op b i,
  b<>105%positive -> (LRglobal,le,M,ir,aux,O,op) |= CurTid WhileReady -> get M (b,i)=None.
Proof.
  intros le M ir aux O op b i Different [tp Hc]. unfold Agvarmapsto in Hc.
  destruct Hc as [ab Hc]. apply sat_split in Hc.
  destruct Hc as (m1&m2&o1&o2&JM&JO&[b0 [GE [EA [EM EO]]]]&[HP HA]).
  cbn in *. subst m1. inversion EA;subst b0.
  assert (ab=105%positive). { change (Some (105%positive,Tptr Tvoid)=Some (ab,Tptr tp)) in GE. inversion GE. reflexivity. }
  subst ab. destruct HP as (bytes&Encoding&Bytes).
  eapply mem_join_get_none;[apply map_emp_get|eapply RPbytes_outside;[exact Different|exact Bytes]|exact JM].
Qed.
Definition RPcells bindings now lo hi cells :=
  (((101%positive,0%Z),Tint32,Vint32 now)::
   ((102%positive,0%Z),Tint8,V293_byteval 1)::
   ((103%positive,0%Z),Tptr V293_tcb_type,Vptr (V293_tick_head (map fst bindings) WhileIdle))::nil) ++
  V293_tick_chain_cells (map fst bindings) WhileIdle ++
  V293_tick_bitmap_cells 92%positive 93%positive (V293_ready_group lo hi) lo hi ++
  V293_tick_idle_cell WhileIdle::
  (concat (map V293_tick_binding_extra bindings) ++ V293_tick_idle_extra WhileIdle Vnull ++
   V293_priority_cells 94%positive 0%Z RCentries ++ cells).
Definition RPpayload bindings now lo hi cells :=
  V293_tick_reentry_payload bindings WhileIdle Vnull WhileReady ChainEvents now
    RCentries 101%positive 102%positive 103%positive 92%positive 93%positive 94%positive lo hi cells.
Lemma RPpayload_fresh : forall bindings now lo hi cells le M O,
  Forall (fun cell=>70%positive<>fst (fst (fst cell)) /\ 71%positive<>fst (fst (fst cell)))
    (RPcells bindings now lo hi cells) ->
  LRstate le M O |= RPpayload bindings now lo hi cells ->
  fresh M 70%positive /\ fresh (allocb M 70%positive 0%Z 4) 71%positive.
Proof.
  intros bindings now lo hi cells le M O Support Held.
  assert (Outside : forall b i, b=70%positive \/ b=71%positive -> get M (b,i)=None).
  { intros b i Which.
    assert (All : Forall (fun cell=>b<>fst (fst (fst cell))) (RPcells bindings now lo hi cells)).
    { eapply Forall_impl;[ |exact Support]. intros cell [H70 H71]. destruct Which;subst b;assumption. }
    unfold RPcells in All.
    repeat first [
      match goal with H : _ /\ _ |- _ => destruct H end |
      match goal with H : Forall _ (_::_) |- _ => inversion H;clear H;subst end |
      progress rewrite Forall_app in *].
    unfold RPpayload,V293_tick_reentry_payload,LRstate,V293_shared_fields in Held.
    let rec outside H :=
      lazymatch type of H with
      | _ |= V293_owned_record_cells ?cs => eapply RPcells_outside;[ |exact H];solve [repeat first [assumption|apply Forall_nil|apply Forall_cons]]
      | _ |= V293_owned_record_cell _ => eapply RPcell_outside;[ |exact H];tauto
      | _ |= CurTid _ => eapply RPcurrent_outside;[destruct Which;subst b;discriminate|exact H]
      | _ |= Aabsdata _ _ =>
        let E:=fresh "Empty" in destruct H as [_ E];cbn in E;rewrite E;apply map_emp_get
      | _ |= _ ** _ =>
        let m1:=fresh "m1" in let m2:=fresh "m2" in let o1:=fresh "o1" in let o2:=fresh "o2" in
        let JM:=fresh "JM" in let JO:=fresh "JO" in let HL:=fresh "HL" in let HR:=fresh "HR" in
        apply sat_split in H;destruct H as (m1&m2&o1&o2&JM&JO&HL&HR);
        eapply (mem_join_get_none m1 m2 _ _);[outside HL|outside HR|exact JM]
      end
    in outside Held. }
  split.
  - intros l i E [v Bound]. subst l. change (get M (70%positive,i)=Some v) in Bound.
    rewrite Outside in Bound by auto. discriminate.
  - intros l i E [v Bound]. subst l.
    change (get (allocb M 70%positive 0%Z 4) (71%positive,i)=Some v) in Bound.
    rewrite V293_success_allocb_outside in Bound by (left;discriminate).
    change (get M (71%positive,i)=Some v) in Bound.
    rewrite Outside in Bound by auto. discriminate.
Qed.
Definition RPallocated bindings now lo hi cells M O := LRstate LRlocal M O |=
  Amapsto (70%positive,0%Z) (Tptr V293_tcb_type) true Vundef **
  (V293_owned_record_cell ((71%positive,0%Z),Tint32,Vint32 Int.zero) ** RPpayload bindings now lo hi cells).
Definition RPnextO O bindings now := set (set O ostmid (ostm (Int.add now Int.one))) abstcblsid
  (abstcblist (V293_tick_record_map false (map V293_tick_reentry_binding bindings) WhileIdle Vnull)).
Lemma RPstep : forall (sd:ossched) P ks bindings now lo hi cells M O lof hif,
  Forall V293_tick_binding_valid bindings -> NoDup (V293_tick_record_keys bindings WhileIdle) ->
  V293_ready_rel lo hi RCentries (V293_tick_record_map false bindings WhileIdle Vnull) ->
  V293_tick_chain_bitmap (map fst bindings) (V293_ready_group lo hi) lo hi=(3,(lof,hif)) ->
  RPallocated bindings now lo hi cells M O -> exists Ms Mf,
  spec_stepstar sd (spec_seq V293_tick_clock_action (V293_tick_chain_code bindings)) O (END None)
    (RPnextO O bindings now) /\ LRexecution P ks M Mf /\
  load Tint32 Ms (101%positive,0%Z)=Some (Vint32 (Int.add now Int.one)) /\
  LRstate LRcaller Mf (RPnextO O bindings now) |=
    RPpayload (map V293_tick_reentry_binding bindings) (Int.add now Int.one) lof hif
      (concat (map V293_tick_reentry_orphan bindings) ++ cells).
Proof.
  intros sd P ks bindings now lo hi cells M O lof hif Valid Unique Rel Bitmap Entry.
  pose proof (V293_tick_raw_reentry_return bindings WhileIdle Vnull WhileReady ChainEvents now
    RCentries sd P ks LRglobal LRcaller M (fun _ => false) false [3%nat] [false] O (spec_done None)
    901%Z 904%Z 902%Z 903%Z 1001%Z 1002%Z 1003%Z 70%positive 71%positive 101%positive 102%positive 103%positive
    92%positive 93%positive 94%positive lo hi 1100%Z
    (sseq (V293_tick_body 901%Z 902%Z 903%Z 904%Z 1001%Z 1002%Z 1003%Z 1101%Z) sret) cells
    ltac:(discriminate) ltac:(discriminate)
    ltac:(vm_compute;reflexivity) ltac:(vm_compute;reflexivity) ltac:(vm_compute;reflexivity)
    ltac:(vm_compute;reflexivity) ltac:(vm_compute;reflexivity)
    ltac:(vm_compute;reflexivity) ltac:(vm_compute;reflexivity)
    ltac:(vm_compute;reflexivity) ltac:(vm_compute;reflexivity)
    ltac:(vm_compute;reflexivity) ltac:(vm_compute;reflexivity)
    ltac:(change (368+50<=4294967295)%Z;lia) Valid Unique Rel Entry) as Run.
  rewrite Bitmap in Run. destruct Run as (Abstract&NewValid&NewUnique&NewRel&Ms&Mf&Exec&Time&Pointer&After&Frame&Gone).
  exists Ms. exists Mf. split;[exact Abstract| ]. split;[exact Exec| ]. split;assumption.
Qed.
Definition RPbindings1 := map V293_tick_reentry_binding WhileBindings.
Definition RPbindings2 := map V293_tick_reentry_binding RPbindings1.
Definition RPcells1 := concat (map V293_tick_reentry_orphan WhileBindings) ++ WhileFrameCells.
Definition RPcells2 := concat (map V293_tick_reentry_orphan RPbindings1) ++ RPcells1.
Definition RPstate1 := RPnextO ChainOld WhileBindings (Int.repr 37).
Definition RPstate2 := RPnextO RPstate1 RPbindings1 (Int.repr 38).
Definition RPprefix P ks M M2 := V293_local_steps P
  (curs (scall 1100%Z nil),(kenil,ks))
  ((LRglobal,LRcaller,M),(fun _ => false),(false,[3%nat],[false]))
  (curs (scall 1101%Z nil),(kenil,kseq (V293_tick_post_hook 901%Z 902%Z 903%Z 1001%Z 1002%Z 1003%Z)
    (kseq sret (kcall 1100%Z
      (sseq (V293_tick_body 901%Z 902%Z 903%Z 904%Z 1001%Z 1002%Z 1003%Z 1101%Z) sret) LRcaller ks))))
  ((LRglobal,LRlocal,M2),(fun _ => false),(false,[3%nat],[false])).

(* Two REAL post-hook suffixes, with a real second allocation prefix, but no
   installed CPU hook: NOT a continuous whole-call or interrupt theorem. *)
Theorem RPtwice : forall (sd:ossched) P ks, P 1100%Z=Some LRfunction ->
  exists M Ms1 Mf1 M2 Ms2 Mf2,
  LRprefix P ks M /\ LRexecution P ks M Mf1 /\
  LRstate LRcaller Mf1 RPstate1 |= RPpayload RPbindings1 (Int.repr 38) 16 20 RPcells1 /\
  RPprefix P ks Mf1 M2 /\
  load (Tptr V293_tcb_type) M2 (70%positive,0%Z)=Some Vundef /\
  load Tint32 M2 (71%positive,0%Z)=Some (Vint32 Int.zero) /\
  LRexecution P ks M2 Mf2 /\
  load Tint32 Ms1 (101%positive,0%Z)=Some (Vint32 (Int.repr 38)) /\
  load Tint32 Ms2 (101%positive,0%Z)=Some (Vint32 (Int.repr 39)) /\
  LRstate LRcaller Mf2 RPstate2 |= RPpayload RPbindings2 (Int.repr 39) 16 20 RPcells2.
Proof.
  intros sd P ks Program.
  destruct (LRallocated_entry P ks Program) as (M&Prefix&Scan&Saved&Entry).
  assert (Raw : RPallocated WhileBindings (Int.repr 37) 16 16 WhileFrameCells M ChainOld).
  { unfold RPallocated,RPpayload,V293_tick_reentry_payload,LRentry,V293_tick_storage_owned in *.
    cbn [V293_owned_record_cells]. clear -Entry. sep auto. }
  destruct (RPstep sd P ks WhileBindings (Int.repr 37) 16 16 WhileFrameCells M ChainOld 16 20
    WhileBindingsValid WhileKeysUnique RCold_rel eq_refl Raw) as (Ms1&Mf1&Abs1&Exec1&Time1&After1).
  change (LRstate LRcaller Mf1 RPstate1 |= RPpayload RPbindings1 (Int.repr 38) 16 20 RPcells1) in After1.
  destruct (RPpayload_fresh RPbindings1 (Int.repr 38) 16 20 RPcells1 LRcaller Mf1 RPstate1
    ltac:(vm_compute;repeat constructor;discriminate) After1) as [FreshScan FreshSaved].
  assert (Callee : LRstate LRlocal Mf1 RPstate1 |= RPpayload RPbindings1 (Int.repr 38) 16 20 RPcells1).
  { eapply V293_tick_reentry_payload_context;exact After1. }
  destruct (V293_tick_call_to_hook P ks LRglobal LRcaller Mf1 (fun _ => false)
    false [3%nat] [false] RPstate1 (spec_done None) 1100%Z 901%Z 902%Z 903%Z 904%Z
    1001%Z 1002%Z 1003%Z 1101%Z 70%positive 71%positive _ Program ltac:(discriminate)
    FreshScan FreshSaved Callee) as (M2&Prefix2&Scan2&Saved2&Allocated2).
  assert (Raw2 : RPallocated RPbindings1 (Int.repr 38) 16 20 RPcells1 M2 RPstate1).
  { unfold RPallocated. clear -Allocated2. sep auto. }
  assert (Valid1 : Forall V293_tick_binding_valid RPbindings1)
    by (apply V293_tick_reentry_valid;exact WhileBindingsValid).
  assert (Unique1 : NoDup (V293_tick_record_keys RPbindings1 WhileIdle))
    by (unfold RPbindings1;rewrite V293_tick_reentry_keys;exact WhileKeysUnique).
  assert (Rel1 : V293_ready_rel 16 20 RCentries (V293_tick_record_map false RPbindings1 WhileIdle Vnull)).
  { unfold RPbindings1;rewrite V293_tick_reentry_record_map. pose proof (V293_tick_record_chain_ready_rel WhileBindings WhileIdle Vnull 16 16 RCentries
      WhileBindingsValid WhileKeysUnique RCold_rel) as [_ Rel]. exact Rel. }
  destruct (RPstep sd P ks RPbindings1 (Int.repr 38) 16 20 RPcells1 M2 RPstate1 16 20
    Valid1 Unique1 Rel1 eq_refl Raw2) as (Ms2&Mf2&Abs2&Exec2&Time2&After2).
  exists M. exists Ms1. exists Mf1. exists M2. exists Ms2. exists Mf2.
  split;[exact Prefix| ]. split;[exact Exec1| ]. split;[exact After1| ].
  split;[exact Prefix2| ]. split;[exact Scan2| ]. split;[exact Saved2| ].
  split;[exact Exec2| ]. split;[exact Time1| ]. split;[exact Time2| ]. exact After2.
Qed.
Lemma RPraw_reads : forall bindings now lo hi cells M O,
  LRstate LRcaller M O |= RPpayload bindings now lo hi cells ->
  load Tint32 M (101%positive,0%Z)=Some (Vint32 now) /\
  (forall a tp v, In (a,tp,v) (V293_tick_chain_cells (map fst bindings) WhileIdle) -> load tp M a=Some v) /\
  (forall a tp v, In (a,tp,v) cells -> load tp M a=Some v).
Proof.
  intros bindings now lo hi cells M O Held.
  unfold RPpayload,V293_tick_reentry_payload in Held.
  assert (Clock : LRstate LRcaller M O |=
    V293_owned_record_cell ((101%positive,0%Z),Tint32,Vint32 now) ** Atrue).
  { cbn [V293_owned_record_cells] in Held. clear -Held. sep auto. }
  assert (Chain : LRstate LRcaller M O |=
    V293_owned_record_cells (V293_tick_chain_cells (map fst bindings) WhileIdle) ** Atrue)
    by (clear -Held;sep auto).
  assert (Caller : LRstate LRcaller M O |= V293_owned_record_cells cells ** Atrue)
    by (clear -Held;sep auto).
  split.
  - change (load Tint32 (getmem (LRstate LRcaller M O)) (101%positive,0%Z)=Some (Vint32 now)).
    eapply V293_record_star_load_l;[apply V293_owned_record_cell_load|exact Clock].
  - split;intros a tp v Member;change (load tp (getmem (LRstate LRcaller M O)) a=Some v);
      eapply V293_record_star_load_l;[ |exact Chain| |exact Caller];
      apply V293_owned_record_cells_load;exact Member.
Qed.
Theorem RPobservations : forall (sd:ossched), exists M Mf1 M2 Mf2,
  LRprefix LRprogram kstop M /\ LRexecution LRprogram kstop M Mf1 /\
  RPprefix LRprogram kstop Mf1 M2 /\ LRexecution LRprogram kstop M2 Mf2 /\
  load Tint32 Mf1 (101%positive,0%Z)=Some (Vint32 (Int.repr 38)) /\
  load Tint32 Mf2 (101%positive,0%Z)=Some (Vint32 (Int.repr 39)) /\
  load Tint32 Mf1 (81%positive,172%Z)=Some (Vint32 (Int.repr 2)) /\
  load Tint32 Mf2 (81%positive,172%Z)=Some (Vint32 (Int.repr 1)) /\
  load (Tcom_ptr 411%Z) Mf1 (81%positive,36%Z)=Some (Vptr (84%positive,Int.repr 4)) /\
  load (Tcom_ptr 411%Z) Mf2 (81%positive,36%Z)=Some (Vptr (84%positive,Int.repr 4)) /\
  load Tint32 Mf2 (90%positive,0%Z)=Some (Vint32 (Int.repr 99)).
Proof.
  intro sd. destruct (RPtwice sd LRprogram kstop eq_refl)
    as (M&Ms1&Mf1&M2&Ms2&Mf2&Prefix&Exec1&After1&Prefix2&Scan2&Saved2&Exec2&Time1&Time2&After2).
  destruct (RPraw_reads _ _ _ _ _ _ _ After1) as (Clock1&Chain1&Frame1).
  destruct (RPraw_reads _ _ _ _ _ _ _ After2) as (Clock2&Chain2&Frame2).
  exists M. exists Mf1. exists M2. exists Mf2.
  split;[exact Prefix| ]. split;[exact Exec1| ]. split;[exact Prefix2| ]. split;[exact Exec2| ].
  split;[exact Clock1| ]. split;[exact Clock2| ].
  split;[apply Chain1;vm_compute;tauto| ]. split;[apply Chain2;vm_compute;tauto| ].
  split;[apply Frame1;vm_compute;tauto| ]. split;[apply Frame2;vm_compute;tauto| ].
  apply Frame2;vm_compute;tauto.
Qed.
Theorem RPbinding_cases : forall reason,
  Forall (fun d=>
    let b:=LRwaitbinding reason d in
    let b':=V293_tick_reentry_binding b in
    V293_tick_binding_valid b' /\
    V293_tick_binding_value false b'=V293_tick_binding_value true b /\
    V293_tick_delay_value (fst b')=Z.max 0 (d-1) /\
    length (V293_tick_binding_extra b')+length (V293_tick_reentry_orphan b)=length (V293_tick_binding_extra b) /\
    length (V293_tick_reentry_orphan b)=
      (if Z.eqb d 1 then match reason with os_stat_time=>0 | _=>1 end else 0)) [0%Z;1%Z;3%Z].
Proof.
  intro reason. destruct reason;
    repeat (apply Forall_cons;[unfold V293_tick_binding_valid,V293_tick_task_valid;vm_compute;
      repeat split;try reflexivity;try discriminate;lia| ]);apply Forall_nil.
Qed.
Theorem RPorphan_not_lost : RPcells1=RPcells2 /\ RPcells2=
  [((81%positive,36%Z),Tcom_ptr 411%Z,Vptr (84%positive,Int.repr 4));
   ((90%positive,0%Z),Tint32,Vint32 (Int.repr 99))] /\
  V293_tick_pend_value (fst (hd (LRwaitbinding os_stat_time 0) RPbindings2))=1.
Proof. repeat split;reflexivity. Qed.
Definition RPchain1 := V293_tick_chain_cells (map fst RPbindings1) WhileIdle.
Definition RPchain_without_next := hd ((81%positive,52%Z),Tint32,Vint32 Int.zero) RPchain1::skipn 2 RPchain1.
Definition RPwithout_next M O := LRstate LRcaller M O |=
  V293_owned_record_cells
    (((101%positive,0%Z),Tint32,Vint32 (Int.repr 38))::
     ((102%positive,0%Z),Tint8,V293_byteval 1)::
     ((103%positive,0%Z),Tptr V293_tcb_type,Vptr WhileHead)::nil) **
  (V293_owned_record_cells RPchain_without_next **
   (V293_owned_record_cells (V293_tick_bitmap_cells 92%positive 93%positive 3 16 20) **
    (V293_owned_record_cell (V293_tick_idle_cell WhileIdle) **
     (V293_owned_record_cells (concat (map V293_tick_binding_extra RPbindings1)) **
      (V293_owned_record_cells (V293_tick_idle_extra WhileIdle Vnull) **
       (V293_owned_record_cells (V293_priority_cells 94%positive 0%Z RCentries) **
        (V293_owned_record_cells RPcells1 **
         (CurTid WhileReady ** V293_shared_fields WhileReady
          (V293_tick_record_map false RPbindings1 WhileIdle Vnull) ChainEvents (Int.repr 38))))))))).
Theorem RPnext_control : forall (sd:ossched), exists M Mf mn mr onext orest,
  LRexecution LRprogram kstop M Mf /\
  LRstate LRcaller Mf RPstate1 |= RPpayload RPbindings1 (Int.repr 38) 16 20 RPcells1 /\
  join mn mr Mf /\ join onext orest RPstate1 /\ onext=emp /\ orest=RPstate1 /\
  LRstate LRcaller mn onext |= V293_owned_record_cell ((81%positive,28%Z),Tcom_ptr 410%Z,Vptr WhileSecond) /\
  RPwithout_next mr orest /\ get mr ((81%positive,28%Z):addr)=None /\
  ~ (LRstate LRcaller mr orest |= RPpayload RPbindings1 (Int.repr 38) 16 20 RPcells1).
Proof.
  intro sd. destruct (RPtwice sd LRprogram kstop eq_refl)
    as (M&Ms1&Mf&M2&Ms2&Mf2&Prefix&Exec&After&Prefix2&Scan2&Saved2&Exec2&Time1&Time2&After2).
  assert (Focus : LRstate LRcaller Mf RPstate1 |=
    V293_owned_record_cell ((81%positive,28%Z),Tcom_ptr 410%Z,Vptr WhileSecond) **
    (V293_owned_record_cells
      (((101%positive,0%Z),Tint32,Vint32 (Int.repr 38))::
       ((102%positive,0%Z),Tint8,V293_byteval 1)::
       ((103%positive,0%Z),Tptr V293_tcb_type,Vptr WhileHead)::nil) **
    (V293_owned_record_cells RPchain_without_next **
     (V293_owned_record_cells (V293_tick_bitmap_cells 92%positive 93%positive 3 16 20) **
      (V293_owned_record_cell (V293_tick_idle_cell WhileIdle) **
       (V293_owned_record_cells (concat (map V293_tick_binding_extra RPbindings1)) **
        (V293_owned_record_cells (V293_tick_idle_extra WhileIdle Vnull) **
         (V293_owned_record_cells (V293_priority_cells 94%positive 0%Z RCentries) **
          (V293_owned_record_cells RPcells1 **
           (CurTid WhileReady ** V293_shared_fields WhileReady
            (V293_tick_record_map false RPbindings1 WhileIdle Vnull) ChainEvents (Int.repr 38))))))))))).
  { unfold RPpayload,V293_tick_reentry_payload in After.
    change (V293_tick_chain_cells (map fst RPbindings1) WhileIdle) with RPchain1 in After.
    change RPchain1 with
      (((81%positive,52%Z),Tint32,Vint32 Int.zero)::
       ((81%positive,28%Z),Tcom_ptr 410%Z,Vptr WhileSecond)::skipn 2 RPchain1) in After.
    unfold RPchain_without_next. change (hd _ RPchain1) with ((81%positive,52%Z),Tint32,Vint32 Int.zero).
    cbn [V293_owned_record_cells] in After |- *. clear -After. sep auto. }
  apply sat_split in Focus. destruct Focus as (mn&mr&onext&orest&JM&JO&Next&Rest).
  assert (EmptyNext : onext=emp).
  { pose proof Next as N. unfold V293_owned_record_cell in N.
    apply astar_l_apure_elim in N. destruct N as [_ [_ Empty]]. exact Empty. }
  assert (SameAbstract : orest=RPstate1).
  { rewrite EmptyNext in JO. eapply map_join_emp''. exact JO. }
  assert (Missing : get mr ((81%positive,28%Z):addr)=None).
  { unfold V293_owned_record_cell in Next. apply astar_l_apure_elim in Next.
    destruct Next as [_ [Points Empty]]. destruct Points as (bytes&Encoding&Cells).
    rewrite <-Encoding in Cells. cbn [encode_val ptomvallist] in Cells.
    destruct Cells as (m0&mt&J0&Byte0&Tail). unfold ptomval in Byte0. subst m0.
    assert (D : disjoint (sig ((81%positive,28%Z):addr)
      (true,memory.Pointer 81%positive (Int.repr 128) 3)) mr).
    { eapply mem_join_join_disjoint;[exact J0|exact JM]. }
    destruct D as (combined&DisjointJoin). eapply mem_join_get_none'. exact DisjointJoin. }
  exists M. exists Mf. exists mn. exists mr. exists onext. exists orest.
  split;[exact Exec| ]. split;[exact After| ]. split;[exact JM| ]. split;[exact JO| ].
  split;[exact EmptyNext| ]. split;[exact SameAbstract| ]. split;[exact Next| ]. split;[exact Rest| ].
  split;[exact Missing| ]. intro Bad.
  destruct (RPraw_reads _ _ _ _ _ _ _ Bad) as [_ [Chain _]].
  assert (Wrong : load (Tcom_ptr 410%Z) mr (81%positive,28%Z)=Some (Vptr WhileSecond))
    by (apply Chain;vm_compute;tauto).
  unfold load,loadm in Wrong. cbn [typelen loadbytes] in Wrong. rewrite Missing in Wrong. discriminate.
Qed.
