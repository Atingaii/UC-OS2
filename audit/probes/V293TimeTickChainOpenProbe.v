(* Canonical entry is packed directly from literal bytes, not from the new opening. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickChainOpen.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickRecordReassembly.
Require Import CertiOS.certiucos.v293.proofs.V293TCBJointShared.
Require Import CertiOS.audit.probes.V293TimeTickWhileCoreProbe.
Require Import CertiOS.framework.proof.soundness.
(* Independent four-task literal heap; original while and exact residuals. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickWhileCore.
Require Import CertiOS.audit.probes.V293TimeTickReadyChainProbe.
Require Import CertiOS.audit.probes.V293TimeTickWhileRecordsProbe.
Require Import CertiOS.audit.probes.V293TimeTickWhileSharedProbe.
Require Import CertiOS.audit.probes.V293TimeTickReadyUpdateProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickReadyUpdate.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickWhileRecords.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickWhileShared.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickDelayHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickWhileHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickTaskBridge.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLosslessFields.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLoop.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickExpiry.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickReadyChain.
Require Import CertiOS.certiucos.v293.proofs.V293TimeReadyShared.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293SharedStateWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.code.V293OSTimeTick.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.audit.probes.V293ReadyTaskInvariantProbe.
Require Import CertiOS.audit.probes.V293TimeTickDelayHoareProbe.
Require Import CertiOS.audit.probes.V293TimeTickTraversalProbe.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Coq.Sorting.Permutation Lia.
Import ListNotations.
Local Open Scope nat_scope.


Definition COcore bindings:=V293_tick_chain_core_pre bindings WhileIdle Vnull WhileReady ChainEvents(Int.repr 37)
  93%positive 92%positive 94%positive 96%positive 70%positive WCframe.
Definition COpre enabled:=<||V293_tick_chain_code WhileBindings||> **
  OS[(fun _=>false),enabled,[1],[false]] ** COcore WhileBindings.
Definition COpost enabled:=EX actual:list(V293_tick_task*(taskstatus*val)),
  (<||END None||> ** OS[(fun _=>false),enabled,[1],[false]] **
    V293_tick_while_core_post actual WhileIdle 93%positive 92%positive 94%positive 96%positive 70%positive WCframe) **
  [|V293_tick_pend_choices WhileBindings actual|].
Definition COhint:list(V293_tick_task*(taskstatus*val)):=
  (V293_tick_wait_node 81%positive 8%Z 1%Z WhileReason 99 10,
    (wait WhileReason(Int.repr 1),Vnull))::tl WhileBindings.
Definition COlayouts:=
  V293_owned_record_cells(V293_record_layout WhileHead 10(wait WhileReason(Int.repr 1))Vnull 7) **
  (V293_owned_record_cells(V293_record_layout WhileSecond 2(wait os_stat_time(Int.repr 3))Vnull 7) **
  (V293_owned_record_cells(V293_record_layout WhileReady 4 rdy Vnull 7) **
   V293_owned_record_cells(V293_record_layout WhileIdle 12 rdy Vnull 7))).
Definition COother:=
  ((CurTid WhileReady ** V293_shared_fields WhileReady WhileOldTasks ChainEvents(Int.repr 37)) **
    V293_ready_owned 93%positive 92%positive 94%positive WhileOldTasks) **
  (PV(96%positive,Int.zero)@Tint32|->Vint32(Int.repr 37) **
  (V293_owned_record_cell(V293_tick_pointer_cell 70%positive WhileHead) **
  (V293_owned_record_cells(V293_tick_chain_missing WhileBindings WhileIdle) ** WCframe))).

Lemma COpack : forall R s,
  s |= COlayouts ** R -> s |= V293_owned_task_records WhileOldTasks ** R.
Proof.
  intros R s Held.
  assert(Enumeration:TcbMod.lst WhileOldTasks=
    [(WhileHead,(Int.repr 10,wait WhileReason(Int.repr 1),Vnull));
     (WhileSecond,(Int.repr 2,wait os_stat_time(Int.repr 3),Vnull));
     (WhileReady,(Int.repr 4,rdy,Vnull));(WhileIdle,(Int.repr 12,rdy,Vnull))])by(vm_compute;reflexivity).
  unfold V293_owned_task_records;rewrite Enumeration;cbn [V293_owned_task_list].
  unfold COlayouts in Held.
  eapply astar_mono;[ |intros st H;exact H|exact Held].
  apply astar_mono.
  - intros st H;unfold V293_owned_task_record;exists 10;exists 7.
    apply astar_l_apure_intro;[exact H|repeat split;reflexivity||lia].
  - apply astar_mono.
    + intros st H;unfold V293_owned_task_record;exists 2;exists 7.
      apply astar_l_apure_intro;[exact H|repeat split;reflexivity||lia].
    + apply astar_mono.
      * intros st H;unfold V293_owned_task_record;exists 4;exists 7.
        apply astar_l_apure_intro;[exact H|repeat split;reflexivity||lia].
      * intros st H.
        assert(K:st |= V293_owned_task_record WhileIdle(Int.repr 12)rdy Vnull).
        { unfold V293_owned_task_record;exists 12;exists 7.
          apply astar_l_apure_intro;[exact H|repeat split;reflexivity||lia]. }
        clear -K;sep auto.
Qed.

Definition COallcells:=
  V293_record_layout WhileHead 10(wait WhileReason(Int.repr 1))Vnull 7 ++
  V293_record_layout WhileSecond 2(wait os_stat_time(Int.repr 3))Vnull 7 ++
  V293_record_layout WhileReady 4 rdy Vnull 7 ++
  V293_record_layout WhileIdle 12 rdy Vnull 7 ++
  V293_ready_cells 93%positive 92%positive 94%positive 16 16 RCentries ++
  [V293_tick_pointer_cell 70%positive WhileHead] ++
  V293_tick_chain_missing WhileBindings WhileIdle ++ [WCclock] ++ WhileFrameCells.
Local Ltac COpermute :=
 lazymatch goal with
 | |- Permutation (@nil _) (@nil _) => constructor
 | |- Permutation ?xs (?x::?ys) =>
   let rec extract before rest :=
    lazymatch rest with
    | x::?tail => eapply Permutation_trans with(l':=x::(before++tail));
      [apply Permutation_sym;apply Permutation_middle|apply perm_skip;cbn [app];COpermute]
    | ?h::?tail => extract(before++[h])tail
    end
   in extract(@nil V293_record_cell)xs
 end.
Lemma COcells_permutation : Permutation WCcells COallcells.
Proof. vm_compute;COpermute. Qed.

Theorem COentry : forall enabled,
  WCstate enabled WCmemory WCabs(V293_tick_chain_code WhileBindings) |= COpre enabled.
Proof.
  intro enabled.
  assert(GP:GoodFrm WCphysical).
  { unfold WCphysical,DHbindings,LINV,V293_witness_li;cbn [GoodFrm].
    repeat split;try(intros;exact I);apply V293_tick_cells_frame. }
  pose proof(goodfrm_prop _ _ _ _ _ _ GP WCspatial(fun _=>false)
    (false,[],[])(spec_done None))as Physical.
  assert(Joint:V293_target_wstate WCge TickLocal WCmemory WCabs |= WCphysical **
    V293_shared_fields WhileReady WhileOldTasks ChainEvents(Int.repr 37)).
  { eapply V293_target_wstate_star with(m1:=WCmemory)(m2:=emp)(o1:=emp)(o2:=WCabs).
    - apply map_join_emp.
    - apply map_join_comm;apply map_join_emp.
    - exact Physical.
    - exact WCabstract. }
  assert(Good:GoodFrm(WCphysical ** V293_shared_fields WhileReady WhileOldTasks ChainEvents(Int.repr 37))).
  { cbn [GoodFrm];split;[exact GP|unfold V293_shared_fields;cbn [GoodFrm];repeat split;exact I]. }
  pose proof(goodfrm_prop _ _ _ _ _ _ Good Joint(fun _=>false)
    (enabled,[1],[false])(V293_tick_chain_code WhileBindings))as Ready.
  assert(Reordered:WCstate enabled WCmemory WCabs(V293_tick_chain_code WhileBindings) |=
    (V293_owned_record_cells COallcells **
      (CurTid WhileReady ** (DHbindings ** LINV V293_witness_li WhileReady []))) **
    V293_shared_fields WhileReady WhileOldTasks ChainEvents(Int.repr 37)).
  { eapply astar_mono;[ |intros st H;exact H|exact Ready].
    unfold WCphysical;apply astar_mono;[ |intros st H;exact H].
    apply V293_owned_cells_permutation;exact COcells_permutation. }
  assert(Flat:WCstate enabled WCmemory WCabs(V293_tick_chain_code WhileBindings) |= COlayouts ** COother).
  { unfold COother,V293_ready_owned. sep normal. exists 16. exists 16. exists RCentries.
    assert(Packed:WCstate enabled WCmemory WCabs(V293_tick_chain_code WhileBindings) |=
      COlayouts **
      (((CurTid WhileReady ** V293_shared_fields WhileReady WhileOldTasks ChainEvents(Int.repr 37)) **
        V293_owned_record_cells(V293_ready_cells 93%positive 92%positive 94%positive 16 16 RCentries)) **
      (PV(96%positive,Int.zero)@Tint32|->Vint32(Int.repr 37) **
      (V293_owned_record_cell(V293_tick_pointer_cell 70%positive WhileHead) **
      (V293_owned_record_cells(V293_tick_chain_missing WhileBindings WhileIdle) ** WCframe))))).
    { unfold COlayouts,COallcells,WCclock,WCframe in Reordered |- *.
      cbn [WhileBindings WhileReason V293_tick_wait_node V293_tick_block V293_tick_base
        V293_tick_prio V293_tick_task_pointer V293_tick_chain_cells V293_tick_task_cells V293_tick_head
        V293_tick_pointer_cell V293_tick_bitmap_cells V293_priority_cells RCentries V293_ready_cells
        V293_tick_binding_extra V293_tick_record_extra V293_tick_idle_extra V293_record_layout
        V293_tick_chain_missing V293_tick_node_missing V293_tick_pend_value
        V293_owned_record_cells app concat map fst snd tl WhileHead WhileSecond WhileReady WhileIdle WhileFrameCells]in Reordered |- *.
      unfold V293_owned_record_cell in Reordered |- *. clear -Reordered;sep auto. }
    clear -Packed;sep auto. exact RCold_rel. }
  pose proof(COpack _ _ Flat)as Packed.
  assert(Entry:WCstate enabled WCmemory WCabs(V293_tick_chain_code WhileBindings) |= COcore WhileBindings).
  { unfold COcore,V293_tick_chain_core_pre,V293_ready_payload,COother in *.
    change(WCstate enabled WCmemory WCabs(V293_tick_chain_code WhileBindings) |=
      ((CurTid WhileReady ** V293_shared_fields WhileReady WhileOldTasks ChainEvents(Int.repr 37)) **
        (V293_owned_task_records WhileOldTasks ** V293_ready_owned 93%positive 92%positive 94%positive WhileOldTasks)) **
      (PV(96%positive,Int.zero)@Tint32|->Vint32(Int.repr 37) **
      (V293_owned_record_cell(V293_tick_pointer_cell 70%positive WhileHead) **
      (V293_owned_record_cells(V293_tick_chain_missing WhileBindings WhileIdle) ** WCframe)))).
    clear -Packed;sep auto. }
  assert(Control:WCstate enabled WCmemory WCabs(V293_tick_chain_code WhileBindings) |=
    Aisr(fun _=>false) ** (Aie enabled ** (Ais(1::nil) ** (Acs(false::nil) ** COcore WhileBindings)))).
  { apply astar_l_aisr_intro;[ |reflexivity]. apply astar_l_aie_intro;[ |reflexivity].
    apply astar_l_ais_intro;[ |reflexivity]. apply astar_l_acs_intro;[exact Entry|reflexivity]. }
  unfold COpre. apply astar_l_aop'_intro;[ |reflexivity]. clear -Control;sep auto.
Qed.

Theorem COhoare : forall Spec sd I r ri enabled,
  InfRules Spec sd V293_witness_li I r ri(COpre enabled)
    (swhile(V293_tick_guard 901%Z)(V293_tick_iteration 901%Z 902%Z 903%Z))
    (COpost enabled)WhileReady.
Proof.
  intros;apply V293_tick_chain_core_hoare with(ct:=WhileReady)(es:=ChainEvents)
    (n:=Int.repr 37)(message:=Vnull).
  - exact RUnoabs.
  - change(368+50<=4294967295)%Z;lia.
  - exact WhileBindingsValid.
  - exact WhileKeysUnique.
  - exact WCenv.
  - exact WCcur.
  - exact WCframe_good.
  - exact WCframe_change.
  - change(1<=INUM)%nat;unfold INUM;lia.
Qed.
Theorem COsemantics : forall Spec sd I r ri enabled,
  simulation.RuleSem Spec sd V293_witness_li I r ri(COpre enabled)
    (swhile(V293_tick_guard 901%Z)(V293_tick_iteration 901%Z 902%Z 903%Z))
    (COpost enabled)WhileReady.
Proof. intros;apply RuleSound;apply COhoare. Qed.

Theorem COopened : forall enabled,
  WCstate enabled WCmemory WCabs(V293_tick_chain_code WhileBindings) |=
  EX actual:list(V293_tick_task*(taskstatus*val)),EX lo:nat,EX hi:nat,EX entries:list val,
    [|V293_tick_pend_choices WhileBindings actual /\
      V293_ready_rel lo hi entries(V293_tick_record_map false actual WhileIdle Vnull)|] **
    V293_tick_while_core_pre actual WhileIdle Vnull WhileReady ChainEvents(Int.repr 37)
      93%positive 92%positive 94%positive 96%positive 70%positive WCframe lo hi entries.
Proof.
  intro enabled;apply V293_tick_chain_core_open;[exact WhileBindingsValid|exact WhileKeysUnique| ].
  pose proof(COentry enabled)as H;unfold COpre in H.
  clear -H;sep auto.
Qed.

Theorem COhint_same :
  V293_tick_record_map false COhint WhileIdle Vnull=WhileOldTasks /\
  V293_tick_chain_code COhint=V293_tick_chain_code WhileBindings /\
  V293_tick_chain_missing COhint WhileIdle=V293_tick_chain_missing WhileBindings WhileIdle /\
  COcore COhint=COcore WhileBindings.
Proof. repeat split;reflexivity. Qed.
Theorem COhint_entry : forall enabled,
  WCstate enabled WCmemory WCabs(V293_tick_chain_code COhint) |=
  <||V293_tick_chain_code COhint||> ** OS[(fun _=>false),enabled,[1],[false]] ** COcore COhint.
Proof.
  intro enabled;destruct COhint_same as[Map[Code[Missing Core]]];rewrite Code,Core;apply COentry.
Qed.

Lemma COliteral_read : forall a tp v,
  In(a,tp,v)WCcells -> load tp WCmemory a=Some v.
Proof.
  intros a tp v Member.
  eapply V293_record_star_load_l with(s:=WCstate false WCmemory emp(END None))
    (P:=V293_owned_record_cells WCcells);[ |exact WCspatial].
  intros st H;eapply V293_owned_record_cells_load;[exact Member|exact H].
Qed.

Theorem COevent_selected : exists pend,pend=7 /\
  WCstate false WCmemory WCabs(V293_tick_chain_code COhint) |=
    V293_owned_record_cells(V293_tick_task_cells(fst(V293_tick_choose_pend(hd
      (V293_tick_wait_node 81%positive 8%Z 1%Z WhileReason 99 10,
        (wait WhileReason(Int.repr 1),Vnull))COhint)pend))WhileSecond) ** Atrue.
Proof.
  pose proof(COhint_entry false)as H.
  set(binding:=(V293_tick_wait_node 81%positive 8%Z 1%Z WhileReason 99 10,
    (wait WhileReason(Int.repr 1),Vnull))).
  assert(Records:WCstate false WCmemory WCabs(V293_tick_chain_code COhint) |=
    V293_owned_task_records WhileOldTasks **
    (V293_owned_record_cells(V293_tick_node_missing binding WhileSecond) ** Atrue)).
  { unfold COcore,V293_tick_chain_core_pre,V293_ready_payload in H.
    change(V293_tick_record_map false COhint WhileIdle Vnull)with WhileOldTasks in H.
    change(V293_tick_chain_missing COhint WhileIdle)with
      (V293_tick_node_missing binding WhileSecond++V293_tick_chain_missing(tl WhileBindings)WhileIdle)in H.
    assert(Whole:WCstate false WCmemory WCabs(V293_tick_chain_code COhint) |=
      V293_owned_task_records WhileOldTasks **
      (V293_owned_record_cells(V293_tick_node_missing binding WhileSecond++
        V293_tick_chain_missing(tl WhileBindings)WhileIdle) ** Atrue))by(clear -H;sep auto).
    assert(Split:WCstate false WCmemory WCabs(V293_tick_chain_code COhint) |=
      V293_owned_task_records WhileOldTasks **
      ((V293_owned_record_cells(V293_tick_node_missing binding WhileSecond) **
        V293_owned_record_cells(V293_tick_chain_missing(tl WhileBindings)WhileIdle)) ** Atrue)).
    { eapply astar_mono;[intros st K;exact K| |exact Whole].
      apply astar_mono;[intros st K;apply V293_tick_cells_append;exact K|intros st K;exact K]. }
    clear -Split;sep auto. }
  assert(Lookup:get WhileOldTasks WhileHead=Some(Int.repr 10,wait WhileReason(Int.repr 1),Vnull))
    by(vm_compute;reflexivity).
  pose proof(V293_owned_task_records_focus _ _ _ _ _ _ _ Lookup Records)as Focused.
  assert(Node:WCstate false WCmemory WCabs(V293_tick_chain_code COhint) |=
    V293_owned_task_record WhileHead(Int.repr 10)(wait WhileReason(Int.repr 1))Vnull **
    (V293_owned_record_cells(V293_tick_node_missing binding WhileSecond) ** Atrue))by(clear -Focused;sep auto).
  assert(Valid:V293_tick_binding_valid binding).
  { exact(V293_tick_choose_pend_valid _ 99 (Forall_inv WhileBindingsValid)ltac:(lia)). }
  destruct(V293_tick_canonical_node_open binding WhileSecond Atrue _ Valid Node)as[pend[Bound Opened]].
  assert(Read:load Tint8 WCmemory(81%positive,57%Z)=Some(V293_byteval pend)).
  { eapply V293_record_star_load_l with(s:=WCstate false WCmemory WCabs(V293_tick_chain_code COhint))
      (P:=V293_owned_record_cells(V293_tick_task_cells(fst(V293_tick_choose_pend binding pend))WhileSecond));[ |exact Opened].
    intros st Held;eapply V293_owned_record_cells_load;[ |exact Held].
    unfold binding,WhileReason,V293_tick_choose_pend,V293_tick_wait_node,V293_tick_task_cells;cbn;intuition. }
  exists pend;split.
  - eapply V293_byteval_injective_bounded;[exact Bound|lia| ].
    pose proof(COliteral_read (81%positive,57%Z)Tint8(V293_byteval 7)ltac:(vm_compute;intuition)).
    congruence.
  - change(WCstate false WCmemory WCabs(V293_tick_chain_code COhint) |=
      V293_owned_record_cells(V293_tick_task_cells(fst(V293_tick_choose_pend binding pend))WhileSecond) ** Atrue).
    clear -Opened;sep auto.
Qed.

Definition COtimebad:list(V293_tick_task*(taskstatus*val)):=
  firstn 1 WhileBindings++
  [(V293_tick_wait_node 81%positive 128%Z 3%Z os_stat_time 99 2,
    (wait os_stat_time(Int.repr 3),Vnull))]++skipn 2 WhileBindings.
Definition COreadybad:list(V293_tick_task*(taskstatus*val)):=
  firstn 2 WhileBindings++
  [(V293_tick_wait_node 81%positive 248%Z 0%Z os_stat_time 99 4,(rdy,Vnull))].

Lemma COmissing_read : forall bindings enabled a tp v,
  In(a,tp,v)(V293_tick_chain_missing bindings WhileIdle) ->
  WCstate enabled WCmemory WCabs(V293_tick_chain_code bindings) |= COcore bindings ->
  load tp WCmemory a=Some v.
Proof.
  intros bindings enabled a tp v Member H.
  assert(Missing:WCstate enabled WCmemory WCabs(V293_tick_chain_code bindings) |=
    V293_owned_record_cells(V293_tick_chain_missing bindings WhileIdle) ** Atrue).
  { unfold COcore,V293_tick_chain_core_pre in H;clear -H;sep auto. }
  eapply V293_record_star_load_l with(s:=WCstate enabled WCmemory WCabs(V293_tick_chain_code bindings))
    (P:=V293_owned_record_cells(V293_tick_chain_missing bindings WhileIdle));[ |exact Missing].
  intros st Held;eapply V293_owned_record_cells_load;[exact Member|exact Held].
Qed.

Theorem COtime_ready_supplements : forall enabled,
  V293_tick_record_map false COtimebad WhileIdle Vnull=WhileOldTasks /\
  V293_tick_record_map false COreadybad WhileIdle Vnull=WhileOldTasks /\
  V293_tick_chain_code COtimebad=V293_tick_chain_code WhileBindings /\
  V293_tick_chain_code COreadybad=V293_tick_chain_code WhileBindings /\
  (~ WCstate enabled WCmemory WCabs(V293_tick_chain_code COtimebad) |= COcore COtimebad) /\
  (~ WCstate enabled WCmemory WCabs(V293_tick_chain_code COreadybad) |= COcore COreadybad).
Proof.
  intro enabled;split;[reflexivity| ];split;[reflexivity| ];split;[reflexivity| ];split;[reflexivity| ];split;intro H.
  - pose proof(COmissing_read COtimebad enabled (81%positive,177%Z)Tint8(V293_byteval 99)
      ltac:(vm_compute;intuition)H)as Bad.
    pose proof(COliteral_read (81%positive,177%Z)Tint8(V293_byteval 7)ltac:(vm_compute;intuition))as Actual.
    rewrite Actual in Bad;vm_compute in Bad;discriminate.
  - pose proof(COmissing_read COreadybad enabled (81%positive,297%Z)Tint8(V293_byteval 99)
      ltac:(vm_compute;intuition)H)as Bad.
    pose proof(COliteral_read (81%positive,297%Z)Tint8(V293_byteval 7)ltac:(vm_compute;intuition))as Actual.
    rewrite Actual in Bad;vm_compute in Bad;discriminate.
Qed.

Theorem COcurrent_clock :
  get WhileOldTasks WhileReady=Some(Int.repr 4,rdy,Vnull) /\
  load Tint32 WCmemory(96%positive,0%Z)=Some(Vint32(Int.repr 37)).
Proof. split;[exact WCcurrent_member|apply COliteral_read;vm_compute;intuition]. Qed.

(* Reuse stage165 independent operation semantics, not an execution of the new RuleSem. *)
Theorem COexecution_control : forall P ks sd enabled,exists Mf,
  (WCstate enabled WCmemory WCabs(V293_tick_chain_code WhileBindings) |= COpre enabled) /\
  WCexecution P ks enabled Mf /\
  spec_stepstar sd(V293_tick_chain_code WhileBindings)WCabs(END None)WCnew /\
  (WCstate enabled Mf WCnew(END None) |= V293_tick_while_core_post WhileBindings WhileIdle
    93%positive 92%positive 94%positive 96%positive 70%positive WCframe) /\
  WCreads Mf /\
  ~ WCneutralized enabled Mf |= V293_time_ready_core 93%positive 92%positive 94%positive 96%positive ** Atrue.
Proof.
  intros P ks sd enabled;destruct(WCexecution_control P ks sd enabled)as[Mf Evidence].
  exists Mf;split;[apply COentry|exact Evidence].
Qed.
