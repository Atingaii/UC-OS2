(* Independent encoded bytes are repacked into the full canonical task map
   before the new rule opens it. This is not kernel initialization reachability. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickCoreFocus.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickRecordReassembly.
Require Import CertiOS.certiucos.v293.proofs.V293TCBJointShared.
Require Import CertiOS.audit.probes.V293TimeTickReadyUpdateProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickReadyUpdate.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickWhileRecords.
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
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.


Definition CFphysical d :=
  (CurTid DHtid ** V293_ready_payload 93%positive 92%positive 95%positive (RUtasks d)) **
  (PV(96%positive,Int.zero)@Tint32|->Vint32(Int.repr 37) **
  (V293_owned_record_cell(V293_tick_pointer_cell 70%positive OwnershipWaiting) **
  (V293_owned_record_cells(V293_tick_wait_missing(RUnode d)RUreason TickNext) ** RUframe))).
Definition CFfixed d := <||spec_prim nil(V293_tick_wait_step OwnershipWaiting)||> **
  OS[(fun _=>false),false,[1],[false]] **
  V293_tick_wait_core_pre 93%positive 92%positive 95%positive 96%positive DHtid
    (RUtasks d)(emp:EcbMod.map)(Int.repr 37) 41%positive 8%Z d RUreason 6 99
    70%positive TickNext RUframe.
Definition CFpre d := EX tasks:TcbMod.map, EX es:EcbMod.map, EX n:int32,
  (<||spec_prim nil(V293_tick_wait_step OwnershipWaiting)||> **
  OS[(fun _=>false),false,[1],[false]] **
  V293_tick_wait_core_pre 93%positive 92%positive 95%positive 96%positive DHtid
    tasks es n 41%positive 8%Z d RUreason 6 99 70%positive TickNext RUframe) **
  [|get tasks OwnershipWaiting=Some(Int.repr 6,wait RUreason(Int.repr d),RUmessage)|].
Definition CFpost d := EX pend:nat, <||END None||> ** OS[(fun _=>false),false,[1],[false]] **
  V293_tick_ready_wait_post 93%positive 92%positive 95%positive 96%positive
    (V293_tick_wait_node 41%positive 8%Z d RUreason pend 6)RUreason RUmessage 70%positive TickNext RUframe.

Lemma CFcanonical_spatial : forall d, DHstate(RUmemory d) |= CFphysical d.
Proof.
  intro d. pose proof(RUspatial d)as Held.
  set(rest:=CurTid DHtid **
    (V293_owned_record_cells(V293_ready_cells 93%positive 92%positive 95%positive 16 0 RTentries) **
    (PV(96%positive,Int.zero)@Tint32|->Vint32(Int.repr 37) **
    (V293_owned_record_cell(V293_tick_pointer_cell 70%positive OwnershipWaiting) **
    (V293_owned_record_cells(V293_tick_wait_missing(RUnode d)RUreason TickNext) ** RUframe))))).
  assert(Packed:DHstate(RUmemory d) |= V293_owned_task_record OwnershipWaiting(Int.repr 6)
    (wait RUreason(Int.repr d))RUmessage ** (V293_owned_task_records(del(RUtasks d)OwnershipWaiting) ** rest)).
  { unfold V293_owned_task_record. sep normal. exists 6. exists 0.
    apply astar_l_apure_intro;[ |repeat split;reflexivity||lia].
    unfold RUphysical,V293_tick_wait_layout,RUnode,rest in Held |- *.
    cbn [V293_tick_wait_node V293_tick_task_pointer V293_tick_prio V293_tick_delay_value V293_tick_pend_value] in Held |- *.
    clear -Held;sep auto. }
  apply V293_owned_task_records_reassemble in Packed.
  assert(Identity:set(RUtasks d)OwnershipWaiting(Int.repr 6,wait RUreason(Int.repr d),RUmessage)=RUtasks d)
    by(apply TcbMod.get_set_same;change(get(RUtasks d)OwnershipWaiting=Some(Int.repr 6,wait RUreason(Int.repr d),RUmessage));apply map_get_set).
  rewrite Identity in Packed. unfold CFphysical,V293_ready_payload,V293_ready_owned.
  sep normal. exists 16. exists 0. exists RTentries.
  apply astar_l_apure_intro;[ |apply RUrel].
  unfold rest in Packed. clear -Packed;sep auto.
Qed.

Lemma CFphysical_good : forall d, GoodFrm(CFphysical d).
Proof.
  intro d. unfold CFphysical,V293_ready_payload,V293_ready_owned.
  cbn [GoodFrm]. repeat split;try exact I;try exact RUframe_good;
    try apply V293_tick_records_frame;try apply V293_tick_cells_frame.
Qed.

Theorem CFentry_fixed : forall d, RUstate d(RUmemory d) |= CFfixed d.
Proof.
  intro d. pose proof(CFcanonical_spatial d)as Physical.
  pose proof(goodfrm_prop _ _ _ _ _ _ (CFphysical_good d)Physical(fun _=>false)
    (false,[],[])(spec_done None))as Rebased.
  assert(Joint:V293_target_wstate DHge TickLocal(RUmemory d)(RUabs d) |=
    CFphysical d ** V293_shared_fields DHtid(RUtasks d)(emp:EcbMod.map)(Int.repr 37)).
  { eapply V293_target_wstate_star with(m1:=RUmemory d)(m2:=emp)(o1:=emp)(o2:=RUabs d).
    - apply map_join_emp.
    - apply map_join_comm;apply map_join_emp.
    - exact Rebased.
    - apply RUabstract. }
  assert(Good:GoodFrm(CFphysical d ** V293_shared_fields DHtid(RUtasks d)(emp:EcbMod.map)(Int.repr 37))).
  { cbn [GoodFrm]. split;[apply CFphysical_good|unfold V293_shared_fields;cbn [GoodFrm];repeat split;exact I]. }
  pose proof(goodfrm_prop _ _ _ _ _ _ Good Joint(fun _=>false)(false,[1],[false])
    (spec_prim nil(V293_tick_wait_step OwnershipWaiting)))as Ready.
  assert(Control:RUstate d(RUmemory d) |= Aisr(fun _=>false) ** (Aie false **
    (Ais(1::nil) ** (Acs(false::nil) ** (CFphysical d **
    V293_shared_fields DHtid(RUtasks d)(emp:EcbMod.map)(Int.repr 37)))))).
  { apply astar_l_aisr_intro;[ |reflexivity]. apply astar_l_aie_intro;[ |reflexivity].
    apply astar_l_ais_intro;[ |reflexivity]. apply astar_l_acs_intro;[exact Ready|reflexivity]. }
  unfold CFfixed. apply astar_l_aop'_intro;[ |reflexivity].
  unfold CFphysical,V293_tick_wait_core_pre,V293_tick_wait_missing,RUnode,RUreason in Control |- *.
  cbn [V293_tick_wait_node V293_tick_block V293_tick_base]. clear -Control;sep auto.
Qed.

Theorem CFentry : forall d, RUstate d(RUmemory d) |= CFpre d.
Proof.
  intro d. pose proof(CFentry_fixed d)as Held.
  unfold CFpre. exists(RUtasks d). exists(emp:EcbMod.map). exists(Int.repr 37).
  apply astar_comm. apply astar_l_apure_intro;[exact Held|apply map_get_set].
Qed.

Theorem CFcore : forall d, RUstate d(RUmemory d) |=
  V293_time_ready_core 93%positive 92%positive 95%positive 96%positive **
  (V293_owned_record_cell(V293_tick_pointer_cell 70%positive OwnershipWaiting) **
  (V293_owned_record_cells(V293_tick_wait_missing
    (V293_tick_wait_node 41%positive 8%Z d RUreason 99 6)RUreason TickNext) ** RUframe)).
Proof.
  intro d. pose proof(CFentry_fixed d)as Held. unfold CFfixed in Held.
  apply V293_tick_wait_core_fold with(ct:=DHtid)(tasks:=RUtasks d)(es:=(emp:EcbMod.map))(n:=Int.repr 37).
  clear -Held;sep auto.
Qed.

Theorem CFrules : forall Spec sd I r ri d, (0<=d<=Int.max_unsigned)%Z ->
  InfRules Spec sd V293_witness_li I r ri (CFpre d)
    (V293_tick_iteration 901%Z 902%Z 903%Z)(CFpost d)DHtid.
Proof.
  intros Spec sd I r ri d D. unfold CFpre,CFpost.
  apply V293_tick_core_wait_iteration with(p:=6)(timepend:=99).
  - exact RUnoabs.
  - change(0<=8 /\ 8+54<=4294967295)%Z;lia.
  - exact D.
  - lia.
  - lia.
  - unfold RUreason;discriminate.
  - apply RUenv.
  - exact RUcur.
  - exact RUframe_good.
  - exact RUframe_change.
  - change(1<=INUM)%nat;unfold INUM;lia.
Qed.

Theorem CFwrong_lookup : forall d,
  get(RUtasks d)OwnershipWaiting<>Some(Int.repr 7,wait RUreason(Int.repr d),RUmessage) /\
  get(RUtasks d)OwnershipWaiting<>Some(Int.repr 6,rdy,RUmessage).
Proof. intro d. unfold RUtasks. rewrite map_get_set. split;discriminate. Qed.

(* A pure observation may project a slot; it never rebuilds physical ownership. *)
Lemma CFmap_identity : forall d tasks es n,
  RUstate d(RUmemory d) |= V293_tick_wait_core_pre 93%positive 92%positive 95%positive 96%positive
    DHtid tasks es n 41%positive 8%Z d RUreason 6 99 70%positive TickNext RUframe -> tasks=RUtasks d.
Proof.
  intros d tasks es n Held.
  assert(Fields:RUstate d(RUmemory d) |= V293_shared_fields DHtid tasks es n ** Atrue).
  { unfold V293_tick_wait_core_pre in Held;clear -Held;sep auto. }
  assert(Slot:get(RUabs d)abstcblsid=Some(abstcblist tasks)).
  { eapply V293_star_abst_get_l with(s:=RUstate d(RUmemory d));[ |exact Fields].
    intros st H;exact(proj1(proj2(V293_shared_fields_get _ _ _ _ _ H))). }
  pose proof(proj1(proj2(V293_shared_fields_get _ _ _ _ _ (RUabstract d))))as Fixed.
  change(get(RUabs d)abstcblsid=Some(abstcblist(RUtasks d)))in Fixed. congruence.
Qed.

Theorem CFreject_wrong_entry : forall d,
  ~ RUstate d(RUmemory d) |= (EX tasks:TcbMod.map, EX es:EcbMod.map, EX n:int32,
    (<||spec_prim nil(V293_tick_wait_step OwnershipWaiting)||> **
    OS[(fun _=>false),false,[1],[false]] **
    V293_tick_wait_core_pre 93%positive 92%positive 95%positive 96%positive DHtid
      tasks es n 41%positive 8%Z d RUreason 6 99 70%positive TickNext RUframe) **
    [|get tasks OwnershipWaiting=Some(Int.repr 7,wait RUreason(Int.repr d),RUmessage)|]).
Proof.
  intros d (tasks&es&n&Held). apply astar_comm in Held.
  apply astar_l_apure_elim in Held. destruct Held as [Wrong Held].
  assert(Core:RUstate d(RUmemory d) |= V293_tick_wait_core_pre 93%positive 92%positive 95%positive 96%positive
    DHtid tasks es n 41%positive 8%Z d RUreason 6 99 70%positive TickNext RUframe)
    by(clear -Held;sep auto).
  pose proof(CFmap_identity d tasks es n Core)as Same. subst tasks.
  exact(proj1(CFwrong_lookup d)Wrong).
Qed.

(* These small independent heaps distinguish a hidden event-wait pend from
   the missing time-wait pend. Neither is an execution premise for the rule. *)
Definition CFpend_cells reason :=
  V293_record_layout OwnershipWaiting 6(wait reason(Int.repr 3))RUmessage 7 ++
  V293_tick_wait_missing(V293_tick_wait_node 41%positive 8%Z 3%Z reason 7 6)reason TickNext.
Definition CFpend_memory reason := OwnershipCellsMemory(CFpend_cells reason).

Lemma CFpend_spatial : forall reason, DHstate(CFpend_memory reason) |= V293_owned_record_cells(CFpend_cells reason).
Proof.
  intro reason.
  assert(Apart:OwnershipCellsSeparated(CFpend_cells reason)).
  { destruct reason as[[eb eo]|[eb eo]| |[eb eo]|[eb eo]];vm_compute;repeat split;intros a Member Rest;
    repeat destruct Member as[Member|Member];try contradiction;subst a;intuition discriminate. }
  assert(Typed:Forall(fun c=>let '(_,tp,v):=c in rule_type_val_match tp v=true)(CFpend_cells reason)).
  { destruct reason as[[eb eo]|[eb eo]| |[eb eo]|[eb eo]];repeat constructor;reflexivity. }
  pose proof(OwnershipCellsSpatial _ Apart Typed DHge TickLocal)as Held.
  unfold DHstate. eapply TickCellsRebase;exact Held.
Qed.

Lemma CFpend_load : forall reason, load Tint8(CFpend_memory reason)(41%positive,57%Z)=Some(V293_byteval 7).
Proof.
  intro reason. eapply V293_owned_record_cells_load with(s:=DHstate(CFpend_memory reason))(cells:=CFpend_cells reason).
  - destruct reason;vm_compute;intuition.
  - apply CFpend_spatial.
Qed.

Theorem CF_event_pend : DHstate(CFpend_memory RUreason) |=
  V293_owned_task_record OwnershipWaiting(Int.repr 6)(wait RUreason(Int.repr 3))RUmessage **
  V293_owned_record_cells(V293_tick_wait_missing(V293_tick_wait_node 41%positive 8%Z 3%Z RUreason 7 6)RUreason TickNext).
Proof.
  pose proof(CFpend_spatial RUreason)as Held. unfold CFpend_cells in Held.
  apply V293_tick_cells_append in Held.
  unfold V293_owned_task_record. sep normal. exists 6. exists 7.
  apply astar_l_apure_intro;[exact Held|repeat split;reflexivity||lia].
Qed.

Theorem CF_time_pend : DHstate(CFpend_memory os_stat_time) |=
  V293_owned_task_record OwnershipWaiting(Int.repr 6)(wait os_stat_time(Int.repr 3))RUmessage **
  V293_owned_record_cells(V293_tick_wait_missing(V293_tick_wait_node 41%positive 8%Z 3%Z os_stat_time 7 6)os_stat_time TickNext).
Proof.
  pose proof(CFpend_spatial os_stat_time)as Held. unfold CFpend_cells in Held.
  apply V293_tick_cells_append in Held.
  unfold V293_owned_task_record. sep normal. exists 6. exists 0.
  apply astar_l_apure_intro;[exact Held|repeat split;reflexivity||lia].
Qed.

Theorem CF_event_selected : exists pend, pend=7 /\
  DHstate(CFpend_memory RUreason) |= V293_owned_record_cells
    (V293_record_layout OwnershipWaiting 6(wait RUreason(Int.repr 3))RUmessage pend) **
  V293_owned_record_cells(V293_tick_wait_missing(V293_tick_wait_node 41%positive 8%Z 3%Z RUreason 7 6)RUreason TickNext).
Proof.
  pose proof(V293_tick_wait_record_open 41%positive 8%Z 3%Z RUreason RUmessage 6 99 _
    ltac:(lia) ltac:(unfold RUreason;discriminate) _ CF_event_pend)as Opened.
  destruct Opened as[pend Opened]. apply astar_l_apure_elim in Opened.
  destruct Opened as[[Bound Time]Opened].
  assert(Read:load Tint8(CFpend_memory RUreason)(41%positive,57%Z)=Some(V293_byteval pend)).
  { eapply V293_record_star_load_l with(s:=DHstate(CFpend_memory RUreason))
      (P:=V293_owned_record_cells(V293_record_layout OwnershipWaiting 6(wait RUreason(Int.repr 3))RUmessage pend));[ |exact Opened].
    intros st H. eapply V293_owned_record_cells_load with(cells:=V293_record_layout OwnershipWaiting 6(wait RUreason(Int.repr 3))RUmessage pend);[unfold V293_record_layout,RUreason;apply in_or_app;right;right;right;left;reflexivity|exact H]. }
  exists pend. split;[ |exact Opened].
  eapply V293_byteval_injective_bounded;[exact Bound|lia| ].
  pose proof(CFpend_load RUreason). congruence.
Qed.

Theorem CF_time_selected : exists pend, pend=7 /\
  DHstate(CFpend_memory os_stat_time) |= V293_owned_record_cells
    (V293_record_layout OwnershipWaiting 6(wait os_stat_time(Int.repr 3))RUmessage pend) **
  V293_owned_record_cells(V293_tick_wait_missing(V293_tick_wait_node 41%positive 8%Z 3%Z os_stat_time pend 6)os_stat_time TickNext).
Proof.
  pose proof(V293_tick_wait_record_open 41%positive 8%Z 3%Z os_stat_time RUmessage 6 7 _
    ltac:(lia) ltac:(intros;lia) _ CF_time_pend)as Opened.
  destruct Opened as[pend Opened]. apply astar_l_apure_elim in Opened.
  destruct Opened as[[Bound Time]Opened]. specialize(Time eq_refl). subst pend.
  exists 7. split;[reflexivity|exact Opened].
Qed.

Theorem CFexecution_control : forall P ks(sd:ossched), exists Mf,
  RUstate 1(RUmemory 1) |= CFpre 1 /\
  RUexecution P ks 1 Mf /\ RUexpiry_reads Mf /\
  load Tint8 Mf(93%positive,0%Z)=Some(V293_byteval 80) /\
  RUout 1 Mf |= V293_tick_ready_wait_post 93%positive 92%positive 95%positive 96%positive
    (RUnode 1)RUreason RUmessage 70%positive TickNext RUframe /\
  ~ RUneutralized 1 Mf |= V293_time_ready_core 93%positive 92%positive 95%positive 96%positive ** Atrue.
Proof.
  intros P ks sd. destruct(RUexpiry_control P ks sd)as(Mf&Exec&Reads&Post&Rejected).
  exists Mf. split;[apply CFentry| ]. split;[exact Exec| ]. split;[exact Reads| ].
  split;[exact(proj1 Reads)| ]. split;[exact Post| ].
  apply RUreject_neutralized;exact(proj1 Reads).
Qed.

Theorem CFcountdown : forall P ks(sd:ossched) d, (d=0%Z \/ d=3%Z) -> exists Mf,
  RUstate d(RUmemory d) |= CFpre d /\ RUexecution P ks d Mf /\
  load Tint8 Mf(93%positive,0%Z)=Some(V293_byteval 16) /\
  load Tint32 Mf(41%positive,52%Z)=Some(Vint32(Int.repr(V293_tick_after_delay d))) /\
  load Tint8 Mf(41%positive,57%Z)=Some(V293_byteval 0) /\
  load Tint32 Mf(96%positive,0%Z)=Some(Vint32(Int.repr 37)) /\
  load Tint32 Mf(90%positive,0%Z)=Some(Vint32(Int.repr 99)).
Proof.
  intros P ks sd d Cases. destruct(RUbranch_cases P ks sd d Cases)as(Mf&Exec&Task&Reads).
  exists Mf. split;[apply CFentry| ]. split;assumption.
Qed.
