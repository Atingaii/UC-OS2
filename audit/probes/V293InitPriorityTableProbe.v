(* Finite write-phase entry and single-slot counterexample, not boot reachability.
   The clear example explicitly reuses the frozen 780-byte entry proof. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitFunction.
Require Import CertiOS.certiucos.v293.code.V293OSMemClr.
Require Import CertiOS.certiucos.v293.code.V293OSInitTCBClear.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.proofs.V293InitPriorityTable.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBClear.
Require Import CertiOS.certiucos.v293.proofs.V293MemClr.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293NullBytes.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require CertiOS.audit.probes.V293InitTCBClearProbe.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope Z_scope.
Definition IPTask : tid := (301%positive,Int.zero).
Definition IPPositive := update_nth_val 12 (repeat Vnull 13) (Vptr IPTask).
Definition IPNegative := update_nth_val 0 IPPositive (Vptr IPTask).
Definition IPTasks : TcbMod.map := set emp IPTask (Int.repr 12,rdy,Vnull).
Definition IPGE : env := set emp 92%Z (84%positive,Tarray(Tptr V293_tcb_type)13).
Definition IPLE : env := set(set emp 101%Z (90%positive,Tint8))
  108%Z (91%positive,Tptr V293_tcb_type).
Definition IPInputs : list V293_record_cell :=
 [((90%positive,0),Tint8,V293_byteval 12);
  ((91%positive,0),Tptr V293_tcb_type,Vptr IPTask)].
Definition IPFrame : list V293_record_cell := [((99%positive,0),Tint32,Vint32(Int.repr 123))].
Definition IPCells := V293_priority_cells 84%positive 0 (repeat Vnull 13)++IPInputs++IPFrame.
Fixpoint IPMemory (cells : list V293_record_cell) : mem :=
  match cells with []=>emp | ((b,off),tp,v)::tail=>
    merge (V293_encoded_memory b off true (encode_val tp v)) (IPMemory tail) end.
Definition IPEntry := IPMemory IPCells.
Ltac IPOutside :=
  repeat first [rewrite V293_encoded_memory_outside by
    (first [left;congruence | right;cbn [length encode_val V293_byteval IPTask typelen list_repeat inj_pointer inj_bytes encode_int List.map];lia])
    | rewrite map_merge_semp by reflexivity];reflexivity.
Ltac IPApart b start count :=
  apply map_join_merge;apply map_disjoint;intros [other off];
  destruct (Pos.eq_dec other b) as [B|B];
  [subst other;destruct (Z_lt_dec off start) as [Low|Low];
    [left;apply V293_encoded_memory_outside;right;left;exact Low |
     destruct (Z_lt_dec off (start+count)) as [Inside|Outside];
     [right;left;IPOutside | left;apply V293_encoded_memory_outside;right;right;
       cbn [length encode_val V293_byteval IPTask typelen list_repeat inj_pointer inj_bytes encode_int List.map];lia]] |
   left;apply V293_encoded_memory_outside;left;exact B].
Lemma IPEntryOwned : V293_wstate IPGE IPLE IPEntry |= V293_rdy_raw_cells IPCells Aemp.
Proof.
  unfold IPEntry,IPCells. cbn [V293_priority_cells repeat IPInputs IPFrame app IPMemory V293_rdy_raw_cells].
  eapply V293_wstate_star with (m1:=V293_encoded_memory 84%positive 0%Z true (encode_val (Tptr V293_tcb_type) Vnull));
    [IPApart 84%positive 0%Z 4%Z | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
  eapply V293_wstate_star with (m1:=V293_encoded_memory 84%positive 4%Z true (encode_val (Tptr V293_tcb_type) Vnull));
    [IPApart 84%positive 4%Z 4%Z | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
  eapply V293_wstate_star with (m1:=V293_encoded_memory 84%positive 8%Z true (encode_val (Tptr V293_tcb_type) Vnull));
    [IPApart 84%positive 8%Z 4%Z | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
  eapply V293_wstate_star with (m1:=V293_encoded_memory 84%positive 12%Z true (encode_val (Tptr V293_tcb_type) Vnull));
    [IPApart 84%positive 12%Z 4%Z | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
  eapply V293_wstate_star with (m1:=V293_encoded_memory 84%positive 16%Z true (encode_val (Tptr V293_tcb_type) Vnull));
    [IPApart 84%positive 16%Z 4%Z | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
  eapply V293_wstate_star with (m1:=V293_encoded_memory 84%positive 20%Z true (encode_val (Tptr V293_tcb_type) Vnull));
    [IPApart 84%positive 20%Z 4%Z | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
  eapply V293_wstate_star with (m1:=V293_encoded_memory 84%positive 24%Z true (encode_val (Tptr V293_tcb_type) Vnull));
    [IPApart 84%positive 24%Z 4%Z | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
  eapply V293_wstate_star with (m1:=V293_encoded_memory 84%positive 28%Z true (encode_val (Tptr V293_tcb_type) Vnull));
    [IPApart 84%positive 28%Z 4%Z | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
  eapply V293_wstate_star with (m1:=V293_encoded_memory 84%positive 32%Z true (encode_val (Tptr V293_tcb_type) Vnull));
    [IPApart 84%positive 32%Z 4%Z | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
  eapply V293_wstate_star with (m1:=V293_encoded_memory 84%positive 36%Z true (encode_val (Tptr V293_tcb_type) Vnull));
    [IPApart 84%positive 36%Z 4%Z | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
  eapply V293_wstate_star with (m1:=V293_encoded_memory 84%positive 40%Z true (encode_val (Tptr V293_tcb_type) Vnull));
    [IPApart 84%positive 40%Z 4%Z | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
  eapply V293_wstate_star with (m1:=V293_encoded_memory 84%positive 44%Z true (encode_val (Tptr V293_tcb_type) Vnull));
    [IPApart 84%positive 44%Z 4%Z | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
  eapply V293_wstate_star with (m1:=V293_encoded_memory 84%positive 48%Z true (encode_val (Tptr V293_tcb_type) Vnull));
    [IPApart 84%positive 48%Z 4%Z | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
  eapply V293_wstate_star with (m1:=V293_encoded_memory 90%positive 0%Z true (encode_val (Tint8) (V293_byteval 12)));
    [IPApart 90%positive 0%Z 1%Z | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
  eapply V293_wstate_star with (m1:=V293_encoded_memory 91%positive 0%Z true (encode_val (Tptr V293_tcb_type) (Vptr IPTask)));
    [IPApart 91%positive 0%Z 4%Z | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
  eapply V293_wstate_star with (m1:=V293_encoded_memory 99%positive 0%Z true (encode_val (Tint32) (Vint32(Int.repr 123))));
    [IPApart 99%positive 0%Z 4%Z | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
  split;reflexivity.
Qed.
Lemma IPWritableEntry : V293_wstate IPGE IPLE IPEntry |=
  V293_owned_priority_table 84%positive (repeat Vnull 13) **
    V293_rdy_raw_cells IPInputs (V293_rdy_raw_cells IPFrame Aemp).
Proof.
  pose proof IPEntryOwned as H. unfold IPCells in H.
  repeat rewrite V293_raw_cells_append in H.
  change (V293_wstate IPGE IPLE IPEntry |= V293_rdy_raw_cells
    (V293_null_pointer_cells 84%positive 0 13)
    (V293_rdy_raw_cells IPInputs (V293_rdy_raw_cells IPFrame Aemp))) in H.
  apply V293_init_null_cells_owned in H;exact H.
Qed.
Lemma IPPositiveAccepted : V293_init_priority_table IPPositive IPTasks.
Proof. apply V293_init_priority_insert;[apply V293_init_priority_empty |lia |reflexivity |reflexivity]. Qed.
Lemma IPNegativeOldAccepted : V293_priority_table IPNegative IPTasks.
Proof.
  split;[reflexivity | ]. intros t pri status message Lookup.
  change (get IPTasks t=Some(pri,status,message)) in Lookup.
  unfold IPTasks in Lookup. destruct (tidspec.beq t IPTask) eqn:E.
  - apply tidspec.beq_true_eq in E;subst t. rewrite map_get_set in Lookup.
    inversion Lookup;subst. exists 12%nat. repeat split;try lia;reflexivity.
  - apply tidspec.beq_false_neq in E. rewrite map_get_set' in Lookup by congruence.
    rewrite map_emp_get in Lookup;discriminate.
Qed.
Lemma IPNegativeCanonicalRejected : ~ V293_init_priority_table IPNegative IPTasks.
Proof.
  intro H. destruct (proj1(V293_init_priority_pointer_exact IPNegative IPTasks 0 IPTask H ltac:(lia)) eq_refl)
    as (st&msg&Lookup).
  change (get IPTasks IPTask=Some(Int.repr 0,st,msg)) in Lookup.
  unfold IPTasks in Lookup. rewrite map_get_set in Lookup. discriminate.
Qed.
Lemma IPSingleSlotOnly : forall p, p<>0%nat -> nth p IPNegative Vnull=nth p IPPositive Vnull.
Proof. intros p Apart;apply V293_init_priority_nth_other;exact Apart. Qed.
Lemma IPLiteralSourceFragment :
  match V293_TCBInit_success_suffix 701%Z 702%Z with
  | sseq _ (sseq _ (sseq write _)) => Some write | _=>None end =
  Some(sassign(earrayelem(evar 92%Z)(evar 101%Z))(evar 108%Z)).
Proof. reflexivity. Qed.
Theorem IPConcreteWrite : forall P ks, exists Mf,
  cstepstar P (curs(sassign(earrayelem(evar 92%Z)(evar 101%Z))(evar 108%Z)),(kenil,ks))
    (IPGE,IPLE,IPEntry) (curs(sskip None),(kenil,ks)) (IPGE,IPLE,Mf) /\
  V293_init_priority_table IPPositive IPTasks /\
  V293_wstate IPGE IPLE Mf |= V293_owned_priority_table 84%positive IPPositive **
    V293_rdy_raw_cells IPInputs (V293_rdy_raw_cells IPFrame Aemp) /\
  V293_table_loads V293_tcb_type Mf 84%positive IPPositive /\
  load Tint32 Mf(99%positive,0)=Some(Vint32(Int.repr 123)).
Proof.
  intros P ks. destruct (V293_OS_TCBInit_canonical_priority_write (repeat Vnull 13) (emp:TcbMod.map)
    IPTask 12 P ks IPGE IPLE IPEntry (fun _=>false) (false,nil,nil) emp (spec_done None)
    (V293_rdy_raw_cells IPFrame Aemp) 84%positive 90%positive 91%positive
    V293_init_priority_empty ltac:(lia) eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl IPWritableEntry)
    as(Mf&Exec&Store&Canonical&Owned&Reads).
  exists Mf. split;[exact Exec | ]. split;[exact Canonical | ]. split;[exact Owned | ].
  split;[exact Reads | ].
  change(load Tint32(getmem(V293_wstate IPGE IPLE Mf))(99%positive,0)=Some(Vint32(Int.repr 123))).
  assert (Frame:V293_wstate IPGE IPLE Mf |= V293_rdy_raw_cells IPFrame
    (V293_owned_priority_table 84%positive IPPositive ** V293_rdy_raw_cells IPInputs Aemp)).
  { cbn [IPFrame IPInputs V293_rdy_raw_cells] in *;clear -Owned;sep auto. }
  eapply V293_rdy_raw_load;[ | |exact Frame];[left;reflexivity |reflexivity].
Qed.
(* Mutation is a controlled memory experiment, not a source-program path. *)
Theorem IPPhysicalSingleSlotControl : forall P ks, exists Good Bad,
  cstepstar P (curs(sassign(earrayelem(evar 92%Z)(evar 101%Z))(evar 108%Z)),(kenil,ks))
    (IPGE,IPLE,IPEntry) (curs(sskip None),(kenil,ks)) (IPGE,IPLE,Good) /\
  store(Tptr V293_tcb_type)Good(84%positive,0)(Vptr IPTask)=Some Bad /\
  V293_table_loads V293_tcb_type Good 84%positive IPPositive /\
  V293_table_loads V293_tcb_type Bad 84%positive IPNegative /\
  V293_priority_table IPPositive IPTasks /\ V293_priority_table IPNegative IPTasks /\
  V293_init_priority_table IPPositive IPTasks /\ ~V293_init_priority_table IPNegative IPTasks /\
  (forall b off,b<>84%positive \/ off<0 \/ 4<=off -> get Bad(b,off)=get Good(b,off)).
Proof.
  intros P ks. destruct(IPConcreteWrite P ks)as(Good&Exec&Canonical&Owned&Reads&Canary).
  destruct(V293_full_priority_table_any_slot_store IPPositive 84%positive _
    IPGE IPLE Good (fun _=>false) (false,nil,nil) emp (spec_done None)
    eq_refl Owned 0 (Vptr IPTask) ltac:(lia) eq_refl)as(Bad&Store&Final).
  assert (BadReads:V293_table_loads V293_tcb_type Bad 84%positive IPNegative).
  { eapply V293_full_priority_table_loads;[reflexivity |exact Final]. }
  exists Good. exists Bad. split;[exact Exec | ]. split;[exact Store | ].
  split;[exact Reads | ]. split;[exact BadReads | ]. split;[exact(proj1 Canonical) | ].
  split;[exact IPNegativeOldAccepted | ]. split;[exact Canonical | ].
  split;[exact IPNegativeCanonicalRejected | ]. intros b off Outside.
  unfold store in Store. eapply V293_storebytes_outside;[exact Store |exact Outside].
Qed.
Theorem IPCanonicalClear : forall ks, exists Mf,
  cstepstar V293InitTCBClearProbe.InitProgram
    (curs(V293_init_tcb_clear 101%Z 31%Z 32%Z),(kenil,ks))
    (V293InitTCBClearProbe.InitGE,emp,V293InitTCBClearProbe.InitMemory)
    (curs(sskip None),(kenil,ks)) (V293InitTCBClearProbe.InitGE,emp,Mf) /\
  V293_init_priority_table (repeat Vnull 13) (emp:TcbMod.map) /\
  V293_wstate V293InitTCBClearProbe.InitGE emp Mf |=
    V293_owned_priority_table 84%positive (repeat Vnull 13) **
    V293_rdy_raw_cells (V293_clr_bytes 82%positive 0 (repeat(Vint32 Int.zero)728)++
      V293InitTCBClearProbe.InitFrame) Atrue.
Proof.
  intro ks. eapply V293_OS_InitTCBList_canonical_clear;
    [apply V293InitTCBClearProbe.InitProgramLookup |discriminate |reflexivity |reflexivity |
      reflexivity |reflexivity |apply repeat_length |apply repeat_length |
      exact V293InitTCBClearProbe.InitLiteralEntry].
Qed.
Print Assumptions IPPhysicalSingleSlotControl.
Print Assumptions IPCanonicalClear.
