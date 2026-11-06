(* Literal physical TCB bytes, not an assumed task-record postcondition.
   Only the concrete priority byte varies; abstract selection stays at 12.
   Both arms execute the real startup call to the missing CPU port. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.certiucos.v293.code.V293OSStart.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.proofs.V293Start.
Require Import CertiOS.certiucos.v293.proofs.V293StartCurrent.
Require Import CertiOS.certiucos.v293.proofs.V293StartRecord.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBClear.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.audit.probes.V293StartProbe.
Require Import CertiOS.audit.probes.V293StartCurrentProbe.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.
Definition RecordFields n : list V293_record_cell :=
 [((90%positive,0%Z),(Tptr Tint32),(Vnull));
  ((90%positive,50%Z),(Tint8),(V293_byteval n));
  ((90%positive,48%Z),(Tint8),(Vint32 Int.zero));
  ((90%positive,49%Z),(Tint8),(Vint32 Int.zero));
  ((90%positive,44%Z),(Tint32),(Vint32 Int.zero));
  ((90%positive,4%Z),(Tptr Tvoid),(Vnull));
  ((90%positive,12%Z),(Tint32),(Vint32(Int.repr 128)));
  ((90%positive,8%Z),(Tptr Tint32),(Vnull));
  ((90%positive,16%Z),(Tint16),(Vint32 Int.zero));
  ((90%positive,18%Z),(Tint16),(Vint32 Int.zero));
  ((90%positive,55%Z),(Tint8),(Vint32 Int.zero));
  ((90%positive,52%Z),(Tint8),(V293_byteval 1));
  ((90%positive,51%Z),(Tint8),(V293_byteval 4));
  ((90%positive,54%Z),(Tint8),(V293_byteval 2));
  ((90%positive,53%Z),(Tint8),(V293_byteval 16));
  ((90%positive,28%Z),(Tcom_ptr 411%Z),(Vnull));
  ((90%positive,36%Z),(Tcom_ptr 412%Z),(Vnull));
  ((90%positive,32%Z),(Tptr Tvoid),(Vnull))].
Definition RecordFrame n := RecordFields n++StartFrame.
Definition RecordCells n := V293_start_cells 81%positive 82%positive 83%positive
  84%positive 85%positive 86%positive 12 (Vint32(Int.repr 7)) (Vint32(Int.repr 8))
  Vnull Vnull (Vint32 Int.zero) (Vptr StartTarget) (RecordFrame n).
Definition RecordOthers n := V293_start_other_cells 81%positive 82%positive 83%positive
  85%positive 86%positive 12 StartTarget (RecordFrame n).
Definition RecordRemainder := V293_tcb_init_record_remainder 90%positive 0%Z
  Vnull Vnull (Vint32 Int.zero) (Vint32(Int.repr 128)) Vnull (Vint32 Int.zero).

Theorem RecordInitializerIdentity : RecordFields 12 = V293_tcb_init_final_fields
  90%positive 0%Z 12 Vnull Vnull (Vint32 Int.zero) (Vint32(Int.repr 128)) Vnull (Vint32 Int.zero).
Proof. reflexivity. Qed.
Theorem RecordOnlyFactor : exists before after,
  RecordCells 12=before++((90%positive,50%Z),Tint8,V293_byteval 12)::after /\
  RecordCells 11=before++((90%positive,50%Z),Tint8,V293_byteval 11)::after.
Proof.
  exists (firstn 7 (RecordCells 12)). exists (skipn 8 (RecordCells 12)). split;reflexivity.
Qed.
Lemma RecordByteOutside : forall n b i,
 (b,i)<>(90%positive,50%Z) ->
 get (StartBytes (90%positive,50%Z) Tint8 (V293_byteval n)) (b,i)=None.
Proof.
 intros n b i Away. unfold StartBytes. cbn [fst snd].
 apply V293_encoded_memory_outside.
 destruct (Pos.eq_dec b 90%positive) as [Same|Different];[subst b |left;exact Different].
 right. cbn [V293_byteval length encode_val typelen inj_bytes encode_int List.map].
 assert (i<>50%Z) by congruence. lia.
Qed.
Lemma RecordMemoryFrame : forall before after a,
 a<>(90%positive,50%Z) ->
 get (StartMem (before++((90%positive,50%Z),Tint8,V293_byteval 12)::after)) a =
 get (StartMem (before++((90%positive,50%Z),Tint8,V293_byteval 11)::after)) a.
Proof.
 induction before as [ |[[a tp] v] tail IH];intros after [b i] Away;cbn [app StartMem].
 - rewrite !map_merge_semp by reflexivity.
   rewrite !RecordByteOutside by exact Away. reflexivity.
 - rewrite !map_merge_semp by reflexivity. rewrite IH by exact Away. reflexivity.
Qed.
Theorem RecordMemoryOnlyFactor : forall a,
 a<>(90%positive,50%Z) ->
 get (StartMem (RecordCells 12)) a=get (StartMem (RecordCells 11)) a.
Proof.
 intros a Away. destruct RecordOnlyFactor as (before&after&Positive&Negative).
 rewrite Positive,Negative. apply RecordMemoryFrame;exact Away.
Qed.
Ltac RecordOutside :=
 unfold StartBytes,V293_witness_inputs,V293_witness_table,V293_witness_group,
   V293_witness_rows,V293_nat_memory;cbn [fst snd];unfold addr,offset in *;
 repeat first [rewrite V293_encoded_memory_outside by
   (first [left;congruence | right;cbn [V293_byteval length encode_val typelen list_repeat inj_pointer inj_bytes encode_int List.map];lia])
   | rewrite map_merge_semp by reflexivity];reflexivity.
Ltac RecordApart b start count :=
 apply map_join_merge;apply map_disjoint;intros [other off];
 destruct (Pos.eq_dec other b) as [B|B];
 [subst other;destruct (Z_lt_dec off start) as [Low|Low];
  [left;unfold StartBytes;cbn [fst snd];apply V293_encoded_memory_outside;right;left;exact Low |
   destruct (Z_lt_dec off (start+count)) as [Inside|Outside];
   [right;left;RecordOutside | left;unfold StartBytes;cbn [fst snd];apply V293_encoded_memory_outside;right;right;
     cbn [V293_byteval length encode_val typelen list_repeat inj_pointer inj_bytes encode_int List.map];lia]] |
  left;unfold StartBytes;cbn [fst snd];apply V293_encoded_memory_outside;left;exact B].
Theorem RecordLiteralEntry : forall n,
 CurrentState (StartMem (RecordCells n)) |= V293_rdy_raw_cells (RecordCells n) Atrue.
Proof.
 intro n. eapply V293_raw_cells_environment with (ge:=StartGE) (le:=(emp:env));[right;reflexivity | ].
 change (StartState (StartMem (RecordCells n)) |= V293_rdy_raw_cells (RecordCells n) Atrue).
 unfold RecordCells,V293_start_cells,RecordFrame,RecordFields,StartFrame.
 cbn [StartMem V293_rdy_raw_cells app].
 eapply StartStar with (m1:=StartBytes (81%positive,0%Z) (Tint8) (Vint32(Int.repr 7))) (o1:=emp) (o2:=StartAbs);
 [StartApart 81%positive |apply map_join_comm;apply map_join_emp|
 split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
 eapply StartStar with (m1:=StartBytes (82%positive,0%Z) (Tint8) (Vint32(Int.repr 8))) (o1:=emp) (o2:=StartAbs);
 [StartApart 82%positive |apply map_join_comm;apply map_join_emp|
 split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
 eapply StartStar with (m1:=StartBytes (83%positive,0%Z) (Tptr V293_tcb_type) (Vnull)) (o1:=emp) (o2:=StartAbs);
 [StartApart 83%positive |apply map_join_comm;apply map_join_emp|
 split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
 eapply StartStar with (m1:=StartBytes (84%positive,0%Z) (Tptr V293_tcb_type) (Vnull)) (o1:=emp) (o2:=StartAbs);
 [StartApart 84%positive |apply map_join_comm;apply map_join_emp|
 split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
 eapply StartStar with (m1:=StartBytes (85%positive,0%Z) (Tint8) (Vint32 Int.zero)) (o1:=emp) (o2:=StartAbs);
 [StartApart 85%positive |apply map_join_comm;apply map_join_emp|
 split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
 eapply StartStar with (m1:=StartBytes (86%positive,48%Z) (Tptr V293_tcb_type) (Vptr StartTarget)) (o1:=emp) (o2:=StartAbs);
 [StartApart 86%positive |apply map_join_comm;apply map_join_emp|
 split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
 eapply StartStar with (m1:=StartBytes (90%positive,0%Z) (Tptr Tint32) (Vnull)) (o1:=emp) (o2:=StartAbs);
 [RecordApart 90%positive 0%Z 4%Z |apply map_join_comm;apply map_join_emp|
 split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
 eapply StartStar with (m1:=StartBytes (90%positive,50%Z) (Tint8) (V293_byteval n)) (o1:=emp) (o2:=StartAbs);
 [RecordApart 90%positive 50%Z 1%Z |apply map_join_comm;apply map_join_emp|
 split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
 eapply StartStar with (m1:=StartBytes (90%positive,48%Z) (Tint8) (Vint32 Int.zero)) (o1:=emp) (o2:=StartAbs);
 [RecordApart 90%positive 48%Z 1%Z |apply map_join_comm;apply map_join_emp|
 split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
 eapply StartStar with (m1:=StartBytes (90%positive,49%Z) (Tint8) (Vint32 Int.zero)) (o1:=emp) (o2:=StartAbs);
 [RecordApart 90%positive 49%Z 1%Z |apply map_join_comm;apply map_join_emp|
 split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
 eapply StartStar with (m1:=StartBytes (90%positive,44%Z) (Tint32) (Vint32 Int.zero)) (o1:=emp) (o2:=StartAbs);
 [RecordApart 90%positive 44%Z 4%Z |apply map_join_comm;apply map_join_emp|
 split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
 eapply StartStar with (m1:=StartBytes (90%positive,4%Z) (Tptr Tvoid) (Vnull)) (o1:=emp) (o2:=StartAbs);
 [RecordApart 90%positive 4%Z 4%Z |apply map_join_comm;apply map_join_emp|
 split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
 eapply StartStar with (m1:=StartBytes (90%positive,12%Z) (Tint32) (Vint32(Int.repr 128))) (o1:=emp) (o2:=StartAbs);
 [RecordApart 90%positive 12%Z 4%Z |apply map_join_comm;apply map_join_emp|
 split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
 eapply StartStar with (m1:=StartBytes (90%positive,8%Z) (Tptr Tint32) (Vnull)) (o1:=emp) (o2:=StartAbs);
 [RecordApart 90%positive 8%Z 4%Z |apply map_join_comm;apply map_join_emp|
 split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
 eapply StartStar with (m1:=StartBytes (90%positive,16%Z) (Tint16) (Vint32 Int.zero)) (o1:=emp) (o2:=StartAbs);
 [RecordApart 90%positive 16%Z 2%Z |apply map_join_comm;apply map_join_emp|
 split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
 eapply StartStar with (m1:=StartBytes (90%positive,18%Z) (Tint16) (Vint32 Int.zero)) (o1:=emp) (o2:=StartAbs);
 [RecordApart 90%positive 18%Z 2%Z |apply map_join_comm;apply map_join_emp|
 split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
 eapply StartStar with (m1:=StartBytes (90%positive,55%Z) (Tint8) (Vint32 Int.zero)) (o1:=emp) (o2:=StartAbs);
 [RecordApart 90%positive 55%Z 1%Z |apply map_join_comm;apply map_join_emp|
 split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
 eapply StartStar with (m1:=StartBytes (90%positive,52%Z) (Tint8) (V293_byteval 1)) (o1:=emp) (o2:=StartAbs);
 [RecordApart 90%positive 52%Z 1%Z |apply map_join_comm;apply map_join_emp|
 split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
 eapply StartStar with (m1:=StartBytes (90%positive,51%Z) (Tint8) (V293_byteval 4)) (o1:=emp) (o2:=StartAbs);
 [RecordApart 90%positive 51%Z 1%Z |apply map_join_comm;apply map_join_emp|
 split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
 eapply StartStar with (m1:=StartBytes (90%positive,54%Z) (Tint8) (V293_byteval 2)) (o1:=emp) (o2:=StartAbs);
 [RecordApart 90%positive 54%Z 1%Z |apply map_join_comm;apply map_join_emp|
 split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
 eapply StartStar with (m1:=StartBytes (90%positive,53%Z) (Tint8) (V293_byteval 16)) (o1:=emp) (o2:=StartAbs);
 [RecordApart 90%positive 53%Z 1%Z |apply map_join_comm;apply map_join_emp|
 split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
 eapply StartStar with (m1:=StartBytes (90%positive,28%Z) (Tcom_ptr 411%Z) (Vnull)) (o1:=emp) (o2:=StartAbs);
 [RecordApart 90%positive 28%Z 4%Z |apply map_join_comm;apply map_join_emp|
 split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
 eapply StartStar with (m1:=StartBytes (90%positive,36%Z) (Tcom_ptr 412%Z) (Vnull)) (o1:=emp) (o2:=StartAbs);
 [RecordApart 90%positive 36%Z 4%Z |apply map_join_comm;apply map_join_emp|
 split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
 eapply StartStar with (m1:=StartBytes (90%positive,32%Z) (Tptr Tvoid) (Vnull)) (o1:=emp) (o2:=StartAbs);
 [RecordApart 90%positive 32%Z 4%Z |apply map_join_comm;apply map_join_emp|
 split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
 eapply StartStar with (m1:=StartBytes (99%positive,0%Z) (Tint32) (Vint32(Int.repr 123))) (o1:=emp) (o2:=StartAbs);
 [StartApart 99%positive |apply map_join_comm;apply map_join_emp|
 split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
 exact I.
Qed.
Theorem RecordNoInitialTask : forall n t,
 ~ CurrentState (StartMem (RecordCells n)) |= CurTid t ** Atrue.
Proof.
 intros n t Held.
 destruct (V293_shared_current_read _ _ _ _ _ _ _ _ _ Held) as (b&tp&Binding&Read).
 change (Some (84%positive,Tptr V293_tcb_type)=Some (b,Tptr tp)) in Binding.
 inversion Binding;subst b tp.
 assert (Null : load (Tptr V293_tcb_type) (StartMem (RecordCells n)) (84%positive,0%Z)=Some Vnull).
 { change (load (Tptr V293_tcb_type) (getmem (CurrentState (StartMem (RecordCells n)))) (84%positive,0%Z)=Some Vnull).
   eapply V293_rdy_raw_load;[ |reflexivity |apply RecordLiteralEntry].
   unfold RecordCells,V293_start_cells;do 3 right;left;reflexivity. }
 change (load (Tptr V293_tcb_type) (StartMem (RecordCells n)) (84%positive,0%Z)=Some(Vptr t)) in Read.
 congruence.
Qed.
Theorem RecordInputReads : forall n,
 V293_sched_read_memory (StartMem (RecordCells n)) 1%positive 2%positive 3%positive 0 16 2.
Proof.
 intro n. pose proof (V293_sched_inputs_load 1%positive 2%positive 3%positive 0 16 2
   ltac:(lia) ltac:(lia) ltac:(lia) _ V293_witness_inputs_sat) as Base.
 change (V293_sched_read_memory V293_witness_inputs 1%positive 2%positive 3%positive 0 16 2) in Base.
 assert (Frame : forall b i,(b<4)%positive ->
   get (StartMem (RecordCells n)) (b,i)=get V293_witness_inputs (b,i)).
 { intros b i Bound. unfold RecordCells,V293_start_cells,RecordFrame,RecordFields,StartFrame;cbn [StartMem app].
   unfold StartBytes;cbn [fst snd];unfold addr,offset in *.
   repeat first [rewrite V293_encoded_memory_outside by (left;lia)
                | rewrite map_merge_semp by reflexivity].
   destruct (get V293_witness_inputs (b,i));reflexivity. }
 destruct Base as (G & Tbl & Low & High). unfold V293_sched_read_memory. split.
 - unfold load,loadm;cbn [typelen loadbytes]. rewrite Frame by lia. exact G.
 - split.
   + intros k Bound. unfold load,loadm;cbn [typelen loadbytes]. rewrite Frame by lia. apply Tbl;exact Bound.
   + split;unfold load,loadm;cbn [typelen loadbytes];rewrite Frame by lia;assumption.
Qed.
Theorem RecordColdCall : forall n, exists Mf,
 cstepstar CurrentProgram (curs (scall 900%Z nil),(kenil,kstop))
 (CurrentGE,StartCaller,StartMem (RecordCells n))
 (curs (sfexec 902%Z nil nil),(kenil,kseq sret (kcall 900%Z CurrentBody StartCaller kstop)))
 (CurrentGE,(emp:env),Mf) /\
 CurrentState Mf |= CurTid StartTarget ** CurTid StartTarget ** V293_rdy_raw_cells (RecordOthers n) Atrue.
Proof.
 intro n. eapply (V293_OSStart_call_establishes_current (RecordFrame n) CurrentProgram kstop CurrentGE StartCaller
  (StartMem (RecordCells n)) (fun _=>false) (false,nil,nil) StartAbs (spec_done None)
  900%Z 108%Z 901%Z 105%Z 103%Z 109%Z 106%Z 902%Z
  100%Z 101%Z 102%Z 104%Z 85%positive 82%positive 81%positive 86%positive
  83%positive 84%positive 1%positive 2%positive 3%positive 0 16
  (Vint32(Int.repr 7)) (Vint32(Int.repr 8)) Vnull Vnull StartTarget);
 try reflexivity;try lia.
 - exact StartNonempty.
 - apply RecordInputReads.
 - apply RecordLiteralEntry.
Qed.
Theorem RecordGoodCall : exists Mf,
 get StartTasks StartTarget=Some(Int.repr 12,rdy,Vnull) /\
 V293_scheduler StartAbs StartTarget /\
 cstepstar CurrentProgram (curs (scall 900%Z nil),(kenil,kstop))
 (CurrentGE,StartCaller,StartMem (RecordCells 12))
 (curs (sfexec 902%Z nil nil),(kenil,kseq sret (kcall 900%Z CurrentBody StartCaller kstop)))
 (CurrentGE,(emp:env),Mf) /\
 CurrentState Mf |= CurTid StartTarget ** CurTid StartTarget **
 V293_owned_task_record StartTarget (Int.repr 12) rdy Vnull **
 V293_rdy_raw_cells RecordRemainder (V293_rdy_raw_cells CurrentOthers Atrue).
Proof.
 eapply (V293_OSStart_initialized_task StartEntries StartTasks StartFrame CurrentProgram kstop CurrentGE StartCaller
  (StartMem (RecordCells 12)) (fun _=>false) (false,nil,nil) StartAbs (spec_done None)
  900%Z 108%Z 901%Z 105%Z 103%Z 109%Z 106%Z 902%Z
  100%Z 101%Z 102%Z 104%Z 85%positive 82%positive 81%positive 86%positive
  83%positive 84%positive 1%positive 2%positive 3%positive 0 16
  (Vint32(Int.repr 7)) (Vint32(Int.repr 8)) Vnull Vnull 90%positive 0%Z 12
  Vnull Vnull (Vint32 Int.zero) (Vint32(Int.repr 128)) Vnull (Vint32 Int.zero));
 try reflexivity;try lia.
 - exact StartNonempty.
 - split;unfold Int.max_unsigned,Int.modulus,Int.wordsize;simpl;lia.
 - repeat split;reflexivity.
 - exact StartBitmap.
 - exact StartTable.
 - apply RecordInputReads.
 - apply RecordLiteralEntry.
Qed.
Theorem RecordPriorityRead : forall n M,
 rule_type_val_match Tint8 (V293_byteval n)=true ->
 CurrentState M |= CurTid StartTarget ** CurTid StartTarget ** V293_rdy_raw_cells (RecordOthers n) Atrue ->
 load Tint8 M (90%positive,50%Z)=Some(V293_byteval n).
Proof.
 intros n M Valid Owned.
 assert (Raw : CurrentState M |= V293_rdy_raw_cells (RecordOthers n) Atrue ** Atrue)
   by (clear -Owned;sep auto).
 change (load Tint8 (getmem (CurrentState M)) (90%positive,50%Z)=Some(V293_byteval n)).
 eapply V293_star_load_l;[ |exact Raw]. intros st HS.
 eapply V293_rdy_raw_load;[ |exact Valid |exact HS].
 unfold RecordOthers,V293_start_other_cells,RecordFrame,RecordFields. cbn [In app];tauto.
Qed.
Theorem RecordBadCall : exists Mf,
 cstepstar CurrentProgram (curs (scall 900%Z nil),(kenil,kstop))
 (CurrentGE,StartCaller,StartMem (RecordCells 11))
 (curs (sfexec 902%Z nil nil),(kenil,kseq sret (kcall 900%Z CurrentBody StartCaller kstop)))
 (CurrentGE,(emp:env),Mf) /\
 (CurrentState Mf |= CurTid StartTarget ** CurTid StartTarget ** V293_rdy_raw_cells (RecordOthers 11) Atrue) /\
 load Tint8 Mf (90%positive,50%Z)=Some(V293_byteval 11) /\
 ~ CurrentState Mf |= V293_owned_task_record StartTarget (Int.repr 12) rdy Vnull ** Atrue.
Proof.
 destruct (RecordColdCall 11) as (Mf&Exec&Owned). exists Mf.
 split;[exact Exec | ]. split;[exact Owned | ].
 pose proof (RecordPriorityRead 11 Mf eq_refl Owned) as Read.
 split;[exact Read | ]. intro FalseRecord.
 apply sat_split in FalseRecord.
 destruct FalseRecord as (m1&m2&o1&o2&JM&JO&Record&Other).
 pose proof (V293_owned_task_record_sound _ _ _ _ _ Record) as Sound.
 assert (Full : V293_task_record Mf StartTarget (Int.repr 12) rdy Vnull).
 { eapply V293_task_record_sub;[exists m2;exact JM |exact Sound]. }
 destruct Full as (p&Range&Priority&Fields&Status).
 assert (p=12).
 { eapply V293_priority_repr_injective;[exact Range |lia |symmetry;exact Priority]. }
 subst p. destruct Fields as (Physical&Rest).
 change (load Tint8 Mf (90%positive,50%Z)=Some(V293_byteval 12)) in Physical.
 rewrite Read in Physical. discriminate.
Qed.
Theorem RecordPortMissing : CurrentProgram 902%Z=None.
Proof. reflexivity. Qed.
Print Assumptions RecordLiteralEntry.
Print Assumptions RecordColdCall.
Print Assumptions RecordGoodCall.
Print Assumptions RecordBadCall.
Print Assumptions RecordOnlyFactor.

Print Assumptions RecordMemoryOnlyFactor.
Print Assumptions RecordNoInitialTask.

Theorem RecordGoodPostSound : forall M,
 CurrentState M |= CurTid StartTarget ** CurTid StartTarget **
 V293_owned_task_record StartTarget (Int.repr 12) rdy Vnull **
 V293_rdy_raw_cells RecordRemainder (V293_rdy_raw_cells CurrentOthers Atrue) ->
 V293_task_record M StartTarget (Int.repr 12) rdy Vnull /\
 load (Tptr V293_tcb_type) M (84%positive,0%Z)=Some(Vptr StartTarget) /\
 load Tint8 M (85%positive,0%Z)=Some(Vint32 Int.zero) /\
 load Tint32 M (99%positive,0%Z)=Some(Vint32(Int.repr 123)).
Proof.
 intros M Owned.
 assert (Physical : CurrentState M |=
   V293_owned_task_record StartTarget (Int.repr 12) rdy Vnull ** Atrue)
   by (clear -Owned;sep auto).
 split.
 - apply sat_split in Physical. destruct Physical as (m1&m2&o1&o2&JM&JO&Record&Rest).
   eapply V293_task_record_sub;[exists m2;exact JM | ].
   exact (V293_owned_task_record_sound _ _ _ _ _ Record).
 - apply CurrentPostReads.
   unfold RecordRemainder,V293_tcb_init_record_remainder in Owned.
   unfold CurrentOthers,V293_start_other_cells,StartFrame in *.
   cbn [V293_rdy_raw_cells app] in Owned |- *. clear -Owned. sep auto.
Qed.
Theorem RecordGoodSameMf : exists Mf,
 get StartTasks StartTarget=Some(Int.repr 12,rdy,Vnull) /\
 V293_scheduler StartAbs StartTarget /\
 cstepstar CurrentProgram (curs (scall 900%Z nil),(kenil,kstop))
 (CurrentGE,StartCaller,StartMem (RecordCells 12))
 (curs (sfexec 902%Z nil nil),(kenil,kseq sret (kcall 900%Z CurrentBody StartCaller kstop)))
 (CurrentGE,(emp:env),Mf) /\
 (CurrentState Mf |= CurTid StartTarget ** CurTid StartTarget **
  V293_owned_task_record StartTarget (Int.repr 12) rdy Vnull **
  V293_rdy_raw_cells RecordRemainder (V293_rdy_raw_cells CurrentOthers Atrue)) /\
 V293_task_record Mf StartTarget (Int.repr 12) rdy Vnull /\
 load (Tptr V293_tcb_type) Mf (84%positive,0%Z)=Some(Vptr StartTarget) /\
 load Tint8 Mf (85%positive,0%Z)=Some(Vint32 Int.zero) /\
 load Tint32 Mf (99%positive,0%Z)=Some(Vint32(Int.repr 123)).
Proof.
 destruct RecordGoodCall as (Mf&Member&Highest&Exec&Owned). exists Mf.
 split;[exact Member | ]. split;[exact Highest | ]. split;[exact Exec | ].
 split;[exact Owned | ]. apply RecordGoodPostSound;exact Owned.
Qed.
Print Assumptions RecordGoodPostSound.
Print Assumptions RecordGoodSameMf.
