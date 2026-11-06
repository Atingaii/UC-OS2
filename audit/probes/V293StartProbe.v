(* Literal pre-start memory, nonempty ready bitmap and a real two-function
   program. CPU port is deliberately absent. Not a reachable OSInit witness. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.certiucos.v293.code.V293OSStart.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.proofs.V293Start.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import Coq.Lists.List.ListNotations.
Local Open Scope nat_scope.
Definition StartGE : env := fold_right (fun '(name,b,tp) e=>set e name (b,tp)) emp
 ((100%Z,1%positive,Tarray Tint8 256)::(101%Z,2%positive,Tint8)::
  (102%Z,3%positive,Tarray Tint8 2)::(103%Z,81%positive,Tint8)::
  (105%Z,82%positive,Tint8)::(106%Z,83%positive,Tptr V293_tcb_type)::
  (107%Z,84%positive,Tptr V293_tcb_type)::(108%Z,85%positive,Tint8)::
  (109%Z,86%positive,Tarray (Tptr V293_tcb_type) 13)::nil).
Definition StartBody := V293_OSStart_body 108%Z 901%Z 105%Z 103%Z 109%Z 106%Z 107%Z 902%Z.
Definition StartProgram : progunit := fun f=>
 if Z.eqb f 900 then Some (V293_OSStart_function 108%Z 901%Z 105%Z 103%Z 109%Z 106%Z 107%Z 902%Z)
 else if Z.eqb f 901 then Some (V293_OSSchedNew_function 100%Z 101%Z 102%Z 103%Z 104%Z) else None.
Definition StartCaller : env := sig 700%Z (98%positive,Tint32).
Definition StartTarget : addrval := (90%positive,Int.zero).
Definition StartFrame : list V293_record_cell := cons ((99%positive,0%Z),Tint32,Vint32(Int.repr 123)) nil.
Definition StartCells (active:bool) := V293_start_cells 81%positive 82%positive 83%positive
  84%positive 85%positive 86%positive 12 (Vint32(Int.repr 7)) (Vint32(Int.repr 8))
  Vnull Vnull (Vint32(if active then Int.one else Int.zero)) (Vptr StartTarget) StartFrame.
Definition StartFinal := V293_start_final 81%positive 82%positive 83%positive
  84%positive 85%positive 86%positive 12 StartTarget StartFrame.
Definition StartBytes a tp v := V293_encoded_memory (fst a) (snd a) true (encode_val tp v).
Fixpoint StartMem cells : mem := match cells with
 | nil=>V293_witness_inputs
 | (a,tp,v)::tail=>merge (StartBytes a tp v) (StartMem tail)
 end.
Definition StartTasks : TcbMod.map := sig StartTarget (Int.repr 12,rdy,Vnull).
Definition StartEntries := (repeat Vnull 12)++cons (Vptr StartTarget) nil.
Definition StartAbs : osabst := sig abstcblsid (abstcblist StartTasks).
Definition StartState M : RstateOP := (StartGE,emp,M,(fun _=>false),(false,nil,nil),StartAbs,spec_done None).
Lemma StartStar : forall m1 m2 m o1 o2 p q,
 join m1 m2 m -> join o1 o2 StartAbs ->
 (StartGE,emp,m1,(fun _=>false),(false,nil,nil),o1,spec_done None) |= p ->
 (StartGE,emp,m2,(fun _=>false),(false,nil,nil),o2,spec_done None) |= q ->
 StartState m |= p ** q.
Proof.
 intros. exists m1. exists m2. exists m. exists o1. exists o2. exists StartAbs.
 repeat first [assumption|reflexivity|split].
Qed.
Ltac StartOutside :=
 unfold StartBytes,V293_witness_inputs,V293_witness_table,V293_witness_group,
   V293_witness_rows,V293_nat_memory;cbn [fst snd];unfold addr,offset in *;
 repeat first [rewrite V293_encoded_memory_outside by (left;congruence)
              | rewrite map_merge_semp by reflexivity];reflexivity.
Ltac StartApart b :=
 apply map_join_merge;apply map_disjoint;intros [other off];
 destruct (Pos.eq_dec other b);[subst other;right;left;StartOutside|left;
 unfold StartBytes;cbn [fst snd];apply V293_encoded_memory_outside;left;assumption].
Theorem StartLiteralEntry : forall active,
 StartState (StartMem (StartCells active)) |= V293_rdy_raw_cells (StartCells active) Atrue.
Proof.
 intros active. unfold StartCells,V293_start_cells,StartFrame.
 cbn [StartMem V293_rdy_raw_cells].
 eapply StartStar with (m1:=StartBytes (81%positive,0%Z) (Tint8) (Vint32(Int.repr 7))) (o1:=emp) (o2:=StartAbs);
 [StartApart 81%positive|apply map_join_comm;apply map_join_emp|
 split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
 eapply StartStar with (m1:=StartBytes (82%positive,0%Z) (Tint8) (Vint32(Int.repr 8))) (o1:=emp) (o2:=StartAbs);
 [StartApart 82%positive|apply map_join_comm;apply map_join_emp|
 split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
 eapply StartStar with (m1:=StartBytes (83%positive,0%Z) (Tptr V293_tcb_type) (Vnull)) (o1:=emp) (o2:=StartAbs);
 [StartApart 83%positive|apply map_join_comm;apply map_join_emp|
 split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
 eapply StartStar with (m1:=StartBytes (84%positive,0%Z) (Tptr V293_tcb_type) (Vnull)) (o1:=emp) (o2:=StartAbs);
 [StartApart 84%positive|apply map_join_comm;apply map_join_emp|
 split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
 eapply StartStar with (m1:=StartBytes (85%positive,0%Z) (Tint8) (Vint32(if active then Int.one else Int.zero))) (o1:=emp) (o2:=StartAbs);
 [StartApart 85%positive|apply map_join_comm;apply map_join_emp|
 split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
 eapply StartStar with (m1:=StartBytes (86%positive,48%Z) (Tptr V293_tcb_type) (Vptr StartTarget)) (o1:=emp) (o2:=StartAbs);
 [StartApart 86%positive|apply map_join_comm;apply map_join_emp|
 split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
 eapply StartStar with (m1:=StartBytes (99%positive,0%Z) (Tint32) (Vint32(Int.repr 123))) (o1:=emp) (o2:=StartAbs);
 [StartApart 99%positive|apply map_join_comm;apply map_join_emp|
 split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
 exact I.
Qed.
Lemma StartInputReads : forall active,
 V293_sched_read_memory (StartMem (StartCells active)) 1%positive 2%positive 3%positive 0 16 2.
Proof.
 intros active.
 pose proof (V293_sched_inputs_load 1%positive 2%positive 3%positive 0 16 2
   ltac:(lia) ltac:(lia) ltac:(lia) _ V293_witness_inputs_sat) as Base.
 change (V293_sched_read_memory V293_witness_inputs 1%positive 2%positive 3%positive 0 16 2) in Base.
 assert (Frame : forall b i,(b<4)%positive ->
   get (StartMem (StartCells active)) (b,i)=get V293_witness_inputs (b,i)).
 { intros b i Bound. unfold StartCells,V293_start_cells,StartFrame;cbn [StartMem].
   unfold StartBytes;cbn [fst snd];unfold addr,offset in *.
   repeat first [rewrite V293_encoded_memory_outside by (left;lia)
                | rewrite map_merge_semp by reflexivity].
   destruct (get V293_witness_inputs (b,i));reflexivity. }
 destruct Base as (G & Tbl & Low & High). unfold V293_sched_read_memory. split.
 - unfold load,loadm;cbn [typelen loadbytes]. rewrite Frame by lia. exact G.
 - split.
   + intros n Bound. unfold load,loadm;cbn [typelen loadbytes]. rewrite Frame by lia. apply Tbl;exact Bound.
   + split;unfold load,loadm;cbn [typelen loadbytes];rewrite Frame by lia;assumption.
Qed.
Lemma StartNonempty : exists p,V293_bitmap_ready 0 16 p.
Proof. exists 12. vm_compute. right. repeat split;try reflexivity;lia. Qed.
Lemma StartTable : V293_priority_table StartEntries StartTasks.
Proof.
 split;[vm_compute;reflexivity| ]. intros t p st m Read.
 unfold StartTasks in Read. destruct (tid_eq_dec StartTarget t) as [E|E].
 - subst t. rewrite map_get_sig in Read. inversion Read;subst.
   exists 12. repeat split;try lia;vm_compute;reflexivity.
 - rewrite map_get_sig' in Read by exact E. discriminate.
Qed.
Lemma StartBitmap : V293_bitmap_tasks 0 16 StartTasks.
Proof.
 intros p Bound. unfold V293_bitmap_ready.
 assert (Bit : (p<8 /\ Nat.testbit 0 p=true) \/ (8<=p /\ p<13 /\ Nat.testbit 16 (p-8)=true) <-> p=12).
 { assert (p=0 \/ p=1 \/ p=2 \/ p=3 \/ p=4 \/ p=5 \/ p=6 \/ p=7 \/ p=8 \/ p=9 \/ p=10 \/ p=11 \/ p=12) by lia.
   repeat destruct H as [H|H];subst p;vm_compute;intuition lia. }
 rewrite Bit. split.
 - intro E;subst p. exists StartTarget. exists Vnull. apply map_get_sig.
 - intros (t&m&Read). unfold StartTasks in Read.
   destruct (tid_eq_dec StartTarget t) as [E|E].
   + subst t. rewrite map_get_sig in Read.
     assert (Prior : Int.repr 12=Int.repr (Z.of_nat p)).
     { exact (f_equal (fun x=>match x with Some (prio,_,_)=>prio | None=>Int.zero end) Read). }
     eapply V293_priority_repr_injective;[exact Bound|lia|symmetry;exact Prior].
   + rewrite map_get_sig' in Read by exact E. discriminate.
Qed.
Theorem StartPortMissing : StartProgram 902%Z=None.
Proof. reflexivity. Qed.
Theorem StartColdCall : exists Mf,
 cstepstar StartProgram (curs (scall 900%Z nil),(kenil,kstop))
 (StartGE,StartCaller,StartMem (StartCells false))
 (curs (sfexec 902%Z nil nil),(kenil,kseq sret (kcall 900%Z StartBody StartCaller kstop)))
 (StartGE,emp,Mf) /\ StartState Mf |= V293_rdy_raw_cells StartFinal Atrue.
Proof.
 eapply (V293_OSStart_call_to_port StartFrame StartProgram kstop StartGE StartCaller
  (StartMem (StartCells false)) (fun _=>false) (false,nil,nil) StartAbs (spec_done None)
  900%Z 108%Z 901%Z 105%Z 103%Z 109%Z 106%Z 107%Z 902%Z
  100%Z 101%Z 102%Z 104%Z 85%positive 82%positive 81%positive 86%positive
  83%positive 84%positive 1%positive 2%positive 3%positive 0 16
  (Vint32(Int.repr 7)) (Vint32(Int.repr 8)) Vnull Vnull StartTarget);
 try reflexivity;try lia.
 - exact StartNonempty.
 - apply StartInputReads.
 - exact (StartLiteralEntry false).
Qed.
Theorem StartWarmCall :
 cstepstar StartProgram (curs (scall 900%Z nil),(kenil,kstop))
 (StartGE,StartCaller,StartMem (StartCells true))
 (curs (sskip None),(kenil,kstop)) (StartGE,StartCaller,StartMem (StartCells true)).
Proof.
 eapply (V293_OSStart_already_running_call StartProgram kstop StartGE StartCaller
  (StartMem (StartCells true)) 900%Z 108%Z 901%Z 105%Z 103%Z 109%Z 106%Z 107%Z 902%Z 85%positive);
 [reflexivity|reflexivity| ].
 eapply V293_start_owned_load;[ | |exact (StartLiteralEntry true)];
 [unfold StartCells,V293_start_cells;do 4 right;left;reflexivity|reflexivity].
Qed.
Print Assumptions StartLiteralEntry.
Print Assumptions StartColdCall.
Print Assumptions StartWarmCall.

Theorem StartAllPostReads : forall M,
 StartState M |= V293_rdy_raw_cells StartFinal Atrue ->
 load Tint8 M (81%positive,0%Z)=Some(Vint32(Int.repr 12)) /\
 load Tint8 M (82%positive,0%Z)=Some(Vint32(Int.repr 12)) /\
 load (Tptr V293_tcb_type) M (83%positive,0%Z)=Some(Vptr StartTarget) /\
 load (Tptr V293_tcb_type) M (84%positive,0%Z)=Some(Vptr StartTarget) /\
 load Tint8 M (85%positive,0%Z)=Some(Vint32 Int.zero) /\
 load (Tptr V293_tcb_type) M (86%positive,48%Z)=Some(Vptr StartTarget) /\
 load Tint32 M (99%positive,0%Z)=Some(Vint32(Int.repr 123)).
Proof.
 intros M Owned. repeat split.
 all: eapply V293_start_owned_load;[ | |exact Owned].
 all: try reflexivity.
 all: unfold StartFinal,V293_start_final,V293_start_cells,StartFrame; simpl;tauto.
Qed.
Theorem StartColdCurrent : exists Mf,
 cstepstar StartProgram (curs (scall 900%Z nil),(kenil,kstop))
 (StartGE,StartCaller,StartMem (StartCells false))
 (curs (sfexec 902%Z nil nil),(kenil,kseq sret (kcall 900%Z StartBody StartCaller kstop)))
 (StartGE,emp,Mf) /\
 load (Tptr V293_tcb_type) Mf (84%positive,0%Z)=Some(Vptr StartTarget).
Proof.
 destruct StartColdCall as (Mf & Exec & Owned). exists Mf. split;[exact Exec| ].
 exact (proj1 (proj2 (proj2 (proj2 (StartAllPostReads Mf Owned))))).
Qed.
Theorem StartHighestCall : exists target message Mf,
 get StartTasks target=Some(Int.repr 12,rdy,message) /\
 V293_scheduler StartAbs target /\
 cstepstar StartProgram (curs (scall 900%Z nil),(kenil,kstop))
 (StartGE,StartCaller,StartMem (StartCells false))
 (curs (sfexec 902%Z nil nil),(kenil,kseq sret (kcall 900%Z StartBody StartCaller kstop)))
 (StartGE,emp,Mf) /\
 StartState Mf |= V293_rdy_raw_cells
  (V293_start_final 81%positive 82%positive 83%positive 84%positive 85%positive 86%positive 12 target StartFrame) Atrue.
Proof.
 eapply (V293_OSStart_highest_ready_call_to_port StartEntries StartTasks StartFrame
  StartProgram kstop StartGE StartCaller (StartMem (StartCells false))
  (fun _=>false) (false,nil,nil) StartAbs (spec_done None)
  900%Z 108%Z 901%Z 105%Z 103%Z 109%Z 106%Z 107%Z 902%Z
  100%Z 101%Z 102%Z 104%Z 85%positive 82%positive 81%positive 86%positive
  83%positive 84%positive 1%positive 2%positive 3%positive 0 16
  (Vint32(Int.repr 7)) (Vint32(Int.repr 8)) Vnull Vnull);
 try reflexivity;try lia.
 - exact StartNonempty.
 - exact StartBitmap.
 - exact StartTable.
 - apply StartInputReads.
 - exact (StartLiteralEntry false).
Qed.
Print Assumptions StartAllPostReads.
Print Assumptions StartColdCurrent.
Print Assumptions StartHighestCall.
