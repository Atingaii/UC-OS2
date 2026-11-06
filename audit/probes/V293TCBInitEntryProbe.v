(* Independent finite entry; no old audit probe imports, no assumed callee result.
   Idle and Stat parameters are separate executions, not two published tasks. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInit.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293NullBytes.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope Z_scope.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitPrefix.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitFunction.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFunction.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitEntry.
Definition SuccessOld : list V293_record_cell :=
 [((301%positive,8%Z),(Tptr Tint32),(Vundef));
  ((301%positive,58%Z),(Tint8),(Vundef));
  ((301%positive,56%Z),(Tint8),(Vundef));
  ((301%positive,57%Z),(Tint8),(Vundef));
  ((301%positive,52%Z),(Tint32),(Vundef));
  ((301%positive,12%Z),(Tptr Tvoid),(Vundef));
  ((301%positive,20%Z),(Tint32),(Vundef));
  ((301%positive,16%Z),(Tptr Tint32),(Vundef));
  ((301%positive,24%Z),(Tint16),(Vundef));
  ((301%positive,26%Z),(Tint16),(Vundef));
  ((301%positive,63%Z),(Tint8),(Vundef));
  ((301%positive,60%Z),(Tint8),(Vundef));
  ((301%positive,59%Z),(Tint8),(Vundef));
  ((301%positive,62%Z),(Tint8),(Vundef));
  ((301%positive,61%Z),(Tint8),(Vundef));
  ((301%positive,36%Z),(Tcom_ptr 411%Z),(Vundef));
  ((301%positive,44%Z),(Tcom_ptr 412%Z),(Vundef));
  ((301%positive,40%Z),(Tptr Tvoid),(Vundef))].
Definition SuccessFrame : list V293_record_cell :=
 [((301%positive,32%Z),(Tcom_ptr 410%Z),(Vptr (502%positive,Int.zero)));
  ((301%positive,48%Z),(Tint16),(Vint32 (Int.repr 4660)));
  ((301%positive,50%Z),(Tint16),(Vint32 (Int.repr 22136)));
  ((601%positive,0%Z),(Tint32),(Vint32 (Int.repr 77)));
  ((602%positive,0%Z),Tint8,Vint32 (Int.repr 88))].
Definition SuccessNext (tail : bool) := if tail then Vptr (501%positive,Int.repr 56) else Vnull.
Definition SuccessLinks tail : list V293_record_cell :=
 [((209%positive,0),Tptr V293_tcb_type,Vptr(301%positive,Int.repr 8));
  ((301%positive,28),Tcom_ptr 410%Z,SuccessNext tail)].
Definition SuccessGE : env := set emp 91%Z (209%positive,Tptr V293_tcb_type).
Definition SuccessCaller : env := set emp 108%Z (602%positive,Tint8).
Definition SuccessProgram f := if Z.eq_dec f 500%Z
 then Some(V293_TCBInit_function 501%Z 502%Z) else None.
Fixpoint SuccessMemory (cells : list V293_record_cell) : mem :=
 match cells with []=>emp | ((b,off),tp,v)::tail=>
 merge (V293_encoded_memory b off true (encode_val tp v)) (SuccessMemory tail) end.
Definition SuccessEntry tail := SuccessMemory (SuccessOld++SuccessLinks tail++SuccessFrame).
Definition SuccessState M := V293_wstate SuccessGE SuccessCaller M.
Definition SuccessArgs p : vallist :=
 [Vint32(Int.repr 3);Vnull;Vint32(Int.repr 128);Vint32(Int.repr 65535);
  Vptr(401%positive,Int.zero);Vptr(401%positive,Int.repr 508);V293_byteval p].
Definition SuccessStop :=
 (curs(sfexec 501%Z (Vptr(301%positive,Int.repr 8)::nil) (Tptr V293_tcb_type::nil)),
 (kenil,V293_tcb_first_hook_cont 500%Z 501%Z 502%Z SuccessCaller kstop)).
Ltac SuccessOutside :=
  repeat first [rewrite V293_encoded_memory_outside by
    (first [left;congruence | right;cbn [length encode_val typelen list_repeat inj_pointer inj_bytes encode_int List.map];lia])
    | rewrite map_merge_semp by reflexivity];reflexivity.
Ltac SuccessApart b start count :=
  apply map_join_merge;apply map_disjoint;intros [other off];
  destruct (Pos.eq_dec other b) as [B|B];
  [subst other;destruct (Z_lt_dec off start) as [Low|Low];
    [left;apply V293_encoded_memory_outside;right;left;exact Low |
     destruct (Z_lt_dec off (start+count)) as [Inside|Outside];
     [right;left;SuccessOutside | left;apply V293_encoded_memory_outside;right;right;
       cbn [length encode_val typelen list_repeat inj_pointer inj_bytes encode_int List.map];lia]] |
   left;apply V293_encoded_memory_outside;left;exact B].
Lemma SuccessLiteralEntry : forall tail,
 SuccessState (SuccessEntry tail) |= V293_rdy_raw_cells
 (SuccessOld++SuccessLinks tail++SuccessFrame) Atrue.
Proof.
 intros tail. destruct tail; unfold SuccessState,SuccessEntry;
 cbn [SuccessOld SuccessLinks SuccessNext SuccessFrame app SuccessMemory V293_rdy_raw_cells].
 all: eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 8%Z true (encode_val (Tptr Tint32) (Vundef)));
 [SuccessApart 301%positive 8%Z 4%Z | split;[apply V293_encoded_memory_mapsto|reflexivity] | ].
 all: eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 58%Z true (encode_val (Tint8) (Vundef)));
 [SuccessApart 301%positive 58%Z 1%Z | split;[apply V293_encoded_memory_mapsto|reflexivity] | ].
 all: eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 56%Z true (encode_val (Tint8) (Vundef)));
 [SuccessApart 301%positive 56%Z 1%Z | split;[apply V293_encoded_memory_mapsto|reflexivity] | ].
 all: eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 57%Z true (encode_val (Tint8) (Vundef)));
 [SuccessApart 301%positive 57%Z 1%Z | split;[apply V293_encoded_memory_mapsto|reflexivity] | ].
 all: eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 52%Z true (encode_val (Tint32) (Vundef)));
 [SuccessApart 301%positive 52%Z 4%Z | split;[apply V293_encoded_memory_mapsto|reflexivity] | ].
 all: eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 12%Z true (encode_val (Tptr Tvoid) (Vundef)));
 [SuccessApart 301%positive 12%Z 4%Z | split;[apply V293_encoded_memory_mapsto|reflexivity] | ].
 all: eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 20%Z true (encode_val (Tint32) (Vundef)));
 [SuccessApart 301%positive 20%Z 4%Z | split;[apply V293_encoded_memory_mapsto|reflexivity] | ].
 all: eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 16%Z true (encode_val (Tptr Tint32) (Vundef)));
 [SuccessApart 301%positive 16%Z 4%Z | split;[apply V293_encoded_memory_mapsto|reflexivity] | ].
 all: eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 24%Z true (encode_val (Tint16) (Vundef)));
 [SuccessApart 301%positive 24%Z 2%Z | split;[apply V293_encoded_memory_mapsto|reflexivity] | ].
 all: eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 26%Z true (encode_val (Tint16) (Vundef)));
 [SuccessApart 301%positive 26%Z 2%Z | split;[apply V293_encoded_memory_mapsto|reflexivity] | ].
 all: eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 63%Z true (encode_val (Tint8) (Vundef)));
 [SuccessApart 301%positive 63%Z 1%Z | split;[apply V293_encoded_memory_mapsto|reflexivity] | ].
 all: eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 60%Z true (encode_val (Tint8) (Vundef)));
 [SuccessApart 301%positive 60%Z 1%Z | split;[apply V293_encoded_memory_mapsto|reflexivity] | ].
 all: eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 59%Z true (encode_val (Tint8) (Vundef)));
 [SuccessApart 301%positive 59%Z 1%Z | split;[apply V293_encoded_memory_mapsto|reflexivity] | ].
 all: eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 62%Z true (encode_val (Tint8) (Vundef)));
 [SuccessApart 301%positive 62%Z 1%Z | split;[apply V293_encoded_memory_mapsto|reflexivity] | ].
 all: eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 61%Z true (encode_val (Tint8) (Vundef)));
 [SuccessApart 301%positive 61%Z 1%Z | split;[apply V293_encoded_memory_mapsto|reflexivity] | ].
 all: eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 36%Z true (encode_val (Tcom_ptr 411%Z) (Vundef)));
 [SuccessApart 301%positive 36%Z 4%Z | split;[apply V293_encoded_memory_mapsto|reflexivity] | ].
 all: eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 44%Z true (encode_val (Tcom_ptr 412%Z) (Vundef)));
 [SuccessApart 301%positive 44%Z 4%Z | split;[apply V293_encoded_memory_mapsto|reflexivity] | ].
 all: eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 40%Z true (encode_val (Tptr Tvoid) (Vundef)));
 [SuccessApart 301%positive 40%Z 4%Z | split;[apply V293_encoded_memory_mapsto|reflexivity] | ].
 all: eapply V293_wstate_star with (m1:=V293_encoded_memory 209%positive 0%Z true (encode_val (Tptr V293_tcb_type) (Vptr(301%positive,Int.repr 8))));
 [SuccessApart 209%positive 0%Z 4%Z | split;[apply V293_encoded_memory_mapsto|reflexivity] | ].
 all: eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 28%Z true (encode_val (Tcom_ptr 410%Z) (_)));
 [SuccessApart 301%positive 28%Z 4%Z | split;[apply V293_encoded_memory_mapsto|reflexivity] | ].
 all: eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 32%Z true (encode_val (Tcom_ptr 410%Z) (Vptr(502%positive,Int.zero))));
 [SuccessApart 301%positive 32%Z 4%Z | split;[apply V293_encoded_memory_mapsto|reflexivity] | ].
 all: eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 48%Z true (encode_val (Tint16) (Vint32(Int.repr 4660))));
 [SuccessApart 301%positive 48%Z 2%Z | split;[apply V293_encoded_memory_mapsto|reflexivity] | ].
 all: eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 50%Z true (encode_val (Tint16) (Vint32(Int.repr 22136))));
 [SuccessApart 301%positive 50%Z 2%Z | split;[apply V293_encoded_memory_mapsto|reflexivity] | ].
 all: eapply V293_wstate_star with (m1:=V293_encoded_memory 601%positive 0%Z true (encode_val (Tint32) (Vint32(Int.repr 77))));
 [SuccessApart 601%positive 0%Z 4%Z | split;[apply V293_encoded_memory_mapsto|reflexivity] | ].
 all: eapply V293_wstate_star with (m1:=V293_encoded_memory 602%positive 0%Z true (encode_val (Tint8) (Vint32(Int.repr 88))));
 [SuccessApart 602%positive 0%Z 1%Z | split;[apply V293_encoded_memory_mapsto|reflexivity] | ].
 all: exact I.
Qed.
Definition SuccessExpected p tail : list V293_record_cell :=
 [((301%positive,8%Z),(Tptr Tint32),(Vptr(401%positive,Int.repr 508)));
  ((301%positive,58%Z),(Tint8),(V293_byteval p));
  ((301%positive,56%Z),(Tint8),(Vint32 Int.zero));
  ((301%positive,57%Z),(Tint8),(Vint32 Int.zero));
  ((301%positive,52%Z),(Tint32),(Vint32 Int.zero));
  ((301%positive,12%Z),(Tptr Tvoid),(Vnull));
  ((301%positive,20%Z),(Tint32),(Vint32(Int.repr 128)));
  ((301%positive,16%Z),(Tptr Tint32),(Vptr(401%positive,Int.zero)));
  ((301%positive,24%Z),(Tint16),(Vint32(Int.repr 3)));
  ((301%positive,26%Z),(Tint16),(Vint32(Int.repr 65535)));
  ((301%positive,63%Z),(Tint8),(Vint32 Int.zero));
  ((301%positive,60%Z),(Tint8),(Vint32 Int.one));
  ((301%positive,59%Z),(Tint8),(Vint32(Int.repr (if Nat.eqb p 12 then 4 else 3))));
  ((301%positive,62%Z),(Tint8),(Vint32(Int.repr 2)));
  ((301%positive,61%Z),(Tint8),(Vint32(Int.repr (if Nat.eqb p 12 then 16 else 8))));
  ((301%positive,36%Z),(Tcom_ptr 411%Z),(Vnull));
  ((301%positive,44%Z),(Tcom_ptr 412%Z),(Vnull));
  ((301%positive,40%Z),(Tptr Tvoid),(Vnull));
  ((209%positive,0),Tptr V293_tcb_type,SuccessNext tail);
  ((301%positive,28),Tcom_ptr 410%Z,SuccessNext tail)]++SuccessFrame.
Theorem SuccessConcreteExecution : forall p tail enabled si ci,
 p=12%nat \/ p=11%nat ->
 exists le Mf,
 V293_local_steps SuccessProgram
 (curs(sfexec 500%Z (SuccessArgs p) V293_TCBInit_argument_types),(kenil,kstop))
 ((SuccessGE,SuccessCaller,SuccessEntry tail),(fun _=>false),(enabled,si,ci))
 SuccessStop ((SuccessGE,le,Mf),(fun _=>false),(enabled,si,ci)) /\
 (forall a tp v, In (a,tp,v) (SuccessExpected p tail) -> load tp Mf a=Some v) /\
 (~ exists C' state', loststep SuccessProgram SuccessStop
 ((SuccessGE,le,Mf),(fun _=>false),(enabled,si,ci)) C' state').
Proof.
 intros p tail enabled si ci Case.
 destruct (V293_OS_TCBInit_call_to_first_hook SuccessProgram kstop SuccessGE SuccessCaller (SuccessEntry tail)
 (fun _=>false) (false,nil,nil) (emp:osabst) (spec_done None) enabled si ci
 500%Z 501%Z 502%Z 209%positive 301%positive 8%Z p
 (Vptr(401%positive,Int.repr 508)) (Vptr(401%positive,Int.zero))
 (Vint32(Int.repr 65535)) (Vint32(Int.repr 128)) Vnull (Vint32(Int.repr 3))
 (SuccessNext tail) (fun _=>Vundef) SuccessFrame)
 as (b1&b2&b3&b4&b5&b6&b7&b8&b9&Mf&ND&Exec&Owned&NoStep).
 - reflexivity.
 - reflexivity.
 - destruct Case;subst p;lia.
 - lia.
 - change (8+55<=4294967295);lia.
 - vm_compute;repeat split;reflexivity.
 - destruct tail;reflexivity.
 - exact (SuccessLiteralEntry tail).
 - exists (V293_tcb_function_env b1 b2 b3 b4 b5 b6 b7 b8 b9). exists Mf.
   split;[exact Exec| ]. split.
   + assert (Range : (p<13)%nat) by (destruct Case;subst p;lia).
     destruct (V293_tcb_init_byte_valid p Range) as (PriorityValid&YValid&XValid&BYValid&BXValid).
     assert (NextValid : rule_type_val_match (Tptr V293_tcb_type) (SuccessNext tail)=true) by (destruct tail;reflexivity).
     assert (LinkValid : rule_type_val_match (Tcom_ptr 410%Z) (SuccessNext tail)=true) by (destruct tail;reflexivity).
     V293_tcb_init_read Owned 0%nat Read0.
     V293_tcb_init_read Owned 1%nat Read1.
     V293_tcb_init_read Owned 2%nat Read2.
     V293_tcb_init_read Owned 3%nat Read3.
     V293_tcb_init_read Owned 4%nat Read4.
     V293_tcb_init_read Owned 5%nat Read5.
     V293_tcb_init_read Owned 6%nat Read6.
     V293_tcb_init_read Owned 7%nat Read7.
     V293_tcb_init_read Owned 8%nat Read8.
     V293_tcb_init_read Owned 9%nat Read9.
     V293_tcb_init_read Owned 10%nat Read10.
     V293_tcb_init_read Owned 11%nat Read11.
     V293_tcb_init_read Owned 12%nat Read12.
     V293_tcb_init_read Owned 13%nat Read13.
     V293_tcb_init_read Owned 14%nat Read14.
     V293_tcb_init_read Owned 15%nat Read15.
     V293_tcb_init_read Owned 16%nat Read16.
     V293_tcb_init_read Owned 17%nat Read17.
     V293_tcb_init_read Owned 26%nat Read26.
     V293_tcb_init_read Owned 27%nat Read27.
     V293_tcb_init_read Owned 29%nat Read29.
     V293_tcb_init_read Owned 30%nat Read30.
     V293_tcb_init_read Owned 31%nat Read31.
     V293_tcb_init_read Owned 32%nat Read32.
     V293_tcb_init_read Owned 33%nat Read33.
     intros a tp v Member. destruct Case;subst p;
     cbn [SuccessExpected SuccessFrame app In] in Member;
     repeat destruct Member as [E|Member];try contradiction;inversion E;subst;
     assumption.
   + apply NoStep. reflexivity.
Qed.
Print Assumptions SuccessLiteralEntry.
Print Assumptions SuccessConcreteExecution.
