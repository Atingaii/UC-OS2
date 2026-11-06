(* Independent finite first-Hook-return anchor. This is not a claim that the
   absent first Hook has executed. No other audit probe is imported. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitEntry.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPriorityHook.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293NullBytes.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBList.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFunction.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitFunction.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitPrefix.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope Z_scope.
Definition PriorityOld (occupied : bool) : val :=
 if occupied then Vptr(399%positive,Int.repr 8) else Vundef.
Definition PriorityInput p occupied : list V293_record_cell :=
 [((201%positive,0),Tint8,V293_byteval p);
  ((202%positive,0),Tptr V293_tcb_type,Vptr(301%positive,Int.repr 8));
  ((310%positive,4*Z.of_nat p),Tptr V293_tcb_type,PriorityOld occupied)].
Definition PriorityFrame : list V293_record_cell :=
 [((310%positive,0),Tptr V293_tcb_type,Vnull);
  ((310%positive,4),Tptr V293_tcb_type,Vptr(398%positive,Int.repr 16));
  ((401%positive,0),Tint8,Vint32(Int.repr 2));
  ((402%positive,1),Tint8,Vint32(Int.repr 2));
  ((403%positive,0),Tint8,Vint32(Int.repr 7));
  ((601%positive,0),Tint32,Vint32(Int.repr 77));
  ((602%positive,0),Tint8,Vint32(Int.repr 88))].
Definition PriorityGE : env := set emp 92%Z (310%positive,Tarray (Tptr V293_tcb_type) 13).
Definition PriorityLE : env := set (set emp 101%Z (201%positive,Tint8)) 108%Z (202%positive,Tptr V293_tcb_type).
Definition PriorityCaller : env := set emp 108%Z (602%positive,Tint8).
Definition PriorityProgram f := if Z.eq_dec f 500%Z then Some(V293_TCBInit_function 501%Z 502%Z) else None.
Fixpoint PriorityMemory (cells : list V293_record_cell) : mem :=
 match cells with []=>emp | ((b,off),tp,v)::tail=>
 merge (V293_encoded_memory b off true (encode_val tp v)) (PriorityMemory tail) end.
Definition PriorityEntry p occupied := PriorityMemory (PriorityInput p occupied++PriorityFrame).
Definition PriorityStart := (curs(sskip None),
 (kenil,V293_tcb_first_hook_cont 500%Z 501%Z 502%Z PriorityCaller kstop)).
Definition PriorityStop := (curs(sfexec 502%Z (Vptr(301%positive,Int.repr 8)::nil) (Tptr V293_tcb_type::nil)),
 (kenil,V293_tcb_second_hook_cont 500%Z 501%Z 502%Z PriorityCaller kstop)).
Ltac PriorityOutside :=
 repeat first [rewrite V293_encoded_memory_outside by
 (first [left;congruence|right;cbn [length V293_byteval encode_val typelen list_repeat inj_pointer inj_bytes encode_int List.map];lia])
 |rewrite map_merge_semp by reflexivity];reflexivity.
Ltac PriorityApart b start count :=
 apply map_join_merge;apply map_disjoint;intros [other off];
 destruct (Pos.eq_dec other b) as [B|B];
 [subst other;destruct (Z_lt_dec off start) as [Low|Low];
 [left;apply V293_encoded_memory_outside;right;left;exact Low|
 destruct (Z_lt_dec off (start+count)) as [Inside|Outside];
 [right;left;PriorityOutside|left;apply V293_encoded_memory_outside;right;right;
 cbn [length V293_byteval encode_val typelen list_repeat inj_pointer inj_bytes encode_int List.map];lia]]|
 left;apply V293_encoded_memory_outside;left;exact B].
Lemma PriorityLiteralEntry : forall p occupied,
 p=12%nat \/ p=11%nat ->
 V293_wstate PriorityGE PriorityLE (PriorityEntry p occupied) |=
 V293_rdy_raw_cells (PriorityInput p occupied++PriorityFrame) Atrue.
Proof.
 intros p occupied Case. destruct Case;subst p;destruct occupied;
 unfold PriorityEntry;cbn [PriorityInput PriorityOld PriorityFrame app PriorityMemory V293_rdy_raw_cells].
 all: match goal with |- V293_wstate _ _ (merge (V293_encoded_memory ?b ?off true ?bytes) _) |= _ =>
 eapply V293_wstate_star with (m1:=V293_encoded_memory b off true bytes);
 [PriorityApart b off 1%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ] end.
 all: eapply V293_wstate_star with (m1:=V293_encoded_memory 202%positive 0%Z true (encode_val (Tptr V293_tcb_type) (Vptr(301%positive,Int.repr 8))));
 [PriorityApart 202%positive 0%Z 4%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
 all: match goal with |- V293_wstate _ _ (merge (V293_encoded_memory ?b ?off true ?bytes) _) |= _ =>
 eapply V293_wstate_star with (m1:=V293_encoded_memory b off true bytes);
 [PriorityApart b off 4%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ] end.
 all: eapply V293_wstate_star with (m1:=V293_encoded_memory 310%positive 0%Z true (encode_val (Tptr V293_tcb_type) (Vnull)));
 [PriorityApart 310%positive 0%Z 4%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
 all: eapply V293_wstate_star with (m1:=V293_encoded_memory 310%positive 4%Z true (encode_val (Tptr V293_tcb_type) (Vptr(398%positive,Int.repr 16))));
 [PriorityApart 310%positive 4%Z 4%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
 all: eapply V293_wstate_star with (m1:=V293_encoded_memory 401%positive 0%Z true (encode_val (Tint8) (Vint32(Int.repr 2))));
 [PriorityApart 401%positive 0%Z 1%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
 all: eapply V293_wstate_star with (m1:=V293_encoded_memory 402%positive 1%Z true (encode_val (Tint8) (Vint32(Int.repr 2))));
 [PriorityApart 402%positive 1%Z 1%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
 all: eapply V293_wstate_star with (m1:=V293_encoded_memory 403%positive 0%Z true (encode_val (Tint8) (Vint32(Int.repr 7))));
 [PriorityApart 403%positive 0%Z 1%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
 all: eapply V293_wstate_star with (m1:=V293_encoded_memory 601%positive 0%Z true (encode_val (Tint32) (Vint32(Int.repr 77))));
 [PriorityApart 601%positive 0%Z 4%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
 all: eapply V293_wstate_star with (m1:=V293_encoded_memory 602%positive 0%Z true (encode_val (Tint8) (Vint32(Int.repr 88))));
 [PriorityApart 602%positive 0%Z 1%Z|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
 all: exact I.
Qed.
Definition PriorityExpected p : list V293_record_cell :=
 [((201%positive,0),Tint8,V293_byteval p);
  ((202%positive,0),Tptr V293_tcb_type,Vptr(301%positive,Int.repr 8));
  ((310%positive,4*Z.of_nat p),Tptr V293_tcb_type,Vptr(301%positive,Int.repr 8))]++PriorityFrame.
Theorem PriorityConcreteExecution : forall p occupied enabled si ci,
 p=12%nat \/ p=11%nat ->
 exists Mf,
 V293_local_steps PriorityProgram PriorityStart
 ((PriorityGE,PriorityLE,PriorityEntry p occupied),(fun _=>false),(enabled,si,ci))
 PriorityStop ((PriorityGE,PriorityLE,Mf),(fun _=>false),(enabled,si,ci)) /\
 (forall a tp v, In (a,tp,v) (PriorityExpected p) -> load tp Mf a=Some v) /\
 (~exists C' state', loststep PriorityProgram PriorityStop
 ((PriorityGE,PriorityLE,Mf),(fun _=>false),(enabled,si,ci)) C' state').
Proof.
 intros p occupied enabled si ci Case.
 pose proof (PriorityLiteralEntry p occupied Case) as Entry.
 rewrite V293_raw_cells_append in Entry.
 destruct (V293_OS_TCBInit_priority_to_second_hook PriorityProgram 500%Z 501%Z 502%Z PriorityCaller kstop
 PriorityGE PriorityLE (PriorityEntry p occupied) (fun _=>false) (false,nil,nil) (emp:osabst) (spec_done None)
 (V293_rdy_raw_cells PriorityFrame Atrue) enabled si ci 201%positive 202%positive 310%positive 301%positive 8%Z p
 (PriorityOld occupied)) as (Mf&Exec&Owned&NoStep).
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - destruct Case;subst p;lia.
 - exact Entry.
 - exists Mf. split;[exact Exec| ]. split.
   + rewrite <-V293_raw_cells_append in Owned.
     assert (Range : (p<256)%nat) by (destruct Case;subst p;lia).
     pose proof (V293_byte_type p Range) as PriorityValid.
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
     intros a tp v Member. cbn [PriorityExpected PriorityFrame app In] in Member.
     repeat destruct Member as [E|Member];try contradiction;inversion E;subst;assumption.
   + apply NoStep. reflexivity.
Qed.
Print Assumptions PriorityLiteralEntry.
Print Assumptions PriorityConcreteExecution.
