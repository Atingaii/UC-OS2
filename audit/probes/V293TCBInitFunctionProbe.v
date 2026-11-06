(* Independent literal entry: no TCB object or stack storage, absent callee locals. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitFunction.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFunction.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293NullBytes.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope Z_scope.
Definition CallFrame : list V293_record_cell :=
 [((601%positive,0),Tint32,Vint32 (Int.repr 77));
  ((602%positive,0),Tint8,Vint32 (Int.repr 88))].
Definition CallCells : list V293_record_cell :=
 ((301%positive,0),Tptr V293_tcb_type,Vnull)::CallFrame.
Fixpoint CallMemory (cells : list V293_record_cell) : mem :=
 match cells with []=>emp | ((b,off),tp,v)::tail=>
 merge (V293_encoded_memory b off true (encode_val tp v)) (CallMemory tail) end.
Definition CallEntry := CallMemory CallCells.
Definition CallGE : env := set emp 91%Z (301%positive,Tptr V293_tcb_type).
Definition CallCaller : env := set emp 108%Z (602%positive,Tint8).
Definition CallState M := V293_wstate CallGE CallCaller M.
Definition CallProgram f := if Z.eq_dec f 500%Z
 then Some (V293_TCBInit_function 501%Z 502%Z) else None.
Definition CallArgs (p : nat) : vallist :=
 [Vint32 (Int.repr 3);Vnull;Vint32 (Int.repr 128);Vint32 (Int.repr 65535);
 Vptr (401%positive,Int.zero);Vptr (401%positive,Int.repr 508);Vint32 (Int.repr (Z.of_nat p))].
Definition CallAddresses := V293_tcb_function_addresses 201%positive 202%positive
 203%positive 204%positive 205%positive 206%positive 207%positive 208%positive 209%positive.
Definition CallBlocks := V293_tcb_function_blocks 201%positive 202%positive
 203%positive 204%positive 205%positive 206%positive 207%positive 208%positive 209%positive.
Ltac CallOutside :=
 cbn [CallEntry CallCells CallFrame CallMemory];
 repeat first [rewrite V293_encoded_memory_outside by
 (first [left;congruence | right;cbn [length encode_val inj_bytes encode_int];lia])
 | rewrite map_merge_semp by reflexivity];reflexivity.
Ltac CallApart b :=
 apply map_join_merge;apply map_disjoint;intros [other off];
 destruct (Pos.eq_dec other b) as [B|B];
 [subst other;right;left;CallOutside | left;apply V293_encoded_memory_outside;left;exact B].
Lemma CallLiteralEntry : CallState CallEntry |= V293_rdy_raw_cells CallCells Atrue.
Proof.
 unfold CallState,CallEntry. cbn [CallCells CallFrame CallMemory V293_rdy_raw_cells].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 301%positive 0 true (encode_val (Tptr V293_tcb_type) Vnull));
 [CallApart 301%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 601%positive 0 true (encode_val Tint32 (Vint32 (Int.repr 77))));
 [CallApart 601%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 602%positive 0 true (encode_val Tint8 (Vint32 (Int.repr 88))));
 [CallApart 602%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
 exact I.
Qed.
Lemma CallAbsentLocals : forall b, In b CallBlocks -> fresh CallEntry b.
Proof.
 intros b Member a i E [v Read];subst a.
 assert (Absent : get CallEntry (b,i)=None).
 { unfold CallBlocks,V293_tcb_function_blocks in Member.
   repeat destruct Member as [Same|Member];try contradiction;subst b;CallOutside. }
 change (get CallEntry (b,i)=Some v) in Read. rewrite Absent in Read;discriminate.
Qed.
Lemma CallFreedByteCount : fold_right (fun bt n=>typelen (snd bt)+n)%nat 0%nat CallAddresses=29%nat.
Proof. reflexivity. Qed.
Lemma CallHooksAbsent : CallProgram 501%Z=None /\ CallProgram 502%Z=None.
Proof. split;reflexivity. Qed.
Theorem CallConcreteExecution : forall p ks enabled si ci,
 p=12%nat \/ p=11%nat ->
 exists Mf,
 V293_local_steps CallProgram
 (curs(sfexec 500%Z (CallArgs p) V293_TCBInit_argument_types),(kenil,ks))
 ((CallGE,CallCaller,CallEntry),(fun _=>false),(enabled,si,ci))
 (curs(sskip(Some(Vint32(Int.repr 66)))),(kenil,ks))
 ((CallGE,CallCaller,Mf),(fun _=>false),(enabled,si,ci)) /\
 CallState Mf |= V293_rdy_raw_cells CallCells Atrue /\
 load (Tptr V293_tcb_type) Mf (301%positive,0)=Some Vnull /\
 load Tint32 Mf (601%positive,0)=Some(Vint32(Int.repr 77)) /\
 load Tint8 Mf (602%positive,0)=Some(Vint32(Int.repr 88)) /\
 (forall b tp k, In (b,tp) CallAddresses -> (k<typelen tp)%nat -> get Mf (b,Z.of_nat k)=None).
Proof.
 intros p ks enabled si ci Case.
 destruct (V293_OS_TCBInit_empty_call_return CallProgram ks CallGE CallCaller CallEntry
 (fun _=>false) (false,nil,nil) (emp:osabst) (spec_done None) enabled si ci
 500%Z 501%Z 502%Z 301%positive 201%positive 202%positive 203%positive
 204%positive 205%positive 206%positive 207%positive 208%positive 209%positive
 (Vint32(Int.repr(Z.of_nat p))) (Vptr(401%positive,Int.repr 508)) (Vptr(401%positive,Int.zero))
 (Vint32(Int.repr 65535)) (Vint32(Int.repr 128)) Vnull (Vint32(Int.repr 3)) CallFrame)
 as (Ms & Mf & Exec & BeforeReturn & Owned & Freed).
 - reflexivity.
 - reflexivity.
 - unfold V293_tcb_function_blocks;repeat constructor;cbn;intuition congruence.
 - apply CallAbsentLocals.
 - destruct Case;subst p;vm_compute;repeat split;reflexivity.
 - intros a tp v Member. cbn [CallFrame In] in Member.
   repeat destruct Member as [E|Member];try contradiction;inversion E;subst;
   cbn [V293_tcb_function_blocks In fst];intuition congruence.
 - exact CallLiteralEntry.
 - change (CallState Mf |= V293_rdy_raw_cells CallCells Atrue) in Owned.
   unfold CallState,V293_wstate in Owned.
   V293_tcb_init_read Owned 0%nat HeadRead.
   V293_tcb_init_read Owned 1%nat FrameRead.
   V293_tcb_init_read Owned 2%nat ShadowRead.
   exists Mf. split;[exact Exec| ]. split;[exact Owned| ].
   split;[exact HeadRead| ]. split;[exact FrameRead| ]. split;[exact ShadowRead|exact Freed].
Qed.
Print Assumptions CallLiteralEntry.
Print Assumptions CallAbsentLocals.
Print Assumptions CallConcreteExecution.
