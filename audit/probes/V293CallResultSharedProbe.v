(* Closed assignment contrast with a nonempty original shared-ready frame.
   The initial ready fixture is independent of complete hook reachability. *)
Require Import CertiOS.certiucos.v293.proofs.V293CallResultShared.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293SharedStateWitness.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.audit.probes.V293ReadyTaskInvariantProbe.
Require Import CertiOS.audit.probes.V293TaskRecordInvariantProbe.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.certiucos.v293.proofs.V293CanonicalInitReturn.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import Coq.Lists.List Lia.
Import ListNotations.

Definition CRSge:=V293_shared_fixture_ge.
Definition CRSle : env:=sig 209%Z(350%positive,Tint8).
Definition CRSO:=RIabstract OwnershipReady.
Definition CRSstate M:=V293_target_wstate CRSge CRSle M CRSO.
Definition CRSprogram : progunit:=fun _=>None.
Definition CRSold:=Vint32(Int.repr 66).

Lemma CRSliteral_core : CRSstate(RTfull OwnershipReady) |=
 V293_ready_core 80%positive 81%positive 82%positive ** Atrue.
Proof.
 pose proof(RTliteral_spatial OwnershipReady)as Held.
 unfold SWINVt in Held.
 eapply astar_mono in Held;[ |apply V293_ready_switch_open |intros st H;exact H].
 assert(Core:RTstate OwnershipReady(RTfull OwnershipReady) |=
  V293_ready_core 80%positive 81%positive 82%positive ** Atrue)by(clear -Held;sep auto).
 unfold CRSstate,CRSge,CRSO,RTstate,RIstate,V293_target_wstate in *.
 eapply rulesoundlib.good_inv_prop;[ |exact Core].
 split;[apply V293_ready_core_good |exact I].
Qed.

Lemma CRSfresh : fresh(RTfull OwnershipReady)350%positive.
Proof.
 intros b i Equal [v Lookup]. subst b.
 assert(Absent:get(RTfull OwnershipReady)(350%positive,i)=None).
 { unfold RTfull,RImemory,V293_shared_fixture_mem. rewrite !map_merge_semp by reflexivity.
   rewrite V293_encoded_memory_outside by(left;discriminate).
   unfold OwnershipMemory,RTmemory.
   rewrite !OwnershipCellsOutside by(intro H;vm_compute in H;intuition congruence).
   reflexivity. }
 change(get(RTfull OwnershipReady)(350%positive,i)=Some v)in Lookup. congruence.
Qed.

Lemma CRSreturn_entry : exists M ct tasks events now,
 load Tint8 M(350%positive,0%Z)=Some CRSold /\
 CRSstate M |= V293_shared_ready_records 80%positive 81%positive 82%positive ct tasks events now **
  V293_rdy_raw_cells (((350%positive,0%Z),Tint8,CRSold)::nil) Atrue.
Proof.
 pose proof(V293_tick_allocate_frame CRSge CRSle(RTfull OwnershipReady)
 (fun _=>false)(false,[],[])CRSO(spec_done None)350%positive Tint8
 (V293_ready_core 80%positive 81%positive 82%positive ** Atrue)CRSfresh CRSliteral_core)as Allocated.
 destruct(V293_tick_raw_slot_update(350%positive,0%Z)Tint8 Vundef CRSold
 (V293_ready_core 80%positive 81%positive 82%positive ** Atrue)CRSge CRSle
 (allocb(RTfull OwnershipReady)350%positive 0%Z(typelen Tint8))
 (fun _=>false)(false,[],[])CRSO(spec_done None)eq_refl Allocated)as(M&Store&Stored).
 assert(Read:load Tint8 M(350%positive,0%Z)=Some CRSold).
 { change(load Tint8(getmem(CRSstate M))(350%positive,0%Z)=Some CRSold).
   eapply V293_record_star_load_l;[apply V293_owned_record_cell_load |exact Stored]. }
 assert(Kept:CRSstate M |= V293_ready_core 80%positive 81%positive 82%positive **
  V293_rdy_raw_cells (((350%positive,0%Z),Tint8,CRSold)::nil) Atrue).
 { unfold V293_owned_record_cell in Stored. cbn[V293_rdy_raw_cells]. clear -Stored. sep auto. }
 apply sat_split in Kept. destruct Kept as(mc&mr&oc&orr&JM&JO&Core&Err).
 destruct Core as(ct&tasks&events&now&Shared).
 exists M. exists ct. exists tasks. exists events. exists now. split;[exact Read | ].
 apply sat_split'. exists mc. exists mr. exists oc. exists orr. split;[exact JM | ]. split;[exact JO | ]. split;assumption.
Qed.

Theorem CRSAssignmentContrast : exists M Mf ct tasks events now,
 load Tint8 M(350%positive,0%Z)=Some CRSold /\
 CRSstate M |= V293_shared_ready_records 80%positive 81%positive 82%positive ct tasks events now **
  V293_rdy_raw_cells (((350%positive,0%Z),Tint8,CRSold)::nil) Atrue /\
 cstepstar CRSprogram(curs(sskip(Some(Vint32 Int.zero))),(kenil,kassignr(evar 209%Z)Tint8 kstop))
  (CRSge,CRSle,M)(curs(sskip None),(kenil,kstop))(CRSge,CRSle,Mf) /\
 CRSstate Mf |= V293_shared_ready_records 80%positive 81%positive 82%positive ct tasks events now **
  V293_rdy_raw_cells (((350%positive,0%Z),Tint8,Vint32 Int.zero)::nil) Atrue /\
 load Tint8 Mf(350%positive,0%Z)=Some(Vint32 Int.zero) /\
 load Tint8 M(350%positive,0%Z)<>Some(Vint32 Int.zero).
Proof.
 destruct CRSreturn_entry as(M&ct&tasks&events&now&Read&Entry).
 destruct(V293_return_assign_shared 80%positive 81%positive 82%positive tasks ct events now [] []
 209%Z 350%positive CRSold CRSprogram kstop CRSge CRSle M(fun _=>false)(false,[],[])CRSO
 (spec_done None)eq_refl Entry)as(Mf&Exec&Final).
 exists M. exists Mf. exists ct. exists tasks. exists events. exists now. split;[exact Read | ]. split;[exact Entry | ].
 split;[exact Exec | ]. split;[exact Final | ]. split.
 - apply V293_raw_cells_frame_in in Final. V293_tcb_init_read Final 0%nat Zero. exact Zero.
 - rewrite Read. discriminate.
Qed.

(* The real runtime caller writes a reserved pointer, not the null-slot
   initialization profile. These two entry heaps cannot be identified. *)
Theorem CRSReservedSlotBoundary : forall table p reserve ge le M ir aux O op R,
 load(Tptr V293_tcb_type)M(table,(4*Z.of_nat p)%Z)=Some(Vptr(reserve,Int.zero)) ->
 ~(ge,le,M,ir,aux,O,op) |=
  V293_rdy_raw_cells (((table,(4*Z.of_nat p)%Z),Tptr V293_tcb_type,Vnull)::nil) R.
Proof.
 intros table p reserve ge le M ir aux O op R Reserved Null.
 V293_tcb_init_read Null 0%nat Empty.
 change(load(Tptr V293_tcb_type)M(table,(4*Z.of_nat p)%Z)=Some Vnull)in Empty.
 rewrite Empty in Reserved. discriminate.
Qed.
