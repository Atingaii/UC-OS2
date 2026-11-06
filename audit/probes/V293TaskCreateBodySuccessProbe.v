(* Same finite CallSpec and frozen byte fixtures; only global 98 / block710 added. *)
Require Import CertiOS.audit.probes.V293TaskCreateTCBCallProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPublish.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateBodyFailure.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtSuffix.
Require Import CertiOS.audit.probes.V293TCBSuccessInternalProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateSuccessHoare.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.proofs.V293TCBSnapshotInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TCBSuccessInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEmptyInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitFunction.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.audit.probes.V293TCBSuccessInternalProbe.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import Coq.Lists.List.ListNotations.
Local Open Scope nat_scope.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateTCBCall.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtCalls.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBClear.
Require Import CertiOS.certiucos.v293.proofs.V293StartRecord.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293TCBHookCall.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293TCBLinkedHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitPrefix.
Import Coq.Lists.List.ListNotations.
Local Open Scope nat_scope.



Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateStackSuccess.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateStackCall.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateStackEntry.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateBodySuccess.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateExtPrefix.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtFunction.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFieldsHoare.

(* Reuse frozen TCB bytes, not an independent source translation. New caller
   bindings are distinct from callee locals. Reserved object needs its address,
   not ownership of an unrelated byte. NULL stack remains a typed witness only. *)
Require Import CertiOS.certiucos.v293.proofs.V293TCBPriorityHoare.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Definition SBReserved := Vptr(721%positive,Int.zero).
Definition SBArg := Vptr(801%positive,Int.zero).
Definition SBInput := Vptr(802%positive,Int.repr 16).
Definition SBArgs := V293_create_stack_values 17%Z SBArg SBInput(Vint32 Int.zero).
Definition SBCells present := V293_tcb_success_pre_owned 211%positive SBReserved
 210%positive 301%positive 128%Z(fun _=>Vundef)SuccessNext
 212%positive 213%positive 214%positive 215%positive 301%positive 256%Z present 11 Vundef 1 129 254 Vundef.
Definition SBRestCells present := tl(SBCells present).
Definition SBBefore present cs := @mkfunasrt
 (V293_tcb_success_external 211%positive 210%positive 212%positive 213%positive 214%positive 215%positive
 (SBCells present)SuccessR(spec_done None)(fun _=>false)[]cs)
 (V293_tcb_success_external_good 211%positive 210%positive 212%positive 213%positive 214%positive 215%positive
 (SBCells present)SuccessR(spec_done None)(fun _=>false)[]cs SuccessRFun).
Definition SBReadyFpre present cs := V293_tcb_success_fpre 211%positive SBReserved
 210%positive 301%positive 128%Z(fun _=>Vundef)11 Vnull Vnull(Vint32 Int.zero)
 (Vint32(Int.repr 128))Vnull(Vint32 Int.zero)SuccessNext 212%positive 213%positive 214%positive
 215%positive 301%positive 256%Z present Vundef 1 129 254 Vundef SuccessR
 (spec_done None)(fun _=>false)[]cs SuccessRFun.
Definition SBFpre present cs := V293_tcb_snapshot_fpre SuccessHead
 (V293_tcb_empty_fpre 210%positive SuccessR(spec_done None)(fun _=>false)[]cs SuccessRFun)
 (SBReadyFpre present cs).
Definition SBFpost := CallFpost.
Definition SBHookPre present cs := V293_create_stack_resource_fpre(SBBefore present cs)SBArgs.
Definition SBHookPost present cs := V293_create_stack_resource_fpost
 (SBFpre present cs SuccessArguments[logic_val SuccessHead]SuccessTid)SBArgs Vnull.
Definition SBSpec present cs : funspec := fun f=>
 if Z.eq_dec f 902%Z then Some(SBHookPre present cs,SBHookPost present cs,(Tptr Tint32,rev V293_stack_argument_types))
 else if Z.eq_dec f 900%Z then Some(SBFpre present cs,SBFpost present cs,(Tint8,rev V293_TCBInit_argument_types))
 else if Z.eq_dec f 501%Z then Some(SuccessFpre SBReserved present cs,SuccessFpost SBReserved present cs,(Tvoid,[Tptr V293_tcb_type]))
 else if Z.eq_dec f 502%Z then Some(SuccessFpre SuccessHead present cs,SuccessFpost SuccessHead present cs,(Tvoid,[Tptr V293_tcb_type]))
 else None.
Ltac SBLookup := unfold SBSpec;repeat destruct(Z.eq_dec _ _);try discriminate;try contradiction;reflexivity.
Lemma SBHookLookup : forall present cs,
 SBSpec present cs 902%Z=Some(SBHookPre present cs,SBHookPost present cs,(Tptr Tint32,rev V293_stack_argument_types)).
Proof. intros;SBLookup. Qed.
Lemma SBTCBLookup : forall present cs,
 SBSpec present cs 900%Z=Some(SBFpre present cs,SBFpost present cs,(Tint8,rev V293_TCBInit_argument_types)).
Proof. intros;SBLookup. Qed.
Definition SBGE : env := set(set(set SuccessGE 98%Z(710%positive,Tint8))
 97%Z(720%positive,Tint8))99%Z(721%positive,Tint8).
Definition SBLE : env := set(set(set(set CallLE 201%Z(711%positive,Tint32))
 202%Z(712%positive,Tptr Tvoid))203%Z(713%positive,Tptr Tint32))109%Z(714%positive,Tint32).
Definition SBState M cs : RstateOP :=
 (SBGE,SBLE,M,(fun _=>false),(false,[],cs),(emp:osabst),spec_done None).
Definition SBRestMemory present := merge(SuccessMemory(SBRestCells present))(merge SuccessCurrent SuccessSentinel).
Definition SBRunning := V293_encoded_memory 710%positive 0 false(encode_val Tint8(Vint32 Int.zero)).
Definition SBExtra cpu := merge(CallByte 711%positive Tint32(V293_task_selector 17%Z))
 (merge(CallByte 712%positive(Tptr Tvoid)SBArg)(merge(CallByte 713%positive(Tptr Tint32)SBInput)
 (merge SBRunning(merge(CallByte 720%positive Tint8(V293_byteval 0))(CallByte 714%positive Tint32 cpu))))).
Definition SBSlot slot := V293_encoded_memory 211%positive 44 true(encode_val(Tptr V293_tcb_type)slot).
Definition SBMemory present cpu := merge(SBSlot Vnull)
 (merge(SBRestMemory present)(merge(CallLocals Vundef Vnull Vundef)(SBExtra cpu))).
Definition SBFrame present := V293_create_success_body_frame(SBRestCells present)(SuccessGlobals ** SuccessR)
 Vundef 17%Z SBArg SBInput(Vint32 Int.zero)Vundef Vnull(Vint32 Int.zero)(Vint32(Int.repr 128))Vnull
 98%Z 710%positive CallFrame.
Definition SBEntry present cpu cs := V293_create_prefix_state 701%positive 720%positive 714%positive
 211%positive 97%Z 99%Z 721%positive 11 cpu Vnull(SBFrame present)(spec_done None)(fun _=>false)[]cs.
Lemma SBStar : forall m1 m2 m cs A B,
 join m1 m2 m -> SBState m1 cs |= A -> SBState m2 cs |= B -> SBState m cs |= A ** B.
Proof.
 intros. apply sat_split'. exists m1. exists m2. exists(emp:osabst). exists(emp:osabst).
 split;[exact H| ]. split;[apply map_join_emp| ]. split;assumption.
Qed.
Lemma SBLVar : forall b x tp v cs,
 get SBLE x=Some(b,tp) -> SBState(CallByte b tp v)cs |= LV x @ tp |->v.
Proof.
 intros b x tp v cs Env. exists b.
 eapply SBStar with(m1:=emp)(m2:=CallByte b tp v).
 - apply map_join_comm;apply map_join_emp.
 - exists b. split;[exact Env| ]. repeat split;reflexivity.
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Ltac SBLocalApart b :=
 apply map_join_merge;apply map_disjoint;intros[other off];
 destruct(Pos.eq_dec other b);[subst other;right;left|left];
 unfold CallByte;
 repeat first[rewrite map_merge_semp by reflexivity|
 rewrite V293_encoded_memory_outside by(left;congruence)];reflexivity.
Ltac SBLocalTactic :=
 lazymatch goal with
 | |- SBState(merge(CallByte ?b ?tp ?v)?tail)?cs |= LV ?x @ ?tp |-> ?v ** _ =>
   eapply SBStar with(m1:=CallByte b tp v)(m2:=tail);
   [SBLocalApart b|apply SBLVar;vm_compute;reflexivity|SBLocalTactic]
 | |- SBState(CallByte 709%positive Tint8(Vint32(Int.repr 77)))?cs |= _ =>
   split;[apply V293_encoded_memory_mapsto|reflexivity]
 end.

Lemma SBCurrentSpatial : forall cs, SBState SuccessCurrent cs |= CurTid SuccessTid.
Proof.
 intro cs. exists Tvoid. exists 402%positive.
 eapply SBStar with (m1:=emp) (m2:=SuccessCurrent).
 - apply map_join_comm;apply map_join_emp.
 - exists 402%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Lemma SBLInvSpatial : forall cs, SBState emp cs |= LINV V293_witness_li SuccessTid [].
Proof.
 intro cs. unfold LINV. apply astar_comm. apply astar_l_apure_intro.
 - split;reflexivity.
 - apply V293_witness_li_good.
Qed.
Ltac SBFrameApart b :=
 apply map_join_merge;apply map_disjoint;intros [other offset];
 destruct(Pos.eq_dec other b);[subst other;right;left|left];
 unfold SuccessCurrent,SuccessSentinel,SuccessBytes;
 repeat first [rewrite map_merge_semp by reflexivity |
 rewrite V293_encoded_memory_outside by (left;congruence)];reflexivity.
Lemma SBRSpatial : forall cs,
 SBState (merge SuccessCurrent SuccessSentinel) cs |= SuccessR.
Proof.
 intro cs. unfold SuccessR.
 eapply SBStar with (m1:=SuccessCurrent) (m2:=SuccessSentinel).
 - SBFrameApart 402%positive.
 - apply SBCurrentSpatial.
 - eapply SBStar with (m1:=emp) (m2:=SuccessSentinel).
   + apply map_join_comm;apply map_join_emp.
   + apply SBLInvSpatial.
   + split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Lemma SBLocalsSpatial : forall cs,
 SBState(CallLocals Vundef Vnull Vundef)cs |= LV 209%Z @ Tint8 |->Vundef **
 (Amapsto(701%positive,0%Z)Tint8 true(V293_byteval 11) **
 LV 108%Z @ (Tptr Tint32) |->Vundef ** LV 205%Z @ (Tptr Tint32) |->Vnull **
 LV 206%Z @ Tint16 |->Vint32 Int.zero ** LV 207%Z @ Tint32 |->Vint32(Int.repr 128) **
 LV 208%Z @ (Tptr Tvoid) |->Vnull ** LV 204%Z @ Tint16 |->Vint32 Int.zero ** CallFrame).
Proof.
 intro cs. unfold CallLocals,CallFrame.
 eapply SBStar with(m1:=CallByte 708%positive Tint8 Vundef).
 - SBLocalApart 708%positive.
 - apply SBLVar;vm_compute;reflexivity.
 - eapply SBStar with(m1:=CallByte 701%positive Tint8(V293_byteval 11)).
   + SBLocalApart 701%positive.
   + split;[apply V293_encoded_memory_mapsto|reflexivity].
   + SBLocalTactic.
Qed.
Ltac SBRawTactic :=
 lazymatch goal with
 | |- SBState(merge(V293_encoded_memory ?b ?off true(encode_val ?tp ?v))?tail)?cs |= _ =>
   let bytes:=eval cbv in(Z.of_nat(typelen tp))in
   eapply SBStar with(m1:=V293_encoded_memory b off true(encode_val tp v));
   [SuccessApart b off bytes|split;[apply V293_encoded_memory_mapsto|reflexivity]|SBRawTactic]
 | |- SBState emp _ |= Aemp => split;reflexivity
 end.
Ltac SBUnfoldRest := unfold SBRestCells,SBCells,V293_tcb_success_pre_owned,
 V293_tcb_init_old_fields,V293_tcb_prefix_links,V293_link_extra;
 cbn[app tl SuccessMemory V293_rdy_raw_cells].
Lemma SBRawRest : forall present cs,
 SBState(SuccessMemory(SBRestCells present))cs |= V293_rdy_raw_cells(SBRestCells present)Aemp.
Proof. intros;destruct present;SBUnfoldRest;SBRawTactic. Qed.
Lemma SBGlobals : forall cs,SBState emp cs |= SuccessGlobals.
Proof.
 intro cs. unfold SuccessGlobals,V293_tcb_success_global_bindings.
 repeat(eapply SBStar with(m1:=emp)(m2:=emp);
 [apply map_join_emp|eexists;split;[vm_compute;reflexivity|repeat split;reflexivity]| ]).
 split;reflexivity.
Qed.
Lemma SBRestSpatial : forall present cs,
 SBState(SBRestMemory present)cs |= V293_rdy_raw_cells(SBRestCells present)(SuccessGlobals ** SuccessR).
Proof.
 intros. apply V293_raw_cells_join. unfold SBRestMemory.
 eapply SBStar with(m1:=SuccessMemory(SBRestCells present)).
 - apply map_join_merge;apply map_disjoint;intros[b off].
   destruct(Pos.eq_dec b 402%positive);[subst b;left| ].
   + destruct present;SBUnfoldRest;SuccessOutside.
   + destruct(Pos.eq_dec b 601%positive);[subst b;left|right;left].
     * destruct present;SBUnfoldRest;SuccessOutside.
     * unfold SuccessCurrent,SuccessSentinel,SuccessBytes;SuccessOutside.
 - apply SBRawRest.
 - eapply SBStar with(m1:=emp).
   + apply map_join_comm;apply map_join_emp.
   + apply SBGlobals.
   + apply SBRSpatial.
Qed.
Lemma SBRunningSpatial : forall cs,SBState SBRunning cs |= V293_create_idle_running 98%Z 710%positive.
Proof.
 intro cs. unfold V293_create_idle_running,V293_create_global_binding.
 eapply SBStar with(m1:=emp).
 - apply map_join_comm;apply map_join_emp.
 - split.
   + exists 710%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
   + split;[intros[v H];vm_compute in H;discriminate H|repeat split;reflexivity].
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Definition SBExtraAsrt cpu := V293_create_stack_kept 17%Z SBArg SBInput
 (V293_create_idle_running 98%Z 710%positive **
 Amapsto(720%positive,0%Z)Tint8 true(V293_byteval 0) ** Amapsto(714%positive,0%Z)Tint32 true cpu).
Lemma SBExtraSpatial : forall cpu cs,SBState(SBExtra cpu)cs |= SBExtraAsrt cpu.
Proof.
 intros. unfold SBExtra,SBExtraAsrt,V293_create_stack_kept.
 eapply SBStar with(m1:=CallByte 711%positive Tint32(V293_task_selector 17%Z)).
 - unfold SBRunning. SBLocalApart 711%positive.
 - apply SBLVar;vm_compute;reflexivity.
 - eapply SBStar with(m1:=CallByte 712%positive(Tptr Tvoid)SBArg).
   + unfold SBRunning. SBLocalApart 712%positive.
   + apply SBLVar;vm_compute;reflexivity.
   + eapply SBStar with(m1:=CallByte 713%positive(Tptr Tint32)SBInput).
     * unfold SBRunning. SBLocalApart 713%positive.
     * apply SBLVar;vm_compute;reflexivity.
     * eapply SBStar with(m1:=SBRunning).
       -- unfold SBRunning. SBLocalApart 710%positive.
       -- apply SBRunningSpatial.
       -- eapply SBStar with(m1:=CallByte 720%positive Tint8(V293_byteval 0)).
          ++ SBLocalApart 720%positive.
          ++ split;[apply V293_encoded_memory_mapsto|reflexivity].
          ++ split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Ltac SBUnfoldMemory := unfold SBRestMemory,CallLocals,SBExtra,SBRunning,SBSlot,CallByte,
 SuccessCurrent,SuccessSentinel,SuccessBytes;SBUnfoldRest.
Lemma SBCallerExtraApart : forall (present:bool) cpu,
 join(CallLocals Vundef Vnull Vundef)(SBExtra cpu)(merge(CallLocals Vundef Vnull Vundef)(SBExtra cpu)).
Proof.
 intros. apply map_join_merge;apply map_disjoint;intros[b off].
 destruct(Pos.eq_dec b 701%positive);[subst b;right;left| ].
 { destruct present;SBUnfoldMemory;SuccessOutside. }
 destruct(Pos.eq_dec b 702%positive);[subst b;right;left| ].
 { destruct present;SBUnfoldMemory;SuccessOutside. }
 destruct(Pos.eq_dec b 703%positive);[subst b;right;left| ].
 { destruct present;SBUnfoldMemory;SuccessOutside. }
 destruct(Pos.eq_dec b 704%positive);[subst b;right;left| ].
 { destruct present;SBUnfoldMemory;SuccessOutside. }
 destruct(Pos.eq_dec b 705%positive);[subst b;right;left| ].
 { destruct present;SBUnfoldMemory;SuccessOutside. }
 destruct(Pos.eq_dec b 706%positive);[subst b;right;left| ].
 { destruct present;SBUnfoldMemory;SuccessOutside. }
 destruct(Pos.eq_dec b 707%positive);[subst b;right;left| ].
 { destruct present;SBUnfoldMemory;SuccessOutside. }
 destruct(Pos.eq_dec b 708%positive);[subst b;right;left| ].
 { destruct present;SBUnfoldMemory;SuccessOutside. }
 destruct(Pos.eq_dec b 709%positive);[subst b;right;left| ].
 { destruct present;SBUnfoldMemory;SuccessOutside. }
 left. destruct present;SBUnfoldMemory;SuccessOutside.
Qed.
Lemma SBRestCallerApart : forall present cpu,
 join(SBRestMemory present)(merge(CallLocals Vundef Vnull Vundef)(SBExtra cpu))(merge(SBRestMemory present)(merge(CallLocals Vundef Vnull Vundef)(SBExtra cpu))).
Proof.
 intros. apply map_join_merge;apply map_disjoint;intros[b off].
 destruct(Pos.eq_dec b 210%positive);[subst b;right;left| ].
 { destruct present;SBUnfoldMemory;SuccessOutside. }
 destruct(Pos.eq_dec b 212%positive);[subst b;right;left| ].
 { destruct present;SBUnfoldMemory;SuccessOutside. }
 destruct(Pos.eq_dec b 213%positive);[subst b;right;left| ].
 { destruct present;SBUnfoldMemory;SuccessOutside. }
 destruct(Pos.eq_dec b 214%positive);[subst b;right;left| ].
 { destruct present;SBUnfoldMemory;SuccessOutside. }
 destruct(Pos.eq_dec b 215%positive);[subst b;right;left| ].
 { destruct present;SBUnfoldMemory;SuccessOutside. }
 destruct(Pos.eq_dec b 301%positive);[subst b;right;left| ].
 { destruct present;SBUnfoldMemory;SuccessOutside. }
 destruct(Pos.eq_dec b 402%positive);[subst b;right;left| ].
 { destruct present;SBUnfoldMemory;SuccessOutside. }
 destruct(Pos.eq_dec b 601%positive);[subst b;right;left| ].
 { destruct present;SBUnfoldMemory;SuccessOutside. }
 left. destruct present;SBUnfoldMemory;SuccessOutside.
Qed.
Lemma SBSlotApart : forall present cpu,
 join(SBSlot Vnull)(merge(SBRestMemory present)(merge(CallLocals Vundef Vnull Vundef)(SBExtra cpu)))(merge(SBSlot Vnull)(merge(SBRestMemory present)(merge(CallLocals Vundef Vnull Vundef)(SBExtra cpu)))).
Proof.
 intros. apply map_join_merge;apply map_disjoint;intros[b off].
 destruct(Pos.eq_dec b 211%positive);[subst b;right;left| ].
 { destruct present;SBUnfoldMemory;SuccessOutside. }
 left. destruct present;SBUnfoldMemory;SuccessOutside.
Qed.
Definition SBSplit present cpu := Amapsto(211%positive,44%Z)(Tptr V293_tcb_type)true Vnull **
 V293_rdy_raw_cells(SBRestCells present)(SuccessGlobals ** SuccessR) **
 (LV 209%Z @ Tint8 |->Vundef ** (Amapsto(701%positive,0%Z)Tint8 true(V293_byteval 11) **
 LV 108%Z @ (Tptr Tint32) |->Vundef ** LV 205%Z @ (Tptr Tint32) |->Vnull **
 LV 206%Z @ Tint16 |->Vint32 Int.zero ** LV 207%Z @ Tint32 |->Vint32(Int.repr 128) **
 LV 208%Z @ (Tptr Tvoid) |->Vnull ** LV 204%Z @ Tint16 |->Vint32 Int.zero ** CallFrame)) ** SBExtraAsrt cpu.
Lemma SBSplitSpatial : forall present cpu cs,SBState(SBMemory present cpu)cs |= SBSplit present cpu.
Proof.
 intros. unfold SBMemory,SBSplit. eapply SBStar.
 - apply SBSlotApart.
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
 - eapply SBStar.
   + apply SBRestCallerApart.
   + apply SBRestSpatial.
   + eapply SBStar.
     * apply(SBCallerExtraApart present).
     * apply SBLocalsSpatial.
     * apply SBExtraSpatial.
Qed.
Lemma SBPrefixBindings : forall cs,
 SBState emp cs |= V293_create_prefix_bindings 701%positive 720%positive 714%positive
 211%positive 97%Z 99%Z 721%positive.
Proof.
 intros. unfold V293_create_prefix_bindings.
 eapply SBStar with(m1:=emp)(m2:=emp);[apply map_join_emp| | ].
 - exists 701%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
 - eapply SBStar with(m1:=emp)(m2:=emp);[apply map_join_emp| | ].
   + exists 714%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
   + eapply SBStar with(m1:=emp)(m2:=emp);[apply map_join_emp| | ].
     * unfold V293_create_global_binding. split.
       -- exists 720%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
       -- split;[intros[x Bad];vm_compute in Bad;discriminate|repeat split;reflexivity].
     * eapply SBStar with(m1:=emp)(m2:=emp);[apply map_join_emp| | ].
       -- unfold V293_create_global_binding. split.
          ++ exists 721%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
          ++ split;[intros[x Bad];vm_compute in Bad;discriminate|repeat split;reflexivity].
       -- unfold V293_tcb_table_binding. split.
          ++ exists 211%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
          ++ split;[intros[x Bad];vm_compute in Bad;discriminate|repeat split;reflexivity].
Qed.
Theorem SBLiteralEntry : forall present cpu cs,
 SBState(SBMemory present cpu)cs |= SBEntry present cpu cs.
Proof.
 intros. unfold SBEntry,V293_create_prefix_state. apply astar_l_aop'_intro;[ |reflexivity].
 assert(K:SBState(SBMemory present cpu)cs |= Aisr(fun _=>false) ** Aie false ** (Ais nil) ** Acs cs **
 (V293_create_prefix_bindings 701%positive 720%positive 714%positive 211%positive 97%Z 99%Z 721%positive ** SBSplit present cpu)).
 { apply astar_l_aisr_intro;[ |reflexivity]. apply astar_l_aie_intro;[ |reflexivity].
   apply astar_l_ais_intro;[ |reflexivity]. apply astar_l_acs_intro;[ |reflexivity].
   eapply SBStar with(m1:=emp).
   - apply map_join_comm;apply map_join_emp.
   - apply SBPrefixBindings.
   - apply SBSplitSpatial. }
 unfold SBFrame,V293_create_success_body_frame,SBSplit,SBExtraAsrt,V293_create_stack_kept,
 V293_create_stack_arguments,V293_create_prefix_cells in *.
 cbn[V293_rdy_raw_cells]. clear -K. sep auto.
Qed.
Definition SBKept := V293_create_prefix_kept 720%positive 714%positive 97%Z 99%Z 721%positive
 (V293_tcb_table_binding 211%positive ** CallFrame).
Definition SBPost present cs := V293_create_success_return 98%Z 710%positive
 (getasrt(SBFpost present cs SuccessArguments(Some(Vint32 Int.zero))[logic_val SuccessHead]SuccessTid) **
 V293_create_tcb_arguments 11 Vnull Vnull(Vint32 Int.zero)(Vint32(Int.repr 128))Vnull(Vint32 Int.zero)
 (V293_create_stack_kept 17%Z SBArg SBInput SBKept)).
Definition SBBody := V293_CreateExt_body 92%Z 97%Z 99%Z 98%Z 901%Z 902%Z 900%Z.
Theorem SBHoareChecked : forall present cs,
 InfRules(SBSpec present cs)V293_scheduler V293_witness_li V293_shared_inv
 (SBPost present cs)Afalse(SBEntry present Vundef cs)SBBody Afalse SuccessTid.
Proof.
 intros. unfold SBPost,SBEntry,SBFrame,SBBody,SBKept,SBRestCells.
 eapply V293_OSTaskCreateExt_success_body_hoare with
 (good:=SuccessRFun)(old:=fun _=>Vundef)(oldprev:=Vundef)(oldback:=Vundef)
 (table:=211%positive)(bg:=210%positive)(bt:=301%positive)(base:=128%Z)(p:=11)
 (top:=Vnull)(bottom:=Vnull)(identity:=Vint32 Int.zero)(size:=Vint32(Int.repr 128))
 (ext:=Vnull)(options:=Vint32 Int.zero)(next:=SuccessNext)(bh:=212%positive)(bgrp:=213%positive)
 (br:=214%positive)(bn:=215%positive)(oldblock:=301%positive)(oldbase:=256%Z)(present:=present)
 (g:=1)(row:=129)(n:=254)(R:=SuccessR)(aop:=spec_done None)(isr:=fun _=>false)(is:=[])(cs:=cs).
 - apply SuccessRGood.
 - exact I.
 - lia.
 - repeat split;reflexivity.
 - repeat split;reflexivity.
 - apply SuccessRCurLINV.
 - apply SBHookLookup.
 - apply SBTCBLookup.
Qed.
Definition SBInternalPre present cs saved := V293_tcb_internal_pre_cells(V293_byteval 11)Vnull Vnull
 (Vint32 Int.zero)(Vint32(Int.repr 128))Vnull(Vint32 Int.zero) **
 getasrt(SBFpre present cs SuccessArguments[logic_val saved]SuccessTid) ** V293_tcb_internal_domain.
Theorem SBSameSpecCallee : forall present cs saved,
 InfRules(SBSpec present cs)V293_scheduler V293_witness_li V293_shared_inv
 (CallInternalPost present cs saved)Afalse(SBInternalPre present cs saved)
 (V293_TCBInit_function_body 501%Z 502%Z)Afalse SuccessTid.
Proof.
 intros present cs saved.
 eapply V293_OS_TCBInit_snapshot_internal_contract
 with(P:=SuccessProgram)(f:=900%Z)(vl:=rev SuccessArguments)(lg:=[logic_val saved])
 (Hfun:=SuccessRFun)(old:=fun _=>Vundef)(oldprev:=Vundef)(oldback:=Vundef)
 (slot:=SBReserved)(table:=211%positive)(bg:=210%positive)(bt:=301%positive)
 (base:=128%Z)(p:=11)(top:=Vnull)(bottom:=Vnull)(identity:=Vint32 Int.zero)
 (size:=Vint32(Int.repr 128))(ext:=Vnull)(options:=Vint32 Int.zero)(next:=SuccessNext)
 (bh:=212%positive)(bgrp:=213%positive)(br:=214%positive)(bn:=215%positive)
 (oldblock:=301%positive)(oldbase:=256%Z)(present:=present)(g:=1)(row:=129)(n:=254)
 (aop:=spec_done None)(isr:=fun _=>false)(is:=[])(cs:=cs).
 - apply SuccessGoodIInhabited.
 - lia.
 - lia.
 - unfold Int.max_unsigned,Int.modulus,Int.wordsize;cbn;lia.
 - lia.
 - unfold Int.max_unsigned,Int.modulus,Int.wordsize;cbn;lia.
 - repeat split;reflexivity.
 - reflexivity.
 - lia.
 - lia.
 - lia.
 - apply SuccessRGood.
 - apply SuccessRCurLINV.
 - SBLookup.
 - SBLookup.
 - reflexivity.
 - reflexivity.
 - reflexivity.
Qed.
Definition SBReservedEntry present cs := V293_create_prefix_state 701%positive 720%positive 714%positive
 211%positive 97%Z 99%Z 721%positive 11(Vint32 Int.zero)SBReserved(SBFrame present)
 (spec_done None)(fun _=>false)[]cs.
Theorem SBPrefixExecution : forall present P ks cs suffix,
 exists Mf,
 V293_local_steps P
 (curs(V293_TaskCreateExt_prefix 92%Z 101%Z 97%Z 109%Z 99%Z suffix),(kenil,ks))
 ((SBGE,SBLE,SBMemory present Vundef),(fun _=>false),(false,[],cs))
 (curs suffix,(kenil,kseq V293_TaskCreateExt_occupied ks))
 ((SBGE,SBLE,Mf),(fun _=>false),(false,[],cs)) /\
 load(Tptr V293_tcb_type)Mf(211%positive,44%Z)=Some SBReserved /\
 SBState Mf cs |= SBReservedEntry present cs.
Proof.
 intros present P ks cs suffix.
 pose proof(SBLiteralEntry present Vundef cs)as Owned.
 unfold SBEntry,V293_create_prefix_state in Owned.
 apply astar_l_aop'_elim in Owned. destruct Owned as[_ Owned].
 edestruct V293_OSTaskCreateExt_prefix_reserved with
 (P:=P)(ks:=ks)(ge:=SBGE)(le:=SBLE)(M:=SBMemory present Vundef)
 (ir:=fun (_:hid)=>false)(aux:=(false,(@nil hid),cs))(O:=(emp:osabst))(op:=spec_done None)
 (enabled:=false)(si:=(@nil hid))(ci:=cs)(table:=92%Z)(prio:=101%Z)(nesting:=97%Z)
 (cpu:=109%Z)(reserved:=99%Z)(bp:=701%positive)(bn:=720%positive)(bc:=714%positive)
 (bt:=211%positive)(br:=721%positive)(p:=11)(old:=Vundef)(suffix:=suffix)
 as[Mf[Trace Final]].
 - vm_compute;reflexivity.
 - vm_compute;reflexivity.
 - vm_compute;reflexivity.
 - vm_compute;reflexivity.
 - vm_compute;reflexivity.
 - vm_compute;reflexivity.
 - vm_compute;reflexivity.
 - vm_compute;reflexivity.
 - lia.
 - exact Owned.
 - exists Mf. split;[exact Trace| ].
   assert(Reserved:SBState Mf cs |= SBReservedEntry present cs).
   { unfold SBReservedEntry,V293_create_prefix_state,SBReserved.
     apply astar_l_aop'_intro;[exact Final|reflexivity]. }
   split;[ |exact Reserved]. unfold V293_create_prefix_cells in Final.
   V293_tcb_init_read Final 3%nat Read. exact Read.
Qed.
Theorem SBReservedSlotNotNull : forall present P ks cs suffix,
 exists Mf,
 V293_local_steps P
 (curs(V293_TaskCreateExt_prefix 92%Z 101%Z 97%Z 109%Z 99%Z suffix),(kenil,ks))
 ((SBGE,SBLE,SBMemory present Vundef),(fun _=>false),(false,[],cs))
 (curs suffix,(kenil,kseq V293_TaskCreateExt_occupied ks))
 ((SBGE,SBLE,Mf),(fun _=>false),(false,[],cs)) /\
 load(Tptr V293_tcb_type)Mf(211%positive,44%Z)<>Some Vnull.
Proof.
 intros. destruct(SBPrefixExecution present P ks cs suffix)as[Mf[T[L _]]].
 exists Mf. split;[exact T| ]. rewrite L. discriminate.
Qed.
(* The Hook adds only true argument/head facts to the same owned resource. *)
Theorem SBHookResourcePostPreserved : forall present cs s,
 s |= getasrt(SBBefore present cs) ->
 s |= getasrt(SBHookPost present cs SBArgs(Some Vnull)[]SuccessTid).
Proof.
 intros present cs s H.
 cbn[SBHookPost V293_create_stack_resource_fpost getasrt].
 apply astar_l_apure_intro;[ |split;reflexivity].
 cbn[SBFpre V293_tcb_snapshot_fpre SuccessHead V293_tcb_guard_fpre getasrt].
 apply astar_l_apure_intro;[ |reflexivity].
 cbn[SBReadyFpre V293_tcb_success_fpre getasrt].
 apply astar_l_apure_intro;[exact H|reflexivity].
Qed.
Definition SBCallsPre present cs := getasrt(SBBefore present cs) ** LV 108%Z @ (Tptr Tint32) |->Vundef **
 V293_create_stack_arguments 17%Z SBArg SBInput(Vint32 Int.zero)
 (LV 209%Z @ Tint8 |->Vundef ** LV 101%Z @ Tint8 |->V293_byteval 11 **
 LV 205%Z @ (Tptr Tint32) |->Vnull ** LV 206%Z @ Tint16 |->Vint32 Int.zero **
 LV 207%Z @ Tint32 |->Vint32(Int.repr 128) ** LV 208%Z @ (Tptr Tvoid) |->Vnull **
 (V293_create_idle_running 98%Z 710%positive ** SBKept)).
Theorem SBPrefixHandoff : forall present P ks cs suffix,
 exists Mf,
 V293_local_steps P
 (curs(V293_TaskCreateExt_prefix 92%Z 101%Z 97%Z 109%Z 99%Z suffix),(kenil,ks))
 ((SBGE,SBLE,SBMemory present Vundef),(fun _=>false),(false,[],cs))
 (curs suffix,(kenil,kseq V293_TaskCreateExt_occupied ks))
 ((SBGE,SBLE,Mf),(fun _=>false),(false,[],cs)) /\ SBState Mf cs |= SBCallsPre present cs.
Proof.
 intros. destruct(SBPrefixExecution present P ks cs suffix)as[Mf[Trace[Loaded Owned]]].
 exists Mf. split;[exact Trace| ].
 unfold SBReservedEntry,SBFrame in Owned.
 unfold SBCallsPre,SBKept,SBBefore,SBCells,SBReserved. cbn[getasrt].
 eapply V293_create_success_body_to_calls. exact Owned.
Qed.
