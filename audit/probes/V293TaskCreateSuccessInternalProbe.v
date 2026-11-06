Require Import CertiOS.certiucos.v293.proofs.V293TCBSuccessHoare.
(* Frozen success bytes; canonical nesting99 / reserved97 symbols.
   Exact caller declaration domain; no independent C translation or whole trace. *)
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
Definition SIReserved := Vptr(721%positive,Int.zero).
Definition SIArg := Vptr(801%positive,Int.zero).
Definition SIInput := Vptr(802%positive,Int.repr 16).
Definition SIArgs := V293_create_stack_values 17%Z SIArg SIInput(Vint32 Int.zero).
Definition SICells present := V293_tcb_success_pre_owned 211%positive SIReserved
 210%positive 301%positive 128%Z(fun _=>Vundef)SuccessNext
 212%positive 213%positive 214%positive 215%positive 301%positive 256%Z present 11 Vundef 1 129 254 Vundef.
Definition SIRestCells present := tl(SICells present).
Definition SIBefore present cs := @mkfunasrt
 (V293_tcb_success_external 211%positive 210%positive 212%positive 213%positive 214%positive 215%positive
 (SICells present)SuccessR(spec_done None)(fun _=>false)[]cs)
 (V293_tcb_success_external_good 211%positive 210%positive 212%positive 213%positive 214%positive 215%positive
 (SICells present)SuccessR(spec_done None)(fun _=>false)[]cs SuccessRFun).
Definition SIReadyFpre present cs := V293_tcb_success_fpre 211%positive SIReserved
 210%positive 301%positive 128%Z(fun _=>Vundef)11 Vnull Vnull(Vint32 Int.zero)
 (Vint32(Int.repr 128))Vnull(Vint32 Int.zero)SuccessNext 212%positive 213%positive 214%positive
 215%positive 301%positive 256%Z present Vundef 1 129 254 Vundef SuccessR
 (spec_done None)(fun _=>false)[]cs SuccessRFun.
Definition SIFpre present cs := V293_tcb_snapshot_fpre SuccessHead
 (V293_tcb_empty_fpre 210%positive SuccessR(spec_done None)(fun _=>false)[]cs SuccessRFun)
 (SIReadyFpre present cs).
Definition SIFpost := CallFpost.
Definition SIHookPre present cs := V293_create_stack_resource_fpre(SIBefore present cs)SIArgs.
Definition SIHookPost present cs := V293_create_stack_resource_fpost
 (SIFpre present cs SuccessArguments[logic_val SuccessHead]SuccessTid)SIArgs Vnull.
Definition SISpec present cs : funspec := fun f=>
 if Z.eq_dec f 902%Z then Some(SIHookPre present cs,SIHookPost present cs,(Tptr Tint32,rev V293_stack_argument_types))
 else if Z.eq_dec f 900%Z then Some(SIFpre present cs,SIFpost present cs,(Tint8,rev V293_TCBInit_argument_types))
 else if Z.eq_dec f 501%Z then Some(SuccessFpre SIReserved present cs,SuccessFpost SIReserved present cs,(Tvoid,[Tptr V293_tcb_type]))
 else if Z.eq_dec f 502%Z then Some(SuccessFpre SuccessHead present cs,SuccessFpost SuccessHead present cs,(Tvoid,[Tptr V293_tcb_type]))
 else None.
Ltac SILookup := unfold SISpec;repeat destruct(Z.eq_dec _ _);try discriminate;try contradiction;reflexivity.
Lemma SIHookLookup : forall present cs,
 SISpec present cs 902%Z=Some(SIHookPre present cs,SIHookPost present cs,(Tptr Tint32,rev V293_stack_argument_types)).
Proof. intros;SILookup. Qed.
Lemma SITCBLookup : forall present cs,
 SISpec present cs 900%Z=Some(SIFpre present cs,SIFpost present cs,(Tint8,rev V293_TCBInit_argument_types)).
Proof. intros;SILookup. Qed.
Definition SIGE : env := set(set(set SuccessGE 98%Z(710%positive,Tint8))
 99%Z(720%positive,Tint8))97%Z(721%positive,Tint8).
Definition SILE : env := set(set(set(set CallLE 201%Z(711%positive,Tint32))
 202%Z(712%positive,Tptr Tvoid))203%Z(713%positive,Tptr Tint32))109%Z(714%positive,Tint32).
Definition SIState M cs : RstateOP :=
 (SIGE,SILE,M,(fun _=>false),(false,[],cs),(emp:osabst),spec_done None).
Definition SIRestMemory present := merge(SuccessMemory(SIRestCells present))(merge SuccessCurrent SuccessSentinel).
Definition SIRunning := V293_encoded_memory 710%positive 0 false(encode_val Tint8(Vint32 Int.zero)).
Definition SIExtra cpu := merge(CallByte 711%positive Tint32(V293_task_selector 17%Z))
 (merge(CallByte 712%positive(Tptr Tvoid)SIArg)(merge(CallByte 713%positive(Tptr Tint32)SIInput)
 (merge SIRunning(merge(CallByte 720%positive Tint8(V293_byteval 0))(CallByte 714%positive Tint32 cpu))))).
Definition SISlot slot := V293_encoded_memory 211%positive 44 true(encode_val(Tptr V293_tcb_type)slot).
Definition SIMemory present cpu := merge(SISlot Vnull)
 (merge(SIRestMemory present)(merge(CallLocals Vundef Vnull Vundef)(SIExtra cpu))).
Definition SIFrame present := V293_create_success_body_frame(SIRestCells present)(SuccessGlobals ** SuccessR)
 Vundef 17%Z SIArg SIInput(Vint32 Int.zero)Vundef Vnull(Vint32 Int.zero)(Vint32(Int.repr 128))Vnull
 98%Z 710%positive CallFrame.
Definition SIEntry present cpu cs := V293_create_prefix_state 701%positive 720%positive 714%positive
 211%positive 99%Z 97%Z 721%positive 11 cpu Vnull(SIFrame present)(spec_done None)(fun _=>false)[]cs.
Lemma SIStar : forall m1 m2 m cs A B,
 join m1 m2 m -> SIState m1 cs |= A -> SIState m2 cs |= B -> SIState m cs |= A ** B.
Proof.
 intros. apply sat_split'. exists m1. exists m2. exists(emp:osabst). exists(emp:osabst).
 split;[exact H| ]. split;[apply map_join_emp| ]. split;assumption.
Qed.
Lemma SILVar : forall b x tp v cs,
 get SILE x=Some(b,tp) -> SIState(CallByte b tp v)cs |= LV x @ tp |->v.
Proof.
 intros b x tp v cs Env. exists b.
 eapply SIStar with(m1:=emp)(m2:=CallByte b tp v).
 - apply map_join_comm;apply map_join_emp.
 - exists b. split;[exact Env| ]. repeat split;reflexivity.
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Ltac SILocalApart b :=
 apply map_join_merge;apply map_disjoint;intros[other off];
 destruct(Pos.eq_dec other b);[subst other;right;left|left];
 unfold CallByte;
 repeat first[rewrite map_merge_semp by reflexivity|
 rewrite V293_encoded_memory_outside by(left;congruence)];reflexivity.
Ltac SILocalTactic :=
 lazymatch goal with
 | |- SIState(merge(CallByte ?b ?tp ?v)?tail)?cs |= LV ?x @ ?tp |-> ?v ** _ =>
   eapply SIStar with(m1:=CallByte b tp v)(m2:=tail);
   [SILocalApart b|apply SILVar;vm_compute;reflexivity|SILocalTactic]
 | |- SIState(CallByte 709%positive Tint8(Vint32(Int.repr 77)))?cs |= _ =>
   split;[apply V293_encoded_memory_mapsto|reflexivity]
 end.

Lemma SICurrentSpatial : forall cs, SIState SuccessCurrent cs |= CurTid SuccessTid.
Proof.
 intro cs. exists Tvoid. exists 402%positive.
 eapply SIStar with (m1:=emp) (m2:=SuccessCurrent).
 - apply map_join_comm;apply map_join_emp.
 - exists 402%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Lemma SILInvSpatial : forall cs, SIState emp cs |= LINV V293_witness_li SuccessTid [].
Proof.
 intro cs. unfold LINV. apply astar_comm. apply astar_l_apure_intro.
 - split;reflexivity.
 - apply V293_witness_li_good.
Qed.
Ltac SIFrameApart b :=
 apply map_join_merge;apply map_disjoint;intros [other offset];
 destruct(Pos.eq_dec other b);[subst other;right;left|left];
 unfold SuccessCurrent,SuccessSentinel,SuccessBytes;
 repeat first [rewrite map_merge_semp by reflexivity |
 rewrite V293_encoded_memory_outside by (left;congruence)];reflexivity.
Lemma SIRSpatial : forall cs,
 SIState (merge SuccessCurrent SuccessSentinel) cs |= SuccessR.
Proof.
 intro cs. unfold SuccessR.
 eapply SIStar with (m1:=SuccessCurrent) (m2:=SuccessSentinel).
 - SIFrameApart 402%positive.
 - apply SICurrentSpatial.
 - eapply SIStar with (m1:=emp) (m2:=SuccessSentinel).
   + apply map_join_comm;apply map_join_emp.
   + apply SILInvSpatial.
   + split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Lemma SILocalsSpatial : forall cs,
 SIState(CallLocals Vundef Vnull Vundef)cs |= LV 209%Z @ Tint8 |->Vundef **
 (Amapsto(701%positive,0%Z)Tint8 true(V293_byteval 11) **
 LV 108%Z @ (Tptr Tint32) |->Vundef ** LV 205%Z @ (Tptr Tint32) |->Vnull **
 LV 206%Z @ Tint16 |->Vint32 Int.zero ** LV 207%Z @ Tint32 |->Vint32(Int.repr 128) **
 LV 208%Z @ (Tptr Tvoid) |->Vnull ** LV 204%Z @ Tint16 |->Vint32 Int.zero ** CallFrame).
Proof.
 intro cs. unfold CallLocals,CallFrame.
 eapply SIStar with(m1:=CallByte 708%positive Tint8 Vundef).
 - SILocalApart 708%positive.
 - apply SILVar;vm_compute;reflexivity.
 - eapply SIStar with(m1:=CallByte 701%positive Tint8(V293_byteval 11)).
   + SILocalApart 701%positive.
   + split;[apply V293_encoded_memory_mapsto|reflexivity].
   + SILocalTactic.
Qed.
Ltac SIRawTactic :=
 lazymatch goal with
 | |- SIState(merge(V293_encoded_memory ?b ?off true(encode_val ?tp ?v))?tail)?cs |= _ =>
   let bytes:=eval cbv in(Z.of_nat(typelen tp))in
   eapply SIStar with(m1:=V293_encoded_memory b off true(encode_val tp v));
   [SuccessApart b off bytes|split;[apply V293_encoded_memory_mapsto|reflexivity]|SIRawTactic]
 | |- SIState emp _ |= Aemp => split;reflexivity
 end.
Ltac SIUnfoldRest := unfold SIRestCells,SICells,V293_tcb_success_pre_owned,
 V293_tcb_init_old_fields,V293_tcb_prefix_links,V293_link_extra;
 cbn[app tl SuccessMemory V293_rdy_raw_cells].
Lemma SIRawRest : forall present cs,
 SIState(SuccessMemory(SIRestCells present))cs |= V293_rdy_raw_cells(SIRestCells present)Aemp.
Proof. intros;destruct present;SIUnfoldRest;SIRawTactic. Qed.
Lemma SIGlobals : forall cs,SIState emp cs |= SuccessGlobals.
Proof.
 intro cs. unfold SuccessGlobals,V293_tcb_success_global_bindings.
 repeat(eapply SIStar with(m1:=emp)(m2:=emp);
 [apply map_join_emp|eexists;split;[vm_compute;reflexivity|repeat split;reflexivity]| ]).
 split;reflexivity.
Qed.
Lemma SIRestSpatial : forall present cs,
 SIState(SIRestMemory present)cs |= V293_rdy_raw_cells(SIRestCells present)(SuccessGlobals ** SuccessR).
Proof.
 intros. apply V293_raw_cells_join. unfold SIRestMemory.
 eapply SIStar with(m1:=SuccessMemory(SIRestCells present)).
 - apply map_join_merge;apply map_disjoint;intros[b off].
   destruct(Pos.eq_dec b 402%positive);[subst b;left| ].
   + destruct present;SIUnfoldRest;SuccessOutside.
   + destruct(Pos.eq_dec b 601%positive);[subst b;left|right;left].
     * destruct present;SIUnfoldRest;SuccessOutside.
     * unfold SuccessCurrent,SuccessSentinel,SuccessBytes;SuccessOutside.
 - apply SIRawRest.
 - eapply SIStar with(m1:=emp).
   + apply map_join_comm;apply map_join_emp.
   + apply SIGlobals.
   + apply SIRSpatial.
Qed.
Lemma SIRunningSpatial : forall cs,SIState SIRunning cs |= V293_create_idle_running 98%Z 710%positive.
Proof.
 intro cs. unfold V293_create_idle_running,V293_create_global_binding.
 eapply SIStar with(m1:=emp).
 - apply map_join_comm;apply map_join_emp.
 - split.
   + exists 710%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
   + split;[intros[v H];vm_compute in H;discriminate H|repeat split;reflexivity].
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Definition SIExtraAsrt cpu := V293_create_stack_kept 17%Z SIArg SIInput
 (V293_create_idle_running 98%Z 710%positive **
 Amapsto(720%positive,0%Z)Tint8 true(V293_byteval 0) ** Amapsto(714%positive,0%Z)Tint32 true cpu).
Lemma SIExtraSpatial : forall cpu cs,SIState(SIExtra cpu)cs |= SIExtraAsrt cpu.
Proof.
 intros. unfold SIExtra,SIExtraAsrt,V293_create_stack_kept.
 eapply SIStar with(m1:=CallByte 711%positive Tint32(V293_task_selector 17%Z)).
 - unfold SIRunning. SILocalApart 711%positive.
 - apply SILVar;vm_compute;reflexivity.
 - eapply SIStar with(m1:=CallByte 712%positive(Tptr Tvoid)SIArg).
   + unfold SIRunning. SILocalApart 712%positive.
   + apply SILVar;vm_compute;reflexivity.
   + eapply SIStar with(m1:=CallByte 713%positive(Tptr Tint32)SIInput).
     * unfold SIRunning. SILocalApart 713%positive.
     * apply SILVar;vm_compute;reflexivity.
     * eapply SIStar with(m1:=SIRunning).
       -- unfold SIRunning. SILocalApart 710%positive.
       -- apply SIRunningSpatial.
       -- eapply SIStar with(m1:=CallByte 720%positive Tint8(V293_byteval 0)).
          ++ SILocalApart 720%positive.
          ++ split;[apply V293_encoded_memory_mapsto|reflexivity].
          ++ split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Ltac SIUnfoldMemory := unfold SIRestMemory,CallLocals,SIExtra,SIRunning,SISlot,CallByte,
 SuccessCurrent,SuccessSentinel,SuccessBytes;SIUnfoldRest.
Lemma SICallerExtraApart : forall (present:bool) cpu,
 join(CallLocals Vundef Vnull Vundef)(SIExtra cpu)(merge(CallLocals Vundef Vnull Vundef)(SIExtra cpu)).
Proof.
 intros. apply map_join_merge;apply map_disjoint;intros[b off].
 destruct(Pos.eq_dec b 701%positive);[subst b;right;left| ].
 { destruct present;SIUnfoldMemory;SuccessOutside. }
 destruct(Pos.eq_dec b 702%positive);[subst b;right;left| ].
 { destruct present;SIUnfoldMemory;SuccessOutside. }
 destruct(Pos.eq_dec b 703%positive);[subst b;right;left| ].
 { destruct present;SIUnfoldMemory;SuccessOutside. }
 destruct(Pos.eq_dec b 704%positive);[subst b;right;left| ].
 { destruct present;SIUnfoldMemory;SuccessOutside. }
 destruct(Pos.eq_dec b 705%positive);[subst b;right;left| ].
 { destruct present;SIUnfoldMemory;SuccessOutside. }
 destruct(Pos.eq_dec b 706%positive);[subst b;right;left| ].
 { destruct present;SIUnfoldMemory;SuccessOutside. }
 destruct(Pos.eq_dec b 707%positive);[subst b;right;left| ].
 { destruct present;SIUnfoldMemory;SuccessOutside. }
 destruct(Pos.eq_dec b 708%positive);[subst b;right;left| ].
 { destruct present;SIUnfoldMemory;SuccessOutside. }
 destruct(Pos.eq_dec b 709%positive);[subst b;right;left| ].
 { destruct present;SIUnfoldMemory;SuccessOutside. }
 left. destruct present;SIUnfoldMemory;SuccessOutside.
Qed.
Lemma SIRestCallerApart : forall present cpu,
 join(SIRestMemory present)(merge(CallLocals Vundef Vnull Vundef)(SIExtra cpu))(merge(SIRestMemory present)(merge(CallLocals Vundef Vnull Vundef)(SIExtra cpu))).
Proof.
 intros. apply map_join_merge;apply map_disjoint;intros[b off].
 destruct(Pos.eq_dec b 210%positive);[subst b;right;left| ].
 { destruct present;SIUnfoldMemory;SuccessOutside. }
 destruct(Pos.eq_dec b 212%positive);[subst b;right;left| ].
 { destruct present;SIUnfoldMemory;SuccessOutside. }
 destruct(Pos.eq_dec b 213%positive);[subst b;right;left| ].
 { destruct present;SIUnfoldMemory;SuccessOutside. }
 destruct(Pos.eq_dec b 214%positive);[subst b;right;left| ].
 { destruct present;SIUnfoldMemory;SuccessOutside. }
 destruct(Pos.eq_dec b 215%positive);[subst b;right;left| ].
 { destruct present;SIUnfoldMemory;SuccessOutside. }
 destruct(Pos.eq_dec b 301%positive);[subst b;right;left| ].
 { destruct present;SIUnfoldMemory;SuccessOutside. }
 destruct(Pos.eq_dec b 402%positive);[subst b;right;left| ].
 { destruct present;SIUnfoldMemory;SuccessOutside. }
 destruct(Pos.eq_dec b 601%positive);[subst b;right;left| ].
 { destruct present;SIUnfoldMemory;SuccessOutside. }
 left. destruct present;SIUnfoldMemory;SuccessOutside.
Qed.
Lemma SISlotApart : forall present cpu,
 join(SISlot Vnull)(merge(SIRestMemory present)(merge(CallLocals Vundef Vnull Vundef)(SIExtra cpu)))(merge(SISlot Vnull)(merge(SIRestMemory present)(merge(CallLocals Vundef Vnull Vundef)(SIExtra cpu)))).
Proof.
 intros. apply map_join_merge;apply map_disjoint;intros[b off].
 destruct(Pos.eq_dec b 211%positive);[subst b;right;left| ].
 { destruct present;SIUnfoldMemory;SuccessOutside. }
 left. destruct present;SIUnfoldMemory;SuccessOutside.
Qed.
Definition SISplit present cpu := Amapsto(211%positive,44%Z)(Tptr V293_tcb_type)true Vnull **
 V293_rdy_raw_cells(SIRestCells present)(SuccessGlobals ** SuccessR) **
 (LV 209%Z @ Tint8 |->Vundef ** (Amapsto(701%positive,0%Z)Tint8 true(V293_byteval 11) **
 LV 108%Z @ (Tptr Tint32) |->Vundef ** LV 205%Z @ (Tptr Tint32) |->Vnull **
 LV 206%Z @ Tint16 |->Vint32 Int.zero ** LV 207%Z @ Tint32 |->Vint32(Int.repr 128) **
 LV 208%Z @ (Tptr Tvoid) |->Vnull ** LV 204%Z @ Tint16 |->Vint32 Int.zero ** CallFrame)) ** SIExtraAsrt cpu.
Lemma SISplitSpatial : forall present cpu cs,SIState(SIMemory present cpu)cs |= SISplit present cpu.
Proof.
 intros. unfold SIMemory,SISplit. eapply SIStar.
 - apply SISlotApart.
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
 - eapply SIStar.
   + apply SIRestCallerApart.
   + apply SIRestSpatial.
   + eapply SIStar.
     * apply(SICallerExtraApart present).
     * apply SILocalsSpatial.
     * apply SIExtraSpatial.
Qed.
Lemma SIPrefixBindings : forall cs,
 SIState emp cs |= V293_create_prefix_bindings 701%positive 720%positive 714%positive
 211%positive 99%Z 97%Z 721%positive.
Proof.
 intros. unfold V293_create_prefix_bindings.
 eapply SIStar with(m1:=emp)(m2:=emp);[apply map_join_emp| | ].
 - exists 701%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
 - eapply SIStar with(m1:=emp)(m2:=emp);[apply map_join_emp| | ].
   + exists 714%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
   + eapply SIStar with(m1:=emp)(m2:=emp);[apply map_join_emp| | ].
     * unfold V293_create_global_binding. split.
       -- exists 720%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
       -- split;[intros[x Bad];vm_compute in Bad;discriminate|repeat split;reflexivity].
     * eapply SIStar with(m1:=emp)(m2:=emp);[apply map_join_emp| | ].
       -- unfold V293_create_global_binding. split.
          ++ exists 721%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
          ++ split;[intros[x Bad];vm_compute in Bad;discriminate|repeat split;reflexivity].
       -- unfold V293_tcb_table_binding. split.
          ++ exists 211%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
          ++ split;[intros[x Bad];vm_compute in Bad;discriminate|repeat split;reflexivity].
Qed.
Theorem SILiteralEntry : forall present cpu cs,
 SIState(SIMemory present cpu)cs |= SIEntry present cpu cs.
Proof.
 intros. unfold SIEntry,V293_create_prefix_state. apply astar_l_aop'_intro;[ |reflexivity].
 assert(K:SIState(SIMemory present cpu)cs |= Aisr(fun _=>false) ** Aie false ** (Ais nil) ** Acs cs **
 (V293_create_prefix_bindings 701%positive 720%positive 714%positive 211%positive 99%Z 97%Z 721%positive ** SISplit present cpu)).
 { apply astar_l_aisr_intro;[ |reflexivity]. apply astar_l_aie_intro;[ |reflexivity].
   apply astar_l_ais_intro;[ |reflexivity]. apply astar_l_acs_intro;[ |reflexivity].
   eapply SIStar with(m1:=emp).
   - apply map_join_comm;apply map_join_emp.
   - apply SIPrefixBindings.
   - apply SISplitSpatial. }
 unfold SIFrame,V293_create_success_body_frame,SISplit,SIExtraAsrt,V293_create_stack_kept,
 V293_create_stack_arguments,V293_create_prefix_cells in *.
 cbn[V293_rdy_raw_cells]. clear -K. sep auto.
Qed.

Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateSuccessInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateEmptyInternal.
Require Import CertiOS.tactics.hoareforward.init_spec.

Definition SIInitialCells present := V293_tcb_success_pre_owned 211%positive Vnull
 210%positive 301%positive 128%Z(fun _=>Vundef)SuccessNext
 212%positive 213%positive 214%positive 215%positive 301%positive 256%Z present 11 Vundef 1 129 254 Vundef.
Definition SIValues := V293_create_internal_values 17%Z SIArg SIInput 11
 (Vint32 Int.zero)Vnull(Vint32(Int.repr 128))Vnull(Vint32 Int.zero).
Definition SIProgram : progunit := fun f=>
 if Z.eq_dec f 903%Z then Some(V293_CreateExt_function 92%Z 99%Z 97%Z 98%Z 901%Z 902%Z 900%Z)
 else SuccessProgram f.
Definition SICreatorPre present cs := V293_create_success_fpre 211%positive 210%positive
 212%positive 213%positive 214%positive 215%positive 720%positive 721%positive 710%positive
 (SIInitialCells present)11 17%Z SIArg SIInput(Vint32 Int.zero)Vnull(Vint32(Int.repr 128))
 Vnull(Vint32 Int.zero)SuccessR(spec_done None)(fun _=>false)[]cs SuccessRFun.
Definition SICreatorPost present cs := V293_create_success_fpost 720%positive 721%positive
 710%positive(SIFpost present cs)SuccessArguments SuccessHead.
Definition SIBuilderPre present cs := V293_create_internal_pre_cells 17%Z SIArg SIInput 11
 (Vint32 Int.zero)Vnull(Vint32(Int.repr 128))Vnull(Vint32 Int.zero) **
 getasrt(SICreatorPre present cs SIValues[]SuccessTid) ** V293_create_internal_domain.
Definition SIBuilderPost present cs : retasrt := fun result=>V293_create_internal_post_cells **
 getasrt(SICreatorPost present cs SIValues result[]SuccessTid) ** V293_create_internal_domain.
Theorem SITypedArguments : dl_vl_match V293_CreateExt_parameters SIValues=true.
Proof. reflexivity. Qed.
Theorem SIRealBuilders : forall present cs,
 Some(SIBuilderPre present cs)=BuildPreI SIProgram 903%Z(rev SIValues)[]
 (SICreatorPre present cs)SuccessTid /\
 Some(SIBuilderPost present cs)=BuildRetI SIProgram 903%Z(rev SIValues)[]
 (SICreatorPost present cs)SuccessTid.
Proof.
 intros. unfold BuildPreI,BuildRetI,SIProgram.
 destruct(Z.eq_dec 903%Z 903%Z);[ |contradiction]. rewrite rev_involutive. split;reflexivity.
Qed.
Theorem SIContractChecked : forall present cs,
 InfRules(SISpec present cs)V293_scheduler V293_witness_li V293_shared_inv
 (SIBuilderPost present cs)Afalse(SIBuilderPre present cs)
 (V293_CreateExt_body 92%Z 99%Z 97%Z 98%Z 901%Z 902%Z 900%Z)Afalse SuccessTid.
Proof.
 intros present cs.
 eapply V293_OSTaskCreateExt_success_internal_contract with
 (P:=SIProgram)(creator:=903%Z)(vl:=rev SIValues)(lg:=[])
 (good:=SuccessRFun)(old:=fun _=>Vundef)(oldprev:=Vundef)(oldback:=Vundef)
 (table:=211%positive)(bg:=210%positive)(bt:=301%positive)(base:=128%Z)(p:=11)
 (top:=Vnull)(bottom:=Vnull)(identity:=Vint32 Int.zero)(size:=Vint32(Int.repr 128))
 (ext:=Vnull)(options:=Vint32 Int.zero)(next:=SuccessNext)(bh:=212%positive)(bgrp:=213%positive)
 (br:=214%positive)(bn:=215%positive)(oldblock:=301%positive)(oldbase:=256%Z)(present:=present)
 (g:=1)(row:=129)(n:=254)(R:=SuccessR)(aop:=spec_done None)(isr:=fun _=>false)(is:=[])(cs:=cs)
 (bnest:=720%positive)(breserved:=721%positive)(brun:=710%positive)
 (target:=17%Z)(argv:=SIArg)(inputtop:=SIInput).
 - apply SuccessRGood.
 - lia.
 - repeat split;reflexivity.
 - repeat split;reflexivity.
 - apply SuccessRCurLINV.
 - apply SIHookLookup.
 - apply SITCBLookup.
 - unfold SIProgram. destruct(Z.eq_dec 903%Z 903%Z);[reflexivity|contradiction].
 - apply SIRealBuilders.
 - apply SIRealBuilders.
Qed.

Lemma SIExactDomain : eq_dom_env SILE(getlenvdom V293_create_internal_declarations).
Proof.
 unfold eq_dom_env. intros x tp.
 destruct(Z.eq_dec x 109%Z)as[E109|E109].
 { subst x. cbn [V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
   unfold SILE,CallLE. repeat rewrite map_get_set' by congruence.
   first[rewrite map_get_set|rewrite map_get_sig]. split.
   - intro H. repeat destruct H as[H|H];try discriminate;try contradiction;inversion H;subst;eexists;reflexivity.
   - intros[b H]. inversion H;subst. cbn. tauto. }
 destruct(Z.eq_dec x 203%Z)as[E203|E203].
 { subst x. cbn [V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
   unfold SILE,CallLE. repeat rewrite map_get_set' by congruence.
   first[rewrite map_get_set|rewrite map_get_sig]. split.
   - intro H. repeat destruct H as[H|H];try discriminate;try contradiction;inversion H;subst;eexists;reflexivity.
   - intros[b H]. inversion H;subst. cbn. tauto. }
 destruct(Z.eq_dec x 202%Z)as[E202|E202].
 { subst x. cbn [V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
   unfold SILE,CallLE. repeat rewrite map_get_set' by congruence.
   first[rewrite map_get_set|rewrite map_get_sig]. split.
   - intro H. repeat destruct H as[H|H];try discriminate;try contradiction;inversion H;subst;eexists;reflexivity.
   - intros[b H]. inversion H;subst. cbn. tauto. }
 destruct(Z.eq_dec x 201%Z)as[E201|E201].
 { subst x. cbn [V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
   unfold SILE,CallLE. repeat rewrite map_get_set' by congruence.
   first[rewrite map_get_set|rewrite map_get_sig]. split.
   - intro H. repeat destruct H as[H|H];try discriminate;try contradiction;inversion H;subst;eexists;reflexivity.
   - intros[b H]. inversion H;subst. cbn. tauto. }
 destruct(Z.eq_dec x 209%Z)as[E209|E209].
 { subst x. cbn [V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
   unfold SILE,CallLE. repeat rewrite map_get_set' by congruence.
   first[rewrite map_get_set|rewrite map_get_sig]. split.
   - intro H. repeat destruct H as[H|H];try discriminate;try contradiction;inversion H;subst;eexists;reflexivity.
   - intros[b H]. inversion H;subst. cbn. tauto. }
 destruct(Z.eq_dec x 204%Z)as[E204|E204].
 { subst x. cbn [V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
   unfold SILE,CallLE. repeat rewrite map_get_set' by congruence.
   first[rewrite map_get_set|rewrite map_get_sig]. split.
   - intro H. repeat destruct H as[H|H];try discriminate;try contradiction;inversion H;subst;eexists;reflexivity.
   - intros[b H]. inversion H;subst. cbn. tauto. }
 destruct(Z.eq_dec x 208%Z)as[E208|E208].
 { subst x. cbn [V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
   unfold SILE,CallLE. repeat rewrite map_get_set' by congruence.
   first[rewrite map_get_set|rewrite map_get_sig]. split.
   - intro H. repeat destruct H as[H|H];try discriminate;try contradiction;inversion H;subst;eexists;reflexivity.
   - intros[b H]. inversion H;subst. cbn. tauto. }
 destruct(Z.eq_dec x 207%Z)as[E207|E207].
 { subst x. cbn [V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
   unfold SILE,CallLE. repeat rewrite map_get_set' by congruence.
   first[rewrite map_get_set|rewrite map_get_sig]. split.
   - intro H. repeat destruct H as[H|H];try discriminate;try contradiction;inversion H;subst;eexists;reflexivity.
   - intros[b H]. inversion H;subst. cbn. tauto. }
 destruct(Z.eq_dec x 206%Z)as[E206|E206].
 { subst x. cbn [V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
   unfold SILE,CallLE. repeat rewrite map_get_set' by congruence.
   first[rewrite map_get_set|rewrite map_get_sig]. split.
   - intro H. repeat destruct H as[H|H];try discriminate;try contradiction;inversion H;subst;eexists;reflexivity.
   - intros[b H]. inversion H;subst. cbn. tauto. }
 destruct(Z.eq_dec x 205%Z)as[E205|E205].
 { subst x. cbn [V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
   unfold SILE,CallLE. repeat rewrite map_get_set' by congruence.
   first[rewrite map_get_set|rewrite map_get_sig]. split.
   - intro H. repeat destruct H as[H|H];try discriminate;try contradiction;inversion H;subst;eexists;reflexivity.
   - intros[b H]. inversion H;subst. cbn. tauto. }
 destruct(Z.eq_dec x 108%Z)as[E108|E108].
 { subst x. cbn [V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
   unfold SILE,CallLE. repeat rewrite map_get_set' by congruence.
   first[rewrite map_get_set|rewrite map_get_sig]. split.
   - intro H. repeat destruct H as[H|H];try discriminate;try contradiction;inversion H;subst;eexists;reflexivity.
   - intros[b H]. inversion H;subst. cbn. tauto. }
 destruct(Z.eq_dec x 101%Z)as[E101|E101].
 { subst x. cbn [V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
   unfold SILE,CallLE. repeat rewrite map_get_set' by congruence.
   first[rewrite map_get_set|rewrite map_get_sig]. split.
   - intro H. repeat destruct H as[H|H];try discriminate;try contradiction;inversion H;subst;eexists;reflexivity.
   - intros[b H]. inversion H;subst. cbn. tauto. }
 cbn [V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
 unfold SILE,CallLE. repeat rewrite map_get_set' by congruence. rewrite map_get_sig' by congruence.
 split.
 - intro H. repeat destruct H as[H|H];try contradiction;inversion H;congruence.
 - intros[b H]. discriminate.
Qed.

Theorem SILiteralBuilderEntry : forall present cpu cs,
 SIState(SIMemory present cpu)cs |= SIBuilderPre present cs ** CallFrame.
Proof.
 intros present cpu cs. pose proof(SILiteralEntry present cpu cs)as H.
 assert(D:SIState(SIMemory present cpu)cs |= V293_create_internal_domain ** SIEntry present cpu cs).
 { apply astar_l_adomlenv_intro;[exact H|apply SIExactDomain]. }
 unfold SIEntry,V293_create_prefix_state,SIFrame,V293_create_success_body_frame,
 V293_create_prefix_cells,V293_create_prefix_bindings,V293_create_stack_arguments in D.
 cbn[V293_rdy_raw_cells]in D.
 assert(K:SIState(SIMemory present cpu)cs |=
 ((Alvarenv 101%Z Tint8(701%positive,0%Z) ** Amapsto(701%positive,0%Z)Tint8 true(V293_byteval 11)) **
 (Alvarenv 109%Z Tint32(714%positive,0%Z) ** Amapsto(714%positive,0%Z)Tint32 true cpu)) **
 (V293_create_internal_domain ** <||spec_done None||> ** OS[(fun _=>false),false,[],cs] **
 (V293_create_global_binding 99%Z Tint8 720%positive **
 V293_create_global_binding 97%Z Tint8 721%positive ** V293_tcb_table_binding 211%positive) **
 Amapsto(211%positive,44%Z)(Tptr V293_tcb_type)true Vnull **
 Amapsto(720%positive,0%Z)Tint8 true(V293_byteval 0) **
 V293_rdy_raw_cells(SIRestCells present)(SuccessGlobals ** SuccessR) **
 LV 108%Z @ (Tptr Tint32) |->Vundef ** LV 201%Z @ Tint32 |->V293_task_selector 17%Z **
 LV 202%Z @ (Tptr Tvoid) |->SIArg ** LV 203%Z @ (Tptr Tint32) |->SIInput **
 LV 204%Z @ Tint16 |->Vint32 Int.zero ** LV 209%Z @ Tint8 |->Vundef **
 LV 205%Z @ (Tptr Tint32) |->Vnull ** LV 206%Z @ Tint16 |->Vint32 Int.zero **
 LV 207%Z @ Tint32 |->Vint32(Int.repr 128) ** LV 208%Z @ (Tptr Tvoid) |->Vnull **
 V293_create_idle_running 98%Z 710%positive ** CallFrame)).
 { clear -D. sep auto. }
 eapply astar_mono in K;[ |apply astar_mono;apply V293_create_raw_local|intros st HS;exact HS].
 assert(G:SIState(SIMemory present cpu)cs |=
 ((V293_create_global_binding 99%Z Tint8 720%positive **
 V293_create_global_binding 97%Z Tint8 721%positive ** V293_tcb_table_binding 211%positive) **
 V293_create_global_binding 98%Z Tint8 710%positive) **
 (V293_create_internal_domain ** <||spec_done None||> ** OS[(fun _=>false),false,[],cs] **
 Amapsto(211%positive,44%Z)(Tptr V293_tcb_type)true Vnull **
 Amapsto(720%positive,0%Z)Tint8 true(V293_byteval 0) **
 V293_rdy_raw_cells(SIRestCells present)(SuccessGlobals ** SuccessR) **
 LV 108%Z @ (Tptr Tint32) |->Vundef ** LV 201%Z @ Tint32 |->V293_task_selector 17%Z **
 LV 202%Z @ (Tptr Tvoid) |->SIArg ** LV 203%Z @ (Tptr Tint32) |->SIInput **
 LV 204%Z @ Tint16 |->Vint32 Int.zero ** LV 209%Z @ Tint8 |->Vundef **
 LV 205%Z @ (Tptr Tint32) |->Vnull ** LV 206%Z @ Tint16 |->Vint32 Int.zero **
 LV 207%Z @ Tint32 |->Vint32(Int.repr 128) ** LV 208%Z @ (Tptr Tvoid) |->Vnull **
 Amapsto(710%positive,0%Z)Tint8 false(Vint32 Int.zero) ** CallFrame **
 LV 101%Z @ Tint8 |->V293_byteval 11 ** LV 109%Z @ Tint32 |->cpu)).
 { unfold V293_create_idle_running in K. clear -K. sep auto. }
 eapply astar_mono with(P':=(Agvarenv 99%Z Tint8(720%positive,0%Z) **
 Agvarenv 97%Z Tint8(721%positive,0%Z) ** Aemp) **
 Agvarenv 98%Z Tint8(710%positive,0%Z)) in G.
 2:{ apply astar_mono.
     - apply astar_mono.
       + intros st[Bound NotLocal];exact Bound.
       + apply astar_mono.
         * intros st[Bound NotLocal];exact Bound.
         * intros st[Bound NotLocal]. clear -Bound. destruct_s st. simpl in *. join auto.
     - intros st[Bound NotLocal];exact Bound. }
 2:{ intros st HS;exact HS. }
 assert(G2:SIState(SIMemory present cpu)cs |=
 (OS[(fun _=>false),false,[],cs] ** V293_rdy_raw_cells(SIRestCells present)(SuccessGlobals ** SuccessR)) **
 (((Agvarenv 99%Z Tint8(720%positive,0%Z) ** Agvarenv 97%Z Tint8(721%positive,0%Z) ** Aemp) **
 Agvarenv 98%Z Tint8(710%positive,0%Z)) **
V293_create_internal_domain ** <||spec_done None||> **
 Amapsto(211%positive,44%Z)(Tptr V293_tcb_type)true Vnull **
 Amapsto(720%positive,0%Z)Tint8 true(V293_byteval 0) **
 LV 108%Z @ (Tptr Tint32) |->Vundef ** LV 201%Z @ Tint32 |->V293_task_selector 17%Z **
 LV 202%Z @ (Tptr Tvoid) |->SIArg ** LV 203%Z @ (Tptr Tint32) |->SIInput **
 LV 204%Z @ Tint16 |->Vint32 Int.zero ** LV 209%Z @ Tint8 |->Vundef **
 LV 205%Z @ (Tptr Tint32) |->Vnull ** LV 206%Z @ Tint16 |->Vint32 Int.zero **
 LV 207%Z @ Tint32 |->Vint32(Int.repr 128) ** LV 208%Z @ (Tptr Tvoid) |->Vnull **
 Amapsto(710%positive,0%Z)Tint8 false(Vint32 Int.zero) ** CallFrame **
 LV 101%Z @ Tint8 |->V293_byteval 11 ** LV 109%Z @ Tint32 |->cpu)).
 { clear -G. sep auto. }
 eapply astar_mono in G2;[ |apply V293_raw_cells_unmove_frame|intros st HS;exact HS].
 assert(InitialShape:SIInitialCells present=
 (((211%positive,44%Z),Tptr V293_tcb_type,Vnull)::SIRestCells present)).
 { reflexivity. }
 unfold SIBuilderPre,SICreatorPre,V293_create_success_fpre. cbn[getasrt].
 unfold V293_create_success_external,V293_tcb_success_external,V293_hook_resource,
 V293_create_internal_pre_cells,V293_create_internal_locals.
 rewrite InitialShape. cbn[V293_rdy_raw_cells]. fold SuccessGlobals.
 clear -G2. sep auto.

Qed.

Definition SIInternalPre present cs saved := V293_tcb_internal_pre_cells(V293_byteval 11)Vnull Vnull
 (Vint32 Int.zero)(Vint32(Int.repr 128))Vnull(Vint32 Int.zero) **
 getasrt(SIFpre present cs SuccessArguments[logic_val saved]SuccessTid) ** V293_tcb_internal_domain.
Theorem SISameSpecCallee : forall present cs saved,
 InfRules(SISpec present cs)V293_scheduler V293_witness_li V293_shared_inv
 (CallInternalPost present cs saved)Afalse(SIInternalPre present cs saved)
 (V293_TCBInit_function_body 501%Z 502%Z)Afalse SuccessTid.
Proof.
 intros present cs saved.
 eapply V293_OS_TCBInit_snapshot_internal_contract
 with(P:=SuccessProgram)(f:=900%Z)(vl:=rev SuccessArguments)(lg:=[logic_val saved])
 (Hfun:=SuccessRFun)(old:=fun _=>Vundef)(oldprev:=Vundef)(oldback:=Vundef)
 (slot:=SIReserved)(table:=211%positive)(bg:=210%positive)(bt:=301%positive)
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
 - SILookup.
 - SILookup.
 - reflexivity.
 - reflexivity.
 - reflexivity.
Qed.
