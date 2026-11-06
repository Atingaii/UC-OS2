(* Composition witness reuses Stage93/96 literal bytes; it is not an
   independent source translation or a call allocation/free execution. *)
Require Import CertiOS.audit.probes.V293TaskCreateTCBCallProbe.
Require Import CertiOS.audit.probes.V293TCBSuccessInternalProbe.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateFailureHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPriorityHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateTCBCall.
Require Import CertiOS.certiucos.v293.proofs.V293TCBSnapshotInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TCBSuccessInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEmptyInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293TCBHookCall.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtSuffix.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtCalls.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitFunction.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import Coq.Lists.List.ListNotations.
Local Open Scope nat_scope.

Require Import CertiOS.audit.probes.V293TaskCreateFailureHoareProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateStackCall.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateStackEntry.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtPrefix.

(* The port is EXTERNAL. NULL is only a typed call-site witness; this does
   not claim that a valid initialized stack can be NULL. *)
Definition StackArg := Vptr(801%positive,Int.zero).
Definition StackInput := Vptr(802%positive,Int.repr 16).
Definition StackArgs := V293_create_stack_values 17%Z StackArg StackInput(Vint32 Int.zero).
Definition StackFpre cs := V293_create_stack_fpre 210%positive SuccessR
 (spec_done None)(fun _=>false)[]cs SuccessRFun StackArgs.
Definition StackFpost cs := V293_create_stack_fpost 210%positive SuccessR
 (spec_done None)(fun _=>false)[]cs SuccessRFun StackArgs Vnull.
Definition StackSpec present cs : funspec := fun f=>
 if Z.eq_dec f 902%Z then Some(StackFpre cs,StackFpost cs,(Tptr Tint32,rev V293_stack_argument_types))
 else CallSpec present cs f.
Lemma StackLookup : forall present cs,
 StackSpec present cs 902%Z=Some(StackFpre cs,StackFpost cs,(Tptr Tint32,rev V293_stack_argument_types)).
Proof. intros. unfold StackSpec. destruct(Z.eq_dec 902%Z 902%Z);[reflexivity|contradiction]. Qed.
Lemma StackTCBLookup : forall present cs,
 StackSpec present cs 900%Z=Some(CallFpre present cs,CallFpost present cs,(Tint8,rev V293_TCBInit_argument_types)).
Proof. intros. unfold StackSpec. destruct(Z.eq_dec 900%Z 902%Z);[discriminate|apply CallLookup]. Qed.
Theorem StackCalleeContractChecked : forall present cs saved,
 InfRules(StackSpec present cs)V293_scheduler V293_witness_li V293_shared_inv
 (CallInternalPost present cs saved) Afalse (CallInternalPre present cs saved)
 (V293_TCBInit_function_body 501%Z 502%Z) Afalse SuccessTid.
Proof.
 intros present cs saved.
 eapply V293_OS_TCBInit_snapshot_internal_contract
 with (P:=SuccessProgram) (f:=900%Z) (vl:=rev SuccessArguments) (lg:=[logic_val saved])
 (Hfun:=SuccessRFun) (old:=fun _=>Vundef) (oldprev:=Vundef) (oldback:=Vundef)
 (slot:=Vundef) (table:=211%positive) (bg:=210%positive) (bt:=301%positive)
 (base:=128%Z) (p:=11) (top:=Vnull) (bottom:=Vnull) (identity:=Vint32 Int.zero)
 (size:=Vint32(Int.repr 128)) (ext:=Vnull) (options:=Vint32 Int.zero) (next:=SuccessNext)
 (bh:=212%positive) (bgrp:=213%positive) (br:=214%positive) (bn:=215%positive)
 (oldblock:=301%positive) (oldbase:=256%Z) (present:=present) (g:=1) (row:=129) (n:=254)
 (aop:=spec_done None) (isr:=fun _=>false) (is:=[]) (cs:=cs).
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
 - unfold StackSpec. destruct(Z.eq_dec 501%Z 902%Z);[discriminate| ].
   unfold CallSpec. destruct(Z.eq_dec 501%Z 900%Z);[discriminate|apply SuccessInitLookup].
 - unfold StackSpec. destruct(Z.eq_dec 502%Z 902%Z);[discriminate| ].
   unfold CallSpec. destruct(Z.eq_dec 502%Z 900%Z);[discriminate|apply SuccessCreateLookup].
 - reflexivity.
 - reflexivity.
 - reflexivity.
Qed.


(* Same old eight caller byte regions plus three new nonaliasing locals. *)
Definition StackLE : env := set(set(set CallLE 201%Z(710%positive,Tint32))
 202%Z(711%positive,Tptr Tvoid))203%Z(712%positive,Tptr Tint32).
Definition StackState M cs : RstateOP :=
 (SuccessGE,StackLE,M,(fun _=>false),(false,[],cs),(emp:osabst),spec_done None).
Definition StackLocals psp inputtop err :=
 merge(CallByte 710%positive Tint32(V293_task_selector 17%Z))
 (merge(CallByte 711%positive(Tptr Tvoid)StackArg)
 (merge(CallByte 712%positive(Tptr Tint32)inputtop)(CallLocals psp Vnull err))).
Definition StackLocalAsrt psp inputtop err :=
 V293_create_stack_kept 17%Z StackArg inputtop
 (LV 209%Z @ Tint8 |-> err ** CallArgs psp Vnull).
Lemma StackStar : forall m1 m2 m cs A B,
 join m1 m2 m -> StackState m1 cs |= A -> StackState m2 cs |= B ->
 StackState m cs |= A ** B.
Proof.
 intros. apply sat_split'. exists m1. exists m2. exists(emp:osabst). exists(emp:osabst).
 split;[exact H| ]. split;[apply map_join_emp| ]. split;assumption.
Qed.
Lemma StackLVar : forall b x tp v cs,
 get StackLE x=Some(b,tp) -> StackState(CallByte b tp v)cs |= LV x @ tp |->v.
Proof.
 intros b x tp v cs Env. exists b.
 eapply StackStar with(m1:=emp)(m2:=CallByte b tp v).
 - apply map_join_comm;apply map_join_emp.
 - exists b. split;[exact Env| ]. repeat split;reflexivity.
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Ltac StackLocalApart b :=
 apply map_join_merge;apply map_disjoint;intros[other off];
 destruct(Pos.eq_dec other b);[subst other;right;left|left];
 unfold CallByte;
 repeat first[rewrite map_merge_semp by reflexivity|
 rewrite V293_encoded_memory_outside by(left;congruence)];reflexivity.
Ltac StackLocalTactic :=
 lazymatch goal with
 | |- StackState(merge(CallByte ?b ?tp ?v)?tail)?cs |= LV ?x @ ?tp |-> ?v ** _ =>
   eapply StackStar with(m1:=CallByte b tp v)(m2:=tail);
   [StackLocalApart b|apply StackLVar;vm_compute;reflexivity|StackLocalTactic]
 | |- StackState(CallByte 709%positive Tint8(Vint32(Int.repr 77)))?cs |= _ =>
   split;[apply V293_encoded_memory_mapsto|reflexivity]
 end.

Lemma StackLocalsSpatial : forall psp inputtop err cs,
 StackState(StackLocals psp inputtop err)cs |= StackLocalAsrt psp inputtop err.
Proof.
 intros. unfold StackLocals,StackLocalAsrt,V293_create_stack_kept,CallLocals,CallArgs,V293_create_tcb_arguments,CallFrame.
 StackLocalTactic.
Qed.
Lemma StackRSpatial : forall cs,
 StackState(merge SuccessCurrent SuccessSentinel)cs |= SuccessR.
Proof.
 intro cs. eapply good_fun_asrt_absop;[exact SuccessRFun|apply SuccessRSpatial].
Qed.
Lemma StackEmptySpatial : forall cs,
 StackState CallEmptyMemory cs |= V293_tcb_empty_external 210%positive SuccessR
 (spec_done None)(fun _=>false)[]cs.
Proof.
 intro cs. unfold V293_tcb_empty_external.
 eapply StackStar with(m1:=emp)(m2:=CallEmptyMemory).
 - apply map_join_comm;apply map_join_emp.
 - exists 210%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
 - unfold CallEmptyMemory. eapply StackStar with(m1:=SuccessBytes 210%positive false(Tptr V293_tcb_type)Vnull).
   + unfold SuccessCurrent,SuccessSentinel,SuccessBytes. StackLocalApart 210%positive.
   + split;[apply V293_encoded_memory_mapsto|reflexivity].
   + apply astar_l_aop'_intro;[ |reflexivity].
     assert(K:StackState(merge SuccessCurrent SuccessSentinel)cs |=
      Aisr(fun _=>false) ** Aie false ** (Ais nil) ** Acs cs ** SuccessR).
     { apply astar_l_aisr_intro;[ |reflexivity].
       apply astar_l_aie_intro;[ |reflexivity].
       apply astar_l_ais_intro;[ |reflexivity].
       apply astar_l_acs_intro;[ |reflexivity]. apply StackRSpatial. }
     clear -K. sep auto.
Qed.

Definition StackRest psp inputtop err := merge CallEmptyMemory(StackLocals psp inputtop err).
Definition StackMemory slot psp inputtop err := merge(RollbackSlot slot)(StackRest psp inputtop err).
Definition StackFrame slot := RollbackBinding **
 (Amapsto(211%positive,44%Z)(Tptr V293_tcb_type)true slot ** CallFrame).
Definition StackEntry slot psp inputtop err cs :=
 V293_tcb_empty_external 210%positive SuccessR(spec_done None)(fun _=>false)[]cs **
 LV 108%Z @ (Tptr Tint32) |-> psp **
 V293_create_stack_arguments 17%Z StackArg inputtop(Vint32 Int.zero)
 (LV 209%Z @ Tint8 |-> err ** LV 101%Z @ Tint8 |-> V293_byteval 11 **
 LV 205%Z @ (Tptr Tint32) |-> Vnull ** LV 206%Z @ Tint16 |-> Vint32 Int.zero **
 LV 207%Z @ Tint32 |-> Vint32(Int.repr 128) ** LV 208%Z @ (Tptr Tvoid) |-> Vnull ** StackFrame slot).
Lemma StackFreshApart : forall psp inputtop err,
 join CallEmptyMemory(StackLocals psp inputtop err)(StackRest psp inputtop err).
Proof.
 intros. apply map_join_merge;apply map_disjoint;intros[b off].
 destruct(Pos.eq_dec b 210%positive);[subst b;right;left| ].
 { unfold StackLocals,CallLocals,CallByte. SuccessOutside. }
 destruct(Pos.eq_dec b 402%positive);[subst b;right;left| ].
 { unfold StackLocals,CallLocals,CallByte. SuccessOutside. }
 destruct(Pos.eq_dec b 601%positive);[subst b;right;left|left].
 { unfold StackLocals,CallLocals,CallByte. SuccessOutside. }
 unfold CallEmptyMemory,SuccessCurrent,SuccessSentinel,SuccessBytes. SuccessOutside.
Qed.
Lemma StackReserveApart : forall slot psp inputtop err,
 join(RollbackSlot slot)(StackRest psp inputtop err)(StackMemory slot psp inputtop err).
Proof.
 intros. apply map_join_merge;apply map_disjoint;intros[b off].
 destruct(Pos.eq_dec b 211%positive);[subst b;right;left|left].
 - unfold StackRest,StackLocals,CallEmptyMemory,CallLocals,CallByte,
   SuccessCurrent,SuccessSentinel,SuccessBytes. SuccessOutside.
 - unfold RollbackSlot. rewrite V293_encoded_memory_outside by(left;congruence). reflexivity.
Qed.
Lemma StackBindingSpatial : forall cs,StackState emp cs |= RollbackBinding.
Proof.
 intro cs. unfold RollbackBinding,V293_tcb_table_binding. split.
 - exists 211%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
 - split;[intros[x Bad];vm_compute in Bad;discriminate|repeat split;reflexivity].
Qed.
Theorem StackLiteralEntry : forall slot psp inputtop err cs,
 StackState(StackMemory slot psp inputtop err)cs |= StackEntry slot psp inputtop err cs.
Proof.
 intros.
 assert(H:StackState(StackMemory slot psp inputtop err)cs |=
 Amapsto(211%positive,44%Z)(Tptr V293_tcb_type)true slot **
 ((V293_tcb_empty_external 210%positive SuccessR(spec_done None)(fun _=>false)[]cs **
 StackLocalAsrt psp inputtop err) ** RollbackBinding)).
 { eapply StackStar with(m1:=RollbackSlot slot)(m2:=StackRest psp inputtop err).
   - apply StackReserveApart.
   - split;[apply V293_encoded_memory_mapsto|reflexivity].
   - eapply StackStar with(m1:=StackRest psp inputtop err)(m2:=emp).
     + apply map_join_emp.
     + unfold StackRest. eapply StackStar with(m1:=CallEmptyMemory)(m2:=StackLocals psp inputtop err).
       * apply StackFreshApart.
       * apply StackEmptySpatial.
       * apply StackLocalsSpatial.
     + apply StackBindingSpatial. }
 unfold StackEntry,StackFrame,StackLocalAsrt,V293_create_stack_arguments,V293_create_stack_kept,
 CallArgs,V293_create_tcb_arguments in *. clear -H. sep auto.
Qed.
Definition StackKept := V293_create_failure_kept 210%positive Vnull Vnull
 (Vint32 Int.zero)(Vint32(Int.repr 128))Vnull(Vint32 Int.zero)SuccessR
 (V293_create_stack_kept 17%Z StackArg StackInput CallFrame).
Definition StackReturn cs := V293_create_failure_return 211%positive 11 StackKept
 (spec_done None)(fun _=>false)[]cs.
Theorem StackFullChainChecked : forall present cs running sched,
 InfRules(StackSpec present cs)V293_scheduler V293_witness_li V293_shared_inv
 (StackReturn cs)Afalse(StackEntry RollbackReserved Vundef StackInput Vundef cs)
 (V293_TaskCreateExt_calls 108%Z 902%Z 201%Z 202%Z 203%Z 204%Z 209%Z 900%Z
 101%Z 205%Z 206%Z 207%Z 208%Z(V293_TaskCreateExt_suffix 92%Z 101%Z 209%Z running sched))
 Afalse SuccessTid.
Proof.
 intros. unfold StackReturn,StackKept,StackEntry,StackFrame,RollbackBinding.
 eapply V293_OSTaskCreateExt_stack_empty_failure_hoare with
 (good:=SuccessRFun)(gb:=SuccessRFun)(old:=fun _=>Vundef)(oldprev:=Vundef)(oldback:=Vundef)
 (reserved:=RollbackReserved)(slot:=Vundef)(table:=211%positive)(bg:=210%positive)(bt:=301%positive)
 (base:=128%Z)(p:=11)(top:=Vnull)(bottom:=Vnull)(identity:=Vint32 Int.zero)
 (size:=Vint32(Int.repr 128))(ext:=Vnull)(options:=Vint32 Int.zero)(next:=SuccessNext)
 (bh:=212%positive)(bgrp:=213%positive)(br:=214%positive)(bn:=215%positive)
 (oldblock:=301%positive)(oldbase:=256%Z)(present:=present)(g:=1)(row:=129)(n:=254)
 (Rbefore:=SuccessR)(aop:=spec_done None)(isr:=fun _=>false)(is:=[])(cs:=cs).
 - apply SuccessRGood.
 - exact I.
 - lia.
 - repeat split;reflexivity.
 - apply SuccessRCurLINV.
 - repeat split;reflexivity.
 - apply SuccessRCurLINV.
 - apply StackLookup.
 - apply StackTCBLookup.
Qed.
Theorem StackFourArgumentsRead : forall cs,
 StackState(StackMemory RollbackReserved Vundef StackInput Vundef)cs |=
 Rvl[evar 201%Z;evar 202%Z;evar 203%Z;evar 204%Z]
 @(rev V293_stack_argument_types)==StackArgs.
Proof.
 intro cs. eapply V293_create_stack_arguments_read with(F:=Atrue).
 - repeat split;reflexivity.
 - pose proof(StackLiteralEntry RollbackReserved Vundef StackInput Vundef cs)as H.
   unfold StackEntry,V293_create_stack_arguments in *. clear -H. sep auto.
Qed.
Theorem StackReturnSatisfiable : forall cs,
 StackState(StackMemory Vnull Vnull StackInput(Vint32(Int.repr 66)))cs |=
 StackReturn cs(Some(Vint32(Int.repr 66))).
Proof.
 intro cs. unfold StackReturn,V293_create_failure_return. apply astar_l_apure_intro;[ |reflexivity].
 pose proof(StackLiteralEntry Vnull Vnull StackInput(Vint32(Int.repr 66))cs)as H.
 unfold V293_create_failure_state,V293_create_failure_resources,StackKept,V293_create_failure_kept,
 StackEntry,StackFrame,RollbackBinding,V293_tcb_empty_external,V293_create_stack_arguments,V293_create_stack_kept in *.
 clear -H. sep auto.
Qed.

(* Assignment-continuation control starts AFTER a port return. There is no
   assumed or fabricated execution of the external port body. *)
Definition StackBefore := StackMemory RollbackReserved Vundef StackInput Vundef.
Lemma StackReturnAssignment : forall P ks cs receiver b M old F,
 get StackLE receiver=Some(b,Tptr Tint32) ->
 StackState M cs |= Amapsto(b,0%Z)(Tptr Tint32)true old ** F ->
 exists Mf,
 cstepstar P(curs(sskip(Some Vnull)),(kenil,kassignr(evar receiver)(Tptr Tint32)ks))
 (SuccessGE,StackLE,M)(curs(sskip None),(kenil,ks))(SuccessGE,StackLE,Mf) /\
 StackState Mf cs |= Amapsto(b,0%Z)(Tptr Tint32)true Vnull ** F.
Proof.
 intros P ks cs receiver b M old F Env Owned.
 destruct(V293_tick_raw_slot_update(b,0%Z)(Tptr Tint32)old Vnull _ _ _ _ _ _ _ _
 ltac:(reflexivity)Owned)as[Mf[Store Updated]].
 exists Mf. split.
 - assert(Ty:evaltype(evar receiver)(SuccessGE,StackLE,M)=Some(Tptr Tint32)).
   { cbn [evaltype get_lenv]. cbv delta [env var memory.ident Modules.ident]in *. rewrite Env. reflexivity. }
   assert(Addr:evaladdr(evar receiver)(SuccessGE,StackLE,M)=Some(Vptr(b,Int.repr 0))).
   { cbn [evaladdr get_lenv]. cbv delta [env var memory.ident Modules.ident]in *. rewrite Env. reflexivity. }
   eapply c_stepstarn. { eapply stmt_step;[reflexivity|apply sassignrv_step]. }
   eapply V293_cstepstar_trans.
   { apply V293_expr_steps. apply evalval_imply_estepstar. eapply evaladdr_val_eq;[exact Ty|exact Addr]. }
   eapply c_stepstarn. { eapply stmt_step;[reflexivity| ]. eapply sassignend_step;try reflexivity. exact Store. }
   apply c_stepstar0.
 - unfold V293_owned_record_cell in Updated. apply astar_assoc_elim in Updated.
   apply astar_l_apure_elim in Updated. exact(proj2 Updated).
Qed.
Lemma StackLocalRaw : forall M cs x b tp v F,
 get StackLE x=Some(b,tp) ->
 StackState M cs |= LV x @ tp |-> v ** F ->
 StackState M cs |= Amapsto(b,0%Z)tp true v ** F.
Proof.
 intros M cs x b tp v F Env Owned. unfold Alvarmapsto,Alvarenv',Aptrmapsto in Owned.
 apply astar_l_aexists_elim in Owned. destruct Owned as[actual Owned].
 apply astar_assoc_elim in Owned. apply astar_l_alvarenv_elim in Owned.
 destruct Owned as[[_ Bind]Owned]. change(get StackLE x=Some(actual,tp))in Bind.
 rewrite Env in Bind. inversion Bind;subst actual. exact Owned.
Qed.
Theorem StackActualReceiverExecution : forall P ks (cs:language.cs),
 exists Mf,
 cstepstar P(curs(sskip(Some Vnull)),(kenil,kassignr(evar 108%Z)(Tptr Tint32)ks))
 (SuccessGE,StackLE,StackBefore)(curs(sskip None),(kenil,ks))(SuccessGE,StackLE,Mf) /\
 load(Tptr Tint32)Mf(702%positive,0%Z)=Some Vnull.
Proof.
 intros. pose proof(StackLiteralEntry RollbackReserved Vundef StackInput Vundef cs)as H.
 assert(Owned:StackState StackBefore cs |= Amapsto(702%positive,0%Z)(Tptr Tint32)true Vundef ** Atrue).
 { eapply StackLocalRaw with(x:=108%Z);[vm_compute;reflexivity| ].
   unfold StackEntry in H. clear -H. sep auto. }
 destruct(StackReturnAssignment P ks cs 108%Z 702%positive StackBefore Vundef Atrue
 ltac:(vm_compute;reflexivity)Owned)as[Mf[Trace After]].
 exists Mf. split;[exact Trace| ].
 change(load(Tptr Tint32)(getmem(StackState Mf cs))(702%positive,0%Z)=Some Vnull).
 eapply V293_star_load_l;[ |exact After]. intros st[Map Empty].
 eapply mapstoval_load;[reflexivity|exact Map].
Qed.
Theorem StackWrongReceiverExecution : forall P ks (cs:language.cs),
 exists Mf,
 cstepstar P(curs(sskip(Some Vnull)),(kenil,kassignr(evar 203%Z)(Tptr Tint32)ks))
 (SuccessGE,StackLE,StackBefore)(curs(sskip None),(kenil,ks))(SuccessGE,StackLE,Mf) /\
 load(Tptr Tint32)Mf(702%positive,0%Z)=Some Vundef /\
 load(Tptr Tint32)Mf(712%positive,0%Z)=Some Vnull.
Proof.
 intros. pose proof(StackLiteralEntry RollbackReserved Vundef StackInput Vundef cs)as H.
 assert(Owned:StackState StackBefore cs |=
 Amapsto(712%positive,0%Z)(Tptr Tint32)true StackInput **
 (Amapsto(702%positive,0%Z)(Tptr Tint32)true Vundef ** Atrue)).
 { assert(L:StackState StackBefore cs |= LV 108%Z @ (Tptr Tint32) |-> Vundef **
     (LV 203%Z @ (Tptr Tint32) |-> StackInput ** Atrue)).
   { unfold StackEntry,V293_create_stack_arguments in H. clear -H. sep auto. }
   apply StackLocalRaw with(b:=702%positive)in L;[ |vm_compute;reflexivity].
   eapply StackLocalRaw with(x:=203%Z);[vm_compute;reflexivity| ]. clear -L. sep auto. }
 destruct(StackReturnAssignment P ks cs 203%Z 712%positive StackBefore StackInput
 (Amapsto(702%positive,0%Z)(Tptr Tint32)true Vundef ** Atrue)
 ltac:(vm_compute;reflexivity)Owned)as[Mf[Trace After]].
 exists Mf. split;[exact Trace| ]. split.
 - change(load(Tptr Tint32)(getmem(StackState Mf cs))(702%positive,0%Z)=Some Vundef).
   eapply V293_star_load_r;[ |exact After]. intros st Rem.
   eapply V293_star_load_l;[ |exact Rem]. intros st' Undef.
   eapply V293_tick_raw_pointer_load;[left;reflexivity|exact Undef].
 - change(load(Tptr Tint32)(getmem(StackState Mf cs))(712%positive,0%Z)=Some Vnull).
   eapply V293_star_load_l;[ |exact After]. intros st[Map Empty].
   eapply mapstoval_load;[reflexivity|exact Map].
Qed.
