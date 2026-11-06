Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtPrefix.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateExtPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope Z_scope.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateStackEntry.
Require Import CertiOS.certiucos.v293.proofs.V293NullBytes.

Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtCalls.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitFunction.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateTCBEntry.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateTCBSuccess.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateResult.
Require Import CertiOS.certiucos.v293.proofs.V293TCBCallSuccess.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFunction.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPriorityHook.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBCall.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitEntry.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPublish.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtSuffix.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateSuffix.
Local Open Scope Z_scope.

Definition CreateGEBase : env :=
 set(set(set(set(set(set(set(set emp
 91%Z (209%positive,Tptr V293_tcb_type))
 92%Z (510%positive,Tarray(Tptr V293_tcb_type)13))
 93%Z (401%positive,Tptr V293_tcb_type)) 94%Z (402%positive,Tint8))
 95%Z (403%positive,Tarray Tint8 2)) 96%Z (404%positive,Tint8))
 97%Z (502%positive,Tint8)) 98%Z (700%positive,Tint8).
Definition CreateGE : env := set CreateGEBase 99%Z (520%positive,Tint8).
Definition CreateRest := V293_TaskCreateExt_suffix 92%Z 101%Z 209%Z 99%Z 904%Z.
Definition CreateLE : env :=
 set(set(set(set(set(set(set(set(set(set(set(set emp
  101%Z (501%positive,Tint8)) 109%Z (503%positive,Tint32))
  108%Z (504%positive,Tptr Tint32)) 201%Z (505%positive,Tint32))
  202%Z (506%positive,Tptr Tvoid)) 203%Z (507%positive,Tptr Tint32))
  204%Z (508%positive,Tint16)) 205%Z (509%positive,Tptr Tint32))
  206%Z (511%positive,Tint16)) 207%Z (512%positive,Tint32))
  208%Z (513%positive,Tptr Tvoid)) 209%Z (514%positive,Tint8).
Definition CreateArg := Vptr(801%positive,Int.zero).
Definition CreateTop := Vptr(802%positive,Int.repr 16).
Definition CreateOpt := Vint32(Int.repr 5).
Definition CreateBottom := Vptr(804%positive,Int.repr 64).
Definition CreateId := Vint32(Int.repr 17).
Definition CreateSize := Vint32(Int.repr 1024).
Definition CreateExt := Vptr(805%positive,Int.zero).
Definition CreateValue (nonnull:bool) := if nonnull then Vptr(803%positive,Int.repr 32) else Vnull.
Definition CreateOld : list V293_record_cell :=
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

Definition CreateNext := Vptr(806%positive,Int.repr 56).
Definition CreateOuterBase : list V293_record_cell :=
 [((510%positive,4),Tptr V293_tcb_type,Vnull);
 ((601%positive,0),Tint32,Vint32(Int.repr 77));
 ((602%positive,0),Tint8,Vint32(Int.repr 88))].
Definition CreateOuter := ((520%positive,0),Tint8,Vint32 Int.zero)::CreateOuterBase.
Definition CreateFrame : list V293_record_cell := CreateOld++
 [((209%positive,0),Tptr V293_tcb_type,Vptr(301%positive,Int.repr 8));
 ((301%positive,28),Tcom_ptr 410%Z,CreateNext);
 ((301%positive,32),Tcom_ptr 410%Z,Vundef);
 ((401%positive,0),Tptr V293_tcb_type,Vnull);
 ((402%positive,0),Tint8,V293_byteval 2);
 ((403%positive,1),Tint8,V293_byteval 2);
 ((404%positive,0),Tint8,V293_byteval 7)]++CreateOuter.
Definition CreateCells p cpu slot pspv : list V293_record_cell :=
 [((501%positive,0),Tint8,V293_byteval p);
  ((502%positive,0),Tint8,Vint32 Int.zero);
  ((503%positive,0),Tint32,cpu);
  ((510%positive,4*Z.of_nat p),Tptr V293_tcb_type,slot);
  ((505%positive,0),Tint32,V293_task_selector 700);
  ((506%positive,0),Tptr Tvoid,CreateArg);
  ((507%positive,0),Tptr Tint32,CreateTop);
  ((508%positive,0),Tint16,CreateOpt);
  ((504%positive,0),Tptr Tint32,pspv);
  ((509%positive,0),Tptr Tint32,CreateBottom);
  ((511%positive,0),Tint16,CreateId);
  ((512%positive,0),Tint32,CreateSize);
  ((513%positive,0),Tptr Tvoid,CreateExt);
  ((514%positive,0),Tint8,Vint32(Int.repr 9))]++CreateFrame.
Definition CreateReturnCells p := CreateCells p (Vint32 Int.zero) (Vptr(700%positive,Int.zero)) Vnull.
Definition CreateBodyCells p := CreateCells p (Vint32(Int.repr 23)) Vnull Vnull.
Definition CreateExpected p nonnull := CreateCells p (Vint32 Int.zero) (Vptr(700%positive,Int.zero)) (CreateValue nonnull).
Fixpoint CreateMemory (cells : list V293_record_cell) : mem :=
 match cells with []=>emp | ((b,off),tp,v)::tail=>
 merge (V293_encoded_memory b off true (encode_val tp v)) (CreateMemory tail) end.
Definition CreateEntry p := CreateMemory(CreateReturnCells p).
Definition CreateBodyEntry p := CreateMemory(CreateBodyCells p).
Definition CreateContinuation := V293_create_stack_cont 108%Z 209%Z 901%Z 101%Z 205%Z 206%Z 207%Z 208%Z 204%Z CreateRest kstop.
Definition CreateReturnStart nonnull := (curs(sskip(Some(CreateValue nonnull))),(kenil,CreateContinuation)).
Definition CreateTCBContinuation := V293_create_TCB_cont 209%Z CreateRest kstop.
Definition CreateStop p nonnull :=
 (curs(sfexec 901%Z [CreateOpt;CreateExt;CreateSize;CreateId;CreateBottom;CreateValue nonnull;V293_byteval p]
 V293_TCBInit_argument_types),(kenil,CreateTCBContinuation)).
Definition CreateStart :=
 (curs(V293_TaskCreateExt_prefix 92%Z 101%Z 97%Z 109%Z 98%Z
 (V293_TaskCreateExt_calls 108%Z 900%Z 201%Z 202%Z 203%Z 204%Z 209%Z 901%Z 101%Z 205%Z 206%Z 207%Z 208%Z CreateRest)),
 (kenil,kstop)).
Definition CreateHookStop :=
 (curs(sfexec 900%Z [CreateOpt;CreateTop;CreateArg;V293_task_selector 700] V293_stack_argument_types),
 (kenil,CreateContinuation)).
Ltac CreateOutside :=
 repeat first [rewrite V293_encoded_memory_outside by
 (first [left;congruence | right;cbn [length CreateNext V293_byteval V293_task_selector CreateArg CreateTop CreateOpt CreateBottom CreateId CreateSize CreateExt CreateValue encode_val typelen list_repeat inj_pointer inj_bytes encode_int List.map];lia])
 | rewrite map_merge_semp by reflexivity];reflexivity.
Ltac CreateApart b start count :=
 apply map_join_merge;apply map_disjoint;intros [other off];
 destruct (Pos.eq_dec other b) as [B | B];
 [subst other;destruct (Z_lt_dec off start) as [Low | Low];
 [left;apply V293_encoded_memory_outside;right;left;exact Low |
 destruct (Z_lt_dec off (start+count)) as [Inside | Outside];
 [right;left;CreateOutside | left;apply V293_encoded_memory_outside;right;right;
 cbn [length CreateNext V293_byteval V293_task_selector CreateArg CreateTop CreateOpt CreateBottom CreateId CreateSize CreateExt CreateValue encode_val typelen list_repeat inj_pointer inj_bytes encode_int List.map];lia]] |
 left;apply V293_encoded_memory_outside;left;exact B].


Lemma CreateLiteralReturnEntry : forall p,
 (p=0%nat \/ p=12%nat) ->
 V293_wstate CreateGE CreateLE (CreateEntry p) |= V293_rdy_raw_cells (CreateReturnCells p) Atrue.
Proof.
 intros p PC. destruct PC;subst p;unfold CreateEntry;
 cbn [CreateReturnCells CreateCells CreateFrame CreateOld CreateOuter CreateOuterBase app CreateMemory V293_rdy_raw_cells].
 all: repeat match goal with
 |- V293_wstate _ _ (merge (V293_encoded_memory ?b ?off true ?bytes) _) |= _ =>
 let count:=eval cbn [length CreateNext V293_byteval V293_task_selector CreateArg CreateTop CreateOpt CreateBottom CreateId CreateSize CreateExt encode_val typelen list_repeat inj_pointer inj_bytes encode_int List.map] in (Z.of_nat(length bytes)) in
 eapply V293_wstate_star with (m1:=V293_encoded_memory b off true bytes);
 [CreateApart b off count | split;[apply V293_encoded_memory_mapsto | reflexivity] | ]
 end.
 all: exact I.
Qed.
Lemma CreateLiteralBodyEntry : forall p,
 (p=0%nat \/ p=12%nat) ->
 V293_wstate CreateGE CreateLE (CreateBodyEntry p) |= V293_rdy_raw_cells (CreateBodyCells p) Atrue.
Proof.
 intros p PC. destruct PC;subst p;unfold CreateBodyEntry;
 cbn [CreateBodyCells CreateCells CreateFrame CreateOld CreateOuter CreateOuterBase app CreateMemory V293_rdy_raw_cells].
 all: repeat match goal with
 |- V293_wstate _ _ (merge (V293_encoded_memory ?b ?off true ?bytes) _) |= _ =>
 let count:=eval cbn [length CreateNext V293_byteval V293_task_selector CreateArg CreateTop CreateOpt CreateBottom CreateId CreateSize CreateExt encode_val typelen list_repeat inj_pointer inj_bytes encode_int List.map] in (Z.of_nat(length bytes)) in
 eapply V293_wstate_star with (m1:=V293_encoded_memory b off true bytes);
 [CreateApart b off count | split;[apply V293_encoded_memory_mapsto | reflexivity] | ]
 end.
 all: exact I.
Qed.

Theorem CreateActualMissingStack : forall P p enabled si ci,
 P 900%Z=None -> (p=0%nat \/ p=12%nat) ->
 exists Mf,
 V293_local_steps P CreateStart ((CreateGE,CreateLE,CreateBodyEntry p),(fun _=>false),(enabled,si,ci))
 CreateHookStop ((CreateGE,CreateLE,Mf),(fun _=>false),(enabled,si,ci)) /\
 ~exists C' state',loststep P CreateHookStop ((CreateGE,CreateLE,Mf),(fun _=>false),(enabled,si,ci)) C' state'.
Proof.
 intros P p enabled si ci Missing PC.
 pose proof(CreateLiteralBodyEntry p PC) as Entry.
 assert(Range:(p<13)%nat) by (destruct PC;subst p;lia).
 destruct(V293_OSTaskCreateExt_to_stack_hook P kstop CreateGE CreateLE (CreateBodyEntry p)
 (fun _=>false) (false,nil,nil) (emp:osabst) (spec_done None)
 (V293_rdy_raw_cells (V293_create_bridge_extra 504%positive 509%positive 511%positive 512%positive 513%positive 514%positive
 Vnull CreateBottom CreateId CreateSize CreateExt (Vint32(Int.repr 9))) (V293_rdy_raw_cells CreateFrame Atrue))
 enabled si ci 92%Z 101%Z 97%Z 109%Z 98%Z 501%positive 502%positive 503%positive 510%positive 700%positive p
 (Vint32(Int.repr 23)) 108%Z 900%Z 201%Z 202%Z 203%Z 204%Z 504%positive
 505%positive 506%positive 507%positive 508%positive 700 CreateArg CreateTop CreateOpt
 (sseq (V293_TaskCreateExt_TCB_call 209%Z 901%Z 101%Z 108%Z 205%Z 206%Z 207%Z 208%Z 204%Z) CreateRest))
 as (Mf&Exec&Owned&Decode&Stuck).
 all: try reflexivity.
 - exact Range.
 - unfold Int.max_unsigned,Int.modulus,Int.wordsize;cbn;lia.
 - repeat split;reflexivity.
 - repeat split;reflexivity.
 - rewrite <-V293_raw_cells_append. rewrite <-V293_raw_cells_append. exact Entry.
 - exists Mf. split;[exact Exec |apply Stuck;exact Missing].
Qed.

(* Real port obligations only. No implementation is constructed. *)
Definition CreateHooks P enabled si ci :=
 (forall b1 b2 b3 b4 b5 b6 b7 b8 b9,
  NoDup (V293_tcb_function_blocks b1 b2 b3 b4 b5 b6 b7 b8 b9) ->
  V293_tcb_creation_hook_return P 902%Z 301%positive 8%Z (V293_tcb_first_hook_cont 901%Z 902%Z 903%Z CreateLE (V293_create_TCB_cont 209%Z CreateRest kstop))
   CreateGE (V293_tcb_function_env b1 b2 b3 b4 b5 b6 b7 b8 b9) (fun _=>false) (false,nil,nil) (emp:osabst) (spec_done None) enabled si ci
   (V293_tcb_hook_cells b1 b2 b3 b4 b5 b6 b7 b8 b9 209%positive 510%positive 301%positive 8%Z 12%nat
    (CreateValue true) CreateBottom CreateId CreateSize CreateExt CreateOpt CreateNext (Vptr(700%positive,Int.zero))
    (V293_tcb_creation_tail 301%positive 8%Z 401%positive 402%positive 403%positive 404%positive 302%positive 16%Z false 12%nat Vundef 2%nat 2%nat 7%nat Vnull++(V293_create_caller_cells 501%positive 502%positive 503%positive 12%nat 505%positive 506%positive 507%positive 508%positive 700%Z CreateArg CreateTop CreateOpt 504%positive 509%positive 511%positive 512%positive 513%positive 514%positive (CreateValue true) CreateBottom CreateId CreateSize CreateExt (Vint32(Int.repr 9))++CreateOuter)))) /\
 (forall b1 b2 b3 b4 b5 b6 b7 b8 b9,
  NoDup (V293_tcb_function_blocks b1 b2 b3 b4 b5 b6 b7 b8 b9) ->
  V293_tcb_creation_hook_return P 903%Z 301%positive 8%Z (V293_tcb_second_hook_cont 901%Z 902%Z 903%Z CreateLE (V293_create_TCB_cont 209%Z CreateRest kstop))
   CreateGE (V293_tcb_function_env b1 b2 b3 b4 b5 b6 b7 b8 b9) (fun _=>false) (false,nil,nil) (emp:osabst) (spec_done None) enabled si ci
   (V293_tcb_hook_cells b1 b2 b3 b4 b5 b6 b7 b8 b9 209%positive 510%positive 301%positive 8%Z 12%nat
    (CreateValue true) CreateBottom CreateId CreateSize CreateExt CreateOpt CreateNext (Vptr(301%positive,Int.repr 8%Z))
    (V293_tcb_creation_tail 301%positive 8%Z 401%positive 402%positive 403%positive 404%positive 302%positive 16%Z false 12%nat Vundef 2%nat 2%nat 7%nat Vnull++(V293_create_caller_cells 501%positive 502%positive 503%positive 12%nat 505%positive 506%positive 507%positive 508%positive 700%Z CreateArg CreateTop CreateOpt 504%positive 509%positive 511%positive 512%positive 513%positive 514%positive (CreateValue true) CreateBottom CreateId CreateSize CreateExt (Vint32(Int.repr 9))++CreateOuter)))) /\
 V293_create_stack_return P 900%Z [CreateOpt;CreateTop;CreateArg;V293_task_selector 700%Z]
 (V293_create_stack_cont 108%Z 209%Z 901%Z 101%Z 205%Z 206%Z 207%Z 208%Z 204%Z CreateRest kstop)
 CreateGE CreateLE (fun _=>false) (false,nil,nil) (emp:osabst) (spec_done None) (V293_rdy_raw_cells (V293_create_TCB_support 209%positive 301%positive 8%Z 401%positive 402%positive 403%positive 404%positive 302%positive 16%Z false 12%nat CreateNext (fun _=>Vundef) Vundef 2%nat 2%nat 7%nat Vnull CreateOuter) Atrue) enabled si ci
 (V293_create_bridge_cells 501%positive 502%positive 503%positive 510%positive 12%nat (Vint32 Int.zero) (Vptr(700%positive,Int.zero))
 505%positive 506%positive 507%positive 508%positive 700%Z CreateArg CreateTop CreateOpt 504%positive 509%positive 511%positive 512%positive 513%positive 514%positive Vnull CreateBottom CreateId CreateSize CreateExt (Vint32(Int.repr 9))) (CreateValue true).

Theorem CreateConditionalExecution : forall P enabled si ci,
 P 901%Z=Some(V293_TCBInit_function 902%Z 903%Z) ->
 CreateHooks P enabled si ci ->
 exists Mbridge, exists b1 b2 b3 b4 b5 b6 b7 b8 b9 Mf,
 NoDup (V293_tcb_function_blocks b1 b2 b3 b4 b5 b6 b7 b8 b9) /\
 (forall b, In b (V293_tcb_function_blocks b1 b2 b3 b4 b5 b6 b7 b8 b9) -> fresh Mbridge b) /\
 V293_local_steps P
 (curs(V293_TaskCreateExt_prefix 92%Z 101%Z 97%Z 109%Z 98%Z
 (V293_TaskCreateExt_calls 108%Z 900%Z 201%Z 202%Z 203%Z 204%Z 209%Z 901%Z 101%Z 205%Z 206%Z 207%Z 208%Z CreateRest)),(kenil,kstop))
 ((CreateGE,CreateLE,(CreateBodyEntry 12)),(fun _=>false),(enabled,si,ci))
 (curs(sfexec 901%Z [CreateOpt;CreateExt;CreateSize;CreateId;CreateBottom;(CreateValue true);V293_byteval 12%nat] V293_TCBInit_argument_types),(kenil,V293_create_TCB_cont 209%Z CreateRest kstop))
 ((CreateGE,CreateLE,Mbridge),(fun _=>false),(enabled,si,ci)) /\
 V293_local_steps P
 (curs(V293_TaskCreateExt_prefix 92%Z 101%Z 97%Z 109%Z 98%Z
 (V293_TaskCreateExt_calls 108%Z 900%Z 201%Z 202%Z 203%Z 204%Z 209%Z 901%Z 101%Z 205%Z 206%Z 207%Z 208%Z CreateRest)),(kenil,kstop))
 ((CreateGE,CreateLE,(CreateBodyEntry 12)),(fun _=>false),(enabled,si,ci))
 (curs(sskip(Some(Vint32 Int.zero))),(kenil,kret(kseq V293_TaskCreateExt_occupied kstop)))
 ((CreateGE,CreateLE,Mf),(fun _=>false),(enabled,si,ci)) /\
 (CreateGE,CreateLE,Mf,(fun _=>false),(false,nil,nil),(emp:osabst),(spec_done None)) |= V293_rdy_raw_cells
 (V293_tcb_creation_result 209%positive 510%positive 301%positive 8%Z 401%positive 402%positive 403%positive 404%positive 302%positive 16%Z false 12%nat
 (CreateValue true) CreateBottom CreateId CreateSize CreateExt CreateOpt CreateNext 2%nat 2%nat 7%nat (V293_create_caller_cells 501%positive 502%positive 503%positive 12%nat 505%positive 506%positive 507%positive 508%positive 700%Z CreateArg CreateTop CreateOpt 504%positive 509%positive 511%positive 512%positive 513%positive 514%positive (CreateValue true) CreateBottom CreateId CreateSize CreateExt (Vint32 Int.zero)++CreateOuter)) Atrue /\
 (forall b tp k, In (b,tp) (V293_tcb_function_addresses b1 b2 b3 b4 b5 b6 b7 b8 b9) ->
 (k<typelen tp)%nat -> get Mf (b,Z.of_nat k)=None).
Proof.
 intros P enabled si ci Program Hooks. destruct Hooks as (Hook1&Hook2&Stack).
 pose proof(CreateLiteralBodyEntry 12 (or_intror eq_refl)) as Entry.
 apply (V293_OSTaskCreateExt_success_dispatch_under_hooks
 P kstop CreateGE CreateLE (CreateBodyEntry 12) (fun _=>false) (false,nil,nil) (emp:osabst) (spec_done None)
 enabled si ci 92%Z 101%Z 97%Z 109%Z 98%Z 501%positive
 502%positive 503%positive 510%positive 700%positive 12%nat (Vint32(Int.repr 23)) 108%Z 900%Z 201%Z
 202%Z 203%Z 204%Z 505%positive 506%positive 507%positive 508%positive 700%Z CreateArg
 CreateTop CreateOpt 209%Z 901%Z 205%Z 206%Z 207%Z 208%Z 504%positive
 509%positive 511%positive 512%positive 513%positive 514%positive Vnull CreateBottom CreateId CreateSize
 CreateExt (Vint32(Int.repr 9)) (CreateValue true) 902%Z 903%Z 209%positive 301%positive 8%Z
 401%positive 402%positive 403%positive 404%positive 302%positive 16%Z false CreateNext (fun _=>Vundef)
 Vundef 2%nat 2%nat 7%nat Vnull CreateOuterBase 99%Z 904%Z 520%positive false).
 all: try reflexivity.
 - lia.
 - unfold Int.max_unsigned,Int.modulus,Int.wordsize;cbn;lia.
 - repeat split;reflexivity.
 - repeat split;reflexivity.
 - repeat split;reflexivity.
 - repeat split;reflexivity.
 - exact Program.
 - lia.
 - unfold Int.max_unsigned,Int.modulus,Int.wordsize;cbn;lia.
 - lia.
 - unfold Int.max_unsigned,Int.modulus,Int.wordsize;cbn;lia.
 - lia.
 - lia.
 - lia.
 - exact Hook1.
 - exact Hook2.
 - exact Stack.
 - unfold V293_create_bridge_cells. rewrite <-V293_raw_cells_append.
   exact Entry.
Qed.

Print Assumptions CreateConditionalExecution.
Print Assumptions CreateLiteralBodyEntry.
Print Assumptions CreateActualMissingStack.

Definition CreateResult := (V293_tcb_creation_result 209%positive 510%positive 301%positive 8%Z 401%positive 402%positive 403%positive 404%positive 302%positive 16%Z false 12%nat
 (CreateValue true) CreateBottom CreateId CreateSize CreateExt CreateOpt CreateNext 2%nat 2%nat 7%nat (V293_create_caller_cells 501%positive 502%positive 503%positive 12%nat 505%positive 506%positive 507%positive 508%positive 700%Z CreateArg CreateTop CreateOpt 504%positive 509%positive 511%positive 512%positive 513%positive 514%positive (CreateValue true) CreateBottom CreateId CreateSize CreateExt (Vint32 Int.zero)++CreateOuter)).
Lemma CreateResultValid : forall a tp v, In (a,tp,v) CreateResult -> rule_type_val_match tp v=true.
Proof.
 intros a tp v Member.
 cbn [CreateResult V293_tcb_creation_result V293_tcb_creation_frame V293_tcb_creation_fields
 V293_tcb_init_final_fields V293_pub_cells V293_pub_old_head V293_create_caller_cells
 V293_create_bridge_extra V293_stack_argument_cells CreateOuter V293_prio_row V293_prio_bit
 app firstn skipn tl In] in Member.
 repeat destruct Member as [E | Member];try contradiction;inversion E;subst;reflexivity.
Qed.
Lemma CreateResultReads : forall Mf,
 (CreateGE,CreateLE,Mf,(fun _=>false),(false,nil,nil),(emp:osabst),(spec_done None)) |=
 V293_rdy_raw_cells CreateResult Atrue ->
 forall a tp v, In (a,tp,v) CreateResult -> load tp Mf a=Some v.
Proof.
 intros Mf Owned a tp v Member.
 eapply (V293_rdy_raw_load CreateResult Atrue a tp v
 (CreateGE,CreateLE,Mf,(fun _=>false),(false,nil,nil),(emp:osabst),(spec_done None))).
 - exact Member.
 - eapply CreateResultValid;exact Member.
 - exact Owned.
Qed.
Eval vm_compute in length CreateResult.
Print Assumptions CreateResultReads.
