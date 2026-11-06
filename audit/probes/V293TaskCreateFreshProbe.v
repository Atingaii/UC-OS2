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
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateReturn.
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
Definition CreateCaller : env := set emp 777%Z (601%positive,Tint32).
Definition CreateBody := V293_TaskCreateExt_prefix 92%Z 101%Z 97%Z 109%Z 98%Z
 (V293_TaskCreateExt_calls 108%Z 900%Z 201%Z 202%Z 203%Z 204%Z 209%Z 901%Z 101%Z 205%Z 206%Z 207%Z 208%Z CreateRest).
Definition CreateK := kcall 905%Z CreateBody CreateCaller kstop.
Definition CreateAddresses := V293_create_local_addresses 501%positive 503%positive
 505%positive 506%positive 507%positive 508%positive 504%positive 509%positive
 511%positive 512%positive 513%positive 514%positive.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtFunction.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateCall.
Definition CreateLE : env := V293_create_function_env
 505%positive 506%positive 507%positive 501%positive 511%positive 509%positive
 512%positive 513%positive 508%positive 504%positive 514%positive 503%positive.
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
Fixpoint CreateMemory (cells : list V293_record_cell) : mem :=
 match cells with []=>emp | ((b,off),tp,v)::tail=>
 merge (V293_encoded_memory b off true (encode_val tp v)) (CreateMemory tail) end.
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


(* Independent initial memory: no creation-function local blocks exist yet. *)
Definition CallCells :=
 [((502%positive,0),Tint8,V293_byteval 0);
  ((510%positive,48),Tptr V293_tcb_type,Vnull)]++CreateFrame.
Definition CallMemory := CreateMemory CallCells.
Definition CallFunction := V293_CreateExt_function 92%Z 97%Z 98%Z 99%Z 904%Z 900%Z 901%Z.
Definition CallStart := (curs(sfexec 905%Z
 [CreateOpt;CreateExt;CreateSize;CreateBottom;CreateId;V293_byteval 12;CreateTop;CreateArg;V293_task_selector 700]
 V293_CreateExt_argument_types),(kenil,kstop)).
Definition CallBlocks := V293_create_function_blocks 505%positive 506%positive 507%positive 501%positive 511%positive
 509%positive 512%positive 513%positive 508%positive 504%positive 514%positive 503%positive.
Lemma CallLiteralEntry :
 V293_wstate CreateGE CreateCaller CallMemory |= V293_rdy_raw_cells CallCells Atrue.
Proof.
 unfold CallMemory;
 cbn [CallCells CreateFrame CreateOld CreateOuter CreateOuterBase app CreateMemory V293_rdy_raw_cells].
 repeat match goal with
 |- V293_wstate _ _ (merge (V293_encoded_memory ?b ?off true ?bytes) _) |= _ =>
 let count:=eval cbn [length CreateNext V293_byteval V293_task_selector CreateArg CreateTop CreateOpt CreateBottom CreateId CreateSize CreateExt encode_val typelen list_repeat inj_pointer inj_bytes encode_int List.map] in (Z.of_nat(length bytes)) in
 eapply V293_wstate_star with (m1:=V293_encoded_memory b off true bytes);
 [CreateApart b off count | split;[apply V293_encoded_memory_mapsto | reflexivity] | ]
 end. exact I.
Qed.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateFresh.

Theorem FreshLiteralPrologue : forall P enabled si ci,
 P 905%Z=Some CallFunction ->
 exists btask, exists barg, exists btop, exists bp, exists bi, exists bb, exists bz, exists be, exists bopt, exists bs, exists berr, exists bc, exists Mi,
 NoDup(V293_create_function_blocks btask barg btop bp bi bb bz be bopt bs berr bc) /\
 (forall b, In b(V293_create_function_blocks btask barg btop bp bi bb bz be bopt bs berr bc) -> fresh (CallMemory) b) /\
 (forall a tp v, In(a,tp,v) ([((1%positive,0),Tvoid,Vundef)]) -> ~In(fst a)(V293_create_function_blocks btask barg btop bp bi bb bz be bopt bs berr bc)) /\
 V293_local_steps (P)
 (curs(sfexec (905%Z) [(CreateOpt);(CreateExt);(CreateSize);(CreateBottom);(CreateId);(V293_byteval 12);(CreateTop);(CreateArg);(V293_task_selector 700)] V293_CreateExt_argument_types),(kenil,(kstop)))
 (((CreateGE),(CreateCaller),(CallMemory)),((fun _=>false)),(enabled,si,ci))
 (curs(V293_CreateExt_body (92%Z) (97%Z) (98%Z) (99%Z) (904%Z) (900%Z) (901%Z)),(kenil,kcall (905%Z) (V293_CreateExt_body (92%Z) (97%Z) (98%Z) (99%Z) (904%Z) (900%Z) (901%Z)) (CreateCaller) (kstop)))
 (((CreateGE),V293_create_function_env btask barg btop bp bi bb bz be bopt bs berr bc,Mi),((fun _=>false)),(enabled,si,ci)) /\
 ((CreateGE),V293_create_function_env btask barg btop bp bi bb bz be bopt bs berr bc,Mi,((fun _=>false)),((false,nil,nil)),((emp:osabst)),((spec_done None))) |=
 V293_rdy_raw_cells (V293_create_function_cells btask barg btop bp bi bb bz be bopt bs berr bc (V293_task_selector 700) (CreateArg) (CreateTop) (V293_byteval 12) (CreateId) (CreateBottom) (CreateSize) (CreateExt) (CreateOpt)++(CallCells)) Atrue.
Proof.
 intros P enabled si ci Function.
 eapply(V293_create_fresh_call_prologue P kstop CreateGE CreateCaller CallMemory (fun _=>false)
 (false,nil,nil) (emp:osabst) (spec_done None) enabled si ci 905%Z 92%Z 97%Z 98%Z 99%Z 904%Z 900%Z 901%Z
 (V293_task_selector 700) CreateArg CreateTop (V293_byteval 12) CreateId CreateBottom CreateSize CreateExt CreateOpt CallCells
 [((1%positive,0),Tvoid,Vundef)]).
 - exact Function.
 - repeat split;reflexivity.
 - exact CallLiteralEntry.
Qed.
Print Assumptions FreshLiteralPrologue.

(* Uniform real Hook family is an explicit, undischarged premise. *)
Theorem FreshConditionalExecution : forall P enabled si ci,
 let body:=V293_CreateExt_body 92%Z 97%Z 98%Z 99%Z 904%Z 900%Z 901%Z in
 let ks:=kcall (905%Z) body (CreateCaller) (kstop) in
 let rest:=V293_TaskCreateExt_suffix 92%Z 101%Z 209%Z 99%Z 904%Z in
 let kept:=(((520%positive),0),Tint8,Vint32 Int.zero)::(CreateOuterBase) in
 let live:=V293_tcb_creation_result (209%positive) (510%positive) (301%positive) (8%Z) (401%positive) (402%positive) (403%positive) (404%positive) (302%positive) (16%Z) (false) (12%nat)
 ((CreateValue true)) (CreateBottom) (CreateId) (CreateSize) (CreateExt) (CreateOpt) (CreateNext) (2%nat) (2%nat) (7%nat) ((((502%positive),0),Tint8,V293_byteval 0)::kept) in
 P 905%Z=Some CallFunction ->
 P 901%Z=Some(V293_TCBInit_function 902%Z 903%Z) ->
 (forall btask barg btop bp bi bb bz be bopt bs berr bc,
 let le:=V293_create_function_env btask barg btop bp bi bb bz be bopt bs berr bc in
 NoDup(V293_create_function_blocks btask barg btop bp bi bb bz be bopt bs berr bc) ->
 (forall b, In b(V293_create_function_blocks btask barg btop bp bi bb bz be bopt bs berr bc) -> fresh (CallMemory) b) ->
 (forall a tp v, In(a,tp,v) live -> ~In(fst a)(map fst(V293_create_local_addresses bp bc btask barg btop bopt bs bb bi bz be berr))) ->
 (forall b1 b2 b3 b4 b5 b6 b7 b8 b9,
  NoDup (V293_tcb_function_blocks b1 b2 b3 b4 b5 b6 b7 b8 b9) ->
  V293_tcb_creation_hook_return P (902%Z) (301%positive) (8%Z) (V293_tcb_first_hook_cont 901%Z (902%Z) (903%Z) le (V293_create_TCB_cont 209%Z rest ks))
   (CreateGE) (V293_tcb_function_env b1 b2 b3 b4 b5 b6 b7 b8 b9) ((fun _=>false)) ((false,nil,nil)) ((emp:osabst)) ((spec_done None)) enabled si ci
   (V293_tcb_hook_cells b1 b2 b3 b4 b5 b6 b7 b8 b9 (209%positive) (510%positive) (301%positive) (8%Z) (12%nat)
    ((CreateValue true)) (CreateBottom) (CreateId) (CreateSize) (CreateExt) (CreateOpt) (CreateNext) (Vptr((700%positive),Int.zero))
    (V293_tcb_creation_tail (301%positive) (8%Z) (401%positive) (402%positive) (403%positive) (404%positive) (302%positive) (16%Z) (false) (12%nat) (Vundef) (2%nat) (2%nat) (7%nat) (Vnull)++(V293_create_caller_cells bp (502%positive) bc (12%nat) btask barg btop bopt (700%Z) (CreateArg) (CreateTop) (CreateOpt) bs bb bi bz be berr ((CreateValue true)) (CreateBottom) (CreateId) (CreateSize) (CreateExt) Vundef++kept)))) /\
 (forall b1 b2 b3 b4 b5 b6 b7 b8 b9,
  NoDup (V293_tcb_function_blocks b1 b2 b3 b4 b5 b6 b7 b8 b9) ->
  V293_tcb_creation_hook_return P (903%Z) (301%positive) (8%Z) (V293_tcb_second_hook_cont 901%Z (902%Z) (903%Z) le (V293_create_TCB_cont 209%Z rest ks))
   (CreateGE) (V293_tcb_function_env b1 b2 b3 b4 b5 b6 b7 b8 b9) ((fun _=>false)) ((false,nil,nil)) ((emp:osabst)) ((spec_done None)) enabled si ci
   (V293_tcb_hook_cells b1 b2 b3 b4 b5 b6 b7 b8 b9 (209%positive) (510%positive) (301%positive) (8%Z) (12%nat)
    ((CreateValue true)) (CreateBottom) (CreateId) (CreateSize) (CreateExt) (CreateOpt) (CreateNext) (Vptr((301%positive),Int.repr (8%Z)))
    (V293_tcb_creation_tail (301%positive) (8%Z) (401%positive) (402%positive) (403%positive) (404%positive) (302%positive) (16%Z) (false) (12%nat) (Vundef) (2%nat) (2%nat) (7%nat) (Vnull)++(V293_create_caller_cells bp (502%positive) bc (12%nat) btask barg btop bopt (700%Z) (CreateArg) (CreateTop) (CreateOpt) bs bb bi bz be berr ((CreateValue true)) (CreateBottom) (CreateId) (CreateSize) (CreateExt) Vundef++kept)))) /\
 V293_create_stack_return P 900%Z [(CreateOpt);(CreateTop);(CreateArg);V293_task_selector (700%Z)]
 (V293_create_stack_cont 108%Z 209%Z 901%Z 101%Z 205%Z 206%Z 207%Z 208%Z 204%Z rest ks)
 (CreateGE) le ((fun _=>false)) ((false,nil,nil)) ((emp:osabst)) ((spec_done None)) (V293_rdy_raw_cells (V293_create_TCB_support (209%positive) (301%positive) (8%Z) (401%positive) (402%positive) (403%positive) (404%positive) (302%positive) (16%Z) (false) (12%nat) (CreateNext) ((fun _=>Vundef)) (Vundef) (2%nat) (2%nat) (7%nat) (Vnull) kept) Atrue) enabled si ci
 (V293_create_bridge_cells bp (502%positive) bc (510%positive) (12%nat) (Vint32 Int.zero) (Vptr((700%positive),Int.zero))
 btask barg btop bopt (700%Z) (CreateArg) (CreateTop) (CreateOpt) bs bb bi bz be berr Vundef (CreateBottom) (CreateId) (CreateSize) (CreateExt) Vundef) ((CreateValue true))) ->
 exists btask, exists barg, exists btop, exists bp, exists bi, exists bb, exists bz, exists be, exists bopt, exists bs, exists berr, exists bc,
 let le:=V293_create_function_env btask barg btop bp bi bb bz be bopt bs berr bc in
 let addresses:=V293_create_local_addresses bp bc btask barg btop bopt bs bb bi bz be berr in
 NoDup(V293_create_function_blocks btask barg btop bp bi bb bz be bopt bs berr bc) /\
 (forall b, In b(V293_create_function_blocks btask barg btop bp bi bb bz be bopt bs berr bc) -> fresh (CallMemory) b) /\
 (forall a tp v, In(a,tp,v) live -> ~In(fst a)(map fst addresses)) /\
 exists Mbridge, exists b1, exists b2, exists b3, exists b4, exists b5, exists b6, exists b7, exists b8, exists b9, exists Mf, exists Mr,
 NoDup (V293_tcb_function_blocks b1 b2 b3 b4 b5 b6 b7 b8 b9) /\
 (forall b, In b (V293_tcb_function_blocks b1 b2 b3 b4 b5 b6 b7 b8 b9) -> fresh Mbridge b) /\
 V293_local_steps P
 (curs(sfexec (905%Z) [(CreateOpt);(CreateExt);(CreateSize);(CreateBottom);(CreateId);V293_byteval (12%nat);(CreateTop);(CreateArg);V293_task_selector (700%Z)] V293_CreateExt_argument_types),(kenil,(kstop)))
 (((CreateGE),(CreateCaller),(CallMemory)),((fun _=>false)),(enabled,si,ci))
 (curs(sfexec 901%Z [(CreateOpt);(CreateExt);(CreateSize);(CreateId);(CreateBottom);((CreateValue true));V293_byteval (12%nat)] V293_TCBInit_argument_types),(kenil,V293_create_TCB_cont 209%Z rest ks))
 (((CreateGE),le,Mbridge),((fun _=>false)),(enabled,si,ci)) /\
 V293_local_steps P
 (curs(sfexec (905%Z) [(CreateOpt);(CreateExt);(CreateSize);(CreateBottom);(CreateId);V293_byteval (12%nat);(CreateTop);(CreateArg);V293_task_selector (700%Z)] V293_CreateExt_argument_types),(kenil,(kstop)))
 (((CreateGE),(CreateCaller),(CallMemory)),((fun _=>false)),(enabled,si,ci))
 (curs(sskip(Some(Vint32 Int.zero))),(kenil,(kstop)))
 (((CreateGE),(CreateCaller),Mr),((fun _=>false)),(enabled,si,ci)) /\
 ((CreateGE),(CreateCaller),Mr,((fun _=>false)),((false,nil,nil)),((emp:osabst)),((spec_done None))) |= V293_rdy_raw_cells live Atrue /\
 (forall b tp k, In (b,tp) (V293_tcb_function_addresses b1 b2 b3 b4 b5 b6 b7 b8 b9) ->
 (k<typelen tp)%nat -> get Mr (b,Z.of_nat k)=None) /\
 (forall b tp k, In(b,tp) addresses -> (k<typelen tp)%nat -> get Mr(b,Z.of_nat k)=None) /\
 (forall b i, ~In b(map fst addresses) -> get Mr(b,i)=get Mf(b,i)).
Proof.
 intros P enabled si ci body ks rest kept live Function Program Hooks.
 apply(V293_OSTaskCreateExt_fresh_success_call_under_hooks
 P kstop CreateCaller 905%Z CreateGE CallMemory (fun _=>false) (false,nil,nil) (emp:osabst) (spec_done None)
 enabled si ci 502%positive 510%positive 700%positive 12%nat 700%Z CreateArg CreateTop CreateOpt
 CreateBottom CreateId CreateSize CreateExt (CreateValue true) 902%Z 903%Z 209%positive 301%positive 8%Z
 401%positive 402%positive 403%positive 404%positive 302%positive 16%Z false CreateNext (fun _=>Vundef)
 Vundef 2%nat 2%nat 7%nat Vnull CreateOuterBase 520%positive).
 all: try reflexivity.
 - exact Function.
 - lia.
 - unfold Int.max_unsigned,Int.modulus,Int.wordsize;cbn;lia.
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
 - exact Hooks.
 - exact CallLiteralEntry.
Qed.
Print Assumptions FreshConditionalExecution.
Definition CreateResult := (V293_tcb_creation_result 209%positive 510%positive 301%positive 8%Z 401%positive 402%positive 403%positive 404%positive 302%positive 16%Z false 12%nat
 (CreateValue true) CreateBottom CreateId CreateSize CreateExt CreateOpt CreateNext 2%nat 2%nat 7%nat (((502%positive,0),Tint8,V293_byteval 0)::CreateOuter)).
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
 (CreateGE,CreateCaller,Mf,(fun _=>false),(false,nil,nil),(emp:osabst),(spec_done None)) |=
 V293_rdy_raw_cells CreateResult Atrue ->
 forall a tp v, In (a,tp,v) CreateResult -> load tp Mf a=Some v.
Proof.
 intros Mf Owned a tp v Member.
 eapply (V293_rdy_raw_load CreateResult Atrue a tp v
 (CreateGE,CreateCaller,Mf,(fun _=>false),(false,nil,nil),(emp:osabst),(spec_done None))).
 - exact Member.
 - eapply CreateResultValid;exact Member.
 - exact Owned.
Qed.
Eval vm_compute in length CreateResult.
Print Assumptions CreateResultReads.

