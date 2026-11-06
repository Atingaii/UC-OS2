(* Body-entry to actual stack-call assignment setup. No assumed store,
   intermediate evaluator/execution result, Hook return or allocation result.
   Reserved token remains a representation obligation (ADR0004), not address1. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtPrefix.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope Z_scope.
Definition V293_create_prefix_cells bp bn bc table p cpu slot : list V293_record_cell :=
 [((bp,0),Tint8,V293_byteval p);((bn,0),Tint8,V293_byteval 0);
  ((bc,0),Tint32,cpu);((table,4*Z.of_nat p),Tptr V293_tcb_type,slot)].
Lemma V293_create_priority_guard_false : forall p,
 (p<13)%nat -> Int.ltu(Int.repr 12)(Int.repr(Z.of_nat p))=false.
Proof.
 intros p Range. do 13 (destruct p as [  |  p];[vm_compute;reflexivity | ]). lia.
Qed.

Theorem V293_OSTaskCreateExt_prefix_reserved : forall P ks ge le M ir aux O op R
 enabled si ci table prio nesting cpu reserved bp bn bc bt br p old suffix,
 get le prio=Some(bp,Tint8) -> get le cpu=Some(bc,Tint32) ->
 get le nesting=None -> get ge nesting=Some(bn,Tint8) ->
 get le table=None -> get ge table=Some(bt,Tarray(Tptr V293_tcb_type)13) ->
 get le reserved=None -> get ge reserved=Some(br,Tint8) ->
 (p<13)%nat ->
 (ge,le,M,ir,aux,O,op)  |= V293_rdy_raw_cells
   (V293_create_prefix_cells bp bn bc bt p old Vnull) R ->
 exists Mf,
 V293_local_steps P
 (curs(V293_TaskCreateExt_prefix table prio nesting cpu reserved suffix),(kenil,ks))
 ((ge,le,M),ir,(enabled,si,ci))
 (curs suffix,(kenil,kseq V293_TaskCreateExt_occupied ks))
 ((ge,le,Mf),ir,(enabled,si,ci)) /\
 (ge,le,Mf,ir,aux,O,op)  |= V293_rdy_raw_cells
 (V293_create_prefix_cells bp bn bc bt p (Vint32 Int.zero) (Vptr(br,Int.zero))) R.
Proof.
 intros P ks ge le M ir aux O op R enabled si ci table prio nesting cpu reserved
 bp bn bc bt br p old suffix Bp Bc Nn Gn Nt Gt Nr Gr Range Owned.
 pose proof (V293_byte_type p ltac:(lia)) as PValid.
 assert (CpuType : evaltype(evar cpu)(ge,le,M)=Some Tint32) by V293_rdy_eval.
 assert (CpuAddr : evaladdr(evar cpu)(ge,le,M)=Some(Vptr(bc,Int.repr 0))) by V293_rdy_eval.
 unfold V293_create_prefix_cells in Owned.
 destruct (V293_rdy_assign
  (((bp,0),Tint8,V293_byteval p)::((bn,0),Tint8,V293_byteval 0)::nil)
  (bc,0) Tint32 old [((bt,4*Z.of_nat p),Tptr V293_tcb_type,Vnull)]
  (Vint32 Int.zero) (evar cpu) (econst32 Int.zero) Tint32 R P ge le M ir aux O op)
  as (M1&Init&H1).
 { exact CpuType. } { exact CpuAddr. } { reflexivity. }
 { reflexivity. } { apply eq_int;auto. } { reflexivity. } { reflexivity. } { exact Owned. }
 V293_tcb_init_read H1 0%nat PriorityRead.
 V293_tcb_init_read H1 1%nat NestingRead.
 V293_tcb_init_read H1 3%nat SlotRead.
 assert (PriorityFalse : evalval (ebinop olt (econst32(Int.repr 12))
  (ecast(evar prio) Tint32)) (ge,le,M1)=Some(Vint32 Int.zero)).
 { cbn [evalval evaltype get_lenv get_genv get_mem].
   cbv delta [env var memory.ident Modules.ident] in *. rewrite Bp.
   cbn beta iota. rewrite PriorityRead.
   cbn [cast_eval V293_byteval is_int_type bop_eval cmp_val cmpu].
   rewrite V293_create_priority_guard_false by exact Range. reflexivity. }
 assert (NestingFalse : evalval (ebinop olt (econst32 Int.zero)
  (ecast(evar nesting) Tint32)) (ge,le,M1)=Some(Vint32 Int.zero)) by V293_rdy_eval.
 destruct (V293_rekey_array_address ge le M1 table prio V293_tcb_type bt bp p
  Nt Gt Bp PriorityRead Range) as (SlotType&SlotAddress).
 assert (SlotTrue : evalval (ebinop oeq (earrayelem(evar table)(evar prio))
  (ecast enull (Tptr V293_tcb_type))) (ge,le,M1)=Some(Vint32 Int.one)).
 {
   cbn [evalval evaltype get_lenv get_genv get_mem].
   cbv delta [env var memory.ident Modules.ident] in *. rewrite Nt,Gt,Bp.
   cbn beta iota. rewrite PriorityRead. cbn [load addr_to_addrval V293_byteval].
   rewrite Int.add_zero_l. unfold Int.mul.
   rewrite (Int.unsigned_repr (Z.of_nat p)) by
     (unfold Int.max_unsigned,Int.modulus,Int.wordsize;simpl;lia).
   change (match load (Tptr V293_tcb_type) M1 (bt,Int.unsigned(Int.repr(4*Z.of_nat p))) with
    | Some v => val_eq v Vnull | _ => None end=Some(Vint32 Int.one)).
   rewrite Int.unsigned_repr by (change (0<=4*Z.of_nat p<=4294967295);lia).
   change (load (Tptr V293_tcb_type) M1 (bt,4*Z.of_nat p)=Some Vnull) in SlotRead.
   rewrite SlotRead. reflexivity. }
 destruct (V293_reserved_symbol_eval ge le M1 reserved br Nr Gr) as (TokenType&TokenValue).
 destruct (V293_rdy_assign
  (((bp,0),Tint8,V293_byteval p)::((bn,0),Tint8,V293_byteval 0)::((bc,0),Tint32,Vint32 Int.zero)::nil)
  (bt,4*Z.of_nat p) (Tptr V293_tcb_type) Vnull [] (Vptr(br,Int.zero))
  (earrayelem(evar table)(evar prio)) (V293_task_prio_reserved_expr reserved)
  (Tptr V293_tcb_type) R P ge le M1 ir aux O op)
  as (Mf&Reserve&Final).
 { exact SlotType. } { exact SlotAddress. }
 { apply Int.unsigned_repr. change (0<=4*Z.of_nat p<=4294967295);lia. }
 { exact TokenType. } { apply eq_vptr;do 2 eexists;split;reflexivity. }
 { exact TokenValue. } { reflexivity. } { exact H1. }
 exists Mf. split;[ | exact Final].
 unfold V293_TaskCreateExt_prefix.
 eapply V293_local_cons. { V293_prefix_stmt. }
 eapply V293_local_trans. { apply V293_csteps_local. apply Init. }
 eapply V293_local_cons. { V293_prefix_stmt. }
 eapply V293_local_cons. { V293_prefix_stmt. }
 eapply V293_local_trans. { apply V293_csteps_local.
   eapply V293_entry_if_select with (flag:=false);exact PriorityFalse. }
 eapply V293_local_cons. { V293_prefix_stmt. }
 eapply V293_local_cons. { V293_prefix_stmt. }
 eapply V293_local_cons. { apply encrit_step;reflexivity. }
 eapply V293_local_cons. { V293_prefix_stmt. }
 eapply V293_local_cons. { V293_prefix_stmt. }
 eapply V293_local_trans. { apply V293_csteps_local.
   eapply V293_entry_if_select with (flag:=false);exact NestingFalse. }
 eapply V293_local_cons. { V293_prefix_stmt. }
 eapply V293_local_cons. { V293_prefix_stmt. }
 eapply V293_local_trans. { apply V293_csteps_local.
   eapply V293_entry_if_select with (flag:=true);exact SlotTrue. }
 eapply V293_local_cons. { V293_prefix_stmt. }
 eapply V293_local_trans. { apply V293_csteps_local. apply Reserve. }
 eapply V293_local_cons. { V293_prefix_stmt. }
 eapply V293_local_cons. { V293_prefix_stmt. }
 eapply V293_local_cons. { apply excrit_step;reflexivity. }
 eapply V293_local_cons. { V293_prefix_stmt. }
 apply V293_local_refl.
Qed.

(* Exact stack initializer call-assignment setup. The task function-pointer
   expression is not evaluated here, and the missing Hook is not executed. *)
Theorem V293_OSTaskCreateExt_to_stack_call_setup : forall P ks ge le M ir aux O op R
 enabled si ci table prio nesting cpu reserved bp bn bc bt br p old
 psp hook task arg top opt bpsp rest,
 get le prio=Some(bp,Tint8) -> get le cpu=Some(bc,Tint32) ->
 get le nesting=None -> get ge nesting=Some(bn,Tint8) ->
 get le table=None -> get ge table=Some(bt,Tarray(Tptr V293_tcb_type)13) ->
 get le reserved=None -> get ge reserved=Some(br,Tint8) ->
 get le psp=Some(bpsp,Tptr Tint32) -> (p<13)%nat ->
 (ge,le,M,ir,aux,O,op)  |= V293_rdy_raw_cells
  (V293_create_prefix_cells bp bn bc bt p old Vnull) R ->
 exists Mf,
 V293_local_steps P
 (curs(V293_TaskCreateExt_prefix table prio nesting cpu reserved
   (sseq (V293_TaskCreateExt_stack_call psp hook task arg top opt) rest)),(kenil,ks))
 ((ge,le,M),ir,(enabled,si,ci))
 (curs(scall hook (evar task::evar arg::evar top::evar opt::nil)),
  (kenil,kassignr (evar psp) (Tptr Tint32) (kseq rest (kseq V293_TaskCreateExt_occupied ks))))
 ((ge,le,Mf),ir,(enabled,si,ci)) /\
 (ge,le,Mf,ir,aux,O,op)  |= V293_rdy_raw_cells
  (V293_create_prefix_cells bp bn bc bt p (Vint32 Int.zero) (Vptr(br,Int.zero))) R.
Proof.
 intros P ks ge le M ir aux O op R enabled si ci table prio nesting cpu reserved bp bn bc bt br
 p old psp hook task arg top opt bpsp rest Bp Bc Nn Gn Nt Gt Nr Gr Bs Range Owned.
 destruct (V293_OSTaskCreateExt_prefix_reserved P ks ge le M ir aux O op R
  enabled si ci table prio nesting cpu reserved bp bn bc bt br p old
  (sseq (V293_TaskCreateExt_stack_call psp hook task arg top opt) rest)
  Bp Bc Nn Gn Nt Gt Nr Gr Range Owned) as (Mf&Prefix&Final).
 exists Mf. split;[ | exact Final].
 eapply V293_local_trans;[exact Prefix | ].
 eapply V293_local_cons. { V293_prefix_stmt. }
 eapply V293_local_cons. { apply ostc_step. eapply stmt_step;[reflexivity | ].
   unfold V293_TaskCreateExt_stack_call. apply scalle_step with (t:=Tptr Tint32). V293_rdy_eval. }
 apply V293_local_refl.
Qed.
Print Assumptions V293_OSTaskCreateExt_prefix_reserved.
Print Assumptions V293_OSTaskCreateExt_to_stack_call_setup.
