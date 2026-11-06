(* Continuous normalized-prefix execution. No intermediate-memory, evaluator,
   call-result or port-contract premise. Not an execution of raw port calls. *)
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293NullBytes.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBList.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import Coq.Lists.List Lia.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInit.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Import ListNotations.
Local Open Scope nat_scope.
Definition V293_tcb_prefix_inputs bc bp bs bb bi bz be bo pc p top bottom identity size ext options :=
  ((bc,0%Z),Tptr V293_tcb_type,pc)::
  tl (V293_tcb_init_input_cells bc bp bs bb bi bz be bo bc 0%Z p top bottom identity size ext options).
Definition V293_tcb_prefix_links bg bt base head next : list V293_record_cell :=
  [((bg,0%Z),Tptr V293_tcb_type,head);((bt,(base+20)%Z),Tcom_ptr 410%Z,next)].
Ltac V293_prefix_stmt := apply ostc_step; eapply stmt_step; [reflexivity|constructor].

Theorem V293_OS_TCBInit_prefix_execution : forall P ks ge le M ir aux O op R enabled si ci
  free ptcb prio ptos pbos id stk_size pext opt bc bp bs bb bi bz be bo bg bt base
  p top bottom identity size ext options pc next old suffix,
  p<13 -> (0<=base)%Z -> (base+55<=Int.max_unsigned)%Z ->
  get le free=None -> get ge free=Some (bg,Tptr V293_tcb_type) ->
  V293_tcb_init_env le ptcb prio ptos pbos id stk_size pext opt bc bp bs bb bi bz be bo ->
  V293_tcb_init_values_valid top bottom identity size ext options ->
  rule_type_val_match (Tptr V293_tcb_type) next=true ->
  (ge,le,M,ir,aux,O,op) |= V293_rdy_raw_cells
    (V293_tcb_init_old_fields bt base old ++
     V293_tcb_prefix_inputs bc bp bs bb bi bz be bo pc p top bottom identity size ext options ++
     V293_tcb_prefix_links bg bt base (Vptr (bt,Int.repr base)) next) R ->
  exists Mf,
    V293_local_steps P
      (curs (V293_TCBInit_prefix free ptcb prio ptos pbos id stk_size pext opt suffix),(kenil,ks))
      ((ge,le,M),ir,(enabled,si,ci))
      (curs suffix,(kenil,kseq V293_TCBInit_empty ks))
      ((ge,le,Mf),ir,(enabled,si,ci)) /\
    (ge,le,Mf,ir,aux,O,op) |= V293_rdy_raw_cells
      (V293_tcb_init_final_fields bt base p top bottom identity size ext options ++
       V293_tcb_init_input_cells bc bp bs bb bi bz be bo bt base p top bottom identity size ext options ++
       V293_tcb_prefix_links bg bt base next next) R.
Proof.
  intros P ks ge le M ir aux O op R enabled si ci free ptcb prio ptos pbos id stk_size pext opt
    bc bp bs bb bi bz be bo bg bt base p top bottom identity size ext options pc next old suffix
    Range Base Bound FreeLocal FreeGlobal Env Valid Next Owned.
  pose proof Env as Bindings. destruct Bindings as (Bc & Bp & Bs & Bb & Bi & Bz & Be & Bo).
  unfold V293_tcb_init_old_fields,V293_tcb_prefix_inputs,V293_tcb_init_input_cells,
    V293_tcb_prefix_links in Owned. cbn [app tl] in Owned.
  assert (PcTy : evaltype (evar ptcb) (ge,le,M)=Some (Tptr V293_tcb_type)) by V293_rdy_eval.
  assert (PcAddr : evaladdr (evar ptcb) (ge,le,M)=Some (Vptr (bc,Int.repr 0))) by V293_rdy_eval.
  V293_tcb_init_read Owned 26 Head.
  V293_tcb_init_write P Owned 18 (evar ptcb) (evar free) (Tptr V293_tcb_type)
    (Vptr (bt,Int.repr base)) M1 ReadStep H1.
  V293_tcb_init_read H1 18 PRead.
  V293_tcb_init_read H1 27 NextRead.
  destruct (V293_tcb_init_field_address ge le M1 ptcb bc bt base 7%Z 20%Z (Tcom_ptr 410%Z)
    Bc PRead ltac:(reflexivity) ltac:(reflexivity) Base ltac:(lia) ltac:(lia)) as [NT NA].
  assert (NV : evalval (efield (ederef (evar ptcb)) 7%Z) (ge,le,M1)=Some next).
  {
    cbn [evaladdr evalval evaltype get_lenv get_genv get_mem]. cbv delta [env var memory.ident Modules.ident] in *. rewrite Bc.
    cbn beta iota. rewrite PRead. unfold getoff.
    cbn [evaltype get_lenv get_genv]. cbv delta [env var memory.ident Modules.ident] in *. rewrite Bc.
    cbn [V293_tcb_type V293_tcb_fields field_offset addrval_to_addr].
    rewrite Int.repr_unsigned. unfold Int.add.
    rewrite (Int.unsigned_repr base) by lia.
    change (load (Tcom_ptr 410%Z) M1 (bt,Int.unsigned (Int.repr (base+20)))=Some next).
    rewrite Int.unsigned_repr by lia. exact NextRead. }
  assert (PopMatch : assign_type_match (Tptr V293_tcb_type) (Tcom_ptr 410%Z)).
  { apply eq_vcomptr. split;left;eexists;reflexivity. }
  assert (FreeTy : evaltype (evar free) (ge,le,M1)=Some (Tptr V293_tcb_type)) by V293_rdy_eval.
  assert (FreeAddr : evaladdr (evar free) (ge,le,M1)=Some (Vptr (bg,Int.repr 0))) by V293_rdy_eval.
  destruct (V293_rdy_assign
    (V293_tcb_init_old_fields bt base old ++
     V293_tcb_init_input_cells bc bp bs bb bi bz be bo bt base p top bottom identity size ext options)
    (bg,0%Z) (Tptr V293_tcb_type) (Vptr (bt,Int.repr base))
    [((bt,(base+20)%Z),Tcom_ptr 410%Z,next)] next
    (evar free) (efield (ederef (evar ptcb)) 7%Z) (Tcom_ptr 410%Z) R P ge le M1 ir aux O op
    FreeTy FreeAddr ltac:(reflexivity) NT PopMatch NV Next H1) as (M2 & PopStep & H2).
  assert (Guard : evalval (eunop oppsite (V293_task_prio_null_test (evar ptcb))) (ge,le,M1)=Some (Vint32 Int.one)).
  { cbn [V293_task_prio_null_test evalval evaltype get_lenv get_genv get_mem]. cbv delta [env var memory.ident Modules.ident] in *. rewrite Bc.
    cbn beta iota. rewrite PRead. reflexivity. }
  assert (Start : (ge,le,M2,ir,aux,O,op) |= V293_rdy_raw_cells
    (V293_tcb_init_old_fields bt base old ++
     V293_tcb_init_input_cells bc bp bs bb bi bz be bo bt base p top bottom identity size ext options)
    (V293_rdy_raw_cells (V293_tcb_prefix_links bg bt base next next) R)).
  { rewrite <- V293_raw_cells_append. exact H2. }
  destruct (V293_OS_TCBInit_fields_execution P (kseq suffix (kseq V293_TCBInit_empty ks)) ge le M2
    ir aux O op (V293_rdy_raw_cells (V293_tcb_prefix_links bg bt base next next) R)
    ptcb prio ptos pbos id stk_size pext opt bc bp bs bb bi bz be bo bt base
    p top bottom identity size ext options old Range Base Bound Env Valid Start) as (Mf & Fields & Final).
  exists Mf. split.
  - unfold V293_TCBInit_prefix.
    eapply V293_local_cons. { V293_prefix_stmt. }
    eapply V293_local_cons. { apply encrit_step;reflexivity. }
    eapply V293_local_cons. { V293_prefix_stmt. }
    eapply V293_local_cons. { V293_prefix_stmt. }
    eapply V293_local_trans. { apply V293_csteps_local. apply ReadStep. }
    eapply V293_local_cons. { V293_prefix_stmt. }
    eapply V293_local_cons. { V293_prefix_stmt. }
    eapply V293_local_trans.
    { apply V293_csteps_local. eapply V293_entry_if_select with (flag:=true). exact Guard. }
    eapply V293_local_cons. { V293_prefix_stmt. }
    eapply V293_local_trans. { apply V293_csteps_local. apply PopStep. }
    eapply V293_local_cons. { V293_prefix_stmt. }
    eapply V293_local_cons. { V293_prefix_stmt. }
    eapply V293_local_cons. { apply excrit_step;reflexivity. }
    eapply V293_local_cons. { V293_prefix_stmt. }
    eapply V293_local_cons. { V293_prefix_stmt. }
    eapply V293_local_trans. { apply V293_csteps_local. exact Fields. }
    eapply V293_local_cons. { V293_prefix_stmt. }
    apply V293_local_refl.
  - rewrite <- V293_raw_cells_append in Final. exact Final.
Qed.

Definition V293_tcb_empty_cells bc bg pc : list V293_record_cell :=
  [((bc,0%Z),Tptr V293_tcb_type,pc);((bg,0%Z),Tptr V293_tcb_type,Vnull)].

(* Empty list requires NO TCB allocation/field/next resource. Stop just before
   return66, not an assumed successful return and not a freed caller state. *)
Theorem V293_OS_TCBInit_empty_prefix_execution : forall P ks ge le M ir aux O op R enabled si ci
  free ptcb prio ptos pbos id stk_size pext opt bc bg pc suffix,
  get le free=None -> get ge free=Some (bg,Tptr V293_tcb_type) ->
  get le ptcb=Some (bc,Tptr V293_tcb_type) ->
  (ge,le,M,ir,aux,O,op) |= V293_rdy_raw_cells
    (V293_tcb_empty_cells bc bg pc) R ->
  exists Mf,
    V293_local_steps P
      (curs (V293_TCBInit_prefix free ptcb prio ptos pbos id stk_size pext opt suffix),(kenil,ks))
      ((ge,le,M),ir,(enabled,si,ci))
      (curs (srete (econst32 (Int.repr 66))),(kenil,ks))
      ((ge,le,Mf),ir,(enabled,si,ci)) /\
    (ge,le,Mf,ir,aux,O,op) |= V293_rdy_raw_cells
      (V293_tcb_empty_cells bc bg Vnull) R.
Proof.
  intros P ks ge le M ir aux O op R enabled si ci free ptcb prio ptos pbos id stk_size pext opt
    bc bg pc suffix FreeLocal FreeGlobal Bc Owned.
  assert (PcTy : evaltype (evar ptcb) (ge,le,M)=Some (Tptr V293_tcb_type)) by V293_rdy_eval.
  assert (PcAddr : evaladdr (evar ptcb) (ge,le,M)=Some (Vptr (bc,Int.repr 0))) by V293_rdy_eval.
  unfold V293_tcb_empty_cells in Owned.
  V293_tcb_init_read Owned 1 Head.
  destruct (V293_rdy_assign nil (bc,0%Z) (Tptr V293_tcb_type) pc
    (tl (V293_tcb_empty_cells bc bg pc)) Vnull (evar ptcb) (evar free)
    (Tptr V293_tcb_type) R P ge le M ir aux O op PcTy PcAddr ltac:(reflexivity)
    ltac:(V293_rdy_eval) ltac:(apply eq_vptr;do 2 eexists;split;reflexivity)
    ltac:(V293_rdy_eval) ltac:(reflexivity) Owned) as (Mf & ReadStep & Final).
  V293_tcb_init_read Final 0 PRead.
  assert (Guard : evalval (eunop oppsite (V293_task_prio_null_test (evar ptcb)))
    (ge,le,Mf)=Some (Vint32 Int.zero)).
  { cbn [V293_task_prio_null_test evalval evaltype get_lenv get_genv get_mem].
    cbv delta [env var memory.ident Modules.ident] in *. rewrite Bc.
    cbn beta iota. rewrite PRead. reflexivity. }
  exists Mf. split;[ | exact Final].
  unfold V293_TCBInit_prefix.
  eapply V293_local_cons. { V293_prefix_stmt. }
  eapply V293_local_cons. { apply encrit_step;reflexivity. }
  eapply V293_local_cons. { V293_prefix_stmt. }
  eapply V293_local_cons. { V293_prefix_stmt. }
  eapply V293_local_trans. { apply V293_csteps_local. apply ReadStep. }
  eapply V293_local_cons. { V293_prefix_stmt. }
  eapply V293_local_cons. { V293_prefix_stmt. }
  eapply V293_local_trans.
  { apply V293_csteps_local. eapply V293_entry_if_select with (flag:=false). exact Guard. }
  eapply V293_local_cons. { V293_prefix_stmt. }
  unfold V293_TCBInit_empty.
  eapply V293_local_cons. { V293_prefix_stmt. }
  eapply V293_local_cons. { apply excrit_step;reflexivity. }
  eapply V293_local_cons. { V293_prefix_stmt. }
  apply V293_local_refl.
Qed.
