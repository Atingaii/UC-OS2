(* Actual value-return assignment and seven TCB arguments; body-entry
   composition requires a real Hook return. No missing Hook body is supplied. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtPrefix.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateExtPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293NullBytes.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.framework.proof.cstepLib.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope Z_scope.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtCalls.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitFunction.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateStackEntry.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.

Local Open Scope Z_scope.

Definition V293_create_TCB_env le psp bottom identity size ext err bs bb bi bz be br :=
 get le psp=Some(bs,Tptr Tint32) /\ get le bottom=Some(bb,Tptr Tint32) /\
 get le identity=Some(bi,Tint16) /\ get le size=Some(bz,Tint32) /\
 get le ext=Some(be,Tptr Tvoid) /\ get le err=Some(br,Tint8).
Definition V293_create_bridge_extra bs bb bi bz be br pspv bottom identity size ext errv : list V293_record_cell :=
 [((bs,0),Tptr Tint32,pspv);((bb,0),Tptr Tint32,bottom);((bi,0),Tint16,identity);
  ((bz,0),Tint32,size);((be,0),Tptr Tvoid,ext);((br,0),Tint8,errv)].
Definition V293_create_bridge_cells bp bn bc table p cpu slot btask barg btop bopt target argv topv optv
 bs bb bi bz be br pspv bottom identity size ext errv :=
 (V293_create_prefix_cells bp bn bc table p cpu slot ++
  V293_stack_argument_cells btask barg btop bopt target argv topv optv) ++
 V293_create_bridge_extra bs bb bi bz be br pspv bottom identity size ext errv.

(* A real value-return trace and exact owned-cell/frame preservation. Whole
   memories may differ; no body, no no-op, no assumed implementation. *)
Definition V293_create_stack_return P hook args cont ge le ir aux O op R enabled si ci cells value :=
 forall Mh, (ge,le,Mh,ir,aux,O,op) |= V293_rdy_raw_cells cells R ->
 exists Mr,
 V293_local_steps P (curs(sfexec hook args V293_stack_argument_types),(kenil,cont))
 ((ge,le,Mh),ir,(enabled,si,ci))
 (curs(sskip(Some value)),(kenil,cont)) ((ge,le,Mr),ir,(enabled,si,ci)) /\
 (ge,le,Mr,ir,aux,O,op) |= V293_rdy_raw_cells cells R.

Lemma V293_return_value_assign : forall before a tp old after value lhs R P ks ge le M ir aux O op,
 evaltype lhs (ge,le,M)=Some tp ->
 evaladdr lhs (ge,le,M)=Some(Vptr(fst a,Int.repr(snd a))) ->
 Int.unsigned(Int.repr(snd a))=snd a ->
 rule_type_val_match tp value=true ->
 (ge,le,M,ir,aux,O,op) |= V293_rdy_raw_cells (before++(a,tp,old)::after) R ->
 exists Mf,
 cstepstar P (curs(sskip(Some value)),(kenil,kassignr lhs tp ks)) (ge,le,M)
 (curs(sskip None),(kenil,ks)) (ge,le,Mf) /\
 (ge,le,Mf,ir,aux,O,op) |= V293_rdy_raw_cells (before++(a,tp,value)::after) R.
Proof.
 intros before a tp old after value lhs R P ks ge le M ir aux O op Ty Addr Offset Valid Owned.
 apply V293_rdy_cell_out in Owned.
 destruct(V293_tick_raw_slot_update _ _ _ _ _ _ _ _ _ _ _ _ Valid Owned) as (Mf&Store&Updated).
 exists Mf. split.
 - eapply c_stepstarn. { eapply stmt_step;[reflexivity | apply sassignrv_step]. }
   eapply V293_cstepstar_trans.
   { apply V293_expr_steps. apply evalval_imply_estepstar. eapply evaladdr_val_eq;[exact Ty |exact Addr]. }
   eapply c_stepstarn. { eapply stmt_step;[reflexivity | ]. eapply sassignend_step;try reflexivity.
     unfold addrval_to_addr. rewrite Offset. destruct a;exact Store. }
   apply c_stepstar0.
 - apply V293_rdy_cell_in. unfold V293_owned_record_cell in Updated.
   apply astar_assoc_elim in Updated. apply astar_l_apure_elim in Updated.
   destruct Updated as [_ Updated]. exact Updated.
Qed.

Lemma V293_create_seven_arguments : forall P ks ge le M tcb a b c d e f g va vb vc vd ve vf vg,
 evaltype(evar a)(ge,le,M)=Some Tint8 -> evalval(evar a)(ge,le,M)=Some va ->
 evaltype(evar b)(ge,le,M)=Some (Tptr Tint32) -> evalval(evar b)(ge,le,M)=Some vb ->
 evaltype(evar c)(ge,le,M)=Some (Tptr Tint32) -> evalval(evar c)(ge,le,M)=Some vc ->
 evaltype(evar d)(ge,le,M)=Some Tint16 -> evalval(evar d)(ge,le,M)=Some vd ->
 evaltype(evar e)(ge,le,M)=Some Tint32 -> evalval(evar e)(ge,le,M)=Some ve ->
 evaltype(evar f)(ge,le,M)=Some (Tptr Tvoid) -> evalval(evar f)(ge,le,M)=Some vf ->
 evaltype(evar g)(ge,le,M)=Some Tint16 -> evalval(evar g)(ge,le,M)=Some vg ->
 cstepstar P
 (curs(scall tcb [evar a;evar b;evar c;evar d;evar e;evar f;evar g]),(kenil,ks)) (ge,le,M)
 (curs(sfexec tcb [vg;vf;ve;vd;vc;vb;va] V293_TCBInit_argument_types),(kenil,ks)) (ge,le,M).
Proof.
 intros P ks ge le M tcb a b c d e f g va vb vc vd ve vf vg TypeA ValA TypeB ValB TypeC ValC TypeD ValD TypeE ValE TypeF ValF TypeG ValG.
 eapply c_stepstarn. { eapply stmt_step;[reflexivity | eapply spcall_step;exact TypeA]. }
 eapply V293_cstepstar_trans. { apply V293_expr_steps. apply evalval_imply_estepstar. exact ValA. }
 eapply c_stepstarn. { eapply stmt_step;[reflexivity | eapply svfeval_step;exact TypeB]. }
 eapply V293_cstepstar_trans. { apply V293_expr_steps. apply evalval_imply_estepstar. exact ValB. }
 eapply c_stepstarn. { eapply stmt_step;[reflexivity | eapply svfeval_step;exact TypeC]. }
 eapply V293_cstepstar_trans. { apply V293_expr_steps. apply evalval_imply_estepstar. exact ValC. }
 eapply c_stepstarn. { eapply stmt_step;[reflexivity | eapply svfeval_step;exact TypeD]. }
 eapply V293_cstepstar_trans. { apply V293_expr_steps. apply evalval_imply_estepstar. exact ValD. }
 eapply c_stepstarn. { eapply stmt_step;[reflexivity | eapply svfeval_step;exact TypeE]. }
 eapply V293_cstepstar_trans. { apply V293_expr_steps. apply evalval_imply_estepstar. exact ValE. }
 eapply c_stepstarn. { eapply stmt_step;[reflexivity | eapply svfeval_step;exact TypeF]. }
 eapply V293_cstepstar_trans. { apply V293_expr_steps. apply evalval_imply_estepstar. exact ValF. }
 eapply c_stepstarn. { eapply stmt_step;[reflexivity | eapply svfeval_step;exact TypeG]. }
 eapply V293_cstepstar_trans. { apply V293_expr_steps. apply evalval_imply_estepstar. exact ValG. }
 eapply c_stepstarn. { eapply stmt_step;[reflexivity | apply svfevalnil_step]. }
 apply c_stepstar0.
Qed.

(* Unconditional AFTER-return anchor: no claim that a missing Hook reaches it. *)
Theorem V293_OSTaskCreateExt_after_stack_to_TCB : forall P ks ge le M ir aux O op R enabled si ci
 psp err tcb prio bottom identity size ext opt rest bp bn bc table reserve p
 btask barg btop bopt target argv topv optv bs bb bi bz be br oldpsp bottomv idv sizev extv olderr value,
 get le prio=Some(bp,Tint8) -> (p<13)%nat ->
 get le opt=Some(bopt,Tint16) ->
 V293_create_TCB_env le psp bottom identity size ext err bs bb bi bz be br ->
 V293_tcb_init_values_valid value bottomv idv sizev extv optv ->
 (ge,le,M,ir,aux,O,op) |= V293_rdy_raw_cells
 (V293_create_bridge_cells bp bn bc table p (Vint32 Int.zero) (Vptr(reserve,Int.zero))
  btask barg btop bopt target argv topv optv bs bb bi bz be br oldpsp bottomv idv sizev extv olderr) R ->
 exists Mf,
 V293_local_steps P (curs(sskip(Some value)),
 (kenil,V293_create_stack_cont psp err tcb prio bottom identity size ext opt rest ks))
 ((ge,le,M),ir,(enabled,si,ci))
 (curs(sfexec tcb [optv;extv;sizev;idv;bottomv;value;V293_byteval p] V293_TCBInit_argument_types),
 (kenil,V293_create_TCB_cont err rest ks)) ((ge,le,Mf),ir,(enabled,si,ci)) /\
 (ge,le,Mf,ir,aux,O,op) |= V293_rdy_raw_cells
 (V293_create_bridge_cells bp bn bc table p (Vint32 Int.zero) (Vptr(reserve,Int.zero))
  btask barg btop bopt target argv topv optv bs bb bi bz be br value bottomv idv sizev extv olderr) R.
Proof.
 intros P ks ge le M ir aux O op R enabled si ci psp err tcb prio bottom identity size ext opt rest
 bp bn bc table reserve p btask barg btop bopt target argv topv optv bs bb bi bz be br oldpsp bottomv idv sizev extv olderr value
 Prio Range Opt Env Valid Owned.
 destruct Env as (Psp&Bottom&Identity&Size&Ext&Err).
 destruct Valid as (ValueValid&BottomValid&IdValid&SizeValid&ExtValid&OptValid).
 assert (Ty : evaltype(evar psp)(ge,le,M)=Some(Tptr Tint32)) by V293_rdy_eval.
 assert (Addr : evaladdr(evar psp)(ge,le,M)=Some(Vptr(bs,Int.repr 0))) by V293_rdy_eval.
 unfold V293_create_bridge_cells,V293_create_bridge_extra in Owned.
 destruct(V293_return_value_assign
  (V293_create_prefix_cells bp bn bc table p (Vint32 Int.zero) (Vptr(reserve,Int.zero))++
   V293_stack_argument_cells btask barg btop bopt target argv topv optv)
  (bs,0) (Tptr Tint32) oldpsp
  (((bb,0),Tptr Tint32,bottomv)::((bi,0),Tint16,idv)::((bz,0),Tint32,sizev)::
   ((be,0),Tptr Tvoid,extv)::((br,0),Tint8,olderr)::nil)
  value (evar psp) R P
  (kseq (sseq (V293_TaskCreateExt_TCB_call err tcb prio psp bottom identity size ext opt) rest)
   (kseq V293_TaskCreateExt_occupied ks)) ge le M ir aux O op Ty Addr eq_refl ValueValid Owned)
 as (Mf&Assign&Final).
 pose proof (V293_byte_type p ltac:(lia)) as PrioValid.
 V293_tcb_init_read Final 0%nat PrioRead.
 V293_tcb_init_read Final 7%nat OptRead.
 V293_tcb_init_read Final 8%nat PspRead.
 V293_tcb_init_read Final 9%nat BottomRead.
 V293_tcb_init_read Final 10%nat IdRead.
 V293_tcb_init_read Final 11%nat SizeRead.
 V293_tcb_init_read Final 12%nat ExtRead.
 assert (TypeA : evaltype(evar prio)(ge,le,Mf)=Some Tint8) by V293_rdy_eval.
 assert (ValA : evalval(evar prio)(ge,le,Mf)=Some(V293_byteval p)) by V293_rdy_eval.
 assert (TypeB : evaltype(evar psp)(ge,le,Mf)=Some(Tptr Tint32)) by V293_rdy_eval.
 assert (ValB : evalval(evar psp)(ge,le,Mf)=Some value) by V293_rdy_eval.
 assert (TypeC : evaltype(evar bottom)(ge,le,Mf)=Some(Tptr Tint32)) by V293_rdy_eval.
 assert (ValC : evalval(evar bottom)(ge,le,Mf)=Some bottomv) by V293_rdy_eval.
 assert (TypeD : evaltype(evar identity)(ge,le,Mf)=Some Tint16) by V293_rdy_eval.
 assert (ValD : evalval(evar identity)(ge,le,Mf)=Some idv) by V293_rdy_eval.
 assert (TypeE : evaltype(evar size)(ge,le,Mf)=Some Tint32) by V293_rdy_eval.
 assert (ValE : evalval(evar size)(ge,le,Mf)=Some sizev) by V293_rdy_eval.
 assert (TypeF : evaltype(evar ext)(ge,le,Mf)=Some(Tptr Tvoid)) by V293_rdy_eval.
 assert (ValF : evalval(evar ext)(ge,le,Mf)=Some extv) by V293_rdy_eval.
 assert (TypeG : evaltype(evar opt)(ge,le,Mf)=Some Tint16) by V293_rdy_eval.
 assert (ValG : evalval(evar opt)(ge,le,Mf)=Some optv) by V293_rdy_eval.
 exists Mf. split.
 - unfold V293_create_stack_cont,V293_create_TCB_cont,V293_TaskCreateExt_TCB_call.
   eapply V293_local_trans;[apply V293_csteps_local;exact Assign | ].
   eapply V293_local_cons. { apply ostc_step. eapply stmt_step;[reflexivity | apply sskip_step]. }
   eapply V293_local_cons. { apply ostc_step. eapply stmt_step;[reflexivity | apply sseq_step]. }
   eapply V293_local_cons. { apply ostc_step. eapply stmt_step;[reflexivity | apply scalle_step with (t:=Tint8);V293_rdy_eval]. }
   apply V293_csteps_local. eapply V293_create_seven_arguments;assumption.
 - exact Final.
Qed.

(* Stable body-entry interface. The only execution supplied by the caller is
   the REAL missing-port return obligation, not the psp store or TCB call. *)
Theorem V293_OSTaskCreateExt_to_TCB_under_stack_return : forall P ks ge le M ir aux O op R
 enabled si ci table prio nesting cpu reserved bp bn bc bt br p old
 psp hook task arg top opt btask barg btop bopt target argv topv optv
 err tcb bottom identity size ext bs bb bi bz be berr oldpsp bottomv idv sizev extv olderr value rest,
 get le prio=Some(bp,Tint8) -> get le cpu=Some(bc,Tint32) ->
 get le nesting=None -> get ge nesting=Some(bn,Tint8) ->
 get le table=None -> get ge table=Some(bt,Tarray(Tptr V293_tcb_type)13) ->
 get le reserved=None -> get ge reserved=Some(br,Tint8) ->
 (p<13)%nat -> 0<=target<=Int.max_unsigned ->
 V293_stack_argument_env le task arg top opt btask barg btop bopt ->
 V293_stack_argument_valid argv topv optv ->
 V293_create_TCB_env le psp bottom identity size ext err bs bb bi bz be berr ->
 V293_tcb_init_values_valid value bottomv idv sizev extv optv ->
 V293_create_stack_return P hook [optv;topv;argv;V293_task_selector target]
 (V293_create_stack_cont psp err tcb prio bottom identity size ext opt rest ks)
 ge le ir aux O op R enabled si ci
 (V293_create_bridge_cells bp bn bc bt p (Vint32 Int.zero) (Vptr(br,Int.zero))
 btask barg btop bopt target argv topv optv bs bb bi bz be berr oldpsp bottomv idv sizev extv olderr) value ->
 (ge,le,M,ir,aux,O,op) |= V293_rdy_raw_cells
 (V293_create_bridge_cells bp bn bc bt p old Vnull
 btask barg btop bopt target argv topv optv bs bb bi bz be berr oldpsp bottomv idv sizev extv olderr) R ->
 exists Mf,
 V293_local_steps P
 (curs(V293_TaskCreateExt_prefix table prio nesting cpu reserved
 (V293_TaskCreateExt_calls psp hook task arg top opt err tcb prio bottom identity size ext rest)),(kenil,ks))
 ((ge,le,M),ir,(enabled,si,ci))
 (curs(sfexec tcb [optv;extv;sizev;idv;bottomv;value;V293_byteval p] V293_TCBInit_argument_types),
 (kenil,V293_create_TCB_cont err rest ks)) ((ge,le,Mf),ir,(enabled,si,ci)) /\
 (ge,le,Mf,ir,aux,O,op) |= V293_rdy_raw_cells
 (V293_create_bridge_cells bp bn bc bt p (Vint32 Int.zero) (Vptr(br,Int.zero))
 btask barg btop bopt target argv topv optv bs bb bi bz be berr value bottomv idv sizev extv olderr) R.
Proof.
 intros P ks ge le M ir aux O op R enabled si ci table prio nesting cpu reserved bp bn bc bt br p old
 psp hook task arg top opt btask barg btop bopt target argv topv optv
 err tcb bottom identity size ext bs bb bi bz be berr oldpsp bottomv idv sizev extv olderr value rest
 Bp Bc Nn Gn Nt Gt Nr Gr Range Target ArgEnv ArgValid Env Valid HookReturn Owned.
 pose proof (proj1 Env) as Psp.
 unfold V293_create_bridge_cells in Owned. rewrite V293_raw_cells_append in Owned.
 destruct(V293_OSTaskCreateExt_to_stack_hook P ks ge le M ir aux O op
 (V293_rdy_raw_cells (V293_create_bridge_extra bs bb bi bz be berr oldpsp bottomv idv sizev extv olderr) R)
 enabled si ci table prio nesting cpu reserved bp bn bc bt br p old
 psp hook task arg top opt bs btask barg btop bopt target argv topv optv
 (sseq (V293_TaskCreateExt_TCB_call err tcb prio psp bottom identity size ext opt) rest)
 Bp Bc Nn Gn Nt Gt Nr Gr Psp Range Target ArgEnv ArgValid Owned)
 as (Mh&Prefix&AtHook&Decode&Missing).
 rewrite <-V293_raw_cells_append in AtHook.
 destruct(HookReturn Mh AtHook) as (Mr&Returned&AfterHook).
 pose proof (proj2 (proj2 (proj2 ArgEnv))) as Opt.
 destruct(V293_OSTaskCreateExt_after_stack_to_TCB P ks ge le Mr ir aux O op R enabled si ci
 psp err tcb prio bottom identity size ext opt rest bp bn bc bt br p
 btask barg btop bopt target argv topv optv bs bb bi bz be berr oldpsp bottomv idv sizev extv olderr value
 Bp Range Opt Env Valid AfterHook) as (Mf&Bridge&Final).
 exists Mf. split;[ |exact Final].
 eapply V293_local_trans;[exact Prefix | ].
 eapply V293_local_trans;[exact Returned |exact Bridge].
Qed.

Theorem V293_missing_stack_hook_cannot_return : forall P hook args types ks m ir au value ks' state',
 P hook=None ->
 ~V293_local_steps P (curs(sfexec hook args types),(kenil,ks)) (m,ir,au)
    (curs(sskip(Some value)),(kenil,ks')) state'.
Proof.
 intros P hook args types ks m ir au value ks' state' Missing Run.
 unfold V293_local_steps in Run.
 inversion Run as [ | y z Step Rest];subst.
 destruct y as [C1 state1]. cbn in Step.
 apply (V293_missing_port_has_no_step P hook args types ks m ir au Missing).
 exists C1. exists state1. exact Step.
Qed.
Print Assumptions V293_return_value_assign.
Print Assumptions V293_create_seven_arguments.
Print Assumptions V293_OSTaskCreateExt_after_stack_to_TCB.
Print Assumptions V293_OSTaskCreateExt_to_TCB_under_stack_return.
Print Assumptions V293_missing_stack_hook_cannot_return.
