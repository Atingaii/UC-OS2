(* Same program unit and shared invariant; replace only the Enter contract.
   This function environment does not establish a continuous ISR trace. *)
Require Import CertiOS.certiucos.v293.proofs.V293InterruptFunctionEnvironment.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStoragePrefix.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyDynamic.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyEnter.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBoundarySwitch.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptExitEnvironment.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedJoint.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedShared.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitch.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyStorageInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.code.V293OSIntEnter.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.framework.proof.toptheorem.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope nat_scope.

Section ReadyInterruptEnvironment.
Variables unmap group rows high table target current counter running nesting lock saved:var.
Variables bt bg br bh bp bo bc bk brun bn bl:block.
Variable rest:list(addr*type).
Variable extra:asrt.
Variable EG:GoodFunAsrt extra.
Let tp:=V293_tcb_type.
Let Inv0:=V293_ready_dynamic_exit_inv target bt bg br bh bp bc bk brun bn bl rest.
Let Hli:=V293_switch_li_good.
Definition V293_ready_irq_prefix:list(addr*type):=
 ((bk,0%Z),Tint32)::((bh,0%Z),Tint8)::((bc,0%Z),Tint8)::
 V293_array_cells bt 0 1 Tint8(length V293_ready_table).
Definition V293_ready_irq_suffix:list(addr*type):=((bl,0%Z),Tint8)::rest.
Lemma V293_ready_irq_inv_layout :
 V293_ready_storage_inv br bg bp target tp
 (V293_ready_irq_prefix++[((brun,0%Z),Tint8);((bn,0%Z),Tint8)]++V293_ready_irq_suffix)=Inv0.
Proof.
 unfold V293_ready_irq_prefix,V293_ready_irq_suffix,Inv0,
 V293_ready_dynamic_exit_inv,V293_ready_builder_inv.
 reflexivity.
Qed.
Let efp:=V293_enter_ready_fpre br bg bp brun bn running nesting target tp
 V293_ready_irq_prefix V293_ready_irq_suffix.
Let efq:=V293_enter_ready_fpost br bg bp brun bn running nesting target tp
 V293_ready_irq_prefix V293_ready_irq_suffix.
Let xfp:=V293_ready_dynamic_exit_fpre unmap group rows high table target current counter running nesting lock
 bt bg br bh bp bo bc bk brun bn bl rest extra EG.
Let xfq:=V293_ready_dynamic_exit_fpost unmap group rows high table target current counter running nesting lock
 bt bg br bh bp bo bc bk brun bn bl rest extra EG.
Let sfp:=V293_joint_sched_fpre unmap group rows high bt bg br bh V293_shared_li V293_opened_inv Inv0 Hli.
Let sfq:=V293_joint_sched_fpost unmap group rows high bt bg br bh V293_shared_li V293_opened_inv Inv0 Hli.
Definition V293_ready_irq_spec exit enter sched:funspec:=
 fun f=>if Z.eq_dec f exit then Some(xfp,xfq,(Tvoid,nil))
 else if Z.eq_dec f enter then Some(efp,efq,(Tvoid,nil))
 else if Z.eq_dec f sched then Some(sfp,sfq,(Tvoid,nil))else None.
Definition V293_ready_irq_unit exit enter sched y:=
 V293_exit_env_unit exit enter sched running nesting unmap group rows high y saved
 (V293_exit_boundary_body running nesting lock saved table high target current counter sched
 (V293_interrupt_handoff high current target)).
Lemma V293_ready_irq_domains : forall exit enter sched y,
 EqDom(V293_ready_irq_unit exit enter sched y)(V293_ready_irq_spec exit enter sched).
Proof.
 intros exit enter sched y f.
 unfold V293_ready_irq_unit,V293_exit_env_unit,V293_irq_internal_unit,pumerge,
 V293_OSIntEnter_unit,V293_OSSchedNew_internal_unit,V293_ready_irq_spec.
 destruct(Z.eq_dec f exit),(Z.eq_dec f enter),(Z.eq_dec f sched);
 split;intros[x H];try discriminate;eexists;reflexivity.
Qed.
Theorem V293_ready_irq_WFFunEnv : forall exit enter sched y,
 exit<>enter ->exit<>sched ->enter<>sched ->
 unmap<>y ->group<>y ->rows<>y ->high<>y ->
 table<>saved ->high<>saved ->target<>saved ->current<>saved ->
 counter<>saved ->nesting<>saved ->lock<>saved ->running<>saved ->
 GoodFrm extra ->
 WFFunEnv(V293_ready_irq_unit exit enter sched y)(V293_ready_irq_spec exit enter sched)
 V293_scheduler V293_shared_li Inv0.
Proof.
 intros exit enter sched y XE XS ES UY GY RY HY T H G C K N L R GF.
 pose proof(V293_exit_env_entries exit enter sched running nesting unmap group rows high y saved
 (V293_exit_boundary_body running nesting lock saved table high target current counter sched
 (V293_interrupt_handoff high current target)) XE XS ES)as(CodeX&CodeE&CodeS).
 assert(Sched:V293_ready_irq_spec exit enter sched sched=Some(sfp,sfq,(Tvoid,nil))).
 { unfold V293_ready_irq_spec;repeat destruct Z.eq_dec;try congruence;reflexivity. }
 split;[apply V293_ready_irq_domains| ].
 intros f pre post t tl Lookup;unfold V293_ready_irq_spec in Lookup.
 destruct(Z.eq_dec f exit)as[E|NE].
 - subst f;inversion Lookup;subst pre post t tl.
   exists dnil;exists(dcons saved Tint32 dnil).
   exists(V293_exit_boundary_body running nesting lock saved table high target current counter sched
   (V293_interrupt_handoff high current target)).
   split;[exact CodeX| ];split;[constructor| ];split;[reflexivity| ].
   intros vl p q lg t Pre Post.
   eapply V293_OSIntExit_ready_dynamic_builder_contract;try eassumption.
 - destruct(Z.eq_dec f enter)as[E|NEE].
   + subst f;inversion Lookup;subst pre post t tl.
     exists dnil;exists dnil;exists(V293_OSIntEnter_body running nesting).
     split;[exact CodeE| ];split;[constructor| ];split;[reflexivity| ].
     intros vl p q lg t Pre Post.
     rewrite <-V293_ready_irq_inv_layout.
     eapply V293_OSIntEnter_ready_contract;try eassumption.
   + destruct(Z.eq_dec f sched)as[E|NES];[ |discriminate].
     subst f;inversion Lookup;subst pre post t tl.
     exists dnil;exists(dcons y Tint8 dnil);exists(V293_OSSchedNew_body unmap group rows high y).
     split;[exact CodeS| ];split;[constructor| ];split;[reflexivity| ].
     intros vl p q lg t Pre Post.
     eapply(V293_OSSchedNew_joint_contract unmap group rows high bt bg br bh
     V293_shared_li V293_opened_inv Inv0 Hli);try eassumption.
Qed.
Theorem V293_ready_irq_WFIFun : forall exit enter sched y,
 exit<>enter ->exit<>sched ->enter<>sched ->
 unmap<>y ->group<>y ->rows<>y ->high<>y ->
 table<>saved ->high<>saved ->target<>saved ->current<>saved ->
 counter<>saved ->nesting<>saved ->lock<>saved ->running<>saved ->
 GoodFrm extra ->
 WFIFun(V293_ready_irq_unit exit enter sched y)(V293_ready_irq_spec exit enter sched)
 V293_scheduler Inv0 V293_shared_li.
Proof.
 intros;destruct(V293_ready_irq_WFFunEnv exit enter sched y
 H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14)as[Dom Body].
 split;[exact Dom| ];intros f p q t tl Lookup.
 destruct(Body f p q t tl Lookup)as(d1&d2&s&Code&Types&Decls&Checked).
 exists d1;exists d2;exists s;auto.
Qed.
Theorem V293_ready_irq_Enter_call : forall exit enter sched r ri aop si ci tid,
 exit<>enter ->
 InfRules(V293_ready_irq_spec exit enter sched)V293_scheduler V293_shared_li Inv0 r ri
 (V293_enter_ready_boundary br bg bp brun bn running nesting target tp
 V293_ready_irq_prefix V293_ready_irq_suffix aop si ci tid ** A_dom_lenv nil)
 (scall enter nil)
 (V293_enter_ready_boundary br bg bp brun bn running nesting target tp
 V293_ready_irq_prefix V293_ready_irq_suffix aop si ci tid ** A_dom_lenv nil)tid.
Proof.
 intros;rewrite <-V293_ready_irq_inv_layout;apply V293_OSIntEnter_ready_call.
 unfold V293_ready_irq_spec;repeat destruct Z.eq_dec;try congruence;reflexivity.
Qed.
End ReadyInterruptEnvironment.
