(* Full Enter calls and a real interrupt-entry prefix. The endpoint is the
   Exit call, not an ISR return, simulation, or initialized-kernel claim. *)
Require Import CertiOS.certiucos.v293.proofs.V293InterruptControlExecution.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptFixedControlSpec.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptControlRetention.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptSourceRoundtrip.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitInterruptGlobal.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293LocalGlobalTrace.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyGlobalTrace.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterInternal.
Require Import CertiOS.certiucos.v293.code.V293OSIntEnter.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.framework.proof.join_prop.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import Coq.Lists.List Coq.Relations.Relation_Operators Lia.
Local Open Scope nat_scope.

(* Caller locals may shadow the global names. sfexec creates the empty
   callee environment and sfree restores exactly the original caller. *)
Theorem V293_control_enter_full_call : forall P ks ge caller M
 f running nesting br bn c,
 P f=Some(V293_OSIntEnter_function running nesting) ->
 V293_control_valid c ->
 get ge running=Some(br,Tint8) ->get ge nesting=Some(bn,Tint8) ->
 load Tint8 M(br,0%Z)=Some(V293_byteval(V293_control_running c)) ->
 load Tint8 M(bn,0%Z)=Some(V293_byteval(V293_control_nesting c)) ->
 (exists v,get M(bn,0%Z)=Some(true,v)) ->
 cstepstar P(curs(scall f nil),(kenil,ks))(ge,caller,M)
 (curs(sskip None),(kenil,ks))(ge,caller,V293_control_enter_memory bn c M).
Proof.
 intros P ks ge caller M f running nesting br bn c Program Valid GR GN LR LN W.
 eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply snpcall_step]| ].
 eapply c_stepstarn.
 { eapply stmt_step;[reflexivity| ];eapply sfexec_step with(d1:=dnil)(d2:=dnil);
   [reflexivity|reflexivity|exact Program|exact I|reflexivity]. }
 eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply sallocend_step]| ].
 unfold V293_OSIntEnter_body at 1.
 eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply sseq_step]| ].
 eapply V293_cstepstar_trans with(m2:=(ge,emp,V293_control_enter_memory bn c M)).
 - eapply V293_control_enter_execution;try eassumption.
   unfold V293_interrupt_env;repeat split;try assumption;apply map_emp_get.
 - eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply sskip_step]| ].
   eapply c_stepstarn.
   { eapply stmt_step;[reflexivity| ];eapply sret_step with(al:=nil);
     [reflexivity|reflexivity|reflexivity]. }
   eapply c_stepstarn;[eapply stmt_step;[reflexivity|eapply sfreeend_step;reflexivity]| ].
   apply c_stepstar0.
Qed.

Theorem V293_control_enter_call_bridge : forall P ks sd O ge caller M
 f running nesting br bn bl c,
 P f=Some(V293_OSIntEnter_function running nesting) ->
 V293_control_valid c ->br<>bn ->bl<>bn ->
 get ge running=Some(br,Tint8) ->get ge nesting=Some(bn,Tint8) ->
 load Tint8 M(br,0%Z)=Some(V293_byteval(V293_control_running c)) ->
 load Tint8 M(bn,0%Z)=Some(V293_byteval(V293_control_nesting c)) ->
 load Tint8 M(bl,0%Z)=Some(V293_byteval(V293_control_lock c)) ->
 (exists v,get M(bn,0%Z)=Some(true,v)) ->
 exists Mf,
 cstepstar P(curs(scall f nil),(kenil,ks))(ge,caller,M)
 (curs(sskip None),(kenil,ks))(ge,caller,Mf) /\
 V293_control_read br bn bl Mf=Some(V293_control_enter c) /\
 V293_control_step sd V293_control_Enter(O,c)
 (V293_control_Core(spec_done None))(O,V293_control_enter c) /\
 (forall a,a<>(bn,0%Z) ->get Mf a=get M a).
Proof.
 intros P ks sd O ge caller M f running nesting br bn bl c Program Valid BR BL GR GN LR LN LL W.
 destruct(V293_control_enter_observation br bn bl c M Valid BR BL LR LN LL)as[Read Frame].
 exists(V293_control_enter_memory bn c M);split.
 - eapply V293_control_enter_full_call;eassumption.
 - split;[exact Read| ];split;[constructor;exact Valid|exact Frame].
Qed.

(* EOI clears only the entered ISR bit. The full call is sandwiched between
   actual sequence steps and leaves Exit unexecuted. *)
Theorem V293_control_enter_irq_local : forall P ge M ir i si
 entry exit vector running nesting br bn c,
 P entry=Some(V293_OSIntEnter_function running nesting) ->
 V293_control_valid c ->
 get ge running=Some(br,Tint8) ->get ge nesting=Some(bn,Tint8) ->
 load Tint8 M(br,0%Z)=Some(V293_byteval(V293_control_running c)) ->
 load Tint8 M(bn,0%Z)=Some(V293_byteval(V293_control_nesting c)) ->
 (exists v,get M(bn,0%Z)=Some(true,v)) ->
 ir i=false ->i=Z.to_nat(Int.unsigned vector) ->
 (0<=Int.unsigned vector<Z.of_nat INUM)%Z ->
 V293_local_steps P
 (curs(V293_irq_source_wrapper entry exit vector),(kenil,kstop))
 ((ge,emp,M),isrupd ir i true,(false,i::si,nil))
 (curs(scall exit nil),(kenil,kseq(sprim exint)kstop))
 ((ge,emp,V293_control_enter_memory bn c M),ir,(false,i::si,nil)).
Proof.
 intros P ge M ir i si entry exit vector running nesting br bn c
 Program Valid GR GN LR LN W Clear Vector VRange.
 unfold V293_irq_source_wrapper.
 eapply V293_local_cons.
 { apply ostc_step;eapply stmt_step;[reflexivity|apply sseq_step]. }
 eapply V293_local_cons.
 { eapply eoi_step;[reflexivity|exact Vector|exact VRange]. }
 rewrite V293_interrupt_eoi_restores_ir by exact Clear.
 eapply V293_local_cons.
 { apply ostc_step;eapply stmt_step;[reflexivity|apply sskip_step]. }
 eapply V293_local_cons.
 { apply ostc_step;eapply stmt_step;[reflexivity|apply sseq_step]. }
 eapply V293_local_trans.
 { apply V293_csteps_local;eapply V293_control_enter_full_call;eassumption. }
 eapply V293_local_cons.
 { apply ostc_step;eapply stmt_step;[reflexivity|apply sskip_step]. }
 eapply V293_local_cons.
 { apply ostc_step;eapply stmt_step;[reflexivity|apply sseq_step]. }
 apply V293_local_refl.
Qed.

(* The input is a task interrupted at arbitrary expression/statement
   continuations. The original pint_step constructs kint; no input kint. *)
Theorem V293_control_enter_irq_global : forall pc po pi ip T les aus cst t
 ge caller M ir si interrupted ike ks i entry exit vector
 running nesting br bn bl c sd O,
 get T t=Some(interrupted,(ike,ks)) ->
 get les t=Some caller ->get aus t=Some((true,si,nil):localst) ->
 goodks(pc,(po,pi,ip))(kint interrupted ike caller ks) ->
 higherint ir i ->i<INUM ->
 i=Z.to_nat(Int.unsigned vector) ->(0<=Int.unsigned vector<Z.of_nat INUM)%Z ->
 ip i=Some(V293_irq_source_wrapper entry exit vector) ->
 (pumerge po pi)entry=Some(V293_OSIntEnter_function running nesting) ->
 V293_control_valid c ->br<>bn ->bl<>bn ->
 get ge running=Some(br,Tint8) ->get ge nesting=Some(bn,Tint8) ->
 load Tint8 M(br,0%Z)=Some(V293_byteval(V293_control_running c)) ->
 load Tint8 M(bn,0%Z)=Some(V293_byteval(V293_control_nesting c)) ->
 load Tint8 M(bl,0%Z)=Some(V293_byteval(V293_control_lock c)) ->
 (exists v,get M(bn,0%Z)=Some(true,v)) ->
 exists Mf,
 V293_global_steps(pc,(po,pi,ip))cst
 (T,(ge,les,M,ir,aus),t)
 (set T t(curs(scall exit nil),(kenil,kseq(sprim exint)(kint interrupted ike caller ks))),
  (ge,set les t emp,Mf,ir,set aus t(false,i::si,nil)),t) /\
 V293_control_read br bn bl Mf=Some(V293_control_enter c) /\
 V293_control_step sd V293_control_Enter(O,c)
 (V293_control_Core(spec_done None))(O,V293_control_enter c) /\
 (forall a,a<>(bn,0%Z) ->get Mf a=get M a).
Proof.
 intros pc po pi ip T les aus cst t ge caller M ir si interrupted ike ks i entry exit vector
 running nesting br bn bl c sd O Code Env Aux Good Higher Range Vector VRange Installed
 Program Valid BR BL GR GN LR LN LL W.
 assert(Clear:ir i=false)by(apply Higher;lia).
 pose proof(V293_control_enter_irq_local(pumerge po pi)ge M ir i si entry exit vector
 running nesting br bn c Program Valid GR GN LR LN W Clear Vector VRange)as Prefix.
 pose proof(V293_interrupt_local_steps_global pc po pi ip _ _ _ _ Prefix
 interrupted ike caller ks T les aus t cst Good)as Lifted.
 destruct(V293_control_enter_observation br bn bl c M Valid BR BL LR LN LL)as[Read Frame].
 exists(V293_control_enter_memory bn c M);split.
 - unfold V293_global_steps;eapply rt1n_trans with(y:=
   (set T t(curs(V293_irq_source_wrapper entry exit vector),(kenil,kint interrupted ike caller ks)),
    (ge,set les t emp,M,isrupd ir i true,set aus t(false,i::si,nil)),t)).
   + eapply V293_interrupt_source_enter;eassumption.
   + exact Lifted.
 - split;[exact Read| ];split;[constructor;exact Valid|exact Frame].
Qed.
