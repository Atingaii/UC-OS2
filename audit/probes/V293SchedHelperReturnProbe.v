(* Return-suffix witnesses, not a complete original active-call witness. *)
Require Import CertiOS.certiucos.v293.proofs.V293SchedHelperReturnTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293SchedCallProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293SchedHelperTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293ReadySchedCall.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.certiucos.v293.proofs.V293ReturnClientTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293PendingReturnTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.audit.probes.V293ReadySchedCallProbe.
Require Import CertiOS.audit.probes.V293ReadyTargetHandoffProbe.
Require Import CertiOS.audit.probes.V293ReadyTaskInvariantProbe.
Require Import CertiOS.audit.probes.V293TaskRecordInvariantProbe.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.simulation.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.memory_prop.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition HRresource := CurTid OwnershipWaiting **Atrue.
Definition HRlocal b : env := set emp 104%Z(b,Tint8).
Definition HRsuffix := (SKIP,(kenil,kseq sret
 (kcall 107%Z(V293_OSSchedNew_body 100%Z 101%Z 102%Z 103%Z 104%Z)RTle kstop))).

Lemma HRgood : GoodInvAsrt HRresource.
Proof.
 unfold HRresource;split;[unfold CurTid,Agvarmapsto,Aptrmapsto;cbn[GoodInvAsrt];intros;repeat split;exact I|exact I].
Qed.

Lemma HRbase : RHstate OwnershipWaiting(RHmemory OwnershipWaiting)|=HRresource.
Proof.
 pose proof(RCentry OwnershipWaiting)as H.
 unfold HRresource,SWINVt in *;fold(CurTid OwnershipWaiting)in H;sep auto.
Qed.

Theorem HRnonvacuous_return : forall ip A,
 exists b,
 fresh(RHmemory OwnershipWaiting)b /\
 (RHge,HRlocal b,allocb(RHmemory OwnershipWaiting)b 0%Z 1,(fun _=>false),
 (false,nil,nil),RIabstract OwnershipWaiting,spec_done None)|=
 Amapsto(b,0%Z)Tint8 true Vundef **HRresource /\
 TaskSim(RCprogram,(RCprogram,(fun _=>None),ip))HRsuffix
 (RHge,HRlocal b,allocb(RHmemory OwnershipWaiting)b 0%Z 1,(fun _=>false),(false,nil,nil))
 (RCprogram,A)(SKIP,(kenil,kstop))(RIabstract OwnershipWaiting)V293_shared_li
 (V293_ready_inv 80%positive 81%positive 82%positive)
 (fun st=>satp(fst st)(snd st)HRresource)OwnershipWaiting.
Proof.
 intros ip A;destruct(memory_has_fresh_block(RHmemory OwnershipWaiting))as[b Fresh].
 assert(Own:(RHge,HRlocal b,allocb(RHmemory OwnershipWaiting)b 0%Z 1,(fun _=>false),
 (false,nil,nil),RIabstract OwnershipWaiting,spec_done None)|=
 Amapsto(b,0%Z)Tint8 true Vundef **HRresource).
 { eapply V293_tick_allocate_frame with(tp:=Tint8);[exact Fresh| ].
   eapply good_inv_prop;[exact HRgood|exact HRbase]. }
 exists b;split;[exact Fresh| ];split;[exact Own| ].
 unfold HRsuffix,HRlocal.
 eapply V293_sched_helper_return_TaskSim with(R:=HRresource)(op:=spec_done None)(v:=Vundef).
 - unfold RCprogram;destruct(Z.eq_dec 107%Z 107%Z);[reflexivity|contradiction].
 - exact HRgood.
 - intros s H;exact H.
 - exact Own.
 - intros Mret Rest;apply V293_return_client_coinduction.
   + right;right;reflexivity.
   + eapply V293_pending_local with(op:=spec_done None);exact Rest.
   + intros ab;eapply good_inv_prop;[exact HRgood|exact Rest].
Qed.

(* Every physical allocation choice is erased by the actual byte free. *)
Theorem HRchoice_erased : forall p ge caller M bh old yval priority y f body ks b c,
 fresh M b ->fresh M c ->b<>c ->get M(bh,0%Z)=Some(true,old) ->
 cstepstar p(SKIP,(kenil,kseq sret(kcall f body caller ks)))
 (ge,set(emp:env)y(b,Tint8),
 V293_write_byte(V293_write_byte(allocb M b 0%Z 1)b yval)bh priority)
 (SKIP,(kenil,ks))(ge,caller,V293_write_byte M bh priority) /\
 cstepstar p(SKIP,(kenil,kseq sret(kcall f body caller ks)))
 (ge,set(emp:env)y(c,Tint8),
 V293_write_byte(V293_write_byte(allocb M c 0%Z 1)c yval)bh priority)
 (SKIP,(kenil,ks))(ge,caller,V293_write_byte M bh priority).
Proof.
 intros p ge caller M bh old yval priority y f body ks b c FB FC Different High.
 split;apply V293_helper_return_steps;eapply V293_sched_storage;eassumption.
Qed.

Theorem HRtwo_choices_exist : forall M,
 exists b c,fresh M b /\fresh M c /\b<>c.
Proof.
 intro M;destruct(memory_has_fresh_block M)as[b FB].
 destruct(V293_ready_fresh_avoiding M[b])as(c&FC&Avoid).
 exists b;exists c;split;[exact FB| ];split;[exact FC| ].
 intro E;subst;apply Avoid;left;reflexivity.
Qed.

(* Same whole memory, but the empty task-owned part cannot free the byte. *)
Theorem HRowned_boundary : forall ge le M ir aux O op b v R,
 (ge,le,M,ir,aux,O,op)|=Amapsto(b,0%Z)Tint8 true v **R ->
 exists Mret,free Tint8 b M=Some Mret /\
 join(emp:mem)M M /\free Tint8 b(emp:mem)=None /\
 forall R',~(ge,le,(emp:mem),ir,aux,(emp:osabst),op)|=
 Amapsto(b,0%Z)Tint8 true v **R'.
Proof.
 intros ge le M ir aux O op b v R Held.
 destruct(V293_ready_release_byte _ _ _ _ _ _ _ _ _ _ Held)as(Mret&Free&Rest&Removed&Outside).
 exists Mret;split;[exact Free| ];split;[apply map_join_comm;apply map_join_emp| ];split;[reflexivity| ].
 intros R' Bad;destruct(V293_ready_release_byte _ _ _ _ _ _ _ _ _ _ Bad)as(Mx&Impossible&Restx).
 discriminate Impossible.
Qed.

Theorem HRframe_preserved : forall ge le M ir aux O op b v R Mf Mall,
 (ge,le,M,ir,aux,O,op)|=Amapsto(b,0%Z)Tint8 true v **R ->
 join M Mf Mall ->exists Mret Mallret,
 free Tint8 b M=Some Mret /\free Tint8 b Mall=Some Mallret /\join Mret Mf Mallret.
Proof.
 intros ge le M ir aux O op b v R Mf Mall Held Join.
 destruct(V293_ready_release_byte _ _ _ _ _ _ _ _ _ _ Held)as(Mret&Free&Rest).
 destruct(free_mono _ _ _ _ _ _ Join Free)as(Mallret&Full).
 exists Mret;exists Mallret;split;[exact Free| ];split;[exact Full| ];eapply join_free;eassumption.
Qed.
