(* Existing weak storage invariant; no current/cache guard is inserted. *)
Require Import CertiOS.certiucos.v293.proofs.V293InvariantPendingTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyStorageInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitch.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyFullCall.
Require Import CertiOS.certiucos.v293.proofs.V293ClientSkipTaskSim.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.simulation.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Section StorageReturn.
Variables br bg bp : block.
Variable target : var.
Variable tp : type.
Variable cells : list(addr*type).
Let G:=V293_ready_storage_inv br bg bp target tp cells.
Let C:=V293_ready_storage_core br bg bp target tp cells.

Lemma V293_storage_return_enabled_INV : forall ge le M ir si ci O op,
 (forall i,ir i=false) -> (ge,le,M,ir,(true,si,ci),O,op)|=C ->
 (ge,le,M,ir,(true,si,ci),O,op)|=INV G.
Proof.
 intros ge le M ir si ci O op Clear Core.
 change((ge,le,M,ir,(true,si,ci),O,op)|=Aemp **(inv_ieon G \\// inv_ieoff G)).
 apply astar_l_aemp_intro;left;unfold inv_ieon.
 apply sat_split';exists(emp:mem);exists M;exists(emp:osabst);exists O.
 split;[apply map_join_comm;apply map_join_emp| ];
 split;[apply map_join_comm;apply map_join_emp| ];split;[repeat split;reflexivity| ].
 unfold invlth_isr;eapply V293_shared_clear_noisr_close;[exact Clear| ].
 apply V293_ready_storage_noisr_core;exact Core.
Qed.

Lemma V293_storage_return_disabled_SWINV : forall ge le M ir si ci O op,
 (forall i,ir i=false) -> (ge,le,M,ir,(false,si,ci),O,op)|=C ->
 (ge,le,M,ir,(false,si,ci),O,op)|=SWINV G.
Proof.
 intros ge le M ir si ci O op Clear Core.
 assert(Flags:(ge,le,(emp:mem),ir,(false,si,ci),(emp:osabst),op)|=isrclr **Aie false).
 { apply sat_split';exists(emp:mem);exists(emp:mem);exists(emp:osabst);exists(emp:osabst).
   split;[apply map_join_emp| ];split;[apply map_join_emp| ];split;[ |repeat split;reflexivity].
   exists ir;split;[repeat split;reflexivity|split;[exact Clear|split;reflexivity]]. }
 unfold SWINV;apply sat_split';exists(emp:mem);exists M;exists(emp:osabst);exists O.
 split;[apply map_join_comm;apply map_join_emp| ];
 split;[apply map_join_comm;apply map_join_emp| ];split;[exact Flags| ].
 exists(gettopis si);apply sat_split';exists(emp:mem);exists M;exists(emp:osabst);exists O.
 split;[apply map_join_comm;apply map_join_emp| ];
 split;[apply map_join_comm;apply map_join_emp| ];split;[repeat split;reflexivity| ].
 unfold invlth_isr;rewrite Nat.sub_0_r.
 eapply V293_shared_clear_noisr_close;[exact Clear| ].
 apply V293_ready_storage_noisr_core;exact Core.
Qed.

Theorem V293_storage_pending_TaskSim : forall pc po pi ip A t ge M ir top ci O op
 f body caller tail tau d1 d2 saved b v,
 po f=Some(tau,d1,d2,body) ->V293_skip_client_state(SKIP,(kenil,tail)) ->
 (forall i,ir i=false) ->
 (ge,V293_cpu_lenv saved b,M,ir,(false,nil,top::ci),O,op)|=
 Amapsto(b,0%Z)Tint32 true v **(C **CurTid t) ->
 TaskSim(pc,(po,pi,ip))
 (SKIP,(kenil,kseq(sprim excrit)(kseq sret(kcall f body caller tail))))
 (ge,V293_cpu_lenv saved b,M,ir,(false,nil,top::ci))
 (pc,A)(SKIP,(kenil,tail))O V293_shared_li G
 (fun st=>satp(fst st)(snd st)(RDYINV G t **LINV V293_shared_li t nil))t.
Proof.
 intros pc po pi ip A t ge M ir top ci O op f body caller tail tau d1 d2 saved b v Bind Cases Clear Held.
 eapply V293_invariant_pending_TaskSim;[reflexivity|apply V293_ready_storage_core_good| | |exact Bind|exact Cases|exact Clear|exact Held].
 - intros;apply V293_storage_return_disabled_SWINV;assumption.
 - intros;apply V293_storage_return_enabled_INV;assumption.
Qed.
End StorageReturn.
