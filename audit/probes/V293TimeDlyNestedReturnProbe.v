(* Exact saved context, with a separate resource-conditional suffix. *)
Require Import CertiOS.audit.probes.V293ReadyOwnedGlobalSwitchProbe.
Require Import CertiOS.audit.probes.V293ReadyOwnedSchedCallProbe.
Require Import CertiOS.audit.probes.V293TimeDlyCallGlobalProbe.
Require Import CertiOS.audit.probes.V293TimeDlyAllocatedProbe.
Require Import CertiOS.audit.probes.V293TimeDlyCallEntryProbe.
Require Import CertiOS.audit.probes.V293TimeDlySwitchProbe.
Require Import CertiOS.audit.probes.V293TimeDlyEntryProbe.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyResumePartition.
Require Import CertiOS.certiucos.v293.proofs.V293TimeDlyNestedReturn.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickReturnTail.
Require Import CertiOS.certiucos.v293.proofs.V293TimeDlyCallEntry.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordInvariant.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyGlobalTrace.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyOwnedGlobalSwitch.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293ClientSkipTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293ReturnClientTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyFullCall.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.simulation.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.


Definition DNcells:list V293_record_cell:=
 cons ((11%positive,0%Z),Tint8,V293_byteval 0)
 (cons ((12%positive,0%Z),Tint32,Vint32(Int.repr 3))
 (cons ((13%positive,0%Z),Tint32,Vint32 Int.zero)nil)).
Definition DNframe c:=V293_owned_record_cells(firstn 7(DOcells c)) **
 V293_read_bytes 80%positive 0%Z V293_ready_table.
Definition DNG:=V293_ready_inv 30%positive 31%positive 83%positive.
Definition DNowned c top bs M:=
 (DWge,V293_cpu_lenv 501%Z bs,M,(fun _:hid=>false),(false,nil,cons top nil),
 DEfinalabs(Int.repr 3),spec_done None)|=
 Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **
 (V293_owned_record_cells DNcells **
 (V293_ready_full 30%positive 31%positive 83%positive OwnershipReady **DNframe c)).

Lemma DNlayout:getaddr DCle=V293_return_addresses DNcells.
Proof. reflexivity. Qed.

Lemma DNcontext:forall bs M top,
 get(DAenvs bs)OwnershipReady=Some(V293_cpu_lenv 501%Z bs) /\
 get(fst(fst(DXfinal top bs M)))OwnershipReady=Some(SKIP,(kenil,DAcontinuation)).
Proof. intros;split;apply map_get_set. Qed.

Lemma DNresources:forall c top,exists bs M,
 DXrun c top bs M /\DOpost c top bs M /\DNowned c top bs M.
Proof.
 intros c top;destruct(DOglobal_sched c top)
 as(bs&y&Mb&Mi&My&Mh&Mtarget&Mcut&Block&Initial&Run&F&FY&Free&Dead&Calls&Count&Owned&Target&Counter).
 assert(Open:(DWge,V293_cpu_lenv 501%Z bs,Mcut,(fun _:hid=>false),(false,nil,cons top nil),
 DEfinalabs(Int.repr 3),spec_done None)|=
 V293_ready_full 30%positive 31%positive 83%positive OwnershipReady **DGframe c bs).
 { eapply V293_owned_switch_active_view;[apply DGframe_good|exact Owned]. }
 exists bs;exists Mcut;split;[exact Run| ];split;[exact Owned| ].
 unfold DNowned,DNframe,DNcells,DGframe,DOcells in *;
 cbn[firstn V293_owned_record_cells]in Open|-*;
 unfold V293_owned_record_cell in Open|-*;clear -Open;sep auto.
Qed.

(* Whole actual saved continuation, not the earlier shortened context.
   Input heap is a genuine prefix endpoint, not a claimed resumed endpoint. *)
Theorem DNnested_TaskSim:forall c top,exists bs M,
 DXrun c top bs M /\DOpost c top bs M /\DNowned c top bs M /\
 TaskSim DAprog(SKIP,(kenil,DAcontinuation))
 (DWge,V293_cpu_lenv 501%Z bs,M,(fun _:hid=>false),(false,nil,cons top nil))
 DWhighprog(SKIP,(kenil,kstop))(DEfinalabs(Int.repr 3))V293_shared_li DNG
 (fun st=>satp(fst st)(snd st)
 ((RDYINV DNG OwnershipReady **DNframe c) **LINV V293_shared_li OwnershipReady nil))OwnershipReady.
Proof.
 intros c top;destruct(DNresources c top)as(bs&M&Run&Post&Owned).
 exists bs;exists M;split;[exact Run| ];split;[exact Post| ];split;[exact Owned| ].
 eapply V293_ready_nested_return_TaskSim with(cells:=DNcells)(op:=spec_done None);
 [reflexivity|reflexivity|exact DNlayout| |right;right;reflexivity| |reflexivity|exact Owned].
 - intros a tp v Member;cbn[DNcells In]in Member;destruct Member as[E|[E|[E|E]]];
   try contradiction;inversion E;reflexivity.
 - unfold DNframe;split;[apply V293_owned_cells_good|vm_compute;repeat split;exact I].
Qed.

(* Local return execution plus the exact residual owned heap. The inner
   boundary is also the prospective outer-free neutralization candidate. *)
Theorem DNrelease:forall c top bs M,DNowned c top bs M ->exists Mi Mf,
 free Tint32 bs M=Some Mi /\freels(V293_return_addresses DNcells)Mi Mf /\
 V293_local_steps DAprogram(SKIP,(kenil,DAcontinuation))
 ((DWge,V293_cpu_lenv 501%Z bs,M),(fun _:hid=>false),(false,nil,cons top nil))
 (SKIP,(kenil,kstop))((DWge,(emp:env),Mf),(fun _:hid=>false),(top,nil,nil)) /\
 (DWge,(emp:env),Mf,(fun _:hid=>false),(top,nil,nil),DEfinalabs(Int.repr 3),spec_done None)|=
 V293_ready_full 30%positive 31%positive 83%positive OwnershipReady **DNframe c /\
 load Tint32 Mi(12%positive,0%Z)=Some(Vint32(Int.repr 3)) /\
 (forall b tp k,In(b,tp)((bs,Tint32)::V293_return_addresses DNcells) ->
 k<typelen tp ->get Mf(b,Z.of_nat k)=None).
Proof.
 intros c top bs M Held;unfold DNowned in Held.
 destruct(V293_tick_free_owned _ _ _ _ _ _ _ _ _ _ _ Held)as(Mi&Inner&Outer).
 assert(Late:load Tint32 Mi(12%positive,0%Z)=Some(Vint32(Int.repr 3))).
 { assert(Member:In((12%positive,0%Z),Tint32,Vint32(Int.repr 3))DNcells)
     by(cbn[DNcells In];tauto).
   exact(V293_record_star_load_l _ _ _ _ _
     (V293_owned_record_cells_load _ _ _ _ Member) _ Outer). }
 assert(Zero:forall a tp v,In(a,tp,v)DNcells ->snd a=0%Z).
 { intros a tp v Member;cbn[DNcells In]in Member;destruct Member as[E|[E|[E|E]]];
   try contradiction;inversion E;reflexivity. }
 destruct(V293_owned_freels DNcells _ _ _ _ _ _ _ _ Zero Outer)as(Mf&Frees&Final).
 assert(Exec:V293_local_steps DAprogram(SKIP,(kenil,DAcontinuation))
   ((DWge,V293_cpu_lenv 501%Z bs,M),(fun _:hid=>false),(false,nil,cons top nil))
   (SKIP,(kenil,kstop))((DWge,(emp:env),Mf),(fun _:hid=>false),(top,nil,nil))).
   { unfold DAcontinuation,DCouter.
     eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sskip_step]| ].
     eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sseq_step]| ].
     eapply V293_local_cons;[apply excrit_step;reflexivity| ].
     apply V293_csteps_local;eapply V293_cstepstar_trans.
     - eapply V293_owned_return_execution with(cells:=cons ((bs,0%Z),Tint32,Vint32 Int.zero)nil);
       [apply V293_cpu_layout|econstructor;[exact Inner|constructor]].
     - eapply V293_owned_return_execution;[exact DNlayout|exact Frees]. }
   exists Mi;exists Mf;split;[exact Inner| ];split;[exact Frees| ];split;[exact Exec| ];split.
   + eapply good_inv_prop;[split;[ |unfold DNframe;split;[apply V293_owned_cells_good|vm_compute;repeat split;exact I]]|exact Final].
     unfold V293_ready_full;cbn[GoodInvAsrt];intros;split;[intros;split;exact I| ].
     split;[unfold V293_shared_fields;repeat split;exact I|apply V293_ready_payload_good].
   + split;[exact Late| ];intros b tp k Member Bound.
     eapply V293_nested_freels_removed;[econstructor;[exact Inner|exact Frees]|exact Member|exact Bound].
Qed.

(* Single factor: stop after the same inner free, instead of performing
   the outer return/free. This is not an execution of a modified OS. *)
Theorem DNouter_free_ablation:forall c top,exists bs M Mi Mf,
 DXrun c top bs M /\DNowned c top bs M /\
 free Tint32 bs M=Some Mi /\freels(V293_return_addresses DNcells)Mi Mf /\
 (forall b tp k,In(b,tp)(V293_return_addresses DNcells) ->
 k<typelen tp ->get Mf(b,Z.of_nat k)=None) /\
 ~(forall b tp k,In(b,tp)(V293_return_addresses DNcells) ->
 k<typelen tp ->get Mi(b,Z.of_nat k)=None).
Proof.
 intros c top;destruct(DNresources c top)as(bs&M&Run&Post&Owned).
 destruct(DNrelease c top bs M Owned)as(Mi&Mf&Inner&Frees&Exec&Final&Late&Removed).
 exists bs;exists M;exists Mi;exists Mf;split;[exact Run| ];split;[exact Owned| ];
 split;[exact Inner| ];split;[exact Frees| ];split.
 - intros b tp k Member Bound;apply(Removed b tp k);[right;exact Member|exact Bound].
 - intros Missing.
   assert(Empty:get Mi(12%positive,0%Z)=None).
   { apply(Missing 12%positive Tint32 0);[cbn[DNcells V293_return_addresses map In];tauto|cbn[typelen];lia]. }
   unfold load,loadm in Late;cbn[typelen loadbytes]in Late.
   change(@get addr(bool *memval)mem memMap Mi(12%positive,0%Z)=None)in Empty.
   rewrite Empty in Late;discriminate.
Qed.
