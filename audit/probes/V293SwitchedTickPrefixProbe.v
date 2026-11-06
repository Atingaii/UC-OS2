(* Source prefix on the switched heap with explicit scanner preparation.
   Not a globally reachable ISR entry or a complete tick call. *)
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.audit.probes.V293TimeDlyEntryProbe.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Require Import CertiOS.audit.probes.V293TimeDlySwitchProbe.
Require Import CertiOS.audit.probes.V293TimeDlyAllocatedProbe.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyGlobalTrace.
Require Import CertiOS.audit.probes.V293TimeDlyCallGlobalProbe.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.audit.probes.V293TimeDlySchedCallProbe.
Require Import CertiOS.audit.probes.V293ReadyOwnedSchedCallProbe.
Require Import CertiOS.framework.proof.rulesoundlib.

Require Import CertiOS.audit.probes.V293ReadyOwnedGlobalSwitchProbe.
Require Import CertiOS.certiucos.v293.proofs.V293SwitchedCountdownClosure.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickTaskBridge.
Require Import CertiOS.certiucos.v293.proofs.V293SwitchedTickPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickTraversal.
Require Import CertiOS.certiucos.v293.code.V293OSTimeTick.
Require Import CertiOS.audit.probes.V293SwitchedCountdownClosureProbe.
Import ListNotations.
Local Open Scope nat_scope.

Definition SPle b:env:=set(emp:env)700%Z(b,Tptr V293_tcb_type).
Definition SPowned c bs b aux O M:=
 (DWge,SPle b,M,(fun _:hid=>false),aux,O,spec_done None)|=
 V293_ready_full 30%positive 31%positive 83%positive OwnershipWaiting **
 (V293_owned_record_cell((b,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady) **DGframe c bs).
Definition SPprepared c bs b M:=SPowned c bs b(true,nil,nil)DGabs M.
Definition SPpost c bs b M:=SPowned c bs b(false,nil,[true])SCabs2 M.
Definition SPsetup b M Mp:=
 fresh M b /\
 alloc 700%Z(Tptr V293_tcb_type)(emp:env)M(SPle b)
 (allocb M b 0%Z(typelen(Tptr V293_tcb_type))) /\
 cstep DAprogram(curs(salloc nil(dcons 700%Z(Tptr V293_tcb_type)dnil)),(kenil,kstop))
 (DWge,(emp:env),M)(curs(salloc nil dnil),(kenil,kstop))
 (DWge,SPle b,allocb M b 0%Z(typelen(Tptr V293_tcb_type))) /\
 store(Tptr V293_tcb_type)(allocb M b 0%Z(typelen(Tptr V293_tcb_type)))
 (b,0%Z)(Vptr OwnershipReady)=Some Mp.
Definition SPexecution b M Mf:=
 V293_local_steps DAprogram(curs(V293_tick_iteration 700%Z 701%Z 702%Z),(kenil,kstop))
 ((DWge,SPle b,M),(fun _:hid=>false),(true,nil,nil))
 (curs(V293_tick_advance 700%Z),(kenil,kseq(sprim excrit)kstop))
 ((DWge,SPle b,Mf),(fun _:hid=>false),(false,nil,[true])).

(* Fresh allocation is real. Pointer initialization is an explicit resource
   preparation store, not a claim about source head assignment or ISR entry. *)
Lemma SPprepare:forall c bs M,DGpost c bs M ->exists b Mp,
 SPsetup b M Mp /\SPprepared c bs b Mp.
Proof.
 intros c bs M Held;destruct(fresh_exist M)as[b Fresh].
 assert(Frame:(DWge,SPle b,M,(fun _:hid=>false),(true,nil,nil),DGabs,spec_done None)|=
 V293_ready_full 30%positive 31%positive 83%positive OwnershipWaiting **DGframe c bs).
 { eapply good_inv_prop;[split;[apply V293_ready_full_good|apply DGframe_good]|exact Held]. }
 assert(Unbound:~indom(emp:env)700%Z).
 { intro Bad;destruct Bad as[v Bad];rewrite map_emp_get in Bad;discriminate. }
 destruct(V293_tick_scan_allocation DAprogram kstop dnil DWge(emp:env)M
 (fun _:hid=>false)(true,nil,nil)DGabs(spec_done None)700%Z b _ Fresh Unbound Frame)
 as(Allocate&Execute&Raw&Undef).
 destruct(V293_tick_raw_slot_update(b,0%Z)(Tptr V293_tcb_type)Vundef(Vptr OwnershipReady)
 _ DWge(SPle b)(allocb M b 0%Z(typelen(Tptr V293_tcb_type)))
 (fun _:hid=>false)(true,nil,nil)DGabs(spec_done None)eq_refl Raw)
 as(Mp&Store&Owned).
 exists b;exists Mp;split.
 - split;[exact Fresh| ];split;[exact Allocate| ];split;assumption.
 - unfold SPprepared,SPowned;clear -Owned;sep auto.
Qed.

Theorem SPfirst:forall c bs b M,SPprepared c bs b M ->exists Mf,
 store Tint32 M(60%positive,44%Z)(Vint32(Int.repr 2))=Some Mf /\
 SPexecution b M Mf /\
 spec_step V293_scheduler(spec_prim nil(V293_tick_wait_step OwnershipReady))DGabs(END None)SCabs2 /\
 SPpost c bs b Mf /\load Tint32 Mf(60%positive,44%Z)=Some(Vint32(Int.repr 2)) /\
 (forall x i,x<>60%positive \/(i<44)%Z \/(48<=i)%Z ->get Mf(x,i)=get M(x,i)).
Proof.
 intros c bs b M Held.
 exact(V293_ready_countdown_iteration_prefix 30%positive 31%positive 83%positive OwnershipWaiting
 (DEblocked(Int.repr 3))60%positive 0(Int.repr 4)3 Vnull(DGframe c bs)DAprogram kstop
 DWge(SPle b)M(fun _:hid=>false)true nil nil DGabs(spec_done None)V293_scheduler
 700%Z 701%Z 702%Z b eq_refl(ltac:(lia))(ltac:(change(44<=4294967295)%Z;lia))
 (ltac:(change(2<=3<=4294967295)%Z;lia))eq_refl eq_refl(DGframe_good c bs)Held).
Qed.

Lemma SPrecords:forall c bs b M,SPpost c bs b M ->V293_task_records M SCtasks2.
Proof.
 intros c bs b M Held;exact(V293_ready_full_records 30%positive 31%positive 83%positive
 OwnershipWaiting SCtasks2 (V293_owned_record_cell((b,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady) **DGframe c bs) DWge(SPle b)M(fun _:hid=>false)(false,nil,[true])
 SCabs2(spec_done None)eq_refl Held).
Qed.

(* The only changed statement is the decrement assignment. Guards, skipped
   expiry, critical entry and the continuation before Next are unchanged. *)
Definition SPmutant_delay ptcb rows group:=
 sifthen(V293_tick_ne(V293_tick_field ptcb 13%Z)0)
 (sseq(sskip None)(sifthen(V293_tick_eq(V293_tick_field ptcb 13%Z)0)
 (V293_tick_expiry ptcb rows group))).
Definition SPmutant_iteration ptcb rows group:=sseq(sprim encrit)
 (sseq(SPmutant_delay ptcb rows group)(sseq(V293_tick_advance ptcb)(sprim excrit))).
Definition SPmutant_execution b M:=
 V293_local_steps DAprogram(curs(SPmutant_iteration 700%Z 701%Z 702%Z),(kenil,kstop))
 ((DWge,SPle b,M),(fun _:hid=>false),(true,nil,nil))
 (curs(V293_tick_advance 700%Z),(kenil,kseq(sprim excrit)kstop))
 ((DWge,SPle b,M),(fun _:hid=>false),(false,nil,[true])).

Theorem SPmutant_late_gate:forall c bs b M,SPprepared c bs b M ->
 SPmutant_execution b M /\SPowned c bs b(false,nil,[true])DGabs M /\
 load Tint32 M(60%positive,44%Z)=Some(Vint32(Int.repr 3)) /\~V293_task_records M SCtasks2.
Proof.
 intros c bs b M Held.
 pose proof(V293_ready_full_records 30%positive 31%positive 83%positive
 OwnershipWaiting(DEblocked(Int.repr 3))(V293_owned_record_cell((b,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady) **DGframe c bs) DWge(SPle b)M(fun _:hid=>false)(true,nil,nil)
 DGabs(spec_done None)eq_refl Held)as Records.
 destruct(Records OwnershipReady(Int.repr 4)(wait os_stat_time(Int.repr 3))Vnull eq_refl)
 as(p&Prange&Priority&Fields&Status);destruct Status as(Stat&Delay&Message).
 change(load Tint32 M(60%positive,44%Z)=Some(Vint32(Int.repr 3)))in Delay.
 assert(Pointer:load(Tptr V293_tcb_type)M(b,0%Z)=Some(Vptr OwnershipReady)).
 { assert(Cell:(DWge,SPle b,M,(fun _:hid=>false),(true,nil,nil),DGabs,spec_done None)|=
 V293_owned_record_cell((b,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady) **Atrue)
 by(clear -Held;unfold SPprepared,SPowned in Held;sep auto).
 exact(V293_record_star_load_l _ _ _ _ _ (V293_owned_record_cell_load _ _ _) _ Cell). }
 destruct(V293_tick_field_eval DWge(SPle b)M 700%Z b 60%positive 0 13%Z 44%Z Tint32 _
 eq_refl Pointer eq_refl eq_refl(ltac:(lia))(ltac:(lia))
 (ltac:(change(44<=4294967295)%Z;lia))Delay)as(Ty&Value).
 assert(Guard:evalval(V293_tick_ne(V293_tick_field 700%Z 13%Z)0)(DWge,SPle b,M)=Some(Vint32 Int.one)).
 { unfold V293_tick_ne,V293_tick_eq;cbn[evalval evaltype];rewrite Ty,Value;reflexivity. }
 assert(Expiry:evalval(V293_tick_eq(V293_tick_field 700%Z 13%Z)0)(DWge,SPle b,M)=Some(Vint32 Int.zero)).
 { unfold V293_tick_eq;cbn[evalval evaltype];rewrite Ty,Value;reflexivity. }
 assert(Execute:forall ks,cstepstar DAprogram(curs(SPmutant_delay 700%Z 701%Z 702%Z),(kenil,ks))
 (DWge,SPle b,M)(curs(sskip None),(kenil,ks))(DWge,SPle b,M)).
 { intro ks;unfold SPmutant_delay;eapply V293_rekey_if_execution with(flag:=true);
 [exact Guard| |discriminate].
 intros _;eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply sseq_step]| ].
 eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply sskip_step]| ].
 eapply V293_rekey_if_execution with(flag:=false);[exact Expiry|discriminate|reflexivity]. }
 split.
 - unfold SPmutant_execution,SPmutant_iteration.
   eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sseq_step]| ].
   eapply V293_local_cons;[apply encrit_step;reflexivity| ].
   eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sskip_step]| ].
   eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sseq_step]| ].
   eapply V293_local_trans;[apply V293_csteps_local;apply Execute| ].
   eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sskip_step]| ].
   eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sseq_step]| ].
   apply V293_local_refl.
 - split.
   + unfold SPowned;eapply good_inv_prop;[ | exact Held].
     split;[apply V293_ready_full_good|split;[unfold V293_owned_record_cell;cbn;auto|apply DGframe_good]].
   + split;[exact Delay| ].
     intro Stale;specialize(Stale OwnershipReady(Int.repr 4)(wait os_stat_time(Int.repr 2))Vnull eq_refl).
     destruct Stale as(q&Bound2&Priority2&Fields2&Status2);destruct Status2 as(Stat2&Delay2&Message2).
     change(load Tint32 M(60%positive,44%Z)=Some(Vint32(Int.repr 2)))in Delay2.
     rewrite Delay in Delay2;discriminate.
Qed.

Theorem SPsame_input_ablation:forall c enabled,exists bs M b Mp Mf,
 V293_global_steps DAprog DXclient(DXinitial c enabled)(DXfinal enabled bs M) /\
 DGpost c bs M /\SPsetup b M Mp /\SPprepared c bs b Mp /\
 SPexecution b Mp Mf /\SPpost c bs b Mf /\V293_task_records Mf SCtasks2 /\
 SPmutant_execution b Mp /\SPowned c bs b(false,nil,[true])DGabs Mp /\
 load Tint32 Mf(60%positive,44%Z)=Some(Vint32(Int.repr 2)) /\
 load Tint32 Mp(60%positive,44%Z)=Some(Vint32(Int.repr 3)) /\~V293_task_records Mp SCtasks2.
Proof.
 intros c enabled;destruct(DGglobal_switch c enabled)
 as(bs&y&My&Mh&Mc&M&Run&Pre&Free&Dead&Trace&Switch&Store&After&Rest).
 destruct(SPprepare c bs M After)as(b&Mp&Setup&Prepared).
 destruct(SPfirst c bs b Mp Prepared)as(Mf&Write&Execute&Abstract&Post&Load&Outside).
 destruct(SPmutant_late_gate c bs b Mp Prepared)as(Mutant&Preserved&Old&Reject).
 exists bs;exists M;exists b;exists Mp;exists Mf.
 split;[exact Trace| ];split;[exact After| ];split;[exact Setup| ];split;[exact Prepared| ];
 split;[exact Execute| ];split;[exact Post| ];split;[eapply SPrecords;exact Post| ];
 split;[exact Mutant| ];split;[exact Preserved| ];split;[exact Load| ];split;assumption.
Qed.

Lemma SPobserved:forall c bs b M,SPpost c bs b M ->
 (forall a tp v,In(a,tp,v)(DOcells c) ->load tp M a=Some v) /\
 load(Tptr V293_tcb_type)M(10%positive,0%Z)=Some(Vptr OwnershipWaiting) /\
 get SCabs2 curtid=Some(oscurt OwnershipWaiting).
Proof.
 intros c bs b M Held;split.
 - intros a tp v Member;eapply DScells_load with(ge:=DWge)(le:=SPle b)
 (ir:=fun _:hid=>false)(aux:=(false,nil,[true]))(O:=SCabs2)(op:=spec_done None);[exact Member| ].
 unfold SPpost,SPowned,DGframe in Held;clear -Held;sep auto.
 - split;[exact(DGcurrent OwnershipWaiting (V293_owned_record_cell((b,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady) **DGframe c bs) (SPle b)M(fun _:hid=>false)(false,nil,[true])SCabs2 Held)|reflexivity].
Qed.
