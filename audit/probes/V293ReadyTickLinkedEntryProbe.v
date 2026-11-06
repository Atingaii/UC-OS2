Require Import CertiOS.certiucos.v293.code.V293OSTimeTick.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
Require Import CertiOS.certiucos.v293.proofs.V293SharedStateWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293TimeDlyTaskBridge.
Require Import CertiOS.certiucos.v293.proofs.V293TimeDlyBlocking.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.audit.probes.V293TimeDlyEntryProbe.
Require Import CertiOS.audit.probes.V293TimeDlyBlockingProbe.
Require Import CertiOS.audit.probes.V293TimeDlyTaskBridgeProbe.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.
Require Import CertiOS.certiucos.v293.proofs.V293TimeDlyAllocated.
Require Import CertiOS.certiucos.v293.proofs.V293TimeDlyCallEntry.
Require Import CertiOS.audit.probes.V293TimeDlyCallEntryProbe.
Require Import CertiOS.audit.probes.V293TimeDlySwitchProbe.
Require Import CertiOS.audit.probes.V293TimeDlyAllocatedProbe.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyGlobalTrace.
Require Import CertiOS.certiucos.v293.proofs.V293LocalGlobalTrace.
Require Import CertiOS.certiucos.v293.code.V293OSTimeDlyCall.
Require Import Coq.Relations.Relation_Operators.
Require Import CertiOS.audit.probes.V293TimeDlyCallGlobalProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TimeDlyReadyClosure.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.audit.probes.V293TimeDlySchedCallProbe.
Require Import CertiOS.audit.probes.V293TimeDlyReadyClosureProbe.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTickLinkedEntry.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.certiucos.v293.proofs.V293SwitchedTickPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickCountdown.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickTaskBridge.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyOwnedSchedCall.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.framework.proof.memory_prop.

(* These cells exist at the client-call entry, not injected after switching.
   This is a resource fixture, not a proof of OS initialization. *)
Definition LHlinks:list V293_record_cell:=
 [((91%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady);
  ((60%positive,20%Z),Tcom_ptr 410%Z,Vptr OwnershipWaiting)].
Definition LHge:=set DWge 703%Z(91%positive,Tptr V293_tcb_type).
Definition LHframe c:=DAframe false c++LHlinks.
Definition LHsmall c:=DAinput++(DLextra++(DLlow++LHframe c)).
Definition LHmem c:=merge(OwnershipCellsMemory(LHsmall c))DSlookup.
Definition LHstate M enabled O:RstateOP:=(LHge,DCle,M,(fun _=>false),(enabled,nil,nil),O,spec_done None).
Definition LHinitial c enabled:=V293_local_global_at DAtasks(sig OwnershipWaiting DCle)(DWaux enabled)
 OwnershipReady(curs(scall 1200%Z[econst32(Int.repr 3)]),(kenil,kstop))
 ((LHge,emp,LHmem c),(fun _:hid=>false),(enabled,nil,nil)).
Definition LHresources c:=V293_owned_record_cells(DRframe c++LHlinks) **
 V293_read_bytes 80%positive 0%Z V293_ready_table.
Definition LHpost c enabled M:=
 LHstate M enabled(DEfinalabs(Int.repr 3))|=
 V293_ready_full 30%positive 31%positive 83%positive OwnershipReady **
 V293_dly_local_frame 11%positive 12%positive 13%positive 70%positive 71%positive 4(Int.repr 3)(LHresources c).
Definition LHrun c enabled M:=V293_global_steps DAprog DXclient(LHinitial c enabled)
 (V293_local_global_at DAtasks(sig OwnershipWaiting DCle)(DWaux enabled)OwnershipReady
 (curs(scall 112%Z nil),(kenil,kseq sret DCouter))
 ((LHge,DCle,M),(fun _:hid=>false),(enabled,nil,nil))).
Lemma LHsmall_spatial:forall c,LHstate(OwnershipCellsMemory(LHsmall c))false emp|=
 V293_owned_record_cells(LHsmall c).
Proof.
 intro c;apply OwnershipCellsSpatial.
 - apply DSseparated_sound;vm_compute;reflexivity.
 - repeat constructor;vm_compute;reflexivity.
Qed.
Lemma LHjoin:forall c,join(OwnershipCellsMemory(LHsmall c))DSlookup(LHmem c).
Proof.
 intro c;apply map_join_merge;apply map_disjoint;intros[b i].
 destruct(Pos.eq_dec b 80%positive)as[Same|Other].
 - subst b;left;apply OwnershipCellsOutside;vm_compute;
   intro H;repeat destruct H as[H|H];congruence.
 - right;left;unfold DSlookup,V293_nat_memory;apply V293_encoded_memory_outside;left;exact Other.
Qed.
Definition LHrawresources c:=V293_owned_record_cells(LHframe c) **
 V293_read_bytes 80%positive 0%Z V293_ready_table.
Lemma LHentry_raw:forall c enabled,LHstate(LHmem c)enabled DCabs|=
 V293_owned_record_cells DAinput **(V293_owned_record_cells DLextra **
 (V293_owned_task_records(del DLtasks OwnershipReady) **
 (V293_shared_fields OwnershipReady DLtasks(emp:EcbMod.map)(Int.repr 37) **LHrawresources c))).
Proof.
 intros c enabled;pose proof(LHsmall_spatial c)as Cells.
 apply(proj1(OwnershipCellsAppend DAinput(DLextra++(DLlow++LHframe c))_))in Cells.
 assert(Physical:V293_target_wstate LHge DCle(OwnershipCellsMemory(LHsmall c))emp|=
 V293_owned_record_cells DAinput **(V293_owned_record_cells DLextra **
 (V293_owned_record_cells DLlow **V293_owned_record_cells(LHframe c)))).
 { eapply astar_mono;[intros st H;exact H| |exact Cells].
   intros st H;apply OwnershipCellsAppend in H.
   eapply astar_mono;[intros st' H';exact H'| |exact H].
   intros st' H';apply OwnershipCellsAppend in H';exact H'. }
 assert(WithLookup:V293_target_wstate LHge DCle(LHmem c)emp|=
 (V293_owned_record_cells DAinput **(V293_owned_record_cells DLextra **
 (V293_owned_record_cells DLlow **V293_owned_record_cells(LHframe c)))) **
 V293_read_bytes 80%positive 0%Z V293_ready_table).
 { eapply V293_wstate_star;[apply LHjoin|exact Physical|apply V293_read_bytes_witness]. }
 assert(Joint:V293_target_wstate LHge DCle(LHmem c)DCabs|=
 ((V293_owned_record_cells DAinput **(V293_owned_record_cells DLextra **
 (V293_owned_record_cells DLlow **V293_owned_record_cells(LHframe c)))) **
 V293_read_bytes 80%positive 0%Z V293_ready_table) **
 V293_shared_fields OwnershipReady DLtasks(emp:EcbMod.map)(Int.repr 37)).
 { eapply V293_target_wstate_star with(m1:=LHmem c)(m2:=emp)(o1:=emp)(o2:=DCabs).
   - apply map_join_emp.
   - apply map_join_comm;apply map_join_emp.
   - exact WithLookup.
   - exact(V293_shared_fixture_fields OwnershipReady DLtasks(emp:EcbMod.map)(Int.repr 37)). }
 assert(Reordered:V293_target_wstate LHge DCle(LHmem c)DCabs|=V293_owned_record_cells DAinput **
 (V293_owned_record_cells DLextra **(V293_owned_record_cells DLlow **
 (V293_shared_fields OwnershipReady DLtasks(emp:EcbMod.map)(Int.repr 37) **LHrawresources c))))
 by(unfold LHrawresources;clear -Joint;sep auto).
 change(LHstate(LHmem c)enabled DCabs|=V293_owned_record_cells DAinput **
 (V293_owned_record_cells DLextra **(V293_owned_record_cells DLlow **
 (V293_shared_fields OwnershipReady DLtasks(emp:EcbMod.map)(Int.repr 37) **LHrawresources c))))in Reordered.
 eapply astar_mono;[intros st H;exact H| |exact Reordered].
 intros st H;eapply astar_mono;[intros st' H';exact H'| |exact H].
 intros st' H';eapply astar_mono;[apply DTlow_owned|intros st'' H'';exact H''|exact H'].
Qed.
Lemma LHentry:forall c enabled,LHstate(LHmem c)enabled DCabs|=
 V293_owned_record_cells DAinput **(V293_owned_record_cells DLextra **
 (V293_owned_task_records(del DLtasks OwnershipReady) **
 (V293_shared_fields OwnershipReady DLtasks(emp:EcbMod.map)(Int.repr 37) **
 (V293_owned_record_cells(V293_priority_cells 83%positive 0%Z DLentries) **LHresources c)))).
Proof.
 intros c enabled;pose proof(LHentry_raw c enabled)as Held.
 unfold LHrawresources,LHframe in Held.
 eapply astar_mono;[intros s H;exact H| |exact Held].
 intros s H;eapply astar_mono;[intros s' H';exact H'| |exact H].
 intros s' H';eapply astar_mono;[intros s'' H'';exact H''| |exact H'].
 intros s'' H'';eapply astar_mono;[intros s''' H''';exact H'''| |exact H''].
 intros st Input.
 assert(Separate:st|=(V293_owned_record_cells(DAframe false c) **V293_owned_record_cells LHlinks) **
 V293_read_bytes 80%positive 0%Z V293_ready_table).
 { eapply astar_mono;[ |intros u L0;exact L0|exact Input].
   intros u L1;apply OwnershipCellsAppend in L1;exact L1. }
 assert(Owned:st|=V293_owned_record_cells(DAframe false c) **
 (V293_owned_record_cells LHlinks **V293_read_bytes 80%positive 0%Z V293_ready_table))
 by(clear -Separate;sep auto).
 unfold DAframe in Owned.
 assert(Split:st|=(V293_owned_record_cells
 (cons ((90%positive,0%Z),Tint32,Vint32(Int.repr 99))
 (cons ((81%positive,0%Z),Tint8,V293_byteval 0)
 (cons ((82%positive,0%Z),Tptr V293_tcb_type,Vnull)nil))) **
 (V293_owned_record_cells(V293_priority_cells 83%positive 0%Z DLentries) **
 V293_owned_record_cells
 (cons ((84%positive,0%Z),Tint8,V293_byteval 4)
 (cons ((85%positive,0%Z),Tint32,Vint32 c)nil)))) **
 (V293_owned_record_cells LHlinks **V293_read_bytes 80%positive 0%Z V293_ready_table)).
 { eapply astar_mono;[ |intros u U1;exact U1|exact Owned].
   intros u U1;apply OwnershipCellsAppend in U1.
   eapply astar_mono;[intros v U2;exact U2| |exact U1].
   intros v U2;apply OwnershipCellsAppend in U2;exact U2. }
 unfold LHresources,DRframe;
cbn[V293_owned_record_cells app]in Split|-*.
 clear -Split;sep auto.
Qed.
Lemma LHfresh:forall c b,b=11%positive \/b=12%positive \/b=13%positive ->fresh(LHmem c)b.
Proof.
 intros c b Choice l i E[v Bound];subst l.
 change(get(LHmem c)(b,i)=Some v)in Bound.
 assert(Absent:get(LHmem c)(b,i)=None).
 { unfold LHmem;rewrite map_merge_semp by reflexivity.
   rewrite OwnershipCellsOutside.
   - assert(L:get DSlookup(b,i)=None).
     { unfold DSlookup,V293_nat_memory;apply V293_encoded_memory_outside;left;intuition congruence. }
     rewrite L;reflexivity.
   - destruct Choice as[Same|[Same|Same]];subst b;vm_compute;
     intro H;repeat destruct H as[H|H];congruence. }
 congruence.
Qed.
Lemma LHenv:V293_dly_env 103%Z 106%Z 105%Z 400%Z 401%Z
 10%positive 11%positive 12%positive 30%positive 31%positive LHge DCle.
Proof. repeat split;reflexivity. Qed.
Theorem LHglobal_ready:forall c enabled,exists Mf,
 LHrun c enabled Mf /\
 spec_step(fun _ _=>False)(spec_prim(cons(Vint32(Int.repr 3))nil)V293_dly_block_step)
 DEabs(END None)(DEfinalabs(Int.repr 3)) /\
 V293_task_records Mf(DEblocked(Int.repr 3)) /\
 V293_priority_table DLentries(DEblocked(Int.repr 3)) /\
 V293_bitmap_tasks 64 0(DEblocked(Int.repr 3)) /\
 V293_ready_loads Mf 30%positive 31%positive 83%positive 64 0 DLentries /\LHpost c enabled Mf.
Proof.
 intros c enabled.
 destruct(V293_dly_global_call_ready (fun _=>None)DAprogram(fun _=>None)(fun _=>None)
 DAtasks(sig OwnershipWaiting DCle)(DWaux enabled)OwnershipReady
 (emp:env)DXcles DXcm DXcle LHge emp(LHmem c)
 (fun _:hid=>false)enabled nil nil DCabs(spec_done None)(fun _ _=>False)(LHresources c)
 1200%Z 103%Z 106%Z 105%Z 400%Z 401%Z 110%Z 111%Z 112%Z 402%Z
 12%positive 11%positive 13%positive 10%positive 60%positive 30%positive 31%positive
 70%positive 71%positive 0%Z 4(Int.repr 3)Int.zero 80 0 DLentries DLtasks Vnull(emp:EcbMod.map)(Int.repr 37)83%positive
 eq_refl eq_refl ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)
 ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)
 (LHfresh c 12%positive ltac:(tauto))(LHfresh c 11%positive ltac:(tauto))
 (LHfresh c 13%positive ltac:(tauto))LHenv eq_refl eq_refl eq_refl eq_refl
 ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(change(54<=4294967295)%Z;lia)
 eq_refl ltac:(exists 6;split;[lia|split;[lia|left;split;[lia|reflexivity]]])
 ltac:(discriminate)DLtable DLbitmap eq_refl(LHentry c enabled))
 as(Mf&Run&Step&Records&Table&Bitmap&Loads&Owned).
 exists Mf;split;[exact Run| ];split;[exact Step| ];split;[exact Records| ];
 split;[exact Table| ];split;[exact Bitmap| ];split;[exact Loads|exact Owned].
Qed.


Definition LHle b:env:=set(emp:env)700%Z(b,Tptr V293_tcb_type).
Definition LHtail c:=V293_dly_local_frame 11%positive 12%positive 13%positive
 70%positive 71%positive 4(Int.repr 3)(DRresources c).
Definition LHrest c:=V293_owned_record_cell((91%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady) **LHtail c.
Definition LHowned c b aux O scan M:=
 (LHge,LHle b,M,(fun _:hid=>false),aux,O,spec_done None)|=
 V293_ready_full 30%positive 31%positive 83%positive OwnershipReady **
 (V293_owned_record_cell((b,0%Z),Tptr V293_tcb_type,Vptr scan) **
 (V293_owned_record_cell((60%positive,20%Z),Tcom_ptr 410%Z,Vptr OwnershipWaiting) **LHrest c)).
Definition LHprepared c b enabled M:=LHowned c b(enabled,nil,nil)(DEfinalabs(Int.repr 3))OwnershipReady M.
Definition LHtasks2:=set(DEblocked(Int.repr 3))OwnershipReady(Int.repr 4,wait os_stat_time(Int.repr 2),Vnull).
Definition LHabs2:=set(DEfinalabs(Int.repr 3))abstcblsid(abstcblist LHtasks2).
Definition LHposttick c b enabled M:=LHowned c b(enabled,nil,nil)LHabs2 OwnershipWaiting M.
Definition LHsetup b M Mp:=
 fresh M b /\
 alloc 700%Z(Tptr V293_tcb_type)(emp:env)M(LHle b)
 (allocb M b 0%Z(typelen(Tptr V293_tcb_type))) /\
 cstep DAprogram(curs(salloc nil(dcons 700%Z(Tptr V293_tcb_type)dnil)),(kenil,kstop))
 (LHge,(emp:env),M)(curs(salloc nil dnil),(kenil,kstop))
 (LHge,LHle b,allocb M b 0%Z(typelen(Tptr V293_tcb_type))) /\
 store(Tptr V293_tcb_type)(allocb M b 0%Z(typelen(Tptr V293_tcb_type)))
 (b,0%Z)(Vptr OwnershipReady)=Some Mp /\
 cstepstar DAprogram(curs(sassign(evar 700%Z)(evar 703%Z)),(kenil,kstop))
 (LHge,LHle b,allocb M b 0%Z(typelen(Tptr V293_tcb_type)))
 (curs(sskip None),(kenil,kstop))(LHge,LHle b,Mp).
Lemma LHrest_good:forall c,GoodInvAsrt(LHrest c).
Proof. intro c;unfold LHrest,LHtail,V293_dly_local_frame,DRresources,DRframe;vm_compute;repeat split;exact I. Qed.

(* The global prefix stops at its original scheduling cutpoint. Allocation
   and the source head assignment below are separate local executions. *)
Lemma LHprepare:forall c enabled M,LHpost c enabled M ->exists b Mp,
 LHsetup b M Mp /\LHprepared c b enabled Mp.
Proof.
 intros c enabled M Held;destruct(fresh_exist M)as[b Fresh].
 assert(Frame:(LHge,LHle b,M,(fun _:hid=>false),(enabled,nil,nil),DEfinalabs(Int.repr 3),spec_done None)|=
 V293_owned_record_cell((91%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady) **
 (V293_ready_full 30%positive 31%positive 83%positive OwnershipReady **
 (V293_owned_record_cell((60%positive,20%Z),Tcom_ptr 410%Z,Vptr OwnershipWaiting) **LHtail c))).
 { assert(Same:(LHge,DCle,M,(fun _:hid=>false),(enabled,nil,nil),DEfinalabs(Int.repr 3),spec_done None)|=
   V293_owned_record_cell((91%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady) **
   (V293_ready_full 30%positive 31%positive 83%positive OwnershipReady **
   (V293_owned_record_cell((60%positive,20%Z),Tcom_ptr 410%Z,Vptr OwnershipWaiting) **LHtail c))).
   { unfold LHpost,LHstate,V293_dly_local_frame,LHresources,DRframe,LHlinks in Held.
     unfold LHtail,V293_dly_local_frame,DRresources,DRframe.
     cbn[V293_owned_record_cells app]in Held|-*;clear -Held;sep auto. }
   eapply good_inv_prop;[ |exact Same].
   split;[split;exact I|split;[apply V293_owned_ready_good|split;[split;exact I| ]]].
   unfold LHtail,V293_dly_local_frame,DRresources,DRframe;vm_compute;repeat split;exact I. }
 assert(Unbound:~indom(emp:env)700%Z).
 { intros[v Bad];rewrite map_emp_get in Bad;discriminate. }
 destruct(V293_tick_scan_allocation DAprogram kstop dnil LHge(emp:env)M
 (fun _:hid=>false)(enabled,nil,nil)(DEfinalabs(Int.repr 3))(spec_done None)700%Z b _ Fresh Unbound Frame)
 as(Allocate&Execute&Raw&Undef).
 destruct(V293_ready_tick_head_execution DAprogram kstop LHge(LHle b)
 (allocb M b 0%Z(typelen(Tptr V293_tcb_type)))(fun _:hid=>false)(enabled,nil,nil)
 (DEfinalabs(Int.repr 3))(spec_done None)700%Z 703%Z b 91%positive Vundef OwnershipReady _
 eq_refl eq_refl eq_refl Raw)as(Mp&Store&Head&Owned&Read&Outside).
 exists b;exists Mp;split.
 - split;[exact Fresh| ];split;[exact Allocate| ];split;[exact Execute| ];
   split;[exact Store|exact Head].
 - unfold LHprepared,LHowned,LHrest;clear -Owned;sep auto.
Qed.
Definition LHexecution b enabled M Mf:=
 V293_local_steps DAprogram(curs(V293_tick_iteration 700%Z 701%Z 702%Z),(kenil,kstop))
 ((LHge,LHle b,M),(fun _:hid=>false),(enabled,nil,nil))
 (curs(sskip None),(kenil,kstop))((LHge,LHle b,Mf),(fun _:hid=>false),(enabled,nil,nil)).
Theorem LHiteration:forall c b enabled M,LHprepared c b enabled M ->exists Md Mf,
 store Tint32 M(60%positive,44%Z)(Vint32(Int.repr 2))=Some Md /\
 store(Tptr V293_tcb_type)Md(b,0%Z)(Vptr OwnershipWaiting)=Some Mf /\
 LHexecution b enabled M Mf /\
 spec_step V293_scheduler(spec_prim nil(V293_tick_wait_step OwnershipReady))
 (DEfinalabs(Int.repr 3))(END None)LHabs2 /\
 LHposttick c b enabled Mf /\
 load Tint32 Mf(60%positive,44%Z)=Some(Vint32(Int.repr 2)) /\
 load(Tptr V293_tcb_type)Mf(b,0%Z)=Some(Vptr OwnershipWaiting) /\
 (forall x i,(x<>60%positive \/(i<44)%Z \/(48<=i)%Z) ->
 (x<>b \/(i<0)%Z \/(4<=i)%Z) ->get Mf(x,i)=get M(x,i)).
Proof.
 intros c b enabled M Held.
 exact(V293_ready_countdown_linked_iteration 30%positive 31%positive 83%positive OwnershipReady
 (DEblocked(Int.repr 3))60%positive 0(Int.repr 4)3 Vnull(LHrest c)DAprogram kstop
 LHge(LHle b)M(fun _:hid=>false)enabled nil nil(DEfinalabs(Int.repr 3))(spec_done None)V293_scheduler
 700%Z 701%Z 702%Z b OwnershipWaiting eq_refl ltac:(lia)ltac:(change(44<=4294967295)%Z;lia)
 ltac:(change(2<=3<=4294967295)%Z;lia)eq_refl eq_refl(LHrest_good c)Held).
Qed.

(* Single statement ablation, fixed before implementation in protocol.json. *)
Definition LHmutant_iteration ptcb rows group:=sseq(sprim encrit)
 (sseq(V293_tick_delay ptcb rows group)(sseq(sskip None)(sprim excrit))).
Definition LHmutant_execution b enabled M Mf:=
 V293_local_steps DAprogram(curs(LHmutant_iteration 700%Z 701%Z 702%Z),(kenil,kstop))
 ((LHge,LHle b,M),(fun _:hid=>false),(enabled,nil,nil))
 (curs(sskip None),(kenil,kstop))((LHge,LHle b,Mf),(fun _:hid=>false),(enabled,nil,nil)).
Theorem LHmutant_late_gate:forall c b enabled M,LHprepared c b enabled M ->exists Mf,
 LHmutant_execution b enabled M Mf /\
 spec_step V293_scheduler(spec_prim nil(V293_tick_wait_step OwnershipReady))
 (DEfinalabs(Int.repr 3))(END None)LHabs2 /\
 LHowned c b(enabled,nil,nil)LHabs2 OwnershipReady Mf /\
 load Tint32 Mf(60%positive,44%Z)=Some(Vint32(Int.repr 2)) /\
 load(Tptr V293_tcb_type)Mf(b,0%Z)=Some(Vptr OwnershipReady) /\
 ~LHposttick c b enabled Mf.
Proof.
 intros c b enabled M Held.
 set(R:=V293_owned_record_cell((60%positive,20%Z),Tcom_ptr 410%Z,Vptr OwnershipWaiting) **LHrest c).
 assert(Good:GoodInvAsrt R)by(split;[split;exact I|apply LHrest_good]).
 assert(Disabled:LHowned c b(false,nil,[enabled])(DEfinalabs(Int.repr 3))OwnershipReady M).
 { eapply good_inv_prop;[split;[apply V293_owned_ready_good|split;[split;exact I|exact Good]]|exact Held]. }
 destruct(V293_ready_countdown_delay_execution 30%positive 31%positive 83%positive OwnershipReady
 (DEblocked(Int.repr 3))60%positive 0(Int.repr 4)3 Vnull R DAprogram
 (kseq(sseq(sskip None)(sprim excrit))kstop)LHge(LHle b)M(fun _:hid=>false)(false,nil,[enabled])
 (DEfinalabs(Int.repr 3))(spec_done None)V293_scheduler 700%Z 701%Z 702%Z b
 eq_refl ltac:(lia)ltac:(change(44<=4294967295)%Z;lia)
 ltac:(change(2<=3<=4294967295)%Z;lia)eq_refl eq_refl Disabled)
 as(Mf&Store&DelayExecution&Abstract&After&Delay&Outside).
 assert(Returned:LHowned c b(enabled,nil,nil)LHabs2 OwnershipReady Mf).
 { eapply good_inv_prop;[split;[apply V293_owned_ready_good|split;[split;exact I|exact Good]]|exact After]. }
 assert(Pointer:load(Tptr V293_tcb_type)Mf(b,0%Z)=Some(Vptr OwnershipReady)).
 { assert(Cell:(LHge,LHle b,Mf,(fun _:hid=>false),(enabled,nil,nil),LHabs2,spec_done None)|=
 V293_owned_record_cell((b,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady) **Atrue)
 by(unfold LHowned in Returned;clear -Returned;sep auto).
 exact(V293_record_star_load_l _ _ _ _ _ (V293_owned_record_cell_load _ _ _) _ Cell). }
 exists Mf;split.
 - unfold LHmutant_execution,LHmutant_iteration.
   eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sseq_step]| ].
   eapply V293_local_cons;[apply encrit_step;reflexivity| ].
   eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sskip_step]| ].
   eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sseq_step]| ].
   eapply V293_local_trans;[apply V293_csteps_local;exact DelayExecution| ].
   eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sskip_step]| ].
   eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sseq_step]| ].
   eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sskip_step]| ].
   eapply V293_local_cons;[apply excrit_step;reflexivity|apply V293_local_refl].
 - split;[exact Abstract| ];split;[exact Returned| ];split;[exact Delay| ];split;[exact Pointer| ].
   intro Expected.
   assert(Cell:(LHge,LHle b,Mf,(fun _:hid=>false),(enabled,nil,nil),LHabs2,spec_done None)|=
   V293_owned_record_cell((b,0%Z),Tptr V293_tcb_type,Vptr OwnershipWaiting) **Atrue)
   by(unfold LHposttick,LHowned in Expected;clear -Expected;sep auto).
   pose proof(V293_record_star_load_l _ _ _ _ _ (V293_owned_record_cell_load _ _ _) _ Cell)as Next.
   change(load(Tptr V293_tcb_type)Mf(b,0%Z)=Some(Vptr OwnershipWaiting))in Next.
   rewrite Pointer in Next;discriminate.
Qed.

Theorem LHsame_input_ablation:forall c enabled,exists M b Mp Md Mf Mmut,
 LHrun c enabled M /\LHpost c enabled M /\
 LHsetup b M Mp /\LHprepared c b enabled Mp /\
 LHexecution b enabled Mp Mf /\LHposttick c b enabled Mf /\
 LHmutant_execution b enabled Mp Mmut /\
 LHowned c b(enabled,nil,nil)LHabs2 OwnershipReady Mmut /\
 store Tint32 Mp(60%positive,44%Z)(Vint32(Int.repr 2))=Some Md /\
 load Tint32 Mf(60%positive,44%Z)=Some(Vint32(Int.repr 2)) /\
 load Tint32 Mmut(60%positive,44%Z)=Some(Vint32(Int.repr 2)) /\
 load(Tptr V293_tcb_type)Mf(b,0%Z)=Some(Vptr OwnershipWaiting) /\
 load(Tptr V293_tcb_type)Mmut(b,0%Z)=Some(Vptr OwnershipReady) /\
 ~LHposttick c b enabled Mmut.
Proof.
 intros c enabled;destruct(LHglobal_ready c enabled)as(M&Run&Step&Records&Table&Bitmap&Loads&Post).
 destruct(LHprepare c enabled M Post)as(b&Mp&Setup&Prepared).
 destruct(LHiteration c b enabled Mp Prepared)as(Md&Mf&Dec&Next&Execute&Abstract&Final&Delay&Read&Outside).
 destruct(LHmutant_late_gate c b enabled Mp Prepared)as(Mmut&Mutant&AbsMut&Preserved&DelayMut&PointerMut&Reject).
 exists M;exists b;exists Mp;exists Md;exists Mf;exists Mmut.
 split;[exact Run| ];split;[exact Post| ];split;[exact Setup| ];split;[exact Prepared| ];
 split;[exact Execute| ];split;[exact Final| ];split;[exact Mutant| ];split;[exact Preserved| ];
 split;[exact Dec| ];split;[exact Delay| ];split;[exact DelayMut| ];split;[exact Read| ];split;assumption.
Qed.
