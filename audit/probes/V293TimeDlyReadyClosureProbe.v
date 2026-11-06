(* Constant client call, distinct heaps, one original global execution. *)
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

Definition DRframe c:list V293_record_cell:=
 cons ((90%positive,0%Z),Tint32,Vint32(Int.repr 99))
 (cons ((81%positive,0%Z),Tint8,V293_byteval 0)
 (cons ((82%positive,0%Z),Tptr V293_tcb_type,Vnull)
 (cons ((84%positive,0%Z),Tint8,V293_byteval 4)
 (cons ((85%positive,0%Z),Tint32,Vint32 c)nil)))).
Definition DRresources c:=V293_owned_record_cells(DRframe c) **
 V293_read_bytes 80%positive 0%Z V293_ready_table.
Definition DRpost c enabled Mf:=
 (DWge,DCle,Mf,(fun _:hid=>false),(enabled,nil,nil),DEfinalabs(Int.repr 3),spec_done None)|=
 V293_ready_full 30%positive 31%positive 83%positive OwnershipReady **
 V293_dly_local_frame 11%positive 12%positive 13%positive 70%positive 71%positive 4(Int.repr 3)(DRresources c).
Definition DRrun c enabled Mf:=V293_global_steps DAprog DXclient(DXinitial c enabled)
 (V293_local_global_at DAtasks(sig OwnershipWaiting DCle)(DWaux enabled)OwnershipReady
 (curs(scall 112%Z nil),(kenil,kseq sret DCouter))
 ((DWge,DCle,Mf),(fun _:hid=>false),(enabled,nil,nil))).

Lemma DRentry:forall c enabled,DAstate(DAmem false c)enabled DCabs|=
 V293_owned_record_cells DAinput **(V293_owned_record_cells DLextra **
 (V293_owned_task_records(del DLtasks OwnershipReady) **
 (V293_shared_fields OwnershipReady DLtasks(emp:EcbMod.map)(Int.repr 37) **
 (V293_owned_record_cells(V293_priority_cells 83%positive 0%Z DLentries) **DRresources c)))).
Proof.
 intros c enabled;pose proof(DAentry false c enabled)as Held.
 unfold DAresources,DAframe in Held.
 eapply astar_mono;[intros s H;exact H| |exact Held].
 intros s H;eapply astar_mono;[intros s' H';exact H'| |exact H].
 intros s' H';eapply astar_mono;[intros s'' H'';exact H''| |exact H'].
 intros s'' H'';eapply astar_mono;[intros s''' H''';exact H'''| |exact H''].
 intros st Owned.
 assert(Split:st|=(V293_owned_record_cells
 (cons ((90%positive,0%Z),Tint32,Vint32(Int.repr 99))
 (cons ((81%positive,0%Z),Tint8,V293_byteval 0)
 (cons ((82%positive,0%Z),Tptr V293_tcb_type,Vnull)nil))) **
 (V293_owned_record_cells(V293_priority_cells 83%positive 0%Z DLentries) **
 V293_owned_record_cells
 (cons ((84%positive,0%Z),Tint8,V293_byteval 4)
 (cons ((85%positive,0%Z),Tint32,Vint32 c)nil)))) **
 V293_read_bytes 80%positive 0%Z V293_ready_table).
 { eapply astar_mono;[ |intros u U1;exact U1|exact Owned].
   intros u U1;apply OwnershipCellsAppend in U1.
   eapply astar_mono;[intros v U2;exact U2| |exact U1].
   intros v U2;apply OwnershipCellsAppend in U2;exact U2. }
 unfold DRresources,DRframe;cbn[V293_owned_record_cells app]in Split|-*.
 clear -Split;sep auto.
Qed.

Theorem DRglobal_ready:forall c enabled,exists Mf,
 DRrun c enabled Mf /\
 spec_step(fun _ _=>False)(spec_prim(cons(Vint32(Int.repr 3))nil)V293_dly_block_step)
 DEabs(END None)(DEfinalabs(Int.repr 3)) /\
 V293_task_records Mf(DEblocked(Int.repr 3)) /\
 V293_priority_table DLentries(DEblocked(Int.repr 3)) /\
 V293_bitmap_tasks 64 0(DEblocked(Int.repr 3)) /\
 V293_ready_loads Mf 30%positive 31%positive 83%positive 64 0 DLentries /\DRpost c enabled Mf.
Proof.
 intros c enabled.
 destruct(V293_dly_global_call_ready (fun _=>None)DAprogram(fun _=>None)(fun _=>None)
 DAtasks(sig OwnershipWaiting DCle)(DWaux enabled)OwnershipReady
 (emp:env)DXcles DXcm DXcle DWge emp(DAmem false c)
 (fun _:hid=>false)enabled nil nil DCabs(spec_done None)(fun _ _=>False)(DRresources c)
 1200%Z 103%Z 106%Z 105%Z 400%Z 401%Z 110%Z 111%Z 112%Z 402%Z
 12%positive 11%positive 13%positive 10%positive 60%positive 30%positive 31%positive
 70%positive 71%positive 0%Z 4(Int.repr 3)Int.zero 80 0 DLentries DLtasks Vnull(emp:EcbMod.map)(Int.repr 37)83%positive
 eq_refl eq_refl ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)
 ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)
 (DAfresh false c 12%positive ltac:(tauto))(DAfresh false c 11%positive ltac:(tauto))
 (DAfresh false c 13%positive ltac:(tauto))DAenv eq_refl eq_refl eq_refl eq_refl
 ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(change(54<=4294967295)%Z;lia)
 eq_refl ltac:(exists 6;split;[lia|split;[lia|left;split;[lia|reflexivity]]])
 ltac:(discriminate)DLtable DLbitmap eq_refl(DRentry c enabled))
 as(Mf&Run&Step&Records&Table&Bitmap&Loads&Owned).
 exists Mf;split;[exact Run| ];split;[exact Step| ];split;[exact Records| ];
 split;[exact Table| ];split;[exact Bitmap| ];split;[exact Loads|exact Owned].
Qed.

Lemma DRcanary_cpu:forall c enabled Mf,DRpost c enabled Mf ->
 load Tint32 Mf(90%positive,0%Z)=Some(Vint32(Int.repr 99)) /\
 load Tint32 Mf(13%positive,0%Z)=Some(Vint32 Int.zero) /\
 V293_bytes_writable Mf 13%positive 0%Z 4.
Proof.
 intros c enabled Mf Held.
 set(S:=(DWge,DCle,Mf,(fun _:hid=>false),(enabled,(nil:list hid),(nil:list bool)),DEfinalabs(Int.repr 3),spec_done None)).
 assert(Frame:S|=V293_owned_record_cells(DRframe c) **Atrue)
 by(unfold S;unfold DRpost,V293_dly_local_frame,DRresources in Held;clear -Held;sep auto).
 assert(CPU:S|=Amapsto(13%positive,0%Z)Tint32 true(Vint32 Int.zero) **Atrue)
 by(unfold S;unfold DRpost,V293_dly_local_frame in Held;clear -Held;sep auto).
 split.
 - eapply DScells_load with(cells:=DRframe c);[left;reflexivity|exact Frame].
 - split.
   + change(load Tint32(getmem S)(13%positive,0%Z)=Some(Vint32 Int.zero)).
     apply DCraw_load;[reflexivity|exact CPU].
   + eapply(V293_tick_raw_owned_writable 13%positive Tint32(Vint32 Int.zero)Atrue
     DWge DCle Mf(fun _:hid=>false)(enabled,nil,nil)(DEfinalabs(Int.repr 3))(spec_done None));exact CPU.
Qed.

Theorem DRboth_IE:forall c,exists Moff Mon,
 DRrun c false Moff /\DRpost c false Moff /\
 DRrun c true Mon /\DRpost c true Mon /\
 load Tint32 Moff(90%positive,0%Z)=Some(Vint32(Int.repr 99)) /\
 load Tint32 Mon(90%positive,0%Z)=Some(Vint32(Int.repr 99)).
Proof.
 intro c;destruct(DRglobal_ready c false)as(Moff&Off&SO&RO&TO&BO&LO&PO).
 destruct(DRglobal_ready c true)as(Mon&On&SN&RN&TN&BN&LN&PN).
 exists Moff;exists Mon;split;[exact Off| ];split;[exact PO| ];
 split;[exact On| ];split;[exact PN| ];split;
 [exact(proj1(DRcanary_cpu c false Moff PO))|exact(proj1(DRcanary_cpu c true Mon PN))].
Qed.

(* Keep the physical run fixed; vary only the abstract correspondence map. *)
Definition DRchosen_tasks(commit:bool):=if commit then DEblocked(Int.repr 3)else DLtasks.
Lemma DRstale_bitmap:~V293_bitmap_tasks 64 0 DLtasks.
Proof.
 intro Bitmap;assert(Ready:V293_bitmap_ready 64 0 4).
 { apply(proj2(Bitmap 4 ltac:(lia)));exists OwnershipReady;exists Vnull;reflexivity. }
 destruct Ready as[[_ Bit]|[Impossible _]];[discriminate|lia].
Qed.

Theorem DRlate_ablation:forall c enabled,exists Mf,
 DRrun c enabled Mf /\DRpost c enabled Mf /\
 V293_ready_loads Mf 30%positive 31%positive 83%positive 64 0 DLentries /\
 V293_task_records Mf(DEblocked(Int.repr 3)) /\
 load Tint32 Mf(90%positive,0%Z)=Some(Vint32(Int.repr 99)) /\
 V293_bytes_writable Mf 13%positive 0%Z 4 /\
 V293_bitmap_tasks 64 0(DRchosen_tasks true) /\
 ~V293_bitmap_tasks 64 0(DRchosen_tasks false).
Proof.
 intros c enabled;destruct(DRglobal_ready c enabled)as(Mf&Run&Step&Records&Table&Bitmap&Loads&Owned).
 destruct(DRcanary_cpu c enabled Mf Owned)as(Canary&CPU&Writable).
 exists Mf;split;[exact Run| ];split;[exact Owned| ];split;[exact Loads| ];split;[exact Records| ];
 split;[exact Canary| ];split;[exact Writable| ];split;[exact Bitmap|exact DRstale_bitmap].
Qed.
