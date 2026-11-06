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

Require Import CertiOS.audit.probes.V293TimeDlyReadyClosureProbe.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyOwnedSchedCall.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyFullCall.
Require Import CertiOS.certiucos.v293.proofs.V293TimeDlyGlobalSwitch.
Require Import CertiOS.certiucos.v293.proofs.V293TimeDlyCallEntry.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293ReadySchedCall.
Require Import CertiOS.certiucos.v293.proofs.V293TimeDlySchedCall.
Require Import CertiOS.certiucos.v293.proofs.V293TimeDlyEntry.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.certiucos.v293.code.V293OSSchedDispatch.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293ReadySourceTail.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCallGlobal.
Local Open Scope nat_scope.

Definition DOrest:=V293_owned_record_cells
 (cons ((90%positive,0%Z),Tint32,Vint32(Int.repr 99))
 (cons ((11%positive,0%Z),Tint8,V293_byteval 0)
 (cons ((12%positive,0%Z),Tint32,Vint32(Int.repr 3))nil))) **
 (Amapsto(13%positive,0%Z)Tint32 true(Vint32 Int.zero) **
 V293_read_bytes 80%positive 0%Z V293_ready_table).

Lemma DOrest_good:GoodInvAsrt DOrest.
Proof. unfold DOrest;vm_compute;repeat split;exact I. Qed.

Lemma DOentry:forall c enabled M,DRpost c enabled M ->
 (DWge,DCle,M,(fun _:hid=>false),(enabled,nil,nil),DEfinalabs(Int.repr 3),spec_done None)|=
 V293_ready_full 30%positive 31%positive 83%positive OwnershipReady **
 V293_owned_sched_frame 81%positive 82%positive 84%positive 85%positive
 70%positive 71%positive(V293_byteval 0)Vnull 4 c DOrest.
Proof.
 intros c enabled M Held;unfold DRpost,V293_dly_local_frame,DRresources,DRframe in Held.
 unfold V293_owned_sched_frame,DOrest;cbn[V293_owned_record_cells V293_dly_guard_cells]in Held|-*.
 clear -Held;sep auto.
Qed.

Lemma DOlookup:forall c enabled M,DRpost c enabled M ->forall n,n<256 ->
 load Tint8 M(80%positive,Z.of_nat n)=Some(V293_byteval(V293_ready_lookup n)).
Proof.
 intros c enabled M Held n Range.
 set(S:=(DWge,DCle,M,(fun _:hid=>false),(enabled,(nil:list hid),(nil:list bool)),DEfinalabs(Int.repr 3),spec_done None)).
 assert(Lookup:S|=V293_read_bytes 80%positive 0%Z V293_ready_table **Atrue)
 by(unfold S;unfold DRpost,V293_dly_local_frame,DRresources in Held;clear -Held;sep auto).
 change(load Tint8(getmem S)(80%positive,Z.of_nat n)=Some(V293_byteval(V293_ready_lookup n))).
 replace(Z.of_nat n)with(0+Z.of_nat n)%Z by lia.
 eapply V293_record_star_load_l;[apply V293_read_bytes_load|exact Lookup].
 - change(n<256);exact Range.
 - change(V293_ready_lookup n<256);pose proof(proj1(V293_ready_row_spec n Range));lia.
Qed.

Lemma DOselected:forall tasks lo hi entries next message,
 get(DEfinalabs(Int.repr 3))abstcblsid=Some(abstcblist tasks) ->
 V293_ready_rel lo hi entries tasks ->
 get tasks next=Some(Int.repr(Z.of_nat(V293_ready_select lo hi(V293_ready_group lo hi))),rdy,message) ->
 V293_ready_select lo hi(V293_ready_group lo hi)=6 /\next=OwnershipWaiting.
Proof.
 intros tasks lo hi entries next message Map Rel Task.
 change(Some(abstcblist(DEblocked(Int.repr 3)))=Some(abstcblist tasks))in Map.
 injection Map as Eq;subst tasks.
 assert(Range:V293_ready_select lo hi(V293_ready_group lo hi)<13).
 { destruct Rel as[Lo[Hi[Nonempty[Bitmap Table]]]];apply V293_ready_selection_range;assumption||reflexivity. }
 destruct(DStask_blocks _ _ _ _ Task)as[E|E];subst next.
 - change(Some(Int.repr 4,wait os_stat_time(Int.repr 3),Vnull)=Some(Int.repr(Z.of_nat(V293_ready_select lo hi(V293_ready_group lo hi))),rdy,message))in Task;discriminate.
 - change(Some(Int.repr 6,rdy,Vptr(120%positive,Int.repr 7))=
   Some(Int.repr(Z.of_nat(V293_ready_select lo hi(V293_ready_group lo hi))),rdy,message))in Task.
   assert(PriorityEqual:Int.repr 6=Int.repr(Z.of_nat(V293_ready_select lo hi(V293_ready_group lo hi))))by congruence.
   split;[apply V293_priority_repr_injective;[exact Range|lia|symmetry;exact PriorityEqual]|reflexivity].
Qed.

Definition DOcells c:list V293_record_cell:=
 cons ((81%positive,0%Z),Tint8,V293_byteval 6)
 (cons ((84%positive,0%Z),Tint8,V293_byteval 4)
 (cons ((85%positive,0%Z),Tint32,Vint32(Int.add c Int.one))
 (cons ((82%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipWaiting)
 (cons ((70%positive,0%Z),Tint8,V293_byteval 0)
 (cons ((71%positive,0%Z),Tint8,V293_byteval 0)
 (cons ((90%positive,0%Z),Tint32,Vint32(Int.repr 99))
 (cons ((11%positive,0%Z),Tint8,V293_byteval 0)
 (cons ((12%positive,0%Z),Tint32,Vint32(Int.repr 3))nil)))))))).
Definition DOpost c enabled bs Mf:=
 (DWge,V293_cpu_lenv 501%Z bs,Mf,(fun _:hid=>false),(false,nil,cons enabled nil),DEfinalabs(Int.repr 3),spec_done None)|=
 SWINVt(V293_ready_inv 30%positive 31%positive 83%positive)OwnershipReady **
 (V293_owned_record_cells(DOcells c) **
 (Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **
 (Amapsto(13%positive,0%Z)Tint32 true(Vint32 Int.zero) **
 V293_read_bytes 80%positive 0%Z V293_ready_table))).

Definition DOcontinuation:=kseq(sseq(sprim excrit)sret)
 (kcall 112%Z(V293_OSSched_success_body 501%Z 110%Z 111%Z 113%Z 117%Z 115%Z 116%Z 118%Z 119%Z)
 DCle(kseq sret kstop)).

Theorem DOglobal_sched:forall c enabled,exists bs byblock Mb Mi My Mh Mt Mf,
 DRrun c enabled Mb /\
 DRpost c enabled Mb /\
 DXrun c enabled bs Mf /\
 fresh Mb bs /\fresh Mi byblock /\
 free Tint8 byblock My=Some Mh /\get Mh(byblock,0%Z)=None /\
 cstepstar DAprogram
 (curs(V293_OSSched_unlocked_prefix 113%Z 117%Z 115%Z 116%Z),(kenil,kseq DSchange DOcontinuation))
 (DWge,V293_cpu_lenv 501%Z bs,Mi)
 (SKIP,(kenil,kseq DSchange DOcontinuation))(DWge,V293_cpu_lenv 501%Z bs,Mt) /\
 store Tint32 Mt(85%positive,0%Z)(Vint32(Int.add c Int.one))=Some Mf /\
 DOpost c enabled bs Mf /\
 load(Tptr V293_tcb_type)Mf(82%positive,0%Z)=Some(Vptr OwnershipWaiting) /\
 load Tint32 Mf(85%positive,0%Z)=Some(Vint32(Int.add c Int.one)).
Proof.
 intros c enabled;destruct(DRglobal_ready c enabled)as(Mb&Blocked&Step&Records&Table&Bitmap&Loads&Owned).
 destruct(V293_owned_sched_call 30%positive 31%positive 83%positive DAprogram(kseq sret kstop)
 DWge DCle Mb enabled nil(DEfinalabs(Int.repr 3))(spec_done None)OwnershipReady DOrest
 112%Z 501%Z 110%Z 111%Z 113%Z 117%Z 115%Z 116%Z 118%Z 119%Z 114%Z 105%Z 106%Z 500%Z
 80%positive 81%positive 82%positive 84%positive 85%positive 70%positive 71%positive
 (V293_byteval 0)Vnull 4 c eq_refl eq_refl ltac:(cbn;intuition congruence)
 ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)
 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(lia)DOrest_good
 (DOlookup c enabled Mb Owned)(DOentry c enabled Mb Owned))
 as(bs&byblock&Mi&My&Mh&Mt&Mf&tasks&lo&hi&entries&next&message&Fresh&FreshY&Map&Rel&Task&Scheduled&Prefix&Free&Removed&Counter&Final&Target&Count).
 destruct(DOselected _ _ _ _ _ _ Map Rel Task)as[Selected Next];subst next.
 rewrite Selected in Scheduled,Counter,Final,Count;cbn[Nat.eqb]in Scheduled,Counter,Final,Count.
 exists bs;exists byblock;exists Mb;exists Mi;exists My;exists Mh;exists Mt;exists Mf.
 split;[exact Blocked| ];split;[exact Owned| ];split.
 - unfold DXrun,DXinitial,DXcut,DAprog,DXclient.
   eapply V293_global_trans;[exact Blocked| ].
   pose proof(V293_local_function_extension DAprogram(pumerge DAprogram(fun _=>None))DXextends _ _ _ _ Scheduled)as Extended.
   eapply(V293_local_steps_global (fun _=>None)DAprogram(fun _=>None)(fun _=>None) _ _ _ _ Extended
   1200%Z DCbody emp kstop Tvoid(dcons 401%Z Tint32 dnil)(dcons 400%Z Tint8(dcons 402%Z Tint32 dnil))
   DAtasks(sig OwnershipWaiting DCle)(DWaux enabled)OwnershipReady((emp:env),DXcles,DXcm)eq_refl).
   exact I.
 - split;[exact Fresh| ];split;[exact FreshY| ];split;[exact Free| ];split;[exact Removed| ];split.
   + exact Prefix.
   + split;[exact Counter| ];split.
     * unfold DOpost,DOcells;unfold DOrest in Final;cbn[V293_owned_record_cells]in Final|-*;clear -Final;sep auto.
     * split;[exact Target|exact Count].
Qed.

Lemma DOobserved:forall c enabled bs Mf,DOpost c enabled bs Mf ->
 (forall a tp v,In(a,tp,v)(DOcells c) ->load tp Mf a=Some v) /\
 load Tint32 Mf(bs,0%Z)=Some(Vint32 Int.zero) /\
 V293_bytes_writable Mf bs 0%Z 4 /\
 load Tint32 Mf(13%positive,0%Z)=Some(Vint32 Int.zero) /\
 V293_bytes_writable Mf 13%positive 0%Z 4.
Proof.
 intros c enabled bs Mf Held.
 set(S:=(DWge,V293_cpu_lenv 501%Z bs,Mf,(fun _:hid=>false),
 (false,(nil:list hid),cons enabled nil),DEfinalabs(Int.repr 3),spec_done None)).
 assert(Cells:S|=V293_owned_record_cells(DOcells c) **Atrue)
 by(unfold S;unfold DOpost in Held;clear -Held;sep auto).
 assert(CPU:S|=Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **Atrue)
 by(unfold S;unfold DOpost in Held;clear -Held;sep auto).
 assert(OldCPU:S|=Amapsto(13%positive,0%Z)Tint32 true(Vint32 Int.zero) **Atrue)
 by(unfold S;unfold DOpost in Held;clear -Held;sep auto).
 split.
 - intros a tp v Member;eapply DScells_load;[exact Member|exact Cells].
 - split.
   + change(load Tint32(getmem S)(bs,0%Z)=Some(Vint32 Int.zero));apply DCraw_load;[reflexivity|exact CPU].
   + split.
     * eapply(V293_tick_raw_owned_writable bs Tint32(Vint32 Int.zero)Atrue
       DWge(V293_cpu_lenv 501%Z bs)Mf(fun _:hid=>false)(false,nil,cons enabled nil)
       (DEfinalabs(Int.repr 3))(spec_done None));exact CPU.
     * split.
       -- change(load Tint32(getmem S)(13%positive,0%Z)=Some(Vint32 Int.zero));apply DCraw_load;[reflexivity|exact OldCPU].
       -- eapply(V293_tick_raw_owned_writable 13%positive Tint32(Vint32 Int.zero)Atrue
          DWge(V293_cpu_lenv 501%Z bs)Mf(fun _:hid=>false)(false,nil,cons enabled nil)
          (DEfinalabs(Int.repr 3))(spec_done None));exact OldCPU.
Qed.

Theorem DOboth_IE:forall c,exists boff bon Moff Mon,
 DXrun c false boff Moff /\DOpost c false boff Moff /\
 DXrun c true bon Mon /\DOpost c true bon Mon /\
 V293_bytes_writable Moff boff 0%Z 4 /\V293_bytes_writable Mon bon 0%Z 4.
Proof.
 intro c;destruct(DOglobal_sched c false)as(boff&yo&Mbo&Mio&Myo&Mho&Mto&Moff&BOff&POff&Off&FO&FYO&FreeO&DeadO&CallO&CountO&OwnedO&TargetO&LoadO).
 destruct(DOglobal_sched c true)as(bon&yn&Mbn&Min&Myn&Mhn&Mtn&Mon&BOn&POn&On&FN&FYN&FreeN&DeadN&CallN&CountN&OwnedN&TargetN&LoadN).
 destruct(DOobserved c false boff Moff OwnedO)as(ObsO&CPUO&WO&OldO&WOldO).
 destruct(DOobserved c true bon Mon OwnedN)as(ObsN&CPUN&WN&OldN&WOldN).
 exists boff;exists bon;exists Moff;exists Mon.
 split;[exact Off| ];split;[exact OwnedO| ];split;[exact On| ];split;[exact OwnedN| ];split;assumption.
Qed.

Theorem DOwrap:exists bs Mf,
 DXrun(Int.repr Int.max_unsigned)true bs Mf /\
 DOpost(Int.repr Int.max_unsigned)true bs Mf /\
 load Tint32 Mf(85%positive,0%Z)=Some(Vint32 Int.zero).
Proof.
 destruct(DOglobal_sched(Int.repr Int.max_unsigned)true)as(bs&byblock&Mb&Mi&My&Mh&Mt&Mf&B&PO&Run&F&FY&Free&Dead&Call&Store&Owned&Target&Count).
 exists bs;exists Mf;split;[exact Run| ];split;[exact Owned| ];rewrite DWcounter_wrap in Count;exact Count.
Qed.

Lemma DOcounter_changes:forall c,Int.add c Int.one<>c.
Proof.
 intros c Eq.
 assert(Cancel:Int.add(Int.neg c)c=Int.zero).
 { rewrite Int.add_commut;apply Int.add_neg_zero. }
 assert(Contradiction:Int.add(Int.neg c)(Int.add c Int.one)=Int.add(Int.neg c)c)by(rewrite Eq;reflexivity).
 rewrite <-Int.add_assoc,Cancel,Int.add_zero_l in Contradiction;discriminate.
Qed.

Definition DOchosen_counter (observe:bool) (c:int32):=if observe then Int.add c Int.one else c.
Theorem DOlate_ablation:forall c enabled,exists bs byblock My Mh Mf,
 DXrun c enabled bs Mf /\DOpost c enabled bs Mf /\
 free Tint8 byblock My=Some Mh /\get Mh(byblock,0%Z)=None /\
 V293_bytes_writable Mf bs 0%Z 4 /\V293_bytes_writable Mf 13%positive 0%Z 4 /\
 load Tint32 Mf(90%positive,0%Z)=Some(Vint32(Int.repr 99)) /\
 load Tint32 Mf(85%positive,0%Z)=Some(Vint32(DOchosen_counter true c)) /\
 load Tint32 Mf(85%positive,0%Z)<>Some(Vint32(DOchosen_counter false c)).
Proof.
 intros c enabled;destruct(DOglobal_sched c enabled)as(bs&byblock&Mb&Mi&My&Mh&Mt&Mf&B&PO&Run&F&FY&Free&Dead&Call&Store&Owned&Target&Count).
 destruct(DOobserved c enabled bs Mf Owned)as(Obs&CPU&W&OldCPU&OldW).
 assert(Canary:load Tint32 Mf(90%positive,0%Z)=Some(Vint32(Int.repr 99)))
 by(apply Obs;cbn[DOcells In];tauto).
 exists bs;exists byblock;exists My;exists Mh;exists Mf.
 split;[exact Run| ];split;[exact Owned| ];split;[exact Free| ];split;[exact Dead| ];
 split;[exact W| ];split;[exact OldW| ];split;[exact Canary| ];split;[exact Count| ].
 unfold DOchosen_counter;rewrite Count;intro Eq;apply(DOcounter_changes c);congruence.
Qed.
