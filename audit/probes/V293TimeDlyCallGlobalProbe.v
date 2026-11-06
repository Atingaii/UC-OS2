(* Constant client call, distinct heaps, one original global execution. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeDlySchedCall.
Require Import CertiOS.certiucos.v293.proofs.V293TimeDlySwitch.
Require Import CertiOS.audit.probes.V293TimeDlySchedCallProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TimeDlyEntry.
Require Import CertiOS.certiucos.v293.proofs.V293TimeDlyTaskBridge.
Require Import CertiOS.certiucos.v293.proofs.V293TimeDlyBlocking.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293SharedStateWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyFullCall.
Require Import CertiOS.certiucos.v293.proofs.V293ReadySchedCall.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
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
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPointerCompare.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Require Import CertiOS.certiucos.v293.proofs.V293TimeDlyAllocated.
Require Import CertiOS.certiucos.v293.proofs.V293TimeDlyTail.
Require Import CertiOS.certiucos.v293.proofs.V293TimeDlyCallEntry.
Require Import CertiOS.audit.probes.V293TimeDlyCallEntryProbe.
Require Import CertiOS.audit.probes.V293TimeDlySwitchProbe.

Require Import CertiOS.audit.probes.V293TimeDlyAllocatedProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TimeDlyCallGlobal.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCallGlobal.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyGlobalTrace.
Require Import CertiOS.certiucos.v293.proofs.V293LocalGlobalTrace.
Require Import CertiOS.certiucos.v293.proofs.V293TimeDlyGlobalSwitch.
Require Import CertiOS.certiucos.v293.code.V293OSTimeDlyCall.
Require Import CertiOS.framework.proof.join_prop.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import Coq.Relations.Relation_Operators.
Local Open Scope nat_scope.
Import ListNotations.

Definition DXcle:env:=set emp 777%Z(12%positive,Tint32).
Definition DXcles:cltenvs:=sig OwnershipReady DXcle.
Definition DXcm:mem:=OwnershipCellsMemory (cons ((12%positive,0%Z),Tint32,Vint32(Int.repr 99)) nil).
Definition DXclient:clientst:=(emp,DXcles,DXcm).
Definition DXinitial c enabled:=V293_local_global_at DAtasks(sig OwnershipWaiting DCle)(DWaux enabled)
 OwnershipReady(curs(scall 1200%Z[econst32(Int.repr 3)]),(kenil,kstop))
 ((DWge,emp,DAmem false c),(fun _:hid=>false),(enabled,nil,nil)).
Definition DXcut enabled bs Mf:=V293_local_global_at DAtasks(sig OwnershipWaiting DCle)(DWaux enabled)
 OwnershipReady(curs(sprim(switch 116%Z)),(kenil,DAcontinuation))
 ((DWge,V293_cpu_lenv 501%Z bs,Mf),(fun _:hid=>false),(false,nil,[enabled])).
Definition DXrun c enabled bs Mf:=V293_global_steps DAprog DXclient(DXinitial c enabled)(DXcut enabled bs Mf).

Lemma DXclient_alias:
 load Tint32 DXcm(12%positive,0%Z)=Some(Vint32(Int.repr 99)) /\
 get DXcles OwnershipReady=Some DXcle /\get DXcle 777%Z=Some(12%positive,Tint32) /\
 get(emp:env)777%Z=None /\get(emp:env)103%Z=None /\
 get DWge 103%Z=Some(10%positive,Tptr V293_tcb_type).
Proof.
 split.
 - assert(Owned:V293_wstate emp emp DXcm|=V293_owned_record_cells
   (cons((12%positive,0%Z),Tint32,Vint32(Int.repr 99))nil)).
   { apply OwnershipCellsSpatial.
     - split;[intros a H Contra;exact Contra|exact I].
     - repeat constructor;reflexivity. }
   change(load Tint32(getmem(V293_wstate emp emp DXcm))(12%positive,0%Z)=Some(Vint32(Int.repr 99))).
   eapply(V293_record_star_load_l(V293_owned_record_cells
   (cons((12%positive,0%Z),Tint32,Vint32(Int.repr 99))nil))Atrue);
   [apply V293_owned_record_cells_load;cbn;tauto| ].
   clear -Owned;sep auto.
 - repeat split;reflexivity.
Qed.

Lemma DXextends:forall f fn,DAprogram f=Some fn ->pumerge DAprogram(fun _=>None)f=Some fn.
Proof. intros f fn Bound;unfold pumerge;rewrite Bound;reflexivity. Qed.

Theorem DXglobal_run:forall c enabled,exists bs byblock Mf,
 DXrun c enabled bs Mf /\
 spec_step(fun _ _=>False)(spec_prim(cons(Vint32(Int.repr 3))nil)V293_dly_block_step)
 DEabs(END None)(DEfinalabs(Int.repr 3)) /\
 V293_task_records Mf(DEblocked(Int.repr 3)) /\
 V293_bitmap_tasks 64 0(DEblocked(Int.repr 3)) /\
 load Tint8 Mf(81%positive,0%Z)=Some(V293_byteval 6) /\
 load(Tptr V293_tcb_type)Mf(82%positive,0%Z)=Some(Vptr(DStarget false)) /\
 load Tint32 Mf(85%positive,0%Z)=Some(Vint32(Int.add c Int.one)) /\
 load Tint8 Mf(84%positive,0%Z)=Some(V293_byteval 4) /\
 V293_bytes_writable Mf 10%positive 0%Z 4 /\
 load Tint32 Mf(90%positive,0%Z)=Some(Vint32(Int.repr 99)) /\
 V293_bytes_writable Mf bs 0%Z 4 /\get Mf(byblock,0%Z)=None /\bs<>10%positive /\DAfacts Mf.
Proof.
 intros c enabled.
 destruct(V293_dly_global_call_to_sched_refines (fun _=>None)DAprogram(fun _=>None)(fun _=>None)
 DAtasks(sig OwnershipWaiting DCle)(DWaux enabled)OwnershipReady
 (emp:env)DXcles DXcm DXcle DWge emp(DAmem false c)
 (fun _:hid=>false)enabled nil nil DCabs(spec_done None)(fun _ _=>False)(DAresources false c)
 1200%Z 103%Z 106%Z 105%Z 400%Z 401%Z 110%Z 111%Z 112%Z 402%Z
 12%positive 11%positive 13%positive 10%positive 60%positive 30%positive 31%positive
 70%positive 71%positive 0%Z 4(Int.repr 3)Int.zero 80 0 DLentries DLtasks Vnull(emp:EcbMod.map)(Int.repr 37)
 eq_refl eq_refl ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)
 ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)
 (DAfresh false c 12%positive ltac:(tauto))(DAfresh false c 11%positive ltac:(tauto))
 (DAfresh false c 13%positive ltac:(tauto))DAenv eq_refl eq_refl eq_refl eq_refl
 ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(change(54<=4294967295)%Z;lia)
 ltac:(discriminate)DLtable DLbitmap eq_refl(DAentry false c enabled)) as(Mb&Blocked&Step&Records&Table&Bitmap&Returned).
 set(S:=(DWge,DCle,Mb,(fun _:hid=>false),(enabled,(nil:list hid),(nil:list bool)),DEfinalabs(Int.repr 3),spec_done None)).
 assert(Cells:S|=V293_owned_record_cells
 (V293_dly_cells 10%positive 11%positive 12%positive 60%positive 30%positive 31%positive
 0%Z 4(Int.repr 3)(Int.repr 3)(V293_byteval 0)64 0 1) **Atrue)
 by(unfold S;clear -Returned;sep auto).
 assert(Control:S|=V293_owned_record_cells(DAframe false c) **Atrue)
 by(unfold S;unfold DAresources in Returned;clear -Returned;sep auto).
 assert(Lookup:S|=V293_read_bytes 80%positive 0%Z V293_ready_table **Atrue)
 by(unfold S;unfold DAresources in Returned;clear -Returned;sep auto).
 assert(Guards:S|=V293_owned_record_cells(V293_dly_guard_cells 70%positive 71%positive) **Atrue)
 by(unfold S;clear -Returned;sep auto).
 assert(RawCPU:S|=Amapsto(13%positive,0%Z)Tint32 true(Vint32 Int.zero) **Atrue)
 by(unfold S;clear -Returned;sep auto).
 assert(Read:forall a tp v,In(a,tp,v)(DAframe false c)->load tp Mb a=Some v).
 { intros a tp v Member;eapply DScells_load;[exact Member|exact Control]. }
 assert(CoreRead:forall a tp v,In(a,tp,v)
 (V293_dly_cells 10%positive 11%positive 12%positive 60%positive 30%positive 31%positive
 0%Z 4(Int.repr 3)(Int.repr 3)(V293_byteval 0)64 0 1)->load tp Mb a=Some v).
 { intros a tp v Member;eapply DScells_load;[exact Member|exact Cells]. }
 assert(Reads:V293_sched_read_memory Mb 80%positive 31%positive 30%positive 64 0(V293_ready_group 64 0)).
 { split;[apply CoreRead;cbn[V293_dly_cells In];tauto| ];split.
   - intros n Range;change(load Tint8(getmem S)(80%positive,Z.of_nat n)=Some(V293_byteval(V293_ready_lookup n))).
     replace(Z.of_nat n)with(0+Z.of_nat n)%Z by lia.
     eapply V293_record_star_load_l;[apply V293_read_bytes_load|exact Lookup].
     + change(n<256);exact Range.
     + change(V293_ready_lookup n<256);pose proof(proj1(V293_ready_row_spec n Range));lia.
   - split;apply CoreRead;cbn[V293_dly_cells In];tauto. }
 destruct(V293_owned_cells_byte_writable(DAframe false c)(81%positive,0%Z)(V293_byteval 0)Atrue
 DWge DCle Mb(fun _:hid=>false)(enabled,nil,nil)(DEfinalabs(Int.repr 3))(spec_done None)
 ltac:(unfold DAframe;cbn;tauto)Control)as(oldhigh&HighWritable).
 assert(TargetWritable:V293_bytes_writable Mb 82%positive 0%Z 4).
 { eapply DScell_writable with(cells:=DAframe false c)(v:=Vnull)(tp:=Tptr V293_tcb_type);
   [unfold DAframe;cbn;tauto|exact Control]. }
 assert(Pointer:load(Tptr V293_tcb_type)Mb(83%positive,24%Z)=Some(Vptr(DStarget false))).
 { apply Read;unfold DAframe;apply in_or_app;right;apply in_or_app;left.
   pose proof(V293_priority_cells_nth(DSentries false)6 83%positive 0%Z ltac:(change(6<13);lia))as Member.
   exact Member. }
 assert(CounterWritable:V293_bytes_writable Mb 85%positive 0%Z 4).
 { eapply DScell_writable with(cells:=DAframe false c)(v:=Vint32 c)(tp:=Tint32);
   [unfold DAframe;apply in_or_app;right;apply in_or_app;right;cbn;tauto|exact Control]. }
 destruct(V293_sched_call_to_switch DAprogram(kseq sret kstop)DWge DCle Mb(fun _:hid=>false)enabled nil nil
 [60%positive;41%positive;90%positive;10%positive;84%positive;11%positive;12%positive;13%positive;30%positive;31%positive]
 112%Z 501%Z 110%Z 111%Z 113%Z 117%Z 115%Z 116%Z 118%Z 119%Z 114%Z 105%Z 106%Z 500%Z
 80%positive 31%positive 30%positive 81%positive 70%positive 71%positive 83%positive 82%positive 84%positive 85%positive 64 0 oldhigh 4 c(DStarget false)
 eq_refl eq_refl ltac:(cbn;intuition congruence)ltac:(cbn;intuition congruence)
 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
 ltac:(eapply DScells_load with(cells:=V293_dly_guard_cells 70%positive 71%positive);[cbn[V293_dly_guard_cells In];tauto|exact Guards])
 ltac:(eapply DScells_load with(cells:=V293_dly_guard_cells 70%positive 71%positive);[cbn[V293_dly_guard_cells In];tauto|exact Guards])Reads HighWritable TargetWritable Pointer
 ltac:(apply Read;unfold DAframe;apply in_or_app;right;apply in_or_app;right;cbn;tauto)
 ltac:(apply Read;unfold DAframe;apply in_or_app;right;apply in_or_app;right;cbn;tauto) CounterWritable
 ltac:(lia)ltac:(lia)ltac:(exists 6;left;split;[lia|reflexivity])ltac:(lia)ltac:(discriminate)
 ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)ltac:(discriminate))as(bs&byblock&Mf&Fresh&Away&Scheduled&High&Target&Counter&CPU&Dead&Frame).
 assert(TaskFrame:V293_task_records Mf(DEblocked(Int.repr 3))).
 { intros t pr st msg Get;eapply V293_task_record_frame;[ |apply Records;exact Get].
   intros i;apply Frame;try(intro E;discriminate E).
   - destruct(DStask_blocks t pr st msg Get)as[E|E];subst t;cbn;intro E;apply Away;cbn;tauto.
   - destruct(DStask_blocks t pr st msg Get)as[E|E];subst t;discriminate.
   - destruct(DStask_blocks t pr st msg Get)as[E|E];subst t;discriminate.
   - destruct(DStask_blocks t pr st msg Get)as[E|E];subst t;discriminate. }
 assert(Canary:load Tint32 Mf(90%positive,0%Z)=Some(Vint32(Int.repr 99))).
 { etransitivity;[apply V293_load_block_frame;intro i;apply Frame;try discriminate;
   intro E;apply Away;cbn;tauto|apply Read;unfold DAframe;cbn;tauto]. }
 assert(Cache:load Tint8 Mf(84%positive,0%Z)=Some(V293_byteval 4)).
 { etransitivity;[apply V293_load_block_frame;intro i;apply Frame;try discriminate;
   intro E;apply Away;cbn;tauto|apply Read;unfold DAframe;apply in_or_app;right;apply in_or_app;right;cbn;tauto]. }
 assert(CurrentWritable:V293_bytes_writable Mf 10%positive 0%Z 4).
 { assert(Owned:V293_bytes_writable Mb 10%positive 0%Z 4).
   { eapply DScell_writable with(cells:=V293_dly_cells 10%positive 11%positive 12%positive 60%positive 30%positive 31%positive
     0%Z 4(Int.repr 3)(Int.repr 3)(V293_byteval 0)64 0 1)(v:=Vptr OwnershipReady)(tp:=Tptr V293_tcb_type);
     [cbn[V293_dly_cells];right;left;reflexivity|exact Cells]. }
   intros k Range;destruct(Owned k Range)as(v&Cell);exists v;rewrite Frame by
   (try discriminate;intro E;apply Away;cbn;tauto);exact Cell. }
 assert(Facts:DAfacts Mf).
 { split.
   - intros [b off] tp v Member.
     assert(AtEntry:load tp Mb(b,off)=Some v).
     { cbn[DAobserved In]in Member;repeat destruct Member as[Member|Member];try contradiction;
       inversion Member;subst;try(apply CoreRead;cbn[V293_dly_cells In];tauto).
       change(load Tint32(getmem S)(13%positive,0%Z)=Some(Vint32 Int.zero)).
       apply DCraw_load;[reflexivity|exact RawCPU]. }
     etransitivity;[apply V293_load_block_frame;intro i;apply Frame;
       cbn[DAobserved In]in Member;repeat destruct Member as[Member|Member];try contradiction;
       inversion Member;subst;try discriminate;intro E;apply Away;rewrite <-E;cbn;tauto|exact AtEntry].
   - assert(W:V293_bytes_writable Mb 13%positive 0%Z 4).
     { eapply(V293_tick_raw_owned_writable 13%positive Tint32(Vint32 Int.zero)Atrue
       DWge DCle Mb(fun _:hid=>false)(enabled,nil,nil)(DEfinalabs(Int.repr 3))(spec_done None));exact RawCPU. }
     intros k Range;destruct(W k Range)as(v&Cell);exists v;rewrite Frame by
       (try discriminate;intro E;apply Away;cbn;tauto);exact Cell. }
 exists bs;exists byblock;exists Mf;split.
 - unfold DXrun,DXinitial,DXcut,DAprog,DXclient.
   eapply V293_global_trans;[exact Blocked| ].
   pose proof(V293_local_function_extension DAprogram(pumerge DAprogram(fun _=>None))DXextends _ _ _ _ Scheduled)as Extended.
   eapply(V293_local_steps_global (fun _=>None)DAprogram(fun _=>None)(fun _=>None) _ _ _ _ Extended
   1200%Z(V293_dly_full_body 103%Z 106%Z 105%Z 400%Z 401%Z 110%Z 111%Z 112%Z 402%Z)emp kstop
   Tvoid(dcons 401%Z Tint32 dnil)(dcons 400%Z Tint8(dcons 402%Z Tint32 dnil))
   DAtasks(sig OwnershipWaiting DCle)(DWaux enabled)OwnershipReady((emp:env),DXcles,DXcm)eq_refl).
   exact I.
 - split;[exact Step| ];split;[exact TaskFrame| ];split;[exact Bitmap| ];
   split;[exact High| ];split;[exact Target| ];split;[exact Counter| ];split;[exact Cache| ];split;[exact CurrentWritable| ];split;[exact Canary| ];split;[exact CPU| ];split;[exact Dead| ];split;[intro E;apply Away;rewrite E;cbn;tauto|exact Facts].
Qed.

Lemma DXcut_exact:forall enabled bs M,DXcut enabled bs M=
 (DAtasks,(DWge,DAenvs bs,M,(fun _:hid=>false),DWaux enabled),OwnershipReady).
Proof.
 intros enabled bs M;unfold DXcut,V293_local_global_at,V293_global_at.
 assert(Task:set DAtasks OwnershipReady(curs(sprim(switch 116%Z)),(kenil,DAcontinuation))=DAtasks)
 by(apply TasksMod.get_set_same;reflexivity).
 assert(Aux:TaskLStMod.set(DWaux enabled)OwnershipReady(false,nil,[enabled])=DWaux enabled)
 by(apply TaskLStMod.get_set_same;reflexivity).
 change((set DAtasks OwnershipReady(curs(sprim(switch 116%Z)),(kenil,DAcontinuation)),
 (DWge,DAenvs bs,M,(fun _:hid=>false),TaskLStMod.set(DWaux enabled)OwnershipReady(false,nil,[enabled])),OwnershipReady)=
 (DAtasks,(DWge,DAenvs bs,M,(fun _:hid=>false),DWaux enabled),OwnershipReady)).
 rewrite Task,Aux;reflexivity.
Qed.
Theorem DXglobal_switch:forall c enabled,exists bs byblock Mcut Mf,
 V293_global_steps DAprog DXclient(DXinitial c enabled)
 (set DAtasks OwnershipReady(SKIP,(kenil,DAcontinuation)),
 (DWge,DAenvs bs,Mf,(fun _:hid=>false),DWaux enabled),OwnershipWaiting) /\
 lpstep DAprog DAtasks DXclient(DWge,DAenvs bs,Mcut,(fun _:hid=>false),DWaux enabled)OwnershipReady
 (set DAtasks OwnershipReady(SKIP,(kenil,DAcontinuation)))DXclient
 (DWge,DAenvs bs,Mf,(fun _:hid=>false),DWaux enabled)OwnershipWaiting /\
 load(Tptr V293_tcb_type)Mf(10%positive,0%Z)=Some(Vptr OwnershipWaiting) /\
 V293_task_records Mf(DEblocked(Int.repr 3)) /\
 V293_bitmap_tasks 64 0(DEblocked(Int.repr 3)) /\
 load Tint32 Mf(85%positive,0%Z)=Some(Vint32(Int.add c Int.one)) /\
 load Tint8 Mf(84%positive,0%Z)=Some(V293_byteval 4) /\
 load Tint32 Mf(90%positive,0%Z)=Some(Vint32(Int.repr 99)) /\
 V293_bytes_writable Mf bs 0%Z 4 /\get Mf(byblock,0%Z)=None /\DAfacts Mf /\
 get(set DAtasks OwnershipReady(SKIP,(kenil,DAcontinuation)))OwnershipReady=Some(SKIP,(kenil,DAcontinuation)) /\
 get(set DAtasks OwnershipReady(SKIP,(kenil,DAcontinuation)))OwnershipWaiting=Some DWready /\
 get(DAenvs bs)OwnershipWaiting=Some DCle /\get(DWaux enabled)OwnershipWaiting=Some(true,nil,nil).
Proof.
 intros c enabled;destruct(DXglobal_run c enabled)
 as(bs&byblock&Mcut&Run&Step&Records&Bitmap&High&Target&Count&Cache&Writable&Canary&CPU&Dead&Away&Facts).
 destruct(V293_sched_switch_commit (fun _=>None)DAprogram(fun _=>None)(fun _=>None)DAtasks DXclient
 DAcontinuation OwnershipReady OwnershipWaiting 116%Z 82%positive 10%positive V293_tcb_type
 DWge(V293_cpu_lenv 501%Z bs)(DAenvs bs)Mcut(fun _:hid=>false)(false,nil,[enabled])(DWaux enabled)
 eq_refl eq_refl eq_refl eq_refl Target eq_refl Writable)as(Mf&Switch&Store&Current&Frame).
 assert(Y:byblock<>10%positive).
 { intro E;destruct(Writable 0 ltac:(lia))as(v&Cell);cbn in Cell;rewrite <-E,Dead in Cell;discriminate. }
 exists bs;exists byblock;exists Mcut;exists Mf;split.
 { unfold DXrun in Run;rewrite DXcut_exact in Run.
   eapply V293_global_trans;[exact Run| ].
   unfold V293_global_steps;eapply rt1n_trans with(y:=
   (set DAtasks OwnershipReady(SKIP,(kenil,DAcontinuation)),
   (DWge,DAenvs bs,Mf,(fun _:hid=>false),DWaux enabled),OwnershipWaiting));
   [exact Switch|apply rt1n_refl]. }
 split;[exact Switch| ];split;[exact Current| ];split.
 - intros t pr st msg Get;eapply V293_task_record_frame;[ |apply Records;exact Get].
   intros i;apply Frame;left;destruct(DStask_blocks t pr st msg Get)as[E|E];subst t;discriminate.
 - split;[exact Bitmap| ];split.
   + etransitivity;[apply V293_load_block_frame;intro i;apply Frame;left;discriminate|exact Count].
   + split.
     * etransitivity;[apply V293_load_block_frame;intro i;apply Frame;left;discriminate|exact Cache].
     * split.
       -- etransitivity;[apply V293_load_block_frame;intro i;apply Frame;left;discriminate|exact Canary].
       -- split.
          ++ intros k Range;destruct(CPU k Range)as(v&Cell);exists v;rewrite Frame by(left;exact Away);exact Cell.
          ++ split;[rewrite Frame by(left;exact Y);exact Dead| ];split.
             ** eapply DAfacts_frame;[intros;apply Frame;left;eassumption|exact Facts].
             ** repeat split;reflexivity.
Qed.

Definition DXfinal enabled bs (M:mem):=
 (set DAtasks OwnershipReady(SKIP,(kenil,DAcontinuation)),
 (DWge,DAenvs bs,M,(fun _:hid=>false),DWaux enabled),OwnershipWaiting).

Theorem DXboth_IE:
 (exists bs M,V293_global_steps DAprog DXclient(DXinitial Int.zero true)(DXfinal true bs M)) /\
 (exists bs M,V293_global_steps DAprog DXclient(DXinitial Int.zero false)(DXfinal false bs M)).
Proof.
 split;[destruct(DXglobal_switch Int.zero true)as(bs&byblock&Mcut&M&Trace&Rest)|
 destruct(DXglobal_switch Int.zero false)as(bs&byblock&Mcut&M&Trace&Rest)];
 exists bs;exists M;exact Trace.
Qed.

Theorem DXglobal_wrap:forall enabled,exists bs M,
 V293_global_steps DAprog DXclient(DXinitial(Int.repr Int.max_unsigned)enabled)(DXfinal enabled bs M) /\
 load Tint32 M(85%positive,0%Z)=Some(Vint32 Int.zero).
Proof.
 intro enabled;destruct(DXglobal_switch(Int.repr Int.max_unsigned)enabled)
 as(bs&byblock&Mcut&M&Trace&Switch&Current&Records&Bitmap&Counter&Rest).
 exists bs;exists M;split;[exact Trace|rewrite DWcounter_wrap in Counter;exact Counter].
Qed.

(* Identical block numbers belong to distinct client and OS heaps. The client
   keeps 99 while the actual OS parameter has become 3. *)
Theorem DXdistinct_heaps:forall c enabled,exists bs M,
 V293_global_steps DAprog DXclient(DXinitial c enabled)(DXfinal enabled bs M) /\
 load Tint32 M(12%positive,0%Z)=Some(Vint32(Int.repr 3)) /\
 load Tint32 DXcm(12%positive,0%Z)=Some(Vint32(Int.repr 99)) /\
 get DXcles OwnershipReady=Some DXcle /\get DXcle 777%Z=Some(12%positive,Tint32).
Proof.
 intros c enabled;destruct(DXglobal_switch c enabled)
 as(bs&byblock&Mcut&M&Trace&Switch&Current&Records&Bitmap&Counter&Cache&Canary&CPU&Dead&Facts&Rest).
 exists bs;exists M;split;[exact Trace| ];split.
 - destruct Facts as[Values Writable];apply Values;cbn[DAobserved In];tauto.
 - pose proof DXclient_alias as[Load[Env[Local Rest']]];auto.
Qed.

Theorem DXhigh_switch:
 hpstep DWhighprog DAhightasks DXclient(DEfinalabs(Int.repr 3))
 (set DAhightasks OwnershipReady DAhighafter)DXclient
 (set(DEfinalabs(Int.repr 3))curtid(oscurt OwnershipWaiting)) /\
 get(set DAhightasks OwnershipReady DAhighafter)OwnershipWaiting=Some DWready.
Proof.
 split;[eapply hswi_step;[reflexivity|exact DWselected|reflexivity|reflexivity|reflexivity|reflexivity]|reflexivity].
Qed.

(* A prospective single factor: remove only the delay OS binding. This is an
   early linkage check, not a test of allocation or downstream scheduling. *)
Definition DXmissing:progunit:=fun f=>if Z.eq_dec f 1200%Z then None else DAprogram f.
Definition DXmissingprog:lprog:=((fun _=>None),(DXmissing,(fun _=>None),(fun _=>None))).
Definition DXentry c enabled:=V293_local_global_at DAtasks(sig OwnershipWaiting DCle)(DWaux enabled)
 OwnershipReady(curs(sfexec 1200%Z(cons(Vint32(Int.repr 3))nil)(cons Tint32 nil)),(kenil,kstop))
 ((DWge,emp,DAmem false c),(fun _:hid=>false),(enabled,nil,nil)).
Lemma DXonly_binding:
 DXmissing 1200%Z=None /\(forall f,f<>1200%Z ->DXmissing f=DAprogram f).
Proof.
 split;[reflexivity|intros f Different;unfold DXmissing;
 destruct(Z.eq_dec f 1200%Z);[contradiction|reflexivity]].
Qed.
Theorem DXsame_client_prefix:forall c enabled,
 V293_global_steps DAprog DXclient(DXinitial c enabled)(DXentry c enabled) /\
 V293_global_steps DXmissingprog DXclient(DXinitial c enabled)(DXentry c enabled).
Proof.
 intros c enabled;split;unfold DAprog,DXmissingprog,DXclient,DXinitial,DXentry;
 eapply V293_constant_call_global;reflexivity.
Qed.
Theorem DXentry_gate:forall m ir aux,
 (exists C' st',loststep DAprogram
 (curs(sfexec 1200%Z(cons(Vint32(Int.repr 3))nil)(cons Tint32 nil)),(kenil,kstop))(m,ir,aux)C' st') /\
 ~(exists C' st',loststep DXmissing
 (curs(sfexec 1200%Z(cons(Vint32(Int.repr 3))nil)(cons Tint32 nil)),(kenil,kstop))(m,ir,aux)C' st').
Proof.
 intros [[ge le]M] ir aux;split.
 - eexists;eexists;apply ostc_step;eapply stmt_step;[reflexivity| ].
   eapply sfexec_step;[reflexivity|reflexivity|reflexivity|split;[exact I|reflexivity]|reflexivity].
 - apply V293_missing_port_has_no_step;reflexivity.
Qed.
