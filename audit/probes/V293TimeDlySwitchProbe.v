(* Actual delay blocking, comparison, counter, original low/high switch.
   Fixture reachability from boot and later resumption are not claimed. *)
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

Definition DWge:env:=set(set(set DSge 118%Z(84%positive,Tint8))
 119%Z(85%positive,Tint32))OSTCBCur(10%positive,Tptr V293_tcb_type).
Definition DWframe(c:int32):=DSframe false++
 [((84%positive,0%Z),Tint8,V293_byteval 4);((85%positive,0%Z),Tint32,Vint32 c)].
Definition DWsmall c:=DEcells(Int.repr 3)++(DLextra++(DLlow++DWframe c)).
Definition DWmem c:=merge(OwnershipCellsMemory(DWsmall c))DSlookup.
Definition DWstate M O:=V293_target_wstate DWge DEle M O.
Definition DWresources c:=V293_owned_record_cells(DWframe c) **
 V293_read_bytes 80%positive 0%Z V293_ready_table.

Lemma DWsmall_spatial : forall c,DWstate(OwnershipCellsMemory(DWsmall c))emp|=
 V293_owned_record_cells(DWsmall c).
Proof.
 intro c;apply OwnershipCellsSpatial.
 - apply DSseparated_sound;vm_compute;reflexivity.
 - repeat constructor;vm_compute;reflexivity.
Qed.
Lemma DWjoin : forall c,join(OwnershipCellsMemory(DWsmall c))DSlookup(DWmem c).
Proof.
 intro c;apply map_join_merge;apply map_disjoint;intros[b i].
 destruct(Pos.eq_dec b 80%positive)as[Same|Other].
 - subst b;left;apply OwnershipCellsOutside;vm_compute;intro H;repeat destruct H as[H|H];congruence.
 - right;left;unfold DSlookup,V293_nat_memory;apply V293_encoded_memory_outside;left;exact Other.
Qed.
Lemma DWentry : forall c,DWstate(DWmem c)DEabs|=
 V293_owned_record_cells(DEcells(Int.repr 3)) **(V293_owned_record_cells DLextra **
 (V293_owned_task_records(del DLtasks OwnershipReady) **
 (V293_shared_fields OwnershipReady DLtasks(emp:EcbMod.map)(Int.repr 37) **DWresources c))).
Proof.
 intro c;pose proof(DWsmall_spatial c)as Cells.
 apply(proj1(OwnershipCellsAppend(DEcells(Int.repr 3))(DLextra++(DLlow++DWframe c))_))in Cells.
 assert(Physical:DWstate(OwnershipCellsMemory(DWsmall c))emp|=
 V293_owned_record_cells(DEcells(Int.repr 3)) **(V293_owned_record_cells DLextra **
 (V293_owned_record_cells DLlow **V293_owned_record_cells(DWframe c)))).
 { eapply astar_mono;[intros st H;exact H| |exact Cells].
   intros st H;apply OwnershipCellsAppend in H.
   eapply astar_mono;[intros st' H';exact H'| |exact H].
   intros st' H';apply OwnershipCellsAppend in H';exact H'. }
 assert(WithLookup:DWstate(DWmem c)emp|=
 (V293_owned_record_cells(DEcells(Int.repr 3)) **(V293_owned_record_cells DLextra **
 (V293_owned_record_cells DLlow **V293_owned_record_cells(DWframe c)))) **
 V293_read_bytes 80%positive 0%Z V293_ready_table).
 { eapply V293_wstate_star;[apply DWjoin|exact Physical|apply V293_read_bytes_witness]. }
 assert(Joint:DWstate(DWmem c)DEabs|=
 ((V293_owned_record_cells(DEcells(Int.repr 3)) **(V293_owned_record_cells DLextra **
 (V293_owned_record_cells DLlow **V293_owned_record_cells(DWframe c)))) **
 V293_read_bytes 80%positive 0%Z V293_ready_table) **
 V293_shared_fields OwnershipReady DLtasks(emp:EcbMod.map)(Int.repr 37)).
 { eapply V293_target_wstate_star with(m1:=DWmem c)(m2:=emp)(o1:=emp)(o2:=DEabs).
   - apply map_join_emp.
   - apply map_join_comm;apply map_join_emp.
   - exact WithLookup.
   - exact(V293_shared_fixture_fields OwnershipReady DLtasks(emp:EcbMod.map)(Int.repr 37)). }
 assert(Reordered:DWstate(DWmem c)DEabs|=V293_owned_record_cells(DEcells(Int.repr 3)) **
 (V293_owned_record_cells DLextra **(V293_owned_record_cells DLlow **
 (V293_shared_fields OwnershipReady DLtasks(emp:EcbMod.map)(Int.repr 37) **DWresources c))))
 by(unfold DWresources;clear -Joint;sep auto).
 eapply astar_mono;[intros st H;exact H| |exact Reordered].
 intros st H;eapply astar_mono;[intros st' H';exact H'| |exact H].
 intros st' H';eapply astar_mono;[apply DTlow_owned|intros st'' H'';exact H''|exact H'].
Qed.
Lemma DWenv:V293_dly_env 103%Z 106%Z 105%Z 400%Z 401%Z
 10%positive 11%positive 12%positive 30%positive 31%positive DWge DEle.
Proof. vm_compute;repeat split;reflexivity. Qed.
Lemma DWinitial_guards : forall c,
 load Tint8(DWmem c)(70%positive,0%Z)=Some(V293_byteval 0) /\
 load Tint8(DWmem c)(71%positive,0%Z)=Some(V293_byteval 0).
Proof.
 intro c;pose proof(DWentry c)as Entry.
 assert(Owned:DWstate(DWmem c)DEabs|=V293_owned_record_cells(DWframe c) **Atrue)
 by(unfold DWresources in Entry;clear -Entry;sep auto).
 split;eapply DScells_load;[ |exact Owned| |exact Owned];unfold DWframe,DSframe,DEframe;cbn;tauto.
Qed.
Definition DWrun c enabled bs Mf:=
 V293_local_steps DSprogram(curs DEbody,(kenil,kstop))
 ((DWge,DEle,DWmem c),(fun _=>false),(enabled,nil,nil))
 (curs(sprim(switch 116%Z)),(kenil,DScontinuation))
 ((DWge,V293_cpu_lenv 501%Z bs,Mf),(fun _=>false),(false,nil,enabled::nil)).

Theorem DWblocked_run : forall c enabled,exists bs byblock Mf,
 DWrun c enabled bs Mf /\
 spec_step(fun _ _=>False)(spec_prim(cons(Vint32(Int.repr 3))nil)V293_dly_block_step)
 DEabs(END None)(DEfinalabs(Int.repr 3)) /\
 V293_task_records Mf(DEblocked(Int.repr 3)) /\
 V293_bitmap_tasks 64 0(DEblocked(Int.repr 3)) /\
 load Tint8 Mf(81%positive,0%Z)=Some(V293_byteval 6) /\
 load(Tptr V293_tcb_type)Mf(82%positive,0%Z)=Some(Vptr(OwnershipWaiting)) /\
 load Tint32 Mf(85%positive,0%Z)=Some(Vint32(Int.add c Int.one)) /\
 load Tint8 Mf(84%positive,0%Z)=Some(V293_byteval 4) /\
 V293_bytes_writable Mf 10%positive 0%Z 4 /\
 load Tint32 Mf(90%positive,0%Z)=Some(Vint32(Int.repr 99)) /\
 V293_bytes_writable Mf bs 0%Z 4 /\get Mf(byblock,0%Z)=None /\bs<>10%positive.
Proof.
 intros c enabled;destruct(DWinitial_guards c)as[Ln Ll].
 destruct(V293_OSTimeDly_body_to_sched_refines 103%Z 106%Z 105%Z 400%Z 401%Z 110%Z 111%Z 112%Z
 10%positive 11%positive 12%positive 60%positive 30%positive 31%positive 70%positive 71%positive 0%Z 4(Int.repr 3)
 DSprogram kstop DWge DEle(DWmem c)(fun _=>false)enabled nil nil DEabs(spec_done None)(fun _ _=>False)
 (DWresources c)Int.zero(V293_byteval 0)80 0 DLentries DLtasks Vnull(emp:EcbMod.map)(Int.repr 37)
 DWenv eq_refl eq_refl Ln eq_refl eq_refl Ll ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)
 ltac:(change(54<=4294967295)%Z;lia)ltac:(discriminate)DLtable DLbitmap eq_refl(DWentry c))
 as(Mb&Blocked&Step&Records&Table&Bitmap&Returned).
 set(S:=(DWge,DEle,Mb,(fun _:hid=>false),(enabled,(nil:list hid),(nil:list bool)),DEfinalabs(Int.repr 3),spec_done None)).
 assert(Cells:S|=V293_owned_record_cells
 (V293_dly_cells 10%positive 11%positive 12%positive 60%positive 30%positive 31%positive
 0%Z 4(Int.repr 3)(Int.repr 3)(V293_byteval 0)64 0 1) **Atrue)
 by(unfold S;clear -Returned;sep auto).
 assert(Control:S|=V293_owned_record_cells(DWframe c) **Atrue)
 by(unfold S;unfold DWresources in Returned;clear -Returned;sep auto).
 assert(Lookup:S|=V293_read_bytes 80%positive 0%Z V293_ready_table **Atrue)
 by(unfold S;unfold DWresources in Returned;clear -Returned;sep auto).
 assert(Read:forall a tp v,In(a,tp,v)(DWframe c)->load tp Mb a=Some v).
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
 destruct(V293_owned_cells_byte_writable(DWframe c)(81%positive,0%Z)(V293_byteval 0)Atrue
 DWge DEle Mb(fun _=>false)(enabled,nil,nil)(DEfinalabs(Int.repr 3))(spec_done None)
 ltac:(unfold DWframe,DSframe;cbn;tauto)Control)as(oldhigh&HighWritable).
 assert(TargetWritable:V293_bytes_writable Mb 82%positive 0%Z 4).
 { eapply DScell_writable with(cells:=DWframe c)(v:=Vnull)(tp:=Tptr V293_tcb_type);
   [unfold DWframe,DSframe;cbn;tauto|exact Control]. }
 assert(Pointer:load(Tptr V293_tcb_type)Mb(83%positive,24%Z)=Some(Vptr(OwnershipWaiting))).
 { apply Read;unfold DWframe,DSframe;apply in_or_app;left;apply in_or_app;right;apply in_or_app;right.
   pose proof(V293_priority_cells_nth(DSentries false)6 83%positive 0%Z ltac:(change(6<13);lia))as Member.
   exact Member. }
 assert(CounterWritable:V293_bytes_writable Mb 85%positive 0%Z 4).
 { eapply DScell_writable with(cells:=DWframe c)(v:=Vint32 c)(tp:=Tint32);
   [unfold DWframe;apply in_or_app;right;cbn;tauto|exact Control]. }
 destruct(V293_sched_call_to_switch DSprogram(kseq sret kstop)DWge DEle Mb(fun _=>false)enabled nil nil
 [60%positive;41%positive;90%positive;10%positive;84%positive]
 112%Z 501%Z 110%Z 111%Z 113%Z 117%Z 115%Z 116%Z 118%Z 119%Z 114%Z 105%Z 106%Z 500%Z
 80%positive 31%positive 30%positive 81%positive 70%positive 71%positive 83%positive 82%positive 84%positive 85%positive 64 0 oldhigh 4 c OwnershipWaiting
 eq_refl eq_refl ltac:(cbn;intuition congruence)ltac:(cbn;intuition congruence)
 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
 ltac:(apply Read;unfold DWframe,DSframe,DEframe;cbn;tauto)
 ltac:(apply Read;unfold DWframe,DSframe,DEframe;cbn;tauto)Reads HighWritable TargetWritable Pointer
 ltac:(apply Read;unfold DWframe;apply in_or_app;right;cbn;tauto)
 ltac:(apply Read;unfold DWframe;apply in_or_app;right;cbn;tauto) CounterWritable
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
   intro E;apply Away;cbn;tauto|apply Read;unfold DWframe,DSframe,DEframe;cbn;tauto]. }
 assert(Cache:load Tint8 Mf(84%positive,0%Z)=Some(V293_byteval 4)).
 { etransitivity;[apply V293_load_block_frame;intro i;apply Frame;try discriminate;
   intro E;apply Away;cbn;tauto|apply Read;unfold DWframe;apply in_or_app;right;cbn;tauto]. }
 assert(CurrentWritable:V293_bytes_writable Mf 10%positive 0%Z 4).
 { assert(Owned:V293_bytes_writable Mb 10%positive 0%Z 4).
   { eapply DScell_writable with(cells:=V293_dly_cells 10%positive 11%positive 12%positive 60%positive 30%positive 31%positive
     0%Z 4(Int.repr 3)(Int.repr 3)(V293_byteval 0)64 0 1)(v:=Vptr OwnershipReady)(tp:=Tptr V293_tcb_type);
     [cbn[V293_dly_cells];right;left;reflexivity|exact Cells]. }
   intros k Range;destruct(Owned k Range)as(v&Cell);exists v;rewrite Frame by
   (try discriminate;intro E;apply Away;cbn;tauto);exact Cell. }
 exists bs;exists byblock;exists Mf;split.
 - unfold DWrun;eapply V293_local_trans;[exact Blocked|exact Scheduled].
 - split;[exact Step| ];split;[exact TaskFrame| ];split;[exact Bitmap| ];
   split;[exact High| ];split;[exact Target| ];split;[exact Counter| ];split;[exact Cache| ];split;[exact CurrentWritable| ];split;[exact Canary| ];split;[exact CPU| ];split;[exact Dead|intro E;apply Away;rewrite E;cbn;tauto].
Qed.


Definition DWready:code:=(cure(econst32(Int.repr 7)),(keop1 negation Tint32 kenil,kseq sret kstop)).
Definition DWtasks:tasks:=set(sig OwnershipWaiting DWready)OwnershipReady
 (curs(sprim(switch 116%Z)),(kenil,DScontinuation)).
Definition DWenvs bs:cltenvs:=set(sig OwnershipWaiting DEle)OwnershipReady(V293_cpu_lenv 501%Z bs).
Definition DWaux enabled:TaskLStMod.map:=set(sig OwnershipWaiting(true,nil,nil))OwnershipReady(false,nil,[enabled]).
Definition DWclient:clientst:=(DWge,emp,emp).
Definition DWprog:lprog:=((fun _=>None),(DSprogram,(fun _=>None),(fun _=>None))).
Definition DWhigh:code:=(curs(hapi_code(sched;;spec_done None)),(kenil,DScontinuation)).
Definition DWhighafter:code:=(curs(hapi_code(spec_done None)),(kenil,DScontinuation)).
Definition DWhightasks:tasks:=set(sig OwnershipWaiting DWready)OwnershipReady DWhigh.
Definition DWhighprog:hprog:=((fun _=>None),((fun _=>None),(fun _=>None),V293_scheduler)).

Lemma DWselected : V293_scheduler(DEfinalabs(Int.repr 3))OwnershipWaiting.
Proof.
 exists(DEblocked(Int.repr 3));split;[reflexivity| ].
 exists(Int.repr 6);exists(Vptr(120%positive,Int.repr 7));split;[reflexivity| ].
 intros t pr msg Get;destruct(DStask_blocks t pr rdy msg Get)as[E|E];subst t.
 - change(get(DEblocked(Int.repr 3))OwnershipReady=Some(pr,rdy,msg))in Get.
   unfold DEblocked in Get;rewrite map_get_set in Get;discriminate.
 - change(get(DEblocked(Int.repr 3))OwnershipWaiting=Some(pr,rdy,msg))in Get.
   unfold DEblocked in Get;rewrite map_get_set' in Get by discriminate.
   unfold DLtasks in Get;rewrite map_get_set in Get;inversion Get;subst;lia.
Qed.

Theorem DWhigh_switch :
 hpstep DWhighprog DWhightasks DWclient(DEfinalabs(Int.repr 3))
 (set DWhightasks OwnershipReady DWhighafter)DWclient
 (set(DEfinalabs(Int.repr 3))curtid(oscurt OwnershipWaiting)) /\
 get(set DWhightasks OwnershipReady DWhighafter)OwnershipReady=Some DWhighafter /\
 get(set DWhightasks OwnershipReady DWhighafter)OwnershipWaiting=Some DWready.
Proof.
 split.
 - eapply hswi_step;[reflexivity|exact DWselected|reflexivity|reflexivity|reflexivity|reflexivity].
 - split;reflexivity.
Qed.

Theorem DWblocked_switch : forall c enabled,exists bs byblock Mcut Mf,
 DWrun c enabled bs Mcut /\
 lpstep DWprog DWtasks DWclient(DWge,DWenvs bs,Mcut,(fun _=>false),DWaux enabled)OwnershipReady
 (set DWtasks OwnershipReady(SKIP,(kenil,DScontinuation)))DWclient
 (DWge,DWenvs bs,Mf,(fun _=>false),DWaux enabled)OwnershipWaiting /\
 load(Tptr V293_tcb_type)Mf(10%positive,0%Z)=Some(Vptr OwnershipWaiting) /\
 V293_task_records Mf(DEblocked(Int.repr 3)) /\
 load Tint32 Mf(85%positive,0%Z)=Some(Vint32(Int.add c Int.one)) /\
 load Tint8 Mf(84%positive,0%Z)=Some(V293_byteval 4) /\
 load Tint32 Mf(90%positive,0%Z)=Some(Vint32(Int.repr 99)) /\
 V293_bytes_writable Mf bs 0%Z 4 /\get Mf(byblock,0%Z)=None /\
 get(set DWtasks OwnershipReady(SKIP,(kenil,DScontinuation)))OwnershipReady=Some(SKIP,(kenil,DScontinuation)) /\
 get(set DWtasks OwnershipReady(SKIP,(kenil,DScontinuation)))OwnershipWaiting=Some DWready /\
 get(DWenvs bs)OwnershipWaiting=Some DEle /\get(DWaux enabled)OwnershipWaiting=Some(true,nil,nil).
Proof.
 intros c enabled;destruct(DWblocked_run c enabled)
 as(bs&byblock&Mcut&Run&Step&Records&Bitmap&High&Target&Count&Cache&Writable&Canary&CPU&Dead&Away).
 destruct(V293_sched_switch_commit (fun _=>None)DSprogram(fun _=>None)(fun _=>None) DWtasks DWclient
 DScontinuation OwnershipReady OwnershipWaiting 116%Z 82%positive 10%positive V293_tcb_type
 DWge(V293_cpu_lenv 501%Z bs)(DWenvs bs)Mcut(fun _=>false)(false,nil,[enabled])(DWaux enabled)
 eq_refl eq_refl eq_refl eq_refl Target eq_refl Writable)as(Mf&Switch&Store&Current&Frame).
 assert(Y:byblock<>10%positive).
 { intro E;destruct(Writable 0 ltac:(lia))as(v&Cell);cbn in Cell;rewrite <-E,Dead in Cell;discriminate. }
 exists bs;exists byblock;exists Mcut;exists Mf;split;[exact Run| ];split;[exact Switch| ];split;[exact Current| ];split.
 - intros t pr st msg Get;eapply V293_task_record_frame;[ |apply Records;exact Get].
   intros i;apply Frame;left;destruct(DStask_blocks t pr st msg Get)as[E|E];subst t;discriminate.
 - split.
   + etransitivity;[apply V293_load_block_frame;intro i;apply Frame;left;discriminate|exact Count].
   + split.
     * etransitivity;[apply V293_load_block_frame;intro i;apply Frame;left;discriminate|exact Cache].
     * split.
       -- etransitivity;[apply V293_load_block_frame;intro i;apply Frame;left;discriminate|exact Canary].
       -- split.
          ++ intros k Range;destruct(CPU k Range)as(v&Cell);exists v;rewrite Frame by(left;exact Away);exact Cell.
          ++ split;[rewrite Frame by(left;exact Y);exact Dead|repeat split;reflexivity].
Qed.

Theorem DWboth_IE :
 (exists (bs byblock:block)(Mcut Mf:mem),DWrun Int.zero true bs Mcut /\
 lpstep DWprog DWtasks DWclient(DWge,DWenvs bs,Mcut,(fun _=>false),DWaux true)OwnershipReady
 (set DWtasks OwnershipReady(SKIP,(kenil,DScontinuation)))DWclient
 (DWge,DWenvs bs,Mf,(fun _=>false),DWaux true)OwnershipWaiting) /\
 (exists (bs byblock:block)(Mcut Mf:mem),DWrun Int.zero false bs Mcut /\
 lpstep DWprog DWtasks DWclient(DWge,DWenvs bs,Mcut,(fun _=>false),DWaux false)OwnershipReady
 (set DWtasks OwnershipReady(SKIP,(kenil,DScontinuation)))DWclient
 (DWge,DWenvs bs,Mf,(fun _=>false),DWaux false)OwnershipWaiting).
Proof.
 split;[destruct(DWblocked_switch Int.zero true)as(bs&byblock&Mcut&Mf&Run&Step&Rest)|
 destruct(DWblocked_switch Int.zero false)as(bs&byblock&Mcut&Mf&Run&Step&Rest)];
 exists bs;exists byblock;exists Mcut;exists Mf;auto.
Qed.

Lemma DWcounter_wrap : Int.add(Int.repr Int.max_unsigned)Int.one=Int.zero.
Proof. vm_compute;apply Int.mkint_eq;reflexivity. Qed.
Theorem DWwrap_run : exists (bs byblock:block)(Mf:mem),
 DWrun(Int.repr Int.max_unsigned)true bs Mf /\
 load Tint32 Mf(85%positive,0%Z)=Some(Vint32 Int.zero).
Proof.
 destruct(DWblocked_run(Int.repr Int.max_unsigned)true)
 as(bs&byblock&Mf&Run&Step&Records&Bitmap&High&Target&Count&Rest).
 exists bs;exists byblock;exists Mf;split;[exact Run|rewrite DWcounter_wrap in Count;exact Count].
Qed.

(* A common actual prefix for the prospective tail-only counter ablation. *)
Definition DWprefix c enabled bs Mf:=
 V293_local_steps DSprogram(curs DEbody,(kenil,kstop))
 ((DWge,DEle,DWmem c),(fun _=>false),(enabled,nil,nil))
 (curs DSchange,(kenil,DScontinuation))
 ((DWge,V293_cpu_lenv 501%Z bs,Mf),(fun _=>false),(false,nil,enabled::nil)).

Theorem DWblocked_prefix : forall c enabled,exists bs byblock Mf,
 DWprefix c enabled bs Mf /\
 spec_step(fun _ _=>False)(spec_prim(cons(Vint32(Int.repr 3))nil)V293_dly_block_step)
 DEabs(END None)(DEfinalabs(Int.repr 3)) /\
 V293_task_records Mf(DEblocked(Int.repr 3)) /\
 V293_bitmap_tasks 64 0(DEblocked(Int.repr 3)) /\
 load Tint8 Mf(81%positive,0%Z)=Some(V293_byteval 6) /\
 load(Tptr V293_tcb_type)Mf(82%positive,0%Z)=Some(Vptr(OwnershipWaiting)) /\
 load Tint32 Mf(85%positive,0%Z)=Some(Vint32 c) /\
 load Tint8 Mf(84%positive,0%Z)=Some(V293_byteval 4) /\
 V293_bytes_writable Mf 10%positive 0%Z 4 /\
 load Tint32 Mf(90%positive,0%Z)=Some(Vint32(Int.repr 99)) /\
 V293_bytes_writable Mf bs 0%Z 4 /\get Mf(byblock,0%Z)=None /\bs<>10%positive /\bs<>85%positive /\V293_bytes_writable Mf 85%positive 0%Z 4.
Proof.
 intros c enabled;destruct(DWinitial_guards c)as[Ln Ll].
 destruct(V293_OSTimeDly_body_to_sched_refines 103%Z 106%Z 105%Z 400%Z 401%Z 110%Z 111%Z 112%Z
 10%positive 11%positive 12%positive 60%positive 30%positive 31%positive 70%positive 71%positive 0%Z 4(Int.repr 3)
 DSprogram kstop DWge DEle(DWmem c)(fun _=>false)enabled nil nil DEabs(spec_done None)(fun _ _=>False)
 (DWresources c)Int.zero(V293_byteval 0)80 0 DLentries DLtasks Vnull(emp:EcbMod.map)(Int.repr 37)
 DWenv eq_refl eq_refl Ln eq_refl eq_refl Ll ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)
 ltac:(change(54<=4294967295)%Z;lia)ltac:(discriminate)DLtable DLbitmap eq_refl(DWentry c))
 as(Mb&Blocked&Step&Records&Table&Bitmap&Returned).
 set(S:=(DWge,DEle,Mb,(fun _:hid=>false),(enabled,(nil:list hid),(nil:list bool)),DEfinalabs(Int.repr 3),spec_done None)).
 assert(Cells:S|=V293_owned_record_cells
 (V293_dly_cells 10%positive 11%positive 12%positive 60%positive 30%positive 31%positive
 0%Z 4(Int.repr 3)(Int.repr 3)(V293_byteval 0)64 0 1) **Atrue)
 by(unfold S;clear -Returned;sep auto).
 assert(Control:S|=V293_owned_record_cells(DWframe c) **Atrue)
 by(unfold S;unfold DWresources in Returned;clear -Returned;sep auto).
 assert(Lookup:S|=V293_read_bytes 80%positive 0%Z V293_ready_table **Atrue)
 by(unfold S;unfold DWresources in Returned;clear -Returned;sep auto).
 assert(Read:forall a tp v,In(a,tp,v)(DWframe c)->load tp Mb a=Some v).
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
 destruct(V293_owned_cells_byte_writable(DWframe c)(81%positive,0%Z)(V293_byteval 0)Atrue
 DWge DEle Mb(fun _=>false)(enabled,nil,nil)(DEfinalabs(Int.repr 3))(spec_done None)
 ltac:(unfold DWframe,DSframe;cbn;tauto)Control)as(oldhigh&HighWritable).
 assert(TargetWritable:V293_bytes_writable Mb 82%positive 0%Z 4).
 { eapply DScell_writable with(cells:=DWframe c)(v:=Vnull)(tp:=Tptr V293_tcb_type);
   [unfold DWframe,DSframe;cbn;tauto|exact Control]. }
 assert(Pointer:load(Tptr V293_tcb_type)Mb(83%positive,24%Z)=Some(Vptr(OwnershipWaiting))).
 { apply Read;unfold DWframe,DSframe;apply in_or_app;left;apply in_or_app;right;apply in_or_app;right.
   pose proof(V293_priority_cells_nth(DSentries false)6 83%positive 0%Z ltac:(change(6<13);lia))as Member.
   exact Member. }
 assert(CounterWritable:V293_bytes_writable Mb 85%positive 0%Z 4).
 { eapply DScell_writable with(cells:=DWframe c)(v:=Vint32 c)(tp:=Tint32);
   [unfold DWframe;apply in_or_app;right;cbn;tauto|exact Control]. }
 destruct(V293_sched_call_to_change DSprogram(kseq sret kstop)DWge DEle Mb(fun _=>false)enabled nil nil
 [60%positive;41%positive;90%positive;10%positive;84%positive;85%positive]
 112%Z 501%Z 110%Z 111%Z 113%Z 117%Z 115%Z 116%Z 118%Z 119%Z 114%Z 105%Z 106%Z 500%Z
 80%positive 31%positive 30%positive 81%positive 70%positive 71%positive 83%positive 82%positive 64 0 oldhigh OwnershipWaiting
 eq_refl eq_refl ltac:(cbn;intuition congruence)ltac:(cbn;intuition congruence)
 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
 ltac:(apply Read;unfold DWframe,DSframe,DEframe;cbn;tauto)
 ltac:(apply Read;unfold DWframe,DSframe,DEframe;cbn;tauto)Reads HighWritable TargetWritable Pointer
 ltac:(lia)ltac:(lia)ltac:(exists 6;left;split;[lia|reflexivity])
 ltac:(discriminate)ltac:(discriminate))
 as(bs&byblock&Mi&Mf&Fresh&Away&FreshY&Scheduled&High&Target&CPU&Dead&OldFrame).
 assert(Frame:forall b i,b<>bs ->b<>81%positive ->b<>82%positive ->b<>85%positive ->get Mf(b,i)=get Mb(b,i))
 by(intros;eapply OldFrame;eassumption).
 assert(Counter:load Tint32 Mf(85%positive,0%Z)=Some(Vint32 c)).
 { etransitivity;[apply V293_load_block_frame;intro i;apply OldFrame;try discriminate;
   intro E;apply Away;cbn;tauto|apply Read;unfold DWframe;apply in_or_app;right;cbn;tauto]. }
 assert(CountWritable:V293_bytes_writable Mf 85%positive 0%Z 4).
 { intros k Range;destruct(CounterWritable k Range)as(v&Cell);exists v;rewrite OldFrame by
   (try discriminate;intro E;apply Away;cbn;tauto);exact Cell. }
 assert(TaskFrame:V293_task_records Mf(DEblocked(Int.repr 3))).
 { intros t pr st msg Get;eapply V293_task_record_frame;[ |apply Records;exact Get].
   intros i;apply Frame;try(intro E;discriminate E).
   - destruct(DStask_blocks t pr st msg Get)as[E|E];subst t;cbn;intro E;apply Away;cbn;tauto.
   - destruct(DStask_blocks t pr st msg Get)as[E|E];subst t;discriminate.
   - destruct(DStask_blocks t pr st msg Get)as[E|E];subst t;discriminate.
   - destruct(DStask_blocks t pr st msg Get)as[E|E];subst t;discriminate. }
 assert(Canary:load Tint32 Mf(90%positive,0%Z)=Some(Vint32(Int.repr 99))).
 { etransitivity;[apply V293_load_block_frame;intro i;apply Frame;try discriminate;
   intro E;apply Away;cbn;tauto|apply Read;unfold DWframe,DSframe,DEframe;cbn;tauto]. }
 assert(Cache:load Tint8 Mf(84%positive,0%Z)=Some(V293_byteval 4)).
 { etransitivity;[apply V293_load_block_frame;intro i;apply Frame;try discriminate;
   intro E;apply Away;cbn;tauto|apply Read;unfold DWframe;apply in_or_app;right;cbn;tauto]. }
 assert(CurrentWritable:V293_bytes_writable Mf 10%positive 0%Z 4).
 { assert(Owned:V293_bytes_writable Mb 10%positive 0%Z 4).
   { eapply DScell_writable with(cells:=V293_dly_cells 10%positive 11%positive 12%positive 60%positive 30%positive 31%positive
     0%Z 4(Int.repr 3)(Int.repr 3)(V293_byteval 0)64 0 1)(v:=Vptr OwnershipReady)(tp:=Tptr V293_tcb_type);
     [cbn[V293_dly_cells];right;left;reflexivity|exact Cells]. }
   intros k Range;destruct(Owned k Range)as(v&Cell);exists v;rewrite Frame by
   (try discriminate;intro E;apply Away;cbn;tauto);exact Cell. }
 exists bs;exists byblock;exists Mf;split.
 - unfold DWprefix;eapply V293_local_trans;[exact Blocked|exact Scheduled].
 - split;[exact Step| ];split;[exact TaskFrame| ];split;[exact Bitmap| ];
   split;[exact High| ];split;[exact Target| ];split;[exact Counter| ];split;[exact Cache| ];split;[exact CurrentWritable| ];split;[exact Canary| ];split;[exact CPU| ];split;[exact Dead| ];split;[intro E;apply Away;rewrite E;cbn;tauto| ];split;[intro E;apply Away;rewrite E;cbn;tauto|exact CountWritable].
Qed.

Definition DWtail (count:bool):stmts:=sifthen(V293_OSSched_different 115%Z 118%Z)
 (if count then sseq(V293_OSSched_increment 119%Z)(sprim(switch 116%Z)) else sprim(switch 116%Z)).
Lemma DWtail_execution : forall count bs M,
 load Tint8 M(81%positive,0%Z)=Some(V293_byteval 6) ->
 load Tint8 M(84%positive,0%Z)=Some(V293_byteval 4) ->
 load Tint32 M(85%positive,0%Z)=Some(Vint32 Int.zero) ->
 V293_bytes_writable M 85%positive 0%Z 4 ->
 exists Mf,
 cstepstar DSprogram(curs(DWtail count),(kenil,DScontinuation))(DWge,V293_cpu_lenv 501%Z bs,M)
 (curs(sprim(switch 116%Z)),(kenil,DScontinuation))(DWge,V293_cpu_lenv 501%Z bs,Mf) /\
 load Tint32 Mf(85%positive,0%Z)=Some(Vint32(if count then Int.add Int.zero Int.one else Int.zero)) /\
 (forall b i,b<>85%positive ->get Mf(b,i)=get M(b,i)).
Proof.
 intros count bs M High Cache Counter Writable;destruct count.
 - destruct(V293_sched_change_raw DSprogram DScontinuation DWge(V293_cpu_lenv 501%Z bs)M
   115%Z 118%Z 119%Z(sprim(switch 116%Z))81%positive 84%positive 85%positive 6 4 Int.zero
   ltac:(lia)ltac:(lia)ltac:(discriminate)eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
   High Cache Counter Writable)as(Mf&Run&Store&Read&Frame).
   exists Mf;split;[exact Run| ];split;[exact Read|intros;apply Frame;left;assumption].
 - destruct(V293_OSSched_byte_comparison_eval DWge(V293_cpu_lenv 501%Z bs)M
   115%Z 118%Z 81%positive 84%positive 6 4 ltac:(lia)ltac:(lia)
   eq_refl eq_refl eq_refl eq_refl High Cache)as[Guard GuardType].
   exists M;split.
   + unfold DWtail.
     eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply sifthen_step]| ].
     eapply V293_cstepstar_trans;[apply V293_expr_steps;apply evalval_imply_estepstar;exact Guard| ].
     eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply svift_step;reflexivity]|apply c_stepstar0].
   + split;[exact Counter|reflexivity].
Qed.

(* Shared incoming state and actual prefix for both tail variants.  This is
   not a claim that the mutated fragment belongs to the original call body. *)
Theorem DWablation_run : exists bs byblock Mr,
 DWprefix Int.zero true bs Mr /\forall count,exists Mcut Mf,
 cstepstar DSprogram(curs(DWtail count),(kenil,DScontinuation))(DWge,V293_cpu_lenv 501%Z bs,Mr)
 (curs(sprim(switch 116%Z)),(kenil,DScontinuation))(DWge,V293_cpu_lenv 501%Z bs,Mcut) /\
 lpstep DWprog DWtasks DWclient(DWge,DWenvs bs,Mcut,(fun _=>false),DWaux true)OwnershipReady
 (set DWtasks OwnershipReady(SKIP,(kenil,DScontinuation)))DWclient
 (DWge,DWenvs bs,Mf,(fun _=>false),DWaux true)OwnershipWaiting /\
 V293_task_records Mf(DEblocked(Int.repr 3)) /\
 load(Tptr V293_tcb_type)Mf(10%positive,0%Z)=Some(Vptr OwnershipWaiting) /\
 load Tint32 Mf(90%positive,0%Z)=Some(Vint32(Int.repr 99)) /\
 V293_bytes_writable Mf bs 0%Z 4 /\get Mf(byblock,0%Z)=None /\
 load Tint32 Mf(85%positive,0%Z)=Some(Vint32(if count then Int.add Int.zero Int.one else Int.zero)).
Proof.
 destruct(DWblocked_prefix Int.zero true)
 as(bs&byblock&Mr&Prefix&Step&Records&Bitmap&High&Target&Counter&Cache&Writable&Canary&CPU&Dead&Away&BK&WK).
 exists bs;exists byblock;exists Mr;split;[exact Prefix| ];intro count.
 destruct(DWtail_execution count bs Mr High Cache Counter WK)as(Mcut&Tail&Count&Frame).
 assert(TargetCut:load(Tptr V293_tcb_type)Mcut(82%positive,0%Z)=Some(Vptr OwnershipWaiting)).
 { etransitivity;[apply V293_load_block_frame;intro i;apply Frame;discriminate|exact Target]. }
 assert(WritableCut:V293_bytes_writable Mcut 10%positive 0%Z 4).
 { intros k Range;destruct(Writable k Range)as(v&Cell);exists v;rewrite Frame by discriminate;exact Cell. }
 destruct(V293_sched_switch_commit (fun _=>None)DSprogram(fun _=>None)(fun _=>None)DWtasks DWclient
 DScontinuation OwnershipReady OwnershipWaiting 116%Z 82%positive 10%positive V293_tcb_type
 DWge(V293_cpu_lenv 501%Z bs)(DWenvs bs)Mcut(fun _=>false)(false,nil,[true])(DWaux true)
 eq_refl eq_refl eq_refl eq_refl TargetCut eq_refl WritableCut)as(Mf&Switch&Store&Current&SwitchFrame).
 assert(YK:byblock<>85%positive).
 { intro E;destruct(WK 0 ltac:(lia))as(v&Cell);cbn in Cell;rewrite <-E,Dead in Cell;discriminate. }
 assert(YC:byblock<>10%positive).
 { intro E;destruct(Writable 0 ltac:(lia))as(v&Cell);cbn in Cell;rewrite <-E,Dead in Cell;discriminate. }
 assert(Net:forall b i,b<>10%positive ->b<>85%positive ->get Mf(b,i)=get Mr(b,i)).
 { intros b i NC NK;rewrite SwitchFrame by(left;exact NC);apply Frame;exact NK. }
 exists Mcut;exists Mf;split;[exact Tail| ];split;[exact Switch| ];split.
 - intros t pr st msg Get;eapply V293_task_record_frame;[ |apply Records;exact Get].
   intros i;apply Net;destruct(DStask_blocks t pr st msg Get)as[E|E];subst t;discriminate.
 - split;[exact Current| ];split.
   + etransitivity;[apply V293_load_block_frame;intro i;apply Net;discriminate|exact Canary].
   + split.
     * intros k Range;destruct(CPU k Range)as(v&Cell);exists v;rewrite Net by assumption;exact Cell.
     * split;[rewrite Net by assumption;exact Dead| ].
       etransitivity;[apply V293_load_block_frame;intro i;apply SwitchFrame;left;discriminate|exact Count].
Qed.
