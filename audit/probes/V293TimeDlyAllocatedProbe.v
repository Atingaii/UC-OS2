(* One real allocated call, one evolving heap, actual scheduler and switch. *)
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

Definition DAprogram:progunit:=fun f=>match DSprogram f with
 |Some fn=>Some fn|None=>if Z.eq_dec f 1200%Z then Some DCfunction else None end.
Definition DAframe wrong(c:int32):list V293_record_cell:=
 [((90%positive,0%Z),Tint32,Vint32(Int.repr 99));
  ((81%positive,0%Z),Tint8,V293_byteval 0);((82%positive,0%Z),Tptr V293_tcb_type,Vnull)]++
 V293_priority_cells 83%positive 0%Z(DSentries wrong)++
 [((84%positive,0%Z),Tint8,V293_byteval 4);((85%positive,0%Z),Tint32,Vint32 c)].
Definition DAinput:=V293_dly_call_cells 10%positive 60%positive 30%positive 31%positive
 70%positive 71%positive 0%Z 4 Int.zero 80 0.
Definition DAsmall wrong c:=DAinput++(DLextra++(DLlow++DAframe wrong c)).
Definition DAmem wrong c:=merge(OwnershipCellsMemory(DAsmall wrong c))DSlookup.
Definition DAstate M enabled O:RstateOP:=(DWge,DCle,M,(fun _=>false),(enabled,nil,nil),O,spec_done None).
Definition DAresources wrong c:=V293_owned_record_cells(DAframe wrong c) **
 V293_read_bytes 80%positive 0%Z V293_ready_table.
Definition DAcontinuation:=kseq(sseq(sprim excrit)sret)
 (kcall 112%Z(V293_OSSched_success_body 501%Z 110%Z 111%Z 113%Z 117%Z 115%Z 116%Z 118%Z 119%Z)
 DCle(kseq sret DCouter)).

Lemma DAsmall_spatial:forall wrong c,DAstate(OwnershipCellsMemory(DAsmall wrong c))false emp|=
 V293_owned_record_cells(DAsmall wrong c).
Proof.
 intros wrong c;apply OwnershipCellsSpatial.
 - apply DSseparated_sound;destruct wrong;vm_compute;reflexivity.
 - destruct wrong;repeat constructor;vm_compute;reflexivity.
Qed.
Lemma DAjoin:forall wrong c,join(OwnershipCellsMemory(DAsmall wrong c))DSlookup(DAmem wrong c).
Proof.
 intros wrong c;apply map_join_merge;apply map_disjoint;intros[b i].
 destruct(Pos.eq_dec b 80%positive)as[Same|Other].
 - subst b;left;apply OwnershipCellsOutside;destruct wrong;vm_compute;
   intro H;repeat destruct H as[H|H];congruence.
 - right;left;unfold DSlookup,V293_nat_memory;apply V293_encoded_memory_outside;left;exact Other.
Qed.
Lemma DAentry:forall wrong c enabled,DAstate(DAmem wrong c)enabled DCabs|=
 V293_owned_record_cells DAinput **(V293_owned_record_cells DLextra **
 (V293_owned_task_records(del DLtasks OwnershipReady) **
 (V293_shared_fields OwnershipReady DLtasks(emp:EcbMod.map)(Int.repr 37) **DAresources wrong c))).
Proof.
 intros wrong c enabled;pose proof(DAsmall_spatial wrong c)as Cells.
 apply(proj1(OwnershipCellsAppend DAinput(DLextra++(DLlow++DAframe wrong c))_))in Cells.
 assert(Physical:V293_target_wstate DWge DCle(OwnershipCellsMemory(DAsmall wrong c))emp|=
 V293_owned_record_cells DAinput **(V293_owned_record_cells DLextra **
 (V293_owned_record_cells DLlow **V293_owned_record_cells(DAframe wrong c)))).
 { eapply astar_mono;[intros st H;exact H| |exact Cells].
   intros st H;apply OwnershipCellsAppend in H.
   eapply astar_mono;[intros st' H';exact H'| |exact H].
   intros st' H';apply OwnershipCellsAppend in H';exact H'. }
 assert(WithLookup:V293_target_wstate DWge DCle(DAmem wrong c)emp|=
 (V293_owned_record_cells DAinput **(V293_owned_record_cells DLextra **
 (V293_owned_record_cells DLlow **V293_owned_record_cells(DAframe wrong c)))) **
 V293_read_bytes 80%positive 0%Z V293_ready_table).
 { eapply V293_wstate_star;[apply DAjoin|exact Physical|apply V293_read_bytes_witness]. }
 assert(Joint:V293_target_wstate DWge DCle(DAmem wrong c)DCabs|=
 ((V293_owned_record_cells DAinput **(V293_owned_record_cells DLextra **
 (V293_owned_record_cells DLlow **V293_owned_record_cells(DAframe wrong c)))) **
 V293_read_bytes 80%positive 0%Z V293_ready_table) **
 V293_shared_fields OwnershipReady DLtasks(emp:EcbMod.map)(Int.repr 37)).
 { eapply V293_target_wstate_star with(m1:=DAmem wrong c)(m2:=emp)(o1:=emp)(o2:=DCabs).
   - apply map_join_emp.
   - apply map_join_comm;apply map_join_emp.
   - exact WithLookup.
   - exact(V293_shared_fixture_fields OwnershipReady DLtasks(emp:EcbMod.map)(Int.repr 37)). }
 assert(Reordered:V293_target_wstate DWge DCle(DAmem wrong c)DCabs|=V293_owned_record_cells DAinput **
 (V293_owned_record_cells DLextra **(V293_owned_record_cells DLlow **
 (V293_shared_fields OwnershipReady DLtasks(emp:EcbMod.map)(Int.repr 37) **DAresources wrong c))))
 by(unfold DAresources;clear -Joint;sep auto).
 change(DAstate(DAmem wrong c)enabled DCabs|=V293_owned_record_cells DAinput **
 (V293_owned_record_cells DLextra **(V293_owned_record_cells DLlow **
 (V293_shared_fields OwnershipReady DLtasks(emp:EcbMod.map)(Int.repr 37) **DAresources wrong c))))in Reordered.
 eapply astar_mono;[intros st H;exact H| |exact Reordered].
 intros st H;eapply astar_mono;[intros st' H';exact H'| |exact H].
 intros st' H';eapply astar_mono;[apply DTlow_owned|intros st'' H'';exact H''|exact H'].
Qed.
Lemma DAfresh:forall wrong c b,b=11%positive \/b=12%positive \/b=13%positive ->fresh(DAmem wrong c)b.
Proof.
 intros wrong c b Choice l i E[v Bound];subst l.
 change(get(DAmem wrong c)(b,i)=Some v)in Bound.
 assert(Absent:get(DAmem wrong c)(b,i)=None).
 { unfold DAmem;rewrite map_merge_semp by reflexivity.
   rewrite OwnershipCellsOutside.
   - assert(L:get DSlookup(b,i)=None).
     { unfold DSlookup,V293_nat_memory;apply V293_encoded_memory_outside;left;intuition congruence. }
     rewrite L;reflexivity.
   - destruct Choice as[Same|[Same|Same]];subst b;destruct wrong;
     vm_compute;intro H;repeat destruct H as[H|H];congruence. }
 congruence.
Qed.
Lemma DAenv:V293_dly_env 103%Z 106%Z 105%Z 400%Z 401%Z
 10%positive 11%positive 12%positive 30%positive 31%positive DWge DCle.
Proof. repeat split;reflexivity. Qed.

Definition DAobserved:list V293_record_cell:=
 [((60%positive,44%Z),Tint32,Vint32(Int.repr 3));
  ((11%positive,0%Z),Tint8,V293_byteval 0);
  ((12%positive,0%Z),Tint32,Vint32(Int.repr 3));
  ((13%positive,0%Z),Tint32,Vint32 Int.zero);
  ((30%positive,0%Z),Tint8,V293_byteval 64);((30%positive,1%Z),Tint8,V293_byteval 0);
  ((31%positive,0%Z),Tint8,V293_byteval 1)].
Definition DAfacts(M:mem):Prop:=
 (forall a tp v,In(a,tp,v)DAobserved ->load tp M a=Some v) /\
 V293_bytes_writable M 13%positive 0%Z 4.

Definition DArun wrong c enabled bs Mf:=
 V293_local_steps DAprogram(curs(scall 1200%Z[econst32(Int.repr 3)]),(kenil,kstop))
 ((DWge,emp,DAmem wrong c),(fun _=>false),(enabled,nil,nil))
 (curs(sprim(switch 116%Z)),(kenil,DAcontinuation))
 ((DWge,V293_cpu_lenv 501%Z bs,Mf),(fun _=>false),(false,nil,enabled::nil)).

Theorem DAallocated_run:forall wrong c enabled,exists bs byblock Mf,
 DArun wrong c enabled bs Mf /\
 spec_step(fun _ _=>False)(spec_prim(cons(Vint32(Int.repr 3))nil)V293_dly_block_step)
 DEabs(END None)(DEfinalabs(Int.repr 3)) /\
 V293_task_records Mf(DEblocked(Int.repr 3)) /\
 V293_bitmap_tasks 64 0(DEblocked(Int.repr 3)) /\
 load Tint8 Mf(81%positive,0%Z)=Some(V293_byteval 6) /\
 load(Tptr V293_tcb_type)Mf(82%positive,0%Z)=Some(Vptr(DStarget wrong)) /\
 load Tint32 Mf(85%positive,0%Z)=Some(Vint32(Int.add c Int.one)) /\
 load Tint8 Mf(84%positive,0%Z)=Some(V293_byteval 4) /\
 V293_bytes_writable Mf 10%positive 0%Z 4 /\
 load Tint32 Mf(90%positive,0%Z)=Some(Vint32(Int.repr 99)) /\
 V293_bytes_writable Mf bs 0%Z 4 /\get Mf(byblock,0%Z)=None /\bs<>10%positive /\DAfacts Mf.
Proof.
 intros wrong c enabled.
 destruct(V293_dly_allocated_to_sched_refines DAprogram kstop DWge emp(DAmem wrong c)
 (fun _=>false)enabled nil nil DCabs(spec_done None)(fun _ _=>False)(DAresources wrong c)
 1200%Z 103%Z 106%Z 105%Z 400%Z 401%Z 110%Z 111%Z 112%Z 402%Z
 12%positive 11%positive 13%positive 10%positive 60%positive 30%positive 31%positive
 70%positive 71%positive 0%Z 4(Int.repr 3)Int.zero 80 0 DLentries DLtasks Vnull(emp:EcbMod.map)(Int.repr 37)
 eq_refl ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)
 ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)
 (DAfresh wrong c 12%positive ltac:(tauto))(DAfresh wrong c 11%positive ltac:(tauto))
 (DAfresh wrong c 13%positive ltac:(tauto))DAenv eq_refl eq_refl eq_refl eq_refl
 ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(change(54<=4294967295)%Z;lia)
 ltac:(discriminate)DLtable DLbitmap eq_refl(DAentry wrong c enabled)) as(Mb&Blocked&Step&Records&Table&Bitmap&Returned).
 set(S:=(DWge,DCle,Mb,(fun _:hid=>false),(enabled,(nil:list hid),(nil:list bool)),DEfinalabs(Int.repr 3),spec_done None)).
 assert(Cells:S|=V293_owned_record_cells
 (V293_dly_cells 10%positive 11%positive 12%positive 60%positive 30%positive 31%positive
 0%Z 4(Int.repr 3)(Int.repr 3)(V293_byteval 0)64 0 1) **Atrue)
 by(unfold S;clear -Returned;sep auto).
 assert(Control:S|=V293_owned_record_cells(DAframe wrong c) **Atrue)
 by(unfold S;unfold DAresources in Returned;clear -Returned;sep auto).
 assert(Lookup:S|=V293_read_bytes 80%positive 0%Z V293_ready_table **Atrue)
 by(unfold S;unfold DAresources in Returned;clear -Returned;sep auto).
 assert(Guards:S|=V293_owned_record_cells(V293_dly_guard_cells 70%positive 71%positive) **Atrue)
 by(unfold S;clear -Returned;sep auto).
 assert(RawCPU:S|=Amapsto(13%positive,0%Z)Tint32 true(Vint32 Int.zero) **Atrue)
 by(unfold S;clear -Returned;sep auto).
 assert(Read:forall a tp v,In(a,tp,v)(DAframe wrong c)->load tp Mb a=Some v).
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
 destruct(V293_owned_cells_byte_writable(DAframe wrong c)(81%positive,0%Z)(V293_byteval 0)Atrue
 DWge DCle Mb(fun _=>false)(enabled,nil,nil)(DEfinalabs(Int.repr 3))(spec_done None)
 ltac:(unfold DAframe;cbn;tauto)Control)as(oldhigh&HighWritable).
 assert(TargetWritable:V293_bytes_writable Mb 82%positive 0%Z 4).
 { eapply DScell_writable with(cells:=DAframe wrong c)(v:=Vnull)(tp:=Tptr V293_tcb_type);
   [unfold DAframe;cbn;tauto|exact Control]. }
 assert(Pointer:load(Tptr V293_tcb_type)Mb(83%positive,24%Z)=Some(Vptr(DStarget wrong))).
 { apply Read;unfold DAframe;apply in_or_app;right;apply in_or_app;left.
   pose proof(V293_priority_cells_nth(DSentries wrong)6 83%positive 0%Z ltac:(change(6<13);lia))as Member.
   exact Member. }
 assert(CounterWritable:V293_bytes_writable Mb 85%positive 0%Z 4).
 { eapply DScell_writable with(cells:=DAframe wrong c)(v:=Vint32 c)(tp:=Tint32);
   [unfold DAframe;apply in_or_app;right;apply in_or_app;right;cbn;tauto|exact Control]. }
 destruct(V293_sched_call_to_switch DAprogram(kseq sret DCouter)DWge DCle Mb(fun _=>false)enabled nil nil
 [60%positive;41%positive;90%positive;10%positive;84%positive;11%positive;12%positive;13%positive;30%positive;31%positive]
 112%Z 501%Z 110%Z 111%Z 113%Z 117%Z 115%Z 116%Z 118%Z 119%Z 114%Z 105%Z 106%Z 500%Z
 80%positive 31%positive 30%positive 81%positive 70%positive 71%positive 83%positive 82%positive 84%positive 85%positive 64 0 oldhigh 4 c(DStarget wrong)
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
       DWge DCle Mb(fun _=>false)(enabled,nil,nil)(DEfinalabs(Int.repr 3))(spec_done None));exact RawCPU. }
     intros k Range;destruct(W k Range)as(v&Cell);exists v;rewrite Frame by
       (try discriminate;intro E;apply Away;cbn;tauto);exact Cell. }
 exists bs;exists byblock;exists Mf;split.
 - unfold DArun;eapply V293_local_trans;[exact Blocked|exact Scheduled].
 - split;[exact Step| ];split;[exact TaskFrame| ];split;[exact Bitmap| ];
   split;[exact High| ];split;[exact Target| ];split;[exact Counter| ];split;[exact Cache| ];split;[exact CurrentWritable| ];split;[exact Canary| ];split;[exact CPU| ];split;[exact Dead| ];split;[intro E;apply Away;rewrite E;cbn;tauto|exact Facts].
Qed.


Lemma DAfacts_frame:forall M N,
 (forall b i,b<>10%positive ->get N(b,i)=get M(b,i)) ->DAfacts M ->DAfacts N.
Proof.
 intros M N Frame[Values Writable];split.
 - intros[b off]tp v Member;etransitivity;[apply V293_load_block_frame;intro i;apply Frame|apply Values;exact Member].
   cbn[DAobserved In]in Member;repeat destruct Member as[Member|Member];try contradiction;
   inversion Member;subst;discriminate.
 - intros k Range;destruct(Writable k Range)as(v&Cell);exists v;rewrite Frame by discriminate;exact Cell.
Qed.
Definition DAtasks:tasks:=set(sig OwnershipWaiting DWready)OwnershipReady
 (curs(sprim(switch 116%Z)),(kenil,DAcontinuation)).
Definition DAenvs bs:cltenvs:=set(sig OwnershipWaiting DCle)OwnershipReady(V293_cpu_lenv 501%Z bs).
Definition DAprog:lprog:=((fun _=>None),(DAprogram,(fun _=>None),(fun _=>None))).
Definition DAhigh:code:=(curs(hapi_code(sched;;spec_done None)),(kenil,DAcontinuation)).
Definition DAhighafter:code:=(curs(hapi_code(spec_done None)),(kenil,DAcontinuation)).
Definition DAhightasks:tasks:=set(sig OwnershipWaiting DWready)OwnershipReady DAhigh.

Theorem DAhigh_switch:
 hpstep DWhighprog DAhightasks DWclient(DEfinalabs(Int.repr 3))
 (set DAhightasks OwnershipReady DAhighafter)DWclient
 (set(DEfinalabs(Int.repr 3))curtid(oscurt OwnershipWaiting)) /\
 get(set DAhightasks OwnershipReady DAhighafter)OwnershipReady=Some DAhighafter /\
 get(set DAhightasks OwnershipReady DAhighafter)OwnershipWaiting=Some DWready.
Proof.
 split.
 - eapply hswi_step;[reflexivity|exact DWselected|reflexivity|reflexivity|reflexivity|reflexivity].
 - split;reflexivity.
Qed.

Theorem DAallocated_switch:forall c enabled,exists bs byblock Mcut Mf,
 DArun false c enabled bs Mcut /\
 lpstep DAprog DAtasks DWclient(DWge,DAenvs bs,Mcut,(fun _=>false),DWaux enabled)OwnershipReady
 (set DAtasks OwnershipReady(SKIP,(kenil,DAcontinuation)))DWclient
 (DWge,DAenvs bs,Mf,(fun _=>false),DWaux enabled)OwnershipWaiting /\
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
 intros c enabled;destruct(DAallocated_run false c enabled)
 as(bs&byblock&Mcut&Run&Step&Records&Bitmap&High&Target&Count&Cache&Writable&Canary&CPU&Dead&Away&Facts).
 destruct(V293_sched_switch_commit (fun _=>None)DAprogram(fun _=>None)(fun _=>None)DAtasks DWclient
 DAcontinuation OwnershipReady OwnershipWaiting 116%Z 82%positive 10%positive V293_tcb_type
 DWge(V293_cpu_lenv 501%Z bs)(DAenvs bs)Mcut(fun _=>false)(false,nil,[enabled])(DWaux enabled)
 eq_refl eq_refl eq_refl eq_refl Target eq_refl Writable)as(Mf&Switch&Store&Current&Frame).
 assert(Y:byblock<>10%positive).
 { intro E;destruct(Writable 0 ltac:(lia))as(v&Cell);cbn in Cell;rewrite <-E,Dead in Cell;discriminate. }
 exists bs;exists byblock;exists Mcut;exists Mf;split;[exact Run| ];split;[exact Switch| ];split;[exact Current| ];split.
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

Theorem DAboth_IE:
 (exists (bs byblock:block)(Mcut Mf:mem),DArun false Int.zero true bs Mcut /\
 lpstep DAprog DAtasks DWclient(DWge,DAenvs bs,Mcut,(fun _=>false),DWaux true)OwnershipReady
 (set DAtasks OwnershipReady(SKIP,(kenil,DAcontinuation)))DWclient
 (DWge,DAenvs bs,Mf,(fun _=>false),DWaux true)OwnershipWaiting) /\
 (exists (bs byblock:block)(Mcut Mf:mem),DArun false Int.zero false bs Mcut /\
 lpstep DAprog DAtasks DWclient(DWge,DAenvs bs,Mcut,(fun _=>false),DWaux false)OwnershipReady
 (set DAtasks OwnershipReady(SKIP,(kenil,DAcontinuation)))DWclient
 (DWge,DAenvs bs,Mf,(fun _=>false),DWaux false)OwnershipWaiting).
Proof.
 split;[destruct(DAallocated_switch Int.zero true)as(bs&byblock&Mcut&Mf&Run&Step&Rest)|
 destruct(DAallocated_switch Int.zero false)as(bs&byblock&Mcut&Mf&Run&Step&Rest)];
 exists bs;exists byblock;exists Mcut;exists Mf;auto.
Qed.

Theorem DAwrap_run:forall enabled,exists (bs byblock:block)(Mf:mem),
 DArun false(Int.repr Int.max_unsigned)enabled bs Mf /\DAfacts Mf /\
 load Tint32 Mf(85%positive,0%Z)=Some(Vint32 Int.zero).
Proof.
 intro enabled;destruct(DAallocated_run false(Int.repr Int.max_unsigned)enabled)
 as(bs&byblock&Mf&Run&Step&Records&Bitmap&High&Target&Count&Cache&Writable&Canary&CPU&Dead&Away&Facts).
 exists bs;exists byblock;exists Mf;split;[exact Run| ];split;[exact Facts|rewrite DWcounter_wrap in Count;exact Count].
Qed.

(* The two initial cell lists differ at exactly one pointer, not code. *)
Lemma DAonly_slot:forall c,
 DAframe false c=firstn 9(DAframe false c)++
 [((83%positive,24%Z),Tptr V293_tcb_type,Vptr OwnershipWaiting)]++skipn 10(DAframe false c) /\
 DAframe true c=firstn 9(DAframe false c)++
 [((83%positive,24%Z),Tptr V293_tcb_type,Vptr OwnershipReady)]++skipn 10(DAframe false c).
Proof. intro c;split;reflexivity. Qed.

(* Local prefix succeeds; the published target gate rejects only at the end.
   The wrong physical table is not a successful abstract scheduler refinement. *)
Theorem DAwrong_target:forall c enabled,exists bs byblock Mf,
 DArun true c enabled bs Mf /\
 V293_task_records Mf(DEblocked(Int.repr 3)) /\V293_bitmap_tasks 64 0(DEblocked(Int.repr 3)) /\
 load Tint8 Mf(81%positive,0%Z)=Some(V293_byteval 6) /\
 load Tint32 Mf(85%positive,0%Z)=Some(Vint32(Int.add c Int.one)) /\
 load Tint8 Mf(84%positive,0%Z)=Some(V293_byteval 4) /\
 load Tint32 Mf(90%positive,0%Z)=Some(Vint32(Int.repr 99)) /\
 V293_bytes_writable Mf bs 0%Z 4 /\get Mf(byblock,0%Z)=None /\DAfacts Mf /\
 load(Tptr V293_tcb_type)Mf(82%positive,0%Z)=Some(Vptr OwnershipReady) /\
 load(Tptr V293_tcb_type)Mf(82%positive,0%Z)<>Some(Vptr OwnershipWaiting) /\
 ~V293_priority_table(DSentries true)(DEblocked(Int.repr 3)).
Proof.
 intros c enabled;destruct(DAallocated_run true c enabled)
 as(bs&byblock&Mf&Run&Step&Records&Bitmap&High&Target&Count&Cache&Writable&Canary&CPU&Dead&Away&Facts).
 exists bs;exists byblock;exists Mf;split;[exact Run| ];split;[exact Records| ];split;[exact Bitmap| ];
 split;[exact High| ];split;[exact Count| ];split;[exact Cache| ];split;[exact Canary| ];
 split;[exact CPU| ];split;[exact Dead| ];split;[exact Facts| ];split;[exact Target| ];split.
 - rewrite Target;discriminate.
 - exact DSmutant_outside_table.
Qed.
