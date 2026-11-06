(* Nonempty delay-to-scheduler execution. Test fixtures, not boot reachability.
   The mutant changes one pointer-table slot only, never the program. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeDlySchedCall.
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
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition DStarget(wrong:bool):=if wrong then OwnershipReady else OwnershipWaiting.
Definition DSentries wrong:=update_nth_val 6 DLentries(Vptr(DStarget wrong)).
Definition DSge:env:=set(set(set(set DEge 114%Z(80%positive,Tarray Tint8 256))
 115%Z(81%positive,Tint8))116%Z(82%positive,Tptr V293_tcb_type))
 117%Z(83%positive,Tarray(Tptr V293_tcb_type)13).
Definition DSframe wrong:=DEframe 0 0++
 [((81%positive,0%Z),Tint8,V293_byteval 0);((82%positive,0%Z),Tptr V293_tcb_type,Vnull)]++
 V293_priority_cells 83%positive 0%Z(DSentries wrong).
Definition DSsmall wrong:=DEcells(Int.repr 3)++(DLextra++(DLlow++DSframe wrong)).
Definition DSlookup:=V293_nat_memory 80%positive 0%Z V293_ready_table.
Definition DSmem wrong:=merge(OwnershipCellsMemory(DSsmall wrong))DSlookup.
Definition DSstate M O:=V293_target_wstate DSge DEle M O.
Definition DSresources wrong:=V293_owned_record_cells(DSframe wrong) **
 V293_read_bytes 80%positive 0%Z V293_ready_table.
Definition DSfunction:=V293_OSSched_success_function 501%Z 110%Z 111%Z 113%Z 117%Z 115%Z 116%Z 118%Z 119%Z.
Definition DShelper:=V293_OSSchedNew_function 114%Z 105%Z 106%Z 115%Z 500%Z.
Definition DSprogram : progunit:=fun f=>if Z.eq_dec f 112%Z then Some DSfunction else
 if Z.eq_dec f 113%Z then Some DShelper else None.
Definition DSchange:=V293_OSSched_change 115%Z 118%Z 119%Z(sprim(switch 116%Z)).
Definition DScontinuation:=kseq(sseq(sprim excrit)sret)
 (kcall 112%Z(V293_OSSched_success_body 501%Z 110%Z 111%Z 113%Z 117%Z 115%Z 116%Z 118%Z 119%Z)
 DEle(kseq sret kstop)).

(* Executable separation check with a proved interpretation; avoids building
   a large propositional disjunction proof for every literal byte pair. *)
Definition DSaddr_dec(a b:addr):{a=b}+{a<>b}.
Proof. decide equality;[apply Z.eq_dec|apply Pos.eq_dec]. Defined.
Fixpoint DSseparated(cells:list V293_record_cell):bool:=match cells with
 | []=>true
 | cell::rest=>forallb(fun a=>if in_dec DSaddr_dec a(OwnershipCellsAddresses rest)
   then false else true)(OwnershipCellAddresses cell)&&DSseparated rest
 end.
Lemma DSseparated_sound : forall cells,DSseparated cells=true ->OwnershipCellsSeparated cells.
Proof.
 induction cells as [ | cell rest IH];intro Checked;[exact I| ].
 cbn[DSseparated]in Checked;apply andb_true_iff in Checked;destruct Checked as[Apart Tail].
 split;[ |apply IH;exact Tail]. intros a Member.
 rewrite forallb_forall in Apart;specialize(Apart a Member).
 destruct(in_dec DSaddr_dec a(OwnershipCellsAddresses rest));[discriminate|assumption].
Qed.
Lemma DSsmall_spatial : forall wrong,DSstate(OwnershipCellsMemory(DSsmall wrong))emp|=
 V293_owned_record_cells(DSsmall wrong).
Proof.
 intro wrong;apply OwnershipCellsSpatial.
 - apply DSseparated_sound;destruct wrong;vm_compute;reflexivity.
 - destruct wrong;repeat constructor;vm_compute;reflexivity.
Qed.
Lemma DSjoin : forall wrong,join(OwnershipCellsMemory(DSsmall wrong))DSlookup(DSmem wrong).
Proof.
 intro wrong;apply map_join_merge;apply map_disjoint;intros[b i].
 destruct(Pos.eq_dec b 80%positive)as[Same|Other].
 - subst b;left;apply OwnershipCellsOutside;destruct wrong;vm_compute;intro H;repeat destruct H as[H|H];congruence.
 - right;left;unfold DSlookup,V293_nat_memory;apply V293_encoded_memory_outside;left;exact Other.
Qed.
Lemma DSentry : forall wrong,DSstate(DSmem wrong)DEabs|=
 V293_owned_record_cells(DEcells(Int.repr 3)) **(V293_owned_record_cells DLextra **
 (V293_owned_task_records(del DLtasks OwnershipReady) **
 (V293_shared_fields OwnershipReady DLtasks(emp:EcbMod.map)(Int.repr 37) **DSresources wrong))).
Proof.
 intro wrong;pose proof(DSsmall_spatial wrong)as Cells.
 apply(proj1(OwnershipCellsAppend(DEcells(Int.repr 3))(DLextra++(DLlow++DSframe wrong))_))in Cells.
 assert(Physical:DSstate(OwnershipCellsMemory(DSsmall wrong))emp|=
 V293_owned_record_cells(DEcells(Int.repr 3)) **(V293_owned_record_cells DLextra **
 (V293_owned_record_cells DLlow **V293_owned_record_cells(DSframe wrong)))).
 { eapply astar_mono;[intros st H;exact H| |exact Cells].
   intros st H;apply OwnershipCellsAppend in H.
   eapply astar_mono;[intros st' H';exact H'| |exact H].
   intros st' H';apply OwnershipCellsAppend in H';exact H'. }
 assert(WithLookup:DSstate(DSmem wrong)emp|=
 (V293_owned_record_cells(DEcells(Int.repr 3)) **(V293_owned_record_cells DLextra **
 (V293_owned_record_cells DLlow **V293_owned_record_cells(DSframe wrong)))) **
 V293_read_bytes 80%positive 0%Z V293_ready_table).
 { eapply V293_wstate_star;[apply DSjoin|exact Physical|apply V293_read_bytes_witness]. }
 assert(Joint:DSstate(DSmem wrong)DEabs|=
 ((V293_owned_record_cells(DEcells(Int.repr 3)) **(V293_owned_record_cells DLextra **
 (V293_owned_record_cells DLlow **V293_owned_record_cells(DSframe wrong)))) **
 V293_read_bytes 80%positive 0%Z V293_ready_table) **
 V293_shared_fields OwnershipReady DLtasks(emp:EcbMod.map)(Int.repr 37)).
 { eapply V293_target_wstate_star with(m1:=DSmem wrong)(m2:=emp)(o1:=emp)(o2:=DEabs).
   - apply map_join_emp.
   - apply map_join_comm;apply map_join_emp.
   - exact WithLookup.
   - exact(V293_shared_fixture_fields OwnershipReady DLtasks(emp:EcbMod.map)(Int.repr 37)). }
 assert(Reordered:DSstate(DSmem wrong)DEabs|=V293_owned_record_cells(DEcells(Int.repr 3)) **
 (V293_owned_record_cells DLextra **(V293_owned_record_cells DLlow **
 (V293_shared_fields OwnershipReady DLtasks(emp:EcbMod.map)(Int.repr 37) **DSresources wrong))))
 by(unfold DSresources;clear -Joint;sep auto).
 eapply astar_mono;[intros st H;exact H| |exact Reordered].
 intros st H;eapply astar_mono;[intros st' H';exact H'| |exact H].
 intros st' H';eapply astar_mono;[apply DTlow_owned|intros st'' H'';exact H''|exact H'].
Qed.
Lemma DScell_writable : forall cells b tp v ge le M ir aux O op,
 In((b,0%Z),tp,v)cells ->
 (ge,le,M,ir,aux,O,op)|=V293_owned_record_cells cells **Atrue ->
 V293_bytes_writable M b 0%Z(typelen tp).
Proof.
 intros cells b tp v ge le M ir aux O op Member Held.
 apply in_split in Member;destruct Member as(left&right&Same);subst cells.
 assert(Split:(ge,le,M,ir,aux,O,op)|=
 (V293_owned_record_cells left **V293_owned_record_cells(((b,0%Z),tp,v)::right)) **Atrue).
 { eapply astar_mono;[apply OwnershipCellsAppend|intros st H;exact H|exact Held]. }
 eapply V293_tick_raw_owned_writable with(v:=v)(R:=Atrue)(ge:=ge)(le:=le)(ir:=ir)(aux:=aux)(O:=O)(op:=op).
 cbn[V293_owned_record_cells]in Split;unfold V293_owned_record_cell in Split;clear -Split;sep auto.
Qed.

Lemma DScells_load : forall cells a tp v ge le M ir aux O op,
 In(a,tp,v)cells ->(ge,le,M,ir,aux,O,op)|=V293_owned_record_cells cells **Atrue ->
 load tp M a=Some v.
Proof.
 intros cells a tp v ge le M ir aux O op Member Held.
 change(load tp(getmem(ge,le,M,ir,aux,O,op))a=Some v).
 eapply V293_record_star_load_l;[apply V293_owned_record_cells_load;exact Member|exact Held].
Qed.
Lemma DSenv:V293_dly_env 103%Z 106%Z 105%Z 400%Z 401%Z
 10%positive 11%positive 12%positive 30%positive 31%positive DSge DEle.
Proof. vm_compute;repeat split;reflexivity. Qed.
Lemma DSinitial_guards : forall wrong,
 load Tint8(DSmem wrong)(70%positive,0%Z)=Some(V293_byteval 0) /\
 load Tint8(DSmem wrong)(71%positive,0%Z)=Some(V293_byteval 0).
Proof.
 intro wrong;pose proof(DSentry wrong)as Entry.
 assert(Owned:DSstate(DSmem wrong)DEabs|=V293_owned_record_cells(DSframe wrong) **Atrue)
 by(unfold DSresources in Entry;clear -Entry;sep auto).
 split;eapply DScells_load;[ |exact Owned| |exact Owned];unfold DSframe,DEframe;cbn;tauto.
Qed.
Lemma DStask_blocks : forall t pr st msg,
 get(DEblocked(Int.repr 3))t=Some(pr,st,msg) ->t=OwnershipReady \/t=OwnershipWaiting.
Proof.
 intros t pr st msg Get;unfold DEblocked in Get.
 destruct(TcbMod.eq_dec t OwnershipReady)as[Same|Apart];[left;exact Same| ].
 rewrite map_get_set' in Get by congruence;unfold DLtasks in Get.
 destruct(TcbMod.eq_dec t OwnershipWaiting)as[Same|ApartW];[right;exact Same| ].
 rewrite map_get_set' in Get by congruence;rewrite map_get_sig' in Get by congruence;discriminate.
Qed.
Definition DSrun wrong enabled bs Mf:=
 V293_local_steps DSprogram(curs DEbody,(kenil,kstop))
 ((DSge,DEle,DSmem wrong),(fun _=>false),(enabled,nil,nil))
 (curs DSchange,(kenil,DScontinuation))
 ((DSge,V293_cpu_lenv 501%Z bs,Mf),(fun _=>false),(false,nil,enabled::nil)).

Theorem DSblocked_run : forall wrong enabled,exists bs byblock Mf,
 DSrun wrong enabled bs Mf /\
 spec_step(fun _ _=>False)(spec_prim(cons(Vint32(Int.repr 3))nil)V293_dly_block_step)
 DEabs(END None)(DEfinalabs(Int.repr 3)) /\
 V293_task_records Mf(DEblocked(Int.repr 3)) /\
 V293_bitmap_tasks 64 0(DEblocked(Int.repr 3)) /\
 load Tint8 Mf(81%positive,0%Z)=Some(V293_byteval 6) /\
 load(Tptr V293_tcb_type)Mf(82%positive,0%Z)=Some(Vptr(DStarget wrong)) /\
 load Tint32 Mf(90%positive,0%Z)=Some(Vint32(Int.repr 99)) /\
 V293_bytes_writable Mf bs 0%Z 4 /\get Mf(byblock,0%Z)=None.
Proof.
 intros wrong enabled;destruct(DSinitial_guards wrong)as[Ln Ll].
 destruct(V293_OSTimeDly_body_to_sched_refines 103%Z 106%Z 105%Z 400%Z 401%Z 110%Z 111%Z 112%Z
 10%positive 11%positive 12%positive 60%positive 30%positive 31%positive 70%positive 71%positive 0%Z 4(Int.repr 3)
 DSprogram kstop DSge DEle(DSmem wrong)(fun _=>false)enabled nil nil DEabs(spec_done None)(fun _ _=>False)
 (DSresources wrong)Int.zero(V293_byteval 0)80 0 DLentries DLtasks Vnull(emp:EcbMod.map)(Int.repr 37)
 DSenv eq_refl eq_refl Ln eq_refl eq_refl Ll ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)
 ltac:(change(54<=4294967295)%Z;lia)ltac:(discriminate)DLtable DLbitmap eq_refl(DSentry wrong))
 as(Mb&Blocked&Step&Records&Table&Bitmap&Returned).
 set(S:=(DSge,DEle,Mb,(fun _:hid=>false),(enabled,(nil:list hid),(nil:list bool)),DEfinalabs(Int.repr 3),spec_done None)).
 assert(Cells:S|=V293_owned_record_cells
 (V293_dly_cells 10%positive 11%positive 12%positive 60%positive 30%positive 31%positive
 0%Z 4(Int.repr 3)(Int.repr 3)(V293_byteval 0)64 0 1) **Atrue)
 by(unfold S;clear -Returned;sep auto).
 assert(Control:S|=V293_owned_record_cells(DSframe wrong) **Atrue)
 by(unfold S;unfold DSresources in Returned;clear -Returned;sep auto).
 assert(Lookup:S|=V293_read_bytes 80%positive 0%Z V293_ready_table **Atrue)
 by(unfold S;unfold DSresources in Returned;clear -Returned;sep auto).
 assert(Read:forall a tp v,In(a,tp,v)(DSframe wrong)->load tp Mb a=Some v).
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
 destruct(V293_owned_cells_byte_writable(DSframe wrong)(81%positive,0%Z)(V293_byteval 0)Atrue
 DSge DEle Mb(fun _=>false)(enabled,nil,nil)(DEfinalabs(Int.repr 3))(spec_done None)
 ltac:(unfold DSframe;cbn;tauto)Control)as(oldhigh&HighWritable).
 assert(TargetWritable:V293_bytes_writable Mb 82%positive 0%Z 4).
 { eapply DScell_writable with(cells:=DSframe wrong)(v:=Vnull)(tp:=Tptr V293_tcb_type);
   [unfold DSframe;cbn;tauto|exact Control]. }
 assert(Pointer:load(Tptr V293_tcb_type)Mb(83%positive,24%Z)=Some(Vptr(DStarget wrong))).
 { apply Read;unfold DSframe;apply in_or_app;right;apply in_or_app;right.
   pose proof(V293_priority_cells_nth(DSentries wrong)6 83%positive 0%Z ltac:(destruct wrong;change(6<13);lia))as Member.
   exact Member. }
 destruct(V293_sched_call_to_change DSprogram(kseq sret kstop)DSge DEle Mb(fun _=>false)enabled nil nil
 [60%positive;41%positive;90%positive]
 112%Z 501%Z 110%Z 111%Z 113%Z 117%Z 115%Z 116%Z 118%Z 119%Z 114%Z 105%Z 106%Z 500%Z
 80%positive 31%positive 30%positive 81%positive 70%positive 71%positive 83%positive 82%positive 64 0 oldhigh(DStarget wrong)
 eq_refl eq_refl ltac:(cbn;intuition congruence)ltac:(cbn;intuition congruence)
 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
 ltac:(apply Read;unfold DSframe,DEframe;cbn;tauto)
 ltac:(apply Read;unfold DSframe,DEframe;cbn;tauto)Reads HighWritable TargetWritable Pointer
 ltac:(lia)ltac:(lia)ltac:(exists 6;left;split;[lia|reflexivity])
 ltac:(discriminate)ltac:(discriminate))as(bs&byblock&Mi&Mf&Fresh&Away&FreshY&Scheduled&High&Target&CPU&Dead&Frame).
 assert(TaskFrame:V293_task_records Mf(DEblocked(Int.repr 3))).
 { intros t pr st msg Get;eapply V293_task_record_frame;[ |apply Records;exact Get].
   intros i;apply Frame;try(intro E;discriminate E).
   - destruct(DStask_blocks t pr st msg Get)as[E|E];subst t;cbn;intro E;apply Away;cbn;tauto.
   - destruct(DStask_blocks t pr st msg Get)as[E|E];subst t;discriminate.
   - destruct(DStask_blocks t pr st msg Get)as[E|E];subst t;discriminate. }
 assert(Canary:load Tint32 Mf(90%positive,0%Z)=Some(Vint32(Int.repr 99))).
 { etransitivity;[apply V293_load_block_frame;intro i;apply Frame;try discriminate;
   intro E;apply Away;cbn;tauto|apply Read;unfold DSframe,DEframe;cbn;tauto]. }
 exists bs;exists byblock;exists Mf;split.
 - unfold DSrun;eapply V293_local_trans;[exact Blocked|exact Scheduled].
 - split;[exact Step| ];split;[exact TaskFrame| ];split;[exact Bitmap| ];
   split;[exact High| ];split;[exact Target| ];split;[exact Canary| ];split;[exact CPU|exact Dead].
Qed.

Lemma DSbaseline_entries : DSentries false=DLentries.
Proof. reflexivity. Qed.
Lemma DSonly_slot : forall wrong p,p<>6 ->nth p(DSentries wrong)Vnull=nth p DLentries Vnull.
Proof.
 intros wrong p Apart;do 7(destruct p as [ | p];[try reflexivity;congruence| ]).
 destruct wrong;reflexivity.
Qed.
Lemma DSblocked_current :
 get(DEfinalabs(Int.repr 3))curtid=Some(oscurt OwnershipReady) /\
 get(DEblocked(Int.repr 3))OwnershipReady=Some(Int.repr 4,wait os_stat_time(Int.repr 3),Vnull) /\
 get(DEblocked(Int.repr 3))OwnershipWaiting=Some(Int.repr 6,rdy,Vptr(120%positive,Int.repr 7)).
Proof. repeat split;reflexivity. Qed.
Lemma DSmutant_outside_table : ~V293_priority_table(DSentries true)(DEblocked(Int.repr 3)).
Proof.
 intros[Length Table].
 destruct(Table OwnershipWaiting(Int.repr 6)rdy(Vptr(120%positive,Int.repr 7))eq_refl)
 as(p&Bound&Priority&Pointer).
 assert(p=6)by(apply V293_priority_repr_injective;[exact Bound|lia|symmetry;exact Priority]).
 subst p;discriminate Pointer.
Qed.
Theorem DSboth_IE :
 (exists bs byblock Mf,DSrun false true bs Mf /\V293_bytes_writable Mf bs 0%Z 4 /\get Mf(byblock,0%Z)=None) /\
 (exists bs byblock Mf,DSrun false false bs Mf /\V293_bytes_writable Mf bs 0%Z 4 /\get Mf(byblock,0%Z)=None).
Proof.
 split;[destruct(DSblocked_run false true)as(bs&byblock&Mf&Exec&Step&Records&Bits&High&Target&Canary&CPU&Dead)|
 destruct(DSblocked_run false false)as(bs&byblock&Mf&Exec&Step&Records&Bits&High&Target&Canary&CPU&Dead)];
 exists bs;exists byblock;exists Mf;repeat split;assumption.
Qed.
