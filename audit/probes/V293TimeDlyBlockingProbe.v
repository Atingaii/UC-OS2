(* Literal nonempty heap for the source blocking fragment. The low-priority
   ready task here is an input fixture, not proof of the preceding wakeup. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSTimeDly.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.certiucos.v293.proofs.V293TimeDlyBlocking.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.
Definition DLge:env:=set(set(sig 103%Z(10%positive,Tptr V293_tcb_type))
 106%Z(30%positive,Tarray Tint8 2))105%Z(31%positive,Tint8).
Definition DLle:env:=set(sig 400%Z(11%positive,Tint8))401%Z(12%positive,Tint32).
Definition DLtasks:TcbMod.map:=set(sig OwnershipReady(Int.repr 4,rdy,Vnull))
 OwnershipWaiting(Int.repr 6,rdy,Vptr(120%positive,Int.repr 7)).
Definition DLentries:list val:=[Vnull;Vnull;Vnull;Vnull;Vptr OwnershipReady;Vnull;
 Vptr OwnershipWaiting;Vnull;Vnull;Vnull;Vnull;Vnull;Vnull].
Definition DLcells:=V293_dly_cells 10%positive 11%positive 12%positive
 60%positive 30%positive 31%positive 0%Z 4(Int.repr 3)Int.zero(V293_byteval 0) 80 0 1.
Definition DLextra:=V293_dly_record_extra 60%positive 0%Z 4 Vnull.
Definition DLlow:=V293_record_layout OwnershipWaiting 6 rdy(Vptr(120%positive,Int.repr 7))0.
Definition DLall:=DLcells++(DLextra++DLlow).
Definition DLmem:=OwnershipCellsMemory DLall.
Definition DLheld:=V293_owned_record_cells DLcells **
 (V293_owned_record_cells DLextra **V293_owned_record_cells DLlow).
Lemma DLspatial : V293_wstate DLge DLle DLmem |=DLheld.
Proof.
 assert(H:V293_wstate DLge DLle DLmem|=V293_owned_record_cells DLall).
 { apply OwnershipCellsSpatial.
   - vm_compute;repeat split;intros;intuition congruence.
   - repeat constructor;vm_compute;reflexivity. }
 apply(proj1(OwnershipCellsAppend DLcells(DLextra++DLlow)_))in H.
 eapply astar_mono;[intros s Hs;exact Hs| |exact H].
 intros s Hs;apply(proj1(OwnershipCellsAppend DLextra DLlow s));exact Hs.
Qed.
Lemma DLenv : V293_dly_env 103%Z 106%Z 105%Z 400%Z 401%Z
 10%positive 11%positive 12%positive 30%positive 31%positive DLge DLle.
Proof. vm_compute;repeat split;reflexivity. Qed.
Lemma DLtable : V293_priority_table DLentries DLtasks.
Proof.
 split;[reflexivity| ]. intros t pr st msg Get.
 unfold DLtasks in Get;destruct(TcbMod.eq_dec t OwnershipWaiting)as[Same|Apart].
 - subst t;rewrite map_get_set in Get;inversion Get;subst.
   exists 6;repeat split;try reflexivity;lia.
 - rewrite map_get_set' in Get by congruence.
   destruct(TcbMod.eq_dec t OwnershipReady)as[Same|ApartR].
   + subst t;rewrite map_get_sig in Get;inversion Get;subst.
     exists 4;repeat split;try reflexivity;lia.
   + rewrite map_get_sig' in Get by congruence;discriminate.
Qed.
Lemma DLbitmap : V293_bitmap_tasks 80 0 DLtasks.
Proof.
 intros p P;split.
 - intro Ready;do 13(destruct p as [ | p];
    [try(solve[vm_compute in Ready;intuition discriminate]);
     first[exists OwnershipReady;exists Vnull;reflexivity|
      exists OwnershipWaiting;exists(Vptr(120%positive,Int.repr 7));reflexivity]| ]);lia.
 - intros(t&msg&Lookup);unfold DLtasks in Lookup.
   destruct(TcbMod.eq_dec t OwnershipWaiting)as[Same|Apart].
   + subst t;rewrite map_get_set in Lookup.
     apply(f_equal(fun x=>match x with Some(pr,_,_)=>pr|None=>Int.zero end))in Lookup.
     assert(p=6)by(apply(V293_priority_repr_injective p 6 P ltac:(lia));exact(eq_sym Lookup)).
     subst p;vm_compute;intuition.
   + rewrite map_get_set' in Lookup by congruence.
     destruct(TcbMod.eq_dec t OwnershipReady)as[Same|ApartR].
     * subst t;rewrite map_get_sig in Lookup.
       apply(f_equal(fun x=>match x with Some(pr,_,_)=>pr|None=>Int.zero end))in Lookup.
       assert(p=4)by(apply(V293_priority_repr_injective p 4 P ltac:(lia));exact(eq_sym Lookup)).
       subst p;vm_compute;intuition.
     * rewrite map_get_sig' in Lookup by congruence;discriminate.
Qed.
Lemma DLhigher_still_runs : ~V293_highest_ready DLtasks OwnershipWaiting.
Proof.
 eapply V293_dly_higher_ready_prevents_selection with(high:=OwnershipReady)(p:=4)(q:=6)
 (mh:=Vnull)(ml:=Vptr(120%positive,Int.repr 7));try lia;vm_compute;reflexivity.
Qed.
Theorem DLactual_block : exists Mf,
 cstepstar (fun _=>None)(curs(V293_dly_updates 103%Z 106%Z 105%Z 400%Z 401%Z),(kenil,kstop))
  (DLge,DLle,DLmem)(SKIP,(kenil,kstop))(DLge,DLle,Mf) /\
 load Tint32 Mf(60%positive,44%Z)=Some(Vint32(Int.repr 3)) /\
 load Tint8 Mf(30%positive,0%Z)=Some(V293_byteval 64) /\
 V293_task_record Mf OwnershipReady(Int.repr 4)(wait os_stat_time(Int.repr 3))Vnull /\
 V293_bitmap_tasks 64 0(set DLtasks OwnershipReady(Int.repr 4,wait os_stat_time(Int.repr 3),Vnull)) /\
 V293_highest_ready(set DLtasks OwnershipReady(Int.repr 4,wait os_stat_time(Int.repr 3),Vnull))OwnershipWaiting.
Proof.
 pose proof(V293_OSTimeDly_blocking_bridge 103%Z 106%Z 105%Z 400%Z 401%Z
 10%positive 11%positive 12%positive 60%positive 30%positive 31%positive 0%Z 4(Int.repr 3)
 (fun _=>None)kstop DLge DLle DLmem(fun _=>false)(false,nil,nil)emp(spec_done None)
 (V293_owned_record_cells DLlow)Int.zero(V293_byteval 0) 80 0 DLentries DLtasks Vnull
 DLenv ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(change(54<=4294967295)%Z;lia)ltac:(discriminate)
 DLtable DLbitmap eq_refl DLspatial)as Result.
 destruct Result as(Mf&Exec&Held&Record&Bitmap&Table&NotReady&NotHighest).
 exists Mf;split;[exact Exec| ]. split.
 - change(load Tint32(getmem(DLge,DLle,Mf,(fun _=>false),(false,nil,nil),emp,spec_done None))(60%positive,44%Z)=Some(Vint32(Int.repr 3))).
   eapply (V293_record_star_load_l (V293_owned_record_cells (V293_dly_cells 10%positive 11%positive 12%positive 60%positive 30%positive 31%positive 0%Z 4(Int.repr 3)(Int.repr 3)(V293_byteval 0)64 0 1)) _);[apply V293_owned_record_cells_load;cbn[V293_dly_cells In];tauto|exact Held].
 - split.
   + change(load Tint8(getmem(DLge,DLle,Mf,(fun _=>false),(false,nil,nil),emp,spec_done None))(30%positive,0%Z)=Some(V293_byteval 64)).
     eapply (V293_record_star_load_l (V293_owned_record_cells (V293_dly_cells 10%positive 11%positive 12%positive 60%positive 30%positive 31%positive 0%Z 4(Int.repr 3)(Int.repr 3)(V293_byteval 0)64 0 1)) _);[apply V293_owned_record_cells_load;cbn[V293_dly_cells In];tauto|exact Held].
   + split;[exact Record| ]. split;[exact Bitmap| ].
     destruct(V293_ready_selection_task 64 0 DLentries _ ltac:(lia)ltac:(lia)
      ltac:(exists 6;vm_compute;intuition)Bitmap Table)as(t&msg&Get&Entry&Highest).
     change(Vptr OwnershipWaiting=Vptr t)in Entry;inversion Entry;subst t;exact Highest.
Qed.

(* Only the final delay store varies. The complete clearing prefix is shared. *)
Definition DLbody (write:bool) :=
 sseq (V293_dly_before_delay 103%Z 106%Z 105%Z 400%Z)
 (sseq (if write then sassign(V293_dly_field 103%Z 13%Z)(evar 401%Z)
        else sskip None) (sskip None)).
Theorem DLwithout_delay : exists Mf,
 cstepstar (fun _=>None)(curs(DLbody false),(kenil,kstop))
  (DLge,DLle,DLmem)(SKIP,(kenil,kstop))(DLge,DLle,Mf) /\
 load Tint32 Mf(60%positive,44%Z)=Some(Vint32 Int.zero) /\
 load Tint8 Mf(30%positive,0%Z)=Some(V293_byteval 64).
Proof.
 destruct(V293_OSTimeDly_before_delay_execution 103%Z 106%Z 105%Z 400%Z 401%Z
 10%positive 11%positive 12%positive 60%positive 30%positive 31%positive 0%Z 4(Int.repr 3)
 (fun _=>None)DLge DLle DLmem(fun _=>false)(false,nil,nil)emp(spec_done None)
 (V293_owned_record_cells DLextra **V293_owned_record_cells DLlow)
 Int.zero(V293_byteval 0)80 0 DLenv ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)
 ltac:(change(54<=4294967295)%Z;lia) DLspatial)as(Mf&Prefix&Held&Delay).
 exists Mf;split.
 - unfold DLbody;eapply V293_rekey_sequence_execution;[exact Prefix| ].
   eapply V293_rekey_sequence_execution;[intro;constructor|constructor].
 - split;[exact Delay| ].
   change(load Tint8(getmem(DLge,DLle,Mf,(fun _=>false),(false,nil,nil),emp,spec_done None))(30%positive,0%Z)=Some(V293_byteval 64)).
   eapply (V293_record_star_load_l (V293_owned_record_cells (V293_dly_cells 10%positive 11%positive 12%positive 60%positive 30%positive 31%positive 0%Z 4(Int.repr 3)Int.zero(V293_byteval 0)64 0 1)) _);
    [apply V293_owned_record_cells_load;cbn[V293_dly_cells In];tauto|exact Held].
Qed.
Theorem DLchosen : forall write, exists Mf,
 cstepstar (fun _=>None)(curs(DLbody write),(kenil,kstop))
  (DLge,DLle,DLmem)(SKIP,(kenil,kstop))(DLge,DLle,Mf) /\
 load Tint32 Mf(60%positive,44%Z)=Some(Vint32(if write then Int.repr 3 else Int.zero)) /\
 load Tint8 Mf(30%positive,0%Z)=Some(V293_byteval 64).
Proof.
 intros [ | ];[ |exact DLwithout_delay].
 destruct DLactual_block as(Mf&Exec&Delay&Row&Rest).
 exists Mf;split;[exact Exec|split;assumption].
Qed.
