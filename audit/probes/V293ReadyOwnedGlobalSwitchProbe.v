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

Require Import CertiOS.audit.probes.V293ReadyOwnedSchedCallProbe.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyOwnedGlobalSwitch.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchState.
Require Import CertiOS.framework.proof.memory_prop.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.rulesoundlib.

Definition DGframe c bs:=V293_owned_record_cells(DOcells c) **
 (Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **
 (Amapsto(13%positive,0%Z)Tint32 true(Vint32 Int.zero) **
 V293_read_bytes 80%positive 0%Z V293_ready_table)).
Definition DGabs:=set(DEfinalabs(Int.repr 3))curtid(oscurt OwnershipWaiting).
Definition DGpost c bs M:=
 (DWge,DCle,M,(fun _:hid=>false),(true,nil,nil),DGabs,spec_done None)|=
 V293_ready_full 30%positive 31%positive 83%positive OwnershipWaiting **DGframe c bs.

Lemma DGframe_good:forall c bs,GoodInvAsrt(DGframe c bs).
Proof. intros;unfold DGframe,DOcells;vm_compute;repeat split;exact I. Qed.

Theorem DGglobal_switch:forall c enabled,exists bs byblock My Mh Mcut Mf,
 DXrun c enabled bs Mcut /\DOpost c enabled bs Mcut /\
 free Tint8 byblock My=Some Mh /\get Mh(byblock,0%Z)=None /\
 V293_global_steps DAprog DXclient(DXinitial c enabled)(DXfinal enabled bs Mf) /\
 lpstep DAprog DAtasks DXclient(DWge,DAenvs bs,Mcut,(fun _:hid=>false),DWaux enabled)OwnershipReady
 (set DAtasks OwnershipReady(SKIP,(kenil,DAcontinuation)))DXclient
 (DWge,DAenvs bs,Mf,(fun _:hid=>false),DWaux enabled)OwnershipWaiting /\
 store(Tptr V293_tcb_type)Mcut(10%positive,0%Z)(Vptr OwnershipWaiting)=Some Mf /\
 DGpost c bs Mf /\load(Tptr V293_tcb_type)Mf(10%positive,0%Z)=Some(Vptr OwnershipWaiting) /\
 get DGabs curtid=Some(oscurt OwnershipWaiting) /\
 get(DAenvs bs)OwnershipWaiting=Some DCle /\get(DWaux enabled)OwnershipWaiting=Some(true,nil,nil) /\
 (forall b i,b<>10%positive \/(i<0)%Z \/(4<=i)%Z ->get Mf(b,i)=get Mcut(b,i)).
Proof.
 intros c enabled;destruct(DOglobal_sched c enabled)
 as(bs&byblock&Mb&Mi&My&Mh&Mt&Mcut&B&PO&Run&F&FY&Free&Dead&Call&Counter&Owned&Target&Count).
 destruct(V293_owned_global_switch 30%positive 31%positive 83%positive
 (fun _=>None)DAprogram(fun _=>None)(fun _=>None)DAtasks DXclient DAcontinuation
 OwnershipReady OwnershipWaiting 116%Z 82%positive 10%positive DWge
 (V293_cpu_lenv 501%Z bs)DCle(DAenvs bs)Mcut(fun _:hid=>false)
 false true nil[enabled]nil(DWaux enabled)(DEfinalabs(Int.repr 3))(spec_done None)(DGframe c bs)V293_tcb_type
 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl Target eq_refl(DGframe_good c bs)Owned)
 as(Mf&Switch&Store&After&Load&Cur&Env&Aux&Outside).
 exists bs;exists byblock;exists My;exists Mh;exists Mcut;exists Mf.
 split;[exact Run| ];split;[exact Owned| ];split;[exact Free| ];split;[exact Dead| ];split.
 - unfold DXrun in Run;rewrite DXcut_exact in Run.
   eapply V293_global_trans;[exact Run| ].
   unfold V293_global_steps,DXfinal;eapply rt1n_trans with(y:=
   (set DAtasks OwnershipReady(SKIP,(kenil,DAcontinuation)),
   (DWge,DAenvs bs,Mf,(fun _:hid=>false),DWaux enabled),OwnershipWaiting));
   [exact Switch|apply rt1n_refl].
 - split;[exact Switch| ];split;[exact Store| ];split;[exact After| ];
   split;[exact Load| ];split;[exact Cur| ];split;[exact Env| ];split;assumption.
Qed.

Lemma DGobserved:forall c bs M,DGpost c bs M ->
 (forall a tp v,In(a,tp,v)(DOcells c) ->load tp M a=Some v) /\
 load Tint32 M(bs,0%Z)=Some(Vint32 Int.zero) /\V293_bytes_writable M bs 0%Z 4 /\
 load Tint32 M(13%positive,0%Z)=Some(Vint32 Int.zero) /\V293_bytes_writable M 13%positive 0%Z 4.
Proof.
 intros c bs M Held.
 set(S:=(DWge,DCle,M,(fun _:hid=>false),(true,(nil:list hid),(nil:list bool)),DGabs,spec_done None)).
 assert(Cells:S|=V293_owned_record_cells(DOcells c) **Atrue)
 by(unfold S;unfold DGpost,DGframe in Held;clear -Held;sep auto).
 assert(CPU:S|=Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **Atrue)
 by(unfold S;unfold DGpost,DGframe in Held;clear -Held;sep auto).
 assert(OldCPU:S|=Amapsto(13%positive,0%Z)Tint32 true(Vint32 Int.zero) **Atrue)
 by(unfold S;unfold DGpost,DGframe in Held;clear -Held;sep auto).
 split.
 - intros a tp v Member;eapply DScells_load;[exact Member|exact Cells].
 - split.
   + change(load Tint32(getmem S)(bs,0%Z)=Some(Vint32 Int.zero));apply DCraw_load;[reflexivity|exact CPU].
   + split.
     * eapply(V293_tick_raw_owned_writable bs Tint32(Vint32 Int.zero)Atrue
       DWge DCle M(fun _:hid=>false)(true,nil,nil)DGabs(spec_done None));exact CPU.
     * split.
       -- change(load Tint32(getmem S)(13%positive,0%Z)=Some(Vint32 Int.zero));apply DCraw_load;[reflexivity|exact OldCPU].
       -- eapply(V293_tick_raw_owned_writable 13%positive Tint32(Vint32 Int.zero)Atrue
          DWge DCle M(fun _:hid=>false)(true,nil,nil)DGabs(spec_done None));exact OldCPU.
Qed.

Theorem DGmatched_high:forall c enabled,exists bs M,
 V293_global_steps DAprog DXclient(DXinitial c enabled)(DXfinal enabled bs M) /\DGpost c bs M /\
 hpstep DWhighprog DAhightasks DXclient(DEfinalabs(Int.repr 3))
 (set DAhightasks OwnershipReady DAhighafter)DXclient DGabs /\
 get(set DAtasks OwnershipReady(SKIP,(kenil,DAcontinuation)))OwnershipReady=Some(SKIP,(kenil,DAcontinuation)) /\
 get(set DAtasks OwnershipReady(SKIP,(kenil,DAcontinuation)))OwnershipWaiting=Some DWready.
Proof.
 intros c enabled;destruct(DGglobal_switch c enabled)
 as(bs&byblock&My&Mh&Mcut&Mf&Run&Owned&Free&Dead&Trace&Switch&Store&After&Rest).
 exists bs;exists Mf;split;[exact Trace| ];split;[exact After| ];split;[exact(proj1 DXhigh_switch)| ];
 split;reflexivity.
Qed.

Theorem DGboth_IE:forall c,
 (exists bs M,V293_global_steps DAprog DXclient(DXinitial c false)(DXfinal false bs M) /\DGpost c bs M) /\
 (exists bs M,V293_global_steps DAprog DXclient(DXinitial c true)(DXfinal true bs M) /\DGpost c bs M).
Proof.
 intro c;split;
 [destruct(DGglobal_switch c false)as(bs&y&My&Mh&Mc&M&Run&Pre&Free&Dead&Trace&Switch&Store&After&Rest)|
 destruct(DGglobal_switch c true)as(bs&y&My&Mh&Mc&M&Run&Pre&Free&Dead&Trace&Switch&Store&After&Rest)];
 exists bs;exists M;split;assumption.
Qed.

Theorem DGwrap:forall enabled,exists bs M,
 V293_global_steps DAprog DXclient(DXinitial(Int.repr Int.max_unsigned)enabled)(DXfinal enabled bs M) /\
 DGpost(Int.repr Int.max_unsigned)bs M /\load Tint32 M(85%positive,0%Z)=Some(Vint32 Int.zero).
Proof.
 intro enabled;destruct(DGglobal_switch(Int.repr Int.max_unsigned)enabled)
 as(bs&y&My&Mh&Mc&M&Run&Pre&Free&Dead&Trace&Switch&Store&After&Rest).
 destruct(DGobserved _ _ _ After)as(Cells&CPU&W&OldCPU&OldW).
 exists bs;exists M;split;[exact Trace| ];split;[exact After| ].
 rewrite <-DWcounter_wrap;apply Cells;cbn[DOcells In];tauto.
Qed.

(* The pointer observation follows ownership, independently of abstract curtid. *)
Lemma DGcurrent:forall t R le M ir aux O,
 (DWge,le,M,ir,aux,O,spec_done None)|=
 V293_ready_full 30%positive 31%positive 83%positive t **R ->
 load(Tptr V293_tcb_type)M(10%positive,0%Z)=Some(Vptr t).
Proof.
 intros t R le M ir aux O Held;unfold V293_ready_full in Held;sep normal in Held;sep destruct Held.
 assert(Named:(DWge,le,M,ir,aux,O,spec_done None)|=(GV OSTCBCur@(Tptr x2)|->Vptr t) **Atrue)by(sep auto).
 apply sat_split in Named;destruct Named as(ma&mb&oa&ob&JM&JO&Cell&Frame).
 destruct(V293_dispatch_named_cell_parts _ _ _ _ _ _ _ _ _ _ Cell)as(b&GE&HC&Empty).
 change(Some(10%positive,Tptr V293_tcb_type)=Some(b,Tptr x2))in GE.
 inversion GE;subst b x2.
 eapply load_mem_mono;[eapply mapstoval_load;[reflexivity|exact HC]|exists mb;exact JM].
Qed.

Theorem DGpointer_commit_ablation:forall c enabled,exists bs byblock My Mh Mcut Mf,
 DXrun c enabled bs Mcut /\DOpost c enabled bs Mcut /\
 free Tint8 byblock My=Some Mh /\get Mh(byblock,0%Z)=None /\
 V293_global_steps DAprog DXclient(DXinitial c enabled)(DXfinal enabled bs Mf) /\
 store(Tptr V293_tcb_type)Mcut(10%positive,0%Z)(Vptr OwnershipWaiting)=Some Mf /\
 DGpost c bs Mf /\
 load(Tptr V293_tcb_type)Mcut(10%positive,0%Z)=Some(Vptr OwnershipReady) /\
 load(Tptr V293_tcb_type)Mf(10%positive,0%Z)=Some(Vptr OwnershipWaiting) /\
 ~DGpost c bs Mcut /\
 load Tint32 Mcut(85%positive,0%Z)=Some(Vint32(Int.add c Int.one)) /\
 load Tint32 Mf(85%positive,0%Z)=Some(Vint32(Int.add c Int.one)) /\
 load Tint32 Mcut(90%positive,0%Z)=Some(Vint32(Int.repr 99)) /\
 load Tint32 Mf(90%positive,0%Z)=Some(Vint32(Int.repr 99)) /\
 V293_bytes_writable Mcut bs 0%Z 4 /\V293_bytes_writable Mf bs 0%Z 4.
Proof.
 intros c enabled;destruct(DGglobal_switch c enabled)
 as(bs&byblock&My&Mh&Mcut&Mf&Run&Pre&Free&Dead&Trace&Switch&Store&After&Current&Rest).
 assert(Before:load(Tptr V293_tcb_type)Mcut(10%positive,0%Z)=Some(Vptr OwnershipReady)).
 { unfold DOpost in Pre.
   pose proof(V293_owned_switch_active_view 30%positive 31%positive 83%positive
   OwnershipReady(DGframe c bs)DWge(V293_cpu_lenv 501%Z bs)Mcut(fun _:hid=>false)
   false nil[enabled](DEfinalabs(Int.repr 3))(spec_done None)(DGframe_good c bs)Pre
   DCle true nil)as Full;eapply DGcurrent;exact Full. }
 assert(Reject:~DGpost c bs Mcut).
 { intro Wrong;unfold DGpost in Wrong;pose proof(DGcurrent _ _ _ _ _ _ _ Wrong)as Load;rewrite Before in Load;discriminate. }
 destruct(DOobserved c enabled bs Mcut Pre)as(OldCells&OldCPU&OldW&OldSaved&OldSavedW).
 destruct(DGobserved c bs Mf After)as(Cells&CPU&W&Saved&SavedW).
 exists bs;exists byblock;exists My;exists Mh;exists Mcut;exists Mf.
 split;[exact Run| ];split;[exact Pre| ];split;[exact Free| ];split;[exact Dead| ];
 split;[exact Trace| ];split;[exact Store| ];split;[exact After| ];
 split;[exact Before| ];split;[exact Current| ];split;[exact Reject| ];split.
 - apply OldCells;cbn[DOcells In];tauto.
 - split;[apply Cells;cbn[DOcells In];tauto| ];split.
   + apply OldCells;cbn[DOcells In];tauto.
   + split;[apply Cells;cbn[DOcells In];tauto| ];split;assumption.
Qed.

Theorem DGdistinct_heaps:forall c enabled,exists bs M,
 V293_global_steps DAprog DXclient(DXinitial c enabled)(DXfinal enabled bs M) /\DGpost c bs M /\
 load Tint32 M(12%positive,0%Z)=Some(Vint32(Int.repr 3)) /\
 load Tint32 DXcm(12%positive,0%Z)=Some(Vint32(Int.repr 99)).
Proof.
 intros c enabled;destruct(DGglobal_switch c enabled)
 as(bs&y&My&Mh&Mc&M&Run&Pre&Free&Dead&Trace&Switch&Store&After&Rest).
 destruct(DGobserved c bs M After)as(Cells&CPU&W&Saved&SavedW).
 exists bs;exists M;split;[exact Trace| ];split;[exact After| ];split.
 - apply Cells;cbn[DOcells In];tauto.
 - exact(proj1 DXclient_alias).
Qed.

(* An enabled selected task cannot inherit the old disabled switch flags. *)
Theorem DGactive_not_disabled:forall M O,
 ~((DWge,DCle,M,(fun _:hid=>false),(true,nil,nil),O,spec_done None)|=
 SWINVt(V293_ready_inv 30%positive 31%positive 83%positive)OwnershipWaiting **Atrue).
Proof.
 intros M O Wrong.
 assert(Flag:(DWge,DCle,M,(fun _:hid=>false),(true,nil,nil),O,spec_done None)|=Aie false **Atrue)
 by(unfold SWINVt,SWINV in Wrong;sep auto).
 apply astar_l_aie_elim in Flag;destruct Flag as[Eq Rest];discriminate.
Qed.
