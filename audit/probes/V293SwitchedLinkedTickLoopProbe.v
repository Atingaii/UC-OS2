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
Require Import CertiOS.audit.probes.V293ReadyOwnedGlobalSwitchProbe.
Require Import CertiOS.audit.probes.V293ReadyTickLinkedEntryProbe.
Require Import CertiOS.certiucos.v293.proofs.V293SwitchedLinkedTickLoop.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyOwnedGlobalSwitch.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTickLinkedEntry.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.certiucos.v293.proofs.V293SwitchedTickPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickCountdown.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickTaskBridge.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.framework.proof.memory_prop.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchState.
Require Import CertiOS.certiucos.v293.code.V293OSTimeTick.
Local Open Scope nat_scope.

(* No second heap fixture: use LHinitial, including the original links,
   and carry the same ownership through the actual scheduler and switch. *)
Definition LGsched_rest:=DOrest **V293_owned_record_cells LHlinks.
Lemma LGsched_rest_good:GoodInvAsrt LGsched_rest.
Proof. unfold LGsched_rest,DOrest,LHlinks;vm_compute;repeat split;exact I. Qed.
Lemma LGentry:forall c enabled M,LHpost c enabled M ->
 (LHge,DCle,M,(fun _:hid=>false),(enabled,nil,nil),DEfinalabs(Int.repr 3),spec_done None)|=
 V293_ready_full 30%positive 31%positive 83%positive OwnershipReady **
 V293_owned_sched_frame 81%positive 82%positive 84%positive 85%positive
 70%positive 71%positive(V293_byteval 0)Vnull 4 c LGsched_rest.
Proof.
 intros c enabled M Held;unfold LHpost,LHstate,V293_dly_local_frame,LHresources,DRframe,LHlinks in Held.
 unfold V293_owned_sched_frame,LGsched_rest,DOrest,LHlinks;cbn[V293_owned_record_cells V293_dly_guard_cells app]in Held|-*.
 clear -Held;sep auto.
Qed.

Lemma LGlookup:forall c enabled M,LHpost c enabled M ->forall n,n<256 ->
 load Tint8 M(80%positive,Z.of_nat n)=Some(V293_byteval(V293_ready_lookup n)).
Proof.
 intros c enabled M Held n Range.
 set(S:=(LHge,DCle,M,(fun _:hid=>false),(enabled,(nil:list hid),(nil:list bool)),DEfinalabs(Int.repr 3),spec_done None)).
 assert(Lookup:S|=V293_read_bytes 80%positive 0%Z V293_ready_table **Atrue)
 by(unfold S;unfold LHpost,LHstate,V293_dly_local_frame,LHresources in Held;clear -Held;sep auto).
 change(load Tint8(getmem S)(80%positive,Z.of_nat n)=Some(V293_byteval(V293_ready_lookup n))).
 replace(Z.of_nat n)with(0+Z.of_nat n)%Z by lia.
 eapply V293_record_star_load_l;[apply V293_read_bytes_load|exact Lookup].
 - change(n<256);exact Range.
 - change(V293_ready_lookup n<256);pose proof(proj1(V293_ready_row_spec n Range));lia.
Qed.

Definition LGframe c bs:=DGframe c bs **V293_owned_record_cells LHlinks.
Definition LGsched_post c enabled bs M:=
 (LHge,V293_cpu_lenv 501%Z bs,M,(fun _:hid=>false),(false,nil,[enabled]),
 DEfinalabs(Int.repr 3),spec_done None)|=
 SWINVt(V293_ready_inv 30%positive 31%positive 83%positive)OwnershipReady **LGframe c bs.
Definition LGcut enabled bs M:=V293_local_global_at DAtasks(sig OwnershipWaiting DCle)(DWaux enabled)
 OwnershipReady(curs(sprim(switch 116%Z)),(kenil,DAcontinuation))
 ((LHge,V293_cpu_lenv 501%Z bs,M),(fun _:hid=>false),(false,nil,[enabled])).
Definition LGfinal enabled bs (M:mem):=
 (set DAtasks OwnershipReady(SKIP,(kenil,DAcontinuation)),
 (LHge,DAenvs bs,M,(fun _:hid=>false),DWaux enabled),OwnershipWaiting).
Definition LGrun c enabled bs M:=V293_global_steps DAprog DXclient(LHinitial c enabled)(LGcut enabled bs M).
Definition LGpost c bs M:=
 (LHge,DCle,M,(fun _:hid=>false),(true,nil,nil),DGabs,spec_done None)|=
 V293_ready_full 30%positive 31%positive 83%positive OwnershipWaiting **LGframe c bs.
Lemma LGframe_good:forall c bs,GoodInvAsrt(LGframe c bs).
Proof. intros;unfold LGframe,DGframe,DOcells,LHlinks;vm_compute;repeat split;exact I. Qed.

Lemma LGcut_exact:forall enabled bs M,LGcut enabled bs M=
 (DAtasks,(LHge,DAenvs bs,M,(fun _:hid=>false),DWaux enabled),OwnershipReady).
Proof.
 intros enabled bs M;unfold LGcut,V293_local_global_at,V293_global_at.
 assert(Task:set DAtasks OwnershipReady(curs(sprim(switch 116%Z)),(kenil,DAcontinuation))=DAtasks)
 by(apply TasksMod.get_set_same;reflexivity).
 assert(Aux:TaskLStMod.set(DWaux enabled)OwnershipReady(false,nil,[enabled])=DWaux enabled)
 by(apply TaskLStMod.get_set_same;reflexivity).
 change((set DAtasks OwnershipReady(curs(sprim(switch 116%Z)),(kenil,DAcontinuation)),
 (LHge,DAenvs bs,M,(fun _:hid=>false),TaskLStMod.set(DWaux enabled)OwnershipReady(false,nil,[enabled])),OwnershipReady)=
 (DAtasks,(LHge,DAenvs bs,M,(fun _:hid=>false),DWaux enabled),OwnershipReady)).
 rewrite Task,Aux;reflexivity.
Qed.

Theorem LGglobal_sched:forall c enabled,exists bs byblock My Mh Mcut,
 LGrun c enabled bs Mcut /\LGsched_post c enabled bs Mcut /\
 free Tint8 byblock My=Some Mh /\get Mh(byblock,0%Z)=None /\
 load(Tptr V293_tcb_type)Mcut(82%positive,0%Z)=Some(Vptr OwnershipWaiting).
Proof.
 intros c enabled;destruct(LHglobal_ready c enabled)as(Mb&Blocked&Step&Records&Table&Bitmap&Loads&Owned).
 destruct(V293_owned_sched_call 30%positive 31%positive 83%positive DAprogram(kseq sret kstop)
 LHge DCle Mb enabled nil(DEfinalabs(Int.repr 3))(spec_done None)OwnershipReady LGsched_rest
 112%Z 501%Z 110%Z 111%Z 113%Z 117%Z 115%Z 116%Z 118%Z 119%Z 114%Z 105%Z 106%Z 500%Z
 80%positive 81%positive 82%positive 84%positive 85%positive 70%positive 71%positive
 (V293_byteval 0)Vnull 4 c eq_refl eq_refl ltac:(cbn;intuition congruence)
 ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)
 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(lia)LGsched_rest_good
 (LGlookup c enabled Mb Owned)(LGentry c enabled Mb Owned))
 as(bs&byblock&Mi&My&Mh&Mt&Mf&tasks&lo&hi&entries&next&message&Fresh&FreshY&Map&Rel&Task&Scheduled&Prefix&Free&Removed&Counter&Final&Target&Count).
 destruct(DOselected _ _ _ _ _ _ Map Rel Task)as[Selected Next];subst next.
 rewrite Selected in Scheduled,Counter,Final,Count;cbn[Nat.eqb]in Scheduled,Counter,Final,Count.
 exists bs;exists byblock;exists My;exists Mh;exists Mf.
 split.
 - unfold LGrun,LGcut;unfold LHrun in Blocked.
   eapply V293_global_trans;[exact Blocked| ].
   pose proof(V293_local_function_extension DAprogram(pumerge DAprogram(fun _=>None))DXextends _ _ _ _ Scheduled)as Extended.
   eapply(V293_local_steps_global (fun _=>None)DAprogram(fun _=>None)(fun _=>None) _ _ _ _ Extended
   1200%Z DCbody emp kstop Tvoid(dcons 401%Z Tint32 dnil)(dcons 400%Z Tint8(dcons 402%Z Tint32 dnil))
   DAtasks(sig OwnershipWaiting DCle)(DWaux enabled)OwnershipReady((emp:env),DXcles,DXcm)eq_refl).
   exact I.
 - split.
   + unfold LGsched_post,LGframe,DGframe,DOcells,LGsched_rest,DOrest in *.
     cbn[V293_owned_record_cells]in Final|-*;clear -Final;sep auto.
   + split;[exact Free| ];split;[exact Removed|exact Target].
Qed.

Theorem LGglobal_switch:forall c enabled,exists bs byblock My Mh Mcut Mf,
 LGrun c enabled bs Mcut /\LGsched_post c enabled bs Mcut /\
 free Tint8 byblock My=Some Mh /\get Mh(byblock,0%Z)=None /\
 V293_global_steps DAprog DXclient(LHinitial c enabled)(LGfinal enabled bs Mf) /\
 lpstep DAprog DAtasks DXclient(LHge,DAenvs bs,Mcut,(fun _:hid=>false),DWaux enabled)OwnershipReady
 (set DAtasks OwnershipReady(SKIP,(kenil,DAcontinuation)))DXclient
 (LHge,DAenvs bs,Mf,(fun _:hid=>false),DWaux enabled)OwnershipWaiting /\
 store(Tptr V293_tcb_type)Mcut(10%positive,0%Z)(Vptr OwnershipWaiting)=Some Mf /\
 LGpost c bs Mf /\load(Tptr V293_tcb_type)Mf(10%positive,0%Z)=Some(Vptr OwnershipWaiting) /\
 get DGabs curtid=Some(oscurt OwnershipWaiting) /\
 (forall b i,b<>10%positive \/(i<0)%Z \/(4<=i)%Z ->get Mf(b,i)=get Mcut(b,i)).
Proof.
 intros c enabled;destruct(LGglobal_sched c enabled)as(bs&byblock&My&Mh&Mcut&Run&Owned&Free&Dead&Target).
 destruct(V293_owned_global_switch 30%positive 31%positive 83%positive
 (fun _=>None)DAprogram(fun _=>None)(fun _=>None)DAtasks DXclient DAcontinuation
 OwnershipReady OwnershipWaiting 116%Z 82%positive 10%positive LHge
 (V293_cpu_lenv 501%Z bs)DCle(DAenvs bs)Mcut(fun _:hid=>false)
 false true nil[enabled]nil(DWaux enabled)(DEfinalabs(Int.repr 3))(spec_done None)(LGframe c bs)V293_tcb_type
 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl Target eq_refl(LGframe_good c bs)Owned)
 as(Mf&Switch&Store&After&Load&Cur&Env&Aux&Outside).
 exists bs;exists byblock;exists My;exists Mh;exists Mcut;exists Mf.
 split;[exact Run| ];split;[exact Owned| ];split;[exact Free| ];split;[exact Dead| ];split.
 - unfold LGrun in Run;rewrite LGcut_exact in Run;eapply V293_global_trans;[exact Run| ].
   unfold V293_global_steps,LGfinal;eapply rt1n_trans with(y:=
   (set DAtasks OwnershipReady(SKIP,(kenil,DAcontinuation)),
   (LHge,DAenvs bs,Mf,(fun _:hid=>false),DWaux enabled),OwnershipWaiting));
   [exact Switch|apply rt1n_refl].
 - split;[exact Switch| ];split;[exact Store| ];split;[exact After| ];
   split;[exact Load| ];split;[exact Cur|exact Outside].
Qed.

Definition LGrest c bs:=
 V293_owned_record_cell((91%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady) **DGframe c bs.
Definition LGowned c bs b aux O scan M:=
 (LHge,LHle b,M,(fun _:hid=>false),aux,O,spec_done None)|=
 V293_ready_full 30%positive 31%positive 83%positive OwnershipWaiting **
 (V293_owned_record_cell((b,0%Z),Tptr V293_tcb_type,Vptr scan) **
 (V293_owned_record_cell((60%positive,20%Z),Tcom_ptr 410%Z,Vptr OwnershipWaiting) **LGrest c bs)).
Definition LGprepared c bs b M:=LGowned c bs b(true,nil,nil)DGabs OwnershipReady M.
Definition LGabs2:=set DGabs abstcblsid(abstcblist LHtasks2).
Definition LGposttick c bs b M:=LGowned c bs b(true,nil,nil)LGabs2 OwnershipWaiting M.
Lemma LGrest_good:forall c bs,GoodInvAsrt(LGrest c bs).
Proof. intros;split;[split;exact I|apply DGframe_good]. Qed.

(* This allocation and local source head execution start from the same
   actual switched heap, but do not assert a legal global ISR transition. *)
Lemma LGprepare:forall c bs M,LGpost c bs M ->exists b Mp,
 LHsetup b M Mp /\LGprepared c bs b Mp.
Proof.
 intros c bs M Held;destruct(fresh_exist M)as[b Fresh].
 assert(Frame:(LHge,LHle b,M,(fun _:hid=>false),(true,nil,nil),DGabs,spec_done None)|=
 V293_owned_record_cell((91%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady) **
 (V293_ready_full 30%positive 31%positive 83%positive OwnershipWaiting **
 (V293_owned_record_cell((60%positive,20%Z),Tcom_ptr 410%Z,Vptr OwnershipWaiting) **DGframe c bs))).
 { assert(Same:(LHge,DCle,M,(fun _:hid=>false),(true,nil,nil),DGabs,spec_done None)|=
   V293_owned_record_cell((91%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady) **
   (V293_ready_full 30%positive 31%positive 83%positive OwnershipWaiting **
   (V293_owned_record_cell((60%positive,20%Z),Tcom_ptr 410%Z,Vptr OwnershipWaiting) **DGframe c bs))).
   { unfold LGpost,LGframe,LHlinks in Held;cbn[V293_owned_record_cells]in Held.
     clear -Held;sep auto. }
   eapply good_inv_prop;[ |exact Same].
   split;[split;exact I|split;[apply V293_owned_ready_good|split;[split;exact I|apply DGframe_good]]]. }
 assert(Unbound:~indom(emp:env)700%Z).
 { intros[v Bad];rewrite map_emp_get in Bad;discriminate. }
 destruct(V293_tick_scan_allocation DAprogram kstop dnil LHge(emp:env)M
 (fun _:hid=>false)(true,nil,nil)DGabs(spec_done None)700%Z b _ Fresh Unbound Frame)
 as(Allocate&Execute&Raw&Undef).
 destruct(V293_ready_tick_head_execution DAprogram kstop LHge(LHle b)
 (allocb M b 0%Z(typelen(Tptr V293_tcb_type)))(fun _:hid=>false)(true,nil,nil)
 DGabs(spec_done None)700%Z 703%Z b 91%positive Vundef OwnershipReady _
 eq_refl eq_refl eq_refl Raw)as(Mp&Store&Head&Owned&Read&Outside).
 exists b;exists Mp;split.
 - split;[exact Fresh| ];split;[exact Allocate| ];split;[exact Execute| ];
   split;[exact Store|exact Head].
 - unfold LGprepared,LGowned,LGrest;clear -Owned;sep auto.
Qed.
Definition LGloop:=swhile(V293_tick_guard 700%Z)(V293_tick_iteration 700%Z 701%Z 702%Z).
Definition LGexecution b M Mf:=
 V293_local_steps DAprogram(curs LGloop,(kenil,kstop))
 ((LHge,LHle b,M),(fun _:hid=>false),(true,nil,nil))
 (curs LGloop,(kenil,kstop))((LHge,LHle b,Mf),(fun _:hid=>false),(true,nil,nil)).
Theorem LGiteration:forall c bs b M,LGprepared c bs b M ->exists Md Mf,
 store Tint32 M(60%positive,44%Z)(Vint32(Int.repr 2))=Some Md /\
 store(Tptr V293_tcb_type)Md(b,0%Z)(Vptr OwnershipWaiting)=Some Mf /\
 LGexecution b M Mf /\
 spec_step V293_scheduler(spec_prim nil(V293_tick_wait_step OwnershipReady))DGabs(END None)LGabs2 /\
 LGposttick c bs b Mf /\
 load Tint32 Mf(60%positive,44%Z)=Some(Vint32(Int.repr 2)) /\
 load(Tptr V293_tcb_type)Mf(b,0%Z)=Some(Vptr OwnershipWaiting) /\
 (forall x i,(x<>60%positive \/(i<44)%Z \/(48<=i)%Z) ->
 (x<>b \/(i<0)%Z \/(4<=i)%Z) ->get Mf(x,i)=get M(x,i)).
Proof.
 intros c bs b M Held.
 exact(V293_ready_countdown_while_step 30%positive 31%positive 83%positive OwnershipWaiting
 (DEblocked(Int.repr 3))60%positive 0 4 3 Vnull(LGrest c bs)DAprogram kstop
 LHge(LHle b)M(fun _:hid=>false)true nil nil DGabs(spec_done None)V293_scheduler
 700%Z 701%Z 702%Z b OwnershipWaiting eq_refl ltac:(lia)ltac:(change(50<=4294967295)%Z;lia)
 ltac:(lia)ltac:(lia)ltac:(change(2<=3<=4294967295)%Z;lia)eq_refl eq_refl(LGrest_good c bs)Held).
Qed.

Definition LGmutant_loop:=swhile(V293_tick_guard 700%Z)(LHmutant_iteration 700%Z 701%Z 702%Z).
Definition LGmutant_execution b M Mf:=
 V293_local_steps DAprogram(curs LGmutant_loop,(kenil,kstop))
 ((LHge,LHle b,M),(fun _:hid=>false),(true,nil,nil))
 (curs LGmutant_loop,(kenil,kstop))((LHge,LHle b,Mf),(fun _:hid=>false),(true,nil,nil)).
Theorem LGmutant_late_gate:forall c bs b M,LGprepared c bs b M ->exists Mf,
 LGmutant_execution b M Mf /\
 spec_step V293_scheduler(spec_prim nil(V293_tick_wait_step OwnershipReady))
 DGabs(END None)LGabs2 /\
 LGowned c bs b(true,nil,nil)LGabs2 OwnershipReady Mf /\
 load Tint32 Mf(60%positive,44%Z)=Some(Vint32(Int.repr 2)) /\
 load(Tptr V293_tcb_type)Mf(b,0%Z)=Some(Vptr OwnershipReady) /\
 ~LGposttick c bs b Mf.
Proof.
 intros c bs b M Held.
 set(R:=V293_owned_record_cell((60%positive,20%Z),Tcom_ptr 410%Z,Vptr OwnershipWaiting) **LGrest c bs).
 assert(Good:GoodInvAsrt R)by(split;[split;exact I|apply LGrest_good]).
 assert(Disabled:LGowned c bs b(false,nil,[true])DGabs OwnershipReady M).
 { eapply good_inv_prop;[split;[apply V293_owned_ready_good|split;[split;exact I|exact Good]]|exact Held]. }
 destruct(V293_ready_countdown_delay_execution 30%positive 31%positive 83%positive OwnershipWaiting
 (DEblocked(Int.repr 3))60%positive 0(Int.repr 4)3 Vnull R DAprogram
 (kseq(sseq(sskip None)(sprim excrit))(kseq LGmutant_loop kstop))LHge(LHle b)M(fun _:hid=>false)(false,nil,[true])
 DGabs(spec_done None)V293_scheduler 700%Z 701%Z 702%Z b
 eq_refl ltac:(lia)ltac:(change(44<=4294967295)%Z;lia)
 ltac:(change(2<=3<=4294967295)%Z;lia)eq_refl eq_refl Disabled)
 as(Mf&Store&DelayExecution&Abstract&After&Delay&Outside).
 assert(Returned:LGowned c bs b(true,nil,nil)LGabs2 OwnershipReady Mf).
 { eapply good_inv_prop;[split;[apply V293_owned_ready_good|split;[split;exact I|exact Good]]|exact After]. }
 assert(Pointer:load(Tptr V293_tcb_type)Mf(b,0%Z)=Some(Vptr OwnershipReady)).
 { assert(Cell:(LHge,LHle b,Mf,(fun _:hid=>false),(true,nil,nil),LGabs2,spec_done None)|=
 V293_owned_record_cell((b,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady) **Atrue)
 by(unfold LGowned in Returned;clear -Returned;sep auto).
 exact(V293_record_star_load_l _ _ _ _ _ (V293_owned_record_cell_load _ _ _) _ Cell). }
 exists Mf;split.
 - pose proof(V293_ready_tick_guard 30%positive 31%positive 83%positive OwnershipWaiting
   (DEblocked(Int.repr 3))60%positive 0 4 _ Vnull R LHge(LHle b)M(fun _:hid=>false)
   (true,nil,nil)DGabs(spec_done None)700%Z b eq_refl ltac:(lia)
   ltac:(change(50<=4294967295)%Z;lia)ltac:(lia)eq_refl eq_refl Held)as Guard.
   unfold LGmutant_execution,LGmutant_loop.
   eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply swhile_step]| ].
   eapply V293_local_trans.
   { apply V293_csteps_local;apply V293_expr_steps;apply evalval_imply_estepstar;exact Guard. }
   eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply svwhilet_step;reflexivity]| ].
   unfold LHmutant_iteration.
   eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sseq_step]| ].
   eapply V293_local_cons;[apply encrit_step;reflexivity| ].
   eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sskip_step]| ].
   eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sseq_step]| ].
   eapply V293_local_trans;[apply V293_csteps_local;exact DelayExecution| ].
   eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sskip_step]| ].
   eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sseq_step]| ].
   eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sskip_step]| ].
   eapply V293_local_cons;[apply excrit_step;reflexivity| ].
   eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sskip_step]|apply V293_local_refl].
 - split;[exact Abstract| ];split;[exact Returned| ];split;[exact Delay| ];split;[exact Pointer| ].
   intro Expected.
   assert(Cell:(LHge,LHle b,Mf,(fun _:hid=>false),(true,nil,nil),LGabs2,spec_done None)|=
   V293_owned_record_cell((b,0%Z),Tptr V293_tcb_type,Vptr OwnershipWaiting) **Atrue)
   by(unfold LGposttick,LGowned in Expected;clear -Expected;sep auto).
   pose proof(V293_record_star_load_l _ _ _ _ _ (V293_owned_record_cell_load _ _ _) _ Cell)as Next.
   change(load(Tptr V293_tcb_type)Mf(b,0%Z)=Some(Vptr OwnershipWaiting))in Next.
   rewrite Pointer in Next;discriminate.
Qed.


Lemma LGcurrent:forall t R le M ir aux O,
 (LHge,le,M,ir,aux,O,spec_done None)|=
 V293_ready_full 30%positive 31%positive 83%positive t **R ->
 load(Tptr V293_tcb_type)M(10%positive,0%Z)=Some(Vptr t).
Proof.
 intros t R le M ir aux O Held;unfold V293_ready_full in Held;sep normal in Held;sep destruct Held.
 assert(Named:(LHge,le,M,ir,aux,O,spec_done None)|=(GV OSTCBCur@(Tptr x2)|->Vptr t) **Atrue)by(sep auto).
 apply sat_split in Named;destruct Named as(ma&mb&oa&ob&JM&JO&Cell&Frame).
 destruct(V293_dispatch_named_cell_parts _ _ _ _ _ _ _ _ _ _ Cell)as(b&GE&HC&Empty).
 change(Some(10%positive,Tptr V293_tcb_type)=Some(b,Tptr x2))in GE.
 inversion GE;subst b x2.
 eapply load_mem_mono;[eapply mapstoval_load;[reflexivity|exact HC]|exists mb;exact JM].
Qed.

Theorem LGobserved:forall c bs b scan M,LGowned c bs b(true,nil,nil)LGabs2 scan M ->
 load(Tptr V293_tcb_type)M(10%positive,0%Z)=Some(Vptr OwnershipWaiting) /\
 load Tint8 M(84%positive,0%Z)=Some(V293_byteval 4) /\
 load Tint32 M(85%positive,0%Z)=Some(Vint32(Int.add c Int.one)) /\
 load Tint32 M(90%positive,0%Z)=Some(Vint32(Int.repr 99)).
Proof.
 intros c bs b scan M Held.
 assert(Cells:(LHge,LHle b,M,(fun _:hid=>false),(true,nil,nil),LGabs2,spec_done None)|=
 V293_owned_record_cells(DOcells c) **Atrue)
 by(unfold LGowned,LGrest,DGframe in Held;clear -Held;sep auto).
 unfold LGowned in Held.
 split;[eapply LGcurrent;exact Held| ].
 split;[ |split];eapply DScells_load;[ |exact Cells| |exact Cells| |exact Cells];
 cbn[DOcells In];tauto.
Qed.

(* The only input parameters are the initial counter and saved IE.
   Both fragments use one actual switched heap and one allocated scanner. *)
Theorem LGsame_input_ablation:forall c enabled,exists bs byblock My Mh Mcut M b Mp Md Mf,exists Mmut,
 LGrun c enabled bs Mcut /\LGsched_post c enabled bs Mcut /\
 free Tint8 byblock My=Some Mh /\get Mh(byblock,0%Z)=None /\
 V293_global_steps DAprog DXclient(LHinitial c enabled)(LGfinal enabled bs M) /\
 store(Tptr V293_tcb_type)Mcut(10%positive,0%Z)(Vptr OwnershipWaiting)=Some M /\
 LGpost c bs M /\LHsetup b M Mp /\LGprepared c bs b Mp /\
 LGexecution b Mp Mf /\LGposttick c bs b Mf /\
 LGmutant_execution b Mp Mmut /\LGowned c bs b(true,nil,nil)LGabs2 OwnershipReady Mmut /\
 spec_step V293_scheduler(spec_prim nil(V293_tick_wait_step OwnershipReady))DGabs(END None)LGabs2 /\
 store Tint32 Mp(60%positive,44%Z)(Vint32(Int.repr 2))=Some Md /\
 load Tint32 Mf(60%positive,44%Z)=Some(Vint32(Int.repr 2)) /\
 load Tint32 Mmut(60%positive,44%Z)=Some(Vint32(Int.repr 2)) /\
 load(Tptr V293_tcb_type)Mf(b,0%Z)=Some(Vptr OwnershipWaiting) /\
 load(Tptr V293_tcb_type)Mmut(b,0%Z)=Some(Vptr OwnershipReady) /\
 load(Tptr V293_tcb_type)Mf(10%positive,0%Z)=Some(Vptr OwnershipWaiting) /\
 load(Tptr V293_tcb_type)Mmut(10%positive,0%Z)=Some(Vptr OwnershipWaiting) /\
 load Tint8 Mf(84%positive,0%Z)=Some(V293_byteval 4) /\
 load Tint8 Mmut(84%positive,0%Z)=Some(V293_byteval 4) /\
 ~LGposttick c bs b Mmut.
Proof.
 intros c enabled;destruct(LGglobal_switch c enabled)
 as(bs&byblock&My&Mh&Mcut&M&Run&Pre&Free&Dead&Trace&Switch&Commit&Post&Current&Cur&Outside).
 destruct(LGprepare c bs M Post)as(b&Mp&Setup&Prepared).
 destruct(LGiteration c bs b Mp Prepared)as(Md&Mf&Dec&Next&Execute&Abstract&Final&Delay&Read&Out).
 destruct(LGmutant_late_gate c bs b Mp Prepared)as(Mmut&Mutant&AbsMut&Preserved&DelayMut&PointerMut&Reject).
 destruct(LGobserved c bs b OwnershipWaiting Mf Final)as(CurF&CacheF&CounterF&CanaryF).
 destruct(LGobserved c bs b OwnershipReady Mmut Preserved)as(CurM&CacheM&CounterM&CanaryM).
 exists bs;exists byblock;exists My;exists Mh;exists Mcut;exists M;exists b;exists Mp;exists Md;exists Mf;exists Mmut.
 split;[exact Run| ];split;[exact Pre| ];split;[exact Free| ];split;[exact Dead| ];
 split;[exact Trace| ];split;[exact Commit| ];split;[exact Post| ];split;[exact Setup| ];
 split;[exact Prepared| ];split;[exact Execute| ];split;[exact Final| ];split;[exact Mutant| ];
 split;[exact Preserved| ];split;[exact Abstract| ];split;[exact Dec| ];split;[exact Delay| ];
 split;[exact DelayMut| ];split;[exact Read| ];split;[exact PointerMut| ];split;[exact CurF| ];
 split;[exact CurM| ];split;[exact CacheF| ];split;assumption.
Qed.
