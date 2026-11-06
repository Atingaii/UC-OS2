(* Independent waiting-current resources and exact OSIntCtxSw call boundary. *)
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293SharedStateWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrent.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.framework.proof.memory_prop.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.audit.probes.V293TaskRecordInvariantProbe.
Import ListNotations.
Local Open Scope nat_scope.

Require Import CertiOS.certiucos.v293.proofs.V293ReadyTargetHandoff.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchState.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.audit.probes.V293ReadyTaskInvariantProbe.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.certiucos.v293.code.V293OSSchedDispatch.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Local Open Scope nat_scope.
Require Import CertiOS.audit.probes.V293ReadyTargetHandoffProbe.
Require Import CertiOS.certiucos.v293.proofs.V293ReadySchedCall.

Require Import CertiOS.audit.probes.V293ReadySchedCallProbe.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitDispatchExecution.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitExecution.
Require Import CertiOS.certiucos.v293.code.V293OSIntExit.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.code.V293OSSchedGuards.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Local Open Scope nat_scope.

Require Import CertiOS.audit.probes.V293OSIntExitDispatchExecutionProbe.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitDispatchCall.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitCallExecution.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCriticalGlobal.

Require Import CertiOS.audit.probes.V293OSIntExitDispatchCallProbe.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitSwitchEntry.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyFullCall.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPointerCompare.
Import ListNotations.
Definition SXct := OwnershipWaiting.
Definition SXge := FXge.
Definition SXcaller := FXcaller.
Definition SXextras := FXextras.
Definition SXextra := FXextra.
Definition SXmemory n nc := merge(RHmemory SXct)(SXextra n nc).
Definition SXstate M := V293_target_wstate SXge SXcaller M(RIabstract SXct).
Definition SXframe := RCframe **
 (V293_owned_record_cell((99%positive,0%Z),Tint8,V293_byteval 23) **
 V293_owned_record_cell((100%positive,0%Z),Tint8,V293_byteval 0)).
Definition SXentry_frame nc := V293_owned_record_cell((96%positive,0%Z),Tint8,V293_byteval nc) **
 (V293_owned_record_cell((98%positive,0%Z),Tint8,V293_byteval 1) **
 (V293_owned_record_cell((97%positive,0%Z),Tint32,Vint32(Int.repr 19)) **SXframe)).
Lemma SXold_outside : forall b i,
 b<>1%positive ->b<>41%positive ->b<>60%positive ->
 b<>80%positive ->b<>81%positive ->b<>82%positive ->
 b<>90%positive ->b<>91%positive ->b<>92%positive ->b<>93%positive ->
 get(RHmemory SXct)(b,i)=None.
Proof.
 intros b i N1 N41 N60 N80 N81 N82 N90 N91 N92 N93.
 unfold RHmemory,RTexec_memory,RTwith_outputs.
 repeat rewrite map_merge_semp by reflexivity.
 rewrite RToutside by assumption.
 unfold RToutputs,RHtarget;repeat rewrite OwnershipCellsOutside by
 (intro H;vm_compute in H;intuition congruence).
 unfold RTdecoder,V293_nat_memory;rewrite V293_encoded_memory_outside by(left;exact N92).
 reflexivity.
Qed.
Lemma SXjoin : forall n nc,join(RHmemory SXct)(SXextra n nc)(SXmemory n nc).
Proof.
 intros n nc;apply map_join_merge;apply map_disjoint;intros[b i].
 destruct(in_dec Pos.eq_dec b [94%positive;95%positive;96%positive;97%positive;98%positive;99%positive;100%positive]) as[Inside |Outside].
 - left;apply SXold_outside;cbn in Inside;intuition congruence.
 - right;left;unfold SXextra;apply OwnershipCellsOutside.
   intro H;vm_compute in H;cbn in Outside;intuition congruence.
Qed.
Lemma SXentry : forall n nc,n<256 ->nc<256 ->
 SXstate(SXmemory n nc)|=SWINVt(V293_ready_inv 80%positive 81%positive 82%positive)SXct **
 (V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval 88) **
 (V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipWaiting) **
 (V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval n) **
 (V293_owned_record_cell((95%positive,0%Z),Tint8,V293_byteval 0) ** SXentry_frame nc)))).
Proof.
 intros n nc N C.
 assert(Extra:V293_target_wstate SXge SXcaller(SXextra n nc)emp|=V293_owned_record_cells(SXextras n nc)).
 { apply OwnershipCellsSpatial.
   - vm_compute;repeat split;intros;intuition congruence.
   - repeat constructor;try reflexivity;apply V293_byte_type;assumption. }
 assert(Both:SXstate(SXmemory n nc)|=
 ((V293_owned_record_cell((90%positive,0%Z),Tint8,V293_byteval 99) **
   V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval 88)) **
 (SWINVt(V293_ready_inv 80%positive 81%positive 82%positive)SXct **
 (V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipWaiting) **
 V293_read_bytes 92%positive 0%Z V293_ready_table))) **V293_owned_record_cells(SXextras n nc)).
 { eapply V293_target_wstate_star with(m1:=RHmemory SXct)(m2:=SXextra n nc)
   (o1:=RIabstract SXct)(o2:=emp).
   - apply SXjoin.
   - apply map_join_emp.
   - apply FXold_entry.
   - exact Extra. }
 unfold SXentry_frame,SXframe,RCframe;cbn[SXextras FXextras DXextras V293_owned_record_cells app]in Both;clear Extra;sep auto.
Qed.

Lemma SXframe_good : GoodInvAsrt SXframe.
Proof. unfold SXframe;repeat split;try exact I;exact RCframe_good. Qed.
Lemma SXlookup : forall n nc k,k<256 ->
 load Tint8(SXmemory n nc)(92%positive,Z.of_nat k)=Some(V293_byteval(V293_ready_lookup k)).
Proof. intros;eapply load_mem_mono;[apply RHlookup;assumption|exists(SXextra n nc);apply SXjoin]. Qed.
Definition SXfunction := FXfunction.
Definition SXprogram := FXprogram.
Definition SXbody := V293_OSIntExit_abstract_body 113%Z 108%Z 109%Z 601%Z
 105%Z 103%Z 106%Z 110%Z 111%Z 107%Z 112%Z.
Definition SXK ks := kseq(sprim excrit)(kseq sret(kcall 300%Z SXbody SXcaller ks)).
Definition SXpre := SWINVt(V293_ready_inv 80%positive 81%positive 82%positive)SXct **
 (V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval 88) **
 (V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipWaiting) **
 (V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval 1) **
 (V293_owned_record_cell((95%positive,0%Z),Tint8,V293_byteval 0) **SXentry_frame 6)))).
Definition SXpost bs := SWINVt(V293_ready_inv 80%positive 81%positive 82%positive)SXct **
 (V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval 4) **
 (V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady) **
 (V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((95%positive,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((96%positive,0%Z),Tint8,V293_byteval 6) **
 (V293_owned_record_cell((98%positive,0%Z),Tint8,V293_byteval 1) **
 (V293_owned_record_cell((97%positive,0%Z),Tint32,Vint32(Int.repr 20)) **
 (Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **SXframe)))))))).
Lemma SXcurrent : V293_current_task OwnershipTasks SXct 6.
Proof.
 split;[lia|exists(wait(os_stat_sem(72%positive,Int.repr 5))Int.one);exists(Vptr(120%positive,Int.repr 7));reflexivity].
Qed.
Lemma SXnot_highest : ~V293_highest_ready OwnershipTasks SXct.
Proof. intros(p&m&Task&Minimum);vm_compute in Task;discriminate. Qed.
Lemma SXindependent_entry : forall ci,
 (SXge,SXcaller,SXmemory 1 6,(fun _=>false),(false,nil,ci),RIabstract SXct,spec_done None)|=SXpre.
Proof.
 intro ci;unfold SXpre;apply V293_ready_critical_stack with(ci:=nil).
 - unfold SXentry_frame;repeat split;try exact I;exact SXframe_good.
 - exact(SXentry 1 6 ltac:(lia)ltac:(lia)).
Qed.
(* The physical current pointer, physical cache, and abstract task map agree.
   Unlike the old byte-only comparison control, current here really waits at6. *)
Theorem SXconsistent_current :
 get SXge OSTCBCur=Some(1%positive,Tptr Tvoid) /\
 load(Tptr Tvoid)(SXmemory 1 6)(1%positive,0%Z)=Some(Vptr SXct) /\
 get(RIabstract SXct)curtid=Some(oscurt SXct) /\
 V293_current_task OwnershipTasks SXct 6 /\
 ~V293_highest_ready OwnershipTasks SXct.
Proof.
 split;[reflexivity| ];split.
 - eapply load_mem_mono;[ |exists(SXextra 1 6);apply SXjoin].
   eapply load_mem_mono;[ |exists RHtarget;apply RHjoin].
   eapply load_mem_mono;[ |exists RTdecoder;apply RTdecoder_join].
   eapply load_mem_mono;[ |exists RToutputs;apply RToutputs_join].
   eapply load_mem_mono;[ |exists RTmemory;apply RTjoin].
   eapply load_mem_mono;[ |exists OwnershipMemory;apply RIjoin].
   eapply mapstoval_load;[reflexivity|apply V293_encoded_memory_mapsto].
 - split;[reflexivity| ];split;[exact SXcurrent|exact SXnot_highest].
Qed.
Theorem SXcomplete_prefix : forall enabled ci ks,exists bs Mf,
 fresh(SXmemory 1 6)bs /\
 V293_local_steps SXprogram(curs(scall 300%Z nil),(kenil,ks))
 ((SXge,SXcaller,SXmemory 1 6),(fun _=>false),(enabled,nil,ci))
 (curs(sfexec 112%Z nil nil),(kenil,SXK ks))
 ((SXge,V293_cpu_lenv 601%Z bs,Mf),(fun _=>false),(false,nil,cons enabled ci)) /\
 (SXge,V293_cpu_lenv 601%Z bs,Mf,(fun _=>false),(false,nil,cons enabled ci),RIabstract SXct,spec_done None)|=SXpost bs /\
 load(Tptr V293_tcb_type)Mf(93%positive,0%Z)=Some(Vptr OwnershipReady) /\
 load Tint32 Mf(97%positive,0%Z)=Some(Vint32(Int.repr 20)) /\
 load Tint8 Mf(96%positive,0%Z)=Some(V293_byteval 6) /\
 (forall k,k<4 ->exists v,get Mf(bs,Z.of_nat k)=Some(true,v)) /\
 (forall c i,c<>bs ->c<>93%positive ->(c,i)<>(91%positive,0%Z) ->(c,i)<>(94%positive,0%Z) ->
   (c<>97%positive \/(i<0)%Z \/(4<=i)%Z) ->get Mf(c,i)=get(SXmemory 1 6)(c,i)).
Proof.
 intros enabled ci ks.
 destruct(V293_OSIntExit_switch_entry_execution 80%positive 81%positive 82%positive
 SXprogram ks SXge SXcaller(SXmemory 1 6)(fun _=>false)enabled nil ci(RIabstract SXct)(spec_done None)
 SXct SXframe OwnershipTasks 6 300%Z 107%Z 100%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z
 108%Z 109%Z 113%Z 601%Z 110%Z 111%Z 112%Z
 92%positive 91%positive 93%positive 94%positive 95%positive 98%positive 96%positive 97%positive(Int.repr 19)
 (V293_byteval 88)(Vptr OwnershipWaiting)
 eq_refl eq_refl ltac:(vm_compute;intuition congruence)
 ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)
 ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)
 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
 (RIfixed_tasks SXct)SXcurrent SXnot_highest SXframe_good(SXlookup 1 6)(SXindependent_entry ci))
 as(bs&next&nh&Mf&Fresh&Different&PriorityDifferent&Highest&NextPriority&Exec&Post&Target&Counter&Cache&Alive&Frame).
 assert(Next:next=OwnershipReady).
 { destruct RTliteral_rel as(Lo&Hi&Nonempty&Bitmap&Table).
   eapply V293_highest_unique;[exact Table|exact Highest|exact FXhighest]. }
 subst next.
 assert(Priority:nh=4).
 { destruct NextPriority as[Bound[st[m Task]]].
   assert(Ready:get OwnershipTasks OwnershipReady=Some(Int.repr 4,rdy,Vnull))by reflexivity.
   unfold get,TcbMap in Task,Ready;rewrite Ready in Task.
   apply V293_priority_repr_injective;[exact Bound|lia| ].
   symmetry;exact(f_equal(fun x=>match x with Some(p,_,_)=>p |None=>Int.zero end)Task). }
 subst nh;exists bs;exists Mf;repeat split;try assumption.
Qed.
Lemma SXpost_loads : forall enabled ci bs M,
 (SXge,V293_cpu_lenv 601%Z bs,M,(fun _=>false),(false,nil,cons enabled ci),RIabstract SXct,spec_done None)|=SXpost bs ->
 load Tint8 M(90%positive,0%Z)=Some(V293_byteval 99) /\
 load Tint8 M(99%positive,0%Z)=Some(V293_byteval 23) /\
 load Tint8 M(100%positive,0%Z)=Some(V293_byteval 0) /\
 load Tint32 M(bs,0%Z)=Some(Vint32 Int.zero).
Proof.
 intros enabled ci bs M Held;unfold SXpost,SXframe,RCframe in Held.
 repeat split;eapply V293_record_star_load_l with
 (s:=(SXge,V293_cpu_lenv 601%Z bs,M,(fun _=>false),(false,nil,cons enabled ci),RIabstract SXct,spec_done None))(Q:=Atrue).
 - apply V293_owned_record_cell_load.
 - sep auto.
 - apply V293_owned_record_cell_load.
 - sep auto.
 - apply V293_owned_record_cell_load.
 - sep auto.
 - instantiate (1:=Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero)).
   intros ((((((ge0,le0),M0),ir0),aux0),O0),op0) [Raw Empty];eapply mapstoval_load;[reflexivity|exact Raw].
 - sep auto.
Qed.
Theorem SXboth_IE_prefix : forall ci,
 exists b0 M0 b1 M1,
 V293_local_steps SXprogram(curs(scall 300%Z nil),(kenil,kstop))
 ((SXge,SXcaller,SXmemory 1 6),(fun _=>false),(false,nil,ci))
 (curs(sfexec 112%Z nil nil),(kenil,SXK kstop))
 ((SXge,V293_cpu_lenv 601%Z b0,M0),(fun _=>false),(false,nil,cons false ci)) /\
 V293_local_steps SXprogram(curs(scall 300%Z nil),(kenil,kstop))
 ((SXge,SXcaller,SXmemory 1 6),(fun _=>false),(true,nil,ci))
 (curs(sfexec 112%Z nil nil),(kenil,SXK kstop))
 ((SXge,V293_cpu_lenv 601%Z b1,M1),(fun _=>false),(false,nil,cons true ci)) /\
 load Tint32 M0(97%positive,0%Z)=Some(Vint32(Int.repr 20)) /\
 load Tint32 M1(97%positive,0%Z)=Some(Vint32(Int.repr 20)) /\
 load Tint8 M0(99%positive,0%Z)=Some(V293_byteval 23) /\
 load Tint8 M1(99%positive,0%Z)=Some(V293_byteval 23) /\
 load Tint8 M0(100%positive,0%Z)=Some(V293_byteval 0) /\
 load Tint8 M1(100%positive,0%Z)=Some(V293_byteval 0) /\
 (forall k,k<4 ->exists v,get M0(b0,Z.of_nat k)=Some(true,v)) /\
 (forall k,k<4 ->exists v,get M1(b1,Z.of_nat k)=Some(true,v)).
Proof.
 intro ci.
 destruct(SXcomplete_prefix false ci kstop)as(b0&M0&Fresh0&Exec0&Post0&Target0&Counter0&Cache0&Alive0&Frame0).
 destruct(SXcomplete_prefix true ci kstop)as(b1&M1&Fresh1&Exec1&Post1&Target1&Counter1&Cache1&Alive1&Frame1).
 destruct(SXpost_loads false ci b0 M0 Post0)as(Canary0&Saved0&Run0&Local0).
 destruct(SXpost_loads true ci b1 M1 Post1)as(Canary1&Saved1&Run1&Local1).
 exists b0;exists M0;exists b1;exists M1;repeat split;assumption.
Qed.
Theorem SXswitch_lookup_absent : SXprogram 112%Z=None.
Proof. reflexivity. Qed.
Theorem SXreal_port_boundary_no_step : forall ks m ir au,
 ~exists C' st',loststep SXprogram(curs(sfexec 112%Z nil nil),(kenil,ks))(m,ir,au)C' st'.
Proof. intros;apply V293_missing_port_has_no_step;exact SXswitch_lookup_absent. Qed.

(* Prospective single-factor control at the exact unequal tail, not a second
   full OSIntExit implementation. Both variants share P, heap and continuation. *)
Definition SXtail := sif(V293_OSSched_different 103%Z 110%Z)
 (sseq(V293_OSSched_increment 111%Z)(sseq(sskip None)(scall 112%Z nil)))(sskip None).
Definition SXomit_tail := sif(V293_OSSched_different 103%Z 110%Z)
 (sseq(sskip None)(scall 112%Z nil))(sskip None).
Definition SXtail_frame := SWINVt(V293_ready_inv 80%positive 81%positive 82%positive)SXct **
 (V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipWaiting) **
 (V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval 1) **
 (V293_owned_record_cell((95%positive,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((96%positive,0%Z),Tint8,V293_byteval 6) **
 (V293_owned_record_cell((98%positive,0%Z),Tint8,V293_byteval 1) **SXframe))))).
Lemma SXpluck : forall tp a v M R,
 SXstate M|=V293_owned_record_cell(a,tp,v)**R ->load tp M a=Some v.
Proof.
 intros;eapply V293_record_star_load_l with(s:=SXstate M);
 [apply V293_owned_record_cell_load|eassumption].
Qed.
Lemma SXindependent_tail : exists M,
 store Tint8(SXmemory 1 6)(91%positive,0%Z)(V293_byteval 4)=Some M /\
 SXstate M|=V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval 4) **
 (V293_owned_record_cell((97%positive,0%Z),Tint32,Vint32(Int.repr 19)) **SXtail_frame).
Proof.
 assert(Held:SXstate(SXmemory 1 6)|=V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval 88) **
 (V293_owned_record_cell((97%positive,0%Z),Tint32,Vint32(Int.repr 19)) **SXtail_frame)).
 { pose proof(SXentry 1 6 ltac:(lia)ltac:(lia))as Entry.
   unfold SXtail_frame,SXentry_frame in *;sep auto. }
 eapply V293_owned_record_cell_update;[reflexivity|exact Held].
Qed.
Lemma SXomit_execution : forall M ks,
 load Tint8 M(91%positive,0%Z)=Some(V293_byteval 4) ->
 load Tint8 M(96%positive,0%Z)=Some(V293_byteval 6) ->
 cstepstar SXprogram(curs SXomit_tail,(kenil,ks))(SXge,SXcaller,M)
 (curs(sfexec 112%Z nil nil),(kenil,ks))(SXge,SXcaller,M).
Proof.
 intros M ks High Cache.
 destruct(V293_OSSched_byte_comparison_eval SXge SXcaller M 103%Z 110%Z 91%positive 96%positive 4 6
 ltac:(lia)ltac:(lia)eq_refl eq_refl eq_refl eq_refl High Cache)as[Guard GuardType].
 cbn[Nat.eqb]in Guard;unfold SXomit_tail.
 eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply sif_step]| ].
 eapply V293_cstepstar_trans;[apply V293_expr_steps;apply evalval_imply_estepstar;exact Guard| ].
 eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply svift_step;reflexivity]| ].
 eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply sseq_step]| ].
 eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply sskip_step]| ].
 eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply snpcall_step]|apply c_stepstar0].
Qed.
Theorem SXcounter_increment_ablation : forall ks,exists M19 M20,
 store Tint8(SXmemory 1 6)(91%positive,0%Z)(V293_byteval 4)=Some M19 /\
 cstepstar SXprogram(curs SXtail,(kenil,ks))(SXge,SXcaller,M19)
 (curs(sfexec 112%Z nil nil),(kenil,ks))(SXge,SXcaller,M20) /\
 cstepstar SXprogram(curs SXomit_tail,(kenil,ks))(SXge,SXcaller,M19)
 (curs(sfexec 112%Z nil nil),(kenil,ks))(SXge,SXcaller,M19) /\
 load Tint32 M19(97%positive,0%Z)=Some(Vint32(Int.repr 19)) /\
 load Tint32 M20(97%positive,0%Z)=Some(Vint32(Int.repr 20)) /\
 load Tint8 M19(96%positive,0%Z)=Some(V293_byteval 6) /\
 load Tint8 M20(96%positive,0%Z)=Some(V293_byteval 6) /\
 load Tint8 M19(99%positive,0%Z)=Some(V293_byteval 23) /\
 load Tint8 M20(99%positive,0%Z)=Some(V293_byteval 23) /\
 (forall b i,b<>97%positive \/(i<0)%Z \/(4<=i)%Z ->get M20(b,i)=get M19(b,i)).
Proof.
 intro ks;destruct SXindependent_tail as(M19&StoreHigh&Held).
 assert(High:load Tint8 M19(91%positive,0%Z)=Some(V293_byteval 4)).
 { eapply SXpluck;exact Held. }
 assert(Cache:load Tint8 M19(96%positive,0%Z)=Some(V293_byteval 6)).
 { eapply SXpluck with(R:=Atrue);unfold SXtail_frame in Held;sep auto. }
 assert(Counter:load Tint32 M19(97%positive,0%Z)=Some(Vint32(Int.repr 19))).
 { eapply SXpluck with(R:=Atrue);sep auto. }
 assert(Caller:load Tint8 M19(99%positive,0%Z)=Some(V293_byteval 23)).
 { eapply SXpluck with(R:=Atrue);unfold SXtail_frame,SXframe in Held;sep auto. }
 assert(CounterHeld:SXstate M19|=V293_owned_record_cell((97%positive,0%Z),Tint32,Vint32(Int.repr 19)) **
 (V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval 4) **SXtail_frame))by sep auto.
 destruct(V293_exit_change_to_sfexec SXprogram ks SXge SXcaller M19(fun _=>false)(false,nil,nil)
 (RIabstract SXct)(spec_done None)
 (V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval 4) **SXtail_frame)
 103%Z 110%Z 111%Z 112%Z 91%positive 96%positive 97%positive 4 6(Int.repr 19)
 ltac:(lia)ltac:(lia)ltac:(lia)eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl High Cache CounterHeld)
 as(M20&Exec&Store&After&Frame).
 assert(Counter20:load Tint32 M20(97%positive,0%Z)=Some(Vint32(Int.repr 20))).
 { eapply SXpluck;exact After. }
 assert(Cache20:load Tint8 M20(96%positive,0%Z)=Some(V293_byteval 6)).
 { eapply SXpluck with(R:=Atrue);unfold SXtail_frame in After;sep auto. }
 assert(Caller20:load Tint8 M20(99%positive,0%Z)=Some(V293_byteval 23)).
 { eapply SXpluck with(R:=Atrue);unfold SXtail_frame,SXframe in After;sep auto. }
 exists M19;exists M20;repeat split;try assumption.
 eapply SXomit_execution;assumption.
Qed.
