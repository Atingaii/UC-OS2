(* Actual allocation and return-tail fixture; NOT execution through the missing hook. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickReturnTail.
Require Import CertiOS.audit.probes.V293TimeTickCallContextProbe.
Require Import CertiOS.audit.probes.V293TimeTickHookContractProbe.
(* Genuine Vundef scan bytes; same existing invariant, not typed Vundef. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickScanSlot.
Require Import CertiOS.audit.probes.V293TimeTickSwitchBoundaryProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.framework.proof.memory_prop.
Require Import CertiOS.framework.proof.lmachLib.
(* Existing SWINV boundary, independent literal-byte entry; disabled/clear only. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickSwitchBoundary.
Require Import CertiOS.audit.probes.V293TimeTickPostHookCoreProbe.
(* New joint byte heap: scan starts at idle, NOT the nonempty head. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickPostHookCore.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickPostHookHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickSuffix.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickShared.
Require Import CertiOS.audit.probes.V293TimeTickChainOpenProbe.
(* Canonical entry is packed directly from literal bytes, not from the new opening. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickChainOpen.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickRecordReassembly.
Require Import CertiOS.certiucos.v293.proofs.V293TCBJointShared.
Require Import CertiOS.audit.probes.V293TimeTickWhileCoreProbe.
Require Import CertiOS.framework.proof.soundness.
(* Independent four-task literal heap; original while and exact residuals. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickWhileCore.
Require Import CertiOS.audit.probes.V293TimeTickReadyChainProbe.
Require Import CertiOS.audit.probes.V293TimeTickWhileRecordsProbe.
Require Import CertiOS.audit.probes.V293TimeTickWhileSharedProbe.
Require Import CertiOS.audit.probes.V293TimeTickReadyUpdateProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickReadyUpdate.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickWhileRecords.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickWhileShared.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickDelayHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickWhileHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickTaskBridge.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLosslessFields.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLoop.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickExpiry.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickReadyChain.
Require Import CertiOS.certiucos.v293.proofs.V293TimeReadyShared.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293SharedStateWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.code.V293OSTimeTick.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.audit.probes.V293ReadyTaskInvariantProbe.
Require Import CertiOS.audit.probes.V293TimeTickDelayHoareProbe.
Require Import CertiOS.audit.probes.V293TimeTickTraversalProbe.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Coq.Sorting.Permutation Lia.
Import ListNotations.
Local Open Scope nat_scope.



Require Import CertiOS.certiucos.v293.proofs.V293TimeTickCallContext.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCritical.

Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLosslessFields.
Definition TRpost run:=V293_tick_scan_switch_result WhileBindings WhileIdle
 93%positive 92%positive 94%positive 96%positive 171%positive 98%positive 99%positive run
 (V293_tick_saved_frame 172%positive CCrest)Vundef(fun _=>false)[1][false].
Definition TRreturned run:=V293_tick_return_resources WhileBindings WhileIdle
 93%positive 92%positive 94%positive 96%positive 98%positive 99%positive run CCrest
 (fun _=>false)[1][false].

Lemma TRbindings_empty : CCbindings ==> Aemp.
Proof.
 intros s Held;destruct s as[[[[[[ge le]M]ir]aux]O]op].
 destruct Held as[[b[Binding[Address[Mem Abs]]]] Rest].
 split;assumption.
Qed.
Lemma TRstrip_result : forall run,CCpost run ==> TRpost run.
Proof.
 intro run;unfold CCpost,TRpost,CCframe.
 apply V293_tick_result_forget_bindings;exact TRbindings_empty.
Qed.
Lemma TRrest_good : GoodFunAsrt CCrest.
Proof.
 unfold CCrest;split;[unfold V293_owned_record_cell;split;exact I| ].
 split;[exact I| ];split.
 - unfold LINV,V293_witness_li;cbn[GoodFunAsrt];split;exact I.
 - apply V293_inv_function_assertion;apply V293_owned_cells_good.
Qed.

(* This accepts precisely the logical output of HCrules; it does not assert
   that the absent hook has run. *)
Theorem TRfrom_hook_contract_post : forall ks caller M O run,
 CCstate M O(END None) |= CCpost run -> exists Mf,
 V293_local_steps CCprogram(curs(sskip None),(kenil,kseq sret(kcall 2001%Z
   (sseq(V293_tick_body 901%Z 902%Z 903%Z 904%Z 1001%Z 1002%Z 1003%Z 2002%Z)sret)caller ks)))
  ((PCge,CCle,M),(fun _=>false),(false,[1],[false]))
  (curs(sskip None),(kenil,ks))((PCge,caller,Mf),(fun _=>false),(false,[1],[false])) /\
 (PCge,caller,Mf,(fun _=>false),(false,[1],[false]),O,END None) |= TRreturned run /\
 (forall k,k<4 -> get Mf(171%positive,Z.of_nat k)=None /\ get Mf(172%positive,Z.of_nat k)=None).
Proof.
 intros ks caller M O run Held;apply TRstrip_result in Held.
 eapply V293_tick_return_tail;[discriminate|exact TRrest_good|exact Held].
Qed.

Lemma TRallocated_resources : forall clock run M O op,
 CCstate M O op |= <||PCcode run||> ** OS[(fun _=>false),false,[1],[false]] ** CCsuffix clock run ->
 CCstate M O op |= Amapsto(171%positive,0%Z)(Tptr V293_tcb_type)true Vundef **
  (Amapsto(172%positive,0%Z)Tint32 true(Vint32 Int.zero) ** CCbare clock run).
Proof.
 intros clock run M O op Held.
 assert(Packed:CCstate M O op |= CCbindings **
  (Amapsto(171%positive,0%Z)(Tptr V293_tcb_type)true Vundef **
   (Amapsto(172%positive,0%Z)Tint32 true(Vint32 Int.zero) ** CCbare clock run))).
 { unfold CCsuffix,V293_tick_call_suffix,V293_tick_scan_switch_pre,V293_tick_scan_supplement,
   V293_tick_saved_frame,CCframe,CCbare,V293_tick_call_shared,V293_owned_record_cell in *;
   clear -Held;sep auto. }
 eapply astar_mono in Packed;[ |exact TRbindings_empty|intros st H;exact H].
 clear -Packed;sep auto.
Qed.

Lemma TRcaller_cells : forall ge le M ir aux O op clock run,
 (ge,le,M,ir,aux,O,op) |= CCbare clock run ->
 load Tint32 M(90%positive,0%Z)=Some(Vint32(Int.repr 99)) /\
 load(Tptr V293_tcb_type)M(70%positive,0%Z)=Some(Vptr WhileIdle).
Proof.
 intros ge le M ir aux O op clock run Held.
 assert(Cells:(ge,le,M,ir,aux,O,op) |= V293_owned_record_cells WhileFrameCells ** Atrue).
 { unfold CCbare,V293_tick_call_shared,CCrest in Held;clear -Held;sep auto. }
 split.
 - change(load Tint32(getmem(ge,le,M,ir,aux,O,op))(90%positive,0%Z)=Some(Vint32(Int.repr 99))).
   eapply V293_record_star_load_l;[ |exact Cells].
   intros st H;eapply V293_owned_record_cells_load with(cells:=WhileFrameCells);
   [unfold WhileFrameCells;left;reflexivity|exact H].
 - assert(Slot:(ge,le,M,ir,aux,O,op) |=
    V293_owned_record_cell(V293_tick_pointer_cell 70%positive WhileIdle) ** Atrue).
   { unfold CCbare,V293_tick_call_shared,CCrest in Held;clear -Held;sep auto. }
   change(load(Tptr V293_tcb_type)(getmem(ge,le,M,ir,aux,O,op))(70%positive,0%Z)=Some(Vptr WhileIdle)).
   eapply V293_record_star_load_l;[apply V293_owned_record_cell_load|exact Slot].
Qed.

(* Independently reject ownership at the exact freed endpoint. *)
Lemma TRfreed_not_owned : forall ge le M ir aux O op b tp v,
 get M(b,0%Z)=None -> 0<typelen tp ->
 ~(ge,le,M,ir,aux,O,op) |= Amapsto(b,0%Z)tp true v ** Atrue.
Proof.
 intros ge le M ir aux O op b tp v Gone Positive Held.
 pose proof(V293_tick_raw_owned_writable _ _ _ _ _ _ _ _ _ _ _ Held)as Writable.
 destruct(Writable 0 Positive)as[byte Cell].
 replace(0+Z.of_nat 0)%Z with 0%Z in Cell by lia.
 rewrite Gone in Cell;discriminate.
Qed.

Theorem TRsame_allocated_return : forall ks caller clock run,run<256 ->exists Ms Mf,
 CCexecution ks clock run Ms /\
 cstepstar CCprogram(curs sret,(kenil,kcall 2001%Z
   (sseq(V293_tick_body 901%Z 902%Z 903%Z 904%Z 1001%Z 1002%Z 1003%Z 2002%Z)sret)caller ks))
  (PCge,CCle,Ms)(curs(sskip None),(kenil,ks))(PCge,caller,Mf) /\
 (PCge,caller,Mf,(fun _=>false),(false,[1],[false]),PCabs clock,PCcode run) |= CCbare clock run /\
 (forall k,k<4 -> get Mf(171%positive,Z.of_nat k)=None /\ get Mf(172%positive,Z.of_nat k)=None) /\
 load Tint32 Mf(90%positive,0%Z)=Some(Vint32(Int.repr 99)) /\
 load(Tptr V293_tcb_type)Mf(70%positive,0%Z)=Some(Vptr WhileIdle) /\
 ~(PCge,caller,Mf,(fun _=>false),(false,[1],[false]),PCabs clock,PCcode run) |=
  Amapsto(171%positive,0%Z)(Tptr V293_tcb_type)true Vundef ** Atrue /\
 ~(PCge,caller,Mf,(fun _=>false),(false,[1],[false]),PCabs clock,PCcode run) |=
  Amapsto(172%positive,0%Z)Tint32 true(Vint32 Int.zero) ** Atrue.
Proof.
 intros ks caller clock run Range.
 destruct(CCallocated_entry ks clock run Range)as(Ms&Prefix&Scan&Saved&Entry).
 pose proof(TRallocated_resources clock run Ms(PCabs clock)(PCcode run)Entry)as Resources.
 destruct(V293_tick_owned_void_return CCprogram ks PCge caller Ms(fun _=>false)
  (false,[1],[false])(PCabs clock)(PCcode run)901%Z 904%Z 171%positive 172%positive 2001%Z
  (sseq(V293_tick_body 901%Z 902%Z 903%Z 904%Z 1001%Z 1002%Z 1003%Z 2002%Z)sret)
  Vundef(CCbare clock run)ltac:(discriminate)(CCbare_good_fun clock run)Resources)
  as(Mf&Return&Rest&Removed).
 destruct(TRcaller_cells _ _ _ _ _ _ _ clock run Rest)as[Canary Old].
 exists Ms;exists Mf;split;[exact Prefix| ];split;[exact Return| ];split;[exact Rest| ];
 split;[exact Removed| ];split;[exact Canary| ];split;[exact Old| ];split.
 - eapply TRfreed_not_owned;[exact(proj1(Removed 0 ltac:(lia)))|cbn;lia].
 - eapply TRfreed_not_owned;[exact(proj2(Removed 0 ltac:(lia)))|cbn;lia].
Qed.

(* The allocation trace stops at the real hook. Return above is a separate
   tail fixture on those bytes, never a composed whole-tick execution. *)
Theorem TRmissing_hook_still_blocked : forall ks m ir aux,
 ~exists C' state',loststep CCprogram(curs(sfexec 2002%Z nil nil),(kenil,ks))(m,ir,aux) C' state'.
Proof. apply HCmissing_no_step. Qed.

Definition TRheap run:=
 Amapsto(171%positive,0%Z)(Tptr V293_tcb_type)true Vundef **
 (Amapsto(172%positive,0%Z)Tint32 true(Vint32 Int.zero) **
  (SWINV SCinv ** (V293_owned_record_cells(V293_tick_chain_missing WhileBindings WhileIdle) **
   (V293_owned_record_cells(V293_tick_post_hook_core_globals WhileBindings WhileIdle
     98%positive 99%positive run) ** CCrest)))).
Lemma TRheap_change : forall run,can_change_aop(TRheap run).
Proof.
 intro run.
 assert(Inv:forall n low,can_change_aop(starinv_isr SCinv low n)).
 { induction n;intro low;cbn[starinv_isr can_change_aop].
   - intro sr;repeat split;apply V293_tick_update_change;apply invp.
   - split;[intro sr;repeat split;apply V293_tick_update_change;apply invp|apply IHn]. }
 unfold TRheap;cbn[can_change_aop];repeat split;try exact I.
 - unfold SWINV,isrclr,invlth_isr;cbn[can_change_aop];repeat split;try exact I.
   apply Inv.
Qed.
Lemma TRheap_from_allocated : forall clock run M O op,
 CCstate M O op |= <||PCcode run||> ** OS[(fun _=>false),false,[1],[false]] ** CCsuffix clock run ->
 CCstate M O op |= TRheap run.
Proof.
 intros clock run M O op Held;apply TRallocated_resources in Held.
 unfold TRheap; eapply astar_mono;[intros st H;exact H| |exact Held].
 apply astar_mono;[intros st H;exact H| ].
 unfold CCbare,V293_tick_call_shared;apply astar_mono.
 - unfold V293_tick_switch_view;intros st[H View];exact H.
 - intros st H;exact H.
Qed.

(* A nonvacuous complete stopped-result fixture on the allocated bytes.
   Only the ghost program position is placed at END; clock++/hook execution
   is NOT claimed by this fixture construction. *)
Theorem TRstopped_result_fixture : forall ks clock run,
 run<256 -> run<>1 ->exists Ms,
 CCexecution ks clock run Ms /\ CCstate Ms(PCabs clock)(END None) |= TRpost run.
Proof.
 intros ks clock run Range Stopped.
 destruct(CCallocated_entry ks clock run Range)as(Ms&Prefix&Scan&Saved&Entry).
 pose proof(TRheap_from_allocated clock run Ms(PCabs clock)(PCcode run)Entry)as Heap.
 assert(New:CCstate Ms(PCabs clock)(END None) |= TRheap run).
 { eapply change_aop_rule;[exact Heap|apply TRheap_change]. }
 assert(Control:CCstate Ms(PCabs clock)(END None) |=
  Aisr(fun _=>false) ** (Aie false ** (Ais([1]) ** (Acs([false]) ** TRheap run)))).
 { apply astar_l_aisr_intro;[ |reflexivity]. apply astar_l_aie_intro;[ |reflexivity].
   apply astar_l_ais_intro;[ |reflexivity]. apply astar_l_acs_intro;[exact New|reflexivity]. }
 assert(End:CCstate Ms(PCabs clock)(END None) |=
  <||END None||> ** OS[(fun _=>false),false,[1],[false]] ** TRheap run).
 { apply astar_l_aop'_intro;[ |reflexivity];clear -Control;sep auto. }
 exists Ms;split;[exact Prefix| ].
 unfold TRpost,V293_tick_scan_switch_result.
 assert(E:Nat.eqb run 1=false)by(apply Nat.eqb_neq;exact Stopped).
 rewrite E.
 unfold TRheap,V293_tick_scan_supplement,V293_tick_saved_frame,V293_owned_record_cell in *;
 clear -End;sep auto.
Qed.

(* The full stopped-result interface is satisfiable and drives the actual
   tail. The prefix and tail remain separate; no absent hook is executed. *)
Theorem TRstopped_fixture_return : forall ks caller clock run,
 run<256 -> run<>1 -> exists Ms,exists Mf,
 CCexecution ks clock run Ms /\
 CCstate Ms(PCabs clock)(END None) |= TRpost run /\
 V293_local_steps CCprogram(curs(sskip None),(kenil,kseq sret(kcall 2001%Z
   (sseq(V293_tick_body 901%Z 902%Z 903%Z 904%Z 1001%Z 1002%Z 1003%Z 2002%Z)sret)caller ks)))
  ((PCge,CCle,Ms),(fun _=>false),(false,[1],[false]))
  (curs(sskip None),(kenil,ks))((PCge,caller,Mf),(fun _=>false),(false,[1],[false])) /\
 (PCge,caller,Mf,(fun _=>false),(false,[1],[false]),PCabs clock,END None) |= TRreturned run /\
 (forall k,k<4 -> get Mf(171%positive,Z.of_nat k)=None /\ get Mf(172%positive,Z.of_nat k)=None).
Proof.
 intros ks caller clock run Range Stopped.
 destruct(TRstopped_result_fixture ks clock run Range Stopped)as(Ms&Prefix&Post).
 assert(Tail:exists Mf,
 V293_local_steps CCprogram(curs(sskip None),(kenil,kseq sret(kcall 2001%Z
   (sseq(V293_tick_body 901%Z 902%Z 903%Z 904%Z 1001%Z 1002%Z 1003%Z 2002%Z)sret)caller ks)))
  ((PCge,CCle,Ms),(fun _=>false),(false,[1],[false]))
  (curs(sskip None),(kenil,ks))((PCge,caller,Mf),(fun _=>false),(false,[1],[false])) /\
 (PCge,caller,Mf,(fun _=>false),(false,[1],[false]),PCabs clock,END None) |= TRreturned run /\
 (forall k,k<4 -> get Mf(171%positive,Z.of_nat k)=None /\ get Mf(172%positive,Z.of_nat k)=None)).
 { eapply V293_tick_return_tail;[discriminate|exact TRrest_good|exact Post]. }
 destruct Tail as(Mf&Exec&Returned&Removed).
 exists Ms;exists Mf;split;[exact Prefix| ];split;[exact Post| ];split;[exact Exec| ];split;assumption.
Qed.
