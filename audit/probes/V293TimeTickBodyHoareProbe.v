(* Full body logic under an external hook Spec; actual trace stops before that hook. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickReturnTail.
Require Import CertiOS.audit.probes.V293TimeTickCallContextProbe.
Require Import CertiOS.audit.probes.V293TimeTickHookContractProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickScanSlot.
Require Import CertiOS.audit.probes.V293TimeTickSwitchBoundaryProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.framework.proof.memory_prop.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickSwitchBoundary.
Require Import CertiOS.audit.probes.V293TimeTickPostHookCoreProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickPostHookCore.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickPostHookHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickSuffix.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickShared.
Require Import CertiOS.audit.probes.V293TimeTickChainOpenProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickChainOpen.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickRecordReassembly.
Require Import CertiOS.certiucos.v293.proofs.V293TCBJointShared.
Require Import CertiOS.audit.probes.V293TimeTickWhileCoreProbe.
Require Import CertiOS.framework.proof.soundness.
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
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickBodyHoare.
Require Import CertiOS.audit.probes.V293TimeTickReturnTailProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.

Definition BHbind:=V293_time_binding true 904%Z 172%positive.
Definition BHentry old clock run:=V293_tick_body_entry WhileBindings WhileIdle Vnull WhileReady ChainEvents
 93%positive 92%positive 94%positive 96%positive 171%positive 172%positive 98%positive 99%positive run
 CCrest 904%Z CCbindings old clock(fun _=>false)[1][false].
Definition BHreturn run:=V293_tick_body_return WhileBindings WhileIdle
 93%positive 92%positive 94%positive 96%positive 171%positive 172%positive 98%positive 99%positive run
 CCrest 904%Z CCbindings(fun _=>false)[1][false].
Definition BHbody:=sseq(V293_tick_body 901%Z 902%Z 903%Z 904%Z 1001%Z 1002%Z 1003%Z 2002%Z)sret.
Definition BHmemory clock run:=allocb(allocb(PCmemory clock run)171%positive 0%Z 4)172%positive 0%Z 4.
Definition BHprefix ks clock run Mi:=V293_local_steps CCprogram
 (curs(scall 2001%Z[]),(kenil,ks))((PCge,emp,PCmemory clock run),(fun _=>false),(false,[1],[false]))
 (curs BHbody,(kenil,kcall 2001%Z BHbody emp ks))((PCge,CCle,Mi),(fun _=>false),(false,[1],[false])).

Lemma BHbinding : forall op,CCstate emp emp op |= BHbind.
Proof.
 intro op;unfold BHbind,V293_time_binding;exists 172%positive.
 split;[vm_compute;reflexivity| ];repeat split;reflexivity.
Qed.
Lemma BHadd_binding : forall M O op p,
 CCstate M O op |= p -> CCstate M O op |= BHbind ** p.
Proof.
 intros M O op p Held;apply sat_split'.
 exists(empmem:mem);exists M;exists(emp:osabst);exists O.
 split;[apply map_join_comm;apply map_join_emp| ];split;[apply map_join_comm;apply map_join_emp| ];
 split;[apply BHbinding|exact Held].
Qed.
Lemma BHraw_saved_load : forall v st,
 (v=Vundef \/ exists i,v=Vint32 i) ->
 st |= Amapsto(172%positive,0%Z)Tint32 true v ->
 load Tint32(getmem st)(172%positive,0%Z)=Some v.
Proof.
 intros v st Values[Mapsto Empty].
 unfold mapstoval in Mapsto;destruct Mapsto as(bytes&Enc&Points);subst bytes.
 pose proof(ptomvallist_loadbytes _ _ _ _ Points)as Read.
 rewrite encode_val_length in Read;unfold load,loadm;rewrite Read.
 destruct Values as[E|[i E]];subst v.
 - reflexivity.
 - apply f_equal;apply type_val_mach_encode_val_decode_val;reflexivity.
Qed.
Lemma BHentry_load : forall old clock run M O op,
 (old=Vundef \/ exists i,old=Vint32 i) ->
 CCstate M O op |= BHentry old clock run ->
 load Tint32 M(172%positive,0%Z)=Some old.
Proof.
 intros old clock run M O op Values Held.
 assert(Slot:CCstate M O op |= Amapsto(172%positive,0%Z)Tint32 true old ** Atrue).
 { unfold BHentry,V293_tick_body_entry,V293_time_cell in Held;clear -Held;sep auto. }
 change(load Tint32(getmem(CCstate M O op))(172%positive,0%Z)=Some old).
 eapply V293_record_star_load_l;[intros st K;apply BHraw_saved_load;[exact Values|exact K]|exact Slot].
Qed.

(* Independent allocation of both raw cells; no initialization before entry. *)
Theorem BHallocated_entry : forall clock run,run<256 ->
 CCstate(BHmemory clock run)(PCabs clock)(PCcode run) |= BHentry Vundef clock run.
Proof.
 intros clock run Range.
 pose proof(V293_tick_allocate_frame _ _ _ _ _ _ _ 171%positive(Tptr V293_tcb_type)_
  (CCfresh clock run _ (or_introl eq_refl))(CCentry clock run Range))as Scan.
 pose proof(V293_tick_allocate_frame _ _ _ _ _ _ _ 172%positive Tint32 _
  (CCfresh_saved clock run)Scan)as Both.
 apply BHadd_binding in Both.
 unfold BHentry,V293_tick_body_entry,V293_time_cell,BHbind,V293_tick_call_shared,CCpre,CCshared,CCframe in *;
 clear -Both;sep auto.
Qed.
Theorem BHallocated_prefix : forall ks clock run,
 BHprefix ks clock run(BHmemory clock run).
Proof.
 intros ks clock run.
 assert(ScanUnbound:~indom(emp:env)901%Z).
 { intros[v E];rewrite map_emp_get in E;discriminate. }
 assert(SavedUnbound:~indom(set(emp:env)901%Z(171%positive,Tptr V293_tcb_type))904%Z).
 { intros[v E];rewrite map_get_set' in E by discriminate;rewrite map_emp_get in E;discriminate. }
 unfold BHprefix,BHbody,BHmemory.
 eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply snpcall_step]| ].
 eapply V293_local_cons.
 { apply ostc_step;eapply stmt_step;[reflexivity| ].
   eapply sfexec_step with(d1:=dnil)(d2:=dcons 901%Z(Tptr V293_tcb_type)(dcons 904%Z Tint32 dnil));
   [reflexivity|reflexivity|reflexivity|exact I|reflexivity]. }
 eapply V293_local_cons.
 { apply ostc_step;eapply stmt_step;[reflexivity| ].
   eapply salloclv_step;[reflexivity|reflexivity| ];exists 171%positive;repeat split;
    try assumption;try reflexivity;apply CCfresh;left;reflexivity. }
 eapply V293_local_cons.
 { apply ostc_step;eapply stmt_step;[reflexivity| ].
   eapply salloclv_step;[reflexivity|reflexivity| ];exists 172%positive;repeat split;
    try assumption;try reflexivity;apply CCfresh_saved. }
 eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sallocend_step]| ].
 apply V293_local_refl.
Qed.
Theorem BHsame_uninitialized_endpoint : forall ks clock run,run<256 ->exists Mi,
 BHprefix ks clock run Mi /\
 CCstate Mi(PCabs clock)(PCcode run) |= BHentry Vundef clock run /\
 load Tint32 Mi(172%positive,0%Z)=Some Vundef /\
 ~CCstate Mi(PCabs clock)(PCcode run) |= BHentry(Vint32 Int.zero)clock run.
Proof.
 intros ks clock run Range;exists(BHmemory clock run).
 pose proof(BHallocated_entry clock run Range)as Held.
 pose proof(BHentry_load _ _ _ _ _ _ (or_introl eq_refl)Held)as Read.
 split;[apply BHallocated_prefix| ];split;[exact Held| ];split;[exact Read| ].
 intro Bad;pose proof(BHentry_load _ _ _ _ _ _ (or_intror(ex_intro _ Int.zero eq_refl))Bad)as Wrong.
 rewrite Read in Wrong;discriminate.
Qed.

Theorem BHrules : forall sd clock run old,run<256 ->
 InfRules(HCspec clock run)sd V293_witness_li SCinv(BHreturn run)Afalse
  (BHentry old clock run)BHbody Afalse WhileReady.
Proof.
 intros sd clock run old Range.
 apply V293_tick_body_hoare with(good:=HCgood clock run).
 - exact RUnoabs.
 - change(368+50<=4294967295)%Z;lia.
 - exact WhileBindingsValid.
 - exact WhileKeysUnique.
 - exact Range.
 - exact CCenv.
 - exact HCcur.
 - exact(proj1 CCframe_good).
 - exact(proj2 CCframe_good).
 - exact(proj1 CCframe_change).
 - exact(proj2 CCframe_change).
 - change(1<=INUM)%nat;unfold INUM;lia.
 - reflexivity.
 - reflexivity.
Qed.
Theorem BHsemantics : forall sd clock run old,run<256 ->
 simulation.RuleSem(HCspec clock run)sd V293_witness_li SCinv(BHreturn run)Afalse
  (BHentry old clock run)BHbody Afalse WhileReady.
Proof. intros;apply RuleSound;apply BHrules;assumption. Qed.

(* A separate return-witness ablation; no initialization failure is reused. *)
Theorem BHwrong_return : forall run v s,~s |= BHreturn run(Some v).
Proof.
 intros run v s H;change(s |= Afalse);eapply V293_tick_body_return_not_value;exact H.
Qed.
Theorem BHmissing_hook_still_blocked : forall ks m ir au,
 ~exists C' state',loststep CCprogram(curs(sfexec 2002%Z[][]),(kenil,ks))(m,ir,au)C' state'.
Proof. apply HCmissing_no_step. Qed.

(* The actual first assignment, from the SAME allocated Mi to one Ms. *)
Theorem BHinitialize_execution : forall ks clock run,run<256 ->exists Ms,
 V293_local_steps CCprogram(curs BHbody,(kenil,kcall 2001%Z BHbody emp ks))
  ((PCge,CCle,BHmemory clock run),(fun _=>false),(false,[1],[false]))
  (curs(scall 2002%Z[]),(kenil,
   kseq(V293_tick_post_hook 901%Z 902%Z 903%Z 1001%Z 1002%Z 1003%Z)
    (kseq sret(kcall 2001%Z BHbody emp ks))))
  ((PCge,CCle,Ms),(fun _=>false),(false,[1],[false])) /\
 CCstate Ms(PCabs clock)(PCcode run) |= BHentry(Vint32 Int.zero)clock run /\
 load Tint32 Ms(172%positive,0%Z)=Some(Vint32 Int.zero) /\
 ~CCstate Ms(PCabs clock)(PCcode run) |= BHentry Vundef clock run /\
 load Tint32 Ms(90%positive,0%Z)=Some(Vint32(Int.repr 99)) /\
 load(Tptr V293_tcb_type)Ms(70%positive,0%Z)=Some(Vptr WhileIdle).
Proof.
 intros ks clock run Range;pose proof(BHallocated_entry clock run Range)as Entry.
 assert(Raw:CCstate(BHmemory clock run)(PCabs clock)(PCcode run) |=
  Amapsto(172%positive,0%Z)Tint32 true Vundef **
   (BHbind ** (<||PCcode run||> ** OS[(fun _=>false),false,[1],[false]] **
    (Amapsto(171%positive,0%Z)(Tptr V293_tcb_type)true Vundef ** CCshared clock run)))).
 { unfold BHentry,V293_tick_body_entry,V293_time_cell,BHbind,CCshared,CCframe in *;
   clear -Entry;sep auto. }
 destruct(V293_tick_raw_slot_update (172%positive,0%Z) Tint32 Vundef (Vint32 Int.zero)_ _ _ _ _ _ _ _ eq_refl Raw)
  as(Ms&Store&Owned).
 assert(New:CCstate Ms(PCabs clock)(PCcode run) |= BHentry(Vint32 Int.zero)clock run).
 { unfold BHentry,V293_tick_body_entry,V293_time_cell,V293_owned_record_cell,BHbind,
    CCshared,CCframe in *;clear -Owned;sep auto. }
 assert(Saved:load Tint32 Ms(172%positive,0%Z)=Some(Vint32 Int.zero)).
 { eapply BHentry_load;[right;eexists;reflexivity|exact New]. }
 assert(Cells:CCstate Ms(PCabs clock)(PCcode run) |= V293_owned_record_cells WhileFrameCells ** Atrue).
 { unfold BHentry,V293_tick_body_entry,V293_tick_call_shared,CCrest in New;clear -New;sep auto. }
 assert(Canary:load Tint32 Ms(90%positive,0%Z)=Some(Vint32(Int.repr 99))).
 { change(load Tint32(getmem(CCstate Ms(PCabs clock)(PCcode run)))(90%positive,0%Z)=Some(Vint32(Int.repr 99))).
   eapply V293_record_star_load_l;[ |exact Cells].
   intros st H;eapply V293_owned_record_cells_load with(cells:=WhileFrameCells);
    [unfold WhileFrameCells;left;reflexivity|exact H]. }
 assert(Slot:CCstate Ms(PCabs clock)(PCcode run) |= V293_owned_record_cell(V293_tick_pointer_cell 70%positive WhileIdle) ** Atrue).
 { unfold BHentry,V293_tick_body_entry,V293_tick_call_shared,CCrest in New;clear -New;sep auto. }
 assert(Old:load(Tptr V293_tcb_type)Ms(70%positive,0%Z)=Some(Vptr WhileIdle)).
 { change(load(Tptr V293_tcb_type)(getmem(CCstate Ms(PCabs clock)(PCcode run)))(70%positive,0%Z)=Some(Vptr WhileIdle)).
   eapply V293_record_star_load_l;[apply V293_owned_record_cell_load|exact Slot]. }
 exists Ms;split.
 - unfold BHbody.
   eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sseq_step]| ].
   unfold V293_tick_body.
   eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sseq_step]| ].
   eapply V293_local_trans.
   { apply V293_csteps_local;eapply V293_success_assign_zero;[vm_compute;reflexivity|exact Store]. }
   eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sskip_step]| ].
   eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sseq_step]| ].
   apply V293_local_refl.
 - split;[exact New| ];split;[exact Saved| ];split.
   + intro Bad;pose proof(BHentry_load _ _ _ _ _ _ (or_introl eq_refl)Bad)as Wrong.
     rewrite Saved in Wrong;discriminate.
   + split;assumption.
Qed.

(* Full return post is nonempty in the stopped case, independently of body
   execution. It changes only the ghost END, exactly as the prior fixture. *)
Theorem BHstopped_return_fixture : forall ks clock run,run<256 ->run<>1 ->exists Ms,
 CCexecution ks clock run Ms /\
 CCstate Ms(PCabs clock)(END None) |= BHreturn run None /\
 ~CCstate Ms(PCabs clock)(END None) |= BHreturn run(Some(Vint32 Int.zero)).
Proof.
 intros ks clock run Range Stopped.
 destruct(TRstopped_result_fixture ks clock run Range Stopped)as(Ms&Prefix&Post).
 assert(Bind:CCstate emp emp(END None) |= CCbindings ** BHbind).
 { pose proof CCbindings_spatial as B;apply BHadd_binding in B;clear -B;sep auto. }
 assert(Both:CCstate Ms(PCabs clock)(END None) |= (CCbindings ** BHbind) ** TRpost run).
 { apply sat_split';exists(empmem:mem);exists Ms;exists(emp:osabst);exists(PCabs clock).
   split;[apply map_join_comm;apply map_join_emp| ];split;[apply map_join_comm;apply map_join_emp| ];
   split;assumption. }
 assert(Full:CCstate Ms(PCabs clock)(END None) |= BHreturn run None).
 { unfold BHreturn,V293_tick_body_return,TRpost,V293_tick_scan_switch_result in *.
   assert(Nat.eqb run 1=false)as Off by(apply Nat.eqb_neq;exact Stopped).
   rewrite Off in *;unfold V293_tick_scan_supplement,V293_tick_saved_frame in *;
   clear -Both;sep auto. }
 exists Ms;split;[exact Prefix| ];split;[exact Full|apply BHwrong_return].
Qed.
Theorem BHreturn_releases_locals : forall ks caller M O run,
 CCstate M O(END None) |= BHreturn run None ->exists Mf,
 V293_local_steps CCprogram(curs(sskip None),(kenil,kseq sret(kcall 2001%Z BHbody caller ks)))
 ((PCge,CCle,M),(fun _=>false),(false,[1],[false]))
 (curs(sskip None),(kenil,ks))((PCge,caller,Mf),(fun _=>false),(false,[1],[false])) /\
 (PCge,caller,Mf,(fun _=>false),(false,[1],[false]),O,END None) |= TRreturned run /\
 (forall k,k<4 ->get Mf(171%positive,Z.of_nat k)=None /\ get Mf(172%positive,Z.of_nat k)=None).
Proof.
 intros ks caller M O run Post.
 eapply V293_tick_body_return_to_caller;[discriminate|exact TRrest_good|exact TRbindings_empty|exact Post].
Qed.

(* Prefix and first-assignment traces really compose; the hook is not run. *)
Theorem BHsame_initialization_controls : forall ks clock run,run<256 ->exists Ms,
 BHprefix ks clock run(BHmemory clock run) /\
 CCstate(BHmemory clock run)(PCabs clock)(PCcode run) |= BHentry Vundef clock run /\
 ~CCstate(BHmemory clock run)(PCabs clock)(PCcode run) |= BHentry(Vint32 Int.zero)clock run /\
 CCexecution ks clock run Ms /\
 CCstate Ms(PCabs clock)(PCcode run) |= BHentry(Vint32 Int.zero)clock run /\
 ~CCstate Ms(PCabs clock)(PCcode run) |= BHentry Vundef clock run /\
 load Tint32 Ms(90%positive,0%Z)=Some(Vint32(Int.repr 99)) /\
 load(Tptr V293_tcb_type)Ms(70%positive,0%Z)=Some(Vptr WhileIdle).
Proof.
 intros ks clock run Range.
 pose proof(BHallocated_entry clock run Range)as Entry.
 destruct(BHinitialize_execution ks clock run Range)as(Ms&Exec&New&Saved&Bad&Canary&Old).
 exists Ms;split;[apply BHallocated_prefix| ];split;[exact Entry| ];split.
 - intro Wrong.
   pose proof(BHentry_load _ _ _ _ _ _ (or_introl eq_refl)Entry)as Before.
   pose proof(BHentry_load _ _ _ _ _ _ (or_intror(ex_intro _ Int.zero eq_refl))Wrong)as Read.
   rewrite Before in Read;discriminate.
 - split.
   + eapply V293_local_trans;[exact(BHallocated_prefix ks clock run)|exact Exec].
   + split;[exact New| ];split;[exact Bad| ];split;assumption.
Qed.
