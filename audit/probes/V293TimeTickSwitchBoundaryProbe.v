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


Definition SCinv:=V293_time_ready_inv 93%positive 92%positive 94%positive 96%positive.
Definition SCsupp run:=V293_tick_switch_supplement WhileBindings WhileIdle
  70%positive 98%positive 99%positive run PCframe WhileIdle.
Definition SCcore clock run:=V293_tick_switch_pre WhileBindings WhileIdle Vnull WhileReady ChainEvents
  93%positive 92%positive 94%positive 96%positive 70%positive 98%positive 99%positive run PCframe clock WhileIdle.
Definition SCpre clock run:=<||PCcode run||> ** OS[(fun _=>false),false,[1],[false]] ** SCcore clock run.
Definition SCpost run:=V293_tick_switch_result WhileBindings WhileIdle
  93%positive 92%positive 94%positive 96%positive 70%positive 98%positive 99%positive run PCframe WhileIdle
  (fun _=>false)[1][false].
Definition SCtime clock:=
  ((CurTid WhileReady ** V293_shared_fields WhileReady WhileOldTasks ChainEvents clock) **
   V293_ready_payload 93%positive 92%positive 94%positive WhileOldTasks) **
  PV(96%positive,Int.zero)@Tint32|->Vint32 clock.
Lemma SCflags : forall M O op p,
  PCstate false M O op |= p -> PCstate false M O op |= V293_shared_flags ** p.
Proof.
 intros M O op p Held.
 apply astar_l_atopis_intro with(i:=1)in Held;[ |reflexivity].
 apply astar_l_aie_intro with(i:=false)in Held;[ |reflexivity].
 apply astar_l_aisr_intro with(i:=fun _=>false)in Held;[ |reflexivity].
 assert(Clr:Aisr(fun _=>false) ==> isrclr).
 { intros st H;unfold isrclr;exists(fun _:hid=>false);split;[exact H| ].
   destruct st as[[[[[[g l]m]r]a]o]p0];cbn in *;tauto. }
 eapply astar_mono in Held;[ |exact Clr|intros st H;exact H].
 unfold V293_shared_flags;clear -Held;sep auto.
Qed.
Lemma SCclose_view : forall clock,
  V293_shared_flags ** SCtime clock ==>
  V293_tick_switch_view 93%positive 92%positive 94%positive 96%positive
    WhileReady WhileOldTasks ChainEvents clock.
Proof.
 intros clock s Held;split.
 - apply V293_time_ready_switch_close.
   unfold SCtime,V293_time_ready_switch_core,V293_time_ready_switch_fields in *;clear -Held;sep auto.
 - unfold SCtime in Held;clear -Held;sep auto.
Qed.
Lemma SCfrom_core : forall clock run M O op,
 PCstate false M O op |= PCcore clock run ->
 PCstate false M O op |= SCcore clock run.
Proof.
 intros clock run M O op Packed.
 apply SCflags in Packed.
 assert(Parts:PCstate false M O op |= (V293_shared_flags ** SCtime clock) ** SCsupp run).
 { unfold PCcore,V293_tick_post_hook_core_pre,V293_tick_post_hook_core_state,
     V293_tick_post_hook_core_frame,SCtime,SCsupp,V293_tick_switch_supplement,PCglobals in *.
   clear -Packed;sep auto. }
 unfold SCcore,V293_tick_switch_pre.
 eapply astar_mono;[apply SCclose_view|intros st H;exact H|exact Parts].
Qed.
Lemma SCpack : forall clock run M O op,
 PCstate false M O op |= PCphysical clock run ** V293_shared_fields WhileReady WhileOldTasks ChainEvents clock ->
 PCstate false M O op |= SCcore clock run.
Proof. intros;apply SCfrom_core;apply PCpack;assumption. Qed.
Theorem SCgood : GoodI SCinv V293_scheduler V293_shared_li.
Proof. apply V293_time_ready_good. Qed.
Theorem SCentry : forall clock run,run<256 ->
 PCstate false(PCmemory clock run)(PCabs clock)(PCcode run) |= SCpre clock run.
Proof.
 intros clock run Range.
 pose proof(SCpack clock run _ _ _(PCjoint clock run false(PCcode run)Range))as Entry.
 assert(Control:PCstate false(PCmemory clock run)(PCabs clock)(PCcode run) |=
   Aisr(fun _=>false) ** (Aie false ** (Ais(1::nil) ** (Acs(false::nil) ** SCcore clock run)))).
 { apply astar_l_aisr_intro;[ |reflexivity]. apply astar_l_aie_intro;[ |reflexivity].
   apply astar_l_ais_intro;[ |reflexivity]. apply astar_l_acs_intro;[exact Entry|reflexivity]. }
 unfold SCpre;apply astar_l_aop'_intro;[ |reflexivity]. clear -Control;sep auto.
Qed.
Theorem SCrules : forall Spec sd r ri clock run,run<256 ->
 InfRules Spec sd V293_witness_li SCinv r ri(SCpre clock run)
  (V293_tick_post_hook 901%Z 902%Z 903%Z 1001%Z 1002%Z 1003%Z)(SCpost run)WhileReady.
Proof.
 intros;apply V293_tick_post_hook_switch_hoare.
 - exact RUnoabs.
 - change(368+50<=4294967295)%Z;lia.
 - exact WhileBindingsValid.
 - exact WhileKeysUnique.
 - assumption.
 - exact PCenv.
 - exact PCcur.
 - exact PCframe_good.
 - exact PCframe_change.
 - change(1<=INUM)%nat;unfold INUM;lia.
 - reflexivity.
Qed.
Theorem SCrunning : forall Spec sd r ri clock,
 InfRules Spec sd V293_witness_li SCinv r ri(SCpre clock 1)
  (V293_tick_post_hook 901%Z 902%Z 903%Z 1001%Z 1002%Z 1003%Z)(SCpost 1)WhileReady.
Proof. intros;apply SCrules;lia. Qed.
Theorem SCstopped : forall Spec sd r ri clock run,run=0 \/ run=255 ->
 InfRules Spec sd V293_witness_li SCinv r ri(SCpre clock run)
  (V293_tick_post_hook 901%Z 902%Z 903%Z 1001%Z 1002%Z 1003%Z)(SCpost run)WhileReady.
Proof. intros;apply SCrules;lia. Qed.
Theorem SCsemantics : forall Spec sd r ri clock run,run<256 ->
 simulation.RuleSem Spec sd V293_witness_li SCinv r ri(SCpre clock run)
  (V293_tick_post_hook 901%Z 902%Z 903%Z 1001%Z 1002%Z 1003%Z)(SCpost run)WhileReady.
Proof. intros;apply RuleSound;apply SCrules;assumption. Qed.

(* Only the observed view changes. Inv, physical bytes, real abstract map and
   supplemental ownership are IDENTICAL to SCentry, including ready bitmap. *)
Definition SCcandidate clock tasks run:=
 (SWINV SCinv //\\ (V293_shared_fields WhileReady tasks ChainEvents clock ** Atrue)) ** SCsupp run.
Lemma SCcandidate_slots : forall s clock tasks run,
 s |= SCcandidate clock tasks run ->
 get(getabst s)ostmid=Some(ostm clock) /\
 get(getabst s)abstcblsid=Some(abstcblist tasks).
Proof.
 intros s clock tasks run Held;split;
 (eapply V293_star_abst_get_l;[ |exact Held]);intros st [_ View];
 (eapply V293_star_abst_get_l;[ |exact View]);intros st0 H;
 destruct(V293_shared_fields_get _ _ _ _ st0 H)as[C[T[E N]]];assumption.
Qed.
Theorem SCwrong_clock : forall run,
 ~ PCstate false(PCmemory(Int.repr 37)run)(PCabs(Int.repr 37))(PCcode run) |=
    SCcandidate(Int.repr 38)WhileOldTasks run.
Proof.
 intros run Wrong;pose proof(proj1(SCcandidate_slots _ _ _ _ Wrong))as Fixed.
 change(Some(ostm(Int.repr 37))=Some(ostm(Int.repr 38)))in Fixed.
 inversion Fixed as[E];vm_compute in E;discriminate.
Qed.
Theorem SCwrong_tasks : forall run,
 ~ PCstate false(PCmemory(Int.repr 37)run)(PCabs(Int.repr 37))(PCcode run) |=
    SCcandidate(Int.repr 37)(emp:TcbMod.map)run.
Proof.
 intros run Wrong;pose proof(proj2(SCcandidate_slots _ _ _ _ Wrong))as Fixed.
 change(Some(abstcblist WhileOldTasks)=Some(abstcblist(emp:TcbMod.map)))in Fixed.
 inversion Fixed as[E].
Qed.
Theorem SCview_nonvacuous : forall run,run<256 ->
 PCstate false(PCmemory(Int.repr 37)run)(PCabs(Int.repr 37))(PCcode run) |=
   SCcandidate(Int.repr 37)WhileOldTasks run.
Proof.
 intros run Range.
 exact(SCpack _ _ _ _ _(PCjoint(Int.repr 37)run false(PCcode run)Range)).
Qed.

(* Independently executed ORIGINAL post-hook. This is not execution of RuleSem. *)
Theorem SCexecution : forall P ks clock run,run<256 ->
 PCstate false(PCmemory clock run)(PCabs clock)(PCcode run) |= SCpre clock run /\
 exists Mf, PCexecution P ks clock run false Mf /\
 load Tint32 Mf(96%positive,0%Z)=Some(Vint32(Int.add clock Int.one)) /\
 (forall a tp v,In(a,tp,v)(PCexpectedcells run) ->load tp Mf a=Some v) /\
 load Tint32 Mf(90%positive,0%Z)=Some(Vint32(Int.repr 99)) /\ PCreturned clock run false Mf.
Proof. intros;split;[apply SCentry;assumption|apply PCliteral_execution;assumption]. Qed.
Theorem SCwrap_entry : forall run,run=0 \/ run=1 \/ run=255 ->
 PCstate false(PCmemory(Int.repr Int.max_unsigned)run)(PCabs(Int.repr Int.max_unsigned))(PCcode run) |=
   SCpre(Int.repr Int.max_unsigned)run.
Proof. intros;apply SCentry;lia. Qed.
(* Existing same-Mf clock neutralization and separate-named task control are
   explicitly reused; neither is relabeled as a new semantic-rule run. *)
Theorem SCclock_control : forall P ks sd clock run,
 (clock=Int.repr 37 \/ clock=Int.repr Int.max_unsigned) ->
 (run=0 \/ run=255) -> exists Mf,
 PCexecution P ks clock run false Mf /\
 spec_stepstar sd(PCcode run)(PCabs clock)(END None)
   (set(PCabs clock)ostmid(ostm(Int.add clock Int.one))) /\
 load Tint32 Mf(96%positive,0%Z)=Some(Vint32(Int.add clock Int.one)) /\
 load Tint32 Mf(90%positive,0%Z)=Some(Vint32(Int.repr 99)) /\
 PCstate false Mf(set(PCabs clock)ostmid(ostm(Int.add clock Int.one)))(PCcode run) |=
   SCcore(Int.add clock Int.one)run /\
 ~ PCstate false Mf(PCabs clock)(PCcode run) |= SWINV SCinv ** Atrue.
Proof.
 intros P ks sd clock run Cases Stop.
 destruct(PCclock_neutralized P ks sd clock run false Cases Stop)
   as(Mf&Exec&Steps&Clock&Canary&Core&Reject).
 exists Mf;split;[exact Exec| ];split;[exact Steps| ];split;[exact Clock| ];
 split;[exact Canary| ];split;[apply SCfrom_core;exact Core| ].
 intro Wrong;apply Reject.
 assert(Opened:PCstate false Mf(PCabs clock)(PCcode run) |=
   (V293_shared_flags ** V293_time_ready_switch_core 93%positive 92%positive 94%positive 96%positive) ** Atrue).
 { eapply astar_mono;[apply V293_time_ready_switch_open|intros st H;exact H|exact Wrong]. }
 assert(Just:PCstate false Mf(PCabs clock)(PCcode run) |=
   V293_time_ready_switch_core 93%positive 92%positive 94%positive 96%positive ** Atrue)
   by(clear -Opened;sep auto).
 eapply astar_mono;[ |intros st H;exact H|exact Just].
 intros st H;apply V293_time_ready_switch_core_equiv;exact H.
Qed.
Definition SCtask_control:=fun P ks sd=>PCexecution_control P ks sd false.
Definition SCwrap_control:=fun P ks run=>PCwrapped_execution P ks run false.
