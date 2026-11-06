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



Definition SSrest clock run:=
 ((CurTid WhileReady ** V293_shared_fields WhileReady WhileOldTasks ChainEvents clock) **
 V293_ready_payload 93%positive 92%positive 94%positive WhileOldTasks) **
 (PV(96%positive,Int.zero)@Tint32|->Vint32 clock **
 (V293_owned_record_cells(V293_tick_chain_missing WhileBindings WhileIdle) **
 V293_tick_post_hook_core_frame WhileBindings WhileIdle 98%positive 99%positive run PCframe)).
Definition SScore clock run scan:=V293_tick_scan_pre WhileBindings WhileIdle Vnull WhileReady ChainEvents
 93%positive 92%positive 94%positive 96%positive 70%positive 98%positive 99%positive run PCframe clock scan.
Definition SSswitch clock run scan:=V293_tick_scan_switch_pre WhileBindings WhileIdle Vnull WhileReady ChainEvents
 93%positive 92%positive 94%positive 96%positive 70%positive 98%positive 99%positive run PCframe clock scan.
Definition SSpre clock run:=<||PCcode run||> ** OS[(fun _=>false),false,[1],[false]] ** SSswitch clock run Vundef.
Definition SSpost run:=V293_tick_scan_switch_result WhileBindings WhileIdle
 93%positive 92%positive 94%positive 96%positive 70%positive 98%positive 99%positive run PCframe Vundef
 (fun _=>false)[1][false].

(* Construct the exact Vundef encoding by a permission-preserving byte store.
   This is fixture construction, NOT a source statement or hook implementation. *)
Lemma SSreplace : forall M O op old R,
 PCstate false M O op |= Amapsto(70%positive,0%Z)(Tptr V293_tcb_type)true old ** R ->
 exists M',store(Tptr V293_tcb_type)M(70%positive,0%Z)Vundef=Some M' /\
 PCstate false M' O op |= Amapsto(70%positive,0%Z)(Tptr V293_tcb_type)true Vundef ** R.
Proof.
 intros M O op old R Held;apply sat_split in Held.
 destruct Held as(m1&m2&o1&o2&JM&JO&[Mapsto Empty]&Rest).
 destruct(store_exist_join' (70%positive,0%Z)(Tptr V293_tcb_type)old Vundef m1 m2 M Mapsto JM)as[M' Store].
 destruct(store_mapstoval_frame1 _ _ _ _ _ _ _ _ Mapsto JM Store)as(m1'&Mapsto'&Local&Join).
 exists M';split;[exact Store| ].
 apply sat_split';exists m1';exists m2;exists o1;exists o2.
 split;[exact Join| ];split;[exact JO| ];split;[split;assumption|exact Rest].
Qed.
Lemma SSpack : forall clock run scan,
 Amapsto(70%positive,0%Z)(Tptr V293_tcb_type)true scan ** SSrest clock run ==> SScore clock run scan.
Proof. intros clock run scan s Held;unfold SScore,V293_tick_scan_pre,V293_tick_scan_state,SSrest,WhileOldTasks in *;clear -Held;sep auto. Qed.
Lemma SSclose : forall clock run scan M O op,
 PCstate false M O op |= SScore clock run scan -> PCstate false M O op |= SSswitch clock run scan.
Proof.
 intros clock run scan M O op Held;apply SCflags in Held.
 assert(Parts:PCstate false M O op |= (V293_shared_flags ** SCtime clock) **
  V293_tick_scan_supplement WhileBindings WhileIdle 70%positive 98%positive 99%positive run PCframe scan).
 { unfold SScore,V293_tick_scan_pre,V293_tick_scan_state,SCtime,V293_tick_scan_supplement in *;clear -Held;sep auto. }
 unfold SSswitch,V293_tick_scan_switch_pre.
 eapply astar_mono;[apply SCclose_view|intros s H;exact H|exact Parts].
Qed.
Lemma SSload : forall clock run scan M O op,
 (scan=Vundef \/ exists a,scan=Vptr a) ->
 PCstate false M O op |= SScore clock run scan ->
 load(Tptr V293_tcb_type)M(70%positive,0%Z)=Some scan.
Proof.
 intros clock run scan M O op Values Held.
 assert(Slot:PCstate false M O op |= Amapsto(70%positive,0%Z)(Tptr V293_tcb_type)true scan ** Atrue).
 { unfold SScore,V293_tick_scan_pre,V293_tick_scan_state in Held;clear -Held;sep auto. }
 change(load(Tptr V293_tcb_type)(getmem(PCstate false M O op))(70%positive,0%Z)=Some scan).
 eapply V293_record_star_load_l;[ |exact Slot].
 intros st H;apply V293_tick_raw_pointer_load;assumption.
Qed.
Theorem SSentry : forall clock run,run<256 ->exists M,
 store(Tptr V293_tcb_type)(PCmemory clock run)(70%positive,0%Z)Vundef=Some M /\
 PCstate false M(PCabs clock)(PCcode run) |= SSpre clock run /\
 PCstate false M(PCabs clock)(PCcode run) |= SScore clock run Vundef /\
 load(Tptr V293_tcb_type)M(70%positive,0%Z)=Some Vundef.
Proof.
 intros clock run Range.
 pose proof(PCpack clock run false _ _ _(PCjoint clock run false(PCcode run)Range))as Packed.
 assert(Raw:PCstate false(PCmemory clock run)(PCabs clock)(PCcode run) |=
  Amapsto(70%positive,0%Z)(Tptr V293_tcb_type)true(Vptr WhileIdle) ** SSrest clock run).
 { unfold PCcore,V293_tick_post_hook_core_pre,V293_tick_post_hook_core_state,SSrest,V293_owned_record_cell,V293_tick_pointer_cell in *;clear -Packed;sep auto. }
 destruct(SSreplace _ _ _ _ _ Raw)as(M&Store&Held).
 apply SSpack in Held;pose proof Held as Core;apply SSclose in Held.
 exists M;split;[exact Store| ];split.
 - unfold SSpre;apply astar_l_aop'_intro;[ |reflexivity].
   unfold PCstate;apply astar_l_aisr_intro with(i:=fun _=>false)in Held;[ |reflexivity].
   apply astar_l_aie_intro with(i:=false)in Held;[ |reflexivity].
   apply astar_l_ais_intro with(i:=[1])in Held;[ |reflexivity].
   apply astar_l_acs_intro with(i:=[false])in Held;[ |reflexivity]. clear -Held;sep auto.
 - split;[exact Core|eapply SSload;[left;reflexivity|exact Core]].
Qed.
Theorem SSrules : forall Spec sd r ri clock run,run<256 ->
 InfRules Spec sd V293_witness_li SCinv r ri(SSpre clock run)
 (V293_tick_post_hook 901%Z 902%Z 903%Z 1001%Z 1002%Z 1003%Z)(SSpost run)WhileReady.
Proof.
 intros;apply V293_tick_scan_switch_hoare.
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
Theorem SSrunning : forall Spec sd r ri clock,
 InfRules Spec sd V293_witness_li SCinv r ri(SSpre clock 1)
 (V293_tick_post_hook 901%Z 902%Z 903%Z 1001%Z 1002%Z 1003%Z)(SSpost 1)WhileReady.
Proof. intros;apply SSrules;lia. Qed.
Theorem SSstopped : forall Spec sd r ri clock run,run=0 \/ run=255 ->
 InfRules Spec sd V293_witness_li SCinv r ri(SSpre clock run)
 (V293_tick_post_hook 901%Z 902%Z 903%Z 1001%Z 1002%Z 1003%Z)(SSpost run)WhileReady.
Proof. intros;apply SSrules;lia. Qed.
Theorem SSsemantics : forall Spec sd r ri clock run,run<256 ->
 simulation.RuleSem Spec sd V293_witness_li SCinv r ri(SSpre clock run)
 (V293_tick_post_hook 901%Z 902%Z 903%Z 1001%Z 1002%Z 1003%Z)(SSpost run)WhileReady.
Proof. intros;apply RuleSound;apply SSrules;assumption. Qed.
Theorem SSwrong_pointer : forall clock run M,
 load(Tptr V293_tcb_type)M(70%positive,0%Z)=Some Vundef ->
 ~ PCstate false M(PCabs clock)(PCcode run) |= SSswitch clock run(Vptr WhileIdle).
Proof.
 intros clock run M Actual Wrong.
 assert(Slot:PCstate false M(PCabs clock)(PCcode run) |=
 Amapsto(70%positive,0%Z)(Tptr V293_tcb_type)true(Vptr WhileIdle) ** Atrue).
 { unfold SSswitch,V293_tick_scan_switch_pre,V293_tick_scan_supplement in Wrong;clear -Wrong;sep auto. }
 assert(Other:load(Tptr V293_tcb_type)M(70%positive,0%Z)=Some(Vptr WhileIdle)).
 { change(load(Tptr V293_tcb_type)(getmem(PCstate false M(PCabs clock)(PCcode run)))(70%positive,0%Z)=Some(Vptr WhileIdle)).
   eapply V293_record_star_load_l;[ |exact Slot].
   intros st H;apply V293_tick_raw_pointer_load;[right;exists WhileIdle;reflexivity|exact H]. }
 congruence.
Qed.
Theorem SSundef_not_typed : forall st,
 ~ st |= V293_owned_record_cell((70%positive,0%Z),Tptr V293_tcb_type,Vundef).
Proof.
 intros st Held;unfold V293_owned_record_cell in Held;apply astar_l_apure_elim in Held.
 destruct Held as[False _];discriminate.
Qed.

Definition SSowned clock run scan:=
 V293_tick_storage_owned 96%positive clock 98%positive run 99%positive WhileHead
  70%positive scan(map fst WhileBindings)WhileIdle 92%positive 93%positive 3 16 16(PCresidual clock).
Definition SSowned_rest clock run:=
 V293_owned_record_cell((96%positive,0%Z),Tint32,Vint32 clock) **
 (V293_owned_record_cell((98%positive,0%Z),Tint8,V293_byteval run) **
 (V293_owned_record_cell((99%positive,0%Z),Tptr V293_tcb_type,Vptr WhileHead) **
 (V293_owned_record_cells(V293_tick_chain_cells(map fst WhileBindings)WhileIdle) **
 (V293_owned_record_cells(V293_tick_bitmap_cells 92%positive 93%positive 3 16 16) **
 (V293_owned_record_cell(V293_tick_idle_cell WhileIdle) ** PCresidual clock))))).
Lemma SSowned_entry : forall clock run M,
 store(Tptr V293_tcb_type)(PCmemory clock run)(70%positive,0%Z)Vundef=Some M ->
 run<256 -> PCstate false M(PCabs clock)(PCcode run) |= SSowned clock run Vundef.
Proof.
 intros clock run M Store Range.
 pose proof(PCowned_entry clock run false Range)as Original.
 assert(Raw:PCstate false(PCmemory clock run)(PCabs clock)(PCcode run) |=
 Amapsto(70%positive,0%Z)(Tptr V293_tcb_type)true(Vptr WhileIdle) ** SSowned_rest clock run).
 { unfold V293_tick_suffix_owned,V293_tick_loop_owned,SSowned_rest,V293_owned_record_cell,V293_tick_pointer_cell in *;clear -Original;sep auto. }
 destruct(SSreplace _ _ _ _ _ Raw)as(M'&Store'&Replaced).
 assert(M'=M)by congruence;subst M'.
 unfold SSowned,V293_tick_storage_owned,SSowned_rest in *;clear -Replaced;sep auto.
Qed.
Definition SSactual P ks M Mf:=V293_local_steps P
 (curs(V293_tick_post_hook 901%Z 902%Z 903%Z 1001%Z 1002%Z 1003%Z),(kenil,ks))
 ((PCge,TickLocal,M),(fun _=>false),(false,[1],[false]))
 (curs(sskip None),(kenil,ks))((PCge,TickLocal,Mf),(fun _=>false),(false,[1],[false])).
Definition SSexpectedcells run:=
 V293_tick_chain_cells(if Nat.eqb run 1 then map V293_tick_task_after(map fst WhileBindings)else map fst WhileBindings)WhileIdle ++
 (V293_tick_bitmap_cells 92%positive 93%positive 3 16(if Nat.eqb run 1 then 20 else 16)++[V293_tick_idle_cell WhileIdle]).
Definition SSreturned clock run Mf:=PCstate false Mf(PCabs clock)(PCcode run) |=
 V293_tick_storage_owned 96%positive(Int.add clock Int.one)98%positive run 99%positive WhileHead
  70%positive(if Nat.eqb run 1 then Vptr WhileIdle else Vundef)
  (if Nat.eqb run 1 then map V293_tick_task_after(map fst WhileBindings)else map fst WhileBindings)
  WhileIdle 92%positive 93%positive 3 16(if Nat.eqb run 1 then 20 else 16)(PCresidual clock).
(* Same fresh M is both a SWINV entry and the concrete execution input.
   No new main theorem is used to construct or execute this input. *)
Theorem SSexecution : forall P ks clock run,run<256 ->exists M Mf,
 store(Tptr V293_tcb_type)(PCmemory clock run)(70%positive,0%Z)Vundef=Some M /\
 PCstate false M(PCabs clock)(PCcode run) |= SSpre clock run /\
 load(Tptr V293_tcb_type)M(70%positive,0%Z)=Some Vundef /\
 SSactual P ks M Mf /\
 load Tint32 Mf(96%positive,0%Z)=Some(Vint32(Int.add clock Int.one)) /\
 load(Tptr V293_tcb_type)Mf(70%positive,0%Z)=Some(if Nat.eqb run 1 then Vptr WhileIdle else Vundef) /\
 (forall a tp v,In(a,tp,v)(SSexpectedcells run) ->load tp Mf a=Some v) /\
 load Tint32 Mf(90%positive,0%Z)=Some(Vint32(Int.repr 99)) /\ SSreturned clock run Mf.
Proof.
 intros P ks clock run Range.
 destruct(SSentry clock run Range)as(M&Store&Pre&Core&Initial).
 destruct(V293_tick_uninitialized_suffix_execution(map fst WhileBindings)P ks PCge TickLocal M
  (fun _=>false)false [1][false](PCabs clock)(PCcode run)901%Z 902%Z 903%Z 1001%Z 1002%Z 1003%Z
  70%positive 96%positive 98%positive 99%positive WhileIdle 92%positive 93%positive clock run 3 16 16(PCresidual clock)
  ltac:(apply map_get_sig)ltac:(vm_compute;reflexivity)ltac:(vm_compute;reflexivity)
  ltac:(vm_compute;reflexivity)ltac:(vm_compute;reflexivity)
  ltac:(vm_compute;reflexivity)ltac:(vm_compute;reflexivity)
  ltac:(vm_compute;reflexivity)ltac:(vm_compute;reflexivity)
  ltac:(vm_compute;reflexivity)ltac:(vm_compute;reflexivity)
  ltac:(change(368+50<=4294967295)%Z;lia)
  ltac:(rewrite Forall_map;eapply Forall_impl;[ |exact WhileBindingsValid];intros[t[st m]]H;exact(proj1 H))
  Range ltac:(lia)ltac:(lia)ltac:(lia)(SSowned_entry clock run M Store Range))as(Mf&Exec&Clock&Pointer&Returned).
 assert(Return:SSreturned clock run Mf).
 { unfold SSreturned;destruct(Nat.eqb run 1);exact Returned. }
 assert(Fields:forall a tp v,In(a,tp,v)(SSexpectedcells run) ->load tp Mf a=Some v).
 { intros a tp v Member;unfold SSreturned,V293_tick_storage_owned in Return.
   change(load tp(getmem(PCstate false Mf(PCabs clock)(PCcode run)))a=Some v).
   eapply V293_record_star_load_r;[ |exact Return]. do 3 eapply V293_record_star_load_r.
   intros st Held;unfold SSexpectedcells in Member.
   apply in_app_iff in Member;destruct Member as[Node|Member].
   - eapply V293_record_star_load_l;[apply V293_owned_record_cells_load;exact Node|exact Held].
   - apply in_app_iff in Member;destruct Member as[Bitmap|Member].
     + eapply V293_record_star_load_r;[ |exact Held].
       eapply V293_record_star_load_l;apply V293_owned_record_cells_load;exact Bitmap.
     + destruct Member as[Same|Empty];[ |contradiction];inversion Same;subst.
       eapply V293_record_star_load_r;[ |exact Held]. eapply V293_record_star_load_r.
       eapply V293_record_star_load_l;apply V293_owned_record_cell_load. }
 assert(Canary:load Tint32 Mf(90%positive,0%Z)=Some(Vint32(Int.repr 99))).
 { assert(Held:PCstate false Mf(PCabs clock)(PCcode run) |= V293_owned_record_cells WhileFrameCells ** Atrue).
   { unfold SSreturned,V293_tick_storage_owned,PCresidual,PCframe in Return.
     clear -Return;sep auto. }
   eapply V293_record_star_load_l with(s:=PCstate false Mf(PCabs clock)(PCcode run));[ |exact Held].
   apply V293_owned_record_cells_load;left;reflexivity. }
 exists M;exists Mf;split;[exact Store| ];split;[exact Pre| ];split;[exact Initial| ];split;[exact Exec| ];
 split;[exact Clock| ];split;[exact Pointer| ];split;[exact Fields| ];split;assumption.
Qed.
Theorem SSwrap : forall P ks run,(run=0 \/ run=1 \/ run=255) ->exists M Mf,
 PCstate false M(PCabs(Int.repr Int.max_unsigned))(PCcode run) |= SSpre(Int.repr Int.max_unsigned)run /\
 SSactual P ks M Mf /\
 load Tint32 Mf(96%positive,0%Z)=Some(Vint32 Int.zero) /\
 load(Tptr V293_tcb_type)Mf(70%positive,0%Z)=Some(if Nat.eqb run 1 then Vptr WhileIdle else Vundef) /\
 load Tint32 Mf(90%positive,0%Z)=Some(Vint32(Int.repr 99)).
Proof.
 intros P ks run Cases.
 destruct(SSexecution P ks(Int.repr Int.max_unsigned)run ltac:(lia))as(M&Mf&Store&Pre&Initial&Exec&Clock&Pointer&Fields&Canary&Returned).
 assert(Wrap:Int.add(Int.repr Int.max_unsigned)Int.one=Int.zero).
 { change(Int.repr 4294967296=Int.repr 0).
   apply Int.eqm_samerepr;unfold Int.eqm,Int.eqmod;exists 1%Z;reflexivity. }
 exists M;exists Mf;split;[exact Pre| ];split;[exact Exec| ];split;[rewrite <-Wrap;exact Clock| ];split;assumption.
Qed.

Lemma SSstopped_recover : forall clock run Mf,
 (run=0 \/ run=255) -> SSreturned clock run Mf ->
 PCstate false Mf(PCabs clock)(PCcode run) |=
 V293_tick_scan_state WhileBindings WhileIdle Vnull WhileReady ChainEvents
  93%positive 92%positive 94%positive 96%positive 70%positive 98%positive 99%positive run PCframe
  clock(Int.add clock Int.one)Vundef.
Proof.
 intros clock run Mf Stop Returned.
 assert(Flag:Nat.eqb run 1=false)by(apply Nat.eqb_neq;lia).
 unfold SSreturned in Returned;rewrite Flag in Returned.
 set(rest:=(CurTid WhileReady ** V293_shared_fields WhileReady WhileOldTasks ChainEvents clock) **
 (PV(96%positive,Int.zero)@Tint32|->Vint32(Int.add clock Int.one) **
 (Amapsto(70%positive,0%Z)(Tptr V293_tcb_type)true Vundef **
 (V293_owned_record_cells(V293_tick_chain_missing WhileBindings WhileIdle) **
 V293_tick_post_hook_core_frame WhileBindings WhileIdle 98%positive 99%positive run PCframe)))).
 assert(Layout:PCstate false Mf(PCabs clock)(PCcode run) |= COlayouts **
  (V293_owned_record_cells(V293_ready_cells 93%positive 92%positive 94%positive 16 16 RCentries) ** rest)).
 { unfold rest,COlayouts,V293_tick_storage_owned,PCresidual,V293_tick_post_hook_core_frame,
   V293_tick_post_hook_core_globals,PCframe in *.
   cbn [WhileBindings WhileReason V293_tick_wait_node V293_tick_block V293_tick_base
    V293_tick_prio V293_tick_task_pointer V293_tick_chain_cells V293_tick_task_cells V293_tick_head
    V293_tick_pointer_cell V293_tick_bitmap_cells V293_priority_cells RCentries V293_ready_cells
    V293_tick_binding_extra V293_tick_record_extra V293_tick_idle_extra V293_record_layout
    V293_tick_chain_missing V293_tick_node_missing V293_tick_pend_value V293_tick_idle_cell
    V293_owned_record_cells app concat map fst snd tl WhileHead WhileSecond WhileReady WhileIdle WhileFrameCells]in *.
   unfold V293_owned_record_cell in *.
   cbn [V293_tick_idle_cell V293_tick_delay_value V293_tick_stat_value V293_tick_x V293_tick_y
    V293_tick_task_pointer V293_tick_wait_node V293_tick_block V293_tick_base V293_tick_prio]in *.
   replace(Int.unsigned(Int.repr 8))with 8%Z in * by(vm_compute;reflexivity).
   replace(Int.unsigned(Int.repr 128))with 128%Z in * by(vm_compute;reflexivity).
   replace(Int.unsigned(Int.repr 248))with 248%Z in * by(vm_compute;reflexivity).
   replace(Int.unsigned(Int.repr 368))with 368%Z in * by(vm_compute;reflexivity).
   clear -Returned;timeout 15 (sep auto). }
 pose proof(COpack _ _ Layout)as Packed.
 unfold V293_tick_scan_state,V293_ready_payload,V293_ready_owned;sep normal;exists 16;exists 16;exists RCentries.
 unfold rest,WhileOldTasks in *;clear -Packed;sep auto. exact RCold_rel.
Qed.
Lemma SSstopped_synced : forall clock run Mf,
 (run=0 \/ run=255) -> SSreturned clock run Mf ->
 PCstate false Mf(set(PCabs clock)ostmid(ostm(Int.add clock Int.one)))(PCcode run) |=
 SSswitch(Int.add clock Int.one)run Vundef.
Proof.
 intros clock run Mf Stop Returned.
 pose proof(SSstopped_recover clock run Mf Stop Returned)as Recovered.
 set(rest:=((CurTid WhileReady **
  (Aabsdata curtid(oscurt WhileReady) **
  (Aabsdata abstcblsid(abstcblist WhileOldTasks) ** Aabsdata absecblsid(absecblist ChainEvents)))) **
  V293_ready_payload 93%positive 92%positive 94%positive WhileOldTasks) **
  (PV(96%positive,Int.zero)@Tint32|->Vint32(Int.add clock Int.one) **
  (Amapsto(70%positive,0%Z)(Tptr V293_tcb_type)true Vundef **
  (V293_owned_record_cells(V293_tick_chain_missing WhileBindings WhileIdle) **
  V293_tick_post_hook_core_frame WhileBindings WhileIdle 98%positive 99%positive run PCframe)))).
 assert(Slot:PCstate false Mf(PCabs clock)(PCcode run) |= Aabsdata ostmid(ostm clock) ** rest).
 { unfold rest,V293_tick_scan_state,V293_shared_fields,WhileOldTasks in *;clear -Recovered;sep auto. }
 unfold PCstate in Slot.
 apply V293_shared_replace_slot with(new:=ostm(Int.add clock Int.one))in Slot.
 apply SSclose.
 unfold SScore,V293_tick_scan_pre,V293_tick_scan_state,PCstate,rest,V293_shared_fields,WhileOldTasks in *;
 clear -Slot;sep auto.
Qed.
(* Additional same-fresh-Mf clock control: only the abstract clock changes.
   Task-neutralization remains the separately identified predecessor endpoint. *)
Theorem SSclock_neutralized : forall P ks clock run,
 (clock=Int.repr 37 \/ clock=Int.repr Int.max_unsigned) ->(run=0 \/ run=255) ->exists M Mf,
 PCstate false M(PCabs clock)(PCcode run) |= SSpre clock run /\
 SSactual P ks M Mf /\
 PCstate false Mf(set(PCabs clock)ostmid(ostm(Int.add clock Int.one)))(PCcode run) |=
 SSswitch(Int.add clock Int.one)run Vundef /\
 ~ PCstate false Mf(PCabs clock)(PCcode run) |=
 V293_time_ready_core 93%positive 92%positive 94%positive 96%positive ** Atrue.
Proof.
 intros P ks clock run Cases Stop.
 destruct(SSexecution P ks clock run ltac:(lia))as(M&Mf&Store&Pre&Initial&Exec&Clock&Pointer&Fields&Canary&Returned).
 exists M;exists Mf;split;[exact Pre| ];split;[exact Exec| ];split.
 - apply SSstopped_synced;assumption.
 - intro Wrong.
   destruct(V293_time_ready_clock_agreement 93%positive 92%positive 94%positive
     96%positive Atrue _ Wrong)as(n&Abstract&Physical).
   pose proof(proj2(proj2(proj2(V293_shared_fields_get _ _ _ _ _(PCabstract clock)))))as Old.
   change(get(PCabs clock)ostmid=Some(ostm n))in Abstract.
   change(get(PCabs clock)ostmid=Some(ostm clock))in Old.
   rewrite Old in Abstract;inversion Abstract;subst n.
   change(load Tint32 Mf(96%positive,0%Z)=Some(Vint32 clock))in Physical.
   rewrite Clock in Physical;inversion Physical as[Equal].
   destruct Cases as[Case|Case];subst clock;vm_compute in Equal;discriminate Equal.
Qed.
