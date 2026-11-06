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


Definition PCge:env:=set(set(set WCge 1001%Z(96%positive,Tint32))
  1002%Z(98%positive,Tint8))1003%Z(99%positive,Tptr V293_tcb_type).
Definition PCbindings:=DHbindings //\\ A_notin_lenv 1001%Z //\\
  Agvarenv 1001%Z Tint32(96%positive,0%Z) //\\ A_notin_lenv 1002%Z //\\
  Agvarenv 1002%Z Tint8(98%positive,0%Z) //\\ A_notin_lenv 1003%Z //\\
  Agvarenv 1003%Z(Tptr V293_tcb_type)(99%positive,0%Z).
Definition PCframe:=PCbindings **
  (LINV V293_witness_li WhileReady [] ** V293_owned_record_cells WhileFrameCells).
Definition PCglobals run:=V293_tick_post_hook_core_globals WhileBindings WhileIdle 98%positive 99%positive run.
Definition PCcells clock run:=
  V293_record_layout WhileHead 10(wait WhileReason(Int.repr 1))Vnull 7 ++
  V293_record_layout WhileSecond 2(wait os_stat_time(Int.repr 3))Vnull 7 ++
  V293_record_layout WhileReady 4 rdy Vnull 7 ++
  V293_record_layout WhileIdle 12 rdy Vnull 7 ++
  V293_ready_cells 93%positive 92%positive 94%positive 16 16 RCentries ++
  [V293_tick_pointer_cell 70%positive WhileIdle] ++
  V293_tick_chain_missing WhileBindings WhileIdle ++
  [((96%positive,0%Z),Tint32,Vint32 clock)] ++ PCglobals run ++ WhileFrameCells.
Definition PCmemory clock run:=merge(OwnershipCellsMemory(PCcells clock run))WCcurrent.
Definition PCabs clock:=V293_shared_fixture_abs WhileReady WhileOldTasks ChainEvents clock.
Definition PCstate enabled M O op:RstateOP:=
  (PCge,TickLocal,M,(fun _=>false),(enabled,[1],[false]),O,op).
Definition PCphysical clock run:=V293_owned_record_cells(PCcells clock run) **
  (CurTid WhileReady ** (PCbindings ** LINV V293_witness_li WhileReady [])).
Definition PCcode run:=V293_tick_post_hook_core_code WhileBindings run.
Definition PCcore clock run:=V293_tick_post_hook_core_pre WhileBindings WhileIdle Vnull WhileReady ChainEvents
  93%positive 92%positive 94%positive 96%positive 70%positive 98%positive 99%positive run PCframe clock WhileIdle.
Definition PCpre clock run enabled:=<||PCcode run||> ** OS[(fun _=>false),enabled,[1],[false]] ** PCcore clock run.
Definition PCpost clock run enabled:=V293_tick_post_hook_core_result WhileBindings WhileIdle Vnull WhileReady ChainEvents
  93%positive 92%positive 94%positive 96%positive 70%positive 98%positive 99%positive run PCframe
  (Int.add clock Int.one) WhileIdle (fun _=>false) enabled [1][false].

Lemma PCframe_good : GoodFrm PCframe.
Proof.
 unfold PCframe,PCbindings,DHbindings,LINV,V293_witness_li;cbn [GoodFrm].
 repeat split;try(intros;exact I).
Qed.
Lemma PCframe_change : can_change_aop PCframe.
Proof.
 unfold PCframe,PCbindings,DHbindings,LINV,V293_witness_li;cbn [can_change_aop].
 repeat split;try(intros;exact I). all:apply V293_tick_update_change;apply V293_owned_cells_good.
Qed.
Lemma PCenv : forall st,st |= PCframe -> V293_tick_post_env 901%Z 902%Z 903%Z 1001%Z 1002%Z 1003%Z
  70%positive 93%positive 92%positive 96%positive 98%positive 99%positive(getgenv st)(getlenv st).
Proof.
 intros st Held;eapply V293_star_env_l;[ |exact Held].
 intros s(Delay&Nn&Gn&Nu&Gu&Nh&Gh).
 destruct Delay as(Bc&Nr&Gr&Ng&Gg).
 destruct Bc as[b[B[E _]]];inversion E;subst b.
 destruct Gr as[br[R[Er _]]];inversion Er;subst br.
 destruct Gg as[bg[G[Eg _]]];inversion Eg;subst bg.
 destruct Gn as[bn[Gn[En _]]];inversion En;subst bn.
 destruct Gu as[bu[Gu[Eu _]]];inversion Eu;subst bu.
 destruct Gh as[bh[Gh[Eh _]]];inversion Eh;subst bh.
 destruct Nr as[Nr _];destruct Ng as[Ng _].
 destruct Nn as[Nn _];destruct Nu as[Nu _];destruct Nh as[Nh _].
 unfold V293_tick_post_env,V293_tick_delay_env;repeat split;try assumption;
 match goal with
 | N:~indom ?le ?x |- get ?le ?x=None =>
   destruct(get le x)eqn:V;[exfalso;apply N;eexists;exact V|exact V]
 end.
Qed.
Lemma PCcur : (CurTid WhileReady ** PCframe) ==> CurLINV V293_witness_li WhileReady.
Proof. unfold PCframe,CurLINV;intros s H;exists([]:list logicvar);clear -H;sep auto. Qed.
Lemma PCstar : forall enabled m1 m2 m p q,
 join m1 m2 m -> PCstate enabled m1 emp(END None) |= p ->
 PCstate enabled m2 emp(END None) |= q -> PCstate enabled m emp(END None) |= p ** q.
Proof.
 intros;apply sat_split';exists m1;exists m2;exists(emp:osabst);exists(emp:osabst).
 split;[assumption| ];split;[apply map_join_emp| ];split;assumption.
Qed.
Lemma PCcurrent_spatial : PCstate false WCcurrent emp(END None) |= CurTid WhileReady.
Proof.
 exists Tvoid;exists 97%positive;eapply PCstar with(m1:=emp)(m2:=WCcurrent).
 - apply map_join_comm;apply map_join_emp.
 - exists 97%positive;split;[vm_compute;reflexivity| ];repeat split;reflexivity.
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Lemma PCbindings_spatial : PCstate false emp emp(END None) |= PCbindings.
Proof.
 unfold PCbindings,DHbindings;repeat split.
 - exists 70%positive;split;[apply map_get_sig| ];repeat split;reflexivity.
 - intros[v E];vm_compute in E;discriminate.
 - exists 93%positive;split;[vm_compute;reflexivity| ];repeat split;reflexivity.
 - intros[v E];vm_compute in E;discriminate.
 - exists 92%positive;split;[vm_compute;reflexivity| ];repeat split;reflexivity.
 - intros[v E];vm_compute in E;discriminate.
 - exists 96%positive;split;[vm_compute;reflexivity| ];repeat split;reflexivity.
 - intros[v E];vm_compute in E;discriminate.
 - exists 98%positive;split;[vm_compute;reflexivity| ];repeat split;reflexivity.
 - intros[v E];vm_compute in E;discriminate.
 - exists 99%positive;split;[vm_compute;reflexivity| ];repeat split;reflexivity.
Qed.
Lemma PClinv_spatial : PCstate false emp emp(END None) |= LINV V293_witness_li WhileReady [].
Proof.
 unfold LINV;apply astar_comm;apply astar_l_apure_intro.
 - split;reflexivity.
 - apply V293_witness_li_good.
Qed.
(* A small proved address-disjointness decision, not an execution oracle.
   It replaces expensive pairwise propositional proof search only. *)
Definition PCaddr_eqb(a b:addr):=Pos.eqb(fst a)(fst b)&&Z.eqb(snd a)(snd b).
Fixpoint PCsepb(cells:list V293_record_cell):bool:=
 match cells with
 | []=>true
 | c::rest=>forallb(fun a=>negb(existsb(PCaddr_eqb a)(OwnershipCellsAddresses rest)))
     (OwnershipCellAddresses c)&&PCsepb rest
 end.
Lemma PCsepb_sound : forall cells,PCsepb cells=true -> OwnershipCellsSeparated cells.
Proof.
 induction cells as[ |c rest IH];cbn [PCsepb OwnershipCellsSeparated];intro Checked;[exact I| ].
 apply andb_true_iff in Checked;destruct Checked as[Head Tail];split;[ |apply IH;exact Tail].
 intros a Member Rest;rewrite forallb_forall in Head;specialize(Head a Member).
 apply Bool.negb_true_iff in Head.
 assert(E:existsb(PCaddr_eqb a)(OwnershipCellsAddresses rest)=true).
 { apply existsb_exists;exists a;split;[exact Rest| ].
   unfold PCaddr_eqb;rewrite Pos.eqb_refl,Z.eqb_refl;reflexivity. }
 congruence.
Qed.
Lemma PCspatial : forall clock run,run<256 ->
 PCstate false(PCmemory clock run)emp(END None) |= PCphysical clock run.
Proof.
 intros clock run Range.
 assert(Apart:OwnershipCellsSeparated(PCcells clock run)).
 { apply PCsepb_sound;change(PCsepb(PCcells(Int.repr 37)0)=true);vm_compute;reflexivity. }
 assert(Typed:Forall(fun c=>let '(_,tp,v):=c in rule_type_val_match tp v=true)(PCcells clock run)).
 { unfold PCcells,PCglobals,V293_tick_post_hook_core_globals.
   cbn [V293_record_layout V293_tick_chain_missing V293_tick_node_missing
    V293_tick_pend_value WhileBindings V293_tick_wait_node V293_tick_task_cells V293_tick_idle_cell
    V293_ready_cells V293_priority_cells RCentries app concat map fst snd tl].
   repeat constructor;try reflexivity;apply V293_byte_type;exact Range. }
 pose proof(OwnershipCellsSpatial _ Apart Typed PCge TickLocal)as Bytes.
 assert(Owned:PCstate false(OwnershipCellsMemory(PCcells clock run))emp(END None) |=
   V293_owned_record_cells(PCcells clock run)).
 { unfold PCstate;eapply TickCellsRebase;exact Bytes. }
 assert(Both:PCstate false(PCmemory clock run)emp(END None) |=
   V293_owned_record_cells(PCcells clock run) ** CurTid WhileReady).
 { eapply PCstar;[ |exact Owned|exact PCcurrent_spatial].
   apply map_join_merge;apply map_disjoint;intros[b i].
   destruct(Pos.eq_dec b 97%positive)as[E|E].
   - subst b;left;apply OwnershipCellsOutside;vm_compute;intuition congruence.
   - right;left;apply V293_encoded_memory_outside;left;exact E. }
 assert(WithEmpty:PCstate false(PCmemory clock run)emp(END None) |= PCbindings **
   (LINV V293_witness_li WhileReady [] ** (V293_owned_record_cells(PCcells clock run) ** CurTid WhileReady))).
 { eapply PCstar with(m1:=emp)(m2:=PCmemory clock run).
   - apply map_join_comm;apply map_join_emp.
   - exact PCbindings_spatial.
   - eapply PCstar with(m1:=emp)(m2:=PCmemory clock run).
     + apply map_join_comm;apply map_join_emp.
     + exact PClinv_spatial.
     + exact Both. }
 unfold PCphysical;clear -WithEmpty;sep auto.
Qed.
Lemma PCabstract : forall clock,V293_target_wstate PCge TickLocal emp(PCabs clock) |=
 V293_shared_fields WhileReady WhileOldTasks ChainEvents clock.
Proof.
 intro clock;unfold V293_shared_fields,PCabs,V293_shared_fixture_abs.
 repeat(eapply V293_target_wstate_star;[apply map_join_emp|
  apply map_join_merge;apply map_disjoint;intros key;destruct key;simpl;auto|
  split;reflexivity| ]);split;reflexivity.
Qed.
Definition PCother clock run:=
 ((CurTid WhileReady ** V293_shared_fields WhileReady WhileOldTasks ChainEvents clock) **
  V293_ready_owned 93%positive 92%positive 94%positive WhileOldTasks) **
 (PV(96%positive,Int.zero)@Tint32|->Vint32 clock **
 (V293_owned_record_cell(V293_tick_pointer_cell 70%positive WhileIdle) **
 (V293_owned_record_cells(V293_tick_chain_missing WhileBindings WhileIdle) **
 (V293_owned_record_cells(PCglobals run) ** PCframe)))).

Lemma PCjoint : forall clock run enabled op,run<256 ->
 PCstate enabled(PCmemory clock run)(PCabs clock)op |=
 PCphysical clock run ** V293_shared_fields WhileReady WhileOldTasks ChainEvents clock.
Proof.
 intros clock run enabled op Range.
 assert(GP:GoodFrm(PCphysical clock run)).
 { unfold PCphysical,PCbindings,DHbindings,LINV,V293_witness_li;cbn [GoodFrm].
   repeat split;try(intros;exact I);apply V293_tick_cells_frame. }
 pose proof(goodfrm_prop _ _ _ _ _ _ GP(PCspatial clock run Range)(fun _=>false)
   (false,[],[])(spec_done None))as Physical.
 assert(Joint:V293_target_wstate PCge TickLocal(PCmemory clock run)(PCabs clock) |=
   PCphysical clock run ** V293_shared_fields WhileReady WhileOldTasks ChainEvents clock).
 { eapply V293_target_wstate_star with(m1:=PCmemory clock run)(m2:=emp)(o1:=emp)(o2:=PCabs clock).
   - apply map_join_emp.
   - apply map_join_comm;apply map_join_emp.
   - exact Physical.
   - apply PCabstract. }
 assert(Good:GoodFrm(PCphysical clock run ** V293_shared_fields WhileReady WhileOldTasks ChainEvents clock)).
 { cbn [GoodFrm];split;[exact GP|unfold V293_shared_fields;cbn [GoodFrm];repeat split;exact I]. }
 pose proof(goodfrm_prop _ _ _ _ _ _ Good Joint(fun _=>false)
   (enabled,[1],[false])op)as Ready.
 exact Ready.
Qed.
Lemma PCpack : forall clock run enabled M O op,
 PCstate enabled M O op |= PCphysical clock run ** V293_shared_fields WhileReady WhileOldTasks ChainEvents clock ->
 PCstate enabled M O op |= PCcore clock run.
Proof.
 intros clock run enabled M O op Ready.
 assert(Flat:PCstate enabled M O op |= COlayouts ** PCother clock run).
 { unfold PCother,V293_ready_owned;sep normal;exists 16;exists 16;exists RCentries.
   assert(Packed:PCstate enabled M O op |=
     COlayouts **
     (((CurTid WhileReady ** V293_shared_fields WhileReady WhileOldTasks ChainEvents clock) **
       V293_owned_record_cells(V293_ready_cells 93%positive 92%positive 94%positive 16 16 RCentries)) **
     (PV(96%positive,Int.zero)@Tint32|->Vint32 clock **
     (V293_owned_record_cell(V293_tick_pointer_cell 70%positive WhileIdle) **
     (V293_owned_record_cells(V293_tick_chain_missing WhileBindings WhileIdle) **
     (V293_owned_record_cells(PCglobals run) ** PCframe)))))).
   { unfold COlayouts,PCphysical,PCcells,PCglobals,PCframe,V293_tick_post_hook_core_globals in Ready |- *.
     cbn [WhileBindings WhileReason V293_tick_wait_node V293_tick_block V293_tick_base
       V293_tick_prio V293_tick_task_pointer V293_tick_chain_cells V293_tick_task_cells V293_tick_head
       V293_tick_pointer_cell V293_tick_bitmap_cells V293_priority_cells RCentries V293_ready_cells
       V293_tick_binding_extra V293_tick_record_extra V293_tick_idle_extra V293_record_layout
       V293_tick_chain_missing V293_tick_node_missing V293_tick_pend_value
       V293_owned_record_cells app concat map fst snd tl WhileHead WhileSecond WhileReady WhileIdle WhileFrameCells]in Ready |- *.
     unfold V293_owned_record_cell in Ready |- *;clear -Ready;sep auto. }
   clear -Packed;sep auto. exact RCold_rel. }
 pose proof(COpack _ _ Flat)as Packed.
 assert(Entry:PCstate enabled M O op |= PCcore clock run).
 { unfold PCcore,V293_tick_post_hook_core_pre,V293_tick_post_hook_core_state,
     V293_tick_post_hook_core_frame,V293_ready_payload,PCother,PCglobals in *.
   change(PCstate enabled M O op |=
    ((CurTid WhileReady ** V293_shared_fields WhileReady WhileOldTasks ChainEvents clock) **
      (V293_owned_task_records WhileOldTasks ** V293_ready_owned 93%positive 92%positive 94%positive WhileOldTasks)) **
    (PV(96%positive,Int.zero)@Tint32|->Vint32 clock **
    (V293_owned_record_cell(V293_tick_pointer_cell 70%positive WhileIdle) **
    (V293_owned_record_cells(V293_tick_chain_missing WhileBindings WhileIdle) **
    (V293_owned_record_cells(V293_tick_post_hook_core_globals WhileBindings WhileIdle 98%positive 99%positive run) ** PCframe))))).
   clear -Packed;sep auto. }
 exact Entry.
Qed.
Theorem PCentry : forall clock run enabled,run<256 ->
 PCstate enabled(PCmemory clock run)(PCabs clock)(PCcode run) |= PCpre clock run enabled.
Proof.
 intros clock run enabled Range.
 pose proof(PCpack clock run enabled _ _ _(PCjoint clock run enabled(PCcode run)Range))as Entry.
 assert(Control:PCstate enabled(PCmemory clock run)(PCabs clock)(PCcode run) |=
   Aisr(fun _=>false) ** (Aie enabled ** (Ais(1::nil) ** (Acs(false::nil) ** PCcore clock run)))).
 { apply astar_l_aisr_intro;[ |reflexivity]. apply astar_l_aie_intro;[ |reflexivity].
   apply astar_l_ais_intro;[ |reflexivity]. apply astar_l_acs_intro;[exact Entry|reflexivity]. }
 unfold PCpre;apply astar_l_aop'_intro;[ |reflexivity]. clear -Control;sep auto.
Qed.

Theorem PCrules : forall Spec sd I r ri clock run enabled,run<256 ->
 InfRules Spec sd V293_witness_li I r ri(PCpre clock run enabled)
  (V293_tick_post_hook 901%Z 902%Z 903%Z 1001%Z 1002%Z 1003%Z)(PCpost clock run enabled)WhileReady.
Proof.
 intros;apply V293_tick_post_hook_core_hoare.
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
Qed.
Theorem PCrunning : forall Spec sd I r ri clock enabled,
 InfRules Spec sd V293_witness_li I r ri(PCpre clock 1 enabled)
  (V293_tick_post_hook 901%Z 902%Z 903%Z 1001%Z 1002%Z 1003%Z)(PCpost clock 1 enabled)WhileReady.
Proof. intros;apply PCrules;lia. Qed.
Theorem PCstopped : forall Spec sd I r ri clock run enabled,run=0 \/ run=255 ->
 InfRules Spec sd V293_witness_li I r ri(PCpre clock run enabled)
  (V293_tick_post_hook 901%Z 902%Z 903%Z 1001%Z 1002%Z 1003%Z)(PCpost clock run enabled)WhileReady.
Proof. intros;apply PCrules;lia. Qed.
Theorem PCsemantics : forall Spec sd I r ri clock run enabled,run<256 ->
 simulation.RuleSem Spec sd V293_witness_li I r ri(PCpre clock run enabled)
  (V293_tick_post_hook 901%Z 902%Z 903%Z 1001%Z 1002%Z 1003%Z)(PCpost clock run enabled)WhileReady.
Proof. intros;apply RuleSound;apply PCrules;assumption. Qed.

Lemma PCread : forall clock run a tp v,run<256 ->
 In(a,tp,v)(PCcells clock run) -> load tp(PCmemory clock run)a=Some v.
Proof.
 intros clock run a tp v Range Member.
 eapply V293_record_star_load_l with(s:=PCstate false(PCmemory clock run)emp(END None))
   (P:=V293_owned_record_cells(PCcells clock run));[ |apply PCspatial;exact Range].
 intros st H;eapply V293_owned_record_cells_load;[exact Member|exact H].
Qed.
Theorem PCscan_not_head : forall clock run,run<256 ->
 load(Tptr V293_tcb_type)(PCmemory clock run)(70%positive,0%Z)=Some(Vptr WhileIdle) /\
 load(Tptr V293_tcb_type)(PCmemory clock run)(99%positive,0%Z)=Some(Vptr WhileHead) /\
 WhileIdle<>WhileHead /\
 evalval(V293_tick_guard 901%Z)(PCge,TickLocal,PCmemory clock run)=Some(Vint32 Int.zero).
Proof.
 intros clock run Range.
 assert(Pointer:load(Tptr V293_tcb_type)(PCmemory clock run)(70%positive,0%Z)=Some(Vptr WhileIdle)).
 { eapply PCread;[exact Range|unfold PCcells;cbn [app In];repeat(first[left;reflexivity|right])]. }
 split;[exact Pointer| ];split.
 - eapply PCread;[exact Range|unfold PCcells,PCglobals,V293_tick_post_hook_core_globals;cbn [app In];repeat(first[left;reflexivity|right])].
 - split;[vm_compute;discriminate| ].
   apply V293_tick_guard_eval with(bc:=70%positive)(bt:=81%positive)(base:=368%Z)(p:=12).
   + apply map_get_sig.
   + exact Pointer.
   + lia.
   + change(368+50<=4294967295)%Z;lia.
   + lia.
   + eapply PCread;[exact Range|unfold PCcells;cbn [app In];repeat(first[left;reflexivity|right])].
Qed.

Definition PCresidual clock:=
 V293_owned_record_cells(concat(map V293_tick_binding_extra WhileBindings)) **
 (V293_owned_record_cells(V293_tick_idle_extra WhileIdle Vnull) **
 (V293_shared_fields WhileReady WhileOldTasks ChainEvents clock **
 (V293_owned_record_cells(V293_priority_cells 94%positive 0%Z RCentries) **
 (CurTid WhileReady ** PCframe)))).
Local Ltac PCexpand :=
 cbn [WhileBindings WhileReason V293_tick_wait_node V293_tick_block V293_tick_base
  V293_tick_prio V293_tick_task_pointer V293_tick_chain_cells V293_tick_task_cells V293_tick_head
  V293_tick_pointer_cell V293_tick_bitmap_cells V293_priority_cells RCentries V293_ready_cells
  V293_tick_binding_extra V293_tick_record_extra V293_tick_idle_extra V293_record_layout
  V293_tick_chain_missing V293_tick_node_missing V293_tick_pend_value V293_tick_idle_cell
  V293_owned_record_cells app concat map fst snd tl WhileHead WhileSecond WhileReady WhileIdle WhileFrameCells]in *.
Definition PCoperationalcells clock run:=
 V293_tick_post_cells 96%positive clock 98%positive run 99%positive WhileHead
  70%positive WhileIdle(map fst WhileBindings)WhileIdle 92%positive 93%positive 3 16 16 ++
 concat(map V293_tick_binding_extra WhileBindings) ++ V293_tick_idle_extra WhileIdle Vnull ++
 V293_priority_cells 94%positive 0%Z RCentries ++ WhileFrameCells.
Local Ltac PCpermute :=
 lazymatch goal with
 | |- Permutation ?xs ?xs => apply Permutation_refl
 | |- Permutation ?xs (?x::?ys) =>
   let rec extract before rest :=
    lazymatch rest with
    | ?h::?tail =>
      tryif unify h x then
       (eapply Permutation_trans with(l':=x::(before++tail));
        [apply Permutation_sym;apply Permutation_middle|apply perm_skip;cbn [app];PCpermute])
      else extract(before++[h])tail
    end
   in extract(@nil V293_record_cell)xs
 end.
Lemma PCoperational_permutation : forall clock run,Permutation(PCcells clock run)(PCoperationalcells clock run).
Proof.
 intros clock run;unfold PCcells,PCglobals,PCoperationalcells,V293_tick_post_hook_core_globals,
  V293_tick_post_cells,V293_tick_post_globals.
 PCexpand.
 PCpermute.
Qed.
Lemma PCowned_entry : forall clock run enabled,run<256 ->
 PCstate enabled(PCmemory clock run)(PCabs clock)(PCcode run) |=
 V293_tick_suffix_owned 96%positive clock 98%positive run 99%positive WhileHead
  70%positive WhileIdle(map fst WhileBindings)WhileIdle 92%positive 93%positive 3 16 16(PCresidual clock).
Proof.
 intros clock run enabled Range;pose proof(PCjoint clock run enabled(PCcode run)Range)as Joint.
 assert(Ordered:PCstate enabled(PCmemory clock run)(PCabs clock)(PCcode run) |=
  (V293_owned_record_cells(PCoperationalcells clock run) **
   (CurTid WhileReady ** (PCbindings ** LINV V293_witness_li WhileReady []))) **
  V293_shared_fields WhileReady WhileOldTasks ChainEvents clock).
 { eapply astar_mono;[ |intros st H;exact H|exact Joint].
   unfold PCphysical;apply astar_mono;[ |intros st H;exact H].
   apply V293_owned_cells_permutation;apply PCoperational_permutation. }
 unfold V293_tick_suffix_owned,V293_tick_loop_owned,PCresidual,PCoperationalcells,
  V293_tick_post_cells,V293_tick_post_globals,PCframe in Ordered |- *.
 PCexpand.
 unfold V293_owned_record_cell in Ordered |- *.
 clear -Ordered;sep auto.
Qed.
Definition PCexecution P ks clock run enabled Mf:=V293_local_steps P
 (curs(V293_tick_post_hook 901%Z 902%Z 903%Z 1001%Z 1002%Z 1003%Z),(kenil,ks))
 ((PCge,TickLocal,PCmemory clock run),(fun _=>false),(enabled,[1],[false]))
 (curs(sskip None),(kenil,ks))((PCge,TickLocal,Mf),(fun _=>false),(enabled,[1],[false])).
Definition PCexpectedcells run:=V293_tick_pointer_cell 70%positive WhileIdle::
 (V293_tick_chain_cells(if Nat.eqb run 1 then map V293_tick_task_after(map fst WhileBindings)else map fst WhileBindings)WhileIdle ++
 (V293_tick_bitmap_cells 92%positive 93%positive 3 16(if Nat.eqb run 1 then 20 else 16)++[V293_tick_idle_cell WhileIdle])).
Definition PCreturned clock run enabled Mf:=
 PCstate enabled Mf(PCabs clock)(PCcode run) |=
 V293_tick_suffix_owned 96%positive(Int.add clock Int.one)98%positive run 99%positive WhileHead
  70%positive WhileIdle
  (if Nat.eqb run 1 then map V293_tick_task_after(map fst WhileBindings)else map fst WhileBindings)
  WhileIdle 92%positive 93%positive 3 16(if Nat.eqb run 1 then 20 else 16)(PCresidual clock).

(* Independent execution in the existing operational semantics on the NEW
   literal heap; NOT an execution experiment for the new RuleSem proof. *)
Theorem PCliteral_execution : forall P ks clock run enabled,run<256 ->exists Mf,
 PCexecution P ks clock run enabled Mf /\
 load Tint32 Mf(96%positive,0%Z)=Some(Vint32(Int.add clock Int.one)) /\
 (forall a tp v,In(a,tp,v)(PCexpectedcells run) ->load tp Mf a=Some v) /\
 load Tint32 Mf(90%positive,0%Z)=Some(Vint32(Int.repr 99)) /\ PCreturned clock run enabled Mf.
Proof.
 intros P ks clock run enabled Range.
 destruct(V293_tick_post_hook_owned_execution(map fst WhileBindings)P ks PCge TickLocal(PCmemory clock run)
  (fun _=>false)enabled [1][false](PCabs clock)(PCcode run)901%Z 902%Z 903%Z 1001%Z 1002%Z 1003%Z
  70%positive 96%positive 98%positive 99%positive WhileIdle WhileIdle 92%positive 93%positive clock run 3 16 16(PCresidual clock)
  ltac:(apply map_get_sig)ltac:(vm_compute;reflexivity)ltac:(vm_compute;reflexivity)
  ltac:(vm_compute;reflexivity)ltac:(vm_compute;reflexivity)
  ltac:(vm_compute;reflexivity)ltac:(vm_compute;reflexivity)
  ltac:(vm_compute;reflexivity)ltac:(vm_compute;reflexivity)
  ltac:(vm_compute;reflexivity)ltac:(vm_compute;reflexivity)
  ltac:(change(368+50<=4294967295)%Z;lia)
  ltac:(rewrite Forall_map;eapply Forall_impl;[ |exact WhileBindingsValid];intros[t[st m]]H;exact(proj1 H))
  Range ltac:(lia)ltac:(lia)ltac:(lia)(PCowned_entry clock run enabled Range))as(Mf&Exec&Clock&Pointer&Returned).
 assert(Return:PCreturned clock run enabled Mf).
 { unfold PCreturned;destruct(Nat.eqb run 1);exact Returned. }
 assert(Fields:forall a tp v,In(a,tp,v)(PCexpectedcells run) ->load tp Mf a=Some v).
 { intros a tp v Member;unfold PCreturned,V293_tick_suffix_owned in Return.
   change(load tp(getmem(PCstate enabled Mf(PCabs clock)(PCcode run)))a=Some v).
   eapply V293_record_star_load_r;[ |exact Return]. do 2 eapply V293_record_star_load_r.
   intros s HS;eapply V293_tick_loop_fields_load;[ |exact HS].
   unfold PCexpectedcells in Member;destruct(Nat.eqb run 1);exact Member. }
 assert(Canary:load Tint32 Mf(90%positive,0%Z)=Some(Vint32(Int.repr 99))).
 { assert(Held:PCstate enabled Mf(PCabs clock)(PCcode run) |= V293_owned_record_cells WhileFrameCells ** Atrue).
   { unfold PCreturned,V293_tick_suffix_owned,V293_tick_loop_owned,PCresidual,PCframe in Return.
     clear -Return;sep auto. }
   eapply V293_record_star_load_l with(s:=PCstate enabled Mf(PCabs clock)(PCcode run));[ |exact Held].
   apply V293_owned_record_cells_load;left;reflexivity. }
 exists Mf;split;[exact Exec| ];split;[exact Clock| ];split;[exact Fields| ];split;assumption.
Qed.

Lemma PCstopped_recover : forall clock run enabled Mf,
 (run=0 \/ run=255) -> PCreturned clock run enabled Mf ->
 PCstate enabled Mf(PCabs clock)(PCcode run) |=
 PCphysical(Int.add clock Int.one)run ** V293_shared_fields WhileReady WhileOldTasks ChainEvents clock.
Proof.
 intros clock run enabled Mf Stop Returned.
 assert(Flag:Nat.eqb run 1=false)by(apply Nat.eqb_neq;lia).
 unfold PCreturned in Returned;rewrite Flag in Returned.
 assert(Ordered:PCstate enabled Mf(PCabs clock)(PCcode run) |=
  (V293_owned_record_cells(PCoperationalcells(Int.add clock Int.one)run) **
   (CurTid WhileReady ** (PCbindings ** LINV V293_witness_li WhileReady []))) **
  V293_shared_fields WhileReady WhileOldTasks ChainEvents clock).
 { unfold V293_tick_suffix_owned,V293_tick_loop_owned,PCresidual,PCoperationalcells,
    V293_tick_post_cells,V293_tick_post_globals,PCframe in Returned |- *.
   PCexpand. unfold V293_owned_record_cell in Returned |- *.
   clear -Returned;sep auto. }
 unfold PCphysical;eapply astar_mono;[ |intros st H;exact H|exact Ordered].
 apply astar_mono;[ |intros st H;exact H].
 apply V293_owned_cells_permutation;apply Permutation_sym;apply PCoperational_permutation.
Qed.

(* The positive and negative states below have IDENTICAL physical output,
   environment, control state, task map, events, abstract program and frame.
   Only ostmid differs. No store or fabricated output is used. *)
Lemma PCstopped_synced : forall clock run enabled Mf,
 (run=0 \/ run=255) -> PCreturned clock run enabled Mf ->
 PCstate enabled Mf(set(PCabs clock)ostmid(ostm(Int.add clock Int.one)))(PCcode run) |=
 PCcore(Int.add clock Int.one)run.
Proof.
 intros clock run enabled Mf Stop Returned.
 pose proof(PCstopped_recover clock run enabled Mf Stop Returned)as Recovered.
 assert(Slot:PCstate enabled Mf(PCabs clock)(PCcode run) |=
  Aabsdata ostmid(ostm clock) **
  (PCphysical(Int.add clock Int.one)run **
   (Aabsdata curtid(oscurt WhileReady) **
    (Aabsdata abstcblsid(abstcblist WhileOldTasks) ** Aabsdata absecblsid(absecblist ChainEvents))))).
 { unfold V293_shared_fields in Recovered;clear -Recovered;sep auto. }
 unfold PCstate in Slot.
 apply V293_shared_replace_slot with(new:=ostm(Int.add clock Int.one))in Slot.
 apply PCpack.
 unfold PCstate,V293_shared_fields;clear -Slot;sep auto.
Qed.

Lemma PCstopped_transition : forall sd clock run,
 (run=0 \/ run=255) ->
 spec_stepstar sd(PCcode run)(PCabs clock)(END None)
   (set(PCabs clock)ostmid(ostm(Int.add clock Int.one))).
Proof.
 intros sd clock run Stop.
 assert(Flag:Nat.eqb run 1=false)by(apply Nat.eqb_neq;lia).
 unfold PCcode,V293_tick_post_hook_core_code,V293_tick_post_hook_core_tail;rewrite Flag.
 eapply spec_stepS.
 - apply spec_seq_step2;apply V293_tick_clock_transition.
   exact(proj2(proj2(proj2(V293_shared_fields_get _ _ _ _ _(PCabstract clock))))).
 - eapply spec_stepS;[apply spec_seq_step1|apply spec_stepO].
Qed.

Theorem PCclock_neutralized : forall P ks sd clock run enabled,
 (clock=Int.repr 37 \/ clock=Int.repr Int.max_unsigned) ->
 (run=0 \/ run=255) -> exists Mf,
 PCexecution P ks clock run enabled Mf /\
 spec_stepstar sd(PCcode run)(PCabs clock)(END None)
   (set(PCabs clock)ostmid(ostm(Int.add clock Int.one))) /\
 load Tint32 Mf(96%positive,0%Z)=Some(Vint32(Int.add clock Int.one)) /\
 load Tint32 Mf(90%positive,0%Z)=Some(Vint32(Int.repr 99)) /\
 PCstate enabled Mf(set(PCabs clock)ostmid(ostm(Int.add clock Int.one)))(PCcode run) |=
   PCcore(Int.add clock Int.one)run /\
 ~ PCstate enabled Mf(PCabs clock)(PCcode run) |=
   V293_time_ready_core 93%positive 92%positive 94%positive 96%positive ** Atrue.
Proof.
 intros P ks sd clock run enabled Cases Stop.
 assert(Range:run<256)by lia.
 destruct(PCliteral_execution P ks clock run enabled Range)as(Mf&Exec&Clock&Fields&Canary&Returned).
 exists Mf;split;[exact Exec| ];split;[apply PCstopped_transition;exact Stop| ];
 split;[exact Clock| ];split;[exact Canary| ];split.
 - apply PCstopped_synced;assumption.
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

Theorem PCwrapped_execution : forall P ks run enabled,
 (run=0 \/ run=1 \/ run=255) ->exists Mf,
 PCexecution P ks(Int.repr Int.max_unsigned)run enabled Mf /\
 load Tint32 Mf(96%positive,0%Z)=Some(Vint32 Int.zero) /\
 (forall a tp v,In(a,tp,v)(PCexpectedcells run) ->load tp Mf a=Some v) /\
 load Tint32 Mf(90%positive,0%Z)=Some(Vint32(Int.repr 99)).
Proof.
 intros P ks run enabled Cases;assert(Range:run<256)by lia.
 destruct(PCliteral_execution P ks(Int.repr Int.max_unsigned)run enabled Range)
   as(Mf&Exec&Clock&Fields&Canary&Returned).
 assert(Wrap:Int.add(Int.repr Int.max_unsigned)Int.one=Int.zero).
 { change(Int.repr 4294967296=Int.repr 0).
   apply Int.eqm_samerepr;unfold Int.eqm,Int.eqmod;exists 1%Z;reflexivity. }
 exists Mf;split;[exact Exec| ];split;[rewrite <-Wrap;exact Clock| ];split;assumption.
Qed.

(* The first witness is the NEW post-hook execution. The second, separate
   witness explicitly reuses stage165's original-while task-neutralization
   control. It is not described as execution of the new RuleSem theorem. *)
Theorem PCexecution_control : forall P ks sd enabled,exists Mf oldMf,
 PCexecution P ks(Int.repr 37)1 enabled Mf /\
 load Tint32 Mf(96%positive,0%Z)=Some(Vint32(Int.repr 38)) /\
 (forall a tp v,In(a,tp,v)(PCexpectedcells 1) ->load tp Mf a=Some v) /\
 load Tint32 Mf(90%positive,0%Z)=Some(Vint32(Int.repr 99)) /\
 WCexecution P ks enabled oldMf /\
 spec_stepstar sd(V293_tick_chain_code WhileBindings)WCabs(END None)WCnew /\
 WCstate enabled oldMf WCnew(END None) |= V293_tick_while_core_post WhileBindings WhileIdle
   93%positive 92%positive 94%positive 96%positive 70%positive WCframe /\
 WCreads oldMf /\
 ~ WCneutralized enabled oldMf |= V293_time_ready_core 93%positive 92%positive 94%positive 96%positive ** Atrue.
Proof.
 intros P ks sd enabled.
 destruct(PCliteral_execution P ks(Int.repr 37)1 enabled ltac:(lia))
   as(Mf&Exec&Clock&Fields&Canary&Returned).
 destruct(WCexecution_control P ks sd enabled)as(oldMf&Oldexec&Steps&Post&Reads&Reject).
 exists Mf;exists oldMf;split;[exact Exec| ];split;[exact Clock| ];split;[exact Fields| ];
 split;[exact Canary| ];split;[exact Oldexec| ];split;[exact Steps| ];split;[exact Post| ];split;assumption.
Qed.
