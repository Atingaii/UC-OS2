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
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.


Definition WCge:env:=set WhileGlobal OSTCBCur (97%positive,Tptr Tvoid).
Definition WCcurrent:mem:=V293_encoded_memory 97%positive 0 false
  (encode_val(Tptr Tvoid)(Vptr WhileReady)).
Definition WCclock:V293_record_cell:=((96%positive,0%Z),Tint32,Vint32(Int.repr 37)).
Definition WCcells:=RCcells++[WCclock].
Definition WCmemory:=merge(OwnershipCellsMemory WCcells)WCcurrent.
Definition WCframe:=DHbindings **
  (LINV V293_witness_li WhileReady [] ** V293_owned_record_cells WhileFrameCells).
Definition WCabs:=V293_shared_fixture_abs WhileReady WhileOldTasks ChainEvents(Int.repr 37).
Definition WCnew:=set WCabs abstcblsid(abstcblist WhileNewTasks).
Definition WCstate enabled M O op:RstateOP:=
  (WCge,TickLocal,M,(fun _=>false),(enabled,[1],[false]),O,op).
Definition WCbefore:=V293_tick_while_cells 70%positive [] (map fst WhileBindings)
  WhileIdle 92%positive 93%positive 3 16 16.
Definition WCafter:=V293_tick_while_cells 70%positive
  (V293_tick_chain_cells(map V293_tick_task_after(map fst WhileBindings))WhileIdle)
  [] WhileIdle 92%positive 93%positive 3 16 20.
Definition WCremainder tasks:=V293_tick_while_core_remainder WhileBindings WhileIdle Vnull
  WhileReady ChainEvents(Int.repr 37)94%positive 96%positive WCframe tasks RCentries.
Definition WCpre enabled:=<||V293_tick_chain_code WhileBindings||> **
  OS[(fun _=>false),enabled,[1],[false]] **
  V293_tick_while_core_pre WhileBindings WhileIdle Vnull WhileReady ChainEvents(Int.repr 37)
    93%positive 92%positive 94%positive 96%positive 70%positive WCframe 16 16 RCentries.
Definition WCpost enabled:=<||END None||> ** OS[(fun _=>false),enabled,[1],[false]] **
  V293_tick_while_core_post WhileBindings WhileIdle 93%positive 92%positive 94%positive
    96%positive 70%positive WCframe.
Definition WCphysical:=V293_owned_record_cells WCcells **
  (CurTid WhileReady ** (DHbindings ** LINV V293_witness_li WhileReady [])).

Lemma WCcurrent_member : get WhileOldTasks WhileReady=Some(Int.repr 4,rdy,Vnull).
Proof. vm_compute;reflexivity. Qed.
Lemma WCframe_good : GoodFrm WCframe.
Proof.
 unfold WCframe,DHbindings,LINV,V293_witness_li. cbn [GoodFrm].
 repeat split;try(intros;exact I).
Qed.
Lemma WCframe_change : can_change_aop WCframe.
Proof.
 unfold WCframe,DHbindings,LINV,V293_witness_li. cbn [can_change_aop].
 repeat split;try(intros;exact I). all:apply V293_tick_update_change;apply V293_owned_cells_good.
Qed.
Lemma WCenv : forall st,st |= WCframe -> V293_tick_delay_env 901%Z 902%Z 903%Z
  70%positive 93%positive 92%positive(getgenv st)(getlenv st).
Proof.
 intros st Held. eapply V293_star_env_l;[ | exact Held].
 intros s (Bc&Nr&Gr&Ng&Gg).
 destruct Bc as [ b[B[E _]]];inversion E;subst b.
 destruct Gr as [ br[R[Er _]]];inversion Er;subst br.
 destruct Gg as [ bg[G[Eg _]]];inversion Eg;subst bg.
 destruct Nr as [ Nr _]. destruct Ng as [ Ng _].
 unfold V293_tick_delay_env;repeat split;try assumption.
 - destruct(get(getlenv s)902%Z)eqn:V;[exfalso;apply Nr;eexists;exact V|exact V].
 - destruct(get(getlenv s)903%Z)eqn:V;[exfalso;apply Ng;eexists;exact V|exact V].
Qed.
Lemma WCcur : (CurTid WhileReady ** WCframe) ==> CurLINV V293_witness_li WhileReady.
Proof. unfold WCframe,CurLINV;intros s H;exists([]:list logicvar);clear -H;sep auto. Qed.
Lemma WCstar : forall enabled m1 m2 m p q,
 join m1 m2 m -> WCstate enabled m1 emp(END None) |= p ->
 WCstate enabled m2 emp(END None) |= q -> WCstate enabled m emp(END None) |= p ** q.
Proof.
 intros;apply sat_split';exists m1;exists m2;exists(emp:osabst);exists(emp:osabst).
 split;[assumption| ];split;[apply map_join_emp| ];split;assumption.
Qed.
Lemma WCcurrent_spatial : WCstate false WCcurrent emp(END None) |= CurTid WhileReady.
Proof.
 exists Tvoid;exists 97%positive;eapply WCstar with(m1:=emp)(m2:=WCcurrent).
 - apply map_join_comm;apply map_join_emp.
 - exists 97%positive;split;[apply map_get_set| ];repeat split;reflexivity.
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Lemma WCbindings_spatial : WCstate false emp emp(END None) |= DHbindings.
Proof.
 unfold DHbindings;repeat split.
 - exists 70%positive;split;[apply map_get_sig| ];repeat split;reflexivity.
 - intros[v E];vm_compute in E;discriminate.
 - exists 93%positive;split;[vm_compute;reflexivity| ];repeat split;reflexivity.
 - intros[v E];vm_compute in E;discriminate.
 - exists 92%positive;split;[vm_compute;reflexivity| ];repeat split;reflexivity.
Qed.
Lemma WClinv_spatial : WCstate false emp emp(END None) |= LINV V293_witness_li WhileReady [].
Proof.
 unfold LINV;apply astar_comm;apply astar_l_apure_intro.
 - split;reflexivity.
 - apply V293_witness_li_good.
Qed.
Lemma WCspatial : WCstate false WCmemory emp(END None) |= WCphysical.
Proof.
 assert(Apart:OwnershipCellsSeparated WCcells).
 { vm_compute;repeat split;intros;intuition congruence. }
 assert(Typed:Forall(fun c=>let '(_,tp,v):=c in rule_type_val_match tp v=true)WCcells).
 { repeat constructor;reflexivity. }
 pose proof(OwnershipCellsSpatial _ Apart Typed WCge TickLocal)as Bytes.
 assert(Owned:WCstate false(OwnershipCellsMemory WCcells)emp(END None) |= V293_owned_record_cells WCcells).
 { unfold WCstate;eapply TickCellsRebase;exact Bytes. }
 assert(Both:WCstate false WCmemory emp(END None) |= V293_owned_record_cells WCcells ** CurTid WhileReady).
 { eapply WCstar;[ | exact Owned|exact WCcurrent_spatial].
   apply map_join_merge;apply map_disjoint;intros[b i].
   destruct(Pos.eq_dec b 97%positive)as [ E|E].
   - subst b;left;apply OwnershipCellsOutside;vm_compute;intuition congruence.
   - right;left;apply V293_encoded_memory_outside;left;exact E. }
 assert(WithEmpty:WCstate false WCmemory emp(END None) |= DHbindings **
   (LINV V293_witness_li WhileReady [] **(V293_owned_record_cells WCcells ** CurTid WhileReady))).
 { eapply WCstar with(m1:=emp)(m2:=WCmemory).
   - apply map_join_comm;apply map_join_emp.
   - exact WCbindings_spatial.
   - eapply WCstar with(m1:=emp)(m2:=WCmemory).
     + apply map_join_comm;apply map_join_emp.
     + exact WClinv_spatial.
     + exact Both. }
 unfold WCphysical;clear -WithEmpty;sep auto.
Qed.
Lemma WCabstract : V293_target_wstate WCge TickLocal emp WCabs |=
  V293_shared_fields WhileReady WhileOldTasks ChainEvents(Int.repr 37).
Proof.
 unfold V293_shared_fields,WCabs,V293_shared_fixture_abs.
 repeat(eapply V293_target_wstate_star;[apply map_join_emp|
  apply map_join_merge;apply map_disjoint;intros key;destruct key;simpl;auto|
  split;reflexivity| ]);split;reflexivity.
Qed.
Theorem WCentry : forall enabled,
  WCstate enabled WCmemory WCabs(V293_tick_chain_code WhileBindings) |= WCpre enabled.
Proof.
 intro enabled.
 assert(GP:GoodFrm WCphysical).
 { unfold WCphysical,DHbindings,LINV,V293_witness_li;cbn [GoodFrm].
   repeat split;try(intros;exact I);apply V293_tick_cells_frame. }
 pose proof(goodfrm_prop _ _ _ _ _ _ GP WCspatial (fun _=>false)
   (false,[],[])(spec_done None))as Physical.
 assert(Joint:V293_target_wstate WCge TickLocal WCmemory WCabs |= WCphysical **
   V293_shared_fields WhileReady WhileOldTasks ChainEvents(Int.repr 37)).
 { eapply V293_target_wstate_star with(m1:=WCmemory)(m2:=emp)(o1:=emp)(o2:=WCabs).
   - apply map_join_emp.
   - apply map_join_comm;apply map_join_emp.
   - exact Physical.
   - exact WCabstract. }
 assert(Good:GoodFrm(WCphysical ** V293_shared_fields WhileReady WhileOldTasks ChainEvents(Int.repr 37))).
 { cbn [GoodFrm];split;[exact GP|unfold V293_shared_fields;cbn [GoodFrm];repeat split;exact I]. }
 pose proof(goodfrm_prop _ _ _ _ _ _ Good Joint (fun _=>false)
   (enabled,[1],[false])(V293_tick_chain_code WhileBindings))as Ready.
 assert(Flat:WCstate enabled WCmemory WCabs(V293_tick_chain_code WhileBindings) |=
   V293_rdy_raw_cells WCbefore(WCremainder WhileOldTasks)).
 { apply V293_tick_owned_to_raw.
   unfold WCphysical,WCcells,RCcells,WCbefore,WCremainder,V293_tick_while_core_remainder,
     V293_tick_while_cells,WCframe,WCclock in *.
   cbn [WhileBindings WhileReason V293_tick_wait_node V293_tick_block V293_tick_base
     V293_tick_prio V293_tick_task_pointer V293_tick_chain_cells V293_tick_task_cells V293_tick_head
     V293_tick_pointer_cell V293_tick_bitmap_cells V293_priority_cells RCentries
     V293_tick_binding_extra V293_tick_record_extra V293_tick_idle_extra V293_record_layout
     V293_owned_record_cells app concat map fst snd tl WhileIdle WhileFrameCells]in Ready |- *.
   unfold V293_owned_record_cell,V293_tick_pointer_cell in Ready |- *.
   change (Vptr(V293_tick_task_pointer(V293_tick_wait_node 81%positive 8%Z 1%Z WhileReason 7 10))) with (Vptr WhileHead).
   clear -Ready;sep auto. }
 assert(Control:WCstate enabled WCmemory WCabs(V293_tick_chain_code WhileBindings) |=
   Aisr(fun _=>false) ** (Aie enabled ** (Ais (1::nil) ** (Acs (false::nil) **
   V293_rdy_raw_cells WCbefore(WCremainder WhileOldTasks))))).
 { apply astar_l_aisr_intro;[ | reflexivity]. apply astar_l_aie_intro;[ | reflexivity].
   apply astar_l_ais_intro;[ | reflexivity]. apply astar_l_acs_intro;[exact Flat|reflexivity]. }
 unfold WCpre. change(WCstate enabled WCmemory WCabs(V293_tick_chain_code WhileBindings) |=
   <||V293_tick_chain_code WhileBindings||> ** OS[(fun _=>false),enabled,[1],[false]] **
   V293_rdy_raw_cells WCbefore(WCremainder WhileOldTasks)).
 apply astar_l_aop'_intro;[ | reflexivity]. clear -Control;sep auto.
Qed.
Theorem WCrules : forall Spec sd I r ri enabled,
 InfRules Spec sd V293_witness_li I r ri(WCpre enabled)
   (swhile(V293_tick_guard 901%Z)(V293_tick_iteration 901%Z 902%Z 903%Z))
   (WCpost enabled)WhileReady.
Proof.
 intros;apply V293_tick_while_core_hoare with(ct:=WhileReady)(es:=ChainEvents)(n:=Int.repr 37)
   (message:=Vnull)(lo:=16)(hi:=16)(entries:=RCentries).
 - exact RUnoabs.
 - change(368+50<=4294967295)%Z;lia.
 - exact WhileBindingsValid.
 - exact WhileKeysUnique.
 - exact RCold_rel.
 - exact WCenv.
 - exact WCcur.
 - exact WCframe_good.
 - exact WCframe_change.
 - change(1<=INUM)%nat;unfold INUM;lia.
Qed.
Theorem WCsemantics : forall Spec sd I r ri enabled,
 simulation.RuleSem Spec sd V293_witness_li I r ri(WCpre enabled)
   (swhile(V293_tick_guard 901%Z)(V293_tick_iteration 901%Z 902%Z 903%Z))
   (WCpost enabled)WhileReady.
Proof. intros;apply RuleSound;apply WCrules. Qed.

Definition WCexecution P ks enabled Mf:=V293_local_steps P
  (curs(swhile(V293_tick_guard 901%Z)(V293_tick_iteration 901%Z 902%Z 903%Z)),(kenil,ks))
  ((WCge,TickLocal,WCmemory),(fun _=>false),(enabled,[1],[false]))
  (curs(sskip None),(kenil,ks))((WCge,TickLocal,Mf),(fun _=>false),(enabled,[1],[false])).
Definition WCneutralized enabled M:=WCstate enabled M WCabs(END None).
Definition WCother:=V293_owned_record_cells(concat(map V293_tick_binding_extra WhileBindings)) **
  (V293_owned_record_cells(V293_tick_idle_extra WhileIdle Vnull) **
  ((Aabsdata curtid(oscurt WhileReady) **
    (Aabsdata absecblsid(absecblist ChainEvents) ** Aabsdata ostmid(ostm(Int.repr 37)))) **
  (V293_owned_record_cells(V293_priority_cells 94%positive 0%Z RCentries) **
  (CurTid WhileReady ** (PV(96%positive,Int.zero)@Tint32|->Vint32(Int.repr 37) ** WCframe))))).
Lemma WCowned_entry : forall enabled,
 WCstate enabled WCmemory WCabs(V293_tick_chain_code WhileBindings) |=
 V293_owned_record_cells WCbefore ** WCremainder WhileOldTasks.
Proof.
 intro enabled;pose proof(WCentry enabled)as H;unfold WCpre,V293_tick_while_core_pre in H.
 assert(Raw:WCstate enabled WCmemory WCabs(V293_tick_chain_code WhileBindings) |=
   V293_rdy_raw_cells WCbefore(WCremainder WhileOldTasks))by(clear -H;sep auto).
 apply V293_tick_raw_to_owned;[ | exact Raw].
 unfold WCbefore;cbn [V293_tick_while_cells WhileBindings V293_tick_chain_cells
  V293_tick_task_cells V293_tick_bitmap_cells app map fst];repeat constructor;reflexivity.
Qed.

(* Independent existing operational semantics, not execution of RuleSem.
   Only the exact closing implication is shared with the production rule;
   it uses V293_tick_chain_records_lossless, never an Atrue reconstruction. *)
Theorem WCliteral_execution : forall P ks sd enabled,exists Mf,
 WCexecution P ks enabled Mf /\
 spec_stepstar sd(V293_tick_chain_code WhileBindings)WCabs(END None)WCnew /\
 WCstate enabled Mf WCabs(V293_tick_chain_code WhileBindings) |=
   V293_owned_record_cells WCafter ** WCremainder WhileOldTasks /\
 WCstate enabled Mf WCnew(END None) |= V293_tick_while_core_post WhileBindings WhileIdle
   93%positive 92%positive 94%positive 96%positive 70%positive WCframe.
Proof.
 intros P ks sd enabled;pose proof(WCowned_entry enabled)as Owned.
 assert(Opened:WCstate enabled WCmemory WCabs(V293_tick_chain_code WhileBindings) |=
  V293_tick_loop_owned 70%positive WhileHead(map fst WhileBindings)WhileIdle
    92%positive 93%positive 3 16 16(WCremainder WhileOldTasks)).
 { unfold WCbefore,V293_tick_while_cells,V293_tick_loop_owned in Owned |- *.
   cbn [WhileBindings WhileReason V293_tick_wait_node V293_tick_block V293_tick_base
     V293_tick_prio V293_tick_task_pointer V293_tick_chain_cells V293_tick_task_cells V293_tick_bitmap_cells
    V293_owned_record_cells app map fst]in Owned |- *;clear -Owned;sep auto. }
 destruct(V293_tick_while_owned_execution(map fst WhileBindings)P ks WCge TickLocal WCmemory
   (fun _=>false)enabled [1][false] WCabs(V293_tick_chain_code WhileBindings)
   901%Z 902%Z 903%Z 70%positive WhileIdle 92%positive 93%positive 3 16 16
   (WCremainder WhileOldTasks)eq_refl eq_refl eq_refl eq_refl eq_refl
   ltac:(change(368+50<=4294967295)%Z;lia)
   ltac:(rewrite Forall_map;eapply Forall_impl;[ | exact WhileBindingsValid];intros[t[st m]]H;exact(proj1 H))
   ltac:(lia)ltac:(lia)ltac:(lia) Opened)as(Mf&Exec&Pointer&Returned).
 assert(Flat:WCstate enabled Mf WCabs(V293_tick_chain_code WhileBindings) |=
   V293_owned_record_cells WCafter ** WCremainder WhileOldTasks).
 { unfold WCafter,V293_tick_while_cells,V293_tick_loop_owned in Returned |- *.
   cbn [WhileBindings V293_tick_chain_bitmap V293_tick_next_group V293_tick_next_lo V293_tick_next_hi
    V293_tick_chain_cells V293_tick_task_cells V293_tick_bitmap_cells V293_tick_head
    V293_owned_record_cells app map fst V293_tick_task_after]in Returned |- *.
   clear -Returned;sep auto. }
 exists Mf;split;[exact Exec| ];split.
 - apply V293_tick_record_chain_transition;[exact WhileBindingsValid|exact WhileKeysUnique| ].
   exact(proj1(proj2(V293_shared_fields_get _ _ _ _ _ WCabstract))).
 - split;[exact Flat| ].
   assert(Slot:WCstate enabled Mf WCabs(V293_tick_chain_code WhileBindings) |=
     Aabsdata abstcblsid(abstcblist WhileOldTasks) ** (V293_owned_record_cells WCafter ** WCother)).
   { unfold WCremainder,V293_tick_while_core_remainder,V293_shared_fields,WCother in *;
      clear -Flat;sep auto. }
   apply V293_shared_replace_slot with(new:=abstcblist WhileNewTasks)in Slot.
   assert(Changed:WCstate enabled Mf WCnew(V293_tick_chain_code WhileBindings) |=
     V293_owned_record_cells WCafter ** WCremainder WhileNewTasks).
   { unfold WCremainder,V293_tick_while_core_remainder,V293_shared_fields,WCother in Slot |- *;
      clear -Slot;sep auto. }
   assert(Good:GoodFrm(V293_owned_record_cells WCafter ** WCremainder WhileNewTasks)).
   { unfold WCremainder,V293_tick_while_core_remainder,V293_shared_fields;cbn [GoodFrm].
     repeat split;try exact I;try exact WCframe_good;apply V293_tick_cells_frame. }
   pose proof(goodfrm_prop _ _ _ _ _ _ Good Changed(fun _=>false)(enabled,[1],[false])(END None))as Final.
   apply V293_tick_while_core_raw_close with(ct:=WhileReady)(es:=ChainEvents)(n:=Int.repr 37)
     (message:=Vnull)(lo:=16)(hi:=16)(entries:=RCentries)(gf:=3)(lof:=16)(hif:=20).
   + exact WhileBindingsValid.
   + exact WhileKeysUnique.
   + exact RCold_rel.
   + reflexivity.
   + apply V293_tick_owned_to_raw;exact Final.
Qed.

Definition WCobserved:=WCafter++concat(map V293_tick_binding_extra WhileBindings)++
  (WCclock::WhileFrameCells).
Lemma WCobservations : forall enabled Mf,
 WCstate enabled Mf WCabs(V293_tick_chain_code WhileBindings) |=
   V293_owned_record_cells WCafter ** WCremainder WhileOldTasks ->
 forall a tp v,In(a,tp,v)WCobserved -> load tp Mf a=Some v.
Proof.
 intros enabled Mf Held a tp v Member.
 assert(Cells:WCstate enabled Mf WCabs(V293_tick_chain_code WhileBindings) |=
   V293_owned_record_cells WCobserved ** Atrue).
 { unfold WCobserved,WCremainder,V293_tick_while_core_remainder,WCframe,
     WCafter,V293_tick_while_cells,WCclock in *.
   cbn [WhileBindings WhileReason V293_tick_wait_node V293_tick_block V293_tick_base
     V293_tick_prio V293_tick_task_pointer V293_tick_chain_cells V293_tick_task_cells V293_tick_bitmap_cells
     V293_tick_task_after V293_tick_head V293_tick_pointer_cell
     V293_tick_binding_extra V293_tick_record_extra
     V293_owned_record_cells app map concat fst snd]in Held |- *.
   unfold V293_owned_record_cell in Held |- *;clear -Held;sep auto. }
 eapply V293_record_star_load_l with(s:=WCstate enabled Mf WCabs(V293_tick_chain_code WhileBindings));[ | exact Cells].
 intros st H;eapply V293_owned_record_cells_load;[exact Member|exact H].
Qed.
Definition WCreads Mf:=
 load Tint8 Mf(93%positive,0%Z)=Some(V293_byteval 16) /\
 load Tint8 Mf(93%positive,1%Z)=Some(V293_byteval 20) /\
 load Tint8 Mf(92%positive,0%Z)=Some(V293_byteval 3) /\
 load(Tptr V293_tcb_type)Mf(70%positive,0%Z)=Some(Vptr WhileIdle) /\
 load(Tcom_ptr 410%Z)Mf(81%positive,28%Z)=Some(Vptr WhileSecond) /\
 load(Tcom_ptr 410%Z)Mf(81%positive,148%Z)=Some(Vptr WhileReady) /\
 load(Tcom_ptr 410%Z)Mf(81%positive,268%Z)=Some(Vptr WhileIdle) /\
 load Tint32 Mf(81%positive,52%Z)=Some(Vint32(Int.repr 0)) /\
 load Tint8 Mf(81%positive,57%Z)=Some(V293_byteval 1) /\
 load(Tcom_ptr 411%Z)Mf(81%positive,36%Z)=Some(Vptr(84%positive,Int.repr 4)) /\
 load Tint32 Mf(81%positive,172%Z)=Some(Vint32(Int.repr 2)) /\
 load Tint8 Mf(81%positive,177%Z)=Some(V293_byteval 7) /\
 load Tint32 Mf(96%positive,0%Z)=Some(Vint32(Int.repr 37)) /\
 load Tint32 Mf(90%positive,0%Z)=Some(Vint32(Int.repr 99)).
Lemma WCobserved_reads : forall enabled Mf,
 WCstate enabled Mf WCabs(V293_tick_chain_code WhileBindings) |=
   V293_owned_record_cells WCafter ** WCremainder WhileOldTasks -> WCreads Mf.
Proof.
 intros enabled Mf H;unfold WCreads;repeat split;(eapply WCobservations;[exact H| ];
   unfold WCobserved,WCafter,V293_tick_while_cells,WCclock;
   cbn [WhileBindings WhileReason V293_tick_wait_node V293_tick_block V293_tick_base
     V293_tick_prio V293_tick_task_pointer V293_tick_chain_cells V293_tick_task_cells V293_tick_bitmap_cells
     V293_tick_task_after V293_tick_head V293_tick_pointer_cell
     V293_tick_binding_extra V293_tick_record_extra app map concat fst snd];
   repeat(first[left;reflexivity|right])).
Qed.
Lemma WCreject_neutralized : forall enabled Mf,
 load Tint8 Mf(93%positive,1%Z)=Some(V293_byteval 20) ->
 ~ WCneutralized enabled Mf |= V293_time_ready_core 93%positive 92%positive 94%positive 96%positive ** Atrue.
Proof.
 intros enabled Mf Wrong Held;unfold V293_time_ready_core,V293_time_ready_fields in Held.
 sep normal in Held;sep destruct Held.
 assert(Fields:WCneutralized enabled Mf |= V293_shared_fields x0 x1 x2 x ** Atrue)
   by(clear -Held;sep auto).
 assert(Lookup:get WCabs abstcblsid=Some(abstcblist x1)).
 { eapply V293_star_abst_get_l with(s:=WCneutralized enabled Mf);[ | exact Fields].
   intros st H;exact(proj1(proj2(V293_shared_fields_get _ _ _ _ _ H))). }
 assert(Tasks:x1=WhileOldTasks).
 { pose proof(proj1(proj2(V293_shared_fields_get _ _ _ _ _ WCabstract)))as Fixed.
   change(get WCabs abstcblsid=Some(abstcblist WhileOldTasks))in Fixed;congruence. }
 subst x1.
 assert(Ready:WCneutralized enabled Mf |= V293_ready_owned 93%positive 92%positive 94%positive WhileOldTasks ** Atrue).
 { unfold V293_ready_payload in Held;clear -Held;sep auto. }
 destruct(V293_ready_owned_observation _ _ _ _ _ _ Ready)as(lo&hi&entries&Rel&Reads).
 destruct Rel as [ Lo[Hi[Nonempty[Bitmap Table]]]]. destruct Reads as [ Low[High Rest]].
 change(load Tint8 Mf(93%positive,1%Z)=Some(V293_byteval hi))in High.
 assert(E:hi=20)by(eapply RTbyte_injective;[exact Hi|lia|congruence]);subst hi.
 assert(Bit:V293_bitmap_ready lo 20 10).
 { unfold V293_bitmap_ready;right;repeat split;try lia;reflexivity. }
 destruct(proj1(Bitmap 10 ltac:(lia))Bit)as(t&m&Task).
 apply RCold_lookup in Task.
 destruct Task as [ [T E]|[[T E]|[[T E]|[T E]]]];vm_compute in E;discriminate E.
Qed.
Theorem WCexecution_control : forall P ks sd enabled,exists Mf,
 WCexecution P ks enabled Mf /\
 spec_stepstar sd(V293_tick_chain_code WhileBindings)WCabs(END None)WCnew /\
 WCstate enabled Mf WCnew(END None) |= V293_tick_while_core_post WhileBindings WhileIdle
   93%positive 92%positive 94%positive 96%positive 70%positive WCframe /\
 WCreads Mf /\
 ~ WCneutralized enabled Mf |= V293_time_ready_core 93%positive 92%positive 94%positive 96%positive ** Atrue.
Proof.
 intros P ks sd enabled;destruct(WCliteral_execution P ks sd enabled)as(Mf&Exec&Steps&Flat&Post).
 pose proof(WCobserved_reads enabled Mf Flat)as Reads.
 exists Mf;split;[exact Exec| ];split;[exact Steps| ];split;[exact Post| ];split;[exact Reads| ].
 apply WCreject_neutralized;exact(proj1(proj2 Reads)).
Qed.
