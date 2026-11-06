(* Independent literal bytes, not an initialized-kernel reachability claim. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickReadyUpdate.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickWhileRecords.
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

Definition RUreason := os_stat_sem (72%positive,Int.repr 5).
Definition RUmessage := Vptr (120%positive,Int.repr 7).
Definition RUtasks d : TcbMod.map := set (sig OwnershipReady (Int.repr 4,rdy,Vnull))
  OwnershipWaiting (Int.repr 6,wait RUreason (Int.repr d),RUmessage).
Definition RUnode d := V293_tick_wait_node 41%positive 8%Z d RUreason 0 6.
Definition RUbinding d := (RUnode d,(wait RUreason (Int.repr d),RUmessage)).
Definition RUframecells : list V293_record_cell := [((90%positive,0%Z),Tint32,Vint32(Int.repr 99))].
Definition RUframe := DHbindings ** (LINV V293_witness_li DHtid [] ** V293_owned_record_cells RUframecells).
Definition RUcells d := V293_tick_wait_layout (RUnode d) RUreason RUmessage ++
  (V293_record_layout OwnershipReady 4 rdy Vnull 0 ++
  (V293_ready_cells 93%positive 92%positive 95%positive 16 0 RTentries ++
  ([((96%positive,0%Z),Tint32,Vint32(Int.repr 37));V293_tick_pointer_cell 70%positive OwnershipWaiting] ++
  (V293_tick_wait_missing (RUnode d) RUreason TickNext ++ RUframecells)))).
Definition RUmemory d := merge (OwnershipCellsMemory (RUcells d)) DHcurrent.
Definition RUabs d := V293_shared_fixture_abs DHtid (RUtasks d) (emp:EcbMod.map) (Int.repr 37).
Definition RUstate d M : RstateOP := (DHge,TickLocal,M,(fun _=>false),(false,[1],[false]),RUabs d,
  spec_prim nil (V293_tick_wait_step OwnershipWaiting)).
Definition RUpre d := <||spec_prim nil (V293_tick_wait_step OwnershipWaiting)||> **
  OS[(fun _=>false),false,[1],[false]] **
  V293_tick_ready_wait_pre 93%positive 92%positive 95%positive 96%positive
    DHtid (RUtasks d) (emp:EcbMod.map) (Int.repr 37) (RUnode d) RUreason RUmessage 0
    16 0 RTentries 70%positive TickNext RUframe.
Definition RUpost d := <||END None||> ** OS[(fun _=>false),false,[1],[false]] **
  V293_tick_ready_wait_post 93%positive 92%positive 95%positive 96%positive
    (RUnode d) RUreason RUmessage 70%positive TickNext RUframe.

Lemma RUvalid : forall d, (0<=d<=Int.max_unsigned)%Z -> V293_tick_binding_valid (RUbinding d).
Proof.
 intros d D. split.
 - apply V293_tick_wait_node_valid;try assumption;try lia.
   change (0<=8 /\ 8+54<=4294967295)%Z;lia.
 - split;[cbn;lia|split;reflexivity].
Qed.
Lemma RUtask : forall d, get (RUtasks d) (V293_tick_task_pointer (RUnode d))=
 Some(V293_tick_binding_value false (RUbinding d)).
Proof. intro d. apply map_get_set. Qed.

Lemma RUonly_ready : forall d p t m,
  p<13 -> get (RUtasks d) t=Some (Int.repr (Z.of_nat p),rdy,m) ->
  p=4 /\ t=OwnershipReady /\ m=Vnull.
Proof.
  intros d p t m Bound H. unfold RUtasks in H.
  destruct (TcbMod.eq_dec OwnershipWaiting t) as [E | E].
  - subst t. rewrite map_get_set in H. discriminate.
  - rewrite map_get_set' in H by exact E.
    destruct (TcbMod.eq_dec OwnershipReady t) as [Er | Er].
    + subst t. rewrite map_get_sig in H. inversion H.
      split; [  |  auto ].
      change (Int.unsigned (Int.repr (Z.of_nat 4))=Int.unsigned (Int.repr (Z.of_nat p))) in H1.
      rewrite !V293_priority_repr_unsigned in H1 by lia. lia.
    + rewrite map_get_sig' in H by exact Er. discriminate.
Qed.
Lemma RUrel : forall d, V293_ready_rel 16 0 RTentries (RUtasks d).
Proof.
  intro d. split; [lia | ]. split; [lia | ]. split.
  - exists 4. left. split; [lia | vm_compute; reflexivity].
  - split.
    + intros p Bound. assert (Bit : V293_bitmap_ready 16 0 p <-> p=4).
      { do 13 (destruct p as [ | p]; [vm_compute; intuition lia | ]). lia. }
      rewrite Bit. split.
      * intro E. subst p. exists OwnershipReady. exists Vnull. vm_compute; reflexivity.
      * intros (t&m&H). exact (proj1 (RUonly_ready d _ _ _ Bound H)).
    + split; [reflexivity | ]. intros t p st m H. unfold RUtasks in H.
      destruct (TcbMod.eq_dec OwnershipWaiting t) as [E | E].
      * subst t. rewrite map_get_set in H. inversion H; subst.
        exists 6. repeat split; reflexivity  ||  lia.
      * rewrite map_get_set' in H by exact E.
        destruct (TcbMod.eq_dec OwnershipReady t) as [Er | Er].
        -- subst t. rewrite map_get_sig in H. inversion H; subst.
           exists 4. repeat split; reflexivity  ||  lia.
        -- rewrite map_get_sig' in H by exact Er. discriminate.
Qed.

Lemma RUenv : forall st, st |= RUframe -> V293_tick_delay_env 901%Z 902%Z 903%Z
 70%positive 93%positive 92%positive (getgenv st) (getlenv st).
Proof.
 intros st Held. eapply V293_star_env_l;[ |exact Held].
 intros s (Bc&Nr&Gr&Ng&Gg).
 destruct Bc as [b [B [E _]]];inversion E;subst b.
 destruct Gr as [br [R [Er _]]];inversion Er;subst br.
 destruct Gg as [bg [G [Eg _]]];inversion Eg;subst bg.
 destruct Nr as [Nr _]. destruct Ng as [Ng _].
 unfold V293_tick_delay_env. repeat split;try assumption.
 - destruct (get (getlenv s) 902%Z) eqn:V;[exfalso;apply Nr;eexists;exact V|exact V].
 - destruct (get (getlenv s) 903%Z) eqn:V;[exfalso;apply Ng;eexists;exact V|exact V].
Qed.
Lemma RUcur : (CurTid DHtid ** RUframe) ==> CurLINV V293_witness_li DHtid.
Proof.
 unfold RUframe. intros s H.
 unfold CurLINV. exists ([]:list logicvar). clear -H;sep auto.
Qed.
Lemma RUframe_good : GoodFrm RUframe.
Proof.
 unfold RUframe,DHbindings,LINV,V293_witness_li.
 cbn [GoodFrm]. repeat split;try (intros;exact I).
Qed.
Lemma RUframe_change : can_change_aop RUframe.
Proof.
 unfold RUframe,DHbindings,LINV,V293_witness_li.
 cbn [can_change_aop]. repeat split;try (intros;exact I).
 all: apply V293_tick_update_change;apply V293_owned_cells_good.
Qed.

Definition RUphysical d : asrt :=
  CurTid DHtid **
  (V293_owned_record_cells (V293_tick_wait_layout (RUnode d) RUreason RUmessage) **
  (V293_owned_task_records (del (RUtasks d) OwnershipWaiting) **
  (V293_owned_record_cells (V293_ready_cells 93%positive 92%positive 95%positive 16 0 RTentries) **
  (PV (96%positive,Int.zero) @ Tint32 |-> Vint32 (Int.repr 37) **
  (V293_owned_record_cell (V293_tick_pointer_cell 70%positive OwnershipWaiting) **
  (V293_owned_record_cells (V293_tick_wait_missing (RUnode d) RUreason TickNext) ** RUframe)))))).

Lemma RUphysical_good : forall d, GoodFrm (RUphysical d).
Proof.
 intro d. unfold RUphysical. cbn [GoodFrm].
 repeat split;try exact I;try exact RUframe_good;
  try apply V293_tick_cells_frame;try apply V293_tick_records_frame.

Qed.

Lemma RUspatial : forall d, DHstate (RUmemory d) |= RUphysical d.
Proof.
 intro d. unfold RUphysical.
 assert(Apart:OwnershipCellsSeparated (RUcells d)).
 { vm_compute. repeat split;intros a Member Rest;repeat destruct Member as[Member|Member];try contradiction;subst a;intuition discriminate. }
 assert(Typed:Forall(fun c=>let '(_,tp,v):=c in rule_type_val_match tp v=true)(RUcells d)).
 { repeat constructor;reflexivity. }
 pose proof (OwnershipCellsSpatial _ Apart Typed DHge TickLocal) as Cells.
 assert(Owned:DHstate (OwnershipCellsMemory(RUcells d)) |= V293_owned_record_cells(RUcells d)).
 { unfold DHstate. eapply TickCellsRebase;exact Cells. }
 assert(Both:DHstate(RUmemory d) |= V293_owned_record_cells(RUcells d) ** CurTid DHtid).
 { eapply DHstar;[ |exact Owned|apply DHcurrent_spatial].
   apply map_join_merge;apply map_disjoint;intros [b i].
   destruct(Pos.eq_dec b 94%positive)as[E|E].
   - subst b. left. apply OwnershipCellsOutside. vm_compute;intuition congruence.
   - right;left. apply V293_encoded_memory_outside;left;exact E. }
 assert(WithEmpty:DHstate(RUmemory d) |= DHbindings **
   (LINV V293_witness_li DHtid [] ** (V293_owned_record_cells(RUcells d) ** CurTid DHtid))).
 { eapply DHstar with(m1:=emp)(m2:=RUmemory d).
   - apply map_join_comm;apply map_join_emp.
   - apply DHbinding_spatial.
   - eapply DHstar with(m1:=emp)(m2:=RUmemory d).
     + apply map_join_comm;apply map_join_emp.
     + apply DHlinv_spatial.
     + exact Both. }
 assert(Deleted:del(RUtasks d)OwnershipWaiting=sig OwnershipReady(Int.repr 4,rdy,Vnull)).
 { apply TcbMod.extensionality. intro u.
   change(get(del(RUtasks d)OwnershipWaiting)u=get(sig OwnershipReady(Int.repr 4,rdy,Vnull))u).
   rewrite map_del_sem. match goal with |- context[if ?choice then _ else _]=>destruct choice as[E|E] end.
   - subst u. symmetry;apply map_get_sig';discriminate.
   - unfold RUtasks. rewrite map_get_set' by exact E. reflexivity. }
 rewrite Deleted. unfold V293_owned_task_records.
 change(DHstate(RUmemory d) |= CurTid DHtid **
  (V293_owned_record_cells(V293_tick_wait_layout(RUnode d)RUreason RUmessage) **
  ((V293_owned_task_record OwnershipReady(Int.repr 4)rdy Vnull ** Aemp) **
  (V293_owned_record_cells(V293_ready_cells 93%positive 92%positive 95%positive 16 0 RTentries) **
  (PV(96%positive,Int.zero)@Tint32|->Vint32(Int.repr 37) **
  (V293_owned_record_cell(V293_tick_pointer_cell 70%positive OwnershipWaiting) **
  (V293_owned_record_cells(V293_tick_wait_missing(RUnode d)RUreason TickNext) ** RUframe))))))).
 unfold RUcells in WithEmpty.
 unfold RUreason,RTentries in WithEmpty |- *.
 (* Lists are finite here. Expose exact cells, then repack just the other record. *)
 cbn [V293_tick_wait_layout V293_record_layout V293_ready_cells
  V293_priority_cells V293_tick_wait_missing V293_owned_record_cells app] in WithEmpty |- *.
 unfold RUframe. unfold V293_owned_task_record. sep normal. exists 4. exists 0.
 apply astar_l_apure_intro;[ |repeat split;reflexivity||lia].
 cbn [V293_record_layout V293_owned_record_cells app] .
 cbn [V293_tick_pointer_cell].
 unfold V293_owned_record_cell in WithEmpty |- *.
 clear -WithEmpty;sep auto.
Qed.

Lemma RUabstract : forall d,
 V293_target_wstate DHge TickLocal emp (RUabs d) |=
 V293_shared_fields DHtid (RUtasks d) (emp:EcbMod.map) (Int.repr 37).
Proof.
 intro d. unfold V293_shared_fields,RUabs,V293_shared_fixture_abs.
 repeat (eapply V293_target_wstate_star;[apply map_join_emp|
  apply map_join_merge;apply map_disjoint;intros key;destruct key;simpl;auto|
  split;reflexivity| ]). split;reflexivity.
Qed.

Theorem RUentry : forall d, RUstate d (RUmemory d) |= RUpre d.
Proof.
 intro d. pose proof (RUspatial d) as Physical.
 pose proof (goodfrm_prop _ _ _ _ _ _ (RUphysical_good d) Physical (fun _=>false)
  (false,[],[]) (spec_done None)) as Rebased.
 assert(Joint:V293_target_wstate DHge TickLocal (RUmemory d) (RUabs d) |=
  RUphysical d ** V293_shared_fields DHtid (RUtasks d) (emp:EcbMod.map) (Int.repr 37)).
 { eapply V293_target_wstate_star with(m1:=RUmemory d)(m2:=emp)(o1:=emp)(o2:=RUabs d).
   - apply map_join_emp.
   - apply map_join_comm;apply map_join_emp.
   - exact Rebased.
   - apply RUabstract. }
 assert(Good:GoodFrm(RUphysical d ** V293_shared_fields DHtid (RUtasks d) (emp:EcbMod.map) (Int.repr 37))).
 { cbn [GoodFrm]. split;[apply RUphysical_good|unfold V293_shared_fields;cbn [GoodFrm];repeat split;exact I]. }
 pose proof(goodfrm_prop _ _ _ _ _ _ Good Joint (fun _=>false)
   (false,[1],[false]) (spec_prim nil (V293_tick_wait_step OwnershipWaiting))) as Ready.
 assert(Control:RUstate d (RUmemory d) |= Aisr(fun _=>false) ** (Aie false **
  (Ais (1::nil) ** (Acs (false::nil) ** (RUphysical d **
  V293_shared_fields DHtid (RUtasks d) (emp:EcbMod.map) (Int.repr 37)))))).
 { apply astar_l_aisr_intro;[ | reflexivity]. apply astar_l_aie_intro;[ | reflexivity].
   apply astar_l_ais_intro;[ | reflexivity]. apply astar_l_acs_intro;[exact Ready|reflexivity]. }
 unfold RUpre. apply astar_l_aop'_intro;[ | reflexivity].
 unfold RUphysical,V293_tick_ready_wait_pre,V293_tick_wait_layout,RUnode in Control |- *.
 clear -Control. sep auto.
Qed.

Lemma RUnoabs : NoAbs V293_witness_li.
Proof.
  intros o O t H O' op. specialize (H op).
  destruct o as [[[[ge le] M] ir] aux].
  destruct H as [lg H].
  apply sat_split in H. destruct H as (m1 & m2 & o1 & o2 & JM & JO & HC & HR).
  assert (EO : o1=emp).
  { destruct HC as [tp [b HC]].
    apply sat_split in HC. destruct HC as (mb & mp & ob & optr & JM1 & JO1 & HB & HP).
    destruct HB as [b' [GE [BE [EM EB]]]]. destruct HP as [Points EP].
    change (ob=emp) in EB. change (optr=emp) in EP. subst ob optr.
    apply map_join_emp' in JO1. symmetry;exact JO1. }
  subst o1. exists lg.
  apply sat_split'. exists m1. exists m2. exists (emp:osabst). exists O'.
  repeat first [assumption | solve [apply map_join_comm;apply map_join_emp] | split].
  unfold LINV,V293_witness_li.
  apply sat_split'. exists (emp:mem). exists m2. exists (emp:osabst). exists O'.
  repeat first [solve [apply map_join_comm;apply map_join_emp] | split].
  - apply astar_l_aemp_intro. split;[apply V293_witness_li_good | repeat split;reflexivity].
Qed.

Theorem RUrules : forall Spec sd I r ri d,
 (0<=d<=Int.max_unsigned)%Z ->
 InfRules Spec sd V293_witness_li I r ri (RUpre d)
   (V293_tick_iteration 901%Z 902%Z 903%Z) (RUpost d) DHtid.
Proof.
 intros Spec sd I r ri d Bound. unfold RUpre,RUpost.
 apply V293_tick_ready_wait_iteration_hoare with(t:=RUnode d).
 - exact RUnoabs.
 - exact(RUvalid d Bound).
 - apply RUtask.
 - apply RUrel.
 - apply RUenv.
 - exact RUcur.
 - exact RUframe_good.
 - exact RUframe_change.
 - change (1<=INUM)%nat;unfold INUM;lia.
Qed.

Definition RUremainder d slot := V293_owned_record_cells(V293_tick_binding_extra(RUbinding d)) **
 (V293_owned_task_records(del(RUtasks d)OwnershipWaiting) **
 (V293_owned_record_cells(V293_priority_cells 95%positive 0%Z RTentries) **
 ((CurTid DHtid ** V293_shared_fields DHtid slot (emp:EcbMod.map) (Int.repr 37)) **
 (PV(96%positive,Int.zero)@Tint32|->Vint32(Int.repr 37) ** RUframe)))).
Definition RUbefore d := V293_tick_pointer_cell 70%positive OwnershipWaiting ::
 (V293_tick_task_cells(RUnode d)TickNext ++ V293_tick_bitmap_cells 92%positive 93%positive 1 16 0).
Definition RUafter d := V293_tick_pointer_cell 70%positive TickNext ::
 (V293_tick_task_cells(V293_tick_task_after(RUnode d))TickNext ++
 V293_tick_bitmap_cells 92%positive 93%positive
  (V293_tick_next_group(RUnode d)1) (V293_tick_next_lo(RUnode d)16) (V293_tick_next_hi(RUnode d)0)).
Definition RUupdated d := set(RUtasks d)OwnershipWaiting
 (Int.repr 6,V293_tick_wait_status RUreason d,RUmessage).
Definition RUout d M : RstateOP := (DHge,TickLocal,M,(fun _=>false),(false,[1],[false]),
 set(RUabs d)abstcblsid(abstcblist(RUupdated d)),END None).
Definition RUneutralized d M : RstateOP := (DHge,TickLocal,M,(fun _=>false),(false,[1],[false]),
 RUabs d,END None).
Definition RUexecution P ks d Mf := V293_local_steps P
 (curs(V293_tick_iteration 901%Z 902%Z 903%Z),(kenil,ks))
 ((DHge,TickLocal,RUmemory d),(fun _=>false),(false,[1],[false]))
 (curs(sskip None),(kenil,ks)) ((DHge,TickLocal,Mf),(fun _=>false),(false,[1],[false])).

Lemma RUowned_entry : forall d, (0<=d<=Int.max_unsigned)%Z ->
 RUstate d (RUmemory d) |= V293_owned_record_cells(RUbefore d) ** RUremainder d (RUtasks d).
Proof.
 intros d Bound. pose proof(RUentry d)as Held. unfold RUpre in Held.
 sep normal in Held. sep destruct Held.
 assert(Focused:RUstate d(RUmemory d) |= V293_tick_ready_wait_pre
  93%positive 92%positive 95%positive 96%positive DHtid(RUtasks d)(emp:EcbMod.map)
  (Int.repr 37)(RUnode d)RUreason RUmessage 0 16 0 RTentries 70%positive TickNext RUframe).
 { clear -Held;sep auto. }
 apply V293_tick_ready_wait_before_open in Focused;[ |exact(RUvalid d Bound)].
 change(RUstate d(RUmemory d) |= V293_rdy_raw_cells(RUbefore d)(RUremainder d(RUtasks d)))in Focused.
 apply V293_tick_raw_to_owned;[ |exact Focused].
 unfold RUbefore. cbn [V293_tick_task_cells V293_tick_bitmap_cells]. repeat constructor;reflexivity.
Qed.

Theorem RUliteral_execution : forall P ks sd d,
 (0<=d<=Int.max_unsigned)%Z -> exists Mf,
 RUexecution P ks d Mf /\
 spec_step sd (spec_prim nil(V293_tick_wait_step OwnershipWaiting))(RUabs d)(END None)
  (set(RUabs d)abstcblsid(abstcblist(RUupdated d))) /\
 RUstate d Mf |= V293_owned_record_cells(RUafter d) ** RUremainder d(RUtasks d) /\
 RUout d Mf |= V293_tick_ready_wait_post 93%positive 92%positive 95%positive 96%positive
   (RUnode d)RUreason RUmessage 70%positive TickNext RUframe.
Proof.
 intros P ks sd d Bound. pose proof(RUowned_entry d Bound)as Owned.
 assert(Opened:RUstate d(RUmemory d) |=
  V293_owned_record_cell(V293_tick_pointer_cell 70%positive OwnershipWaiting) **
  (V293_owned_record_cells(V293_tick_task_cells(RUnode d)TickNext) **
  (V293_owned_record_cells(V293_tick_bitmap_cells 92%positive 93%positive 1 16 0) **
   RUremainder d(RUtasks d)))).
 { unfold RUbefore in Owned. cbn [V293_tick_task_cells V293_tick_bitmap_cells
    V293_owned_record_cells app]in Owned |- *;clear -Owned;sep auto. }
 destruct(V293_tick_node_iteration_owned_execution P ks DHge TickLocal (RUmemory d)
   (fun _=>false) false [1] [false] (RUabs d)
   (spec_prim nil(V293_tick_wait_step OwnershipWaiting))
   901%Z 902%Z 903%Z 70%positive(RUnode d)TickNext 92%positive 93%positive 1 16 0
   (RUremainder d(RUtasks d)) eq_refl eq_refl eq_refl eq_refl eq_refl
   (proj1(RUvalid d Bound)) ltac:(lia) ltac:(lia) ltac:(lia) Opened)
   as(Mf&Exec&Returned).
 assert(Flat:RUstate d Mf |= V293_owned_record_cells(RUafter d) ** RUremainder d(RUtasks d)).
 { unfold RUafter. cbn [V293_tick_task_cells V293_tick_bitmap_cells
    V293_owned_record_cells app]in Returned |- *;clear -Returned;sep auto. }
 exists Mf. split;[exact Exec| ].
 split.
 - unfold RUupdated. eapply V293_tick_wait_transition.
   + exact(proj1(proj2(V293_shared_fields_get _ _ _ _ _ (RUabstract d)))).
   + apply map_get_set.
   + exact Bound.
 - split;[exact Flat| ].
   assert(Changed:(DHge,TickLocal,Mf,(fun _=>false),(false,[1],[false]),
     set(RUabs d)abstcblsid(abstcblist(RUupdated d)),spec_prim nil(V293_tick_wait_step OwnershipWaiting)) |=
     V293_owned_record_cells(RUafter d) ** RUremainder d(RUupdated d)).
   { assert(Slot:RUstate d Mf |= Aabsdata abstcblsid(abstcblist(RUtasks d)) **
       (V293_owned_record_cells(RUafter d) **
       (V293_owned_record_cells(V293_tick_binding_extra(RUbinding d)) **
       (V293_owned_task_records(del(RUtasks d)OwnershipWaiting) **
       (V293_owned_record_cells(V293_priority_cells 95%positive 0%Z RTentries) **
       ((CurTid DHtid ** (Aabsdata curtid(oscurt DHtid) **
        (Aabsdata absecblsid(absecblist(emp:EcbMod.map)) ** Aabsdata ostmid(ostm(Int.repr 37))))) **
       (PV(96%positive,Int.zero)@Tint32|->Vint32(Int.repr 37) ** RUframe))))))).
     { unfold RUremainder,V293_shared_fields in Flat;clear -Flat;sep auto. }
     apply V293_shared_replace_slot with(new:=abstcblist(RUupdated d))in Slot.
     unfold RUremainder,V293_shared_fields. clear -Slot;sep auto. }
   assert(Good:GoodFrm(V293_owned_record_cells(RUafter d) ** RUremainder d(RUupdated d))).
   { unfold RUremainder,V293_shared_fields. cbn [GoodFrm].
     repeat split;try exact I;try exact RUframe_good;
     try apply V293_tick_cells_frame;try apply V293_tick_records_frame. }
   pose proof(goodfrm_prop _ _ _ _ _ _ Good Changed (fun _=>false)(false,[1],[false])(END None))as Final.
   apply V293_tick_ready_wait_raw_close with(ct:=DHtid)(tasks:=RUtasks d)(es:=(emp:EcbMod.map))
    (n:=Int.repr 37)(lo:=16)(hi:=0)(entries:=RTentries).
   + exact(RUvalid d Bound).
   + apply RUtask.
   + apply RUrel.
   + apply V293_tick_owned_to_raw. exact Final.
Qed.

(* Project reads only for diagnostics; the production post retains every cell. *)
Definition RUobserved d := RUafter d ++ V293_tick_binding_extra(RUbinding d) ++
 [((96%positive,0%Z),Tint32,Vint32(Int.repr 37));
  ((90%positive,0%Z),Tint32,Vint32(Int.repr 99))].
Lemma RUobservations : forall d Mf,
 RUstate d Mf |= V293_owned_record_cells(RUafter d) ** RUremainder d(RUtasks d) ->
 forall a tp v, In (a,tp,v)(RUobserved d) -> load tp Mf a=Some v.
Proof.
 intros d Mf Held a tp v Member.
 assert(Cells:RUstate d Mf |= V293_owned_record_cells(RUobserved d) ** Atrue).
 { unfold RUobserved,RUremainder,RUframe,RUframecells in *.
   cbn [RUafter V293_tick_task_cells V293_tick_bitmap_cells
    V293_tick_binding_extra RUbinding V293_tick_record_extra RUreason
    V293_owned_record_cells app]in Held |- *.
   unfold V293_owned_record_cell in Held |- *. clear -Held;sep auto. }
 eapply V293_record_star_load_l with(s:=RUstate d Mf);[ |exact Cells].
 intros st H. eapply V293_owned_record_cells_load;[exact Member|exact H].
Qed.

Lemma RUreject_neutralized : forall Mf,
 load Tint8 Mf (93%positive,0%Z)=Some(V293_byteval 80) ->
 ~ RUneutralized 1 Mf |= V293_time_ready_core 93%positive 92%positive 95%positive 96%positive ** Atrue.
Proof.
 intros Mf Wrong Held.
 unfold V293_time_ready_core,V293_time_ready_fields in Held.
 sep normal in Held. sep destruct Held.
 assert(Fields:RUneutralized 1 Mf |= V293_shared_fields x0 x1 x2 x ** Atrue).
 { clear -Held;sep auto. }
 assert(Lookup:get(RUabs 1)abstcblsid=Some(abstcblist x1)).
 { eapply V293_star_abst_get_l with(s:=RUneutralized 1 Mf);[ |exact Fields].
   intros st H;exact(proj1(proj2(V293_shared_fields_get _ _ _ _ _ H))). }
 assert(Tasks:x1=RUtasks 1).
 { pose proof(proj1(proj2(V293_shared_fields_get _ _ _ _ _ (RUabstract 1))))as Fixed.
   change(get(RUabs 1)abstcblsid=Some(abstcblist(RUtasks 1)))in Fixed. congruence. }
 subst x1.
 assert(Ready:RUneutralized 1 Mf |= V293_ready_owned 93%positive 92%positive 95%positive(RUtasks 1) ** Atrue).
 { unfold V293_ready_payload in Held;clear -Held;sep auto. }
 destruct(V293_ready_owned_observation _ _ _ _ _ _ Ready)as(lo&hi&entries&Rel&Reads).
 destruct Rel as[Lo[Hi[Nonempty[Bitmap Table]]]]. destruct Reads as[Low Rest].
 change(load Tint8 Mf(93%positive,0%Z)=Some(V293_byteval lo))in Low.
 assert(E:lo=80)by(eapply RTbyte_injective;[exact Lo|lia|congruence]). subst lo.
 assert(Bit:V293_bitmap_ready 80 hi 6)by(vm_compute;auto).
 destruct(proj1(Bitmap 6 ltac:(lia)) Bit)as(t&m&Task).
 pose proof(RUonly_ready 1 6 t m ltac:(lia) Task)as[Bad _]. discriminate.
Qed.

Definition RUexpiry_reads Mf :=
 load Tint8 Mf(93%positive,0%Z)=Some(V293_byteval 80) /\
 load Tint8 Mf(93%positive,1%Z)=Some(V293_byteval 0) /\
 load Tint8 Mf(92%positive,0%Z)=Some(V293_byteval 1) /\
 load Tint32 Mf(41%positive,52%Z)=Some(Vint32(Int.repr 0)) /\
 load Tint8 Mf(41%positive,57%Z)=Some(V293_byteval 1) /\
 load(Tptr V293_tcb_type)Mf(70%positive,0%Z)=Some(Vptr TickNext) /\
 load(Tcom_ptr 411%Z)Mf(41%positive,36%Z)=Some(Vptr(72%positive,Int.repr 5)) /\
 load Tint32 Mf(96%positive,0%Z)=Some(Vint32(Int.repr 37)) /\
 load Tint32 Mf(90%positive,0%Z)=Some(Vint32(Int.repr 99)).
Lemma RUexpiry_observed : forall Mf,
 RUstate 1 Mf |= V293_owned_record_cells(RUafter 1) ** RUremainder 1(RUtasks 1) -> RUexpiry_reads Mf.
Proof.
 intros Mf Held. unfold RUexpiry_reads. repeat split;
 (eapply RUobservations;[exact Held|vm_compute;intuition]).
Qed.
Theorem RUexpiry_control : forall P ks (sd:ossched), exists Mf,
 RUexecution P ks 1 Mf /\ RUexpiry_reads Mf /\
 RUout 1 Mf |= V293_tick_ready_wait_post 93%positive 92%positive 95%positive 96%positive
   (RUnode 1)RUreason RUmessage 70%positive TickNext RUframe /\
 ~ RUneutralized 1 Mf |= V293_time_ready_core 93%positive 92%positive 95%positive 96%positive ** Atrue.
Proof.
 intros P ks sd. destruct(RUliteral_execution P ks sd 1 ltac:(change(0<=1<=4294967295)%Z;lia))
 as(Mf&Exec&Step&Owned&Post).
 pose proof(RUexpiry_observed Mf Owned)as Reads.
 exists Mf. split;[exact Exec| ]. split;[exact Reads| ]. split;[exact Post| ].
 apply RUreject_neutralized. exact(proj1 Reads).
Qed.

Theorem RUbranch_cases : forall P ks (sd:ossched) d, (d=0%Z \/ d=3%Z) -> exists Mf,
 RUexecution P ks d Mf /\
 get(RUupdated d)OwnershipWaiting=Some(Int.repr 6,wait RUreason(Int.repr(V293_tick_after_delay d)),RUmessage) /\
 load Tint8 Mf(93%positive,0%Z)=Some(V293_byteval 16) /\
 load Tint32 Mf(41%positive,52%Z)=Some(Vint32(Int.repr(V293_tick_after_delay d))) /\
 load Tint8 Mf(41%positive,57%Z)=Some(V293_byteval 0) /\
 load Tint32 Mf(96%positive,0%Z)=Some(Vint32(Int.repr 37)) /\
 load Tint32 Mf(90%positive,0%Z)=Some(Vint32(Int.repr 99)).
Proof.
 intros P ks sd d Cases. assert(Bound:(0<=d<=Int.max_unsigned)%Z).
 { change(0<=d<=4294967295)%Z;destruct Cases;subst;lia. }
 destruct(RUliteral_execution P ks sd d Bound)as(Mf&Exec&Step&Owned&Post).
 exists Mf. split;[exact Exec| ]. split.
 - unfold RUupdated,V293_tick_wait_status. destruct Cases;subst;apply map_get_set.
 - destruct Cases;subst;repeat split;(eapply RUobservations;[exact Owned|vm_compute;intuition]).
Qed.
Theorem RUresidual_expiry : V293_tick_residual_cells(RUbinding 1)TickNext =
 [((41%positive,28%Z),Tcom_ptr 410%Z,Vptr TickNext);
  ((41%positive,52%Z),Tint32,Vint32(Int.repr 0));
  ((41%positive,57%Z),Tint8,V293_byteval 1);
  ((41%positive,36%Z),Tcom_ptr 411%Z,Vptr(72%positive,Int.repr 5))].
Proof. vm_compute;reflexivity. Qed.
Theorem RUresidual_waiting : forall d, (d=0%Z \/ d=3%Z) ->
 V293_tick_residual_cells(RUbinding d)TickNext =
 [((41%positive,28%Z),Tcom_ptr 410%Z,Vptr TickNext)].
Proof. intros d[H|H];subst;vm_compute;reflexivity. Qed.
