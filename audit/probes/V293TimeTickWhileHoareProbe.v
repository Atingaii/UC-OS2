(* Nonempty mixed chain, literal byte entry with readonly current, legal
   interrupt stack, both IE values. Independent operational controls remain
   explicitly distinct from running the new RuleSem theorem. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickWhileHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLoop.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickDelayHoare.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFieldsHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBSuccessHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293NullBytes.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.audit.probes.V293TimeTickLoopProbe.
Require Import CertiOS.audit.probes.V293TimeTickDelayHoareProbe.
Require Import CertiOS.audit.probes.V293TimeTickTraversalProbe.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.certiucos.v293.code.V293OSTimeTick.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition WHframe := DHbindings ** (CurTid DHtid ** LINV V293_witness_li DHtid [] ** LoopFrame).
Definition WHcells := V293_tick_while_cells 70%positive [] LoopTasks LoopIdle 92%positive 93%positive 0 0 0.
Definition WHmemory := merge (OwnershipCellsMemory (WHcells++LoopFrameCells)) DHcurrent.
Definition WHstate enabled M : RstateOP :=
 (DHge,TickLocal,M,(fun _=>false),(enabled,[1],[false]),emp,spec_done None).
Definition WHpre enabled := V293_tick_while_resource (spec_done None) (fun _=>false) enabled [1] [false]
 70%positive [] LoopTasks LoopIdle 92%positive 93%positive 0 0 0 WHframe.
Definition WHpost enabled := V293_tick_while_resource (spec_done None) (fun _=>false) enabled [1] [false]
 70%positive (V293_tick_chain_cells LoopFinalTasks LoopIdle) [] LoopIdle 92%positive 93%positive 3 4 4 WHframe.

Lemma WHenv : forall st, st |= WHframe -> V293_tick_delay_env 901%Z 902%Z 903%Z
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
Lemma WHcur : WHframe ==> CurLINV V293_witness_li DHtid.
Proof.
 unfold WHframe. apply V293_star_CurLINV_r. intros st H.
 unfold CurLINV. exists ([]:list logicvar). clear -H. sep auto.
Qed.
Lemma WHframe_good : GoodFrm WHframe.
Proof.
 unfold WHframe,DHbindings,CurTid,LINV,V293_witness_li,LoopFrame,LoopFrameCells,
  V293_owned_record_cells,V293_owned_record_cell.
 cbn [GoodFrm]. repeat split;intros;exact I.
Qed.
Lemma WHvalid : Forall V293_tick_task_valid LoopTasks.
Proof.
 unfold LoopTasks.
 repeat (apply Forall_cons;[unfold V293_tick_task_valid;vm_compute;repeat split;try discriminate;lia| ]).
 apply Forall_nil.
Qed.

(* Construct exact writable bytes plus a separate readonly current cell. *)
Lemma WHspatial : DHstate WHmemory |= V293_owned_record_cells WHcells ** WHframe.
Proof.
 assert(Apart:OwnershipCellsSeparated (WHcells++LoopFrameCells)).
 { vm_compute. repeat split;intros a Member Rest;
   repeat destruct Member as [Member|Member];try contradiction;subst a;intuition discriminate. }
 assert(Valid:Forall (fun cell=>let '(_,tp,v):=cell in rule_type_val_match tp v=true)
   (WHcells++LoopFrameCells)).
 { repeat constructor;reflexivity. }
 pose proof (OwnershipCellsSpatial _ Apart Valid DHge TickLocal) as Owned.
 assert(Rebased:DHstate (OwnershipCellsMemory (WHcells++LoopFrameCells)) |=
   V293_owned_record_cells WHcells ** LoopFrame).
 { apply V293_tick_cells_append. unfold DHstate. eapply TickCellsRebase;exact Owned. }
 assert(Both:DHstate WHmemory |= (V293_owned_record_cells WHcells ** LoopFrame) ** CurTid DHtid).
 { eapply DHstar;[ |exact Rebased|apply DHcurrent_spatial].
   apply map_join_merge;apply map_disjoint;intros [b i].
   destruct (Pos.eq_dec b 94%positive) as [E|E].
   - subst b. left. apply OwnershipCellsOutside. vm_compute. intuition congruence.
   - right;left. apply V293_encoded_memory_outside;left;exact E. }
 assert(WithEmpty:DHstate WHmemory |= DHbindings ** (LINV V293_witness_li DHtid [] **
   ((V293_owned_record_cells WHcells ** LoopFrame) ** CurTid DHtid))).
 { eapply DHstar with (m1:=emp) (m2:=WHmemory).
   - apply map_join_comm;apply map_join_emp.
   - exact DHbinding_spatial.
   - eapply DHstar with (m1:=emp) (m2:=WHmemory).
     + apply map_join_comm;apply map_join_emp.
     + exact DHlinv_spatial.
     + exact Both. }
 unfold WHframe. clear -WithEmpty. sep auto.
Qed.
Theorem WHentry : forall enabled, WHstate enabled WHmemory |= WHpre enabled.
Proof.
 intros enabled. pose proof (DHowned_raw WHcells WHframe _ WHspatial) as Raw.
 assert(Good:GoodFrm(V293_rdy_raw_cells WHcells WHframe))
   by (apply V293_raw_cells_good_frame;exact WHframe_good).
 pose proof (goodfrm_prop _ _ _ _ _ _ Good Raw (fun _=>false)
   (enabled,[1],[false]) (spec_done None)) as Rebased.
 assert(Control:WHstate enabled WHmemory |= Aisr(fun _=>false) ** (Aie enabled **
   (Ais(1::nil) ** (Acs(false::nil) ** V293_rdy_raw_cells WHcells WHframe)))).
 { apply astar_l_aisr_intro;[ |reflexivity]. apply astar_l_aie_intro;[ |reflexivity].
   apply astar_l_ais_intro;[ |reflexivity]. apply astar_l_acs_intro;[exact Rebased|reflexivity]. }
 unfold WHpre,V293_tick_while_resource. apply astar_l_aop'_intro;[ |reflexivity].
 clear -Control. sep auto.
Qed.
Theorem WHrules : forall Spec sd I r ri enabled,
 InfRules Spec sd V293_witness_li I r ri (WHpre enabled)
 (swhile (V293_tick_guard 901%Z) (V293_tick_iteration 901%Z 902%Z 903%Z)) (WHpost enabled) DHtid.
Proof.
 intros. pose proof (V293_tick_while_hoare Spec sd V293_witness_li I r ri DHtid (spec_done None) WHframe
  901%Z 902%Z 903%Z 70%positive LoopTasks LoopIdle 92%positive 93%positive 0 0 0 enabled
  (fun _=>false) [1] [false] ltac:(change (4+50<=4294967295)%Z;lia)
  WHvalid ltac:(lia) ltac:(lia) ltac:(lia) WHenv WHcur WHframe_good
  ltac:(change (1<=INUM)%nat;unfold INUM;lia)) as Rules.
 exact Rules.
Qed.
Theorem WHnonvacuous : forall enabled,
 WHstate enabled WHmemory |= WHpre enabled /\
 (forall Spec sd I r ri, InfRules Spec sd V293_witness_li I r ri (WHpre enabled)
  (swhile (V293_tick_guard 901%Z) (V293_tick_iteration 901%Z 902%Z 903%Z)) (WHpost enabled) DHtid) /\
 WHstate enabled WHmemory |= Rv (V293_tick_guard 901%Z) @ Tint32 == Vint32 Int.one.
Proof.
 intros. split;[apply WHentry| ]. split;[intros;apply WHrules| ].
 eapply V293_tick_while_guard_resource with (remaining:=LoopTasks) (processed:=[])
  (g:=0) (lo:=0) (hi:=0);[exact WHenv| |exact WHvalid|apply WHentry].
 change (4+50<=4294967295)%Z;lia.
Qed.

(* This is the earlier operational while proof instantiated at the same
   literal bytes and legal control stack, not an evaluator premise of WHrules. *)
Lemma WHowned_entry : forall enabled, WHstate enabled WHmemory |=
 V293_tick_loop_owned 70%positive (V293_tick_head LoopTasks LoopIdle) LoopTasks LoopIdle
 92%positive 93%positive 0 0 0 WHframe.
Proof.
 intros enabled. assert(Good:GoodFrm(V293_owned_record_cells WHcells ** WHframe)).
 { cbn [GoodFrm]. split;[ |exact WHframe_good].
   unfold WHcells,V293_tick_while_cells,LoopTasks,V293_tick_chain_cells,V293_tick_task_cells,
    V293_tick_pointer_cell,V293_tick_head,V293_tick_task_pointer,V293_tick_bitmap_cells,
    V293_tick_idle_cell,V293_owned_record_cells,V293_owned_record_cell.
   cbn [GoodFrm]. repeat split;exact I. }
 pose proof (goodfrm_prop _ _ _ _ _ _ Good WHspatial (fun _=>false)
   (enabled,[1],[false]) (spec_done None)) as Owned.
 unfold WHcells,V293_tick_while_cells in Owned. cbn [app] in Owned.
 cbn [V293_owned_record_cells] in Owned. apply astar_assoc_elim in Owned.
 change (WHstate enabled WHmemory |= V293_owned_record_cell
   (V293_tick_pointer_cell 70%positive (V293_tick_head LoopTasks LoopIdle)) **
   (V293_owned_record_cells (V293_tick_chain_cells LoopTasks LoopIdle ++
    (V293_tick_bitmap_cells 92%positive 93%positive 0 0 0 ++ [V293_tick_idle_cell LoopIdle])) ** WHframe)) in Owned.
 unfold V293_tick_loop_owned.
 eapply astar_mono;[intros s H;exact H| |exact Owned]. intros st H.
 assert (Split:st |= (V293_owned_record_cells (V293_tick_chain_cells LoopTasks LoopIdle) **
   V293_owned_record_cells (V293_tick_bitmap_cells 92%positive 93%positive 0 0 0 ++
     [V293_tick_idle_cell LoopIdle])) ** WHframe).
 { eapply astar_mono;[ |intros s HS;exact HS|exact H].
   intros s HS. apply V293_tick_cells_append. exact HS. }
 assert (Split2:st |= (V293_owned_record_cells (V293_tick_chain_cells LoopTasks LoopIdle) **
   (V293_owned_record_cells (V293_tick_bitmap_cells 92%positive 93%positive 0 0 0) **
    V293_owned_record_cells (V293_tick_idle_cell LoopIdle :: nil))) ** WHframe).
 { eapply astar_mono;[ |intros s HS;exact HS|exact Split].
   intros s HS. eapply astar_mono;[intros s0 H0;exact H0| |exact HS].
   intros s0 H0. apply V293_tick_cells_append. exact H0. }
 cbn [V293_owned_record_cells] in Split2. clear -Split2. sep auto.
Qed.
Definition WHexecution P ks enabled Mf :=
 V293_local_steps P (curs(swhile(V293_tick_guard 901%Z)(V293_tick_iteration 901%Z 902%Z 903%Z)),(kenil,ks))
 ((DHge,TickLocal,WHmemory),(fun _=>false),(enabled,[1],[false]))
 (curs(sskip None),(kenil,ks)) ((DHge,TickLocal,Mf),(fun _=>false),(enabled,[1],[false])).
Theorem WHliteral_execution : forall P ks enabled, exists Mf,
 WHexecution P ks enabled Mf /\
 load (Tptr V293_tcb_type) Mf (70%positive,0%Z)=Some(Vptr LoopIdle) /\
 (forall a tp v, In (a,tp,v) LoopExpectedCells -> load tp Mf a=Some v) /\
 load Tint32 Mf (90%positive,0%Z)=Some(Vint32(Int.repr 99)) /\
 WHstate enabled Mf |= V293_tick_loop_owned 70%positive LoopIdle LoopFinalTasks LoopIdle
 92%positive 93%positive 3 4 4 WHframe.
Proof.
 intros. pose proof (V293_tick_while_owned_execution LoopTasks P ks DHge TickLocal WHmemory
  (fun _=>false) enabled [1] [false] emp (spec_done None) 901%Z 902%Z 903%Z
  70%positive LoopIdle 92%positive 93%positive 0 0 0 WHframe
  ltac:(apply map_get_sig) ltac:(vm_compute;reflexivity) ltac:(vm_compute;reflexivity)
  ltac:(vm_compute;reflexivity) ltac:(vm_compute;reflexivity)
  ltac:(change (4+50<=4294967295)%Z;lia) WHvalid ltac:(lia) ltac:(lia) ltac:(lia)
  (WHowned_entry enabled)) as Run.
 destruct Run as (Mf & Exec & Pointer & Returned).
 change (WHstate enabled Mf |= V293_tick_loop_owned 70%positive LoopIdle LoopFinalTasks LoopIdle
  92%positive 93%positive 3 4 4 WHframe) in Returned.
 exists Mf. split;[exact Exec| ]. split;[exact Pointer| ]. split.
 - intros a tp v Member. change (load tp (getmem(WHstate enabled Mf)) a=Some v).
   eapply V293_tick_loop_fields_load;[exact Member|exact Returned].
 - split;[ |exact Returned].
   change (load Tint32 (getmem(WHstate enabled Mf)) (90%positive,0%Z)=Some(Vint32(Int.repr 99))).
   unfold V293_tick_loop_owned in Returned.
   eapply V293_record_star_load_r;[ |exact Returned]. eapply V293_record_star_load_r.
   eapply V293_record_star_load_r. eapply V293_record_star_load_r.
   unfold WHframe. eapply V293_record_star_load_r. eapply V293_record_star_load_r.
   eapply V293_record_star_load_r. unfold LoopFrame. apply V293_owned_record_cells_load. left;reflexivity.
Qed.
Theorem WHwrong_pointer : forall P ks enabled, exists Mf,
 WHexecution P ks enabled Mf /\
 load (Tptr V293_tcb_type) Mf (70%positive,0%Z)=Some(Vptr LoopIdle) /\
 load (Tptr V293_tcb_type) Mf (70%positive,0%Z)<>Some(Vptr(V293_tick_head LoopTasks LoopIdle)) /\
 load Tint8 Mf (93%positive,1%Z)=Some(V293_byteval 4) /\
 load Tint32 Mf (90%positive,0%Z)=Some(Vint32(Int.repr 99)).
Proof.
 intros. destruct (WHliteral_execution P ks enabled) as (Mf&Exec&PtrEq&Loads&Canary&Returned).
 exists Mf. split;[exact Exec| ]. split;[exact PtrEq| ]. split.
 - rewrite PtrEq. vm_compute;discriminate.
 - split;[apply Loads;unfold LoopExpectedCells;vm_compute;tauto|exact Canary].
Qed.
Theorem WHwrong_row : forall P ks enabled, exists Mf,
 WHexecution P ks enabled Mf /\
 load Tint8 Mf (93%positive,1%Z)=Some(V293_byteval 4) /\
 load Tint8 Mf (93%positive,1%Z)<>Some(V293_byteval 0) /\
 load (Tptr V293_tcb_type) Mf (70%positive,0%Z)=Some(Vptr LoopIdle) /\
 load Tint32 Mf (90%positive,0%Z)=Some(Vint32(Int.repr 99)).
Proof.
 intros. destruct (WHliteral_execution P ks enabled) as (Mf&Exec&PtrEq&Loads&Canary&Returned).
 assert(RowEq:load Tint8 Mf (93%positive,1%Z)=Some(V293_byteval 4))
   by (apply Loads;unfold LoopExpectedCells;vm_compute;tauto).
 exists Mf. split;[exact Exec| ]. split;[exact RowEq| ]. split.
 - rewrite RowEq. vm_compute;discriminate.
 - split;assumption.
Qed.

Theorem WHguard_exit : forall P ks enabled, exists Mf,
 WHexecution P ks enabled Mf /\
 evalval (V293_tick_guard 901%Z) (DHge,TickLocal,Mf)=Some(Vint32 Int.zero) /\
 load Tint8 Mf (93%positive,1%Z)=Some(V293_byteval 4) /\
 load Tint32 Mf (90%positive,0%Z)=Some(Vint32(Int.repr 99)).
Proof.
 intros. destruct (WHliteral_execution P ks enabled) as (Mf&Exec&PtrEq&Loads&Canary&Returned).
 assert (Read:load Tint8 Mf (87%positive,54%Z)=Some(V293_byteval 12)).
 { apply Loads. unfold LoopExpectedCells. vm_compute;tauto. }
 exists Mf. split;[exact Exec| ]. split.
 - exact (V293_tick_guard_eval DHge TickLocal Mf 901%Z 70%positive 87%positive 4%Z 12
     ltac:(apply map_get_sig) PtrEq ltac:(lia)
     ltac:(change (4+50<=4294967295)%Z;lia) ltac:(lia) Read).
 - split;[apply Loads;unfold LoopExpectedCells;vm_compute;tauto|exact Canary].
Qed.

Print Assumptions WHentry.
Print Assumptions WHrules.
Print Assumptions WHnonvacuous.
Print Assumptions WHliteral_execution.
Print Assumptions WHwrong_pointer.
Print Assumptions WHwrong_row.

Print Assumptions WHguard_exit.
