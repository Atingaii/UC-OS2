(* Literal post-hook entry and independent operational controls. No claim
   of initialized kernel reachability or execution of RuleSem is made. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickPostHookHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickSuffix.
Require Import CertiOS.audit.probes.V293TimeTickWhileHoareProbe.
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


Definition PHge : env := set (set (set DHge 1001%Z (101%positive,Tint32))
 1002%Z (102%positive,Tint8)) 1003%Z (103%positive,Tptr V293_tcb_type).
Definition PHbindings := DHbindings //\\ A_notin_lenv 1001%Z //\\
 Agvarenv 1001%Z Tint32 (101%positive,0%Z) //\\ A_notin_lenv 1002%Z //\\
 Agvarenv 1002%Z Tint8 (102%positive,0%Z) //\\ A_notin_lenv 1003%Z //\\
 Agvarenv 1003%Z (Tptr V293_tcb_type) (103%positive,0%Z).
Definition PHframe := PHbindings ** (CurTid DHtid ** LINV V293_witness_li DHtid [] ** LoopFrame).
Definition PHcells tick run := V293_tick_post_cells 101%positive tick 102%positive run 103%positive
 (V293_tick_head LoopTasks LoopIdle) 70%positive LoopIdle LoopTasks LoopIdle 92%positive 93%positive 0 0 0.
Definition PHmemory tick run := merge (OwnershipCellsMemory (PHcells tick run++LoopFrameCells)) DHcurrent.
Definition PHstate enabled M : RstateOP :=
 (PHge,TickLocal,M,(fun _=>false),(enabled,[1],[false]),emp,spec_done None).
Definition PHpre tick run enabled := V293_tick_post_resource (spec_done None) (fun _=>false) enabled [1] [false]
 101%positive tick 102%positive run 103%positive (V293_tick_head LoopTasks LoopIdle)
 70%positive LoopIdle LoopTasks LoopIdle 92%positive 93%positive 0 0 0 PHframe.
Definition PHpost tick run enabled := V293_tick_post_result (spec_done None) (fun _=>false) enabled [1] [false]
 101%positive (Int.add tick Int.one) 102%positive run 103%positive (V293_tick_head LoopTasks LoopIdle)
 70%positive LoopIdle LoopTasks LoopIdle 92%positive 93%positive 0 0 0 PHframe.

Lemma PHenv : forall st, st |= PHframe -> V293_tick_post_env 901%Z 902%Z 903%Z 1001%Z 1002%Z 1003%Z
 70%positive 93%positive 92%positive 101%positive 102%positive 103%positive (getgenv st)(getlenv st).
Proof.
 intros st Held. eapply V293_star_env_l;[ |exact Held].
 intros s (Delay&Nn&Gn&Nu&Gu&Nh&Gh).
 destruct Delay as (Bc&Nr&Gr&Ng&Gg).
 destruct Bc as [b [B [E _]]];inversion E;subst b.
 destruct Gr as [br [R [Er _]]];inversion Er;subst br.
 destruct Gg as [bg [G [Eg _]]];inversion Eg;subst bg.
 destruct Gn as [bn [Gn [En _]]];inversion En;subst bn.
 destruct Gu as [bu [Gu [Eu _]]];inversion Eu;subst bu.
 destruct Gh as [bh [Gh [Eh _]]];inversion Eh;subst bh.
 destruct Nr as [Nr _]. destruct Ng as [Ng _].
 destruct Nn as [Nn _]. destruct Nu as [Nu _]. destruct Nh as [Nh _].
 unfold V293_tick_post_env,V293_tick_delay_env. repeat split;try assumption;
 match goal with
 | N : ~ indom ?le ?x |- get ?le ?x=None =>
   destruct (get le x) eqn:V;[exfalso;apply N;eexists;exact V|exact V]
 end.
Qed.
Lemma PHcur : PHframe ==> CurLINV V293_witness_li DHtid.
Proof.
 unfold PHframe. apply V293_star_CurLINV_r. intros st H.
 unfold CurLINV. exists ([]:list logicvar). clear -H. sep auto.
Qed.
Lemma PHframe_good : GoodFrm PHframe.
Proof.
 unfold PHframe,PHbindings,DHbindings,CurTid,LINV,V293_witness_li,LoopFrame,LoopFrameCells,
  V293_owned_record_cells,V293_owned_record_cell.
 cbn [GoodFrm]. repeat split;intros;exact I.
Qed.
Lemma PHstar : forall enabled m1 m2 m p q,
 join m1 m2 m -> PHstate enabled m1 |= p -> PHstate enabled m2 |= q -> PHstate enabled m |= p ** q.
Proof.
 intros. apply sat_split'. exists m1. exists m2. exists (emp:osabst). exists (emp:osabst).
 split;[assumption| ]. split;[apply map_join_emp| ]. split;assumption.
Qed.
Lemma PHbinding_spatial : forall enabled, PHstate enabled emp |= PHbindings.
Proof.
 intros. unfold PHbindings,DHbindings. repeat split.
 - exists 70%positive. split;[apply map_get_sig| ]. repeat split;reflexivity.
 - intros [v E];vm_compute in E;discriminate.
 - exists 93%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
 - intros [v E];vm_compute in E;discriminate.
 - exists 92%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
 - intros [v E];vm_compute in E;discriminate.
 - exists 101%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
 - intros [v E];vm_compute in E;discriminate.
 - exists 102%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
 - intros [v E];vm_compute in E;discriminate.
 - exists 103%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
Qed.
Lemma PHcurrent_spatial : forall enabled, PHstate enabled DHcurrent |= CurTid DHtid.
Proof.
 intros. exists Tvoid. exists 94%positive. eapply PHstar with (m1:=emp) (m2:=DHcurrent).
 - apply map_join_comm;apply map_join_emp.
 - exists 94%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Lemma PHlinv_spatial : forall enabled, PHstate enabled emp |= LINV V293_witness_li DHtid [].
Proof.
 intros. unfold LINV. apply astar_comm. apply astar_l_apure_intro.
 - split;reflexivity.
 - apply V293_witness_li_good.
Qed.
Lemma PHspatial : forall tick run enabled, run<256 ->
 PHstate enabled (PHmemory tick run) |= V293_owned_record_cells (PHcells tick run) ** PHframe.
Proof.
 intros tick run enabled Range.
 assert(Apart:OwnershipCellsSeparated (PHcells tick run++LoopFrameCells)).
 { vm_compute. repeat split;intros a Member Rest;
   repeat destruct Member as [Member|Member];try contradiction;subst a;intuition discriminate. }
 assert(Valid:Forall (fun cell=>let '(_,tp,v):=cell in rule_type_val_match tp v=true)
   (PHcells tick run++LoopFrameCells)).
 { apply Forall_cons;[reflexivity| ]. apply Forall_cons;[apply V293_byte_type;exact Range| ].
   repeat constructor;reflexivity. }
 pose proof(OwnershipCellsSpatial _ Apart Valid PHge TickLocal) as Owned.
 assert(Rebased:PHstate enabled (OwnershipCellsMemory (PHcells tick run++LoopFrameCells)) |=
   V293_owned_record_cells (PHcells tick run) ** LoopFrame).
 { apply V293_tick_cells_append. unfold PHstate. eapply TickCellsRebase;exact Owned. }
 assert(Both:PHstate enabled (PHmemory tick run) |=
   (V293_owned_record_cells (PHcells tick run) ** LoopFrame) ** CurTid DHtid).
 { eapply PHstar;[ |exact Rebased|apply PHcurrent_spatial].
   apply map_join_merge;apply map_disjoint;intros [b i].
   destruct(Pos.eq_dec b 94%positive) as [E|E].
   - subst b. left. apply OwnershipCellsOutside. vm_compute. intuition congruence.
   - right;left. apply V293_encoded_memory_outside;left;exact E. }
 assert(WithEmpty:PHstate enabled (PHmemory tick run) |= PHbindings ** (LINV V293_witness_li DHtid [] **
   ((V293_owned_record_cells (PHcells tick run) ** LoopFrame) ** CurTid DHtid))).
 { eapply PHstar with (m1:=emp) (m2:=PHmemory tick run).
   - apply map_join_comm;apply map_join_emp.
   - apply PHbinding_spatial.
   - eapply PHstar with (m1:=emp) (m2:=PHmemory tick run).
     + apply map_join_comm;apply map_join_emp.
     + apply PHlinv_spatial.
     + exact Both. }
 unfold PHframe. clear -WithEmpty. sep auto.
Qed.
Theorem PHentry : forall tick run enabled, run<256 -> PHstate enabled (PHmemory tick run) |= PHpre tick run enabled.
Proof.
 intros tick run enabled Range.
 pose proof(DHowned_raw (PHcells tick run) PHframe _ (PHspatial tick run enabled Range)) as Raw.
 assert(Control:PHstate enabled (PHmemory tick run) |= Aisr(fun _=>false) ** (Aie enabled **
   (Ais(1::nil) ** (Acs(false::nil) ** V293_rdy_raw_cells (PHcells tick run) PHframe)))).
 { apply astar_l_aisr_intro;[ |reflexivity]. apply astar_l_aie_intro;[ |reflexivity].
   apply astar_l_ais_intro;[ |reflexivity]. apply astar_l_acs_intro;[exact Raw|reflexivity]. }
 unfold PHpre,V293_tick_post_resource. apply astar_l_aop'_intro;[ |reflexivity].
 clear -Control. sep auto.
Qed.
Theorem PHrules : forall Spec sd I r ri tick run enabled, run<256 ->
 InfRules Spec sd V293_witness_li I r ri (PHpre tick run enabled)
 (V293_tick_post_hook 901%Z 902%Z 903%Z 1001%Z 1002%Z 1003%Z) (PHpost tick run enabled) DHtid.
Proof.
 intros. apply V293_tick_post_hook_hoare;
 [change (4+50<=4294967295)%Z;lia|exact WHvalid|assumption|lia|lia|lia|exact PHenv|exact PHcur|exact PHframe_good| ].
 change (1<=INUM)%nat;unfold INUM;lia.
Qed.
Theorem PHnonvacuous : forall tick run enabled, run<256 ->
 PHstate enabled (PHmemory tick run) |= PHpre tick run enabled /\
 (forall Spec sd I r ri, InfRules Spec sd V293_witness_li I r ri (PHpre tick run enabled)
  (V293_tick_post_hook 901%Z 902%Z 903%Z 1001%Z 1002%Z 1003%Z) (PHpost tick run enabled) DHtid).
Proof. intros. split;[apply PHentry;assumption|intros;apply PHrules;assumption]. Qed.

Local Lemma PHowned_suffix : forall bn tick bu run bh head bc scan tasks idle bg br g lo hi R,
 V293_owned_record_cells (V293_tick_post_cells bn tick bu run bh head bc scan tasks idle bg br g lo hi) ** R ==>
 V293_tick_suffix_owned bn tick bu run bh head bc scan tasks idle bg br g lo hi R.
Proof.
 intros bn tick bu run bh head bc scan tasks idle bg br g lo hi R st H.
 unfold V293_tick_suffix_owned,V293_tick_loop_owned.
 change (st |= (V293_owned_record_cell ((bn,0%Z),Tint32,Vint32 tick) **
  (V293_owned_record_cell ((bu,0%Z),Tint8,V293_byteval run) **
   (V293_owned_record_cell ((bh,0%Z),Tptr V293_tcb_type,Vptr head) **
    (V293_owned_record_cell (V293_tick_pointer_cell bc scan) **
     V293_owned_record_cells (V293_tick_chain_cells tasks idle ++
      (V293_tick_bitmap_cells bg br g lo hi ++ [V293_tick_idle_cell idle])))))) ** R) in H.
 apply astar_assoc_elim in H. eapply astar_mono;[intros s HS;exact HS| |exact H].
 intros st1 H1. apply astar_assoc_elim in H1. eapply astar_mono;[intros s HS;exact HS| |exact H1].
 intros st2 H2. apply astar_assoc_elim in H2. eapply astar_mono;[intros s HS;exact HS| |exact H2].
 intros st3 H3. apply astar_assoc_elim in H3. eapply astar_mono;[intros s HS;exact HS| |exact H3].
 intros st4 H4.
 assert(Split:st4 |= (V293_owned_record_cells(V293_tick_chain_cells tasks idle) **
   V293_owned_record_cells(V293_tick_bitmap_cells bg br g lo hi ++ [V293_tick_idle_cell idle])) ** R).
 { eapply astar_mono;[ |intros s HS;exact HS|exact H4]. intros s HS;apply V293_tick_cells_append;exact HS. }
 assert(Split2:st4 |= (V293_owned_record_cells(V293_tick_chain_cells tasks idle) **
   (V293_owned_record_cells(V293_tick_bitmap_cells bg br g lo hi) **
    V293_owned_record_cells(V293_tick_idle_cell idle::nil))) ** R).
 { eapply astar_mono;[ |intros s HS;exact HS|exact Split]. intros s HS.
   eapply astar_mono;[intros s0 H0;exact H0| |exact HS].
   intros s0 H0;apply V293_tick_cells_append;exact H0. }
 cbn [V293_owned_record_cells] in Split2. clear -Split2. sep auto.
Qed.
Lemma PHowned_entry : forall tick run enabled, run<256 ->
 PHstate enabled (PHmemory tick run) |= V293_tick_suffix_owned 101%positive tick 102%positive run
 103%positive (V293_tick_head LoopTasks LoopIdle) 70%positive LoopIdle LoopTasks LoopIdle
 92%positive 93%positive 0 0 0 PHframe.
Proof. intros. apply PHowned_suffix. apply PHspatial;assumption. Qed.


(* Neutralize only head assignment: the original guard at the unchanged
   initial scan=idle is false. Thus its loop cannot reach the six tasks. *)
Theorem PHguard_before_head : forall tick run (enabled : ie), run<256 ->
 evalval(V293_tick_guard 901%Z)(PHge,TickLocal,PHmemory tick run)=Some(Vint32 Int.zero).
Proof.
 intros tick run enabled Range.
 pose proof(DHowned_raw (PHcells tick run) PHframe _ (PHspatial tick run enabled Range)) as Raw.
 assert(Pointer:load (Tptr V293_tcb_type) (PHmemory tick run) (70%positive,0%Z)=Some(Vptr LoopIdle)).
 { eapply (V293_rdy_raw_load (PHcells tick run) PHframe (70%positive,0%Z)
   (Tptr V293_tcb_type) (Vptr LoopIdle) (PHstate enabled (PHmemory tick run)));
   [unfold PHcells,V293_tick_post_cells,V293_tick_post_globals;cbn [app In];tauto|reflexivity|exact Raw]. }
 assert(Idle:load Tint8 (PHmemory tick run) (87%positive,54%Z)=Some(V293_byteval 12)).
 { eapply (V293_rdy_raw_load (PHcells tick run) PHframe (87%positive,54%Z)
   Tint8 (V293_byteval 12) (PHstate enabled (PHmemory tick run)));
   [unfold PHcells,V293_tick_post_cells;apply in_or_app;right;right;apply in_or_app;right;
    apply in_or_app;right;left;reflexivity|reflexivity|exact Raw]. }
 exact(V293_tick_guard_eval PHge TickLocal (PHmemory tick run) 901%Z 70%positive 87%positive 4%Z 12
   ltac:(apply map_get_sig) Pointer ltac:(lia) ltac:(change (4+50<=4294967295)%Z;lia) ltac:(lia) Idle).
Qed.

Definition PHexecution P ks tick run enabled Mf :=
 V293_local_steps P (curs(V293_tick_post_hook 901%Z 902%Z 903%Z 1001%Z 1002%Z 1003%Z),(kenil,ks))
 ((PHge,TickLocal,PHmemory tick run),(fun _=>false),(enabled,[1],[false]))
 (curs(sskip None),(kenil,ks)) ((PHge,TickLocal,Mf),(fun _=>false),(enabled,[1],[false])).
Definition PHexpectedcells run := V293_tick_pointer_cell 70%positive LoopIdle ::
 (V293_tick_chain_cells (if Nat.eqb run 1 then LoopFinalTasks else LoopTasks) LoopIdle ++
  (V293_tick_bitmap_cells 92%positive 93%positive (if Nat.eqb run 1 then 3 else 0)
   (if Nat.eqb run 1 then 4 else 0) (if Nat.eqb run 1 then 4 else 0) ++ [V293_tick_idle_cell LoopIdle])).

(* This independently runs the existing operational theorem from the SAME
   literal entry and legal stack; it is not running the new RuleSem proof. *)
Theorem PHliteral_execution : forall P ks tick run enabled, run<256 -> exists Mf,
 PHexecution P ks tick run enabled Mf /\
 load Tint32 Mf (101%positive,0%Z)=Some(Vint32(Int.add tick Int.one)) /\
 load (Tptr V293_tcb_type) Mf (70%positive,0%Z)=Some(Vptr LoopIdle) /\
 (forall a tp v, In (a,tp,v) (PHexpectedcells run) -> load tp Mf a=Some v) /\
 load Tint32 Mf (90%positive,0%Z)=Some(Vint32(Int.repr 99)).
Proof.
 intros P ks tick run enabled Range.
 pose proof(V293_tick_post_hook_owned_execution LoopTasks P ks PHge TickLocal (PHmemory tick run)
  (fun _=>false) enabled [1] [false] emp (spec_done None) 901%Z 902%Z 903%Z 1001%Z 1002%Z 1003%Z
  70%positive 101%positive 102%positive 103%positive LoopIdle LoopIdle 92%positive 93%positive tick run 0 0 0 PHframe
  ltac:(apply map_get_sig) ltac:(vm_compute;reflexivity) ltac:(vm_compute;reflexivity)
  ltac:(vm_compute;reflexivity) ltac:(vm_compute;reflexivity)
  ltac:(vm_compute;reflexivity) ltac:(vm_compute;reflexivity)
  ltac:(vm_compute;reflexivity) ltac:(vm_compute;reflexivity)
  ltac:(vm_compute;reflexivity) ltac:(vm_compute;reflexivity)
  ltac:(change (4+50<=4294967295)%Z;lia) WHvalid Range ltac:(lia) ltac:(lia) ltac:(lia)
  (PHowned_entry tick run enabled Range)) as Run.
 destruct Run as (Mf&Exec&Clock&Pointer&Returned).
 assert(Fields:forall a tp v, In(a,tp,v)(PHexpectedcells run) -> load tp Mf a=Some v).
 { intros a tp v Member.
   change (load tp (getmem(PHstate enabled Mf)) a=Some v).
   unfold V293_tick_suffix_owned in Returned.
   eapply V293_record_star_load_r;[ |exact Returned]. eapply V293_record_star_load_r.
   eapply V293_record_star_load_r. intros s HS.
   eapply V293_tick_loop_fields_load;[ |exact HS].
   unfold PHexpectedcells in Member. destruct(Nat.eqb run 1);exact Member. }
 assert(Canary:load Tint32 Mf (90%positive,0%Z)=Some(Vint32(Int.repr 99))).
 { change (load Tint32(getmem(PHstate enabled Mf))(90%positive,0%Z)=Some(Vint32(Int.repr 99))).
   unfold V293_tick_suffix_owned,V293_tick_loop_owned in Returned.
   eapply V293_record_star_load_r;[ |exact Returned].
   do 6 eapply V293_record_star_load_r.
   unfold PHframe. eapply V293_record_star_load_r. eapply V293_record_star_load_r.
   eapply V293_record_star_load_r. unfold LoopFrame. apply V293_owned_record_cells_load;left;reflexivity. }
 exists Mf. split;[exact Exec| ]. split;[exact Clock| ]. split.
 - destruct(Nat.eqb run 1);exact Pointer.
 - split;assumption.
Qed.

Lemma PHuint32_wrap : Int.add(Int.repr 4294967295)Int.one=Int.zero.
Proof.
 change (Int.repr 4294967296=Int.repr 0).
 apply Int.eqm_samerepr. unfold Int.eqm,Int.eqmod. exists 1%Z;reflexivity.
Qed.
Theorem PHrunning_wrapped : forall P ks enabled, exists Mf,
 PHexecution P ks (Int.repr 4294967295) 1 enabled Mf /\
 load Tint32 Mf (101%positive,0%Z)=Some(Vint32 Int.zero) /\
 load Tint32 Mf (82%positive,56%Z)=Some(Vint32(Int.repr 2)) /\
 load Tint8 Mf (92%positive,0%Z)=Some(V293_byteval 3) /\
 load Tint32 Mf (90%positive,0%Z)=Some(Vint32(Int.repr 99)).
Proof.
 intros. destruct(PHliteral_execution P ks (Int.repr 4294967295) 1 enabled ltac:(lia)) as (Mf&Exec&Clock&Pointer&Fields&Canary).
 exists Mf. split;[exact Exec| ]. split;[rewrite <- PHuint32_wrap;exact Clock| ].
 split;[apply Fields;unfold PHexpectedcells;vm_compute;tauto| ].
 split;[apply Fields;unfold PHexpectedcells;vm_compute;tauto|exact Canary].
Qed.
Theorem PHstopped_wrapped : forall P ks enabled run, (run=0 \/ run=255) -> exists Mf,
 PHexecution P ks (Int.repr 4294967295) run enabled Mf /\
 load Tint32 Mf (101%positive,0%Z)=Some(Vint32 Int.zero) /\
 load Tint32 Mf (82%positive,56%Z)=Some(Vint32(Int.repr 3)) /\
 load Tint8 Mf (92%positive,0%Z)=Some(V293_byteval 0) /\
 load Tint32 Mf (90%positive,0%Z)=Some(Vint32(Int.repr 99)).
Proof.
 intros P ks enabled run Stopped. assert(Range:run<256) by lia.
 destruct(PHliteral_execution P ks (Int.repr 4294967295) run enabled Range) as (Mf&Exec&Clock&Pointer&Fields&Canary).
 exists Mf. split;[exact Exec| ]. split;[rewrite <- PHuint32_wrap;exact Clock| ].
 assert(StoppedFlag:Nat.eqb run 1=false) by (apply Nat.eqb_neq;lia).
 unfold PHexpectedcells in Fields. rewrite StoppedFlag in Fields.
 split;[apply Fields;vm_compute;tauto| ]. split;[apply Fields;vm_compute;tauto|exact Canary].
Qed.

(* Single-field wrong claims are refuted on the actual Mf, without a store,
   deletion or a fabricated output. The other observations remain correct. *)
Theorem PHwrong_clock_stopped : forall P ks enabled, exists Mf,
 PHexecution P ks (Int.repr 4294967295) 0 enabled Mf /\
 load Tint32 Mf (101%positive,0%Z)<>Some(Vint32(Int.repr 4294967295)) /\
 load (Tptr V293_tcb_type) Mf (70%positive,0%Z)=Some(Vptr LoopIdle) /\
 load Tint8 Mf (92%positive,0%Z)=Some(V293_byteval 0) /\
 load Tint32 Mf (90%positive,0%Z)=Some(Vint32(Int.repr 99)).
Proof.
 intros. destruct(PHliteral_execution P ks (Int.repr 4294967295) 0 enabled ltac:(lia)) as (Mf&Exec&Clock&Pointer&Fields&Canary).
 exists Mf. split;[exact Exec| ]. split.
 - rewrite Clock,PHuint32_wrap;vm_compute;discriminate.
 - split;[exact Pointer| ]. split;[apply Fields;unfold PHexpectedcells;vm_compute;tauto|exact Canary].
Qed.
Theorem PHwrong_skipped_loop : forall P ks enabled, exists Mf,
 PHexecution P ks (Int.repr 4294967295) 1 enabled Mf /\
 load Tint32 Mf (82%positive,56%Z)<>Some(Vint32(Int.repr 3)) /\
 load Tint32 Mf (101%positive,0%Z)=Some(Vint32 Int.zero) /\
 load Tint8 Mf (92%positive,0%Z)=Some(V293_byteval 3) /\
 load Tint32 Mf (90%positive,0%Z)=Some(Vint32(Int.repr 99)).
Proof.
 intros. destruct(PHrunning_wrapped P ks enabled) as (Mf&Exec&Clock&Delay&Group&Canary).
 exists Mf. split;[exact Exec| ]. split.
 - rewrite Delay;vm_compute;discriminate.
 - split;[exact Clock| ]. split;assumption.
Qed.

Print Assumptions PHentry.
Print Assumptions PHrules.
Print Assumptions PHnonvacuous.
Print Assumptions PHliteral_execution.
Print Assumptions PHrunning_wrapped.
Print Assumptions PHstopped_wrapped.
Print Assumptions PHwrong_clock_stopped.
Print Assumptions PHwrong_skipped_loop.

Print Assumptions PHguard_before_head.
