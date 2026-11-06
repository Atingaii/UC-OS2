(* Interrupt-exit dispatch witnesses and prospective single-factor controls.
   These are local existence witnesses, not initialization reachability. *)
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

(* Independent nonempty resources. Only nesting / current priority varies;
   current=6 is a comparison control, not a consistent current-TCB claim. *)
Definition DXct := OwnershipReady.
Definition DXge : env := set(set(set(set RHge
 108%Z(94%positive,Tint8))109%Z(95%positive,Tint8))
 110%Z(96%positive,Tint8))111%Z(97%positive,Tint32).
Definition DXbase_state M := V293_target_wstate DXge RTle M(RIabstract DXct).
Definition DXextras n nc : list V293_record_cell :=
 [((94%positive,0%Z),Tint8,V293_byteval n);
  ((95%positive,0%Z),Tint8,V293_byteval 0);
  ((96%positive,0%Z),Tint8,V293_byteval nc);
  ((97%positive,0%Z),Tint32,Vint32(Int.repr 19))].
Definition DXextra n nc := OwnershipCellsMemory(DXextras n nc).
Definition DXmemory n nc := merge(RHmemory DXct)(DXextra n nc).
Definition DXstate M := DXbase_state M.
Definition DXframe nc :=
 V293_owned_record_cell((96%positive,0%Z),Tint8,V293_byteval nc) **
 (V293_owned_record_cell((97%positive,0%Z),Tint32,Vint32(Int.repr 19)) ** RCframe).
Definition DXtail := sif(V293_OSSched_different 103%Z 110%Z)
 (sseq(V293_OSSched_increment 111%Z)(sseq(sskip None)(scall 112%Z nil)))(sskip None).
Definition DXdispatch := V293_OSIntExit_dispatch 105%Z 103%Z 106%Z 110%Z 111%Z 107%Z 112%Z.
Definition DXmiddle := V293_OSIntExit_nesting_dispatch 108%Z 109%Z DXdispatch.
Lemma DXbase_entry : forall ct,
  V293_target_wstate DXge RTle (RTexec_memory ct) (RIabstract ct) |=
    (V293_owned_record_cell ((90%positive,0%Z),Tint8,V293_byteval 99) **
     V293_owned_record_cell ((91%positive,0%Z),Tint8,V293_byteval 88)) **
    (SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) ct **
     V293_read_bytes 92%positive 0%Z V293_ready_table).
Proof.
  intro ct.
  assert (Outputs : V293_target_wstate DXge RTle RToutputs emp |=
    V293_owned_record_cell ((90%positive,0%Z),Tint8,V293_byteval 99) **
    V293_owned_record_cell ((91%positive,0%Z),Tint8,V293_byteval 88)).
  { pose proof (OwnershipCellsSpatial RToutput_cells ltac:(vm_compute;repeat split;intros;intuition congruence)
      ltac:(repeat constructor;vm_compute;reflexivity) DXge RTle) as Out.
    cbn [RToutput_cells V293_owned_record_cells] in Out. sep auto. }
  assert (First : V293_target_wstate DXge RTle (RTwith_outputs ct) (RIabstract ct) |=
    SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) ct **
    (V293_owned_record_cell ((90%positive,0%Z),Tint8,V293_byteval 99) **
     V293_owned_record_cell ((91%positive,0%Z),Tint8,V293_byteval 88))).
  { eapply V293_target_wstate_star with (m1:=RTfull ct) (m2:=RToutputs)
      (o1:=RIabstract ct) (o2:=emp).
    - apply RToutputs_join.
    - apply map_join_emp.
    - apply RTenv_spatial. vm_compute;reflexivity.
    - exact Outputs. }
  assert (Raw : V293_target_wstate DXge RTle (RTexec_memory ct) (RIabstract ct) |=
    (SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) ct **
     (V293_owned_record_cell ((90%positive,0%Z),Tint8,V293_byteval 99) **
      V293_owned_record_cell ((91%positive,0%Z),Tint8,V293_byteval 88))) **
    V293_read_bytes 92%positive 0%Z V293_ready_table).
  { eapply V293_target_wstate_star with (m1:=RTwith_outputs ct) (m2:=RTdecoder)
      (o1:=RIabstract ct) (o2:=emp).
    - apply RTdecoder_join.
    - apply map_join_emp.
    - exact First.
    - apply V293_read_bytes_witness. }
  clear First Outputs. sep auto.
Qed.

Lemma DXold_entry : forall ct,
  V293_target_wstate DXge RTle (RHmemory ct) (RIabstract ct) |=
    (V293_owned_record_cell ((90%positive,0%Z),Tint8,V293_byteval 99) **
     V293_owned_record_cell ((91%positive,0%Z),Tint8,V293_byteval 88)) **
    (SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) ct **
     (V293_owned_record_cell ((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipWaiting) **
      V293_read_bytes 92%positive 0%Z V293_ready_table)).
Proof.
  intro ct.
  assert (Target : V293_target_wstate DXge RTle RHtarget emp |=
    V293_owned_record_cell ((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipWaiting)).
  { pose proof (OwnershipCellsSpatial RHtarget_cells
      ltac:(vm_compute;repeat split;intros;intuition congruence)
      ltac:(repeat constructor;reflexivity) DXge RTle) as H.
    cbn [RHtarget_cells V293_owned_record_cells] in H. sep auto. }
  assert (Both : V293_target_wstate DXge RTle (RHmemory ct) (RIabstract ct) |=
    ((V293_owned_record_cell ((90%positive,0%Z),Tint8,V293_byteval 99) **
      V293_owned_record_cell ((91%positive,0%Z),Tint8,V293_byteval 88)) **
     (SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) ct **
      V293_read_bytes 92%positive 0%Z V293_ready_table)) **
     V293_owned_record_cell ((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipWaiting)).
  { eapply V293_target_wstate_star with (m1:=RTexec_memory ct) (m2:=RHtarget)
      (o1:=RIabstract ct) (o2:=emp).
    - apply RHjoin.
    - apply map_join_emp.
    - apply DXbase_entry.
    - exact Target. }
  clear Target. sep auto.
Qed.
Lemma DXold_outside : forall b i,
 b<>1%positive ->b<>41%positive ->b<>60%positive ->
 b<>80%positive ->b<>81%positive ->b<>82%positive ->
 b<>90%positive ->b<>91%positive ->b<>92%positive ->b<>93%positive ->
 get(RHmemory DXct)(b,i)=None.
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
Lemma DXjoin : forall n nc,join(RHmemory DXct)(DXextra n nc)(DXmemory n nc).
Proof.
 intros n nc;apply map_join_merge;apply map_disjoint;intros[b i].
 destruct(in_dec Pos.eq_dec b [94%positive;95%positive;96%positive;97%positive]) as[Inside |Outside].
 - left;apply DXold_outside;cbn in Inside;intuition congruence.
 - right;left;unfold DXextra;apply OwnershipCellsOutside.
   intro H;vm_compute in H;cbn in Outside;intuition congruence.
Qed.
Lemma DXentry : forall n nc,n<256 ->nc<256 ->
 DXstate(DXmemory n nc)|=SWINVt(V293_ready_inv 80%positive 81%positive 82%positive)DXct **
 (V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval 88) **
 (V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipWaiting) **
 (V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval n) **
 (V293_owned_record_cell((95%positive,0%Z),Tint8,V293_byteval 0) ** DXframe nc)))).
Proof.
 intros n nc N C.
 assert(Extra:V293_target_wstate DXge RTle(DXextra n nc)emp|=V293_owned_record_cells(DXextras n nc)).
 { apply OwnershipCellsSpatial.
   - vm_compute;repeat split;intros;intuition congruence.
   - repeat constructor;try reflexivity;apply V293_byte_type;assumption. }
 assert(Both:DXstate(DXmemory n nc)|=
 ((V293_owned_record_cell((90%positive,0%Z),Tint8,V293_byteval 99) **
   V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval 88)) **
 (SWINVt(V293_ready_inv 80%positive 81%positive 82%positive)DXct **
 (V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipWaiting) **
 V293_read_bytes 92%positive 0%Z V293_ready_table))) **V293_owned_record_cells(DXextras n nc)).
 { eapply V293_target_wstate_star with(m1:=RHmemory DXct)(m2:=DXextra n nc)
   (o1:=RIabstract DXct)(o2:=emp).
   - apply DXjoin.
   - apply map_join_emp.
   - apply DXold_entry.
   - exact Extra. }
 unfold DXframe,RCframe;cbn[DXextras V293_owned_record_cells]in Both;clear Extra;sep auto.
Qed.
Lemma DXframe_good : forall nc,GoodInvAsrt(DXframe nc).
Proof. intro;unfold DXframe;repeat split;try exact I;exact RCframe_good. Qed.
Lemma DXlookup : forall n nc k,k<256 ->
 load Tint8(DXmemory n nc)(92%positive,Z.of_nat k)=Some(V293_byteval(V293_ready_lookup k)).
Proof. intros;eapply load_mem_mono;[apply RHlookup;assumption |exists(DXextra n nc);apply DXjoin]. Qed.

Theorem DXprefix : forall ks nc,nc<256 ->exists Mf,
 cstepstar RCprogram(curs DXmiddle,(kenil,ks))(DXge,RTle,DXmemory 1 nc)
 (curs DXtail,(kenil,ks))(DXge,RTle,Mf) /\
 DXstate Mf|=SWINVt(V293_ready_inv 80%positive 81%positive 82%positive)DXct **
 (V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval 4) **
 (V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady) **
 (V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((95%positive,0%Z),Tint8,V293_byteval 0) **DXframe nc)))) /\
 load(Tptr V293_tcb_type)Mf(93%positive,0%Z)=Some(Vptr OwnershipReady) /\
 (forall c i,c<>93%positive ->(c,i)<>(91%positive,0%Z) ->(c,i)<>(94%positive,0%Z) ->
 get Mf(c,i)=get(DXmemory 1 nc)(c,i)).
Proof.
 intros ks nc Bound.
 destruct(V293_OSIntExit_dispatch_prefix_execution 80%positive 81%positive 82%positive
 RCprogram ks DXge RTle(DXmemory 1 nc)(fun _=>false)(false,nil,nil)(RIabstract DXct)(spec_done None)
 DXct(DXframe nc)107%Z 100%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z
 108%Z 109%Z 110%Z 111%Z 112%Z 92%positive 91%positive 93%positive 94%positive 95%positive
 (V293_byteval 88)(Vptr OwnershipWaiting)
 ltac:(vm_compute;reflexivity)
 ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)
 ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)
 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
 eq_refl eq_refl eq_refl eq_refl(DXframe_good nc)(DXlookup 1 nc)(DXentry 1 nc ltac:(lia)Bound))
 as(tasks&lo&hi&entries&next&message&M0&b&Ms&Mskip&Mf&Store&Fresh&Free&Removed&Map&Rel&Task&Exec&After&Load&Sched&Frame).
 pose proof(RIfixed_tasks DXct);assert(tasks=OwnershipTasks)by(congruence);subst tasks.
 assert(Range:V293_ready_select lo hi(V293_ready_group lo hi)<13).
 { apply V293_ready_selection_range;[exact(proj1 Rel) |exact(proj1(proj2 Rel)) |reflexivity |exact(proj1(proj2(proj2 Rel)))]. }
 destruct(RTonly_ready _ _ _ Range Task)as[Selected[Target Message]];subst next.
 rewrite Selected in After.
 exists Mf;split;[exact Exec | ]. split;[exact After | ]. split;assumption.
Qed.

Definition DXpost nc := SWINVt(V293_ready_inv 80%positive 81%positive 82%positive)DXct **
 (V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval 4) **
 (V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady) **
 (V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((95%positive,0%Z),Tint8,V293_byteval 0) **DXframe nc)))).
Lemma DXpluck : forall tp a v M R,
 DXstate M|=V293_owned_record_cell(a,tp,v)**R ->load tp M a=Some v.
Proof.
 intros;eapply V293_record_star_load_l with(s:=DXstate M);
 [intros st Cell;apply V293_owned_record_cell_load;exact Cell |eassumption].
Qed.
Lemma DXpost_loads : forall M nc,DXstate M|=DXpost nc ->
 load Tint8 M(91%positive,0%Z)=Some(V293_byteval 4) /\
 load Tint8 M(96%positive,0%Z)=Some(V293_byteval nc) /\
 load Tint32 M(97%positive,0%Z)=Some(Vint32(Int.repr 19)) /\
 load Tint8 M(90%positive,0%Z)=Some(V293_byteval 99).
Proof.
 intros M nc Held;unfold DXpost,DXframe,RCframe in Held.
 repeat split;eapply DXpluck with(R:=Atrue);sep auto.
Qed.
Lemma DXbranch : forall P ks M v,
 evalval(V293_OSSched_different 103%Z 110%Z)(DXge,RTle,M)=Some(Vint32 v) ->
 (v=Int.zero \/ v=Int.one) ->
 cstepstar P(curs DXtail,(kenil,ks))(DXge,RTle,M)
 (curs(if Int.eq v Int.zero then sskip None else
 sseq(V293_OSSched_increment 111%Z)(sseq(sskip None)(scall 112%Z nil))),
 (kenil,ks))(DXge,RTle,M).
Proof.
 intros P ks M v Eval Values;unfold DXtail.
 eapply c_stepstarn;[eapply stmt_step;[reflexivity |constructor] | ].
 eapply V293_cstepstar_trans.
 { apply V293_expr_steps;apply evalval_imply_estepstar;exact Eval. }
 destruct Values as[Zero |One];subst v;cbn[Int.eq].
 - eapply c_stepstarn;[eapply stmt_step;[reflexivity |apply sviff_step;reflexivity] |apply c_stepstar0].
 - eapply c_stepstarn;[eapply stmt_step;[reflexivity |apply svift_step;reflexivity] |apply c_stepstar0].
Qed.
Lemma DXcompare_reads : forall ge le M nc,
 nc<256 ->get le 103%Z=None ->get le 110%Z=None ->
 get ge 103%Z=Some(91%positive,Tint8) ->get ge 110%Z=Some(96%positive,Tint8) ->
 load Tint8 M(91%positive,0%Z)=Some(V293_byteval 4) ->
 load Tint8 M(96%positive,0%Z)=Some(V293_byteval nc) ->
 evalval(V293_OSSched_different 103%Z 110%Z)(ge,le,M)=
 Some(Vint32(if Nat.eqb 4 nc then Int.zero else Int.one)).
Proof.
 intros ge le M nc Bound HN CN HG CG High Current.
 pose proof(V293_byte_variable (V293_target_wstate ge le M emp)
   103%Z 91%positive 4 HG HN High)as[Eh Th].
 pose proof(V293_byte_variable (V293_target_wstate ge le M emp)
   110%Z 96%positive nc CG CN Current)as[Ec Tc].
 unfold V293_OSSched_different.
 cbn[V293_target_wstate getsmem get_smem evalval evaltype]in Eh,Th,Ec,Tc|-*.
 rewrite Eh,Ec,Th,Tc.
 unfold V293_byteval;cbn[bop_eval bop_type val_eq].
 rewrite V293_byte_eq by lia.
 destruct(Nat.eqb 4 nc);reflexivity.
Qed.
Lemma DXpriority4_eval : forall M,
 load Tint8 M(91%positive,0%Z)=Some(V293_byteval 4) ->
 load Tint8 M(96%positive,0%Z)=Some(V293_byteval 4) ->
 evalval(V293_OSSched_different 103%Z 110%Z)(DXge,RTle,M)=Some(Vint32 Int.zero).
Proof. intros;exact(DXcompare_reads DXge RTle M 4 ltac:(lia)eq_refl eq_refl eq_refl eq_refl H H0). Qed.
Lemma DXpriority6_eval : forall M,
 load Tint8 M(91%positive,0%Z)=Some(V293_byteval 4) ->
 load Tint8 M(96%positive,0%Z)=Some(V293_byteval 6) ->
 evalval(V293_OSSched_different 103%Z 110%Z)(DXge,RTle,M)=Some(Vint32 Int.one).
Proof. intros;exact(DXcompare_reads DXge RTle M 6 ltac:(lia)eq_refl eq_refl eq_refl eq_refl H H0). Qed.
Theorem DXsame_priority_complete_middle : forall ks,exists Mf,
 cstepstar RCprogram(curs DXmiddle,(kenil,ks))(DXge,RTle,DXmemory 1 4)
 (curs(sskip None),(kenil,ks))(DXge,RTle,Mf) /\
 DXstate Mf|=DXpost 4 /\
 load(Tptr V293_tcb_type)Mf(93%positive,0%Z)=Some(Vptr OwnershipReady) /\
 load Tint32 Mf(97%positive,0%Z)=Some(Vint32(Int.repr 19)) /\
 load Tint8 Mf(90%positive,0%Z)=Some(V293_byteval 99).
Proof.
 intro ks;destruct(DXprefix ks 4 ltac:(lia))as(Mf&Exec&After&Target&Frame).
 destruct(DXpost_loads Mf 4 After)as(High&Current&Counter&Canary).
 exists Mf;split.
 - eapply V293_cstepstar_trans;[exact Exec | ].
   exact(DXbranch RCprogram ks Mf Int.zero(DXpriority4_eval Mf High Current)(or_introl eq_refl)).
 - split;[exact After | ]. split;[exact Target | ]. split;assumption.
Qed.
(* This is the real TRUE branch cursor, not execution of OSIntCtxSw. *)
Theorem DXdifferent_priority_enters_change : forall ks,exists Mf,
 cstepstar RCprogram(curs DXmiddle,(kenil,ks))(DXge,RTle,DXmemory 1 6)
 (curs(sseq(V293_OSSched_increment 111%Z)(sseq(sskip None)(scall 112%Z nil))),
 (kenil,ks))(DXge,RTle,Mf) /\
 DXstate Mf|=DXpost 6 /\
 load(Tptr V293_tcb_type)Mf(93%positive,0%Z)=Some(Vptr OwnershipReady) /\
 load Tint32 Mf(97%positive,0%Z)=Some(Vint32(Int.repr 19)).
Proof.
 intro ks;destruct(DXprefix ks 6 ltac:(lia))as(Mf&Exec&After&Target&Frame).
 destruct(DXpost_loads Mf 6 After)as(High&Current&Counter&Canary).
 exists Mf;split.
 - eapply V293_cstepstar_trans;[exact Exec | ].
   exact(DXbranch RCprogram ks Mf Int.one(DXpriority6_eval Mf High Current)(or_intror eq_refl)).
 - split;[exact After | ]. split;assumption.
Qed.

Lemma DXbyte_outside : forall n b0 b i,(b,i)<>(b0,0%Z) ->
 get(OwnershipCellMemory((b0,0%Z),Tint8,V293_byteval n))(b,i)=None.
Proof.
 intros n b0 b i Outside;unfold OwnershipCellMemory;apply OwnershipBytesOutside.
 intro Inside;vm_compute in Inside;intuition congruence.
Qed.
Lemma DXmerge_reads : forall(L L' R R':mem)(a:addr),
 get L a=get L' a ->get R a=get R' a ->get(merge L R)a=get(merge L' R')a.
Proof.
 intros L L' R R' a Left Right;repeat rewrite map_merge_semp by reflexivity.
 rewrite Left,Right;reflexivity.
Qed.
(* These are whole-heap equations outside ONE byte, not merely equal loads. *)
Theorem DXcurrent_only : forall b i,(b,i)<>(96%positive,0%Z) ->
 get(DXmemory 1 6)(b,i)=get(DXmemory 1 4)(b,i).
Proof.
 intros b i Outside;unfold DXmemory;apply DXmerge_reads;[reflexivity | ].
 unfold DXextra,DXextras;apply DXmerge_reads;[reflexivity | ].
 apply DXmerge_reads;[reflexivity | ].
 apply DXmerge_reads;[ |reflexivity].
 transitivity (None : option (bool * memval));[apply DXbyte_outside |symmetry;apply DXbyte_outside];exact Outside.
Qed.
Theorem DXnesting_only : forall b i,(b,i)<>(94%positive,0%Z) ->
 get(DXmemory 2 4)(b,i)=get(DXmemory 1 4)(b,i).
Proof.
 intros b i Outside;unfold DXmemory;apply DXmerge_reads;[reflexivity | ].
 unfold DXextra,DXextras;apply DXmerge_reads;[ |reflexivity].
 transitivity (None : option (bool * memval));[apply DXbyte_outside |symmetry;apply DXbyte_outside];exact Outside.
Qed.
Theorem DXnested_two_skips_dispatch : forall ks,exists Mf,
 cstepstar RCprogram(curs DXmiddle,(kenil,ks))(DXge,RTle,DXmemory 2 4)
 (curs(sskip None),(kenil,ks))(DXge,RTle,Mf) /\
 load Tint8 Mf(94%positive,0%Z)=Some(V293_byteval 1) /\
 load Tint8 Mf(91%positive,0%Z)=Some(V293_byteval 88) /\
 load(Tptr V293_tcb_type)Mf(93%positive,0%Z)=Some(Vptr OwnershipWaiting) /\
 load Tint32 Mf(97%positive,0%Z)=Some(Vint32(Int.repr 19)).
Proof.
 intro ks;pose proof(DXentry 2 4 ltac:(lia)ltac:(lia))as Entry.
 assert(Held:DXstate(DXmemory 2 4)|=
 V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval 2) **
 (SWINVt(V293_ready_inv 80%positive 81%positive 82%positive)DXct **
 (V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval 88) **
 (V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipWaiting) **
 (V293_owned_record_cell((95%positive,0%Z),Tint8,V293_byteval 0) **DXframe 4))))).
 { unfold DXframe in *;sep auto. }
 assert(Nest:load Tint8(DXmemory 2 4)(94%positive,0%Z)=Some(V293_byteval 2)).
 { eapply DXpluck;exact Held. }
 destruct(V293_owned_record_cell_update _ Tint8 _ (V293_byteval 1) _ _ _ _ _ _ _ _ eq_refl Held)
 as(Mf&Store&After).
 exists Mf;split.
 - exact(V293_OSIntExit_nested_middle_execution RCprogram ks DXge RTle(DXmemory 2 4)Mf
   108%Z 109%Z 94%positive 2 DXdispatch ltac:(lia)ltac:(lia)eq_refl eq_refl Nest Store).
 - split;[eapply V293_exit_byte_readback;[lia |exact Store] | ].
   unfold DXframe in After;repeat split;eapply DXpluck with(R:=Atrue);sep auto.
Qed.
(* Only deletion of the decrement: SAME physical nesting=1 entry and callee. *)
Theorem DXomit_decrement_skips_dispatch : forall ks,
 cstepstar RCprogram(curs(V293_OSIntExit_guards 108%Z 109%Z DXdispatch),(kenil,ks))
 (DXge,RTle,DXmemory 1 4)(curs(sskip None),(kenil,ks))(DXge,RTle,DXmemory 1 4) /\
 load Tint8(DXmemory 1 4)(91%positive,0%Z)=Some(V293_byteval 88) /\
 load(Tptr V293_tcb_type)(DXmemory 1 4)(93%positive,0%Z)=Some(Vptr OwnershipWaiting).
Proof.
 intro ks;pose proof(DXentry 1 4 ltac:(lia)ltac:(lia))as Entry.
 assert(Nest:load Tint8(DXmemory 1 4)(94%positive,0%Z)=Some(V293_byteval 1)).
 { eapply DXpluck with(R:=Atrue);sep auto. }
 split.
 - unfold V293_OSIntExit_guards.
   eapply c_stepstarn;[eapply stmt_step;[reflexivity |constructor] | ].
   eapply V293_cstepstar_trans.
   { apply V293_expr_steps;apply evalval_imply_estepstar.
     exact(V293_success_global_byte_eq DXge RTle(DXmemory 1 4)108%Z 94%positive 1 0
     ltac:(lia)ltac:(lia)eq_refl eq_refl Nest). }
   eapply c_stepstarn;[eapply stmt_step;[reflexivity |apply sviff_step;reflexivity] |apply c_stepstar0].
 - split;eapply DXpluck with(R:=Atrue);sep auto.
Qed.
Theorem DXswitch_body_absent : RCprogram 112%Z=None.
Proof. reflexivity. Qed.
