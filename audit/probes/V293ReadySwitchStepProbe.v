(* Same literal bytes as stage137; only current's environment type is aligned.
   These are joint witnesses, not initialization reachability. *)
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
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTargetHandoff.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchState.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.audit.probes.V293ReadyTaskInvariantProbe.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.certiucos.v293.code.V293OSSchedDispatch.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.audit.probes.V293ReadyTargetHandoffProbe.
Require Import CertiOS.certiucos.v293.proofs.V293ReadySchedCall.
Require Import CertiOS.audit.probes.V293ReadySchedCallProbe.
Require Import CertiOS.certiucos.v293.proofs.V293ReadySwitchStep.
Import ListNotations.
Local Open Scope nat_scope.
Definition RSge : env := set RHge OSTCBCur (1%positive,Tptr V293_tcb_type).
Definition RSstate ct M := V293_target_wstate RSge RTle M (RIabstract ct).
Lemma RSenv_spatial : forall ge le ct tp,
  get ge OSTCBCur=Some (1%positive,Tptr tp) ->
  V293_target_wstate ge le (RTfull ct) (RIabstract ct) |=
    SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) ct.
Proof.
  intros ge le ct tp Cur.
  assert (Flags : V293_target_wstate ge le emp emp |= V293_shared_flags).
  { unfold V293_shared_flags.
    repeat (eapply V293_target_wstate_star with (m1:=emp) (m2:=emp) (o1:=emp) (o2:=emp);
      [apply map_join_emp | apply map_join_emp | | ]).
    - exists (fun _ : hid => false). split; repeat split; reflexivity.
    - repeat split; reflexivity.
    - exists INUM. repeat split; reflexivity. }
  assert (Fields : V293_target_wstate ge le emp (RIabstract ct) |=
    V293_shared_fields ct OwnershipTasks (emp : EcbMod.map) Int.zero).
  { unfold V293_shared_fields,RIabstract,V293_shared_fixture_abs.
    repeat (eapply V293_target_wstate_star;
      [apply map_join_emp | apply map_join_merge;apply map_disjoint;intros key;destruct key;simpl;auto | split;reflexivity | ]).
    split;reflexivity. }
  assert (Pointer : V293_target_wstate ge le (V293_shared_fixture_mem ct) emp |=
    GV OSTCBCur @ (Tptr tp) |-> (Vptr ct)).
  { exists 1%positive. eapply V293_target_wstate_star with
      (m1:=emp) (m2:=V293_shared_fixture_mem ct) (o1:=emp) (o2:=emp).
    - apply map_join_comm;apply map_join_emp.
    - apply map_join_emp.
    - exists 1%positive. split; [exact Cur | ]. repeat split;reflexivity.
    - split; [apply V293_encoded_memory_mapsto | reflexivity]. }
  assert (Core : V293_target_wstate ge le (RImemory ct) (RIabstract ct) |=
    (EX tp : type, GV OSTCBCur @ (Tptr tp) |-> (Vptr ct)) **
    (V293_shared_fields ct OwnershipTasks (emp : EcbMod.map) Int.zero **
      V293_owned_task_records OwnershipTasks)).
  { eapply V293_target_wstate_star with (m1:=V293_shared_fixture_mem ct) (m2:=OwnershipMemory)
      (o1:=emp) (o2:=RIabstract ct).
    - apply RIjoin.
    - apply map_join_comm;apply map_join_emp.
    - exists tp. exact Pointer.
    - eapply V293_target_wstate_star with (m1:=emp) (m2:=OwnershipMemory)
        (o1:=RIabstract ct) (o2:=emp).
      + apply map_join_comm;apply map_join_emp.
      + apply map_join_emp.
      + exact Fields.
      + eapply V293_task_list_context;exact OwnershipLiteralSpatial. }
  assert (Raw : V293_target_wstate ge le (RTfull ct) (RIabstract ct) |=
    ((EX tp : type, GV OSTCBCur @ (Tptr tp) |-> (Vptr ct)) **
     (V293_shared_fields ct OwnershipTasks (emp : EcbMod.map) Int.zero **
       V293_owned_task_records OwnershipTasks)) **
    V293_ready_owned 80%positive 81%positive 82%positive OwnershipTasks).
  { eapply V293_target_wstate_star with (m1:=RImemory ct) (m2:=RTmemory)
      (o1:=RIabstract ct) (o2:=emp).
    - apply RTjoin.
    - apply map_join_emp.
    - exact Core.
    - exists 16. exists 0. exists RTentries. apply astar_l_apure_intro.
      + eapply V293_owned_cells_context;exact RTliteral_cells.
      + exact RTliteral_rel. }
  apply V293_ready_switch_halves.
  eapply V293_target_wstate_star with (m1:=emp) (m2:=RTfull ct)
    (o1:=emp) (o2:=RIabstract ct).
  - apply map_join_comm;apply map_join_emp.
  - apply map_join_comm;apply map_join_emp.
  - exact Flags.
  - unfold V293_ready_full,V293_ready_payload. clear Core Fields Pointer Flags. sep auto.
Qed.
Lemma RSbase_entry : forall ct,
  V293_target_wstate RSge RTle (RTexec_memory ct) (RIabstract ct) |=
    (V293_owned_record_cell ((90%positive,0%Z),Tint8,V293_byteval 99) **
     V293_owned_record_cell ((91%positive,0%Z),Tint8,V293_byteval 88)) **
    (SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) ct **
     V293_read_bytes 92%positive 0%Z V293_ready_table).
Proof.
  intro ct.
  assert (Outputs : V293_target_wstate RSge RTle RToutputs emp |=
    V293_owned_record_cell ((90%positive,0%Z),Tint8,V293_byteval 99) **
    V293_owned_record_cell ((91%positive,0%Z),Tint8,V293_byteval 88)).
  { pose proof (OwnershipCellsSpatial RToutput_cells ltac:(vm_compute;repeat split;intros;intuition congruence)
      ltac:(repeat constructor;vm_compute;reflexivity) RSge RTle) as Out.
    cbn [RToutput_cells V293_owned_record_cells] in Out. sep auto. }
  assert (First : V293_target_wstate RSge RTle (RTwith_outputs ct) (RIabstract ct) |=
    SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) ct **
    (V293_owned_record_cell ((90%positive,0%Z),Tint8,V293_byteval 99) **
     V293_owned_record_cell ((91%positive,0%Z),Tint8,V293_byteval 88))).
  { eapply V293_target_wstate_star with (m1:=RTfull ct) (m2:=RToutputs)
      (o1:=RIabstract ct) (o2:=emp).
    - apply RToutputs_join.
    - apply map_join_emp.
    - apply RSenv_spatial with (tp:=V293_tcb_type). vm_compute;reflexivity.
    - exact Outputs. }
  assert (Raw : V293_target_wstate RSge RTle (RTexec_memory ct) (RIabstract ct) |=
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

Lemma RSraw_entry : forall ct,
  RSstate ct (RHmemory ct) |=
    (V293_owned_record_cell ((90%positive,0%Z),Tint8,V293_byteval 99) **
     V293_owned_record_cell ((91%positive,0%Z),Tint8,V293_byteval 88)) **
    (SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) ct **
     (V293_owned_record_cell ((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipWaiting) **
      V293_read_bytes 92%positive 0%Z V293_ready_table)).
Proof.
  intro ct.
  assert (Target : V293_target_wstate RSge RTle RHtarget emp |=
    V293_owned_record_cell ((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipWaiting)).
  { pose proof (OwnershipCellsSpatial RHtarget_cells
      ltac:(vm_compute;repeat split;intros;intuition congruence)
      ltac:(repeat constructor;reflexivity) RSge RTle) as H.
    cbn [RHtarget_cells V293_owned_record_cells] in H. sep auto. }
  assert (Both : RSstate ct (RHmemory ct) |=
    ((V293_owned_record_cell ((90%positive,0%Z),Tint8,V293_byteval 99) **
      V293_owned_record_cell ((91%positive,0%Z),Tint8,V293_byteval 88)) **
     (SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) ct **
      V293_read_bytes 92%positive 0%Z V293_ready_table)) **
     V293_owned_record_cell ((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipWaiting)).
  { eapply V293_target_wstate_star with (m1:=RTexec_memory ct) (m2:=RHtarget)
      (o1:=RIabstract ct) (o2:=emp).
    - apply RHjoin.
    - apply map_join_emp.
    - apply RSbase_entry.
    - exact Target. }
  clear Target. sep auto.
Qed.

Lemma RSentry : forall ct, RSstate ct (RHmemory ct) |=
  SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) ct **
    (V293_owned_record_cell ((91%positive,0%Z),Tint8,V293_byteval 88) **
      (V293_owned_record_cell ((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipWaiting) ** RCframe)).
Proof. intro ct. pose proof (RSraw_entry ct). unfold RCframe. sep auto. Qed.

Theorem RSbinding_type_only :
  get RHge OSTCBCur=Some (1%positive,Tptr Tvoid) /\
  get RSge OSTCBCur=Some (1%positive,Tptr V293_tcb_type) /\
  (forall x, x<>OSTCBCur -> get RSge x=get RHge x).
Proof.
  split; [reflexivity | ]. split; [apply map_get_set | ].
  intros x Apart. unfold RSge. apply map_get_set'. congruence.
Qed.
Theorem RSold_no_common_type : forall bt bc tp,
  ~ (get RHge 106%Z=Some (bt,Tptr tp) /\
     get RHge OSTCBCur=Some (bc,Tptr tp)).
Proof.
  intros bt bc tp [Target Current].
  change (Some (93%positive,Tptr V293_tcb_type)=Some (bt,Tptr tp)) in Target.
  change (Some (1%positive,Tptr Tvoid)=Some (bc,Tptr tp)) in Current.
  unfold V293_tcb_type in Target. congruence.
Qed.
(* The earlier complete call and SWPRE still hold in the rejected old type
   environment; its rejection is not an early bitmap/selection failure. *)
Theorem RSold_SWPRE_without_switch_type : forall ks live, exists M,
  cstepstar RCprogram
    (curs (V293_OSSched_unlocked_prefix 107%Z 105%Z 103%Z 106%Z),(kenil,ks))
    (RHge,RTle,RHmemory (RIcurrent live)) (curs (sskip None),(kenil,ks)) (RHge,RTle,M) /\
  RHstate (RIcurrent live) M |= SWPRE V293_scheduler 106%Z (RIcurrent live) /\
  (forall bt bc tp, ~ (get RHge 106%Z=Some (bt,Tptr tp) /\
     get RHge OSTCBCur=Some (bc,Tptr tp))).
Proof.
  intros ks live. destruct (RCjoint_call_handoff_and_omission ks live)
    as (b & Ms & Mskip & M & Fresh & Call & Free & Removed & Exec & Store & Pre & Rest).
  exists M. split; [exact Exec | ]. split; [exact Pre | apply RSold_no_common_type].
Qed.

Lemma RScurrent_load : forall t M O R,
  (RSge,RTle,M,(fun _=>false),(false,nil,nil),O,spec_done None) |=
    SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) t ** R ->
  load (Tptr V293_tcb_type) M (1%positive,0%Z)=Some (Vptr t).
Proof.
  intros t M O R Held.
  assert (Read : (RSge,RTle,M,(fun _=>false),(false,nil,nil),O,spec_done None) |= CurTid t ** Atrue).
  { unfold SWINVt in Held. unfold CurTid. sep auto. }
  destruct (V293_shared_current_read _ _ _ _ _ _ _ _ _ Read) as (b & tp & GE & LD).
  change (Some (1%positive,Tptr V293_tcb_type)=Some (b,Tptr tp)) in GE.
  inversion GE;subst b tp. exact LD.
Qed.
Definition RStasks (ct : tid) ks : tasks :=
  set (sig OwnershipReady (SKIP,(kenil,kstop))) ct (curs (sprim (switch 106%Z)),(kenil,ks)).
Definition RSles (ct : tid) : cltenvs := set (sig OwnershipReady emp) ct RTle.
Definition RSaux (ct : tid) : ltaskstset := set (sig OwnershipReady (false,nil,nil)) ct (false,nil,nil).

Theorem RSjoint_call_switch : forall ks live po pi ip cst, exists b Ms Mskip Mtarget Mf,
  fresh (RHmemory (RIcurrent live)) b /\
  free Tint8 b Ms=Some Mskip /\ get Mskip (b,0%Z)=None /\
  cstepstar RCprogram
    (curs (V293_OSSched_unlocked_prefix 107%Z 105%Z 103%Z 106%Z),(kenil,ks))
    (RSge,RTle,RHmemory (RIcurrent live)) (curs (sskip None),(kenil,ks)) (RSge,RTle,Mtarget) /\
  store (Tptr V293_tcb_type) Mskip (93%positive,0%Z) (Vptr OwnershipReady)=Some Mtarget /\
  RSstate (RIcurrent live) Mtarget |= SWPRE V293_scheduler 106%Z (RIcurrent live) /\
  lpstep (RCprogram,(po,pi,ip)) (RStasks (RIcurrent live) ks) cst
    (RSge,RSles (RIcurrent live),Mtarget,(fun _=>false),RSaux (RIcurrent live)) (RIcurrent live)
    (set (RStasks (RIcurrent live) ks) (RIcurrent live) (SKIP,(kenil,ks))) cst
    (RSge,RSles (RIcurrent live),Mf,(fun _=>false),RSaux (RIcurrent live)) OwnershipReady /\
  store (Tptr V293_tcb_type) Mtarget (1%positive,0%Z) (Vptr OwnershipReady)=Some Mf /\
  (RSge,emp,Mf,(fun _=>false),(false,nil,nil),set (RIabstract (RIcurrent live)) curtid (oscurt OwnershipReady),spec_done None) |=
    SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) OwnershipReady ** Atrue /\
  load (Tptr V293_tcb_type) Mf (1%positive,0%Z)=Some (Vptr OwnershipReady) /\
  load (Tptr V293_tcb_type) Mtarget (1%positive,0%Z)=Some (Vptr (RIcurrent live)) /\
  ~ (RSge,RTle,Mtarget,(fun _=>false),(false,nil,nil),set (RIabstract (RIcurrent live)) curtid (oscurt OwnershipReady),spec_done None) |=
    SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) OwnershipReady ** Atrue /\
  V293_task_records Mf OwnershipTasks /\
  load Tint8 Mf (90%positive,0%Z)=Some (V293_byteval 99) /\
  projS (RSge,RSles (RIcurrent live),Mf,(fun _=>false),RSaux (RIcurrent live)) OwnershipReady=
    Some ((RSge,emp,Mf),(fun _=>false),(false,nil,nil)) /\
  get (set (RStasks (RIcurrent live) ks) (RIcurrent live) (SKIP,(kenil,ks))) (RIcurrent live)=Some (SKIP,(kenil,ks)) /\
  get (set (RStasks (RIcurrent live) ks) (RIcurrent live) (SKIP,(kenil,ks))) OwnershipReady=Some (SKIP,(kenil,kstop)) /\
  (forall c i, c<>1%positive \/ (i<0)%Z \/ (4<=i)%Z -> get Mf (c,i)=get Mtarget (c,i)).
Proof.
  intros ks live po pi ip cst. set (ct:=RIcurrent live).
  assert (Different : ct<>OwnershipReady) by (unfold ct,RIcurrent;destruct live;discriminate).
  destruct (V293_ready_call_then_switch 80%positive 81%positive 82%positive RCprogram ks RSge RTle
    (RHmemory ct) (fun _=>false) (false,nil,nil) (RIabstract ct) (spec_done None)
    ct RCframe 107%Z 100%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 92%positive 91%positive 93%positive
    (V293_byteval 88) (Vptr OwnershipWaiting)
    RCprogram po pi ip (RStasks ct ks) cst (RSles ct) (RSaux ct) 1%positive
    ltac:(vm_compute;reflexivity)
    ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
    ltac:(discriminate) ltac:(discriminate)
    eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
    RCframe_good (RHlookup ct) (RSentry ct)
    (map_get_set _ _ _) (map_get_set _ _ _) (map_get_set _ _ _) (map_get_set _ _ _))
    as (ts & lo & hi & es & next & msg & b & Ms & Mskip & Mtarget & Mf & Fresh & Map & Rel & Task & Call & Free & Removed & Exec & Store & Sched & Before & Pre & Step & CurStore & After & CurLoad & Outside).
  pose proof (RIfixed_tasks ct). assert (ts=OwnershipTasks) by congruence. subst ts.
  assert (Bound : V293_ready_select lo hi (V293_ready_group lo hi)<13).
  { apply V293_ready_selection_range; [exact (proj1 Rel) | exact (proj1 (proj2 Rel)) | reflexivity | exact (proj1 (proj2 (proj2 Rel)))]. }
  destruct (RTonly_ready _ _ _ Bound Task) as [Selected [Target Message]]. subst next.
  assert (OldLoad : load (Tptr V293_tcb_type) Mtarget (1%positive,0%Z)=Some (Vptr ct)).
  { eapply RScurrent_load; exact Before. }
  assert (Omitted : ~ (RSge,RTle,Mtarget,(fun _=>false),(false,nil,nil),set (RIabstract ct) curtid (oscurt OwnershipReady),spec_done None) |=
    SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) OwnershipReady ** Atrue).
  { intro Bad. pose proof (RScurrent_load _ _ _ _ Bad) as BadLoad.
    assert (ct=OwnershipReady) by congruence. contradiction. }
  assert (Ready : (RSge,RTle,Mf,(fun _=>false),(false,nil,nil),set (RIabstract ct) curtid (oscurt OwnershipReady),spec_done None) |=
    SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) OwnershipReady ** Atrue).
  { clear Before Pre. sep auto. }
  assert (Records : V293_task_records Mf OwnershipTasks).
  { destruct (V293_ready_switch_sound _ _ _ _ _ _ Ready) as (ts & l & h & es' & Lookup & Records & RR & Loads).
    change (get (set (RIabstract ct) curtid (oscurt OwnershipReady)) abstcblsid=Some (abstcblist ts)) in Lookup.
    rewrite map_get_set' in Lookup by discriminate.
    pose proof (RIfixed_tasks ct). assert (ts=OwnershipTasks) by congruence. subst ts. exact Records. }
  assert (Canary : load Tint8 Mf (90%positive,0%Z)=Some (V293_byteval 99)).
  { eapply V293_record_star_load_l with
      (s:=(RSge,RTle,Mf,(fun _=>false),(false,nil,nil),set (RIabstract ct) curtid (oscurt OwnershipReady),spec_done None))
      (P:=V293_owned_record_cell ((90%positive,0%Z),Tint8,V293_byteval 99)) (Q:=Atrue).
    - intros st Cell; apply V293_owned_record_cell_load;exact Cell.
    - unfold RCframe in After. clear Ready Before Pre. sep auto. }
  assert (Projection : projS (RSge,RSles ct,Mf,(fun _=>false),RSaux ct) OwnershipReady=
    Some ((RSge,emp,Mf),(fun _=>false),(false,nil,nil))).
  { unfold projS,projD,RSles,RSaux. cbn.
    rewrite !map_get_set' by exact Different. rewrite !map_get_sig. reflexivity. }
  exists b. exists Ms. exists Mskip. exists Mtarget. exists Mf.
  split; [exact Fresh | ]. split; [exact Free | ]. split; [exact Removed | ].
  split; [exact Exec | ]. split; [exact Store | ]. split; [exact Pre | ]. split; [exact Step | ].
  split; [exact CurStore | ]. split.
  - eapply V293_ready_lenv_frame; [exact I | exact Ready].
  - split; [exact CurLoad | ]. split; [exact OldLoad | ]. split; [exact Omitted | ].
    split; [exact Records | ]. split; [exact Canary | ]. split; [exact Projection | ].
    split; [apply map_get_set | ]. split; [ | exact Outside].
    unfold RStasks. rewrite !map_get_set' by exact Different. apply map_get_sig.

Qed.
