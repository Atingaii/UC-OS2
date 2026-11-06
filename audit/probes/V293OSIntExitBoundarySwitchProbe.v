(* Existing interrupt continuation in actual global maps; no port body. *)
(* Independent waiting-current resources and exact OSIntCtxSw call boundary. *)
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

Require Import CertiOS.audit.probes.V293OSIntExitDispatchExecutionProbe.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitDispatchCall.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitCallExecution.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCriticalGlobal.

Require Import CertiOS.audit.probes.V293OSIntExitDispatchCallProbe.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitSwitchEntry.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyFullCall.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPointerCompare.
Import ListNotations.
Require Import CertiOS.audit.probes.V293OSIntExitSwitchEntryProbe.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitInterruptGlobal.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyGlobalTrace.
Require Import CertiOS.certiucos.v293.proofs.V293LocalGlobalTrace.
Require Import CertiOS.tactics.basetac.join_lib.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import CertiOS.audit.probes.V293OSIntExitInterruptGlobalProbe.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBoundarySwitch.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCacheContract.

(* Same physical heap; align current/target pointee types for ORIGINAL pswitch. *)
Definition BXge := set SXge OSTCBCur(1%positive,Tptr V293_tcb_type).
Lemma BXready : forall ge le ct,
  get ge OSTCBCur=Some (1%positive,Tptr V293_tcb_type) ->
  V293_target_wstate ge le (RTfull ct) (RIabstract ct) |=
    SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) ct.
Proof.
  intros ge le ct Cur.
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
    GV OSTCBCur @ (Tptr V293_tcb_type) |-> (Vptr ct)).
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
    - exists V293_tcb_type. exact Pointer.
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
Lemma BXbase_entry : forall ct,
  V293_target_wstate BXge FXcaller (RTexec_memory ct) (RIabstract ct) |=
    (V293_owned_record_cell ((90%positive,0%Z),Tint8,V293_byteval 99) **
     V293_owned_record_cell ((91%positive,0%Z),Tint8,V293_byteval 88)) **
    (SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) ct **
     V293_read_bytes 92%positive 0%Z V293_ready_table).
Proof.
  intro ct.
  assert (Outputs : V293_target_wstate BXge FXcaller RToutputs emp |=
    V293_owned_record_cell ((90%positive,0%Z),Tint8,V293_byteval 99) **
    V293_owned_record_cell ((91%positive,0%Z),Tint8,V293_byteval 88)).
  { pose proof (OwnershipCellsSpatial RToutput_cells ltac:(vm_compute;repeat split;intros;intuition congruence)
      ltac:(repeat constructor;vm_compute;reflexivity) BXge FXcaller) as Out.
    cbn [RToutput_cells V293_owned_record_cells] in Out. sep auto. }
  assert (First : V293_target_wstate BXge FXcaller (RTwith_outputs ct) (RIabstract ct) |=
    SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) ct **
    (V293_owned_record_cell ((90%positive,0%Z),Tint8,V293_byteval 99) **
     V293_owned_record_cell ((91%positive,0%Z),Tint8,V293_byteval 88))).
  { eapply V293_target_wstate_star with (m1:=RTfull ct) (m2:=RToutputs)
      (o1:=RIabstract ct) (o2:=emp).
    - apply RToutputs_join.
    - apply map_join_emp.
    - apply BXready. vm_compute;reflexivity.
    - exact Outputs. }
  assert (Raw : V293_target_wstate BXge FXcaller (RTexec_memory ct) (RIabstract ct) |=
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
Lemma BXold_entry : forall ct,
  V293_target_wstate BXge FXcaller (RHmemory ct) (RIabstract ct) |=
    (V293_owned_record_cell ((90%positive,0%Z),Tint8,V293_byteval 99) **
     V293_owned_record_cell ((91%positive,0%Z),Tint8,V293_byteval 88)) **
    (SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) ct **
     (V293_owned_record_cell ((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipWaiting) **
      V293_read_bytes 92%positive 0%Z V293_ready_table)).
Proof.
  intro ct.
  assert (Target : V293_target_wstate BXge FXcaller RHtarget emp |=
    V293_owned_record_cell ((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipWaiting)).
  { pose proof (OwnershipCellsSpatial RHtarget_cells
      ltac:(vm_compute;repeat split;intros;intuition congruence)
      ltac:(repeat constructor;reflexivity) BXge FXcaller) as H.
    cbn [RHtarget_cells V293_owned_record_cells] in H. sep auto. }
  assert (Both : V293_target_wstate BXge FXcaller (RHmemory ct) (RIabstract ct) |=
    ((V293_owned_record_cell ((90%positive,0%Z),Tint8,V293_byteval 99) **
      V293_owned_record_cell ((91%positive,0%Z),Tint8,V293_byteval 88)) **
     (SWINVt (V293_ready_inv 80%positive 81%positive 82%positive) ct **
      V293_read_bytes 92%positive 0%Z V293_ready_table)) **
     V293_owned_record_cell ((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipWaiting)).
  { eapply V293_target_wstate_star with (m1:=RTexec_memory ct) (m2:=RHtarget)
      (o1:=RIabstract ct) (o2:=emp).
    - apply RHjoin.
    - apply map_join_emp.
    - apply BXbase_entry.
    - exact Target. }
  clear Target. sep auto.
Qed.
Lemma BXentry : forall n nc,n<256 ->nc<256 ->
 V293_target_wstate BXge SXcaller(SXmemory n nc)(RIabstract SXct)|=SWINVt(V293_ready_inv 80%positive 81%positive 82%positive)SXct **
 (V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval 88) **
 (V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipWaiting) **
 (V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval n) **
 (V293_owned_record_cell((95%positive,0%Z),Tint8,V293_byteval 0) ** SXentry_frame nc)))).
Proof.
 intros n nc N C.
 assert(Extra:V293_target_wstate BXge SXcaller(SXextra n nc)emp|=V293_owned_record_cells(SXextras n nc)).
 { apply OwnershipCellsSpatial.
   - vm_compute;repeat split;intros;intuition congruence.
   - repeat constructor;try reflexivity;apply V293_byte_type;assumption. }
 assert(Both:V293_target_wstate BXge SXcaller(SXmemory n nc)(RIabstract SXct)|=
 ((V293_owned_record_cell((90%positive,0%Z),Tint8,V293_byteval 99) **
   V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval 88)) **
 (SWINVt(V293_ready_inv 80%positive 81%positive 82%positive)SXct **
 (V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipWaiting) **
 V293_read_bytes 92%positive 0%Z V293_ready_table))) **V293_owned_record_cells(SXextras n nc)).
 { eapply V293_target_wstate_star with(m1:=RHmemory SXct)(m2:=SXextra n nc)
   (o1:=RIabstract SXct)(o2:=emp).
   - apply SXjoin.
   - apply map_join_emp.
   - apply BXold_entry.
   - exact Extra. }
 unfold SXentry_frame,SXframe,RCframe;cbn[SXextras FXextras DXextras V293_owned_record_cells app]in Both;clear Extra;sep auto.
Qed.
Lemma BXindependent_entry : forall ci,
 (BXge,SXcaller,SXmemory 1 6,(fun _=>false),(false,nil,ci),RIabstract SXct,spec_done None)|=SXpre.
Proof.
 intro ci;unfold SXpre;apply V293_ready_critical_stack with(ci:=nil).
 - unfold SXentry_frame;repeat split;try exact I;exact SXframe_good.
 - exact(BXentry 1 6 ltac:(lia)ltac:(lia)).
Qed.

Definition BXcmd(sync:bool) := if sync then V293_interrupt_handoff 103%Z 110%Z 106%Z else sprim(switch 106%Z).
Definition BXbody sync := V293_exit_boundary_body 113%Z 108%Z 109%Z 601%Z
 105%Z 103%Z 106%Z 110%Z 111%Z 107%Z(BXcmd sync).
Definition BXfunction sync := V293_exit_boundary_function 113%Z 108%Z 109%Z 601%Z
 105%Z 103%Z 106%Z 110%Z 111%Z 107%Z(BXcmd sync).
Definition BXprogram sync (f:fid) := if Z.eq_dec f 300%Z then Some(BXfunction sync)else RCprogram f.
Definition BXglobal sync := (GXempty,(BXprogram sync,GXempty,(fun _=>None):intunit)).
Definition BXend sync : code := (SKIP,(kenil,kseq(sprim excrit)(kseq sret(kcall 300%Z(BXbody sync)SXcaller GXirq)))).
Definition BXpost(sync:bool)bs := SWINVt(V293_ready_inv 80%positive 81%positive 82%positive)OwnershipReady **
 (V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval 4) **
 (V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady) **
 (V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((95%positive,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((96%positive,0%Z),Tint8,V293_byteval(if sync then 4 else 6)) **
 (V293_owned_record_cell((98%positive,0%Z),Tint8,V293_byteval 1) **
 (V293_owned_record_cell((97%positive,0%Z),Tint32,Vint32(Int.repr 20)) **
 (Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **SXframe)))))))).
Lemma BXmerge : forall sync,BXprogram sync=pumerge(BXprogram sync)GXempty.
Proof. intros;apply functional_extensionality;intro f;unfold pumerge,GXempty;destruct(BXprogram sync f);reflexivity. Qed.
Lemma BXdomain : forall other otherle otheraux enabled ci t pr st msg,
 get OwnershipTasks t=Some(pr,st,msg) ->
 exists C le aux,get(GXtasks other)t=Some C /\get(GXenvs otherle)t=Some le /\
 @get tid localst ltaskstset TaskLStMap(GXaux enabled ci otheraux)t=Some aux.
Proof.
 intros other otherle otheraux enabled ci t pr st msg Task.
 unfold OwnershipTasks in Task.
 destruct(tid_eq_dec OwnershipWaiting t)as[E|N].
 - subst t;exists(curs(scall 300%Z nil),(kenil,GXirq));exists SXcaller;exists((enabled,nil,ci):localst).
   repeat split.
 - rewrite map_get_set' in Task by exact N.
   destruct(tid_eq_dec OwnershipReady t)as[E|NR].
   + subst t;exists other;exists otherle;exists otheraux.
     unfold GXtasks,GXenvs,GXaux;repeat split;rewrite map_get_set' by discriminate;apply map_get_set.
   + rewrite map_get_sig' in Task by exact NR;discriminate.
Qed.
Theorem BXcomplete_switch : forall sync enabled ci other otherle otheraux cst,
 exists bs Mf,fresh(SXmemory 1 6)bs /\
 V293_global_steps(BXglobal sync)cst
 (GXtasks other,(BXge,GXenvs otherle,SXmemory 1 6,(fun _=>false),GXaux enabled ci otheraux),SXct)
 (set(GXtasks other)SXct(BXend sync),
 (BXge,set(GXenvs otherle)SXct(V293_cpu_lenv 601%Z bs),Mf,(fun _=>false),
 set(GXaux enabled ci otheraux)SXct(false,nil,enabled::ci)),OwnershipReady) /\
 (BXge,V293_cpu_lenv 601%Z bs,Mf,(fun _=>false),(false,nil,enabled::ci),
 set(RIabstract SXct)curtid(oscurt OwnershipReady),spec_done None)|=BXpost sync bs /\
 load(Tptr V293_tcb_type)Mf(1%positive,0%Z)=Some(Vptr OwnershipReady) /\
 load Tint8 Mf(96%positive,0%Z)=Some(V293_byteval(if sync then 4 else 6)) /\
 load Tint32 Mf(97%positive,0%Z)=Some(Vint32(Int.repr 20)) /\
 (forall k,k<4 ->exists v,get Mf(bs,Z.of_nat k)=Some(true,v)) /\
 (V293_cache_current OwnershipTasks OwnershipReady Mf 96%positive <->sync=true).
Proof.
 intros sync enabled ci other otherle otheraux cst.
 destruct(V293_OSIntExit_boundary_switch sync 80%positive 81%positive 82%positive
 (BXprogram sync)kstop GXempty(BXprogram sync)GXempty((fun _=>None):intunit)
 (GXtasks other)(GXenvs otherle)(GXaux enabled ci otheraux)cst
 (curs(scall 501%Z nil))kenil SXcaller BXge SXcaller(SXmemory 1 6)(fun _=>false)
 enabled nil ci(RIabstract SXct)(spec_done None)SXct SXframe OwnershipTasks 6
 300%Z 107%Z 100%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z
 108%Z 109%Z 113%Z 601%Z 110%Z 111%Z
 92%positive 91%positive 93%positive 94%positive 95%positive 98%positive 96%positive 97%positive
 (Int.repr 19)(V293_byteval 88)(Vptr OwnershipWaiting)1%positive
 (BXmerge sync)(GXcode other)(GXenv otherle)(GXaux_current enabled ci otheraux)I
 eq_refl eq_refl ltac:(vm_compute;intuition congruence)
 ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)
 ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)
 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
 (map_get_set _ _ _)(BXdomain other otherle otheraux enabled ci)
 (RIfixed_tasks SXct)SXcurrent SXnot_highest SXframe_good(SXlookup 1 6)(BXindependent_entry ci))
 as(bs&next&nh&Me&Ms&Mf&Fresh&Different&PriorityDifferent&Highest&NextPriority&Exec&Post&Pointer&Cache&Counter&Alive&Coherent&CopyStore&PointerStore&NextBindings).
 assert(Next:next=OwnershipReady).
 { destruct RTliteral_rel as(Lo&Hi&Nonempty&Bitmap&Table).
   eapply V293_highest_unique;[exact Table|exact Highest|exact FXhighest]. }
 subst next.
 assert(Priority:nh=4).
 { destruct NextPriority as[Bound[st[m Task]]].
   assert(Ready:get OwnershipTasks OwnershipReady=Some(Int.repr 4,rdy,Vnull))by reflexivity.
   unfold get,TcbMap in Task,Ready;rewrite Ready in Task.
   apply V293_priority_repr_injective;[exact Bound|lia| ].
   symmetry;exact(f_equal(fun x=>match x with Some(p,_,_)=>p |None=>Int.zero end)Task). }
 subst nh;exists bs;exists Mf;repeat first[assumption|split].
Qed.

Lemma BXpost_canaries : forall sync enabled ci bs Mf,
 (BXge,V293_cpu_lenv 601%Z bs,Mf,(fun _=>false),(false,nil,enabled::ci),
 set(RIabstract SXct)curtid(oscurt OwnershipReady),spec_done None)|=BXpost sync bs ->
 load Tint8 Mf(99%positive,0%Z)=Some(V293_byteval 23) /\
 load Tint8 Mf(100%positive,0%Z)=Some(V293_byteval 0).
Proof.
 intros sync enabled ci bs Mf Held;unfold BXpost,SXframe in Held;split;
 eapply V293_record_star_load_l with
 (s:=(BXge,V293_cpu_lenv 601%Z bs,Mf,(fun _=>false),(false,nil,enabled::ci),
 set(RIabstract SXct)curtid(oscurt OwnershipReady),spec_done None))
 (Q:=Atrue);[apply V293_owned_record_cell_load|sep auto|apply V293_owned_record_cell_load|sep auto].
Qed.
Lemma BXother_maps : forall sync other otherle otheraux enabled ci bs,
 @get tid code tasks TasksMap(set(GXtasks other)SXct(BXend sync))OwnershipReady=Some other /\
 get(set(GXenvs otherle)SXct(V293_cpu_lenv 601%Z bs))OwnershipReady=Some otherle /\
 @get tid localst ltaskstset TaskLStMap(set(GXaux enabled ci otheraux)SXct(false,nil,enabled::ci))OwnershipReady=Some otheraux.
Proof.
 intros;unfold GXtasks,GXenvs,GXaux;repeat split;
 repeat rewrite map_get_set' by discriminate;apply map_get_set.
Qed.
Lemma BXprogram_only_callsite : forall f,f<>300%Z ->BXprogram true f=BXprogram false f.
Proof. intros;unfold BXprogram;destruct(Z.eq_dec f 300%Z);congruence. Qed.
Lemma BXcommon_pointer_types :
 get BXge OSTCBCur=Some(1%positive,Tptr V293_tcb_type) /\
 get BXge 106%Z=Some(93%positive,Tptr V293_tcb_type).
Proof. split;reflexivity. Qed.

Theorem BXboth_IE_complete : forall sync ci other otherle otheraux cst,
 exists b0 M0 b1 M1,
 V293_global_steps(BXglobal sync)cst
 (GXtasks other,(BXge,GXenvs otherle,SXmemory 1 6,(fun _=>false),GXaux false ci otheraux),SXct)
 (set(GXtasks other)SXct(BXend sync),
 (BXge,set(GXenvs otherle)SXct(V293_cpu_lenv 601%Z b0),M0,(fun _=>false),
 set(GXaux false ci otheraux)SXct(false,nil,false::ci)),OwnershipReady) /\
 V293_global_steps(BXglobal sync)cst
 (GXtasks other,(BXge,GXenvs otherle,SXmemory 1 6,(fun _=>false),GXaux true ci otheraux),SXct)
 (set(GXtasks other)SXct(BXend sync),
 (BXge,set(GXenvs otherle)SXct(V293_cpu_lenv 601%Z b1),M1,(fun _=>false),
 set(GXaux true ci otheraux)SXct(false,nil,true::ci)),OwnershipReady) /\
 load Tint8 M0(96%positive,0%Z)=Some(V293_byteval(if sync then 4 else 6)) /\
 load Tint8 M1(96%positive,0%Z)=Some(V293_byteval(if sync then 4 else 6)) /\
 load Tint32 M0(97%positive,0%Z)=Some(Vint32(Int.repr 20)) /\
 load Tint32 M1(97%positive,0%Z)=Some(Vint32(Int.repr 20)) /\
 load Tint8 M0(99%positive,0%Z)=Some(V293_byteval 23) /\
 load Tint8 M1(100%positive,0%Z)=Some(V293_byteval 0) /\
 (forall k,k<4 ->exists v,get M0(b0,Z.of_nat k)=Some(true,v)) /\
 (forall k,k<4 ->exists v,get M1(b1,Z.of_nat k)=Some(true,v)).
Proof.
 intros sync ci other otherle otheraux cst.
 destruct(BXcomplete_switch sync false ci other otherle otheraux cst)
 as(b0&M0&Fresh0&Exec0&Post0&Pointer0&Cache0&Counter0&Alive0&Coherent0).
 destruct(BXcomplete_switch sync true ci other otherle otheraux cst)
 as(b1&M1&Fresh1&Exec1&Post1&Pointer1&Cache1&Counter1&Alive1&Coherent1).
 destruct(BXpost_canaries sync false ci b0 M0 Post0)as(Canary0&Local0).
 destruct(BXpost_canaries sync true ci b1 M1 Post1)as(Canary1&Local1).
 exists b0;exists M0;exists b1;exists M1;repeat first[assumption|split].
Qed.

Theorem BXcopy_ablation : forall enabled ci other otherle otheraux cst,
 exists b0 M0 b1 M1,
 V293_global_steps(BXglobal true)cst
 (GXtasks other,(BXge,GXenvs otherle,SXmemory 1 6,(fun _=>false),GXaux enabled ci otheraux),SXct)
 (set(GXtasks other)SXct(BXend true),
 (BXge,set(GXenvs otherle)SXct(V293_cpu_lenv 601%Z b0),M0,(fun _=>false),
 set(GXaux enabled ci otheraux)SXct(false,nil,enabled::ci)),OwnershipReady) /\
 V293_global_steps(BXglobal false)cst
 (GXtasks other,(BXge,GXenvs otherle,SXmemory 1 6,(fun _=>false),GXaux enabled ci otheraux),SXct)
 (set(GXtasks other)SXct(BXend false),
 (BXge,set(GXenvs otherle)SXct(V293_cpu_lenv 601%Z b1),M1,(fun _=>false),
 set(GXaux enabled ci otheraux)SXct(false,nil,enabled::ci)),OwnershipReady) /\
 load(Tptr V293_tcb_type)M0(1%positive,0%Z)=Some(Vptr OwnershipReady) /\
 load(Tptr V293_tcb_type)M1(1%positive,0%Z)=Some(Vptr OwnershipReady) /\
 load Tint8 M0(96%positive,0%Z)=Some(V293_byteval 4) /\
 load Tint8 M1(96%positive,0%Z)=Some(V293_byteval 6) /\
 load Tint32 M0(97%positive,0%Z)=Some(Vint32(Int.repr 20)) /\
 load Tint32 M1(97%positive,0%Z)=Some(Vint32(Int.repr 20)) /\
 V293_cache_current OwnershipTasks OwnershipReady M0 96%positive /\
 ~V293_cache_current OwnershipTasks OwnershipReady M1 96%positive.
Proof.
 intros enabled ci other otherle otheraux cst.
 destruct(BXcomplete_switch true enabled ci other otherle otheraux cst)
 as(b0&M0&Fresh0&Exec0&Post0&Pointer0&Cache0&Counter0&Alive0&Coherent0).
 destruct(BXcomplete_switch false enabled ci other otherle otheraux cst)
 as(b1&M1&Fresh1&Exec1&Post1&Pointer1&Cache1&Counter1&Alive1&Coherent1).
 assert(C0:V293_cache_current OwnershipTasks OwnershipReady M0 96%positive)by(apply Coherent0;reflexivity).
 assert(C1:~V293_cache_current OwnershipTasks OwnershipReady M1 96%positive)by(rewrite Coherent1;discriminate).
 exists b0;exists M0;exists b1;exists M1;repeat first[assumption|split].
Qed.

Theorem BXraw_port_still_stuck : forall other otherle otheraux enabled ci bs Mf cst,
 ~exists T' cst' S' t',lpstep GXprogram
 (set(GXtasks other)SXct GXend)cst
 (BXge,set(GXenvs otherle)SXct(V293_cpu_lenv 601%Z bs),Mf,(fun _=>false),
 set(GXaux enabled ci otheraux)SXct(false,nil,enabled::ci))SXct T' cst' S' t'.
Proof.
 intros;unfold GXprogram,GXend.
 eapply V293_missing_port_disabled_no_global_step.
 - apply map_get_set.
 - apply map_get_set.
 - apply map_get_set.
 - exists(curs(sfexec 112%Z nil nil));exists kenil;exists(SXK GXirq);split;[reflexivity| ].
   right;left;exists 300%Z;exists SXcaller;exists GXirq.
   exists Tvoid;exists dnil;exists(dcons 601%Z Tint32 dnil);exists SXbody;exists SXbody.
   split;reflexivity.
 - rewrite <-GXmerge;exact SXswitch_lookup_absent.
Qed.

Lemma BXnormalization :
 (match V293_port_normalize 301%Z 302%Z 601%Z
 (V293_OSIntExit_body 113%Z 108%Z 109%Z 601%Z 105%Z 103%Z 106%Z 110%Z 111%Z 107%Z 301%Z 302%Z 112%Z)with
 |Some s=>V293_intswitch_calls 112%Z(BXcmd true)s|None=>None end)=Some(BXbody true).
Proof. apply V293_OSIntExit_boundary_normalization;discriminate. Qed.
Lemma BXreject_nonempty_args :
 V293_intswitch_calls 112%Z(BXcmd true)(scall 112%Z[econst32 Int.zero])=None.
Proof. reflexivity. Qed.
Lemma BXreject_value_call :
 V293_intswitch_calls 112%Z(BXcmd true)(scalle(evar 601%Z)112%Z nil)=None.
Proof. reflexivity. Qed.
Lemma BXreject_runtime :
 V293_intswitch_calls 112%Z(BXcmd true)(sfexec 112%Z nil nil)=None /\
 V293_intswitch_calls 112%Z(BXcmd true)(salloc nil dnil)=None /\
 V293_intswitch_calls 112%Z(BXcmd true)(sfree nil None)=None.
Proof. repeat split. Qed.
