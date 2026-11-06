(* A nonempty shared/local entry for the universal task relation.
   No boot reachability or interrupt-body correctness is claimed. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeSourceTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293TimeSourceAPI.
Require Import CertiOS.certiucos.v293.proofs.V293TimeReadyAPI.
Require Import CertiOS.certiucos.v293.proofs.V293TimeReadyShared.
Require Import CertiOS.certiucos.v293.proofs.V293TimeReadyEntry.
Require Import CertiOS.certiucos.v293.proofs.V293TimeNamesGood.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.audit.probes.V293TimeReadyEntryProbe.
Require Import CertiOS.audit.probes.V293TimeReadySharedProbe.
Require Import CertiOS.audit.probes.V293TimeReadyAPIProbe.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.soundness.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.simulation.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.framework.proof.oscorrectness.
Require Import CertiOS.framework.proof.toptheorem.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List.


Definition TSapi := V293_source_time_program 203%Z 202%Z 1001%Z 1002%Z 1003%Z.
Definition TSaspec := V293_source_time_spec 203%Z 202%Z.
Definition TSinv := V293_time_ready_inv 80%positive 81%positive 82%positive 150%positive.
Definition TSstate ge M : taskst := (ge,emp,M,empisr,(true,nil,nil)).
Definition TSclientbody n := sseq (scall 203%Z nil) (scall 202%Z (cons (econst32 n) nil)).
Definition TSpc n : progunit := fun f =>
  if Z.eq_dec f 300%Z then Some(Tvoid,dnil,dnil,TSclientbody n) else None.

Theorem TSinternal_checked :
  WFFuncsSim RAinternal RAspec V293_scheduler RAli TSinv.
Proof.
  apply WFFunEnv_imply_WFFuncsSim.
  apply V293_OSSchedNew_WFFunEnv;discriminate.
Qed.

Lemma TSstructure : forall n,
  no_fun_same TSapi RAinternal /\ no_call_api_pu RAinternal TSapi /\
  good_os_pu RAinternal /\ GoodClient (TSpc n) TSapi RAinternal /\
  GoodStmt (TSclientbody n) RAinternal.
Proof.
  intro n. split.
  - unfold no_fun_same,TSapi,V293_source_time_program,RAinternal,V293_OSSchedNew_internal_unit.
    split;intros f H;repeat destruct Z.eq_dec;try congruence.
  - split.
    + intros f tau d1 d2 s H. unfold RAinternal,V293_OSSchedNew_internal_unit in H.
      destruct Z.eq_dec;try discriminate;inversion H;subst;simpl;tauto.
    + split.
      * intros f tau d1 d2 s H. unfold RAinternal,V293_OSSchedNew_internal_unit in H.
        destruct Z.eq_dec;try discriminate;inversion H;subst;simpl;tauto.
      * split.
        -- unfold GoodClient. split.
           ++ intros f tau d1 d2 s H. unfold TSpc in H.
              destruct Z.eq_dec;try discriminate;inversion H;subst;vm_compute;tauto.
           ++ split;intros f H;
                unfold TSpc,TSapi,V293_source_time_program in *;
                repeat destruct Z.eq_dec;try congruence.
        -- vm_compute;tauto.
Qed.

Lemma TSlocal : forall ge t M O,
  get ge 1001%Z=Some(150%positive,Tint32) ->
  satp (TSstate ge M) O (CurTid t) ->
  InitTaskSt RAli t (TSstate ge M,O).
Proof.
  intros ge t M O Name Current. split;[ | reflexivity]. intro op.
  specialize (Current op). unfold LINV,RAli,V293_time_names_li.
  assert (Local : (TSstate ge (emp:mem),emp,op) |=
      Agvarenv 1001%Z Tint32 (150%positive,0%Z) **
      [|GoodLInvAsrt (V293_time_names_li 1001%Z 150%positive)|] **
      OS[empisr,true,nil,nil]).
  { apply astar_l_agvarenv_intro.
    - apply astar_l_apure_intro;[ | apply V293_time_names_local_good].
      unfold TSstate.
      repeat first [solve [repeat split;reflexivity] |
        eapply sat_split'; exists (emp:mem); exists (emp:mem);
        exists (emp:osabst); exists (emp:osabst);
        split;[apply map_join_emp | ];split;[apply map_join_emp | ];split].
    - split;[reflexivity | exact Name]. }
  eapply sat_split'. exists M. exists (emp:mem). exists O. exists (emp:osabst).
  split;[apply map_join_emp | ]. split;[apply map_join_emp | ].
  split.
  - exact Current.
  - apply astar_assoc_intro;exact Local.
Qed.

Lemma TScore_inv : forall ge M O op,
  (TSstate ge M,O,op) |= V293_time_ready_core 80%positive 81%positive 82%positive 150%positive ->
  (TSstate ge M,O,op) |= INV TSinv.
Proof.
  intros ge M O op Core. unfold INV.
  apply astar_l_aemp_intro. left. unfold inv_ieon.
  eapply sat_split'. exists (emp:mem). exists M. exists (emp:osabst). exists O.
  split;[apply map_join_comm;apply map_join_emp | ].
  split;[apply map_join_comm;apply map_join_emp | ]. split.
  - repeat split;reflexivity.
  - apply V293_time_ready_irq_close;[intro;reflexivity | exact Core].
Qed.

Theorem TSnonempty_joint_entry : forall t clock,
  exists Ml Ms Ol Os,
    join Ml Ms (TRmemory t clock) /\ join Ol Os (TRabstract t clock) /\
    InitTaskSt RAli t (TSstate JGE Ml,Ol) /\
    satp (TSstate JGE Ms) Os (INV TSinv).
Proof.
  intros t clock. pose proof (Jcore_and_current t clock (END None)) as Held.
  apply sat_split in Held. destruct Held as (Ms&Ml&Os&Ol&JM&JO&Core&Current).
  assert (AllCurrent : satp (TSstate JGE Ml) Ol (CurTid t)).
  { intro op. eapply V293_current_entry_context;[reflexivity | exact Current]. }
  exists Ml. exists Ms. exists Ol. exists Os.
  split;[apply map_join_comm;exact JM | ]. split;[apply map_join_comm;exact JO | ].
  split.
  - apply TSlocal;[reflexivity | exact AllCurrent].
  - intro op. apply TScore_inv.
    eapply V293_time_ready_entry_context;[reflexivity | exact Core].
Qed.

(* The ISR maps are not replaced by an empty installation. Their structural
   compatibility remains explicit; no WFInt/ISR-body result is inferred. *)
Theorem TSget_set_client : forall ip intspec t clock n,
  no_call_api_ipu ip TSapi -> EqDomInt ip intspec ->
  exists Ml Ms Ol Os,
    join Ml Ms (TRmemory t clock) /\ join Ol Os (TRabstract t clock) /\
    InitTaskSt RAli t (TSstate JGE Ml,Ol) /\
    satp (TSstate JGE Ms) Os (INV TSinv) /\
    TaskSim (TSpc n,(TSapi,RAinternal,ip)) (nilcont(TSclientbody n))
      (TSstate JGE Ml) (TSpc n,(TSaspec,intspec,V293_scheduler))
      (nilcont(TSclientbody n)) Ol RAli TSinv (InitTaskSt RAli t) t.
Proof.
  intros ip intspec t clock n Calls Dom.
  destruct (TSnonempty_joint_entry t clock) as (Ml&Ms&Ol&Os&JM&JO&Entry&Inv).
  destruct (TSstructure n) as [Sep [IC [Syn [Client Stmt]]]].
  exists Ml. exists Ms. exists Ol. exists Os.
  split;[exact JM | ]. split;[exact JO | ]. split;[exact Entry | ]. split;[exact Inv | ].
  eapply V293_source_time_ready_tasksim with (Spec:=RAspec);try discriminate;
    try eassumption;exact TSinternal_checked.
Qed.

Theorem TSmissing_name_entry : forall t M O,
  ~ InitTaskSt RAli t (TSstate (del JGE 1001%Z) M,O).
Proof.
  intros t M O [Held Empty]. specialize (Held (END None)).
  apply sat_split in Held. destruct Held as (m1&m2&o1&o2&JM&JO&Cur&Rest).
  apply sat_split in Rest. destruct Rest as (m3&m4&o3&o4&JM'&JO'&Name&Flags).
  unfold LINV,RAli,V293_time_names_li in Name.
  apply astar_l_agvarenv_elim in Name. destruct Name as [[Offset Lookup] Resource].
  change (get (del JGE 1001%Z) 1001%Z=Some(150%positive,Tint32)) in Lookup.
  change (EnvMod.get (EnvMod.del JGE 1001%Z) 1001%Z=Some(150%positive,Tint32)) in Lookup.
  rewrite EnvMod.map_del_sem in Lookup.
  destruct (EnvMod.map_dec_a 1001%Z 1001%Z);congruence.
Qed.

Theorem TSname_single_factor : forall t clock,
  exists Ml Ms Ol Os,
    join Ml Ms (TRmemory t clock) /\ join Ol Os (TRabstract t clock) /\
    InitTaskSt RAli t (TSstate JGE Ml,Ol) /\
    satp (TSstate JGE Ms) Os (INV TSinv) /\
    satp (TSstate (del JGE 1001%Z) Ms) Os (INV TSinv) /\
    (forall x,x<>1001%Z -> get(del JGE 1001%Z)x=get JGE x) /\
    ~InitTaskSt RAli t (TSstate (del JGE 1001%Z) Ml,Ol).
Proof.
  intros t clock. pose proof (Jcore_and_current t clock (END None)) as Held.
  apply sat_split in Held. destruct Held as (Ms&Ml&Os&Ol&JM&JO&Core&Current).
  exists Ml. exists Ms. exists Ol. exists Os.
  split;[apply map_join_comm;exact JM | ]. split;[apply map_join_comm;exact JO | ].
  split.
  - apply TSlocal;[reflexivity | intro op].
    eapply V293_current_entry_context;[reflexivity | exact Current].
  - split.
    + intro op. apply TScore_inv.
      eapply V293_time_ready_entry_context;[reflexivity | exact Core].
    + split.
      * intro op. apply TScore_inv.
        eapply V293_time_ready_entry_context with (ge:=JGE);[reflexivity | exact Core].
      * split.
        -- intros x NE. change (EnvMod.get (EnvMod.del JGE 1001%Z) x=EnvMod.get JGE x).
           rewrite EnvMod.map_del_sem. destruct (EnvMod.map_dec_a 1001%Z x);congruence.
        -- apply TSmissing_name_entry.
Qed.
