(* Same original increment and same physical memory in both control arms.
   Only omission of the abstract clock update is varied. *)
Require Import CertiOS.audit.probes.V293TimeNamesGoodProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickShared.
Require Import CertiOS.certiucos.v293.proofs.V293TimeShared.
Require Import CertiOS.certiucos.v293.proofs.V293TimeSharedSet.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickCountdown.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.step_prop.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Theorem checked_tick_step_exact : forall sd O result O' clock,
  get O ostmid=Some (ostm clock) ->
  spec_step sd V293_tick_clock_action O (END result) O' ->
  result=None /\ O'=set O ostmid (ostm (Int.add clock Int.one)).
Proof.
  intros sd O result O' clock Time Step.
  unfold V293_tick_clock_action in Step. inversion Step;subst.
  match goal with H : V293_tick_clock_step _ _ _ |- _ =>
    destruct H as [_ [n [Read Eq]]] end.
  inversion Eq;subst.
  assert (Whole : get O ostmid=Some (ostm n)).
  { eapply OSAbstMod.join_get_l;eassumption. }
  assert (n=clock) by congruence. subst n.
  assert (No : get Of ostmid=None).
  { destruct (get Of ostmid) as [v | ] eqn:E;[ | reflexivity].
    exfalso. eapply OSAbstMod.map_join_get_some with (x:=O0) (y:=Of) (z:=O);
      [reflexivity | eassumption | exact Read | exact E]. }
  split;[reflexivity | ].
  eapply map_join_deter;[eassumption | ].
  eapply OSAbstMod.map_join_set_none;eassumption.
Qed.

Theorem checked_tick_other_slots : forall sd O result O' clock k,
  get O ostmid=Some (ostm clock) -> k<>ostmid ->
  spec_step sd V293_tick_clock_action O (END result) O' -> get O' k=get O k.
Proof.
  intros sd O result O' clock k Time Different Step.
  destruct (checked_tick_step_exact sd O result O' clock Time Step) as [_ E].
  rewrite E. apply map_get_set';congruence.
Qed.

Theorem checked_tick_positive : forall sd,
  spec_step sd V293_tick_clock_action (NamesAbstract (Int.repr 37)) (END None)
    (set (NamesAbstract (Int.repr 37)) ostmid (ostm (Int.repr 38))).
Proof.
  intro sd. replace (Int.repr 38) with (Int.add (Int.repr 37) Int.one) by reflexivity.
  apply V293_tick_clock_transition;reflexivity.
Qed.

Theorem checked_tick_wrong_increment : forall sd,
  ~spec_step sd V293_tick_clock_action (NamesAbstract (Int.repr 37)) (END None)
    (set (NamesAbstract (Int.repr 37)) ostmid (ostm (Int.repr 39))).
Proof.
  intros sd Step.
  destruct (checked_tick_step_exact sd (NamesAbstract (Int.repr 37)) None
    (set (NamesAbstract (Int.repr 37)) ostmid (ostm (Int.repr 39)))
    (Int.repr 37) ltac:(reflexivity) Step) as [_ E].
  apply (f_equal (fun O=>get O ostmid)) in E. vm_compute in E;discriminate.
Qed.

Theorem checked_tick_wrap : forall sd,
  Int.add (Int.repr Int.max_unsigned) Int.one=Int.zero /\
  spec_step sd V293_tick_clock_action (NamesAbstract (Int.repr Int.max_unsigned)) (END None)
    (set (NamesAbstract (Int.repr Int.max_unsigned)) ostmid (ostm Int.zero)).
Proof.
  intro sd. assert (Wrap : Int.add (Int.repr Int.max_unsigned) Int.one=Int.zero) by (vm_compute;apply Int.mkint_eq;reflexivity).
  split;[exact Wrap | ]. rewrite <- Wrap. apply V293_tick_clock_transition;reflexivity.
Qed.

(* A nonempty spatial entry: current pointer and the four actual clock bytes.
   TCB/ECB maps here are empty; this is not a reachable kernel-init witness. *)
Theorem checked_tick_clock_spatial : forall clock,
  NamesState (merge NamesPointer (NamesClock clock)) (NamesAbstract clock) |=
    V293_time_shared_fields clock ** PV (80%positive,Int.zero) @ Tint32 |-> Vint32 clock.
Proof.
  intro clock. destruct (NamesCoreSpatial clock) as [n Owned].
  assert (Read : get (NamesAbstract clock) ostmid=Some (ostm n)).
  { change (get (getabst (NamesState (merge NamesPointer (NamesClock clock)) (NamesAbstract clock)))
      ostmid=Some (ostm n)).
    exact (@V293_star_abst_get_l _ (PV (80%positive,Int.zero) @ Tint32 |-> Vint32 n)
      ostmid _ (V293_time_fields_clock n) _ Owned). }
  assert (Literal : get (NamesAbstract clock) ostmid=Some (ostm clock)) by reflexivity.
  assert (n=clock) by congruence. subst n. exact Owned.
Qed.

Theorem checked_tick_physical_control : forall P ks,
  exists Mf,
    cstepstar P
      (curs (sassign (evar 1001%Z) (ebinop oplus (evar 1001%Z) (econst32 Int.one))),(kenil,ks))
      (NamesGE,NamesLE,merge NamesPointer (NamesClock (Int.repr 37)))
      (curs (sskip None),(kenil,ks)) (NamesGE,NamesLE,Mf) /\
    load Tint32 Mf (80%positive,0%Z)=Some (Vint32 (Int.repr 38)) /\
    ~NamesState Mf (NamesAbstract (Int.repr 37)) |= V293_time_shared_core 80%positive /\
    NamesState Mf (set (NamesAbstract (Int.repr 37)) ostmid (ostm (Int.repr 38))) |=
      V293_time_shared_core 80%positive.
Proof.
  intros P ks. pose proof (checked_tick_clock_spatial (Int.repr 37)) as Core.
  assert (Entry : NamesState (merge NamesPointer (NamesClock (Int.repr 37))) (NamesAbstract (Int.repr 37)) |=
    V293_owned_record_cell ((80%positive,0%Z),Tint32,Vint32 (Int.repr 37)) **
      V293_time_shared_fields (Int.repr 37)).
  { cbn [V293_owned_record_cell]. clear -Core. sep auto. }
  destruct (V293_owned_record_cell_update (80%positive,0%Z) Tint32 _ (Vint32 (Int.repr 38))
    _ _ _ _ _ _ _ _ eq_refl Entry) as (Mf & Store & Returned).
  assert (Read : load Tint32 Mf (80%positive,0%Z)=Some (Vint32 (Int.repr 38))).
  { change (load Tint32 (getmem (NamesState Mf (NamesAbstract (Int.repr 37))))
      (80%positive,0%Z)=Some (Vint32 (Int.repr 38))).
    eapply V293_record_star_load_l;[apply V293_owned_record_cell_load | exact Returned]. }
  exists Mf. split.
  - eapply V293_tick_assign32_execution with (b:=80%positive) (off:=0%Z);try exact Store.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + change (match load Tint32 (merge NamesPointer (NamesClock (Int.repr 37))) (80%positive,0%Z)
        with Some v => add v (Vint32 Int.one) Tint32 Tint32 | None => None end = Some (Vint32 (Int.repr 38))).
      rewrite (proj2 (NamesLiteralClockAgreement (Int.repr 37))). reflexivity.
    + change (0<=0<=4294967295)%Z;lia.
  - split;[exact Read | ]. split.
    + intro Wrong. destruct (V293_time_shared_clock_agreement _ _ _ _ _ _ _ _ Wrong)
        as [n [Abstract Physical]].
      change (get (NamesAbstract (Int.repr 37)) ostmid=Some (ostm n)) in Abstract.
      assert (Literal : get (NamesAbstract (Int.repr 37)) ostmid=Some (ostm (Int.repr 37))) by reflexivity.
      assert (n=Int.repr 37) by congruence. subst n.
      change (load Tint32 Mf (80%positive,0%Z)=Some (Vint32 (Int.repr 37))) in Physical.
      rewrite Read in Physical. vm_compute in Physical;discriminate.
    + assert (Slots : NamesState Mf (NamesAbstract (Int.repr 37)) |=
        Aabsdata ostmid (ostm (Int.repr 37)) **
          ((EX t : tid, EX ts : TcbMod.map, EX es : EcbMod.map,
            CurTid t ** (Aabsdata curtid (oscurt t) **
              (Aabsdata abstcblsid (abstcblist ts) ** Aabsdata absecblsid (absecblist es)))) **
            PV (80%positive,Int.zero) @ Tint32 |-> Vint32 (Int.repr 38))).
      { unfold V293_owned_record_cell,V293_time_shared_fields,V293_shared_fields in Returned.
        clear -Returned. sep auto. }
      apply V293_shared_replace_slot with (new:=ostm (Int.repr 38)) in Slots.
      unfold V293_time_shared_core,V293_time_shared_fields,V293_shared_fields.
      clear -Slots. sep auto.
Qed.
