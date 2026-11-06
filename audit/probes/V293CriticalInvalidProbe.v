(* Independently typed expected interfaces and physical samples. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import Coq.Lists.List Lia.
Local Open Scope nat_scope.

(* Deliberately spell out the outer guard/encrit sequence independently. *)
Example expected_invalid_interface :
  forall P ks ge le caller M f body next suffix ir enabled si ci
    table oldprio newprio ptcb current reserved bo bn old new,
  old < 256 -> new < 256 ->
  ((12 <= old /\ old <> 255) \/ 12 <= new) ->
  get le oldprio = Some (bo,Tint8) -> get le newprio = Some (bn,Tint8) ->
  load Tint8 M (bo,0%Z) = Some (V293_byteval old) ->
  load Tint8 M (bn,0%Z) = Some (V293_byteval new) ->
  callcont ks = Some (kcall f body caller next) ->
  NoDup (map fst (getaddr le)) ->
  (forall c t, In (c,t) (getaddr le) -> V293_bytes_writable M c 0%Z (typelen t)) ->
  exists Mf,
    V293_local_steps P
      (curs (sseq
        (sseq (V293_task_prio_argument_guards oldprio newprio)
          (sseq (sprim encrit) (V293_primitive_entry table oldprio newprio ptcb current reserved)))
        suffix),(kenil,ks))
      ((ge,le,M),ir,(enabled,si,ci))
      (curs (sskip (Some (Vint32 (Int.repr 42)))),(kenil,next))
      ((ge,caller,Mf),ir,(enabled,si,ci)) /\
    (forall c i, ~ In c (map fst (getaddr le)) -> get Mf (c,i) = get M (c,i)) /\
    (forall c t k, In (c,t) (getaddr le) -> k < typelen t -> get Mf (c,Z.of_nat k) = None).
Proof. exact V293_invalid_critical_return. Qed.

Definition expected_invalid_physical P old new enabled ir si ci :=
  exists Mf,
    V293_local_steps P
      (curs (sseq (V293_primitive_critical_prefix 500%Z 501%Z 502%Z 400%Z 750%Z 603%Z)
        (scall 999%Z nil)),(kenil,kcall 700%Z sret emp kstop))
      ((emp,V293_critical_fixture_le,V293_invalid_critical_fixture_mem old new),ir,(enabled,si,ci))
      (curs (sskip (Some (Vint32 (Int.repr 42)))),(kenil,kstop))
      ((emp,emp,Mf),ir,(enabled,si,ci)) /\
    (forall k, k < 4 -> get Mf (61%positive,Z.of_nat k) = None) /\
    get Mf (51%positive,0%Z) = None /\ get Mf (52%positive,0%Z) = None /\
    load Tint8 Mf (90%positive,0%Z) = Some (V293_byteval 23).

Example expected_invalid_witness : forall P old new enabled ir si ci,
  old < 256 -> new < 256 -> ((12 <= old /\ old <> 255) \/ 12 <= new) ->
  expected_invalid_physical P old new enabled ir si ci.
Proof. exact V293_invalid_critical_witness. Qed.

(* Three different guard routes, SAME program and empty globals. *)
Example expected_invalid_samples : forall P enabled ir si ci,
  expected_invalid_physical P 12 6 enabled ir si ci /\
  expected_invalid_physical P 8 12 enabled ir si ci /\
  expected_invalid_physical P 255 12 enabled ir si ci.
Proof.
  intros P enabled ir si ci. split.
  - apply expected_invalid_witness;lia.
  - split;apply expected_invalid_witness;lia.
Qed.
Print Assumptions expected_invalid_interface.
Print Assumptions expected_invalid_witness.
Print Assumptions expected_invalid_samples.
