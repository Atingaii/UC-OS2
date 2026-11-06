(* Handwritten expected interfaces. Not extracted from candidate headers and
   not a verified frontend or a proof that a C port implementation exists. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import Coq.Lists.List.
Local Open Scope nat_scope.

Definition checked_saved_value : forall M bs saved,
  V293_saved_ie M bs saved <->
  load Tint32 M (bs,0%Z) = Some (Vint32 (if saved then Int.one else Int.zero)) :=
  fun _ _ _ => conj (fun H => H) (fun H => H).

Definition checked_restore : forall P ks ge le M ir active si ci bs saved,
  V293_saved_ie M bs saved ->
  loststep P (curs (sprim excrit),(kenil,ks))
    ((ge,le,M),ir,(active,si,saved::ci))
    (curs (sskip None),(kenil,ks)) ((ge,le,M),ir,(saved,si,ci)) /\
  V293_saved_ie M bs saved := V293_excrit_restores_saved.

Definition checked_disabled : forall P ks ge le M ir si ci bs,
  V293_saved_ie M bs false ->
  loststep P (curs (sprim excrit),(kenil,ks))
    ((ge,le,M),ir,(false,si,false::ci))
    (curs (sskip None),(kenil,ks)) ((ge,le,M),ir,(false,si,ci)) :=
  fun P ks ge le M ir si ci bs T =>
    proj1 (V293_excrit_restores_saved P ks ge le M ir false si ci bs false T).

Definition checked_missing : forall P exit_id args types ks m ir au,
  P exit_id = None ->
  ~ exists C' state', loststep P (curs (sfexec exit_id args types),(kenil,ks))
    (m,ir,au) C' state' := V293_missing_port_has_no_step.

Definition checked_return : forall P ks ge le caller M f body next error,
  callcont ks = Some (kcall f body caller next) ->
  NoDup (map fst (getaddr le)) ->
  (forall b t, In (b,t) (getaddr le) -> V293_bytes_writable M b 0%Z (typelen t)) ->
  exists M',
    cstepstar P
      (curs (sskip None),(kenil,kseq (srete (econst32 (Int.repr error))) ks)) (ge,le,M)
      (curs (sskip (Some (Vint32 (Int.repr error)))),(kenil,next)) (ge,caller,M') /\
    (forall b i, ~ In b (map fst (getaddr le)) -> get M' (b,i) = get M (b,i)) /\
    (forall b t k, In (b,t) (getaddr le) -> k < typelen t -> get M' (b,Z.of_nat k) = None) :=
  V293_error_after_port_return.

Definition checked_reserved :
  forall P ks ge le M table oldprio newprio ptcb current reserved cpu_sr exit_id
    b bo bn bc bs bcur bct base old new curprio br saved,
  old < 256 -> new < 12 ->
  let resolved := if old =? 255 then curprio else old in
  resolved < 13 ->
  get le table = None -> get ge table = Some (b,Tarray (Tptr V293_tcb_type) 13) ->
  get le oldprio = Some (bo,Tint8) -> get le newprio = Some (bn,Tint8) ->
  get le ptcb = Some (bc,Tptr V293_tcb_type) -> get le cpu_sr = Some (bs,Tint32) ->
  get le reserved = None -> get ge reserved = Some (br,Tint8) ->
  load Tint8 M (bo,0%Z) = Some (V293_byteval old) ->
  load Tint8 M (bn,0%Z) = Some (V293_byteval new) ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat new)%Z) = Some Vnull ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat resolved)%Z) = Some (Vptr (br,Int.zero)) ->
  b <> bo -> b <> bc -> bo <> bn -> bc <> bn -> bc <> bo ->
  (old = 255 ->
    get le current = None /\ get ge current = Some (bcur,Tptr V293_tcb_type) /\
    load (Tptr V293_tcb_type) M (bcur,0%Z) = Some (Vptr (bct,Int.repr base)) /\
    (0 <= base)%Z /\ (base+50 <= Int.max_unsigned)%Z /\
    load Tint8 M (bct,(base+50)%Z) = Some (V293_byteval curprio) /\
    (exists v, get M (bo,0%Z) = Some (true,v))) ->
  V293_bytes_writable M bc 0%Z 4 ->
  bs <> bo -> bs <> bc -> V293_saved_ie M bs saved ->
  exists Mf,
    cstepstar P
      (curs (V293_task_prio_entry_reserved table oldprio newprio ptcb current reserved cpu_sr exit_id),(kenil,ks)) (ge,le,M)
      (curs (sfexec exit_id (Vptr (bs,Int.zero)::nil) (Tptr Tint32::nil)),
        (kenil,kseq (srete (econst32 (Int.repr 67))) ks)) (ge,le,Mf) /\
    V293_saved_ie Mf bs saved /\
    load (Tptr V293_tcb_type) Mf (bc,0%Z) = Some (Vptr (br,Int.zero)) /\
    (forall c i, c <> bo -> c <> bc -> get Mf (c,i) = get M (c,i)) :=
  V293_reserved_entry_preserves_saved.

Print Assumptions checked_saved_value.
Print Assumptions checked_restore.
Print Assumptions checked_disabled.
Print Assumptions checked_missing.
Print Assumptions checked_return.
Print Assumptions checked_reserved.
Print Assumptions V293_error_return_locals_witness.
Print Assumptions V293_reserved_saved_witness.
Print Assumptions V293_saved_byte_alias_counterexample.
