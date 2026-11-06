(* Independently written interface probes. Not a whole-function specification. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import Coq.Lists.List.
Local Open Scope nat_scope.

Example expected_error_interface :
  forall P ks ge le caller M f body next suffix ir enabled si ci
    table oldprio newprio ptcb current reserved b bo bn bc bcur bct base old new curprio br absent,
  old < 256 -> (old < 12 \/ old = 255) -> new < 12 ->
  let resolved := if old =? 255 then curprio else old in
  resolved < 13 ->
  get le table = None -> get ge table = Some (b,Tarray (Tptr V293_tcb_type) 13) ->
  get le oldprio = Some (bo,Tint8) -> get le newprio = Some (bn,Tint8) ->
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  (absent = false -> get le reserved = None /\ get ge reserved = Some (br,Tint8)) ->
  load Tint8 M (bo,0%Z) = Some (V293_byteval old) ->
  load Tint8 M (bn,0%Z) = Some (V293_byteval new) ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat new)%Z) = Some Vnull ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat resolved)%Z) =
    Some (if absent then Vnull else Vptr (br,Int.zero)) ->
  b <> bo -> bc <> bo ->
  (old = 255 ->
    get le current = None /\ get ge current = Some (bcur,Tptr V293_tcb_type) /\
    load (Tptr V293_tcb_type) M (bcur,0%Z) = Some (Vptr (bct,Int.repr base)) /\
    (0 <= base)%Z /\ (base+50 <= Int.max_unsigned)%Z /\
    load Tint8 M (bct,(base+50)%Z) = Some (V293_byteval curprio) /\
    (exists v, get M (bo,0%Z) = Some (true,v))) ->
  callcont ks = Some (kcall f body caller next) ->
  NoDup (map fst (getaddr le)) ->
  (forall c t, In (c,t) (getaddr le) -> V293_bytes_writable M c 0%Z (typelen t)) ->
  exists Mf,
    V293_local_steps P
      (curs (sseq (V293_primitive_critical_prefix table oldprio newprio ptcb current reserved) suffix),(kenil,ks))
      ((ge,le,M),ir,(enabled,si,ci))
      (curs (sskip (Some (Vint32 (Int.repr (if absent then 41 else 67))))),(kenil,next))
      ((ge,caller,Mf),ir,(enabled,si,ci)) /\
    (forall c j, ~ In c (map fst (getaddr le)) -> get Mf (c,j) = get M (c,j)) /\
    (forall c t k, In (c,t) (getaddr le) -> k < typelen t -> get Mf (c,Z.of_nat k) = None).
Proof. exact V293_lookup_error_critical_return. Qed.

Example expected_physical_errors : forall P self absent enabled ir,
  load (Tptr V293_tcb_type) (V293_lookup_critical_fixture_mem self absent) (40%positive,0%Z) =
    Some (Vptr (70%positive,Int.zero)) /\
  load Tint32 (V293_lookup_critical_fixture_mem self absent) (61%positive,0%Z) =
    Some (Vint32 (Int.repr 23)) /\
  exists Mf,
    V293_local_steps P
      (curs (sseq (V293_primitive_critical_prefix 500%Z 501%Z 502%Z 400%Z 750%Z 603%Z)
        (scall 999%Z nil)),(kenil,kcall 700%Z sret emp kstop))
      ((V293_error_fixture_ge,V293_error_fixture_le,V293_lookup_critical_fixture_mem self absent),
        ir,(enabled,nil,nil))
      (curs (sskip (Some (Vint32 (Int.repr (if absent then 41 else 67))))),(kenil,kstop))
      ((V293_error_fixture_ge,emp,Mf),ir,(enabled,nil,nil)) /\
    (forall k, k < 4 -> get Mf (40%positive,Z.of_nat k) = None /\ get Mf (61%positive,Z.of_nat k) = None) /\
    get Mf (51%positive,0%Z) = None /\ get Mf (52%positive,0%Z) = None /\
    load (Tptr V293_tcb_type) Mf (50%positive,32%Z) =
      Some (if absent then Vnull else Vptr (90%positive,Int.zero)).
Proof. exact V293_lookup_error_critical_witness. Qed.

Example expected_permission_transport : forall bytes M M' b i,
  storebytes M (b,i) bytes = Some M' ->
  forall c j v, get M (c,j) = Some (true,v) ->
  exists w, get M' (c,j) = Some (true,w).
Proof. exact V293_storebytes_preserves_writable. Qed.

Print Assumptions expected_error_interface.
Print Assumptions expected_physical_errors.
Print Assumptions expected_permission_transport.
