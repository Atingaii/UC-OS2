(* Handwritten literal expectations, not extracted from candidate headers.
   This is not an independent C front end. Symbolic representation, critical calls and full API remain explicit boundaries. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import Coq.Lists.List.
Local Open Scope nat_scope.
Local Opaque HalfPermMap.set.

Definition checked_fields : decllist :=
  dcons 1%Z (Tptr Tint32) (dcons 2%Z (Tptr Tvoid)
  (dcons 3%Z (Tptr Tint32) (dcons 4%Z Tint32
  (dcons 5%Z Tint16 (dcons 6%Z Tint16
  (dcons 7%Z (Tcom_ptr 410%Z) (dcons 8%Z (Tcom_ptr 410%Z)
  (dcons 9%Z (Tcom_ptr 411%Z) (dcons 10%Z (Tptr Tvoid)
  (dcons 11%Z (Tcom_ptr 412%Z) (dcons 12%Z Tint16
  (dcons (Z.opp 1) (Tarray Tint8 2) (dcons 13%Z Tint32
  (dcons 14%Z Tint8 (dcons 15%Z Tint8 (dcons 16%Z Tint8
  (dcons 17%Z Tint8 (dcons 18%Z Tint8 (dcons 19%Z Tint8
  (dcons 20%Z Tint8 (dcons 21%Z Tint8 dnil))))))))))))))))))))).
Definition checked_tcb := Tstruct 410%Z checked_fields.
Definition checked_byte n := Vint32 (Int.repr (Z.of_nat n)).
Definition checked_ge_limit (p : var) :=
  eunop oppsite (ebinop olt (ecast (evar p) Tint32) (econst32 (Int.repr 12))).
Definition checked_self (p : var) :=
  ebinop oeq (ecast (evar p) Tint32) (econst32 (Int.repr 255)).
Definition checked_arguments (oldprio newprio : var) :=
  sseq (sifthen (checked_ge_limit oldprio)
    (sifthen (eunop oppsite (checked_self oldprio)) (srete (econst32 (Int.repr 42)))))
    (sifthen (checked_ge_limit newprio) (srete (econst32 (Int.repr 42)))).
Definition checked_stop old new newprio ks : code :=
  let bad := curs (sskip (Some (checked_byte 42))) in
  if old <? 12 then
    if new <? 12 then (curs (sskip None),(kenil,ks)) else (bad,(kenil,kret ks))
  else if old =? 255 then
    if new <? 12 then (curs (sskip None),(kenil,ks)) else (bad,(kenil,kret ks))
  else (bad,(kenil,kret (kseq (sifthen (checked_ge_limit newprio)
    (srete (econst32 (Int.repr 42)))) ks))).
Definition checked_null e := ebinop oeq e (ecast enull (Tptr checked_tcb)).
Definition checked_lookup table oldprio newprio ptcb current cpu_sr exit_id :=
  sseq (sifthen (eunop oppsite (checked_null (earrayelem (evar table) (evar newprio))))
    (sseq (scall exit_id (evar cpu_sr :: nil)) (srete (econst32 (Int.repr 40)))))
    (sseq (sifthen (checked_self oldprio)
      (sassign (evar oldprio) (efield (ederef (evar current)) 16%Z)))
      (sseq (sassign (evar ptcb) (earrayelem (evar table) (evar oldprio)))
        (sifthen (checked_null (evar ptcb))
          (sseq (scall exit_id (evar cpu_sr :: nil)) (srete (econst32 (Int.repr 41))))))).
Definition checked_writable M b i n :=
  forall k, k < n -> exists v, get M (b,(i+Z.of_nat k)%Z) = Some (true,v).

Definition checked_entries : list val :=
  Vnull :: Vnull :: Vnull :: Vnull :: Vptr (60%positive,Int.zero) :: Vnull :: Vnull ::
  Vnull :: Vptr (41%positive,Int.repr 8) :: Vnull :: Vnull :: Vnull :: Vnull :: nil.
Fixpoint checked_bytes (M : mem) (b : block) (i : Z) (bytes : list memval) : mem :=
  match bytes with nil => M | v :: rest => set (checked_bytes M b (i+1)%Z rest) (b,i) (true,v) end.
Fixpoint checked_table (M : mem) (b : block) (i : Z) (entries : list val) : mem :=
  match entries with nil => M | v :: rest =>
    checked_bytes (checked_table M b (i+4)%Z rest) b i (encode_val (Tptr checked_tcb) v) end.
Definition checked_put (M : mem) (a : addr) n :=
  set M a (true,Byte (Byte.repr (Int.unsigned (Int.repr (Z.of_nat n))))).
Definition checked_ge : env :=
  set (set emp 500%Z (50%positive,Tarray (Tptr checked_tcb) 13)) 750%Z (80%positive,Tptr checked_tcb).
Definition checked_le : env :=
  set (set (set emp 501%Z (51%positive,Tint8)) 502%Z (52%positive,Tint8)) 400%Z (40%positive,Tptr checked_tcb).
Definition checked_core : mem :=
  checked_bytes (checked_bytes emp 80%positive 0%Z
    (encode_val (Tptr checked_tcb) (Vptr (41%positive,Int.repr 8))))
    40%positive 0%Z (encode_val (Tptr checked_tcb) Vnull).
Definition checked_memory (self : bool) : mem :=
  checked_put (checked_put (checked_put
    (checked_table checked_core 50%positive 0%Z checked_entries)
    (41%positive,58%Z) 8) (51%positive,0%Z) (if self then 255 else 8)) (52%positive,0%Z) 6.

(* Static address token: neither a memory load nor machine integer address 1. *)
Definition checked_symbol reserved := ecast (eaddrof (evar reserved)) (Tptr checked_tcb).
Definition checked_matches (br : block) (value : val) : bool :=
  match value with
  | Vptr (b,i) => if peq b br then Int.eq i Int.zero else false
  | _ => false
  end.
Definition checked_error (cpu_sr : var) (exit_id : fid) :=
  sseq (scall exit_id (evar cpu_sr :: nil)) (srete (econst32 (Int.repr 67))).
Definition checked_guard ptcb reserved cpu_sr exit_id :=
  sifthen (ebinop oeq (evar ptcb) (checked_symbol reserved)) (checked_error cpu_sr exit_id).
Definition checked_program table oldprio newprio ptcb current reserved cpu_sr exit_id :=
  sseq (checked_lookup table oldprio newprio ptcb current cpu_sr exit_id)
    (checked_guard ptcb reserved cpu_sr exit_id).
Definition checked_reserved_ge : env := set checked_ge 900%Z (99%positive,Tint8).

Definition checked_symbol_root : forall ge le M reserved br,
  get le reserved = None -> get ge reserved = Some (br,Tint8) ->
  evaltype (checked_symbol reserved) (ge,le,M) = Some (Tptr checked_tcb) /\
  evalval (checked_symbol reserved) (ge,le,M) = Some (Vptr (br,Int.zero))
  := V293_reserved_symbol_eval.
Print Assumptions checked_symbol_root.

Definition checked_equality_root : forall br next,
  next <> (br,Int.zero) ->
  val_eq Vnull (Vptr (br,Int.zero)) = Some (Vint32 Int.zero) /\
  val_eq (Vptr (br,Int.zero)) (Vptr (br,Int.zero)) = Some (Vint32 Int.one) /\
  val_eq (Vptr next) (Vptr (br,Int.zero)) = Some (Vint32 Int.zero)
  := V293_reserved_three_way_equality.
Print Assumptions checked_equality_root.

Definition checked_select_root :
  forall P ks ge le M ptcb reserved (cpu_sr : var) (exit_id : fid) bc br value,
  get le ptcb = Some (bc,Tptr checked_tcb) ->
  load (Tptr checked_tcb) M (bc,0%Z) = Some value ->
  (value = Vnull \/ exists next, value = Vptr next) ->
  get le reserved = None -> get ge reserved = Some (br,Tint8) ->
  cstepstar P (curs (checked_guard ptcb reserved cpu_sr exit_id),(kenil,ks))
    (ge,le,M)
    (curs (if checked_matches br value
      then checked_error cpu_sr exit_id else sskip None),(kenil,ks)) (ge,le,M)
  := V293_task_prio_reserved_select.
Print Assumptions checked_select_root.

Definition checked_continuous_root :
  forall P ks ge le M table oldprio newprio ptcb current reserved (cpu_sr : var) (exit_id : fid)
    b bo bn bc bcur bct base old new curprio next br,
  old < 256 -> new < 12 ->
  let resolved := if old =? 255 then curprio else old in
  resolved < 13 ->
  get le table = None -> get ge table = Some (b,Tarray (Tptr checked_tcb) 13) ->
  get le oldprio = Some (bo,Tint8) -> get le newprio = Some (bn,Tint8) ->
  get le ptcb = Some (bc,Tptr checked_tcb) ->
  load Tint8 M (bo,0%Z) = Some (checked_byte old) ->
  load Tint8 M (bn,0%Z) = Some (checked_byte new) ->
  load (Tptr checked_tcb) M (b,(4*Z.of_nat new)%Z) = Some Vnull ->
  load (Tptr checked_tcb) M (b,(4*Z.of_nat resolved)%Z) = Some (Vptr next) ->
  b <> bo -> b <> bc -> bo <> bn -> bc <> bn -> bc <> bo ->
  (old = 255 ->
    get le current = None /\ get ge current = Some (bcur,Tptr checked_tcb) /\
    load (Tptr checked_tcb) M (bcur,0%Z) = Some (Vptr (bct,Int.repr base)) /\
    (0 <= base)%Z /\ (base+50 <= Int.max_unsigned)%Z /\
    load Tint8 M (bct,(base+50)%Z) = Some (checked_byte curprio) /\
    (exists v, get M (bo,0%Z) = Some (true,v))) ->
  get le reserved = None -> get ge reserved = Some (br,Tint8) ->
  next <> (br,Int.zero) ->
  checked_writable M bc 0%Z 4 ->
  exists Mf,
  resolved <> new /\
  cstepstar P (curs (checked_program table oldprio newprio ptcb current reserved cpu_sr exit_id),
    (kenil,ks)) (ge,le,M) (curs (sskip None),(kenil,ks)) (ge,le,Mf) /\
  load Tint8 Mf (bo,0%Z) = Some (checked_byte resolved) /\
  load Tint8 Mf (bn,0%Z) = Some (checked_byte new) /\
  load (Tptr checked_tcb) Mf (bc,0%Z) = Some (Vptr next) /\
  load (Tptr checked_tcb) Mf (b,(4*Z.of_nat resolved)%Z) = Some (Vptr next) /\
  load (Tptr checked_tcb) Mf (b,(4*Z.of_nat new)%Z) = Some Vnull /\
  checked_writable Mf bc 0%Z 4 /\
  (forall c i, c <> bo -> c <> bc -> get Mf (c,i) = get M (c,i))
  := V293_task_prio_entry_reserved_execution.
Print Assumptions checked_continuous_root.

Definition checked_noncollision_root : forall br,
  checked_matches br (Vptr (br,Int.zero)) = true /\ checked_matches br Vnull = false
  := V293_reserved_noncollision_needed.
Print Assumptions checked_noncollision_root.

Definition checked_witness_root : forall self P ks,
  exists Mf,
  load (Tptr checked_tcb) (checked_memory self) (40%positive,0%Z) = Some Vnull /\
  cstepstar P (curs (checked_program
    500%Z 501%Z 502%Z 400%Z 750%Z 900%Z 751%Z 752%Z),(kenil,ks))
    (checked_reserved_ge,checked_le,checked_memory self)
    (curs (sskip None),(kenil,ks)) (checked_reserved_ge,checked_le,Mf) /\
  load Tint8 Mf (51%positive,0%Z) = Some (checked_byte 8) /\
  load Tint8 Mf (52%positive,0%Z) = Some (checked_byte 6) /\
  load (Tptr checked_tcb) Mf (40%positive,0%Z) = Some (Vptr (41%positive,Int.repr 8)) /\
  load (Tptr checked_tcb) Mf (50%positive,32%Z) = Some (Vptr (41%positive,Int.repr 8)) /\
  load (Tptr checked_tcb) Mf (50%positive,24%Z) = Some Vnull
  := V293_task_prio_reserved_witness.
Print Assumptions checked_witness_root.
