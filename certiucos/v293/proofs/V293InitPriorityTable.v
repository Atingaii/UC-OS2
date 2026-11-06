(* Initialization-only table relation: no reservations and no extra pointers.
   The clear prefix and real between-hooks assignment return the same heap.
   This does not execute either hook or establish whole-kernel reachability. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.code.V293OSMemClr.
Require Import CertiOS.certiucos.v293.code.V293OSInitTCBClear.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBClear.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBList.
Require Import CertiOS.certiucos.v293.proofs.V293MemClr.
Require Import CertiOS.certiucos.v293.proofs.V293NullBytes.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitFunction.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition V293_init_priority_table (entries : list val) (tasks : TcbMod.map) :=
  V293SchedulerTasks.V293_priority_table entries tasks /\
  forall p, p<13 -> nth p entries Vnull=Vnull \/
    exists t status message, nth p entries Vnull=Vptr t /\
      get tasks t=Some(Int.repr(Z.of_nat p),status,message).

Lemma V293_init_priority_empty :
  V293_init_priority_table (repeat Vnull 13) (emp:TcbMod.map).
Proof.
  split.
  - split;[apply repeat_length | ]. intros t priority status message H.
    rewrite map_emp_get in H. discriminate.
  - intros p Bound. left. apply nth_repeat.
Qed.

Lemma V293_init_priority_nth_same : forall entries p value,
  p<length entries -> nth p (update_nth_val p entries value) Vnull=value.
Proof.
  induction entries as [ | x xs IH];intros [ | p] value Bound;cbn in *;try lia;
    [reflexivity | apply IH;lia].
Qed.
Lemma V293_init_priority_nth_other : forall entries p q value,
  p<>q -> nth p (update_nth_val q entries value) Vnull=nth p entries Vnull.
Proof.
  induction entries as [ | x xs IH];intros [ | p] [ | q] value Apart;
    cbn in *;try reflexivity;try congruence. apply IH;congruence.
Qed.

Theorem V293_init_priority_insert : forall entries tasks t p status message,
  V293_init_priority_table entries tasks -> p<13 ->
  nth p entries Vnull=Vnull -> get tasks t=None ->
  V293_init_priority_table (update_nth_val p entries (Vptr t))
    (set tasks t (Int.repr(Z.of_nat p),status,message)).
Proof.
  intros entries tasks t p status message [[Len Forward] Reverse] Range Empty Fresh.
  split.
  - split;[rewrite V293_priority_update_length;exact Len | ].
    intros u priority st msg Lookup. destruct (tidspec.beq u t) eqn:Same.
    + apply tidspec.beq_true_eq in Same. subst u. rewrite map_get_set in Lookup.
      inversion Lookup;subst. exists p. split;[exact Range | ]. split;[reflexivity | ].
      apply V293_init_priority_nth_same;lia.
    + assert (Apart:u<>t) by (apply tidspec.beq_false_neq;exact Same).
      rewrite map_get_set' in Lookup by congruence.
      destruct (Forward u priority st msg Lookup) as (q&Q&Priority&Slot).
      exists q. split;[exact Q | ]. split;[exact Priority | ].
      rewrite V293_init_priority_nth_other;[exact Slot | ].
      intro E;subst q. rewrite Empty in Slot;discriminate.
  - intros q Q. destruct (Nat.eq_dec q p) as [E | Apart].
    + subst q. right. exists t. exists status. exists message. split.
      * apply V293_init_priority_nth_same;lia.
      * apply map_get_set.
    + rewrite V293_init_priority_nth_other by exact Apart.
      destruct (Reverse q Q) as [Null | (u&st&msg&Slot&Lookup)];[left;exact Null | ].
      right. exists u. exists st. exists msg. split;[exact Slot | ].
      rewrite map_get_set';[exact Lookup | ]. intro E;subst u. change (TcbMod.get tasks t=None) in Fresh.
      change (TcbMod.get tasks t=Some(Int.repr(Z.of_nat q),st,msg)) in Lookup. congruence.
Qed.

(* The reverse condition is necessary: a pointer in an unused slot cannot
   be justified by the task-to-table direction alone. *)
Theorem V293_init_priority_pointer_exact : forall entries tasks p t,
  V293_init_priority_table entries tasks -> p<13 ->
  (nth p entries Vnull=Vptr t <->
    exists status message,get tasks t=Some(Int.repr(Z.of_nat p),status,message)).
Proof.
  intros entries tasks p t [[Len Forward] Reverse] Bound. split.
  - intro Slot. destruct (Reverse p Bound) as [Null | (u&st&msg&E&Lookup)];[congruence | ].
    assert (u=t) by congruence. subst u. exists st. exists msg;exact Lookup.
  - intros (st&msg&Lookup). destruct (Forward t _ st msg Lookup) as (q&Q&E&Slot).
    assert (q=p) by (eapply V293_priority_repr_injective;[exact Q |exact Bound |congruence]).
    subst q;exact Slot.
Qed.
Theorem V293_init_priority_null_exact : forall entries tasks p,
  V293_init_priority_table entries tasks -> p<13 ->
  (nth p entries Vnull=Vnull <->
    forall t status message,get tasks t<>Some(Int.repr(Z.of_nat p),status,message)).
Proof.
  intros entries tasks p Canonical Bound. split.
  - intros Null t st msg Lookup.
    pose proof (proj2(V293_init_priority_pointer_exact entries tasks p t Canonical Bound)
      (ex_intro _ st (ex_intro _ msg Lookup))). congruence.
  - intro Absent. destruct (proj2 Canonical p Bound) as [Null | (t&st&msg&Slot&Lookup)].
    + exact Null.
    + exfalso. exact (Absent t st msg Lookup).
Qed.

Lemma V293_init_null_cells_owned : forall n b off R,
  V293_rdy_raw_cells (V293_null_pointer_cells b off n) R ==>
    V293_owned_record_cells (V293_priority_cells b off (repeat Vnull n)) ** R.
Proof.
  induction n;intros b off R st H;cbn [V293_null_pointer_cells V293_rdy_raw_cells
    repeat V293_priority_cells V293_owned_record_cells] in *.
  - clear -H;sep auto.
  - assert (K:st |= V293_owned_record_cell ((b,off),Tptr V293_tcb_type,Vnull) **
       (V293_owned_record_cells (V293_priority_cells b (off+4)%Z (repeat Vnull n)) ** R)).
    { eapply astar_mono;[ |apply IHn |exact H]. intros s Cell.
      unfold V293_owned_record_cell. apply astar_l_apure_intro;[exact Cell |reflexivity]. }
    clear -K;sep auto.
Qed.

Theorem V293_OS_InitTCBList_canonical_clear : forall oldtcbs oldprios frame P ks ge le M
  ir aux O op f dest size table priorities bt bp,
  P f=Some (V293_MemClr_function dest size) -> dest<>size ->
  get le table=None -> get ge table=Some (bt,V293_tcb_table_type) ->
  get le priorities=None -> get ge priorities=Some (bp,V293_tcb_prio_table_type) ->
  length oldtcbs=728 -> length oldprios=52 ->
  (ge,le,M,ir,aux,O,op) |= V293_rdy_raw_cells
    (V293_clr_bytes bt 0 oldtcbs++V293_clr_bytes bp 0 oldprios++frame) Atrue ->
  exists Mf,
    cstepstar P (curs (V293_init_tcb_clear f table priorities),(kenil,ks)) (ge,le,M)
      (curs (sskip None),(kenil,ks)) (ge,le,Mf) /\
    V293_init_priority_table (repeat Vnull 13) (emp:TcbMod.map) /\
    (ge,le,Mf,ir,aux,O,op) |= V293_owned_priority_table bp (repeat Vnull 13) **
      V293_rdy_raw_cells (V293_clr_bytes bt 0 (repeat (Vint32 Int.zero) 728)++frame) Atrue.
Proof.
  intros oldtcbs oldprios frame P ks ge le M ir aux O op f dest size table priorities bt bp
    Program Names TL TG PL PG TLen PLen Owned.
  destruct (V293_OS_InitTCBList_cleared_tables oldtcbs oldprios frame P ks ge le M
    ir aux O op f dest size table priorities bt bp Program Names TL TG PL PG TLen PLen Owned)
    as (Mf&Exec&Final&Reads).
  exists Mf. split;[exact Exec | ]. split;[apply V293_init_priority_empty | ].
  repeat rewrite V293_raw_cells_append in Final |- *.
  apply V293_raw_cells_swap in Final.
  rewrite V293_raw_cells_append in Final.
  apply V293_init_null_cells_owned in Final.
  unfold V293_owned_priority_table. eapply astar_mono;
    [intros st H;exact H | apply V293_raw_cells_swap | exact Final].
Qed.

(* Stable source fragment interface: store success and all thirteen reads
   follow from full writable table ownership, not independent output oracles.
   The task-map insertion is a pure relation, not a hidden abstract step. *)
Theorem V293_OS_TCBInit_canonical_priority_write :
  forall entries tasks t p P ks ge le M ir aux O op R table bp bc,
  V293_init_priority_table entries tasks -> p<13 -> nth p entries Vnull=Vnull ->
  get tasks t=None ->
  get le 92%Z=None -> get ge 92%Z=Some(table,Tarray(Tptr V293_tcb_type)13) ->
  get le 101%Z=Some(bp,Tint8) -> get le 108%Z=Some(bc,Tptr V293_tcb_type) ->
  (ge,le,M,ir,aux,O,op) |= V293_owned_priority_table table entries **
    V293_rdy_raw_cells (((bp,0%Z),Tint8,V293_byteval p)::
      ((bc,0%Z),Tptr V293_tcb_type,Vptr t)::nil) R ->
  exists Mf,
    cstepstar P (curs(sassign(earrayelem(evar 92%Z)(evar 101%Z))(evar 108%Z)),(kenil,ks))
      (ge,le,M) (curs(sskip None),(kenil,ks)) (ge,le,Mf) /\
    store(Tptr V293_tcb_type)M(table,(4*Z.of_nat p)%Z)(Vptr t)=Some Mf /\
    V293_init_priority_table (update_nth_val p entries(Vptr t))
      (set tasks t (Int.repr(Z.of_nat p),rdy,Vnull)) /\
    (ge,le,Mf,ir,aux,O,op) |=
      V293_owned_priority_table table(update_nth_val p entries(Vptr t)) **
      V293_rdy_raw_cells (((bp,0%Z),Tint8,V293_byteval p)::
      ((bc,0%Z),Tptr V293_tcb_type,Vptr t)::nil) R /\
    V293_table_loads V293_tcb_type Mf table(update_nth_val p entries(Vptr t)).
Proof.
  intros entries tasks t p P ks ge le M ir aux O op R table bp bc
    Canonical Range Null Fresh Local Global PriorityLocal PointerLocal Owned.
  assert (Len:length entries=13) by exact(proj1(proj1 Canonical)).
  assert (Inputs:(ge,le,M,ir,aux,O,op) |=
    V293_rdy_raw_cells (((bp,0%Z),Tint8,V293_byteval p)::
      ((bc,0%Z),Tptr V293_tcb_type,Vptr t)::nil)
      (V293_owned_priority_table table entries ** R)) by (cbn[V293_rdy_raw_cells] in *;sep auto).
  assert (PriorityRead:load Tint8 M(bp,0%Z)=Some(V293_byteval p)).
  { change(load Tint8(getmem(ge,le,M,ir,aux,O,op))(bp,0%Z)=Some(V293_byteval p)).
    eapply V293_rdy_raw_load;[ | |exact Inputs];[left;reflexivity |exact(proj1(V293_tcb_init_byte_valid p Range))]. }
  assert (PointerRead:load(Tptr V293_tcb_type)M(bc,0%Z)=Some(Vptr t)).
  { change(load(Tptr V293_tcb_type)(getmem(ge,le,M,ir,aux,O,op))(bc,0%Z)=Some(Vptr t)).
    eapply V293_rdy_raw_load;[ | |exact Inputs];[right;left;reflexivity |reflexivity]. }
  destruct(V293_full_priority_table_any_slot_store entries table _ ge le M ir aux O op
    Len Owned p(Vptr t)Range eq_refl)as(Mf&Store&Final).
  destruct(V293_rekey_array_address ge le M 92%Z 101%Z V293_tcb_type table bp p
    Local Global PriorityLocal PriorityRead Range)as(SlotType&SlotAddress).
  assert (Value:evalval(evar 108%Z)(ge,le,M)=Some(Vptr t)) by V293_rdy_eval.
  assert (RhsType:evaltype(evar 108%Z)(ge,le,M)=Some(Tptr V293_tcb_type)) by V293_rdy_eval.
  exists Mf. split.
  - eapply V293_assign_pointer_execution;[exact SlotType |exact RhsType | |exact SlotAddress |exact Value | |exact Store].
    + apply eq_vptr. do 2 eexists;split;reflexivity.
    + change(0<=4*Z.of_nat p<=4294967295)%Z;lia.
  - split;[exact Store | ]. split.
    + apply V293_init_priority_insert;assumption.
    + split;[exact Final | ]. eapply V293_full_priority_table_loads;
        [rewrite V293_priority_update_length;exact Len |exact Final].
Qed.

Print Assumptions V293_OS_InitTCBList_canonical_clear.
Print Assumptions V293_OS_TCBInit_canonical_priority_write.
