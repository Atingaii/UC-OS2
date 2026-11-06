(* Actual finite OSTimeTick while. Owned Next links, field-based guards and
   the three actual iteration theorems; no execution oracle or global Inv. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickExpiry.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickCountdown.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickTraversal.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.code.V293OSTimeTick.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition V293_tick_after_delay d := if Z.eqb d 0 then 0%Z else (d-1)%Z.
Definition V293_tick_after_stat d s := if Z.eqb d 1 then V293_tick_expired_stat s else s.
Definition V293_tick_after_pend d p s := if Z.eqb d 1 then V293_tick_expired_pend s else p.
Definition V293_tick_after_group d s g y := if Z.eqb d 1 then V293_tick_expired_group s g y else g.
Definition V293_tick_after_row d s r x := if Z.eqb d 1 then V293_tick_expired_row s r x else r.
Definition V293_tick_iteration_tail bt base s pend y x bg g br r : list V293_record_cell :=
  [((bt,(base+48)%Z),Tint8,V293_byteval s);
   ((bt,(base+49)%Z),Tint8,V293_byteval pend);
   ((bt,(base+52)%Z),Tint8,V293_byteval y);
   ((bt,(base+54)%Z),Tint8,V293_byteval (2^y));
   ((bt,(base+53)%Z),Tint8,V293_byteval (2^x));
   ((bg,0%Z),Tint8,V293_byteval g);
   ((br,Z.of_nat y),Tint8,V293_byteval r)].

Theorem V293_tick_all_iteration_owned_execution :
  forall P ks ge le M ir enabled si ci O op ptcb rows group bc bt base next d s pend y x bg g br r R,
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  get le rows = None -> get ge rows = Some (br,Tarray Tint8 2) ->
  get le group = None -> get ge group = Some (bg,Tint8) ->
  (0 <= base)%Z -> (base+54 <= Int.max_unsigned)%Z -> (0<=d<=Int.max_unsigned)%Z ->
  s < 256 -> pend < 256 -> y < 2 -> x < 8 -> g < 256 -> r < 256 ->
  (ge,le,M,ir,(enabled,si,ci),O,op) |= V293_owned_record_cells
    (V293_tick_expiry_cells bc bt base (bt,Int.repr base) (Int.repr d) next s pend y x bg g br r) ** R ->
  exists Mf,
  V293_local_steps P (curs (V293_tick_iteration ptcb rows group),(kenil,ks))
    ((ge,le,M),ir,(enabled,si,ci))
    (curs (sskip None),(kenil,ks)) ((ge,le,Mf),ir,(enabled,si,ci)) /\
  (ge,le,Mf,ir,(enabled,si,ci),O,op) |= V293_owned_record_cells
    (V293_tick_expiry_cells bc bt base next (Int.repr (V293_tick_after_delay d)) next
      (V293_tick_after_stat d s) (V293_tick_after_pend d pend s) y x bg
      (V293_tick_after_group d s g y) br (V293_tick_after_row d s r x)) ** R.
Proof.
  intros P ks ge le M ir enabled si ci O op ptcb rows group bc bt base next d s pend y x bg g br r R
    Bind Nr Gr Ng Gg Base Limit D S Pend Y X G Row Owned.
  destruct (Z.eq_dec d 0) as [Zero|Nonzero].
  - subst d.
    assert (Entry : (ge,le,M,ir,(enabled,si,ci),O,op) |=
      V293_owned_record_cell ((bc,0%Z),Tptr V293_tcb_type,Vptr (bt,Int.repr base)) **
      (V293_tick_zero_node bt base next **
        (V293_owned_record_cells (V293_tick_iteration_tail bt base s pend y x bg g br r) ** R))).
    { cbn [V293_tick_expiry_cells V293_tick_iteration_tail V293_owned_record_cells] in Owned |- *.
      unfold V293_tick_zero_node. clear -Owned. sep auto. }
    destruct (V293_tick_zero_iteration_owned_execution P ks ge le M ir enabled si ci O op
      ptcb rows group bc bt base next _ Bind Base ltac:(lia) Entry)
      as (Mf & Store & Exec & Pointer & Returned & Outside).
    exists Mf. split; [exact Exec | ].
    cbn [V293_tick_after_delay V293_tick_after_stat V293_tick_after_pend
      V293_tick_after_group V293_tick_after_row V293_tick_expiry_cells V293_owned_record_cells].
    unfold V293_tick_zero_node,V293_tick_iteration_tail in Returned.
    cbn [V293_owned_record_cells] in Returned. clear -Returned. sep auto.
  - destruct (Z.eq_dec d 1) as [One|Notone].
    + subst d.
      destruct (V293_tick_expiry_iteration_owned_execution P ks ge le M ir enabled si ci O op
        ptcb rows group bc bt base next s pend y x bg g br r R
        Bind Nr Gr Ng Gg Base Limit S Pend Y X G Row Owned)
        as (Mf & Exec & Dly & Stat & Pnd & Group & Rw & Pointer & Returned).
      exists Mf. split; [exact Exec | exact Returned].
    + assert (E0 : Z.eqb d 0 = false) by (apply Z.eqb_neq; exact Nonzero).
      assert (E1 : Z.eqb d 1 = false) by (apply Z.eqb_neq; exact Notone).
      assert (Entry : (ge,le,M,ir,(enabled,si,ci),O,op) |=
        V293_owned_record_cell ((bc,0%Z),Tptr V293_tcb_type,Vptr (bt,Int.repr base)) **
        (V293_tick_countdown_node bt base d next **
          (V293_owned_record_cells (V293_tick_iteration_tail bt base s pend y x bg g br r) ** R))).
      { cbn [V293_tick_expiry_cells V293_tick_iteration_tail V293_owned_record_cells] in Owned |- *.
        unfold V293_tick_countdown_node. clear -Owned. sep auto. }
      destruct (V293_tick_countdown_iteration_owned_execution P ks ge le M ir enabled si ci O op
        ptcb rows group bc bt base d next _ Bind Base ltac:(lia) ltac:(lia) Entry)
        as (M1 & Mf & Store1 & Storef & Exec & Dly & Pointer & Returned & Outside).
      exists Mf. split; [exact Exec | ].
      unfold V293_tick_after_delay,V293_tick_after_stat,V293_tick_after_pend,
        V293_tick_after_group,V293_tick_after_row. rewrite E0,E1.
      cbn [V293_tick_expiry_cells V293_owned_record_cells].
      unfold V293_tick_countdown_node,V293_tick_iteration_tail in Returned.
      cbn [V293_owned_record_cells] in Returned. clear -Returned. sep auto.
Qed.

(* Only fields read or written by this while, not a complete TCB. Next is
   derived from the list itself rather than postulating an execution chain. *)
Record V293_tick_task := {
  V293_tick_block : block;
  V293_tick_base : Z;
  V293_tick_delay_value : Z;
  V293_tick_stat_value : nat;
  V293_tick_pend_value : nat;
  V293_tick_y : nat;
  V293_tick_x : nat;
  V293_tick_prio : nat
}.
Definition V293_tick_task_pointer t := (V293_tick_block t,Int.repr (V293_tick_base t)).
Definition V293_tick_head tasks idle :=
  match tasks with [] => idle | t::_ => V293_tick_task_pointer t end.
Definition V293_tick_task_valid t :=
  (0<=V293_tick_base t /\ V293_tick_base t+54<=Int.max_unsigned)%Z /\
  (0<=V293_tick_delay_value t<=Int.max_unsigned)%Z /\
  V293_tick_stat_value t<256 /\ V293_tick_pend_value t<256 /\
  V293_tick_y t<2 /\ V293_tick_x t<8 /\
  V293_tick_prio t<256 /\ V293_tick_prio t<>12.
Definition V293_tick_task_cells t next : list V293_record_cell :=
  let b:=V293_tick_block t in let off:=V293_tick_base t in
  [((b,(off+44)%Z),Tint32,Vint32 (Int.repr (V293_tick_delay_value t)));
   ((b,(off+20)%Z),Tcom_ptr 410%Z,Vptr next);
   ((b,(off+48)%Z),Tint8,V293_byteval (V293_tick_stat_value t));
   ((b,(off+49)%Z),Tint8,V293_byteval (V293_tick_pend_value t));
   ((b,(off+52)%Z),Tint8,V293_byteval (V293_tick_y t));
   ((b,(off+54)%Z),Tint8,V293_byteval (2^(V293_tick_y t)));
   ((b,(off+53)%Z),Tint8,V293_byteval (2^(V293_tick_x t)));
   ((b,(off+50)%Z),Tint8,V293_byteval (V293_tick_prio t))].
Definition V293_tick_task_after t :=
  Build_V293_tick_task (V293_tick_block t) (V293_tick_base t)
    (V293_tick_after_delay (V293_tick_delay_value t))
    (V293_tick_after_stat (V293_tick_delay_value t) (V293_tick_stat_value t))
    (V293_tick_after_pend (V293_tick_delay_value t) (V293_tick_pend_value t) (V293_tick_stat_value t))
    (V293_tick_y t) (V293_tick_x t) (V293_tick_prio t).
Fixpoint V293_tick_chain_cells tasks idle : list V293_record_cell :=
  match tasks with
  | [] => []
  | t::rest => V293_tick_task_cells t (V293_tick_head rest idle) ++ V293_tick_chain_cells rest idle
  end.
Definition V293_tick_bitmap_cells bg br g lo hi : list V293_record_cell :=
  [((bg,0%Z),Tint8,V293_byteval g);((br,0%Z),Tint8,V293_byteval lo);((br,1%Z),Tint8,V293_byteval hi)].
Definition V293_tick_idle_cell idle : V293_record_cell :=
  ((fst idle,(Int.unsigned (snd idle)+50)%Z),Tint8,V293_byteval 12).
Definition V293_tick_pointer_cell bc pointer : V293_record_cell :=
  ((bc,0%Z),Tptr V293_tcb_type,Vptr pointer).
Definition V293_tick_loop_owned bc pointer tasks idle bg br g lo hi R : asrt :=
  V293_owned_record_cell (V293_tick_pointer_cell bc pointer) **
  (V293_owned_record_cells (V293_tick_chain_cells tasks idle) **
    (V293_owned_record_cells (V293_tick_bitmap_cells bg br g lo hi) **
      (V293_owned_record_cell (V293_tick_idle_cell idle) ** R))).

Lemma V293_tick_cells_append : forall prefix suffix st,
  st |= V293_owned_record_cells (prefix++suffix) <->
  st |= V293_owned_record_cells prefix ** V293_owned_record_cells suffix.
Proof.
  induction prefix as [ | c prefix IH]; intros suffix st; cbn [app V293_owned_record_cells].
  - split; [apply astar_l_aemp_intro | apply astar_l_aemp_elim].
  - split; intro H.
    + apply astar_assoc_intro. eapply astar_mono; [ | | exact H].
      * intros s A; exact A.
      * intros s A; apply IH; exact A.
    + apply astar_assoc_elim in H. eapply astar_mono; [ | | exact H].
      * intros s A; exact A.
      * intros s A; apply IH; exact A.
Qed.

Definition V293_tick_next_group t g := V293_tick_after_group
  (V293_tick_delay_value t) (V293_tick_stat_value t) g (V293_tick_y t).
Definition V293_tick_next_lo t lo := if Nat.eqb (V293_tick_y t) 0 then
  V293_tick_after_row (V293_tick_delay_value t) (V293_tick_stat_value t) lo (V293_tick_x t) else lo.
Definition V293_tick_next_hi t hi := if Nat.eqb (V293_tick_y t) 1 then
  V293_tick_after_row (V293_tick_delay_value t) (V293_tick_stat_value t) hi (V293_tick_x t) else hi.

Lemma V293_tick_node_iteration_owned_execution :
  forall P ks ge le M ir enabled si ci O op ptcb rows group bc t next bg br g lo hi R,
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  get le rows = None -> get ge rows = Some (br,Tarray Tint8 2) ->
  get le group = None -> get ge group = Some (bg,Tint8) ->
  V293_tick_task_valid t -> g<256 -> lo<256 -> hi<256 ->
  (ge,le,M,ir,(enabled,si,ci),O,op) |=
    V293_owned_record_cell (V293_tick_pointer_cell bc (V293_tick_task_pointer t)) **
    (V293_owned_record_cells (V293_tick_task_cells t next) **
      (V293_owned_record_cells (V293_tick_bitmap_cells bg br g lo hi) ** R)) ->
  exists Mf,
  V293_local_steps P (curs (V293_tick_iteration ptcb rows group),(kenil,ks))
    ((ge,le,M),ir,(enabled,si,ci))
    (curs (sskip None),(kenil,ks)) ((ge,le,Mf),ir,(enabled,si,ci)) /\
  (ge,le,Mf,ir,(enabled,si,ci),O,op) |=
    V293_owned_record_cell (V293_tick_pointer_cell bc next) **
    (V293_owned_record_cells (V293_tick_task_cells (V293_tick_task_after t) next) **
      (V293_owned_record_cells (V293_tick_bitmap_cells bg br
        (V293_tick_next_group t g) (V293_tick_next_lo t lo) (V293_tick_next_hi t hi)) ** R)).
Proof.
  intros P ks ge le M ir enabled si ci O op ptcb rows group bc t next bg br g lo hi R
    Bind Nr Gr Ng Gg Valid G Lo Hi Owned.
  destruct t as [b off d s p y x prio].
  destruct Valid as ([Base Limit] & D & S & Pend & Y & X & Prio & Nonidle).
  cbn in Base,Limit,D,S,Pend,Y,X,Prio,Nonidle.
  assert (Rows : y=0 \/ y=1) by lia. destruct Rows as [Row|Row]; subst y.
  - assert (Entry : (ge,le,M,ir,(enabled,si,ci),O,op) |= V293_owned_record_cells
      (V293_tick_expiry_cells bc b off (b,Int.repr off) (Int.repr d) next s p 0 x bg g br lo) **
      (V293_owned_record_cell ((b,(off+50)%Z),Tint8,V293_byteval prio) **
        (V293_owned_record_cell ((br,1%Z),Tint8,V293_byteval hi) ** R))).
    { cbn [V293_tick_expiry_cells V293_tick_pointer_cell V293_tick_task_pointer
        V293_tick_task_cells V293_tick_bitmap_cells V293_owned_record_cells] in Owned |- *.
      clear -Owned. sep auto. }
    destruct (V293_tick_all_iteration_owned_execution P ks ge le M ir enabled si ci O op
      ptcb rows group bc b off next d s p 0 x bg g br lo _
      Bind Nr Gr Ng Gg Base Limit D S Pend ltac:(lia) X G Lo Entry) as (Mf & Exec & Returned).
    exists Mf. split; [exact Exec | ].
    cbn [V293_tick_pointer_cell V293_tick_task_pointer V293_tick_task_cells V293_tick_task_after
      V293_tick_bitmap_cells V293_tick_next_group V293_tick_next_lo V293_tick_next_hi V293_owned_record_cells].
    cbn [V293_tick_expiry_cells V293_owned_record_cells] in Returned. clear -Returned. sep auto.
  - assert (Entry : (ge,le,M,ir,(enabled,si,ci),O,op) |= V293_owned_record_cells
      (V293_tick_expiry_cells bc b off (b,Int.repr off) (Int.repr d) next s p 1 x bg g br hi) **
      (V293_owned_record_cell ((b,(off+50)%Z),Tint8,V293_byteval prio) **
        (V293_owned_record_cell ((br,0%Z),Tint8,V293_byteval lo) ** R))).
    { cbn [V293_tick_expiry_cells V293_tick_pointer_cell V293_tick_task_pointer
        V293_tick_task_cells V293_tick_bitmap_cells V293_owned_record_cells] in Owned |- *.
      clear -Owned. sep auto. }
    destruct (V293_tick_all_iteration_owned_execution P ks ge le M ir enabled si ci O op
      ptcb rows group bc b off next d s p 1 x bg g br hi _
      Bind Nr Gr Ng Gg Base Limit D S Pend ltac:(lia) X G Hi Entry) as (Mf & Exec & Returned).
    exists Mf. split; [exact Exec | ].
    cbn [V293_tick_pointer_cell V293_tick_task_pointer V293_tick_task_cells V293_tick_task_after
      V293_tick_bitmap_cells V293_tick_next_group V293_tick_next_lo V293_tick_next_hi V293_owned_record_cells].
    cbn [V293_tick_expiry_cells V293_owned_record_cells] in Returned. clear -Returned. sep auto.
Qed.

Lemma V293_tick_next_bitmap_bounds : forall t g lo hi,
  V293_tick_task_valid t -> g<256 -> lo<256 -> hi<256 ->
  V293_tick_next_group t g<256 /\ V293_tick_next_lo t lo<256 /\ V293_tick_next_hi t hi<256.
Proof.
  intros t g lo hi Valid G Lo Hi.
  destruct Valid as (Base & D & S & Pend & Y & X & Prio & Nonidle).
  destruct (V293_rekey_byte_arithmetic g (V293_tick_y t) G ltac:(lia)) as [_ [GB RestG]].
  destruct (V293_rekey_byte_arithmetic lo (V293_tick_x t) Lo X) as [_ [LB RestL]].
  destruct (V293_rekey_byte_arithmetic hi (V293_tick_x t) Hi X) as [_ [HB RestH]].
  unfold V293_tick_next_group,V293_tick_next_lo,V293_tick_next_hi,
    V293_tick_after_group,V293_tick_after_row,V293_tick_expired_group,V293_tick_expired_row.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end; auto.
Qed.

Lemma V293_tick_guard_eval : forall ge le M ptcb bc bt base p,
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  load (Tptr V293_tcb_type) M (bc,0%Z) = Some (Vptr (bt,Int.repr base)) ->
  (0<=base)%Z -> (base+50<=Int.max_unsigned)%Z -> p<256 ->
  load Tint8 M (bt,(base+50)%Z) = Some (V293_byteval p) ->
  evalval (V293_tick_guard ptcb) (ge,le,M) =
    Some (Vint32 (if Nat.eqb p 12 then Int.zero else Int.one)).
Proof.
  intros ge le M ptcb bc bt base p Bind Pointer Base Limit Prio Read.
  destruct (V293_tick_field_eval ge le M ptcb bc bt base 16%Z 50%Z Tint8 _
    Bind Pointer eq_refl eq_refl Base ltac:(lia) Limit Read) as [Tp Vp].
  assert (Compare : Int.eq (Int.repr (Z.of_nat p)) (Int.repr 12) = Nat.eqb p 12).
  { destruct (Nat.eq_dec p 12) as [Same|Apart].
    - subst p. reflexivity.
    - rewrite (proj2 (Nat.eqb_neq p 12) Apart). apply Int.eq_false. intro Eq.
      apply (f_equal Int.unsigned) in Eq.
      rewrite (Int.unsigned_repr (Z.of_nat p)) in Eq by
        (change (0<=Z.of_nat p<=4294967295)%Z; lia).
      rewrite (Int.unsigned_repr 12) in Eq by
        (change (0<=12<=4294967295)%Z; lia).
      apply Apart. lia. }
  unfold V293_tick_guard,V293_tick_ne,V293_tick_eq.
  cbn [evalval evaltype]. rewrite Tp,Vp.
  change (match (if Int.eq (Int.repr (Z.of_nat p)) (Int.repr 12)
    then Some (Vint32 Int.one) else Some (Vint32 Int.zero)) with
    | Some v => notint v | None => None end =
    Some (Vint32 (if Nat.eqb p 12 then Int.zero else Int.one))).
  rewrite Compare. destruct (Nat.eqb p 12); reflexivity.
Qed.

Fixpoint V293_tick_chain_bitmap tasks g lo hi : nat * (nat * nat) :=
  match tasks with
  | [] => (g,(lo,hi))
  | t::rest => V293_tick_chain_bitmap rest
      (V293_tick_next_group t g) (V293_tick_next_lo t lo) (V293_tick_next_hi t hi)
  end.
Lemma V293_tick_head_after : forall tasks idle,
  V293_tick_head (map V293_tick_task_after tasks) idle = V293_tick_head tasks idle.
Proof. intros tasks idle. destruct tasks; reflexivity. Qed.

Lemma V293_tick_loop_fields_load : forall bc pointer tasks idle bg br g lo hi R st a tp v,
  In (a,tp,v) (V293_tick_pointer_cell bc pointer ::
    (V293_tick_chain_cells tasks idle ++ (V293_tick_bitmap_cells bg br g lo hi ++ [V293_tick_idle_cell idle]))) ->
  st |= V293_tick_loop_owned bc pointer tasks idle bg br g lo hi R ->
  load tp (getmem st) a = Some v.
Proof.
  intros bc pointer tasks idle bg br g lo hi R st a tp v Member Owned.
  unfold V293_tick_loop_owned in Owned. destruct Member as [Same|Member].
  - inversion Same; subst. eapply V293_record_star_load_l; [apply V293_owned_record_cell_load | exact Owned].
  - apply in_app_iff in Member. destruct Member as [Node|Member].
    + eapply V293_record_star_load_r; [ | exact Owned]. eapply V293_record_star_load_l.
      apply V293_owned_record_cells_load. exact Node.
    + apply in_app_iff in Member. destruct Member as [Bitmap|Member].
      * eapply V293_record_star_load_r; [ | exact Owned]. eapply V293_record_star_load_r.
        eapply V293_record_star_load_l. apply V293_owned_record_cells_load. exact Bitmap.
      * destruct Member as [Same|Empty]; [ | contradiction]. inversion Same; subst.
        eapply V293_record_star_load_r; [ | exact Owned]. eapply V293_record_star_load_r.
        eapply V293_record_star_load_r. eapply V293_record_star_load_l. apply V293_owned_record_cell_load.
Qed.

Theorem V293_tick_while_owned_execution :
  forall tasks P ks ge le M ir enabled si ci O op ptcb rows group bc idle bg br g lo hi R,
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  get le rows = None -> get ge rows = Some (br,Tarray Tint8 2) ->
  get le group = None -> get ge group = Some (bg,Tint8) ->
  (Int.unsigned (snd idle)+50<=Int.max_unsigned)%Z ->
  Forall V293_tick_task_valid tasks -> g<256 -> lo<256 -> hi<256 ->
  (ge,le,M,ir,(enabled,si,ci),O,op) |=
    V293_tick_loop_owned bc (V293_tick_head tasks idle) tasks idle bg br g lo hi R ->
  let '(gf,(lof,hif)) := V293_tick_chain_bitmap tasks g lo hi in
  exists Mf,
  V293_local_steps P
    (curs (swhile (V293_tick_guard ptcb) (V293_tick_iteration ptcb rows group)),(kenil,ks))
    ((ge,le,M),ir,(enabled,si,ci))
    (curs (sskip None),(kenil,ks)) ((ge,le,Mf),ir,(enabled,si,ci)) /\
  load (Tptr V293_tcb_type) Mf (bc,0%Z) = Some (Vptr idle) /\
  (ge,le,Mf,ir,(enabled,si,ci),O,op) |=
    V293_tick_loop_owned bc idle (map V293_tick_task_after tasks) idle bg br gf lof hif R.
Proof.
  induction tasks as [ | t rest IH];
    intros P ks ge le M ir enabled si ci O op ptcb rows group bc idle bg br g lo hi R
      Bind Nr Gr Ng Gg IdleLimit Valid G Lo Hi Owned.
  - cbn [V293_tick_chain_bitmap map].
    assert (Pointer : load (Tptr V293_tcb_type) M (bc,0%Z) = Some (Vptr idle)).
    { change (load (Tptr V293_tcb_type) (getmem (ge,le,M,ir,(enabled,si,ci),O,op)) (bc,0%Z) = Some (Vptr idle)).
      eapply V293_tick_loop_fields_load; [left;reflexivity | exact Owned]. }
    assert (Read : load Tint8 M (fst idle,(Int.unsigned (snd idle)+50)%Z) = Some (V293_byteval 12)).
    { change (load Tint8 (getmem (ge,le,M,ir,(enabled,si,ci),O,op))
        (fst idle,(Int.unsigned (snd idle)+50)%Z) = Some (V293_byteval 12)).
      eapply V293_tick_loop_fields_load; [ | exact Owned].
      right. apply in_app_iff. right. apply in_app_iff. right. left. reflexivity. }
    assert (Normalized : load (Tptr V293_tcb_type) M (bc,0%Z) =
      Some (Vptr (fst idle,Int.repr (Int.unsigned (snd idle))))).
    { rewrite Int.repr_unsigned. destruct idle; exact Pointer. }
    pose proof (V293_tick_guard_eval ge le M ptcb bc (fst idle) (Int.unsigned (snd idle)) 12
      Bind Normalized (proj1 (Int.unsigned_range _)) IdleLimit ltac:(lia) Read) as Guard.
    exists M. split.
    + eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity | apply swhile_step]. }
      eapply V293_local_trans.
      { apply V293_csteps_local. apply V293_expr_steps. apply evalval_imply_estepstar. exact Guard. }
      eapply V293_local_cons.
      { apply ostc_step. eapply stmt_step; [reflexivity | apply svwhilef_step;reflexivity]. }
      apply V293_local_refl.
    + split; [exact Pointer | exact Owned].
  - inversion Valid as [ | t0 rest0 HeadValid TailValid]; subst t0 rest0.
    pose proof HeadValid as Bounds.
    destruct Bounds as ([Base Limit] & Delay & Stat & Pend & Y & X & Prio & Nonidle).
    assert (Pointer : load (Tptr V293_tcb_type) M (bc,0%Z) = Some (Vptr (V293_tick_task_pointer t))).
    { change (load (Tptr V293_tcb_type) (getmem (ge,le,M,ir,(enabled,si,ci),O,op)) (bc,0%Z) = Some (Vptr (V293_tick_task_pointer t))).
      eapply V293_tick_loop_fields_load; [left;reflexivity | exact Owned]. }
    assert (Read : load Tint8 M (V293_tick_block t,(V293_tick_base t+50)%Z) = Some (V293_byteval (V293_tick_prio t))).
    { change (load Tint8 (getmem (ge,le,M,ir,(enabled,si,ci),O,op))
        (V293_tick_block t,(V293_tick_base t+50)%Z) = Some (V293_byteval (V293_tick_prio t))).
      eapply V293_tick_loop_fields_load; [ | exact Owned].
      right. apply in_app_iff. left. cbn [V293_tick_chain_cells]. apply in_app_iff. left.
      unfold V293_tick_task_cells. simpl. tauto. }
    pose proof (V293_tick_guard_eval ge le M ptcb bc (V293_tick_block t) (V293_tick_base t)
      (V293_tick_prio t) Bind Pointer Base ltac:(lia) Prio Read) as Guard.
    assert (Notidle : Nat.eqb (V293_tick_prio t) 12 = false) by (apply Nat.eqb_neq; exact Nonidle).
    rewrite Notidle in Guard.
    assert (Opened : (ge,le,M,ir,(enabled,si,ci),O,op) |=
      V293_owned_record_cell (V293_tick_pointer_cell bc (V293_tick_task_pointer t)) **
      (V293_owned_record_cells (V293_tick_task_cells t (V293_tick_head rest idle)) **
        (V293_owned_record_cells (V293_tick_chain_cells rest idle) **
          (V293_owned_record_cells (V293_tick_bitmap_cells bg br g lo hi) **
            (V293_owned_record_cell (V293_tick_idle_cell idle) ** R))))).
    { unfold V293_tick_loop_owned in Owned. cbn [V293_tick_head V293_tick_chain_cells] in Owned.
      eapply astar_mono; [ | | exact Owned].
      - intros st H; exact H.
      - intros st H. apply astar_assoc_elim. eapply astar_mono; [ | | exact H].
        + intros st0 H0. apply V293_tick_cells_append. exact H0.
        + intros st0 H0; exact H0. }
    assert (Entry : (ge,le,M,ir,(enabled,si,ci),O,op) |=
      V293_owned_record_cell (V293_tick_pointer_cell bc (V293_tick_task_pointer t)) **
      (V293_owned_record_cells (V293_tick_task_cells t (V293_tick_head rest idle)) **
        (V293_owned_record_cells (V293_tick_bitmap_cells bg br g lo hi) **
          (V293_owned_record_cells (V293_tick_chain_cells rest idle) **
            (V293_owned_record_cell (V293_tick_idle_cell idle) ** R))))) by (clear -Opened; sep auto).
    destruct (V293_tick_node_iteration_owned_execution P
      (kseq (swhile (V293_tick_guard ptcb) (V293_tick_iteration ptcb rows group)) ks)
      ge le M ir enabled si ci O op ptcb rows group bc t (V293_tick_head rest idle) bg br g lo hi _
      Bind Nr Gr Ng Gg HeadValid G Lo Hi Entry) as (M1 & StepExec & ReturnedStep).
    destruct (V293_tick_next_bitmap_bounds t g lo hi HeadValid G Lo Hi) as [G1 [Lo1 Hi1]].
    assert (EntryRest : (ge,le,M1,ir,(enabled,si,ci),O,op) |=
      V293_tick_loop_owned bc (V293_tick_head rest idle) rest idle bg br
        (V293_tick_next_group t g) (V293_tick_next_lo t lo) (V293_tick_next_hi t hi)
        (V293_owned_record_cells (V293_tick_task_cells (V293_tick_task_after t) (V293_tick_head rest idle)) ** R)).
    { unfold V293_tick_loop_owned. clear -ReturnedStep. sep auto. }
    specialize (IH P ks ge le M1 ir enabled si ci O op ptcb rows group bc idle bg br
      (V293_tick_next_group t g) (V293_tick_next_lo t lo) (V293_tick_next_hi t hi) _
      Bind Nr Gr Ng Gg IdleLimit TailValid G1 Lo1 Hi1 EntryRest).
    cbn [V293_tick_chain_bitmap].
    destruct (V293_tick_chain_bitmap rest (V293_tick_next_group t g)
      (V293_tick_next_lo t lo) (V293_tick_next_hi t hi)) as [gf [lof hif]] eqn:Bitmap.
    destruct IH as (Mf & RestExec & FinalPointer & ReturnedRest).
    exists Mf. split.
    + eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity | apply swhile_step]. }
      eapply V293_local_trans.
      { apply V293_csteps_local. apply V293_expr_steps. apply evalval_imply_estepstar. exact Guard. }
      eapply V293_local_cons.
      { apply ostc_step. eapply stmt_step; [reflexivity | apply svwhilet_step;reflexivity]. }
      eapply V293_local_trans; [exact StepExec | ].
      eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity | apply sskip_step]. }
      exact RestExec.
    + split; [exact FinalPointer | ].
      assert (Combined : (ge,le,Mf,ir,(enabled,si,ci),O,op) |=
        V293_owned_record_cell (V293_tick_pointer_cell bc idle) **
        ((V293_owned_record_cells (V293_tick_task_cells (V293_tick_task_after t) (V293_tick_head rest idle)) **
          V293_owned_record_cells (V293_tick_chain_cells (map V293_tick_task_after rest) idle)) **
          (V293_owned_record_cells (V293_tick_bitmap_cells bg br gf lof hif) **
            (V293_owned_record_cell (V293_tick_idle_cell idle) ** R)))).
      { unfold V293_tick_loop_owned in ReturnedRest. clear -ReturnedRest. sep auto. }
      unfold V293_tick_loop_owned. cbn [map V293_tick_chain_cells]. rewrite V293_tick_head_after.
      eapply astar_mono; [ | | exact Combined].
      * intros st H; exact H.
      * intros st H. eapply astar_mono; [ | | exact H].
        -- intros st0 H0. apply V293_tick_cells_append. exact H0.
        -- intros st0 H0; exact H0.
Qed.

Print Assumptions V293_tick_all_iteration_owned_execution.
Print Assumptions V293_tick_node_iteration_owned_execution.
Print Assumptions V293_tick_guard_eval.
Print Assumptions V293_tick_while_owned_execution.
