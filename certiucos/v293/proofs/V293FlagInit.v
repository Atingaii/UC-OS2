(* Actual FlagInit body with writable event fields and all untouched zero bytes. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSInitTCBList.
Require Import CertiOS.certiucos.v293.code.V293OSMemClr.
Require Import CertiOS.certiucos.v293.code.V293OSInitTCBClear.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBClear.
Require Import CertiOS.certiucos.v293.proofs.V293MemClr.
Require Import CertiOS.certiucos.v293.proofs.V293NullBytes.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Coq.Sorting.Permutation Lia.
Import ListNotations.
Local Open Scope Z_scope.

Require Import CertiOS.certiucos.v293.code.V293OSFlagInit.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBList.

Theorem V293_init_flag_layout : typelen V293_flag_type=12%nat /\
  typelen V293_flag_table_type=60%nat /\
  field_offset 1 V293_flag_fields=Some Int.zero /\ field_offset 2 V293_flag_fields=Some (Int.repr 4).
Proof. repeat split;reflexivity. Qed.

Fixpoint V293_flag_fields_cells b off n : list V293_record_cell :=
  match n with O=>[] | S m=>
    ((b,off),Tint8,Vint32 Int.zero)::((b,off+4),Tptr Tvoid,Vnull)::
    V293_flag_fields_cells b (off+12) m end.
Fixpoint V293_flag_untouched_cells b off n : list V293_record_cell :=
  match n with O=>[] | S m=>
    V293_clr_bytes b (off+1) (repeat (Vint32 Int.zero) 3)++
    V293_clr_bytes b (off+8) (repeat (Vint32 Int.zero) 4)++
    V293_flag_untouched_cells b (off+12) m end.
Lemma V293_zero_flag_fields : forall n b off R,
  V293_rdy_raw_cells (V293_clr_bytes b off (repeat (Vint32 Int.zero) (12*n))) R ==>
    V293_rdy_raw_cells (V293_flag_fields_cells b off n)
      (V293_rdy_raw_cells (V293_flag_untouched_cells b off n) R).
Proof.
  induction n as [ | n IH];intros b off R s H;[exact H | ].
  replace (12*S n)%nat with (1+(3+(4+(4+12*n))))%nat in H by lia.
  rewrite (V293_zero_bytes_split 1),V293_raw_cells_append in H.
  cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in H.
  cbn [Z.of_nat] in H.
  rewrite (V293_zero_bytes_split 3),V293_raw_cells_append in H.
  cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in H.
  replace (off+1+3) with (off+4) in H by lia.
  rewrite (V293_zero_bytes_split 4),V293_raw_cells_append in H.
  cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in H.
  replace (off+4+4) with (off+8) in H by lia.
  rewrite (V293_zero_bytes_split 4),V293_raw_cells_append in H.
  cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in H.
  replace (off+8+4) with (off+12) in H by lia.
  apply (V293_raw_cells_mono _ _ _ (V293_raw_cells_mono _ _ _
    (V293_zero4_null_owned b (off+4) Tvoid _))) in H.
  assert (K : s |= V293_rdy_raw_cells
    (V293_clr_bytes b off [Vint32 Int.zero])
    (V293_rdy_raw_cells ([((b,off+4),Tptr Tvoid,Vnull)])
      (V293_rdy_raw_cells (V293_clr_bytes b (off+1) (repeat (Vint32 Int.zero) 3))
        (V293_rdy_raw_cells (V293_clr_bytes b (off+8) (repeat (Vint32 Int.zero) 4))
          (V293_rdy_raw_cells (V293_clr_bytes b (off+12) (repeat (Vint32 Int.zero) (12*n))) R))))).
  { eapply V293_raw_cells_mono;[apply V293_raw_cells_swap | exact H]. }
  cbn [V293_flag_fields_cells V293_rdy_raw_cells V293_clr_bytes] in K |- *.
  eapply astar_mono;[intros st HS;exact HS | | exact K].
  intros st HS. eapply astar_mono;[intros st' HT;exact HT | | exact HS].
  intros st' HT.
  assert (J : st' |= V293_rdy_raw_cells
    (V293_clr_bytes b (off+1) (repeat (Vint32 Int.zero) 3)++
     V293_clr_bytes b (off+8) (repeat (Vint32 Int.zero) 4))
    (V293_rdy_raw_cells (V293_flag_fields_cells b (off+12) n)
      (V293_rdy_raw_cells (V293_flag_untouched_cells b (off+12) n) R))).
  { rewrite V293_raw_cells_append.
    eapply V293_raw_cells_mono;[apply V293_raw_cells_mono;apply IH | exact HT]. }
  apply V293_raw_cells_swap in J.
  cbn [V293_flag_untouched_cells]. repeat rewrite V293_raw_cells_append in *;exact J.
Qed.
Definition V293_flag_link_env ge le table free_head ix ix_next pgrp1 pgrp2 bt bf bi bn b1 b2 :=
  get le table=None /\ get ge table=Some (bt,V293_flag_table_type) /\
  get le free_head=None /\ get ge free_head=Some (bf,Tptr V293_flag_type) /\
  get le ix=Some (bi,Tint16) /\ get le ix_next=Some (bn,Tint16) /\
  get le pgrp1=Some (b1,Tptr V293_flag_type) /\ get le pgrp2=Some (b2,Tptr V293_flag_type).
Definition V293_flag_link_locals bi bn b1 b2 bf vi vn v1 v2 vf : list V293_record_cell :=
  [((bi,0),Tint16,vi);((bn,0),Tint16,vn);
   ((b1,0),Tptr V293_flag_type,v1);((b2,0),Tptr V293_flag_type,v2);
   ((bf,0),Tptr V293_flag_type,vf)].
Definition V293_flag_linked bt : list V293_record_cell :=
  [((bt,0),Tint8,Vint32 Int.zero);((bt,4),Tptr Tvoid,Vptr (bt,Int.repr 12));
   ((bt,12),Tint8,Vint32 Int.zero);((bt,16),Tptr Tvoid,Vptr (bt,Int.repr 24));
   ((bt,24),Tint8,Vint32 Int.zero);((bt,28),Tptr Tvoid,Vptr (bt,Int.repr 36));
   ((bt,36),Tint8,Vint32 Int.zero);((bt,40),Tptr Tvoid,Vptr (bt,Int.repr 48));
   ((bt,48),Tint8,Vint32 Int.zero);((bt,52),Tptr Tvoid,Vnull)].
Definition V293_flag_link_final bi bn b1 b2 bf bt :=
  V293_flag_link_locals bi bn b1 b2 bf (Vint32 (Int.repr 4)) (Vint32 (Int.repr 4))
    (Vptr (bt,Int.repr 48)) (Vptr (bt,Int.repr 48)) (Vptr (bt,Int.zero))++V293_flag_linked bt.

Ltac V293_flag_write P H n lhs rhs value next step owned :=
  let lhs := eval cbv beta delta [V293_flag_type_field V293_flag_ptr_field V293_flag_link_address V293_flag_link_inc] in lhs in
  let rhs := eval cbv beta delta [V293_flag_type_field V293_flag_ptr_field V293_flag_link_address V293_flag_link_inc] in rhs in
  lazymatch type of H with
  | (?ge,?le,?M,?ir,?aux,?O,?op) |= V293_rdy_raw_cells ?cells ?R =>
    let before := eval cbn in (firstn n cells) in
    let cell := eval cbn in (nth n cells ((1%positive,0%Z),Tint8,Vundef)) in
    let after := eval cbn in (skipn (S n) cells) in
    lazymatch cell with (?a,?tp,?old) =>
    let updated := eval cbn [app] in (before++(a,tp,value)::after) in
    let T := fresh "Write" in
    assert (T : exists Mf,
      (forall ks, cstepstar P (curs (sassign lhs rhs),(kenil,ks)) (ge,le,M)
        (curs (sskip None),(kenil,ks)) (ge,le,Mf)) /\
      (ge,le,Mf,ir,aux,O,op) |= V293_rdy_raw_cells updated R);
    [eapply (V293_rdy_assign before a tp old after value lhs rhs _ R P ge le M ir aux O op);
      [V293_tcb_eval | V293_tcb_eval | reflexivity | V293_tcb_eval |
       first [solve [apply eq_int;auto] |
         apply eq_vptr;eexists;eexists;split;reflexivity |
         apply eq_vcomptr;split;
           first [left;eexists;reflexivity | right;eexists;reflexivity]] |
       V293_tcb_eval | reflexivity | exact H] |
     destruct T as (next & step & owned)]
    end
  end.


Theorem V293_OS_FlagInit_links_execution : forall P ge le M ir aux O op R
  table free_head ix ix_next pgrp1 pgrp2 bt bf bi bn b1 b2 vi vn v1 v2 vf,
  V293_flag_link_env ge le table free_head ix ix_next pgrp1 pgrp2 bt bf bi bn b1 b2 ->
  (ge,le,M,ir,aux,O,op) |= V293_rdy_raw_cells
    (V293_flag_link_locals bi bn b1 b2 bf vi vn v1 v2 vf++V293_flag_fields_cells bt 0 5) R ->
  exists Mf,
    (forall ks, cstepstar P
      (curs (V293_init_flag_links table free_head ix ix_next pgrp1 pgrp2),(kenil,ks)) (ge,le,M)
      (curs (sskip None),(kenil,ks)) (ge,le,Mf)) /\
    (ge,le,Mf,ir,aux,O,op) |= V293_rdy_raw_cells (V293_flag_link_final bi bn b1 b2 bf bt) R.
Proof.
  intros P ge le M ir aux O op R table free_head ix ix_next pgrp1 pgrp2 bt bf bi bn b1 b2
    vi vn v1 v2 vf Env Owned.
  destruct Env as (Tn&Tg&Fn&Fg&Ix&Inext&P1&P2).
  cbn [V293_flag_link_locals V293_flag_fields_cells app] in Owned.
  V293_flag_write P Owned 0%nat (evar ix) (ecast (econst32 Int.zero) Tint16)
    (Vint32 Int.zero) M0 Init H0.
  V293_clr_read H0 0%nat Ix0.
  assert (G0 : evalval (V293_flag_link_guard ix) (ge,le,M0)=Some (Vint32 Int.one)).
  { unfold V293_flag_link_guard. V293_tcb_eval. }
  V293_flag_write P H0 1%nat (evar ix_next) (V293_flag_link_inc ix)
    (Vint32 (Int.repr 1)) M0a S0a H0a.
  V293_clr_read H0a 0%nat I0a.
  V293_flag_write P H0a 2%nat (evar pgrp1) (V293_flag_link_address table ix)
    (Vptr (bt,Int.zero)) M0b S0b H0b.
  V293_clr_read H0b 1%nat I0b.
  V293_flag_write P H0b 3%nat (evar pgrp2) (V293_flag_link_address table ix_next)
    (Vptr (bt,(Int.repr 12))) M0c S0c H0c.
  V293_clr_read H0c 2%nat I0c.
  V293_flag_write P H0c 5%nat (V293_flag_type_field pgrp1) (ecast (econst32 Int.zero) Tint8)
    (Vint32 Int.zero) M0d S0d H0d.
  V293_clr_read H0d 2%nat I0d.
  V293_clr_read H0d 3%nat I0d2.
  V293_flag_write P H0d 6%nat (V293_flag_ptr_field pgrp1) (ecast (evar pgrp2) (Tptr Tvoid))
    (Vptr (bt,(Int.repr 12))) M0e S0e H0e.
  V293_clr_read H0e 0%nat I0e.
  V293_flag_write P H0e 0%nat (evar ix) (V293_flag_link_inc ix)
    (Vint32 (Int.repr 1)) M1 S0f H1.
  V293_clr_read H1 0%nat Ix1.
  assert (G1 : evalval (V293_flag_link_guard ix) (ge,le,M1)=Some (Vint32 Int.one)).
  { unfold V293_flag_link_guard. V293_tcb_eval. }
  V293_flag_write P H1 1%nat (evar ix_next) (V293_flag_link_inc ix)
    (Vint32 (Int.repr 2)) M1a S1a H1a.
  V293_clr_read H1a 0%nat I1a.
  V293_flag_write P H1a 2%nat (evar pgrp1) (V293_flag_link_address table ix)
    (Vptr (bt,(Int.repr 12))) M1b S1b H1b.
  V293_clr_read H1b 1%nat I1b.
  V293_flag_write P H1b 3%nat (evar pgrp2) (V293_flag_link_address table ix_next)
    (Vptr (bt,(Int.repr 24))) M1c S1c H1c.
  V293_clr_read H1c 2%nat I1c.
  V293_flag_write P H1c 7%nat (V293_flag_type_field pgrp1) (ecast (econst32 Int.zero) Tint8)
    (Vint32 Int.zero) M1d S1d H1d.
  V293_clr_read H1d 2%nat I1d.
  V293_clr_read H1d 3%nat I1d2.
  V293_flag_write P H1d 8%nat (V293_flag_ptr_field pgrp1) (ecast (evar pgrp2) (Tptr Tvoid))
    (Vptr (bt,(Int.repr 24))) M1e S1e H1e.
  V293_clr_read H1e 0%nat I1e.
  V293_flag_write P H1e 0%nat (evar ix) (V293_flag_link_inc ix)
    (Vint32 (Int.repr 2)) M2 S1f H2.
  V293_clr_read H2 0%nat Ix2.
  assert (G2 : evalval (V293_flag_link_guard ix) (ge,le,M2)=Some (Vint32 Int.one)).
  { unfold V293_flag_link_guard. V293_tcb_eval. }
  V293_flag_write P H2 1%nat (evar ix_next) (V293_flag_link_inc ix)
    (Vint32 (Int.repr 3)) M2a S2a H2a.
  V293_clr_read H2a 0%nat I2a.
  V293_flag_write P H2a 2%nat (evar pgrp1) (V293_flag_link_address table ix)
    (Vptr (bt,(Int.repr 24))) M2b S2b H2b.
  V293_clr_read H2b 1%nat I2b.
  V293_flag_write P H2b 3%nat (evar pgrp2) (V293_flag_link_address table ix_next)
    (Vptr (bt,(Int.repr 36))) M2c S2c H2c.
  V293_clr_read H2c 2%nat I2c.
  V293_flag_write P H2c 9%nat (V293_flag_type_field pgrp1) (ecast (econst32 Int.zero) Tint8)
    (Vint32 Int.zero) M2d S2d H2d.
  V293_clr_read H2d 2%nat I2d.
  V293_clr_read H2d 3%nat I2d2.
  V293_flag_write P H2d 10%nat (V293_flag_ptr_field pgrp1) (ecast (evar pgrp2) (Tptr Tvoid))
    (Vptr (bt,(Int.repr 36))) M2e S2e H2e.
  V293_clr_read H2e 0%nat I2e.
  V293_flag_write P H2e 0%nat (evar ix) (V293_flag_link_inc ix)
    (Vint32 (Int.repr 3)) M3 S2f H3.
  V293_clr_read H3 0%nat Ix3.
  assert (G3 : evalval (V293_flag_link_guard ix) (ge,le,M3)=Some (Vint32 Int.one)).
  { unfold V293_flag_link_guard. V293_tcb_eval. }
  V293_flag_write P H3 1%nat (evar ix_next) (V293_flag_link_inc ix)
    (Vint32 (Int.repr 4)) M3a S3a H3a.
  V293_clr_read H3a 0%nat I3a.
  V293_flag_write P H3a 2%nat (evar pgrp1) (V293_flag_link_address table ix)
    (Vptr (bt,(Int.repr 36))) M3b S3b H3b.
  V293_clr_read H3b 1%nat I3b.
  V293_flag_write P H3b 3%nat (evar pgrp2) (V293_flag_link_address table ix_next)
    (Vptr (bt,(Int.repr 48))) M3c S3c H3c.
  V293_clr_read H3c 2%nat I3c.
  V293_flag_write P H3c 11%nat (V293_flag_type_field pgrp1) (ecast (econst32 Int.zero) Tint8)
    (Vint32 Int.zero) M3d S3d H3d.
  V293_clr_read H3d 2%nat I3d.
  V293_clr_read H3d 3%nat I3d2.
  V293_flag_write P H3d 12%nat (V293_flag_ptr_field pgrp1) (ecast (evar pgrp2) (Tptr Tvoid))
    (Vptr (bt,(Int.repr 48))) M3e S3e H3e.
  V293_clr_read H3e 0%nat I3e.
  V293_flag_write P H3e 0%nat (evar ix) (V293_flag_link_inc ix)
    (Vint32 (Int.repr 4)) M4 S3f H4.
  V293_clr_read H4 0%nat Ix4.
  assert (G4 : evalval (V293_flag_link_guard ix) (ge,le,M4)=Some (Vint32 Int.zero)).
  { unfold V293_flag_link_guard. V293_tcb_eval. }
  V293_flag_write P H4 2%nat (evar pgrp1) (V293_flag_link_address table ix)
    (Vptr (bt,Int.repr 48)) Mt1 St1 Ht1.
  V293_clr_read Ht1 2%nat Pt1.
  V293_flag_write P Ht1 13%nat (V293_flag_type_field pgrp1) (ecast (econst32 Int.zero) Tint8)
    (Vint32 Int.zero) Mt2 St2 Ht2.
  V293_clr_read Ht2 2%nat Pt2.
  V293_flag_write P Ht2 14%nat (V293_flag_ptr_field pgrp1) (ecast enull (Tptr Tvoid))
    Vnull Mt3 St3 Ht3.
  V293_flag_write P Ht3 4%nat (evar free_head) (eaddrof (earrayelem (evar table) (econst32 Int.zero)))
    (Vptr (bt,Int.zero)) Mf St4 Hf.
  assert (Loop : forall ks, cstepstar P
    (curs (V293_flag_link_loop table ix ix_next pgrp1 pgrp2),(kenil,ks)) (ge,le,M0)
    (curs (sskip None),(kenil,ks)) (ge,le,M4)).
  { intro ks. unfold V293_flag_link_loop,V293_flag_link_iteration.
    eapply V293_rdy_while_true;[exact G0 | | ].
    { intro tail.
      eapply V293_rekey_sequence_execution;[exact S0a | ].
      eapply V293_rekey_sequence_execution;[exact S0b | ].
      eapply V293_rekey_sequence_execution;[exact S0c | ].
      eapply V293_rekey_sequence_execution;[exact S0d | ].
      eapply V293_rekey_sequence_execution;[exact S0e | ].
      apply S0f. }
    eapply V293_rdy_while_true;[exact G1 | | ].
    { intro tail.
      eapply V293_rekey_sequence_execution;[exact S1a | ].
      eapply V293_rekey_sequence_execution;[exact S1b | ].
      eapply V293_rekey_sequence_execution;[exact S1c | ].
      eapply V293_rekey_sequence_execution;[exact S1d | ].
      eapply V293_rekey_sequence_execution;[exact S1e | ].
      apply S1f. }
    eapply V293_rdy_while_true;[exact G2 | | ].
    { intro tail.
      eapply V293_rekey_sequence_execution;[exact S2a | ].
      eapply V293_rekey_sequence_execution;[exact S2b | ].
      eapply V293_rekey_sequence_execution;[exact S2c | ].
      eapply V293_rekey_sequence_execution;[exact S2d | ].
      eapply V293_rekey_sequence_execution;[exact S2e | ].
      apply S2f. }
    eapply V293_rdy_while_true;[exact G3 | | ].
    { intro tail.
      eapply V293_rekey_sequence_execution;[exact S3a | ].
      eapply V293_rekey_sequence_execution;[exact S3b | ].
      eapply V293_rekey_sequence_execution;[exact S3c | ].
      eapply V293_rekey_sequence_execution;[exact S3d | ].
      eapply V293_rekey_sequence_execution;[exact S3e | ].
      apply S3f. }
    apply V293_rdy_while_false;exact G4. }
  exists Mf. split;[ | exact Hf]. intro ks.
  unfold V293_init_flag_links,V293_flag_link_tail.
  eapply V293_rekey_sequence_execution;[exact Init | ].
  eapply V293_rekey_sequence_execution;[exact Loop | ].
  eapply V293_rekey_sequence_execution;[exact St1 | ].
  eapply V293_rekey_sequence_execution;[exact St2 | ].
  eapply V293_rekey_sequence_execution;[exact St3 | apply St4].
Qed.

(* Real clear call, with fresh parameters derived from this actual memory. *)
Theorem V293_OS_FlagInit_clear_call : forall oldflags frame P ks ge le M ir aux O op
  clear dest size table bt,
  P clear=Some (V293_MemClr_function dest size) -> dest<>size ->
  get le table=None -> get ge table=Some (bt,V293_flag_table_type) ->
  length oldflags=60%nat ->
  (ge,le,M,ir,aux,O,op) |= V293_rdy_raw_cells (V293_clr_bytes bt 0 oldflags++frame) Atrue ->
  exists Mf,
    cstepstar P (curs (scall clear [V293_init_clear_address table;
      V293_init_clear_size V293_flag_table_type]),(kenil,ks)) (ge,le,M)
      (curs (sskip None),(kenil,ks)) (ge,le,Mf) /\
    (ge,le,Mf,ir,aux,O,op) |= V293_rdy_raw_cells
      (V293_clr_bytes bt 0 (repeat (Vint32 Int.zero) 60)++frame) Atrue.
Proof.
  intros oldflags frame P ks ge le M ir aux O op clear dest size table bt
    Lookup Names Tn Tg Length Entry.
  destruct (V293_fresh_parameters_away M (((bt,0),Tint8,Vundef)::frame))
    as (bp&bs&DS&FD&FS&Away).
  assert (Bt : bt<>bp /\ bt<>bs) by (apply (Away (bt,0) Tint8 Vundef);left;reflexivity).
  destruct (V293_init_clear_arguments ge le M table bt V293_flag_type 5 Tn Tg
    ltac:(change (60<=65535);lia)) as (DT&DV&ST&SV).
  destruct (V293_MemClr_call_owned oldflags frame P ks ge le M ir aux O op
    clear dest size bp bs bt 0 (V293_init_clear_address table)
    (V293_init_clear_size V293_flag_table_type) Lookup Names DS (proj1 Bt) (proj2 Bt)
    ltac:(intros a tp v Member;apply (Away a tp v);right;exact Member)
    FS FD DT DV ST ltac:(rewrite Length;exact SV)
    ltac:(rewrite Length;cbn;lia) ltac:(lia)
    ltac:(rewrite Length;change (0+60<=4294967295);lia) Entry)
    as (Mf&Exec&Final&DGone&SGone).
  exists Mf. split;[exact Exec | rewrite Length in Final;exact Final].
Qed.
Lemma V293_flag_prepare_cleared : forall bt locals frame,
  V293_rdy_raw_cells (V293_clr_bytes bt 0 (repeat (Vint32 Int.zero) 60)++locals++frame) Atrue ==>
  V293_rdy_raw_cells (locals++V293_flag_fields_cells bt 0 5)
    (V293_rdy_raw_cells (V293_flag_untouched_cells bt 0 5)
      (V293_rdy_raw_cells frame Atrue)).
Proof.
  intros bt locals frame s H. repeat rewrite V293_raw_cells_append in H.
  apply (V293_zero_flag_fields 5 bt 0 _) in H.
  change (s |= V293_rdy_raw_cells
    (V293_flag_fields_cells bt 0 5++V293_flag_untouched_cells bt 0 5)
    (V293_rdy_raw_cells locals (V293_rdy_raw_cells frame Atrue))) in H.
  apply V293_raw_cells_swap in H. repeat rewrite V293_raw_cells_append in *;exact H.
Qed.
Theorem V293_OS_FlagInit_body_execution : forall oldflags frame P ks ge le M ir aux O op
  clear dest size table free_head ix ix_next pgrp1 pgrp2 bt bf bi bn b1 b2 vi vn v1 v2 vf,
  P clear=Some (V293_MemClr_function dest size) -> dest<>size ->
  V293_flag_link_env ge le table free_head ix ix_next pgrp1 pgrp2 bt bf bi bn b1 b2 ->
  length oldflags=60%nat ->
  (ge,le,M,ir,aux,O,op) |= V293_rdy_raw_cells
    (V293_clr_bytes bt 0 oldflags++V293_flag_link_locals bi bn b1 b2 bf vi vn v1 v2 vf++frame) Atrue ->
  exists Mf,
    cstepstar P (curs (V293_init_flag_body clear table free_head ix ix_next pgrp1 pgrp2),
      (kenil,ks)) (ge,le,M) (curs (sskip None),(kenil,ks)) (ge,le,Mf) /\
    (ge,le,Mf,ir,aux,O,op) |= V293_rdy_raw_cells (V293_flag_link_final bi bn b1 b2 bf bt)
      (V293_rdy_raw_cells (V293_flag_untouched_cells bt 0 5)
        (V293_rdy_raw_cells frame Atrue)).
Proof.
  intros oldflags frame P ks ge le M ir aux O op clear dest size table free_head ix ix_next
    pgrp1 pgrp2 bt bf bi bn b1 b2 vi vn v1 v2 vf Lookup Names Env Length Entry.
  destruct Env as (Tn&Tg&Rest).
  destruct (V293_OS_FlagInit_clear_call oldflags
    (V293_flag_link_locals bi bn b1 b2 bf vi vn v1 v2 vf++frame) P
    (kseq (V293_init_flag_links table free_head ix ix_next pgrp1 pgrp2) ks)
    ge le M ir aux O op clear dest size table bt Lookup Names Tn Tg Length Entry)
    as (M1&Clear&Cleared).
  apply (V293_flag_prepare_cleared bt _ frame) in Cleared.
  destruct (V293_OS_FlagInit_links_execution P ge le M1 ir aux O op _
    table free_head ix ix_next pgrp1 pgrp2 bt bf bi bn b1 b2 vi vn v1 v2 vf
    (conj Tn (conj Tg Rest)) Cleared) as (Mf&Links&Final).
  exists Mf. split;[ | exact Final]. unfold V293_init_flag_body.
  eapply c_stepstarn. { eapply stmt_step;[reflexivity | apply sseq_step]. }
  eapply V293_cstepstar_trans;[exact Clear | ].
  eapply c_stepstarn. { eapply stmt_step;[reflexivity | constructor]. }
  apply Links.
Qed.

Require Import CertiOS.certiucos.v293.proofs.V293InitTCBCall.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.tactics.basetac.join_lib.
Definition V293_flag_call_locals ix ix_next pgrp1 pgrp2 bi bn b1 b2 : env :=
  set (set (set (set emp ix (bi,Tint16)) ix_next (bn,Tint16))
    pgrp1 (b1,Tptr V293_flag_type)) pgrp2 (b2,Tptr V293_flag_type).
Definition V293_flag_call_blocks (bi bn b1 b2 : block) := [bi;bn;b1;b2].
Definition V293_flag_call_head bf vf : list V293_record_cell :=
  [((bf,0),Tptr V293_flag_type,vf)].
Definition V293_flag_call_result bf bt frame :=
  V293_flag_call_head bf (Vptr (bt,Int.zero))++V293_flag_linked bt++
    V293_flag_untouched_cells bt 0 5++frame.
Lemma V293_flag_call_addresses : forall ix ix_next pgrp1 pgrp2 bi bn b1 b2,
  ix<ix_next -> ix_next<pgrp1 -> pgrp1<pgrp2 ->
  getaddr (V293_flag_call_locals ix ix_next pgrp1 pgrp2 bi bn b1 b2)=
    [(bi,Tint16);(bn,Tint16);(b1,Tptr V293_flag_type);(b2,Tptr V293_flag_type)].
Proof.
  intros ix ix_next pgrp1 pgrp2 bi bn b1 b2 A B C.
  unfold V293_flag_call_locals.
  change (getaddr (EnvMod.set (EnvMod.set (EnvMod.set (EnvMod.set EnvMod.emp ix (bi,Tint16))
    ix_next (bn,Tint16)) pgrp1 (b1,Tptr V293_flag_type)) pgrp2 (b2,Tptr V293_flag_type))=
    [(bi,Tint16);(bn,Tint16);(b1,Tptr V293_flag_type);(b2,Tptr V293_flag_type)]).
  cbn [EnvMod.set EnvMod.lst EnvMod.set' EnvMod.emp EnvMod.emp' getaddr getaddrlist].
  repeat first [ progress cbn [EnvMod.set' getaddrlist] | match goal with
  | |- context [identspec.blt ?x ?y] =>
    let H:=fresh in assert (H:identspec.blt x y=false) by (unfold identspec.blt;apply Z.ltb_ge;lia);rewrite H
  | |- context [identspec.beq ?x ?y] => rewrite (identspec.neq_beq_false x y) by lia
  end ]. reflexivity.
Qed.

Theorem V293_OS_FlagInit_call_return : forall oldflags frame P ks ge caller M
  ir aux O op f clear dest size table free_head ix ix_next pgrp1 pgrp2
  bt bf bi bn b1 b2 vf,
  P f=Some (V293_FlagInit_function clear table free_head ix ix_next pgrp1 pgrp2) ->
  P clear=Some (V293_MemClr_function dest size) -> dest<>size ->
  ix<ix_next -> ix_next<pgrp1 -> pgrp1<pgrp2 ->
  NoDup (V293_flag_call_blocks bi bn b1 b2) ->
  fresh M bi -> fresh M bn -> fresh M b1 -> fresh M b2 ->
  V293_flag_link_env ge (V293_flag_call_locals ix ix_next pgrp1 pgrp2 bi bn b1 b2)
    table free_head ix ix_next pgrp1 pgrp2 bt bf bi bn b1 b2 ->
  length oldflags=60%nat ->
  (forall a tp v, In (a,tp,v) (V293_flag_call_result bf bt frame) ->
    ~In (fst a) (V293_flag_call_blocks bi bn b1 b2)) ->
  (ge,caller,M,ir,aux,O,op) |= V293_rdy_raw_cells
    (V293_clr_bytes bt 0 oldflags++
      V293_flag_call_head bf vf++frame) Atrue ->
  exists Ms Mf,
    cstepstar P (curs (scall f nil),(kenil,ks)) (ge,caller,M)
      (curs (sskip None),(kenil,ks)) (ge,caller,Mf) /\
    (ge,V293_flag_call_locals ix ix_next pgrp1 pgrp2 bi bn b1 b2,Ms,ir,aux,O,op) |=
      V293_rdy_raw_cells (V293_flag_link_final bi bn b1 b2 bf bt)
        (V293_rdy_raw_cells (V293_flag_untouched_cells bt 0 5)
          (V293_rdy_raw_cells frame Atrue)) /\
    (ge,caller,Mf,ir,aux,O,op) |= V293_rdy_raw_cells (V293_flag_call_result bf bt frame) Atrue /\
    (forall c i, ~In c (V293_flag_call_blocks bi bn b1 b2) -> get Mf (c,i)=get Ms (c,i)) /\
    (forall c tp k, In (c,tp) [(bi,Tint16);(bn,Tint16);(b1,Tptr V293_flag_type);(b2,Tptr V293_flag_type)] ->
      (k<typelen tp)%nat -> get Mf (c,Z.of_nat k)=None).
Proof.
  intros oldflags frame P ks ge caller M ir aux O op f clear dest size table
    free_head ix ix_next pgrp1 pgrp2 bt bf bi bn b1 b2 vf
    Program Clear Names A B C ND Fi Fn F1 F2 Env Length Away Owned.
  set (le:=V293_flag_call_locals ix ix_next pgrp1 pgrp2 bi bn b1 b2).
  assert (Frame : (ge,le,M,ir,aux,O,op) |= V293_rdy_raw_cells
    (V293_clr_bytes bt 0 oldflags++V293_flag_call_head bf vf++frame) Atrue).
  { eapply V293_raw_cells_environment;[right;reflexivity | exact Owned]. }
  assert (Distinct : bi<>bn /\ bi<>b1 /\ bi<>b2 /\ bn<>b1 /\ bn<>b2 /\ b1<>b2).
  { unfold V293_flag_call_blocks in ND.
    inversion ND as [ | xi xsi NI N1];subst. inversion N1 as [ | xn xsn NN N2];subst.
    inversion N2 as [ | xone xsone NOne N3];subst. cbn in NI,NN,NOne. intuition congruence. }
  destruct Distinct as (Din&D11&D12&Dn1&Dn2&D12p).
  set (M1:=allocb M bi 0 (typelen Tint16)).
  set (M2:=allocb M1 bn 0 (typelen Tint16)).
  set (M3:=allocb M2 b1 0 (typelen (Tptr V293_flag_type))).
  set (M4:=allocb M3 b2 0 (typelen (Tptr V293_flag_type))).
  assert (Fn1 : fresh M1 bn) by (unfold M1;apply V293_tcb_fresh_after_alloc;assumption).
  assert (F12 : fresh M2 b1).
  { unfold M2,M1. repeat apply V293_tcb_fresh_after_alloc;first [assumption | congruence]. }
  assert (F23 : fresh M3 b2).
  { unfold M3,M2,M1. repeat apply V293_tcb_fresh_after_alloc;first [assumption | congruence]. }
  pose proof (V293_tick_allocate_frame ge le M ir aux O op bi Tint16 _ Fi Frame) as H1.
  pose proof (V293_tick_allocate_frame ge le M1 ir aux O op bn Tint16 _ Fn1 H1) as H2.
  pose proof (V293_tick_allocate_frame ge le M2 ir aux O op b1 (Tptr V293_flag_type) _ F12 H2) as H3.
  pose proof (V293_tick_allocate_frame ge le M3 ir aux O op b2 (Tptr V293_flag_type) _ F23 H3) as H4.
  assert (Start : (ge,le,M4,ir,aux,O,op) |= V293_rdy_raw_cells
    (V293_clr_bytes bt 0 oldflags++
      V293_flag_link_locals bi bn b1 b2 bf Vundef Vundef Vundef Vundef vf++frame) Atrue).
  { rewrite V293_raw_cells_append in H4.
    change ((ge,le,M4,ir,aux,O,op) |= V293_rdy_raw_cells
      ([((b2,0),Tptr V293_flag_type,Vundef);((b1,0),Tptr V293_flag_type,Vundef);
       ((bn,0),Tint16,Vundef);((bi,0),Tint16,Vundef)])
      (V293_rdy_raw_cells (V293_clr_bytes bt 0 oldflags)
        (V293_rdy_raw_cells (V293_flag_call_head bf vf++frame) Atrue))) in H4.
    apply V293_raw_cells_swap in H4.
    rewrite V293_raw_cells_append.
    eapply V293_raw_cells_mono;[ | exact H4].
    intros st HS. cbn [V293_flag_link_locals V293_flag_call_head V293_rdy_raw_cells app] in *.
    clear -HS. sep auto. }
  set (body:=sseq (V293_init_flag_body clear table free_head ix ix_next pgrp1 pgrp2) sret).
  destruct (V293_OS_FlagInit_body_execution oldflags frame P
    (kseq sret (kcall f body caller ks)) ge le M4 ir aux O op
    clear dest size table free_head ix ix_next pgrp1 pgrp2
    bt bf bi bn b1 b2 Vundef Vundef Vundef Vundef vf
    Clear Names Env Length Start) as (Ms&Exec&Final).
  assert (Layout : getaddr le=[(bi,Tint16);(bn,Tint16);(b1,Tptr V293_flag_type);(b2,Tptr V293_flag_type)]).
  { unfold le. apply V293_flag_call_addresses;assumption. }
  assert (Writable : forall c tp, In (c,tp) (getaddr le) -> V293_bytes_writable Ms c 0 (typelen tp)).
  { intros c tp Member. rewrite Layout in Member.
    unfold V293_flag_link_final,V293_flag_link_locals in Final.
    cbn [app V293_rdy_raw_cells] in Final.
    destruct Member as [E | [E | [E | [E | E]]]];
      try contradiction;inversion E;subst;
      eapply V293_tick_raw_owned_writable with (R:=Atrue) (ge:=ge) (le:=le) (ir:=ir) (aux:=aux) (O:=O) (op:=op);clear -Final;sep auto. }
  destruct (V293_tick_void_return P (kcall f body caller ks) ge le caller Ms f body ks)
    as (Mf&Return&Preserve&Removed).
  - reflexivity.
  - rewrite Layout. exact ND.
  - exact Writable.
  - exists Ms. exists Mf. split.
    + eapply c_stepstarn. { eapply stmt_step;[reflexivity | apply snpcall_step]. }
      eapply c_stepstarn.
      { eapply stmt_step;[reflexivity | ]. eapply sfexec_step with (d1:=dnil)
          (d2:=dcons ix Tint16 (dcons ix_next Tint16 (dcons pgrp1 (Tptr V293_flag_type) (dcons pgrp2 (Tptr V293_flag_type) dnil))));
          [reflexivity | reflexivity | exact Program | exact I | reflexivity]. }
      eapply c_stepstarn.
      { eapply stmt_step;[reflexivity | ]. eapply salloclv_step;[reflexivity | reflexivity | ].
        exists bi. repeat split;try assumption;try reflexivity.
        intros [v E]. rewrite map_emp_get in E;discriminate. }
      eapply c_stepstarn.
      { eapply stmt_step;[reflexivity | ]. eapply salloclv_step;[reflexivity | reflexivity | ].
        exists bn. repeat split;try assumption;try reflexivity.
        intros [v E]. rewrite map_get_set' in E by lia. rewrite map_emp_get in E;discriminate. }
      eapply c_stepstarn.
      { eapply stmt_step;[reflexivity | ]. eapply salloclv_step;[reflexivity | reflexivity | ].
        exists b1. repeat split;try assumption;try reflexivity.
        intros [v E]. repeat rewrite map_get_set' in E by lia. rewrite map_emp_get in E;discriminate. }
      eapply c_stepstarn.
      { eapply stmt_step;[reflexivity | ]. eapply salloclv_step;[reflexivity | reflexivity | ].
        exists b2. repeat split;try assumption;try reflexivity.
        intros [v E]. repeat rewrite map_get_set' in E by lia. rewrite map_emp_get in E;discriminate. }
      eapply c_stepstarn. { eapply stmt_step;[reflexivity | apply sallocend_step]. }
      eapply c_stepstarn. { eapply stmt_step;[reflexivity | apply sseq_step]. }
      eapply V293_cstepstar_trans;[exact Exec | ].
      eapply c_stepstarn. { eapply stmt_step;[reflexivity | constructor]. }
      exact Return.
    + split;[exact Final | ]. split.
      * eapply V293_raw_cells_return_many with (M:=Ms) (le:=le) (freed:=V293_flag_call_blocks bi bn b1 b2).
        -- exact Away.
        -- intros c i Outside. apply Preserve. rewrite Layout. exact Outside.
        -- change ((ge,le,Ms,ir,aux,O,op) |= V293_rdy_raw_cells
             ([((bi,0),Tint16,Vint32 (Int.repr 4));((bn,0),Tint16,Vint32 (Int.repr 4));
               ((b1,0),Tptr V293_flag_type,Vptr (bt,Int.repr 48));
               ((b2,0),Tptr V293_flag_type,Vptr (bt,Int.repr 48))])
             (V293_rdy_raw_cells (V293_flag_call_result bf bt frame) Atrue)) in Final.
           apply V293_raw_cells_swap in Final. exact Final.
      * split.
        -- intros c i Outside. apply Preserve. rewrite Layout. exact Outside.
        -- intros c tp k Member Bound. apply (Removed c tp k);[rewrite Layout;exact Member | exact Bound].
Qed.
