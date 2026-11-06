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

Require Import CertiOS.certiucos.v293.code.V293OSMemInit.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBList.

Theorem V293_init_mem_layout : typelen V293_mem_type=20%nat /\
  typelen V293_mem_table_type=100%nat /\
  field_offset 1 V293_mem_fields=Some Int.zero /\
  field_offset 2 V293_mem_fields=Some (Int.repr 4) /\
  field_offset 3 V293_mem_fields=Some (Int.repr 8) /\
  field_offset 4 V293_mem_fields=Some (Int.repr 12) /\
  field_offset 5 V293_mem_fields=Some (Int.repr 16).
Proof. repeat split;reflexivity. Qed.
Fixpoint V293_mem_fields_cells b off n : list V293_record_cell :=
  match n with O=>[] | S m=> ((b,off+4),Tptr Tvoid,Vnull)::
    V293_mem_fields_cells b (off+20) m end.
Fixpoint V293_mem_untouched_cells b off n : list V293_record_cell :=
  match n with O=>[] | S m=>
    V293_clr_bytes b off (repeat (Vint32 Int.zero) 4)++
    V293_clr_bytes b (off+8) (repeat (Vint32 Int.zero) 12)++
    V293_mem_untouched_cells b (off+20) m end.
Lemma V293_zero_mem_fields : forall n b off R,
  V293_rdy_raw_cells (V293_clr_bytes b off (repeat (Vint32 Int.zero) (20*n))) R ==>
    V293_rdy_raw_cells (V293_mem_fields_cells b off n)
      (V293_rdy_raw_cells (V293_mem_untouched_cells b off n) R).
Proof.
  induction n as [ | n IH];intros b off R s H;[exact H | ].
  replace (20*S n)%nat with (4+(4+(12+20*n)))%nat in H by lia.
  rewrite (V293_zero_bytes_split 4),V293_raw_cells_append in H.
  cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in H.
  rewrite (V293_zero_bytes_split 4),V293_raw_cells_append in H.
  cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in H.
  replace (off+4+4) with (off+8) in H by lia.
  rewrite (V293_zero_bytes_split 12),V293_raw_cells_append in H.
  cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in H.
  replace (off+8+12) with (off+20) in H by lia.
  apply (V293_raw_cells_mono _ _ _ (V293_zero4_null_owned b (off+4) Tvoid _)) in H.
  change (s |= V293_rdy_raw_cells (V293_clr_bytes b off (repeat (Vint32 Int.zero) 4))
    (V293_rdy_raw_cells ([((b,off+4),Tptr Tvoid,Vnull)])
      (V293_rdy_raw_cells (V293_clr_bytes b (off+8) (repeat (Vint32 Int.zero) 12))
        (V293_rdy_raw_cells (V293_clr_bytes b (off+20) (repeat (Vint32 Int.zero) (20*n))) R)))) in H.
  apply V293_raw_cells_swap in H.
  cbn [V293_mem_fields_cells V293_rdy_raw_cells] in H |- *.
  eapply astar_mono;[intros st HS;exact HS | | exact H].
  intros st HS.
  assert (J : st |= V293_rdy_raw_cells
    (V293_clr_bytes b off (repeat (Vint32 Int.zero) 4)++
     V293_clr_bytes b (off+8) (repeat (Vint32 Int.zero) 12))
    (V293_rdy_raw_cells (V293_mem_fields_cells b (off+20) n)
      (V293_rdy_raw_cells (V293_mem_untouched_cells b (off+20) n) R))).
  { rewrite V293_raw_cells_append.
    eapply V293_raw_cells_mono;[apply V293_raw_cells_mono;apply IH | exact HS]. }
  apply V293_raw_cells_swap in J.
  cbn [V293_mem_untouched_cells]. repeat rewrite V293_raw_cells_append in *;exact J.
Qed.
Definition V293_mem_link_env ge le table free_head pmem ix bt bf bp bi :=
  get le table=None /\ get ge table=Some (bt,V293_mem_table_type) /\
  get le free_head=None /\ get ge free_head=Some (bf,Tptr V293_mem_type) /\
  get le pmem=Some (bp,Tptr V293_mem_type) /\ get le ix=Some (bi,Tint16).
Definition V293_mem_link_locals bp bi bf vp vi vf : list V293_record_cell :=
  [((bp,0),Tptr V293_mem_type,vp);((bi,0),Tint16,vi);((bf,0),Tptr V293_mem_type,vf)].
Definition V293_mem_linked bt : list V293_record_cell :=
  [((bt,4),Tptr Tvoid,Vptr (bt,Int.repr 20));
   ((bt,24),Tptr Tvoid,Vptr (bt,Int.repr 40));
   ((bt,44),Tptr Tvoid,Vptr (bt,Int.repr 60));
   ((bt,64),Tptr Tvoid,Vptr (bt,Int.repr 80));
   ((bt,84),Tptr Tvoid,Vnull)].
Definition V293_mem_link_final bp bi bf bt :=
  V293_mem_link_locals bp bi bf (Vptr (bt,Int.repr 80))
    (Vint32 (Int.repr 4)) (Vptr (bt,Int.zero))++V293_mem_linked bt.
Ltac V293_mem_write P H n lhs rhs value next step owned :=
  let lhs := eval cbv beta delta [V293_mem_ptr_field V293_mem_link_address V293_mem_link_next V293_mem_link_inc] in lhs in
  let rhs := eval cbv beta delta [V293_mem_ptr_field V293_mem_link_address V293_mem_link_next V293_mem_link_inc] in rhs in
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


Theorem V293_OS_MemInit_links_execution : forall P ge le M ir aux O op R
  table free_head pmem ix bt bf bp bi vp vi vf,
  V293_mem_link_env ge le table free_head pmem ix bt bf bp bi ->
  (ge,le,M,ir,aux,O,op) |= V293_rdy_raw_cells
    (V293_mem_link_locals bp bi bf vp vi vf++V293_mem_fields_cells bt 0 5) R ->
  exists Mf,
    (forall ks, cstepstar P
      (curs (V293_init_mem_links table free_head pmem ix),(kenil,ks)) (ge,le,M)
      (curs (sskip None),(kenil,ks)) (ge,le,Mf)) /\
    (ge,le,Mf,ir,aux,O,op) |= V293_rdy_raw_cells (V293_mem_link_final bp bi bf bt) R.
Proof.
  intros P ge le M ir aux O op R table free_head pmem ix bt bf bp bi vp vi vf Env Owned.
  destruct Env as (Tn&Tg&Fn&Fg&Pm&Ix).
  cbn [V293_mem_link_locals V293_mem_fields_cells app] in Owned.
  V293_mem_write P Owned 1%nat (evar ix) (ecast (econst32 Int.zero) Tint16)
    (Vint32 Int.zero) M0 Init H0.
  V293_clr_read H0 1%nat Ix0.
  assert (G0 : evalval (V293_mem_link_guard ix) (ge,le,M0)=Some (Vint32 Int.one)).
  { unfold V293_mem_link_guard. V293_tcb_eval. }
  V293_mem_write P H0 0%nat (evar pmem) (V293_mem_link_address table ix)
    (Vptr (bt,Int.repr 0)) M0a S0a H0a.
  V293_clr_read H0a 0%nat P0a.
  V293_clr_read H0a 1%nat I0a.
  V293_mem_write P H0a 3%nat (V293_mem_ptr_field pmem) (V293_mem_link_next table ix)
    (Vptr (bt,Int.repr 20)) M0b S0b H0b.
  V293_clr_read H0b 1%nat I0b.
  V293_mem_write P H0b 1%nat (evar ix) (V293_mem_link_inc ix)
    (Vint32 (Int.repr 1)) M1 S0c H1.
  V293_clr_read H1 1%nat Ix1.
  assert (G1 : evalval (V293_mem_link_guard ix) (ge,le,M1)=Some (Vint32 Int.one)).
  { unfold V293_mem_link_guard. V293_tcb_eval. }
  V293_mem_write P H1 0%nat (evar pmem) (V293_mem_link_address table ix)
    (Vptr (bt,Int.repr 20)) M1a S1a H1a.
  V293_clr_read H1a 0%nat P1a.
  V293_clr_read H1a 1%nat I1a.
  V293_mem_write P H1a 4%nat (V293_mem_ptr_field pmem) (V293_mem_link_next table ix)
    (Vptr (bt,Int.repr 40)) M1b S1b H1b.
  V293_clr_read H1b 1%nat I1b.
  V293_mem_write P H1b 1%nat (evar ix) (V293_mem_link_inc ix)
    (Vint32 (Int.repr 2)) M2 S1c H2.
  V293_clr_read H2 1%nat Ix2.
  assert (G2 : evalval (V293_mem_link_guard ix) (ge,le,M2)=Some (Vint32 Int.one)).
  { unfold V293_mem_link_guard. V293_tcb_eval. }
  V293_mem_write P H2 0%nat (evar pmem) (V293_mem_link_address table ix)
    (Vptr (bt,Int.repr 40)) M2a S2a H2a.
  V293_clr_read H2a 0%nat P2a.
  V293_clr_read H2a 1%nat I2a.
  V293_mem_write P H2a 5%nat (V293_mem_ptr_field pmem) (V293_mem_link_next table ix)
    (Vptr (bt,Int.repr 60)) M2b S2b H2b.
  V293_clr_read H2b 1%nat I2b.
  V293_mem_write P H2b 1%nat (evar ix) (V293_mem_link_inc ix)
    (Vint32 (Int.repr 3)) M3 S2c H3.
  V293_clr_read H3 1%nat Ix3.
  assert (G3 : evalval (V293_mem_link_guard ix) (ge,le,M3)=Some (Vint32 Int.one)).
  { unfold V293_mem_link_guard. V293_tcb_eval. }
  V293_mem_write P H3 0%nat (evar pmem) (V293_mem_link_address table ix)
    (Vptr (bt,Int.repr 60)) M3a S3a H3a.
  V293_clr_read H3a 0%nat P3a.
  V293_clr_read H3a 1%nat I3a.
  V293_mem_write P H3a 6%nat (V293_mem_ptr_field pmem) (V293_mem_link_next table ix)
    (Vptr (bt,Int.repr 80)) M3b S3b H3b.
  V293_clr_read H3b 1%nat I3b.
  V293_mem_write P H3b 1%nat (evar ix) (V293_mem_link_inc ix)
    (Vint32 (Int.repr 4)) M4 S3c H4.
  V293_clr_read H4 1%nat Ix4.
  assert (G4 : evalval (V293_mem_link_guard ix) (ge,le,M4)=Some (Vint32 Int.zero)).
  { unfold V293_mem_link_guard. V293_tcb_eval. }
  V293_mem_write P H4 0%nat (evar pmem) (V293_mem_link_address table ix)
    (Vptr (bt,Int.repr 80)) Mt1 St1 Ht1.
  V293_clr_read Ht1 0%nat Pt1.
  V293_mem_write P Ht1 7%nat (V293_mem_ptr_field pmem) (ecast enull (Tptr Tvoid))
    Vnull Mt2 St2 Ht2.
  V293_mem_write P Ht2 2%nat (evar free_head) (eaddrof (earrayelem (evar table) (econst32 Int.zero)))
    (Vptr (bt,Int.zero)) Mf St3 Hf.
  assert (Loop : forall ks, cstepstar P
    (curs (V293_mem_link_loop table pmem ix),(kenil,ks)) (ge,le,M0)
    (curs (sskip None),(kenil,ks)) (ge,le,M4)).
  { intro ks. unfold V293_mem_link_loop,V293_mem_link_iteration.
    eapply V293_rdy_while_true;[exact G0 | | ].
    { intro tail.
      eapply V293_rekey_sequence_execution;[exact S0a | ].
      eapply V293_rekey_sequence_execution;[exact S0b | ].
      apply S0c. }
    eapply V293_rdy_while_true;[exact G1 | | ].
    { intro tail.
      eapply V293_rekey_sequence_execution;[exact S1a | ].
      eapply V293_rekey_sequence_execution;[exact S1b | ].
      apply S1c. }
    eapply V293_rdy_while_true;[exact G2 | | ].
    { intro tail.
      eapply V293_rekey_sequence_execution;[exact S2a | ].
      eapply V293_rekey_sequence_execution;[exact S2b | ].
      apply S2c. }
    eapply V293_rdy_while_true;[exact G3 | | ].
    { intro tail.
      eapply V293_rekey_sequence_execution;[exact S3a | ].
      eapply V293_rekey_sequence_execution;[exact S3b | ].
      apply S3c. }
    apply V293_rdy_while_false;exact G4. }
  exists Mf. split;[ | exact Hf]. intro ks.
  unfold V293_init_mem_links,V293_mem_link_tail.
  eapply V293_rekey_sequence_execution;[exact Init | ].
  eapply V293_rekey_sequence_execution;[exact Loop | ].
  eapply V293_rekey_sequence_execution;[exact St1 | ].
  eapply V293_rekey_sequence_execution;[exact St2 | apply St3].
Qed.
(* Real clear call, with fresh parameters derived from this actual memory. *)
Theorem V293_OS_MemInit_clear_call : forall oldmems frame P ks ge le M ir aux O op
  clear dest size table bt,
  P clear=Some (V293_MemClr_function dest size) -> dest<>size ->
  get le table=None -> get ge table=Some (bt,V293_mem_table_type) ->
  length oldmems=100%nat ->
  (ge,le,M,ir,aux,O,op) |= V293_rdy_raw_cells (V293_clr_bytes bt 0 oldmems++frame) Atrue ->
  exists Mf,
    cstepstar P (curs (scall clear [V293_init_clear_address table;
      V293_init_clear_size V293_mem_table_type]),(kenil,ks)) (ge,le,M)
      (curs (sskip None),(kenil,ks)) (ge,le,Mf) /\
    (ge,le,Mf,ir,aux,O,op) |= V293_rdy_raw_cells
      (V293_clr_bytes bt 0 (repeat (Vint32 Int.zero) 100)++frame) Atrue.
Proof.
  intros oldmems frame P ks ge le M ir aux O op clear dest size table bt
    Lookup Names Tn Tg Length Entry.
  destruct (V293_fresh_parameters_away M (((bt,0),Tint8,Vundef)::frame))
    as (bp&bs&DS&FD&FS&Away).
  assert (Bt : bt<>bp /\ bt<>bs) by (apply (Away (bt,0) Tint8 Vundef);left;reflexivity).
  destruct (V293_init_clear_arguments ge le M table bt V293_mem_type 5 Tn Tg
    ltac:(change (100<=65535);lia)) as (DT&DV&ST&SV).
  destruct (V293_MemClr_call_owned oldmems frame P ks ge le M ir aux O op
    clear dest size bp bs bt 0 (V293_init_clear_address table)
    (V293_init_clear_size V293_mem_table_type) Lookup Names DS (proj1 Bt) (proj2 Bt)
    ltac:(intros a tp v Member;apply (Away a tp v);right;exact Member)
    FS FD DT DV ST ltac:(rewrite Length;exact SV)
    ltac:(rewrite Length;cbn;lia) ltac:(lia)
    ltac:(rewrite Length;change (0+100<=4294967295);lia) Entry)
    as (Mf&Exec&Final&DGone&SGone).
  exists Mf. split;[exact Exec | rewrite Length in Final;exact Final].
Qed.
Lemma V293_mem_prepare_cleared : forall bt locals frame,
  V293_rdy_raw_cells (V293_clr_bytes bt 0 (repeat (Vint32 Int.zero) 100)++locals++frame) Atrue ==>
  V293_rdy_raw_cells (locals++V293_mem_fields_cells bt 0 5)
    (V293_rdy_raw_cells (V293_mem_untouched_cells bt 0 5)
      (V293_rdy_raw_cells frame Atrue)).
Proof.
  intros bt locals frame s H. repeat rewrite V293_raw_cells_append in H.
  apply (V293_zero_mem_fields 5 bt 0 _) in H.
  change (s |= V293_rdy_raw_cells
    (V293_mem_fields_cells bt 0 5++V293_mem_untouched_cells bt 0 5)
    (V293_rdy_raw_cells locals (V293_rdy_raw_cells frame Atrue))) in H.
  apply V293_raw_cells_swap in H. repeat rewrite V293_raw_cells_append in *;exact H.
Qed.
Theorem V293_OS_MemInit_body_execution : forall oldmems frame P ks ge le M ir aux O op
  clear dest size table free_head pmem ix bt bf bp bi vp vi vf,
  P clear=Some (V293_MemClr_function dest size) -> dest<>size ->
  V293_mem_link_env ge le table free_head pmem ix bt bf bp bi ->
  length oldmems=100%nat ->
  (ge,le,M,ir,aux,O,op) |= V293_rdy_raw_cells
    (V293_clr_bytes bt 0 oldmems++V293_mem_link_locals bp bi bf vp vi vf++frame) Atrue ->
  exists Mf,
    cstepstar P (curs (V293_init_mem_body clear table free_head pmem ix),
      (kenil,ks)) (ge,le,M) (curs (sskip None),(kenil,ks)) (ge,le,Mf) /\
    (ge,le,Mf,ir,aux,O,op) |= V293_rdy_raw_cells (V293_mem_link_final bp bi bf bt)
      (V293_rdy_raw_cells (V293_mem_untouched_cells bt 0 5)
        (V293_rdy_raw_cells frame Atrue)).
Proof.
  intros oldmems frame P ks ge le M ir aux O op clear dest size table free_head pmem ix
    bt bf bp bi vp vi vf Lookup Names Env Length Entry.
  destruct Env as (Tn&Tg&Rest).
  destruct (V293_OS_MemInit_clear_call oldmems
    (V293_mem_link_locals bp bi bf vp vi vf++frame) P
    (kseq (V293_init_mem_links table free_head pmem ix) ks)
    ge le M ir aux O op clear dest size table bt Lookup Names Tn Tg Length Entry)
    as (M1&Clear&Cleared).
  apply (V293_mem_prepare_cleared bt _ frame) in Cleared.
  destruct (V293_OS_MemInit_links_execution P ge le M1 ir aux O op _
    table free_head pmem ix bt bf bp bi vp vi vf
    (conj Tn (conj Tg Rest)) Cleared) as (Mf&Links&Final).
  exists Mf. split;[ | exact Final]. unfold V293_init_mem_body.
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
Definition V293_mem_call_locals pmem ix bp bi : env :=
  set (set emp pmem (bp,Tptr V293_mem_type)) ix (bi,Tint16).
Definition V293_mem_call_blocks (bp bi : block) := [bp;bi].
Definition V293_mem_call_head bf vf : list V293_record_cell :=
  [((bf,0),Tptr V293_mem_type,vf)].
Definition V293_mem_call_result bf bt frame :=
  V293_mem_call_head bf (Vptr (bt,Int.zero))++V293_mem_linked bt++
    V293_mem_untouched_cells bt 0 5++frame.
Lemma V293_mem_call_addresses : forall pmem ix bp bi,
  pmem<ix -> getaddr (V293_mem_call_locals pmem ix bp bi)=
    [(bp,Tptr V293_mem_type);(bi,Tint16)].
Proof.
  intros pmem ix bp bi A. unfold V293_mem_call_locals.
  change (getaddr (EnvMod.set (EnvMod.set EnvMod.emp pmem (bp,Tptr V293_mem_type))
    ix (bi,Tint16))=[(bp,Tptr V293_mem_type);(bi,Tint16)]).
  cbn [EnvMod.set EnvMod.lst EnvMod.set' EnvMod.emp EnvMod.emp' getaddr getaddrlist].
  repeat first [progress cbn [EnvMod.set' getaddrlist] | match goal with
  | |- context [identspec.blt ?x ?y] =>
    let H:=fresh in assert (H:identspec.blt x y=false) by (unfold identspec.blt;apply Z.ltb_ge;lia);rewrite H
  | |- context [identspec.beq ?x ?y] => rewrite (identspec.neq_beq_false x y) by lia
  end ]. reflexivity.
Qed.

Theorem V293_OS_MemInit_call_return : forall oldmems frame P ks ge caller M
  ir aux O op f clear dest size table free_head pmem ix
  bt bf bp bi vf,
  P f=Some (V293_MemInit_function clear table free_head pmem ix) ->
  P clear=Some (V293_MemClr_function dest size) -> dest<>size ->
  pmem<ix ->
  NoDup (V293_mem_call_blocks bp bi) ->
  fresh M bp -> fresh M bi ->
  V293_mem_link_env ge (V293_mem_call_locals pmem ix bp bi)
    table free_head pmem ix bt bf bp bi ->
  length oldmems=100%nat ->
  (forall a tp v, In (a,tp,v) (V293_mem_call_result bf bt frame) ->
    ~In (fst a) (V293_mem_call_blocks bp bi)) ->
  (ge,caller,M,ir,aux,O,op) |= V293_rdy_raw_cells
    (V293_clr_bytes bt 0 oldmems++
      V293_mem_call_head bf vf++frame) Atrue ->
  exists Ms Mf,
    cstepstar P (curs (scall f nil),(kenil,ks)) (ge,caller,M)
      (curs (sskip None),(kenil,ks)) (ge,caller,Mf) /\
    (ge,V293_mem_call_locals pmem ix bp bi,Ms,ir,aux,O,op) |=
      V293_rdy_raw_cells (V293_mem_link_final bp bi bf bt)
        (V293_rdy_raw_cells (V293_mem_untouched_cells bt 0 5)
          (V293_rdy_raw_cells frame Atrue)) /\
    (ge,caller,Mf,ir,aux,O,op) |= V293_rdy_raw_cells (V293_mem_call_result bf bt frame) Atrue /\
    (forall c i, ~In c (V293_mem_call_blocks bp bi) -> get Mf (c,i)=get Ms (c,i)) /\
    (forall c tp k, In (c,tp) [(bp,Tptr V293_mem_type);(bi,Tint16)] ->
      (k<typelen tp)%nat -> get Mf (c,Z.of_nat k)=None).
Proof.
  intros oldmems frame P ks ge caller M ir aux O op f clear dest size table
    free_head pmem ix bt bf bp bi vf
    Program Clear Names A ND Fp Fi Env Length Away Owned.
  set (le:=V293_mem_call_locals pmem ix bp bi).
  assert (Frame : (ge,le,M,ir,aux,O,op) |= V293_rdy_raw_cells
    (V293_clr_bytes bt 0 oldmems++V293_mem_call_head bf vf++frame) Atrue).
  { eapply V293_raw_cells_environment;[right;reflexivity | exact Owned]. }
  assert (Distinct : bp<>bi).
  { unfold V293_mem_call_blocks in ND. inversion ND as [ | x xs NI N1];subst.
    cbn in NI. intuition congruence. }
  set (M1:=allocb M bp 0 (typelen (Tptr V293_mem_type))).
  set (M2:=allocb M1 bi 0 (typelen Tint16)).
  assert (Fi1 : fresh M1 bi).
  { unfold M1;apply V293_tcb_fresh_after_alloc;[congruence | exact Fi]. }
  pose proof (V293_tick_allocate_frame ge le M ir aux O op bp (Tptr V293_mem_type) _ Fp Frame) as H1.
  pose proof (V293_tick_allocate_frame ge le M1 ir aux O op bi Tint16 _ Fi1 H1) as H2.
  assert (Start : (ge,le,M2,ir,aux,O,op) |= V293_rdy_raw_cells
    (V293_clr_bytes bt 0 oldmems++
      V293_mem_link_locals bp bi bf Vundef Vundef vf++frame) Atrue).
  { rewrite V293_raw_cells_append in H2.
    change ((ge,le,M2,ir,aux,O,op) |= V293_rdy_raw_cells
      ([((bi,0),Tint16,Vundef);((bp,0),Tptr V293_mem_type,Vundef)])
      (V293_rdy_raw_cells (V293_clr_bytes bt 0 oldmems)
        (V293_rdy_raw_cells (V293_mem_call_head bf vf++frame) Atrue))) in H2.
    apply V293_raw_cells_swap in H2.
    rewrite V293_raw_cells_append.
    eapply V293_raw_cells_mono;[ | exact H2].
    intros st HS. cbn [V293_mem_link_locals V293_mem_call_head V293_rdy_raw_cells app] in *.
    clear -HS. sep auto. }
  set (body:=sseq (V293_init_mem_body clear table free_head pmem ix) sret).
  destruct (V293_OS_MemInit_body_execution oldmems frame P
    (kseq sret (kcall f body caller ks)) ge le M2 ir aux O op
    clear dest size table free_head pmem ix
    bt bf bp bi Vundef Vundef vf
    Clear Names Env Length Start) as (Ms&Exec&Final).
  assert (Layout : getaddr le=[(bp,Tptr V293_mem_type);(bi,Tint16)]).
  { unfold le. apply V293_mem_call_addresses;assumption. }
  assert (Writable : forall c tp, In (c,tp) (getaddr le) -> V293_bytes_writable Ms c 0 (typelen tp)).
  { intros c tp Member. rewrite Layout in Member.
    unfold V293_mem_link_final,V293_mem_link_locals in Final.
    cbn [app V293_rdy_raw_cells] in Final.
    destruct Member as [E | [E | E]];
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
          (d2:=dcons pmem (Tptr V293_mem_type) (dcons ix Tint16 dnil));
          [reflexivity | reflexivity | exact Program | exact I | reflexivity]. }
      eapply c_stepstarn.
      { eapply stmt_step;[reflexivity | ]. eapply salloclv_step;[reflexivity | reflexivity | ].
        exists bp. repeat split;try assumption;try reflexivity.
        intros [v E]. rewrite map_emp_get in E;discriminate. }
      eapply c_stepstarn.
      { eapply stmt_step;[reflexivity | ]. eapply salloclv_step;[reflexivity | reflexivity | ].
        exists bi. repeat split;try assumption;try reflexivity.
        intros [v E]. rewrite map_get_set' in E by lia. rewrite map_emp_get in E;discriminate. }
      eapply c_stepstarn. { eapply stmt_step;[reflexivity | apply sallocend_step]. }
      eapply c_stepstarn. { eapply stmt_step;[reflexivity | apply sseq_step]. }
      eapply V293_cstepstar_trans;[exact Exec | ].
      eapply c_stepstarn. { eapply stmt_step;[reflexivity | constructor]. }
      exact Return.
    + split;[exact Final | ]. split.
      * eapply V293_raw_cells_return_many with (M:=Ms) (le:=le) (freed:=V293_mem_call_blocks bp bi).
        -- exact Away.
        -- intros c i Outside. apply Preserve. rewrite Layout. exact Outside.
        -- change ((ge,le,Ms,ir,aux,O,op) |= V293_rdy_raw_cells
             ([((bp,0),Tptr V293_mem_type,Vptr (bt,Int.repr 80));
               ((bi,0),Tint16,Vint32 (Int.repr 4))])
             (V293_rdy_raw_cells (V293_mem_call_result bf bt frame) Atrue)) in Final.
           apply V293_raw_cells_swap in Final. exact Final.
      * split.
        -- intros c i Outside. apply Preserve. rewrite Layout. exact Outside.
        -- intros c tp k Member Bound. apply (Removed c tp k);[rewrite Layout;exact Member | exact Bound].
Qed.
