(* Writable OSTCBNext links in the same memory returned by actual MemClr calls.
   Fixed configuration, existential no-interleaving executions, not GOOD_OS. *)
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

Lemma V293_zero4_comptr_null_owned : forall b off id R,
  V293_rdy_raw_cells (V293_clr_bytes b off (repeat (Vint32 Int.zero) 4)) R ==>
    Amapsto (b,off) (Tcom_ptr id) true Vnull ** R.
Proof.
  intros b off id R s H. apply V293_raw_cells_separate in H.
  eapply astar_mono;[ | intros st HS;exact HS | exact H].
  intros st HS. destruct (V293_zero_bytes_memory 4 b off st HS) as [Bytes Empty].
  split;[ | exact Empty]. exists (repeat (Byte Byte.zero) 4). split;[reflexivity | exact Bytes].
Qed.
Lemma V293_raw_cells_swap : forall a b R,
  V293_rdy_raw_cells a (V293_rdy_raw_cells b R) ==>
  V293_rdy_raw_cells b (V293_rdy_raw_cells a R).
Proof.
  intros a b R. repeat rewrite <-V293_raw_cells_append.
  apply V293_raw_cells_permutation. apply Permutation_app_comm.
Qed.
Fixpoint V293_tcb_next_cells b off n : list V293_record_cell :=
  match n with O=>[] | S m=>((b,off+20),Tcom_ptr 410,Vnull)::V293_tcb_next_cells b (off+56) m end.
Fixpoint V293_tcb_untouched_cells b off n : list V293_record_cell :=
  match n with O=>[] | S m=>
    V293_clr_bytes b off (repeat (Vint32 Int.zero) 20)++
    V293_clr_bytes b (off+24) (repeat (Vint32 Int.zero) 32)++
    V293_tcb_untouched_cells b (off+56) m end.
Theorem V293_zero_tcb_next_cells : forall n b off R,
  V293_rdy_raw_cells (V293_clr_bytes b off (repeat (Vint32 Int.zero) (56*n))) R ==>
  V293_rdy_raw_cells (V293_tcb_next_cells b off n)
    (V293_rdy_raw_cells (V293_tcb_untouched_cells b off n) R).
Proof.
  induction n as [ | n IH];intros b off R s H.
  - exact H.
  - replace (56*S n)%nat with (20+(4+(32+56*n)))%nat in H by lia.
    rewrite (V293_zero_bytes_split 20),V293_raw_cells_append in H.
    cbn [Z.of_nat] in H.
    rewrite (V293_zero_bytes_split 4),V293_raw_cells_append in H.
    replace (off+20+4) with (off+24) in H by lia.
    rewrite (V293_zero_bytes_split 32),V293_raw_cells_append in H.
    change (s |= V293_rdy_raw_cells
      (V293_clr_bytes b off (repeat (Vint32 Int.zero) 20))
      (V293_rdy_raw_cells (V293_clr_bytes b (off+20) (repeat (Vint32 Int.zero) 4))
      (V293_rdy_raw_cells (V293_clr_bytes b (off+20+4) (repeat (Vint32 Int.zero) 32))
      (V293_rdy_raw_cells (V293_clr_bytes b (off+20+4+32) (repeat (Vint32 Int.zero) (56*n))) R)))) in H.
    replace (off+20+4+32) with (off+56) in H by lia.
    replace (off+20+4) with (off+24) in H by lia.
    apply (V293_raw_cells_mono _ _ _ (V293_zero4_comptr_null_owned b (off+20) 410 _)) in H.
    apply V293_clr_frame_out in H.
    cbn [V293_tcb_next_cells V293_rdy_raw_cells].
    eapply astar_mono;[intros st HS;exact HS | | exact H].
    intros st HS.
    assert (K : st |= V293_rdy_raw_cells
      (V293_clr_bytes b off (repeat (Vint32 Int.zero) 20)++
       V293_clr_bytes b (off+24) (repeat (Vint32 Int.zero) 32))
      (V293_rdy_raw_cells (V293_tcb_next_cells b (off+56) n)
        (V293_rdy_raw_cells (V293_tcb_untouched_cells b (off+56) n) R))).
    { rewrite V293_raw_cells_append.
      eapply V293_raw_cells_mono;[apply V293_raw_cells_mono;apply IH | exact HS]. }
    apply V293_raw_cells_swap in K.
    cbn [V293_tcb_untouched_cells]. repeat rewrite V293_raw_cells_append.
    repeat rewrite V293_raw_cells_append in K. exact K.
Qed.

Definition V293_tcb_link_env ge le table list_head free_head ix ix_next ptcb1 ptcb2
  bt bl bf bi bn b1 b2 :=
  get le table=None /\ get ge table=Some (bt,V293_tcb_table_type) /\
  get le list_head=None /\ get ge list_head=Some (bl,Tptr V293_tcb_type) /\
  get le free_head=None /\ get ge free_head=Some (bf,Tptr V293_tcb_type) /\
  get le ix=Some (bi,Tint8) /\ get le ix_next=Some (bn,Tint8) /\
  get le ptcb1=Some (b1,Tptr V293_tcb_type) /\ get le ptcb2=Some (b2,Tptr V293_tcb_type).
Definition V293_tcb_link_locals bi bn b1 b2 bl bf vi vn v1 v2 vl vf : list V293_record_cell :=
  [((bi,0),Tint8,vi);((bn,0),Tint8,vn);
   ((b1,0),Tptr V293_tcb_type,v1);((b2,0),Tptr V293_tcb_type,v2);
   ((bl,0),Tptr V293_tcb_type,vl);((bf,0),Tptr V293_tcb_type,vf)].
Definition V293_tcb_linked_next bt :=
  map (fun i => ((bt,56*Z.of_nat i+20),Tcom_ptr 410,
    Vptr (bt,Int.repr (56*Z.of_nat (S i))))) (seq 0 12)++
  [((bt,692),Tcom_ptr 410,Vnull)].
Definition V293_tcb_link_final bi bn b1 b2 bl bf bt :=
  V293_tcb_link_locals bi bn b1 b2 bl bf
    (Vint32 (Int.repr 12)) (Vint32 (Int.repr 12))
    (Vptr (bt,Int.repr 672)) (Vptr (bt,Int.repr 672)) Vnull (Vptr (bt,Int.zero))++
  V293_tcb_linked_next bt.

Ltac V293_tcb_eval :=
  cbn [evaltype evalval evaladdr getoff get_lenv get_genv get_mem];
  cbv delta [env var memory.ident Modules.ident] in *;
  repeat first [match goal with H : ?lhs = ?rhs |- _ => progress rewrite H end |
    progress unfold getoff |
    progress cbv delta [env var memory.ident Modules.ident] |
    progress cbn [evaltype evalval evaladdr getoff get_lenv get_genv get_mem
      bop_type bop_int_type bop_eval is_int_type cast_eval add sub cmp_val cmpu typelen]];
  reflexivity.
Ltac V293_tcb_write P H n lhs rhs value next step owned :=
  let lhs := eval cbv beta delta [V293_tcb_link_field V293_tcb_link_address V293_tcb_link_inc] in lhs in
  let rhs := eval cbv beta delta [V293_tcb_link_field V293_tcb_link_address V293_tcb_link_inc] in rhs in
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
         apply eq_vcomptr;split;
           first [left;eexists;reflexivity | right;eexists;reflexivity]] |
       V293_tcb_eval | reflexivity | exact H] |
     destruct T as (next & step & owned)]
    end
  end.

Theorem V293_OS_InitTCBList_links_execution : forall P ge le M ir aux O op R
  table list_head free_head ix ix_next ptcb1 ptcb2 bt bl bf bi bn b1 b2 vi vn v1 v2 vl vf,
  V293_tcb_link_env ge le table list_head free_head ix ix_next ptcb1 ptcb2 bt bl bf bi bn b1 b2 ->
  (ge,le,M,ir,aux,O,op) |= V293_rdy_raw_cells
    (V293_tcb_link_locals bi bn b1 b2 bl bf vi vn v1 v2 vl vf++V293_tcb_next_cells bt 0 13) R ->
  exists Mf,
    (forall ks, cstepstar P
      (curs (V293_init_tcb_links table list_head free_head ix ix_next ptcb1 ptcb2),(kenil,ks)) (ge,le,M)
      (curs (sskip None),(kenil,ks)) (ge,le,Mf)) /\
    (ge,le,Mf,ir,aux,O,op) |= V293_rdy_raw_cells (V293_tcb_link_final bi bn b1 b2 bl bf bt) R.
Proof.
  intros P ge le M ir aux O op R table list_head free_head ix ix_next ptcb1 ptcb2
    bt bl bf bi bn b1 b2 vi vn v1 v2 vl vf Env Owned.
  destruct Env as (Tn&Tg&Ln&Lg&Fn&Fg&Ix&Inext&P1&P2).
  cbn [V293_tcb_link_locals V293_tcb_next_cells app] in Owned.
  V293_tcb_write P Owned 0%nat (evar ix) (ecast (econst32 Int.zero) Tint8)
    (Vint32 Int.zero) M0 Init H0.
  V293_clr_read H0 0%nat Ix0.
  assert (G0 : evalval (V293_tcb_link_guard ix) (ge,le,M0)=Some (Vint32 Int.one)).
  { unfold V293_tcb_link_guard. V293_tcb_eval. }
  V293_tcb_write P H0 1%nat (evar ix_next) (V293_tcb_link_inc ix)
    (Vint32 (Int.repr 1)) M0a S0a H0a.
  V293_clr_read H0a 0%nat Ia0.
  V293_tcb_write P H0a 2%nat (evar ptcb1) (V293_tcb_link_address table ix)
    (Vptr (bt,Int.repr 0)) M0b S0b H0b.
  V293_clr_read H0b 1%nat Ib0.
  V293_tcb_write P H0b 3%nat (evar ptcb2) (V293_tcb_link_address table ix_next)
    (Vptr (bt,Int.repr 56)) M0c S0c H0c.
  V293_clr_read H0c 2%nat Ic0.
  V293_clr_read H0c 3%nat Id0.
  V293_tcb_write P H0c 6%nat (V293_tcb_link_field ptcb1) (evar ptcb2)
    (Vptr (bt,Int.repr 56)) M0d S0d H0d.
  V293_clr_read H0d 0%nat Ie0.
  V293_tcb_write P H0d 0%nat (evar ix) (V293_tcb_link_inc ix)
    (Vint32 (Int.repr 1)) M1 S0e H1.
  V293_clr_read H1 0%nat Ix1.
  assert (G1 : evalval (V293_tcb_link_guard ix) (ge,le,M1)=Some (Vint32 Int.one)).
  { unfold V293_tcb_link_guard. V293_tcb_eval. }
  V293_tcb_write P H1 1%nat (evar ix_next) (V293_tcb_link_inc ix)
    (Vint32 (Int.repr 2)) M1a S1a H1a.
  V293_clr_read H1a 0%nat Ia1.
  V293_tcb_write P H1a 2%nat (evar ptcb1) (V293_tcb_link_address table ix)
    (Vptr (bt,Int.repr 56)) M1b S1b H1b.
  V293_clr_read H1b 1%nat Ib1.
  V293_tcb_write P H1b 3%nat (evar ptcb2) (V293_tcb_link_address table ix_next)
    (Vptr (bt,Int.repr 112)) M1c S1c H1c.
  V293_clr_read H1c 2%nat Ic1.
  V293_clr_read H1c 3%nat Id1.
  V293_tcb_write P H1c 7%nat (V293_tcb_link_field ptcb1) (evar ptcb2)
    (Vptr (bt,Int.repr 112)) M1d S1d H1d.
  V293_clr_read H1d 0%nat Ie1.
  V293_tcb_write P H1d 0%nat (evar ix) (V293_tcb_link_inc ix)
    (Vint32 (Int.repr 2)) M2 S1e H2.
  V293_clr_read H2 0%nat Ix2.
  assert (G2 : evalval (V293_tcb_link_guard ix) (ge,le,M2)=Some (Vint32 Int.one)).
  { unfold V293_tcb_link_guard. V293_tcb_eval. }
  V293_tcb_write P H2 1%nat (evar ix_next) (V293_tcb_link_inc ix)
    (Vint32 (Int.repr 3)) M2a S2a H2a.
  V293_clr_read H2a 0%nat Ia2.
  V293_tcb_write P H2a 2%nat (evar ptcb1) (V293_tcb_link_address table ix)
    (Vptr (bt,Int.repr 112)) M2b S2b H2b.
  V293_clr_read H2b 1%nat Ib2.
  V293_tcb_write P H2b 3%nat (evar ptcb2) (V293_tcb_link_address table ix_next)
    (Vptr (bt,Int.repr 168)) M2c S2c H2c.
  V293_clr_read H2c 2%nat Ic2.
  V293_clr_read H2c 3%nat Id2.
  V293_tcb_write P H2c 8%nat (V293_tcb_link_field ptcb1) (evar ptcb2)
    (Vptr (bt,Int.repr 168)) M2d S2d H2d.
  V293_clr_read H2d 0%nat Ie2.
  V293_tcb_write P H2d 0%nat (evar ix) (V293_tcb_link_inc ix)
    (Vint32 (Int.repr 3)) M3 S2e H3.
  V293_clr_read H3 0%nat Ix3.
  assert (G3 : evalval (V293_tcb_link_guard ix) (ge,le,M3)=Some (Vint32 Int.one)).
  { unfold V293_tcb_link_guard. V293_tcb_eval. }
  V293_tcb_write P H3 1%nat (evar ix_next) (V293_tcb_link_inc ix)
    (Vint32 (Int.repr 4)) M3a S3a H3a.
  V293_clr_read H3a 0%nat Ia3.
  V293_tcb_write P H3a 2%nat (evar ptcb1) (V293_tcb_link_address table ix)
    (Vptr (bt,Int.repr 168)) M3b S3b H3b.
  V293_clr_read H3b 1%nat Ib3.
  V293_tcb_write P H3b 3%nat (evar ptcb2) (V293_tcb_link_address table ix_next)
    (Vptr (bt,Int.repr 224)) M3c S3c H3c.
  V293_clr_read H3c 2%nat Ic3.
  V293_clr_read H3c 3%nat Id3.
  V293_tcb_write P H3c 9%nat (V293_tcb_link_field ptcb1) (evar ptcb2)
    (Vptr (bt,Int.repr 224)) M3d S3d H3d.
  V293_clr_read H3d 0%nat Ie3.
  V293_tcb_write P H3d 0%nat (evar ix) (V293_tcb_link_inc ix)
    (Vint32 (Int.repr 4)) M4 S3e H4.
  V293_clr_read H4 0%nat Ix4.
  assert (G4 : evalval (V293_tcb_link_guard ix) (ge,le,M4)=Some (Vint32 Int.one)).
  { unfold V293_tcb_link_guard. V293_tcb_eval. }
  V293_tcb_write P H4 1%nat (evar ix_next) (V293_tcb_link_inc ix)
    (Vint32 (Int.repr 5)) M4a S4a H4a.
  V293_clr_read H4a 0%nat Ia4.
  V293_tcb_write P H4a 2%nat (evar ptcb1) (V293_tcb_link_address table ix)
    (Vptr (bt,Int.repr 224)) M4b S4b H4b.
  V293_clr_read H4b 1%nat Ib4.
  V293_tcb_write P H4b 3%nat (evar ptcb2) (V293_tcb_link_address table ix_next)
    (Vptr (bt,Int.repr 280)) M4c S4c H4c.
  V293_clr_read H4c 2%nat Ic4.
  V293_clr_read H4c 3%nat Id4.
  V293_tcb_write P H4c 10%nat (V293_tcb_link_field ptcb1) (evar ptcb2)
    (Vptr (bt,Int.repr 280)) M4d S4d H4d.
  V293_clr_read H4d 0%nat Ie4.
  V293_tcb_write P H4d 0%nat (evar ix) (V293_tcb_link_inc ix)
    (Vint32 (Int.repr 5)) M5 S4e H5.
  V293_clr_read H5 0%nat Ix5.
  assert (G5 : evalval (V293_tcb_link_guard ix) (ge,le,M5)=Some (Vint32 Int.one)).
  { unfold V293_tcb_link_guard. V293_tcb_eval. }
  V293_tcb_write P H5 1%nat (evar ix_next) (V293_tcb_link_inc ix)
    (Vint32 (Int.repr 6)) M5a S5a H5a.
  V293_clr_read H5a 0%nat Ia5.
  V293_tcb_write P H5a 2%nat (evar ptcb1) (V293_tcb_link_address table ix)
    (Vptr (bt,Int.repr 280)) M5b S5b H5b.
  V293_clr_read H5b 1%nat Ib5.
  V293_tcb_write P H5b 3%nat (evar ptcb2) (V293_tcb_link_address table ix_next)
    (Vptr (bt,Int.repr 336)) M5c S5c H5c.
  V293_clr_read H5c 2%nat Ic5.
  V293_clr_read H5c 3%nat Id5.
  V293_tcb_write P H5c 11%nat (V293_tcb_link_field ptcb1) (evar ptcb2)
    (Vptr (bt,Int.repr 336)) M5d S5d H5d.
  V293_clr_read H5d 0%nat Ie5.
  V293_tcb_write P H5d 0%nat (evar ix) (V293_tcb_link_inc ix)
    (Vint32 (Int.repr 6)) M6 S5e H6.
  V293_clr_read H6 0%nat Ix6.
  assert (G6 : evalval (V293_tcb_link_guard ix) (ge,le,M6)=Some (Vint32 Int.one)).
  { unfold V293_tcb_link_guard. V293_tcb_eval. }
  V293_tcb_write P H6 1%nat (evar ix_next) (V293_tcb_link_inc ix)
    (Vint32 (Int.repr 7)) M6a S6a H6a.
  V293_clr_read H6a 0%nat Ia6.
  V293_tcb_write P H6a 2%nat (evar ptcb1) (V293_tcb_link_address table ix)
    (Vptr (bt,Int.repr 336)) M6b S6b H6b.
  V293_clr_read H6b 1%nat Ib6.
  V293_tcb_write P H6b 3%nat (evar ptcb2) (V293_tcb_link_address table ix_next)
    (Vptr (bt,Int.repr 392)) M6c S6c H6c.
  V293_clr_read H6c 2%nat Ic6.
  V293_clr_read H6c 3%nat Id6.
  V293_tcb_write P H6c 12%nat (V293_tcb_link_field ptcb1) (evar ptcb2)
    (Vptr (bt,Int.repr 392)) M6d S6d H6d.
  V293_clr_read H6d 0%nat Ie6.
  V293_tcb_write P H6d 0%nat (evar ix) (V293_tcb_link_inc ix)
    (Vint32 (Int.repr 7)) M7 S6e H7.
  V293_clr_read H7 0%nat Ix7.
  assert (G7 : evalval (V293_tcb_link_guard ix) (ge,le,M7)=Some (Vint32 Int.one)).
  { unfold V293_tcb_link_guard. V293_tcb_eval. }
  V293_tcb_write P H7 1%nat (evar ix_next) (V293_tcb_link_inc ix)
    (Vint32 (Int.repr 8)) M7a S7a H7a.
  V293_clr_read H7a 0%nat Ia7.
  V293_tcb_write P H7a 2%nat (evar ptcb1) (V293_tcb_link_address table ix)
    (Vptr (bt,Int.repr 392)) M7b S7b H7b.
  V293_clr_read H7b 1%nat Ib7.
  V293_tcb_write P H7b 3%nat (evar ptcb2) (V293_tcb_link_address table ix_next)
    (Vptr (bt,Int.repr 448)) M7c S7c H7c.
  V293_clr_read H7c 2%nat Ic7.
  V293_clr_read H7c 3%nat Id7.
  V293_tcb_write P H7c 13%nat (V293_tcb_link_field ptcb1) (evar ptcb2)
    (Vptr (bt,Int.repr 448)) M7d S7d H7d.
  V293_clr_read H7d 0%nat Ie7.
  V293_tcb_write P H7d 0%nat (evar ix) (V293_tcb_link_inc ix)
    (Vint32 (Int.repr 8)) M8 S7e H8.
  V293_clr_read H8 0%nat Ix8.
  assert (G8 : evalval (V293_tcb_link_guard ix) (ge,le,M8)=Some (Vint32 Int.one)).
  { unfold V293_tcb_link_guard. V293_tcb_eval. }
  V293_tcb_write P H8 1%nat (evar ix_next) (V293_tcb_link_inc ix)
    (Vint32 (Int.repr 9)) M8a S8a H8a.
  V293_clr_read H8a 0%nat Ia8.
  V293_tcb_write P H8a 2%nat (evar ptcb1) (V293_tcb_link_address table ix)
    (Vptr (bt,Int.repr 448)) M8b S8b H8b.
  V293_clr_read H8b 1%nat Ib8.
  V293_tcb_write P H8b 3%nat (evar ptcb2) (V293_tcb_link_address table ix_next)
    (Vptr (bt,Int.repr 504)) M8c S8c H8c.
  V293_clr_read H8c 2%nat Ic8.
  V293_clr_read H8c 3%nat Id8.
  V293_tcb_write P H8c 14%nat (V293_tcb_link_field ptcb1) (evar ptcb2)
    (Vptr (bt,Int.repr 504)) M8d S8d H8d.
  V293_clr_read H8d 0%nat Ie8.
  V293_tcb_write P H8d 0%nat (evar ix) (V293_tcb_link_inc ix)
    (Vint32 (Int.repr 9)) M9 S8e H9.
  V293_clr_read H9 0%nat Ix9.
  assert (G9 : evalval (V293_tcb_link_guard ix) (ge,le,M9)=Some (Vint32 Int.one)).
  { unfold V293_tcb_link_guard. V293_tcb_eval. }
  V293_tcb_write P H9 1%nat (evar ix_next) (V293_tcb_link_inc ix)
    (Vint32 (Int.repr 10)) M9a S9a H9a.
  V293_clr_read H9a 0%nat Ia9.
  V293_tcb_write P H9a 2%nat (evar ptcb1) (V293_tcb_link_address table ix)
    (Vptr (bt,Int.repr 504)) M9b S9b H9b.
  V293_clr_read H9b 1%nat Ib9.
  V293_tcb_write P H9b 3%nat (evar ptcb2) (V293_tcb_link_address table ix_next)
    (Vptr (bt,Int.repr 560)) M9c S9c H9c.
  V293_clr_read H9c 2%nat Ic9.
  V293_clr_read H9c 3%nat Id9.
  V293_tcb_write P H9c 15%nat (V293_tcb_link_field ptcb1) (evar ptcb2)
    (Vptr (bt,Int.repr 560)) M9d S9d H9d.
  V293_clr_read H9d 0%nat Ie9.
  V293_tcb_write P H9d 0%nat (evar ix) (V293_tcb_link_inc ix)
    (Vint32 (Int.repr 10)) M10 S9e H10.
  V293_clr_read H10 0%nat Ix10.
  assert (G10 : evalval (V293_tcb_link_guard ix) (ge,le,M10)=Some (Vint32 Int.one)).
  { unfold V293_tcb_link_guard. V293_tcb_eval. }
  V293_tcb_write P H10 1%nat (evar ix_next) (V293_tcb_link_inc ix)
    (Vint32 (Int.repr 11)) M10a S10a H10a.
  V293_clr_read H10a 0%nat Ia10.
  V293_tcb_write P H10a 2%nat (evar ptcb1) (V293_tcb_link_address table ix)
    (Vptr (bt,Int.repr 560)) M10b S10b H10b.
  V293_clr_read H10b 1%nat Ib10.
  V293_tcb_write P H10b 3%nat (evar ptcb2) (V293_tcb_link_address table ix_next)
    (Vptr (bt,Int.repr 616)) M10c S10c H10c.
  V293_clr_read H10c 2%nat Ic10.
  V293_clr_read H10c 3%nat Id10.
  V293_tcb_write P H10c 16%nat (V293_tcb_link_field ptcb1) (evar ptcb2)
    (Vptr (bt,Int.repr 616)) M10d S10d H10d.
  V293_clr_read H10d 0%nat Ie10.
  V293_tcb_write P H10d 0%nat (evar ix) (V293_tcb_link_inc ix)
    (Vint32 (Int.repr 11)) M11 S10e H11.
  V293_clr_read H11 0%nat Ix11.
  assert (G11 : evalval (V293_tcb_link_guard ix) (ge,le,M11)=Some (Vint32 Int.one)).
  { unfold V293_tcb_link_guard. V293_tcb_eval. }
  V293_tcb_write P H11 1%nat (evar ix_next) (V293_tcb_link_inc ix)
    (Vint32 (Int.repr 12)) M11a S11a H11a.
  V293_clr_read H11a 0%nat Ia11.
  V293_tcb_write P H11a 2%nat (evar ptcb1) (V293_tcb_link_address table ix)
    (Vptr (bt,Int.repr 616)) M11b S11b H11b.
  V293_clr_read H11b 1%nat Ib11.
  V293_tcb_write P H11b 3%nat (evar ptcb2) (V293_tcb_link_address table ix_next)
    (Vptr (bt,Int.repr 672)) M11c S11c H11c.
  V293_clr_read H11c 2%nat Ic11.
  V293_clr_read H11c 3%nat Id11.
  V293_tcb_write P H11c 17%nat (V293_tcb_link_field ptcb1) (evar ptcb2)
    (Vptr (bt,Int.repr 672)) M11d S11d H11d.
  V293_clr_read H11d 0%nat Ie11.
  V293_tcb_write P H11d 0%nat (evar ix) (V293_tcb_link_inc ix)
    (Vint32 (Int.repr 12)) M12 S11e H12.
  V293_clr_read H12 0%nat Ix12.
  assert (G12 : evalval (V293_tcb_link_guard ix) (ge,le,M12)=Some (Vint32 Int.zero)).
  { unfold V293_tcb_link_guard. V293_tcb_eval. }
  V293_tcb_write P H12 2%nat (evar ptcb1) (V293_tcb_link_address table ix)
    (Vptr (bt,Int.repr 672)) Mt1 St1 Ht1.
  V293_clr_read Ht1 2%nat Pt12.
  V293_tcb_write P Ht1 18%nat (V293_tcb_link_field ptcb1) (ecast enull (Tptr V293_tcb_type))
    Vnull Mt2 St2 Ht2.
  V293_tcb_write P Ht2 4%nat (evar list_head) (ecast enull (Tptr V293_tcb_type)) Vnull Mt3 St3 Ht3.
  V293_tcb_write P Ht3 5%nat (evar free_head) (eaddrof (earrayelem (evar table) (econst32 Int.zero)))
    (Vptr (bt,Int.zero)) Mf St4 Hf.
  assert (Loop : forall ks, cstepstar P
    (curs (V293_tcb_link_loop table ix ix_next ptcb1 ptcb2),(kenil,ks)) (ge,le,M0)
    (curs (sskip None),(kenil,ks)) (ge,le,M12)).
  { intro ks. unfold V293_tcb_link_loop,V293_tcb_link_iteration.
    eapply V293_rdy_while_true;[exact G0 | | ].
    { intro tail.
      eapply V293_rekey_sequence_execution;[exact S0a | ].
      eapply V293_rekey_sequence_execution;[exact S0b | ].
      eapply V293_rekey_sequence_execution;[exact S0c | ].
      eapply V293_rekey_sequence_execution;[exact S0d | apply S0e]. }
    eapply V293_rdy_while_true;[exact G1 | | ].
    { intro tail.
      eapply V293_rekey_sequence_execution;[exact S1a | ].
      eapply V293_rekey_sequence_execution;[exact S1b | ].
      eapply V293_rekey_sequence_execution;[exact S1c | ].
      eapply V293_rekey_sequence_execution;[exact S1d | apply S1e]. }
    eapply V293_rdy_while_true;[exact G2 | | ].
    { intro tail.
      eapply V293_rekey_sequence_execution;[exact S2a | ].
      eapply V293_rekey_sequence_execution;[exact S2b | ].
      eapply V293_rekey_sequence_execution;[exact S2c | ].
      eapply V293_rekey_sequence_execution;[exact S2d | apply S2e]. }
    eapply V293_rdy_while_true;[exact G3 | | ].
    { intro tail.
      eapply V293_rekey_sequence_execution;[exact S3a | ].
      eapply V293_rekey_sequence_execution;[exact S3b | ].
      eapply V293_rekey_sequence_execution;[exact S3c | ].
      eapply V293_rekey_sequence_execution;[exact S3d | apply S3e]. }
    eapply V293_rdy_while_true;[exact G4 | | ].
    { intro tail.
      eapply V293_rekey_sequence_execution;[exact S4a | ].
      eapply V293_rekey_sequence_execution;[exact S4b | ].
      eapply V293_rekey_sequence_execution;[exact S4c | ].
      eapply V293_rekey_sequence_execution;[exact S4d | apply S4e]. }
    eapply V293_rdy_while_true;[exact G5 | | ].
    { intro tail.
      eapply V293_rekey_sequence_execution;[exact S5a | ].
      eapply V293_rekey_sequence_execution;[exact S5b | ].
      eapply V293_rekey_sequence_execution;[exact S5c | ].
      eapply V293_rekey_sequence_execution;[exact S5d | apply S5e]. }
    eapply V293_rdy_while_true;[exact G6 | | ].
    { intro tail.
      eapply V293_rekey_sequence_execution;[exact S6a | ].
      eapply V293_rekey_sequence_execution;[exact S6b | ].
      eapply V293_rekey_sequence_execution;[exact S6c | ].
      eapply V293_rekey_sequence_execution;[exact S6d | apply S6e]. }
    eapply V293_rdy_while_true;[exact G7 | | ].
    { intro tail.
      eapply V293_rekey_sequence_execution;[exact S7a | ].
      eapply V293_rekey_sequence_execution;[exact S7b | ].
      eapply V293_rekey_sequence_execution;[exact S7c | ].
      eapply V293_rekey_sequence_execution;[exact S7d | apply S7e]. }
    eapply V293_rdy_while_true;[exact G8 | | ].
    { intro tail.
      eapply V293_rekey_sequence_execution;[exact S8a | ].
      eapply V293_rekey_sequence_execution;[exact S8b | ].
      eapply V293_rekey_sequence_execution;[exact S8c | ].
      eapply V293_rekey_sequence_execution;[exact S8d | apply S8e]. }
    eapply V293_rdy_while_true;[exact G9 | | ].
    { intro tail.
      eapply V293_rekey_sequence_execution;[exact S9a | ].
      eapply V293_rekey_sequence_execution;[exact S9b | ].
      eapply V293_rekey_sequence_execution;[exact S9c | ].
      eapply V293_rekey_sequence_execution;[exact S9d | apply S9e]. }
    eapply V293_rdy_while_true;[exact G10 | | ].
    { intro tail.
      eapply V293_rekey_sequence_execution;[exact S10a | ].
      eapply V293_rekey_sequence_execution;[exact S10b | ].
      eapply V293_rekey_sequence_execution;[exact S10c | ].
      eapply V293_rekey_sequence_execution;[exact S10d | apply S10e]. }
    eapply V293_rdy_while_true;[exact G11 | | ].
    { intro tail.
      eapply V293_rekey_sequence_execution;[exact S11a | ].
      eapply V293_rekey_sequence_execution;[exact S11b | ].
      eapply V293_rekey_sequence_execution;[exact S11c | ].
      eapply V293_rekey_sequence_execution;[exact S11d | apply S11e]. }
    apply V293_rdy_while_false;exact G12. }
  exists Mf. split;[ | exact Hf].
  intro ks. unfold V293_init_tcb_links,V293_tcb_link_tail.
  eapply V293_rekey_sequence_execution;[exact Init | ].
  eapply V293_rekey_sequence_execution;[exact Loop | ].
  eapply V293_rekey_sequence_execution;[exact St1 | ].
  eapply V293_rekey_sequence_execution;[exact St2 | ].
  eapply V293_rekey_sequence_execution;[exact St3 | apply St4].
Qed.
Print Assumptions V293_OS_InitTCBList_links_execution.

Lemma V293_tcb_prepare_cleared : forall bt bp locals frame,
  V293_rdy_raw_cells
    (V293_clr_bytes bt 0 (repeat (Vint32 Int.zero) 728)++
     V293_clr_bytes bp 0 (repeat (Vint32 Int.zero) 52)++locals++frame) Atrue ==>
  V293_rdy_raw_cells (locals++V293_tcb_next_cells bt 0 13)
    (V293_rdy_raw_cells (V293_tcb_untouched_cells bt 0 13)
      (V293_rdy_raw_cells (V293_null_pointer_cells bp 0 13)
        (V293_rdy_raw_cells frame Atrue))).
Proof.
  intros bt bp locals frame s H. repeat rewrite V293_raw_cells_append in H.
  apply (V293_raw_cells_mono _ _ _ (V293_zero_pointer_cells 13 bp 0 _)) in H.
  apply (V293_zero_tcb_next_cells 13 bt 0 _) in H.
  assert (K : s |= V293_rdy_raw_cells
    (V293_tcb_next_cells bt 0 13++V293_tcb_untouched_cells bt 0 13++V293_null_pointer_cells bp 0 13)
    (V293_rdy_raw_cells locals (V293_rdy_raw_cells frame Atrue))).
  { repeat rewrite V293_raw_cells_append. exact H. }
  apply (V293_raw_cells_swap
    (V293_tcb_next_cells bt 0 13++V293_tcb_untouched_cells bt 0 13++V293_null_pointer_cells bp 0 13)
    locals (V293_rdy_raw_cells frame Atrue)) in K.
  repeat rewrite V293_raw_cells_append in *. exact K.
Qed.

(* Stable source-body interface: both calls, native loop and all four suffix
   writes are one actual execution. The four outer locals are already owned;
   their enclosing call allocation/free and OSInit/OSStart remain separate. *)
Theorem V293_OS_InitTCBList_body_execution : forall oldtcbs oldprios frame P ks ge le M
  ir aux O op clear dest size table priorities list_head free_head ix ix_next ptcb1 ptcb2
  bt bp bl bf bi bn b1 b2 vi vn v1 v2 vl vf,
  P clear=Some (V293_MemClr_function dest size) -> dest<>size ->
  V293_tcb_link_env ge le table list_head free_head ix ix_next ptcb1 ptcb2 bt bl bf bi bn b1 b2 ->
  get le priorities=None -> get ge priorities=Some (bp,V293_tcb_prio_table_type) ->
  length oldtcbs=728%nat -> length oldprios=52%nat ->
  (ge,le,M,ir,aux,O,op) |= V293_rdy_raw_cells
    (V293_clr_bytes bt 0 oldtcbs++V293_clr_bytes bp 0 oldprios++
     V293_tcb_link_locals bi bn b1 b2 bl bf vi vn v1 v2 vl vf++frame) Atrue ->
  exists Mf,
    cstepstar P (curs (V293_init_tcb_body clear table priorities list_head free_head ix ix_next ptcb1 ptcb2),
      (kenil,ks)) (ge,le,M) (curs (sskip None),(kenil,ks)) (ge,le,Mf) /\
    (ge,le,Mf,ir,aux,O,op) |= V293_rdy_raw_cells (V293_tcb_link_final bi bn b1 b2 bl bf bt)
      (V293_rdy_raw_cells (V293_tcb_untouched_cells bt 0 13)
        (V293_rdy_raw_cells (V293_null_pointer_cells bp 0 13)
          (V293_rdy_raw_cells frame Atrue))).
Proof.
  intros oldtcbs oldprios frame P ks ge le M ir aux O op clear dest size table priorities
    list_head free_head ix ix_next ptcb1 ptcb2 bt bp bl bf bi bn b1 b2 vi vn v1 v2 vl vf
    Lookup Dist Env Prn Prg Lt Lp Owned.
  destruct Env as (Tn&Tg&Rest).
  destruct (V293_OS_InitTCBList_clear_calls oldtcbs oldprios
    (V293_tcb_link_locals bi bn b1 b2 bl bf vi vn v1 v2 vl vf++frame) P
    (kseq (V293_init_tcb_links table list_head free_head ix ix_next ptcb1 ptcb2) ks)
    ge le M ir aux O op clear dest size table priorities bt bp
    Lookup Dist Tn Tg Prn Prg Lt Lp ltac:(repeat rewrite app_assoc;repeat rewrite app_assoc in Owned;exact Owned))
    as (M1&Clear&Cleared).
  apply (V293_tcb_prepare_cleared bt bp _ frame) in Cleared.
  destruct (V293_OS_InitTCBList_links_execution P ge le M1 ir aux O op _
    table list_head free_head ix ix_next ptcb1 ptcb2 bt bl bf bi bn b1 b2 vi vn v1 v2 vl vf
    (conj Tn (conj Tg Rest)) Cleared) as (Mf&Links&Final).
  exists Mf. split;[ | exact Final]. unfold V293_init_tcb_body.
  eapply c_stepstarn. { eapply stmt_step;[reflexivity | apply sseq_step]. }
  eapply V293_cstepstar_trans;[exact Clear | ].
  eapply c_stepstarn. { eapply stmt_step;[reflexivity | constructor]. }
  apply Links.
Qed.
Print Assumptions V293_zero_tcb_next_cells.
Print Assumptions V293_OS_InitTCBList_body_execution.
