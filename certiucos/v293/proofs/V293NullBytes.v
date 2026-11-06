(* Canonical zero bytes, not a readback oracle, give typed null ownership. *)
Require Import CertiOS.certiucos.v293.code.V293OSMemClr.
Require Import CertiOS.certiucos.v293.proofs.V293MemClr.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope Z_scope.

Theorem V293_pointer_zero_bytes_iff : forall tp bl,
  decode_val (Tptr tp) (inj_bytes bl)=Vnull <-> bl=list_repeat 4 Byte.zero.
Proof.
  intros tp bl. unfold decode_val. rewrite proj_inj_bytes.
  destruct (list_eq_dec Byte.eq_dec bl (list_repeat 4 Byte.zero));
    split;intros;try assumption;try reflexivity;try discriminate;contradiction.
Qed.

Lemma V293_raw_cells_separate : forall cells R,
  V293_rdy_raw_cells cells R ==> V293_rdy_raw_cells cells Aemp ** R.
Proof.
  induction cells as [ | [[a tp] v] tail IH];intros R s H;cbn [V293_rdy_raw_cells] in *.
  - clear -H. sep auto.
  - assert (K : s |= Amapsto a tp true v ** (V293_rdy_raw_cells tail Aemp ** R)).
    { eapply astar_mono;[intros st HS;exact HS | apply IH | exact H]. }
    clear -K. sep auto.
Qed.

Lemma V293_zero_bytes_memory : forall n b off s,
  s |= V293_rdy_raw_cells (V293_clr_bytes b off (repeat (Vint32 Int.zero) n)) Aemp ->
  ptomvallist (b,off) true (repeat (Byte Byte.zero) n) (getmem s) /\
  getabst s=emp.
Proof.
  induction n as [ | n IH];intros b off s H.
  - destruct s as [[[[[[ge le] M] ir] aux] O] op].
    cbn [repeat V293_clr_bytes V293_rdy_raw_cells sat empst emptaskst emposabst getmem getabst] in *.
    tauto.
  - cbn [repeat V293_clr_bytes V293_rdy_raw_cells] in H.
    destruct H as (M1&M2&M&o1&o2&o&ME&J&OE&JO&Head&Tail).
    specialize (IH b (off+1) (substmo s M2 o2) Tail).
    destruct s as [[[[[[ge le] Ms] ir] aux] Os] op].
    cbn [substmo getmem getabst] in *;subst M o.
    destruct IH as [Rest O2].
    cbn [sat getmem getabst emposabst] in Head.
    destruct Head as [(vl&Enc&Point) O1]. subst vl.
    change (exists a c, join a c M1 /\ ptomval (b,off) true (Byte Byte.zero) a /\ c=emp) in Point.
    destruct Point as (a&c&JC&Single&Empty);subst c.
    apply map_join_emp' in JC. subst a.
    split.
    + cbn [repeat ptomvallist]. exists M1. exists M2. split;[exact J | ]. split;assumption.
    + unfold emposabst in O1. subst o1 o2. apply map_join_emp' in JO. symmetry;exact JO.
Qed.

Theorem V293_zero4_null_owned : forall b off tp R,
  V293_rdy_raw_cells (V293_clr_bytes b off (repeat (Vint32 Int.zero) 4)) R ==>
    Amapsto (b,off) (Tptr tp) true Vnull ** R.
Proof.
  intros b off tp R s H. apply V293_raw_cells_separate in H.
  eapply astar_mono;[ | intros st HS;exact HS | exact H].
  intros st HS. destruct (V293_zero_bytes_memory 4 b off st HS) as [Bytes Empty].
  split;[ | exact Empty]. exists (repeat (Byte Byte.zero) 4). split;[reflexivity | exact Bytes].
Qed.

Lemma V293_raw_cells_append : forall before after R,
  V293_rdy_raw_cells (before++after) R=V293_rdy_raw_cells before (V293_rdy_raw_cells after R).
Proof. induction before as [ | [[a tp] v] tail IH];intros;cbn;[reflexivity | rewrite IH;reflexivity]. Qed.

Theorem V293_OS_MemClr_null_cell : forall values P ks ge le M ir aux O op R
  dest size bp bs b off tp,
  get le dest=Some (bp,Tptr Tint8) -> get le size=Some (bs,Tint16) ->
  length values=4%nat -> 0<=off -> off+4<=Int.max_unsigned ->
  (ge,le,M,ir,aux,O,op) |= V293_rdy_raw_cells (V293_clr_cells bp bs b off values) R ->
  exists Mf,
    cstepstar P (curs (V293_clr_loop dest size),(kenil,ks)) (ge,le,M)
      (curs (sskip None),(kenil,ks)) (ge,le,Mf) /\
    (ge,le,Mf,ir,aux,O,op) |= V293_rdy_raw_cells
      (V293_clr_params bp bs b (off+4) 0) (Amapsto (b,off) (Tptr tp) true Vnull ** R) /\
    load (Tptr tp) Mf (b,off)=Some Vnull.
Proof.
  intros values P ks ge le M ir aux O op R dest size bp bs b off tp Dest Size Len Start Limit Owned.
  destruct (V293_OS_MemClr_loop_execution values P ks ge le M ir aux O op R dest size bp bs b off
    Dest Size ltac:(rewrite Len;cbn;lia) Start ltac:(rewrite Len;exact Limit) Owned)
    as (Mf&Exec&Final).
  rewrite Len in Final. cbn [Z.of_nat] in Final.
  rewrite V293_raw_cells_append in Final.
  assert (Null : (ge,le,Mf,ir,aux,O,op) |= V293_rdy_raw_cells
      (V293_clr_params bp bs b (off+4) 0) (Amapsto (b,off) (Tptr tp) true Vnull ** R)).
  { cbn [V293_clr_params V293_rdy_raw_cells] in *.
    eapply astar_mono;[intros st HS;exact HS | | exact Final].
    eapply astar_mono;[intros st HS;exact HS | apply V293_zero4_null_owned]. }
  exists Mf. split;[exact Exec | ]. split;[exact Null | ].
  cbn [V293_clr_params V293_rdy_raw_cells] in Null.
  change (load (Tptr tp) (getmem (ge,le,Mf,ir,aux,O,op)) (b,off)=Some Vnull).
  eapply V293_star_load_r;[ | exact Null]. intros st H.
  eapply V293_star_load_r;[ | exact H]. intros st' H'.
  eapply V293_star_load_l;[ | exact H'].
  intros st'' [Points Empty]. eapply mapstoval_load;[reflexivity | exact Points].
Qed.
Print Assumptions V293_zero4_null_owned.
Print Assumptions V293_OS_MemClr_null_cell.
