(* Return writable raw ownership, not merely loads, through both real calls. *)
Require Import CertiOS.certiucos.v293.code.V293OSInitTCBClear.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.code.V293OSMemClr.
Require Import CertiOS.certiucos.v293.proofs.V293MemClr.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293MemClrCall.
Require Import CertiOS.certiucos.v293.proofs.V293NullBytes.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.basetac.join_lib.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope Z_scope.

Theorem V293_init_tcb_layout :
  typelen V293_tcb_type=56%nat /\
  typelen V293_tcb_table_type=728%nat /\
  typelen V293_tcb_prio_table_type=52%nat.
Proof. repeat split;reflexivity. Qed.

(* Only memory-only assertions are moved between environments. *)
Lemma V293_raw_cells_environment : forall cells R,
  R=Aemp \/ R=Atrue ->
  forall ge le M ir aux O op ge' le',
  (ge,le,M,ir,aux,O,op) |= V293_rdy_raw_cells cells R ->
  (ge',le',M,ir,aux,O,op) |= V293_rdy_raw_cells cells R.
Proof.
  induction cells as [ | [[a tp] v] tail IH];intros R Pure ge le M ir aux O op ge' le' Owned.
  - cbn [V293_rdy_raw_cells] in *. destruct Pure as [E | E];subst R;exact Owned.
  - apply sat_split in Owned. destruct Owned as (mh&mt&oh&ot&JM&JO&Head&Tail).
    apply sat_split'. exists mh. exists mt. exists oh. exists ot.
    split;[exact JM | ]. split;[exact JO | ]. split;[exact Head | ].
    eapply IH;[exact Pure | exact Tail].
Qed.

Lemma V293_raw_cells_absent_block : forall cells ge le M ir aux O op c,
  (forall a tp v, In (a,tp,v) cells -> fst a<>c) ->
  (ge,le,M,ir,aux,O,op) |= V293_rdy_raw_cells cells Aemp ->
  forall i, get M (c,i)=None.
Proof.
  induction cells as [ | [[[b off] tp] v] tail IH];intros ge le M ir aux O op c Away Owned i.
  - cbn [V293_rdy_raw_cells sat empst emptaskst] in Owned.
    destruct Owned as [Empty _]. subst M. apply map_emp_get.
  - apply sat_split in Owned. destruct Owned as (mh&mt&oh&ot&JM&JO&[Head Empty]&Tail).
    assert (Hh : get mh (c,i)=None).
    { destruct Head as (bytes&Encoding&Points).
      eapply V293_ptomvallist_other_block;[exact Points | ].
      pose proof (Away (b,off) tp v (or_introl eq_refl)). cbn in H;congruence. }
    erewrite map_join_get_none;[ | exact JM | exact Hh].
    eapply IH;[ | exact Tail]. intros a t w Member. apply (Away a t w);right;exact Member.
Qed.

Lemma V293_raw_cells_join : forall cells R,
  V293_rdy_raw_cells cells Aemp ** R ==> V293_rdy_raw_cells cells R.
Proof.
  induction cells as [ | [[a tp] v] tail IH];intros R s Owned;cbn [V293_rdy_raw_cells] in *.
  - clear -Owned. sep auto.
  - eapply astar_mono;[intros st H;exact H | apply IH | ]. clear -Owned. sep auto.
Qed.

(* The final free can remove parameters, but cannot remove an owned byte
   in another block. Retain the exact writable fragment via Maps.sub. *)
Lemma V293_raw_cells_return_frame : forall cells R ge le M ir aux O op
  caller Mf bp bs,
  (forall a tp v, In (a,tp,v) cells -> fst a<>bp /\ fst a<>bs) ->
  (forall c i, c<>bp -> c<>bs -> get Mf (c,i)=get M (c,i)) ->
  (ge,le,M,ir,aux,O,op) |= V293_rdy_raw_cells cells R ->
  (ge,caller,Mf,ir,aux,O,op) |= V293_rdy_raw_cells cells Atrue.
Proof.
  intros cells R ge le M ir aux O op caller Mf bp bs Away Frame Owned.
  apply V293_raw_cells_separate in Owned. apply sat_split in Owned.
  destruct Owned as (mp&mr&opart&orest&JM&JO&Part&Rest).
  assert (Sub : Maps.sub mp Mf).
  { unfold addr in *. apply sub_semp;[reflexivity | ]. intros [c i].
    destruct (Pos.eq_dec c bp) as [E | Cp].
    - subst c. rewrite (V293_raw_cells_absent_block cells ge le mp ir aux opart op bp
        ltac:(intros a tp v H;exact (proj1 (Away a tp v H))) Part).
      destruct (get Mf (bp,i));exact I.
    - destruct (Pos.eq_dec c bs) as [E | Cs].
      + subst c. rewrite (V293_raw_cells_absent_block cells ge le mp ir aux opart op bs
          ltac:(intros a tp v H;exact (proj2 (Away a tp v H))) Part).
        destruct (get Mf (bs,i));exact I.
      + rewrite Frame by assumption.
        destruct (get mp (c,i)) as [[permission value] | ] eqn:Cell.
        * destruct (@sub_semp1 (block*offset) (bool*memval) mem memMap mp M (c,i)
            (permission,value) eq_refl ltac:(exists mr;exact JM) Cell) as [Same | [Split Read]].
          -- rewrite Same. destruct permission;reflexivity.
          -- rewrite Split. destruct permission;cbn in *;try discriminate;reflexivity.
        * destruct (get M (c,i));exact I. }
  destruct Sub as [remainder Joined].
  apply V293_raw_cells_join.
  apply sat_split'. exists mp. exists remainder. exists opart. exists orest.
  split;[exact Joined | ]. split;[exact JO | ]. split;[ | exact I].
  eapply V293_raw_cells_environment;[left;reflexivity | exact Part].
Qed.

Lemma V293_clr_bytes_blocks : forall values b off a tp v,
  In (a,tp,v) (V293_clr_bytes b off values) -> fst a=b.
Proof.
  induction values as [ | w tail IH];intros b off a tp v Member;[contradiction | ].
  destruct Member as [E | Member];[inversion E;reflexivity | eapply IH;exact Member].
Qed.

Lemma V293_raw_cells_absorb_true : forall cells,
  V293_rdy_raw_cells cells Atrue ** Atrue ==> V293_rdy_raw_cells cells Atrue.
Proof.
  induction cells as [ | [[a tp] v] tail IH];intros s Owned;cbn [V293_rdy_raw_cells] in *.
  - exact I.
  - eapply astar_mono;[intros st H;exact H | apply IH | ]. clear -Owned. sep auto.
Qed.

Theorem V293_MemClr_call_owned : forall values frame P ks ge caller M ir aux O op
  f dest size bp bs b off ed es,
  P f=Some (V293_MemClr_function dest size) ->
  dest<>size -> bp<>bs -> b<>bp -> b<>bs ->
  (forall a tp v, In (a,tp,v) frame -> fst a<>bp /\ fst a<>bs) ->
  fresh M bs -> fresh M bp ->
  evaltype ed (ge,caller,M)=Some (Tptr Tint8) ->
  evalval ed (ge,caller,M)=Some (Vptr (b,Int.repr off)) ->
  evaltype es (ge,caller,M)=Some Tint16 ->
  evalval es (ge,caller,M)=Some (Vint32 (Int.repr (Z.of_nat (length values)))) ->
  Z.of_nat (length values)<=65535 -> 0<=off ->
  off+Z.of_nat (length values)<=Int.max_unsigned ->
  (ge,caller,M,ir,aux,O,op) |= V293_rdy_raw_cells
    (V293_clr_bytes b off values++frame) Atrue ->
  exists Mf,
    cstepstar P (curs (scall f [ed;es]),(kenil,ks)) (ge,caller,M)
      (curs (sskip None),(kenil,ks)) (ge,caller,Mf) /\
    (ge,caller,Mf,ir,aux,O,op) |= V293_rdy_raw_cells
      (V293_clr_bytes b off (repeat (Vint32 Int.zero) (length values))++frame) Atrue /\
    (forall k, (k<4)%nat -> get Mf (bp,Z.of_nat k)=None) /\
    (forall k, (k<2)%nat -> get Mf (bs,Z.of_nat k)=None).
Proof.
  intros values frame P ks ge caller M ir aux O op f dest size bp bs b off ed es
    Program Names Blocks Bp Bs FrameAway FreshSize FreshDest DT DV ST SV Bound Start Limit Owned.
  assert (Entry : (ge,V293_clr_locals dest size bp bs,M,ir,aux,O,op) |=
    V293_rdy_raw_cells (V293_clr_bytes b off values) (V293_rdy_raw_cells frame Atrue)).
  { rewrite <- V293_raw_cells_append.
    eapply V293_raw_cells_environment;[right;reflexivity | exact Owned]. }
  destruct (V293_OS_MemClr_call_return values P ks ge caller M ir aux O op
    (V293_rdy_raw_cells frame Atrue) f dest size bp bs b off ed es Program Names Blocks
    FreshSize FreshDest DT DV ST SV Bound Start Limit Entry)
    as (Ms&Mf&Exec&Final&Preserve&DestGone&SizeGone).
  exists Mf. split;[exact Exec | ]. split;[ | split;assumption].
  rewrite V293_raw_cells_append in Final. cbn [V293_clr_params V293_rdy_raw_cells] in Final.
  (* Discard only the two parameter objects, never the target/frame ownership. *)
  assert (Body : (ge,V293_clr_locals dest size bp bs,Ms,ir,aux,O,op) |=
    V293_rdy_raw_cells
      (V293_clr_bytes b off (repeat (Vint32 Int.zero) (length values))++frame) Atrue ** Atrue).
  { rewrite V293_raw_cells_append. clear -Final. sep auto. }
  apply V293_raw_cells_absorb_true in Body.
  eapply V293_raw_cells_return_frame;[ | exact Preserve | exact Body].
  intros a tp v Member. apply in_app_or in Member. destruct Member as [Byte | Cell].
  - pose proof (V293_clr_bytes_blocks _ _ _ _ _ _ Byte) as Same. rewrite Same. split;assumption.
  - exact (FrameAway a tp v Cell).
Qed.
Print Assumptions V293_init_tcb_layout.
Print Assumptions V293_MemClr_call_owned.

Require Import CertiOS.framework.proof.memory_bound.
Require Import CertiOS.framework.proof.memory_representation.
Require Import Coq.Sorting.Permutation.

Lemma V293_raw_cells_permutation : forall before after,
  Permutation before after -> forall R,
  V293_rdy_raw_cells before R ==> V293_rdy_raw_cells after R.
Proof.
  intros before after Order. induction Order;intros R s Owned;cbn [V293_rdy_raw_cells] in *.
  - exact Owned.
  - destruct x as [[a tp] v]. cbn [V293_rdy_raw_cells] in *.
    eapply astar_mono;[intros st H;exact H | apply IHOrder | exact Owned].
  - destruct x as [[a tp] v],y as [[b tq] w]. cbn [V293_rdy_raw_cells] in *. clear -Owned. sep auto.
  - apply IHOrder2. apply IHOrder1. exact Owned.
Qed.

Lemma V293_fresh_parameters_away : forall M (cells : list V293_record_cell),
  exists bp bs, bp<>bs /\ fresh M bp /\ fresh M bs /\
    (forall a tp v, In (a,tp,v) cells -> fst a<>bp /\ fst a<>bs).
Proof.
  intros M cells.
  set (bound:=fold_right Pos.max 1%positive (map (fun cell : V293_record_cell => fst (fst (fst cell))) cells)).
  assert (CellBound : forall a tp v, In (a,tp,v) cells -> (fst a<=bound)%positive).
  { unfold bound. induction cells as [ | [[a tp] v] tail IH];intros x t w Member;[contradiction | ].
    cbn [map fold_right]. destruct Member as [E | Member].
    - inversion E;subst. apply Pos.le_max_l.
    - eapply Pos.le_trans;[eapply IH;exact Member | apply Pos.le_max_r]. }
  destruct (memory_is_bounded M) as [upper MemoryBound].
  set (bp:=Pos.succ (Pos.max upper bound)). set (bs:=Pos.succ bp).
  assert (UpperPtr : (upper<bp)%positive).
  { unfold bp. eapply Pos.le_lt_trans;[apply Pos.le_max_l | apply Pos.lt_succ_diag_r]. }
  assert (BoundPtr : (bound<bp)%positive).
  { unfold bp. eapply Pos.le_lt_trans;[apply Pos.le_max_r | apply Pos.lt_succ_diag_r]. }
  assert (PtrSize : (bp<bs)%positive) by (unfold bs;apply Pos.lt_succ_diag_r).
  exists bp. exists bs. split.
  - intro E. rewrite E in PtrSize. exact (Pos.lt_irrefl _ PtrSize).
  - split;[apply blocks_below_fresh; eapply blocks_below_monotone;[exact MemoryBound | apply Pos.lt_le_incl;exact UpperPtr] | ].
    split.
    + apply blocks_below_fresh. eapply blocks_below_monotone;[exact MemoryBound | ].
      apply Pos.lt_le_incl. eapply Pos.lt_trans;[exact UpperPtr | exact PtrSize].
    + intros a tp v Member. split;intro E;pose proof (CellBound a tp v Member) as Small;rewrite E in Small.
      * exact (Pos.lt_irrefl _ (Pos.le_lt_trans _ _ _ Small BoundPtr)).
      * apply (Pos.lt_irrefl bs). eapply Pos.le_lt_trans;[exact Small | ].
        eapply Pos.lt_trans;[exact BoundPtr | exact PtrSize].
Qed.

Lemma V293_init_clear_arguments : forall ge le M table b tp n,
  get le table=None -> get ge table=Some (b,Tarray tp n) ->
  Z.of_nat (typelen (Tarray tp n))<=65535 ->
  evaltype (V293_init_clear_address table) (ge,le,M)=Some (Tptr Tint8) /\
  evalval (V293_init_clear_address table) (ge,le,M)=Some (Vptr (b,Int.zero)) /\
  evaltype (V293_init_clear_size (Tarray tp n)) (ge,le,M)=Some Tint16 /\
  evalval (V293_init_clear_size (Tarray tp n)) (ge,le,M)=
    Some (Vint32 (Int.repr (Z.of_nat (typelen (Tarray tp n))))).
Proof.
  intros ge le M table b tp n Local Global Bound.
  unfold V293_init_clear_address,V293_init_clear_size.
  cbn [evaltype evalval evaladdr get_lenv get_genv get_mem].
  cbv delta [env var memory.ident Modules.ident] in *.
  rewrite Local,Global. cbn [load addr_to_addrval evaltype evalval evaladdr
    get_lenv get_genv get_mem is_int_type cast_eval].
  rewrite Int.mul_zero,Int.add_zero. repeat split;try reflexivity.
  f_equal. f_equal. unfold Int.modu.
  rewrite Int.unsigned_repr by (change (0<=Z.of_nat (typelen (Tarray tp n))<=4294967295);lia).
  change (Int.repr (Z.of_nat (typelen (Tarray tp n)) mod 65536)=Int.repr (Z.of_nat (typelen (Tarray tp n)))).
  rewrite Z.mod_small by lia. reflexivity.
Qed.

(* Same source prefix, two actual calls; second allocation is chosen fresh
   in the memory actually returned by the first, not postulated there. *)
Theorem V293_OS_InitTCBList_clear_calls : forall oldtcbs oldprios frame P ks ge le M
  ir aux O op f dest size table priorities bt bp,
  P f=Some (V293_MemClr_function dest size) -> dest<>size ->
  get le table=None -> get ge table=Some (bt,V293_tcb_table_type) ->
  get le priorities=None -> get ge priorities=Some (bp,V293_tcb_prio_table_type) ->
  length oldtcbs=728%nat -> length oldprios=52%nat ->
  (ge,le,M,ir,aux,O,op) |= V293_rdy_raw_cells
    (V293_clr_bytes bt 0 oldtcbs++V293_clr_bytes bp 0 oldprios++frame) Atrue ->
  exists Mf,
    cstepstar P (curs (V293_init_tcb_clear f table priorities),(kenil,ks)) (ge,le,M)
      (curs (sskip None),(kenil,ks)) (ge,le,Mf) /\
    (ge,le,Mf,ir,aux,O,op) |= V293_rdy_raw_cells
      (V293_clr_bytes bt 0 (repeat (Vint32 Int.zero) 728)++
       V293_clr_bytes bp 0 (repeat (Vint32 Int.zero) 52)++frame) Atrue.
Proof.
  intros oldtcbs oldprios frame P ks ge le M ir aux O op f dest size table priorities bt bp
    Program Names TableLocal TableGlobal PrioLocal PrioGlobal TcbLen PrioLen Entry.
  set (cells:=((bt,0),Tint8,Vundef)::((bp,0),Tint8,Vundef)::frame).
  destruct (V293_fresh_parameters_away M cells) as (d1&s1&DS1&FD1&FS1&Away1).
  assert (Bt1 : bt<>d1 /\ bt<>s1) by (apply (Away1 (bt,0) Tint8 Vundef);left;reflexivity).
  assert (Bp1 : bp<>d1 /\ bp<>s1) by (apply (Away1 (bp,0) Tint8 Vundef);right;left;reflexivity).
  destruct (V293_init_clear_arguments ge le M table bt V293_tcb_type 13 TableLocal TableGlobal
    ltac:(change (728<=65535);lia)) as (DT1&DV1&ST1&SV1).
  set (second:=scall f [V293_init_clear_address priorities;V293_init_clear_size V293_tcb_prio_table_type]).
  destruct (V293_MemClr_call_owned oldtcbs (V293_clr_bytes bp 0 oldprios++frame) P (kseq second ks)
    ge le M ir aux O op f dest size d1 s1 bt 0
    (V293_init_clear_address table) (V293_init_clear_size V293_tcb_table_type)
    Program Names DS1 (proj1 Bt1) (proj2 Bt1)
    ltac:(intros a tp v Member;apply in_app_or in Member;destruct Member as [B|F];
      [rewrite (V293_clr_bytes_blocks _ _ _ _ _ _ B);exact Bp1 |
       apply (Away1 a tp v);right;right;exact F]) FS1 FD1 DT1 DV1 ST1
    ltac:(rewrite TcbLen;exact SV1) ltac:(rewrite TcbLen;cbn;lia) ltac:(lia)
    ltac:(rewrite TcbLen;change (0+728<=4294967295);lia) Entry)
    as (M1&First&AfterFirst&D1Gone&S1Gone).
  rewrite TcbLen in AfterFirst.
  assert (SecondEntry : (ge,le,M1,ir,aux,O,op) |= V293_rdy_raw_cells
    (V293_clr_bytes bp 0 oldprios++V293_clr_bytes bt 0 (repeat (Vint32 Int.zero) 728)++frame) Atrue).
  { eapply V293_raw_cells_permutation;[ | exact AfterFirst].
    repeat rewrite app_assoc. apply Permutation_app_tail. apply Permutation_app_comm. }
  destruct (V293_fresh_parameters_away M1 cells) as (d2&s2&DS2&FD2&FS2&Away2).
  assert (Bt2 : bt<>d2 /\ bt<>s2) by (apply (Away2 (bt,0) Tint8 Vundef);left;reflexivity).
  assert (Bp2 : bp<>d2 /\ bp<>s2) by (apply (Away2 (bp,0) Tint8 Vundef);right;left;reflexivity).
  destruct (V293_init_clear_arguments ge le M1 priorities bp (Tptr V293_tcb_type) 13 PrioLocal PrioGlobal
    ltac:(change (52<=65535);lia)) as (DT2&DV2&ST2&SV2).
  destruct (V293_MemClr_call_owned oldprios (V293_clr_bytes bt 0 (repeat (Vint32 Int.zero) 728)++frame)
    P ks ge le M1 ir aux O op f dest size d2 s2 bp 0
    (V293_init_clear_address priorities) (V293_init_clear_size V293_tcb_prio_table_type)
    Program Names DS2 (proj1 Bp2) (proj2 Bp2)
    ltac:(intros a tp v Member;apply in_app_or in Member;destruct Member as [B|F];
      [rewrite (V293_clr_bytes_blocks _ _ _ _ _ _ B);exact Bt2 |
       apply (Away2 a tp v);right;right;exact F]) FS2 FD2 DT2 DV2 ST2
    ltac:(rewrite PrioLen;exact SV2) ltac:(rewrite PrioLen;cbn;lia) ltac:(lia)
    ltac:(rewrite PrioLen;change (0+52<=4294967295);lia) SecondEntry)
    as (Mf&Second&Final&D2Gone&S2Gone).
  exists Mf. split.
  - unfold V293_init_tcb_clear. eapply c_stepstarn.
    { eapply stmt_step;[reflexivity | apply sseq_step]. }
    eapply V293_cstepstar_trans;[exact First | ].
    eapply c_stepstarn. { eapply stmt_step;[reflexivity | apply sskip_step]. }
    exact Second.
  - rewrite PrioLen in Final. eapply V293_raw_cells_permutation;[ | exact Final].
    repeat rewrite app_assoc. apply Permutation_app_tail. apply Permutation_app_comm.
Qed.
Print Assumptions V293_init_clear_arguments.
Print Assumptions V293_OS_InitTCBList_clear_calls.

Lemma V293_zero_bytes_split : forall n m b off,
  V293_clr_bytes b off (repeat (Vint32 Int.zero) (n+m)) =
  V293_clr_bytes b off (repeat (Vint32 Int.zero) n) ++
    V293_clr_bytes b (off+Z.of_nat n) (repeat (Vint32 Int.zero) m).
Proof.
  induction n as [ | n IH];intros m b off;cbn [Nat.add repeat V293_clr_bytes app].
  - rewrite Z.add_0_r;reflexivity.
  - rewrite IH. f_equal. replace (off+1+Z.of_nat n) with (off+Z.of_nat (S n)) by lia. reflexivity.
Qed.

Fixpoint V293_null_pointer_cells b off n : list V293_record_cell :=
  match n with
  | O => []
  | S n' => ((b,off),Tptr V293_tcb_type,Vnull)::V293_null_pointer_cells b (off+4) n'
  end.
Lemma V293_zero_pointer_cells : forall n b off R,
  V293_rdy_raw_cells (V293_clr_bytes b off (repeat (Vint32 Int.zero) (4*n))) R ==>
    V293_rdy_raw_cells (V293_null_pointer_cells b off n) R.
Proof.
  induction n as [ | n IH];intros b off R s Owned.
  - exact Owned.
  - replace (4*S n)%nat with (4+4*n)%nat in Owned by lia.
    rewrite V293_zero_bytes_split,V293_raw_cells_append in Owned.
    apply (V293_zero4_null_owned b off V293_tcb_type _) in Owned.
    cbn [V293_null_pointer_cells V293_rdy_raw_cells].
    eapply astar_mono;[intros st H;exact H | apply IH | exact Owned].
Qed.
Lemma V293_raw_cells_mono : forall cells P Q,
  (P ==> Q) -> V293_rdy_raw_cells cells P ==> V293_rdy_raw_cells cells Q.
Proof.
  induction cells as [ | [[a tp] v] tail IH];intros P Q Imp s Owned;cbn [V293_rdy_raw_cells] in *.
  - apply Imp;exact Owned.
  - eapply astar_mono;[intros st H;exact H | apply IH;exact Imp | exact Owned].
Qed.
Lemma V293_null_pointer_member : forall n p b off,
  (p<n)%nat ->
  In ((b,off+4*Z.of_nat p),Tptr V293_tcb_type,Vnull) (V293_null_pointer_cells b off n).
Proof.
  induction n as [ | n IH];intros p b off Small;[lia | ].
  destruct p as [ | p];cbn [V293_null_pointer_cells].
  - replace (off+4*Z.of_nat 0) with off by (cbn;lia). left;reflexivity.
  - right. replace (off+4*Z.of_nat (S p)) with ((off+4)+4*Z.of_nat p) by lia.
    apply IH;lia.
Qed.

(* Stable interface for the two-call source prefix, including all thirteen
   canonical null slots and returned write permissions for subsequent linking. *)
Theorem V293_OS_InitTCBList_cleared_tables : forall oldtcbs oldprios frame P ks ge le M
  ir aux O op f dest size table priorities bt bp,
  P f=Some (V293_MemClr_function dest size) -> dest<>size ->
  get le table=None -> get ge table=Some (bt,V293_tcb_table_type) ->
  get le priorities=None -> get ge priorities=Some (bp,V293_tcb_prio_table_type) ->
  length oldtcbs=728%nat -> length oldprios=52%nat ->
  (ge,le,M,ir,aux,O,op) |= V293_rdy_raw_cells
    (V293_clr_bytes bt 0 oldtcbs++V293_clr_bytes bp 0 oldprios++frame) Atrue ->
  exists Mf,
    cstepstar P (curs (V293_init_tcb_clear f table priorities),(kenil,ks)) (ge,le,M)
      (curs (sskip None),(kenil,ks)) (ge,le,Mf) /\
    (ge,le,Mf,ir,aux,O,op) |= V293_rdy_raw_cells
      (V293_clr_bytes bt 0 (repeat (Vint32 Int.zero) 728)++
       V293_null_pointer_cells bp 0 13++frame) Atrue /\
    (forall p, (p<13)%nat -> load (Tptr V293_tcb_type) Mf (bp,4*Z.of_nat p)=Some Vnull).
Proof.
  intros oldtcbs oldprios frame P ks ge le M ir aux O op f dest size table priorities bt bp
    Program Names TL TG PL PG TLen PLen Entry.
  destruct (V293_OS_InitTCBList_clear_calls oldtcbs oldprios frame P ks ge le M ir aux O op
    f dest size table priorities bt bp Program Names TL TG PL PG TLen PLen Entry)
    as (Mf&Exec&Final).
  assert (Typed : (ge,le,Mf,ir,aux,O,op) |= V293_rdy_raw_cells
      (V293_clr_bytes bt 0 (repeat (Vint32 Int.zero) 728)++
       V293_null_pointer_cells bp 0 13++frame) Atrue).
  { repeat rewrite V293_raw_cells_append in *.
    eapply V293_raw_cells_mono;[ | exact Final].
    apply (V293_zero_pointer_cells 13 bp 0 (V293_rdy_raw_cells frame Atrue)). }
  exists Mf. split;[exact Exec | ]. split;[exact Typed | ].
  intros p Small.
  change (load (Tptr V293_tcb_type) (getmem (ge,le,Mf,ir,aux,O,op)) (bp,4*Z.of_nat p)=Some Vnull).
  eapply V293_rdy_raw_load;[ | reflexivity | exact Typed].
  apply in_or_app;right. apply in_or_app;left.
  replace (4*Z.of_nat p) with (0+4*Z.of_nat p) by lia.
  apply V293_null_pointer_member;exact Small.
Qed.
Print Assumptions V293_OS_InitTCBList_cleared_tables.
