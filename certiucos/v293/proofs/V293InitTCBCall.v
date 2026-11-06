(* Four real local allocations and release around the already-connected body.
   Raw returned resources are moved back to caller only by memory-only transport. *)
Require Import CertiOS.certiucos.v293.code.V293OSInitTCBCall.
Require Import CertiOS.certiucos.v293.code.V293OSInitTCBList.
Require Import CertiOS.certiucos.v293.code.V293OSMemClr.
Require Import CertiOS.certiucos.v293.code.V293OSInitTCBClear.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBList.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBClear.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293MemClr.
Require Import CertiOS.certiucos.v293.proofs.V293NullBytes.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.basetac.join_lib.
Require Import Coq.Lists.List Lia Sorting.Permutation.
Import ListNotations.
Local Open Scope Z_scope.
Definition V293_tcb_call_locals ix ix_next ptcb1 ptcb2 bi bn b1 b2 : env :=
  set (set (set (set emp ix (bi,Tint8)) ix_next (bn,Tint8))
    ptcb1 (b1,Tptr V293_tcb_type)) ptcb2 (b2,Tptr V293_tcb_type).
Definition V293_tcb_call_blocks (bi bn b1 b2 : block) := [bi;bn;b1;b2].
Definition V293_tcb_call_heads bl bf vl vf : list V293_record_cell :=
  [((bl,0),Tptr V293_tcb_type,vl);((bf,0),Tptr V293_tcb_type,vf)].
Definition V293_tcb_call_result bl bf bt bp frame :=
  V293_tcb_call_heads bl bf Vnull (Vptr (bt,Int.zero))++
  V293_tcb_linked_next bt++V293_tcb_untouched_cells bt 0 13++
  V293_null_pointer_cells bp 0 13++frame.

(* Ascending identifier numbers are an alpha-renaming convention; the runtime
   counter values remain arbitrary Undef before the real body initializes them. *)
Lemma V293_tcb_call_addresses : forall ix ix_next ptcb1 ptcb2 bi bn b1 b2,
  ix<ix_next -> ix_next<ptcb1 -> ptcb1<ptcb2 ->
  getaddr (V293_tcb_call_locals ix ix_next ptcb1 ptcb2 bi bn b1 b2)=
    [(bi,Tint8);(bn,Tint8);(b1,Tptr V293_tcb_type);(b2,Tptr V293_tcb_type)].
Proof.
  intros ix ix_next ptcb1 ptcb2 bi bn b1 b2 A B C.
  unfold V293_tcb_call_locals.
  change (getaddr (EnvMod.set (EnvMod.set (EnvMod.set (EnvMod.set EnvMod.emp ix (bi,Tint8))
    ix_next (bn,Tint8)) ptcb1 (b1,Tptr V293_tcb_type)) ptcb2 (b2,Tptr V293_tcb_type))=
    [(bi,Tint8);(bn,Tint8);(b1,Tptr V293_tcb_type);(b2,Tptr V293_tcb_type)]).
  cbn [EnvMod.set EnvMod.lst EnvMod.set' EnvMod.emp EnvMod.emp' getaddr getaddrlist].
  repeat first [ progress cbn [EnvMod.set' getaddrlist] | match goal with
  | |- context [identspec.blt ?x ?y] =>
    let H:=fresh in assert (H:identspec.blt x y=false) by (unfold identspec.blt;apply Z.ltb_ge;lia);rewrite H
  | |- context [identspec.beq ?x ?y] => rewrite (identspec.neq_beq_false x y) by lia
  end ]. reflexivity.
Qed.

Lemma V293_tcb_fresh_after_alloc : forall M old new tp,
  old<>new -> fresh M new -> fresh (allocb M old 0 (typelen tp)) new.
Proof.
  intros M old new tp Different Fresh a i E [v Read];subst a.
  apply (Fresh (new,i) i eq_refl). exists v.
  rewrite V293_success_allocb_outside in Read by (left;congruence). exact Read.
Qed.

Lemma V293_raw_cells_return_many : forall cells R freed ge le M ir aux O op caller Mf,
  (forall a tp v, In (a,tp,v) cells -> ~In (fst a) freed) ->
  (forall c i, ~In c freed -> get Mf (c,i)=get M (c,i)) ->
  (ge,le,M,ir,aux,O,op) |= V293_rdy_raw_cells cells R ->
  (ge,caller,Mf,ir,aux,O,op) |= V293_rdy_raw_cells cells Atrue.
Proof.
  intros cells R freed ge le M ir aux O op caller Mf Away Frame Owned.
  apply V293_raw_cells_separate in Owned. apply sat_split in Owned.
  destruct Owned as (mp&mr&opart&orest&JM&JO&Part&Rest).
  assert (Sub : Maps.sub mp Mf).
  { unfold addr in *. apply sub_semp;[reflexivity | ]. intros [c i].
    destruct (in_dec Pos.eq_dec c freed) as [Member | Outside].
    - rewrite (V293_raw_cells_absent_block cells ge le mp ir aux opart op c
        ltac:(intros a tp v H E;apply (Away a tp v H);rewrite E;exact Member) Part).
      destruct (get Mf (c,i));exact I.
    - rewrite Frame by exact Outside.
      destruct (get mp (c,i)) as [[permission value] | ] eqn:Cell.
      + destruct (@sub_semp1 (block*offset) (bool*memval) mem memMap mp M (c,i)
          (permission,value) eq_refl ltac:(exists mr;exact JM) Cell) as [Same | [Split Read]].
        * rewrite Same. destruct permission;reflexivity.
        * rewrite Split. destruct permission;cbn in *;try discriminate;reflexivity.
      + destruct (get M (c,i));exact I. }
  destruct Sub as [remainder Joined]. apply V293_raw_cells_join.
  apply sat_split'. exists mp. exists remainder. exists opart. exists orest.
  split;[exact Joined | ]. split;[exact JO | ]. split;[ | exact I].
  eapply V293_raw_cells_environment;[left;reflexivity | exact Part].
Qed.

Theorem V293_OS_InitTCBList_call_return : forall oldtcbs oldprios frame P ks ge caller M
  ir aux O op f clear dest size table priorities list_head free_head ix ix_next ptcb1 ptcb2
  bt bp bl bf bi bn b1 b2 vl vf,
  P f=Some (V293_InitTCBList_function clear table priorities list_head free_head ix ix_next ptcb1 ptcb2) ->
  P clear=Some (V293_MemClr_function dest size) -> dest<>size ->
  ix<ix_next -> ix_next<ptcb1 -> ptcb1<ptcb2 ->
  NoDup (V293_tcb_call_blocks bi bn b1 b2) ->
  fresh M bi -> fresh M bn -> fresh M b1 -> fresh M b2 ->
  V293_tcb_link_env ge (V293_tcb_call_locals ix ix_next ptcb1 ptcb2 bi bn b1 b2)
    table list_head free_head ix ix_next ptcb1 ptcb2 bt bl bf bi bn b1 b2 ->
  get (V293_tcb_call_locals ix ix_next ptcb1 ptcb2 bi bn b1 b2) priorities=None ->
  get ge priorities=Some (bp,V293_tcb_prio_table_type) ->
  length oldtcbs=728%nat -> length oldprios=52%nat ->
  (forall a tp v, In (a,tp,v) (V293_tcb_call_result bl bf bt bp frame) ->
    ~In (fst a) (V293_tcb_call_blocks bi bn b1 b2)) ->
  (ge,caller,M,ir,aux,O,op) |= V293_rdy_raw_cells
    (V293_clr_bytes bt 0 oldtcbs++V293_clr_bytes bp 0 oldprios++
      V293_tcb_call_heads bl bf vl vf++frame) Atrue ->
  exists Ms Mf,
    cstepstar P (curs (scall f nil),(kenil,ks)) (ge,caller,M)
      (curs (sskip None),(kenil,ks)) (ge,caller,Mf) /\
    (ge,V293_tcb_call_locals ix ix_next ptcb1 ptcb2 bi bn b1 b2,Ms,ir,aux,O,op) |=
      V293_rdy_raw_cells (V293_tcb_link_final bi bn b1 b2 bl bf bt)
        (V293_rdy_raw_cells (V293_tcb_untouched_cells bt 0 13)
          (V293_rdy_raw_cells (V293_null_pointer_cells bp 0 13)
            (V293_rdy_raw_cells frame Atrue))) /\
    (ge,caller,Mf,ir,aux,O,op) |= V293_rdy_raw_cells (V293_tcb_call_result bl bf bt bp frame) Atrue /\
    (forall c i, ~In c (V293_tcb_call_blocks bi bn b1 b2) -> get Mf (c,i)=get Ms (c,i)) /\
    (forall c tp k, In (c,tp) [(bi,Tint8);(bn,Tint8);(b1,Tptr V293_tcb_type);(b2,Tptr V293_tcb_type)] ->
      (k<typelen tp)%nat -> get Mf (c,Z.of_nat k)=None).
Proof.
  intros oldtcbs oldprios frame P ks ge caller M ir aux O op f clear dest size table priorities
    list_head free_head ix ix_next ptcb1 ptcb2 bt bp bl bf bi bn b1 b2 vl vf
    Program Clear Names A B C ND Fi Fn F1 F2 Env Prn Prg Lt Lp Away Owned.
  set (le:=V293_tcb_call_locals ix ix_next ptcb1 ptcb2 bi bn b1 b2).
  assert (Frame : (ge,le,M,ir,aux,O,op) |= V293_rdy_raw_cells
    (V293_clr_bytes bt 0 oldtcbs++V293_clr_bytes bp 0 oldprios++V293_tcb_call_heads bl bf vl vf++frame) Atrue).
  { eapply V293_raw_cells_environment;[right;reflexivity | exact Owned]. }
  assert (Distinct : bi<>bn /\ bi<>b1 /\ bi<>b2 /\ bn<>b1 /\ bn<>b2 /\ b1<>b2).
  { unfold V293_tcb_call_blocks in ND.
    inversion ND as [ | xi xsi NI N1];subst. inversion N1 as [ | xn xsn NN N2];subst.
    inversion N2 as [ | xone xsone NOne N3];subst. cbn in NI,NN,NOne. intuition congruence. }
  destruct Distinct as (Din&D11&D12&Dn1&Dn2&D12p).
  set (M1:=allocb M bi 0 (typelen Tint8)).
  set (M2:=allocb M1 bn 0 (typelen Tint8)).
  set (M3:=allocb M2 b1 0 (typelen (Tptr V293_tcb_type))).
  set (M4:=allocb M3 b2 0 (typelen (Tptr V293_tcb_type))).
  assert (Fn1 : fresh M1 bn) by (unfold M1;apply V293_tcb_fresh_after_alloc;assumption).
  assert (F12 : fresh M2 b1).
  { unfold M2,M1. repeat apply V293_tcb_fresh_after_alloc;first [assumption | congruence]. }
  assert (F23 : fresh M3 b2).
  { unfold M3,M2,M1. repeat apply V293_tcb_fresh_after_alloc;first [assumption | congruence]. }
  pose proof (V293_tick_allocate_frame ge le M ir aux O op bi Tint8 _ Fi Frame) as H1.
  pose proof (V293_tick_allocate_frame ge le M1 ir aux O op bn Tint8 _ Fn1 H1) as H2.
  pose proof (V293_tick_allocate_frame ge le M2 ir aux O op b1 (Tptr V293_tcb_type) _ F12 H2) as H3.
  pose proof (V293_tick_allocate_frame ge le M3 ir aux O op b2 (Tptr V293_tcb_type) _ F23 H3) as H4.
  assert (Start : (ge,le,M4,ir,aux,O,op) |= V293_rdy_raw_cells
    (V293_clr_bytes bt 0 oldtcbs++V293_clr_bytes bp 0 oldprios++
      V293_tcb_link_locals bi bn b1 b2 bl bf Vundef Vundef Vundef Vundef vl vf++frame) Atrue).
  { rewrite app_assoc in H4. rewrite V293_raw_cells_append in H4.
    change ((ge,le,M4,ir,aux,O,op) |= V293_rdy_raw_cells
      ([((b2,0),Tptr V293_tcb_type,Vundef);((b1,0),Tptr V293_tcb_type,Vundef);
       ((bn,0),Tint8,Vundef);((bi,0),Tint8,Vundef)])
      (V293_rdy_raw_cells (V293_clr_bytes bt 0 oldtcbs++V293_clr_bytes bp 0 oldprios)
        (V293_rdy_raw_cells (V293_tcb_call_heads bl bf vl vf++frame) Atrue))) in H4.
    apply V293_raw_cells_swap in H4.
    rewrite app_assoc. rewrite V293_raw_cells_append.
    eapply V293_raw_cells_mono;[ | exact H4].
    intros st HS. cbn [V293_tcb_link_locals V293_tcb_call_heads V293_rdy_raw_cells app] in *.
    clear -HS. sep auto. }
  set (body:=sseq (V293_init_tcb_body clear table priorities list_head free_head ix ix_next ptcb1 ptcb2) sret).
  destruct (V293_OS_InitTCBList_body_execution oldtcbs oldprios frame P
    (kseq sret (kcall f body caller ks)) ge le M4 ir aux O op
    clear dest size table priorities list_head free_head ix ix_next ptcb1 ptcb2
    bt bp bl bf bi bn b1 b2 Vundef Vundef Vundef Vundef vl vf
    Clear Names Env Prn Prg Lt Lp Start) as (Ms&Exec&Final).
  assert (Layout : getaddr le=[(bi,Tint8);(bn,Tint8);(b1,Tptr V293_tcb_type);(b2,Tptr V293_tcb_type)]).
  { unfold le. apply V293_tcb_call_addresses;assumption. }
  assert (Writable : forall c tp, In (c,tp) (getaddr le) -> V293_bytes_writable Ms c 0 (typelen tp)).
  { intros c tp Member. rewrite Layout in Member.
    unfold V293_tcb_link_final,V293_tcb_link_locals in Final.
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
          (d2:=dcons ix Tint8 (dcons ix_next Tint8 (dcons ptcb1 (Tptr V293_tcb_type) (dcons ptcb2 (Tptr V293_tcb_type) dnil))));
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
      * eapply V293_raw_cells_return_many with (M:=Ms) (le:=le) (freed:=V293_tcb_call_blocks bi bn b1 b2).
        -- exact Away.
        -- intros c i Outside. apply Preserve. rewrite Layout. exact Outside.
        -- change ((ge,le,Ms,ir,aux,O,op) |= V293_rdy_raw_cells
             ([((bi,0),Tint8,Vint32 (Int.repr 12));((bn,0),Tint8,Vint32 (Int.repr 12));
               ((b1,0),Tptr V293_tcb_type,Vptr (bt,Int.repr 672));
               ((b2,0),Tptr V293_tcb_type,Vptr (bt,Int.repr 672))])
             (V293_rdy_raw_cells (V293_tcb_call_result bl bf bt bp frame) Atrue)) in Final.
           apply V293_raw_cells_swap in Final. exact Final.
      * split.
        -- intros c i Outside. apply Preserve. rewrite Layout. exact Outside.
        -- intros c tp k Member Bound. apply (Removed c tp k);[rewrite Layout;exact Member | exact Bound].
Qed.
Print Assumptions V293_tcb_call_addresses.
Print Assumptions V293_raw_cells_return_many.
Print Assumptions V293_OS_InitTCBList_call_return.
