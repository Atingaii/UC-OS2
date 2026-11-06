(* Same-program, same-memory composition; not full OSInit or all executions. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSInitChain.
Require Import CertiOS.certiucos.v293.code.V293OSInitMisc.
Require Import CertiOS.certiucos.v293.code.V293OSInitRdyList.
Require Import CertiOS.certiucos.v293.code.V293OSInitTCBCall.
Require Import CertiOS.certiucos.v293.code.V293OSMemClr.
Require Import CertiOS.certiucos.v293.code.V293OSInitTCBClear.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.proofs.V293InitMisc.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBClear.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBList.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBCall.
Require Import CertiOS.certiucos.v293.proofs.V293MemClr.
Require Import CertiOS.certiucos.v293.proofs.V293NullBytes.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.framework.proof.memory_bound.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope Z_scope.
Definition V293_misc_zero_cells slots : list V293_record_cell :=
  map (fun d=>((init_block d,0),init_type d,Vint32 Int.zero)) slots.
Lemma V293_raw_cells_absorb : forall cells R,
  R ** V293_rdy_raw_cells cells Atrue ==> V293_rdy_raw_cells cells Atrue.
Proof.
  induction cells as [ | [[a tp] v] tail IH];intros R s H;cbn [V293_rdy_raw_cells] in *.
  - exact I.
  - assert (K : s |= Amapsto a tp true v ** (R ** V293_rdy_raw_cells tail Atrue)) by (clear -H;sep auto).
    eapply astar_mono;[intros st HS;exact HS | apply IH | exact K].
Qed.
Lemma V293_init_resources_raw : forall slots tail,
  V293_init_resources slots true (V293_rdy_raw_cells tail Atrue) ==>
  V293_rdy_raw_cells (V293_misc_zero_cells slots++tail) Atrue.
Proof.
  induction slots as [ | d ds IH];intros tail s H;cbn [V293_init_resources V293_misc_zero_cells map app V293_rdy_raw_cells] in *.
  - exact H.
  - assert (K : s |= (V293_init_binding d ** V293_init_memory d true) **
      V293_rdy_raw_cells (V293_misc_zero_cells ds++tail) Atrue).
    { eapply astar_mono;[intros st HS;exact HS | apply IH | exact H]. }
    cbn [V293_init_memory] in K.
    assert (F : s |= V293_init_binding d ** V293_rdy_raw_cells
      (((init_block d,0),init_type d,Vint32 Int.zero)::(V293_misc_zero_cells ds++tail)) Atrue)
      by (cbn [V293_rdy_raw_cells];clear -K;sep auto).
    apply V293_raw_cells_absorb in F. exact F.
Qed.
Lemma V293_init_slots_call : forall slots P ks R ge caller M ir aux O op f,
  Forall V293_init_scalar slots ->
  P f=Some (Tvoid,dnil,dnil,sseq (V293_init_program slots) sret) ->
  (ge,emp,M,ir,aux,O,op) |= V293_init_resources slots false R ->
  exists Mf,
  cstepstar P (curs (scall f nil),(kenil,ks)) (ge,caller,M)
    (curs (sskip None),(kenil,ks)) (ge,caller,Mf) /\
  (ge,emp,Mf,ir,aux,O,op) |= V293_init_resources slots true R.
Proof.
  intros slots P ks R ge caller M ir aux O op f Scalar Program Owned.
  set (body:=sseq (V293_init_program slots) sret).
  destruct (V293_init_sequence_execution slots P (kseq sret (kcall f body caller ks)) R
    ge emp M ir aux O op Scalar Owned) as (Mf&Exec&Final).
  exists Mf. split;[ | exact Final].
  eapply c_stepstarn. { eapply stmt_step;[reflexivity | apply snpcall_step]. }
  eapply c_stepstarn. { eapply stmt_step;[reflexivity | ]. eapply sfexec_step with (d1:=dnil) (d2:=dnil);
    [reflexivity | reflexivity | exact Program | exact I | reflexivity]. }
  eapply c_stepstarn. { eapply stmt_step;[reflexivity | apply sallocend_step]. }
  eapply c_stepstarn. { eapply stmt_step;[reflexivity | apply sseq_step]. }
  eapply V293_cstepstar_trans;[exact Exec | ].
  eapply c_stepstarn. { eapply stmt_step;[reflexivity | constructor]. }
  eapply c_stepstarn. { eapply stmt_step;[reflexivity | ]. eapply sret_step;reflexivity. }
  eapply c_stepstarn. { eapply stmt_step;[reflexivity | ]. eapply sfreeend_step;reflexivity. }
  apply c_stepstar0.
Qed.
Definition V293_cells_upper (cells : list V293_record_cell) : positive :=
  fold_right Pos.max 1%positive (map (fun c=>fst (fst (fst c))) cells).
Lemma V293_cells_upper_bound : forall cells a tp v,
  In (a,tp,v) cells -> (fst a<=V293_cells_upper cells)%positive.
Proof.
  induction cells as [ | [[b t] w] tail IH];intros a tp v H;[contradiction | ].
  destruct H as [E | H].
  - inversion E;subst. cbn [V293_cells_upper map fold_right]. apply Pos.le_max_l.
  - cbn [V293_cells_upper map fold_right]. eapply Pos.le_trans;[eapply IH;exact H | apply Pos.le_max_r].
Qed.
(* Allocation choices are constructed AFTER the preceding call, from the actual
   bounded memory and finite returned footprint, not assumed at its output. *)
Lemma V293_init_fresh_four : forall M (cells : list V293_record_cell),
  exists bi bn b1 b2,
    NoDup (V293_tcb_call_blocks bi bn b1 b2) /\
    fresh M bi /\ fresh M bn /\ fresh M b1 /\ fresh M b2 /\
    (forall a tp v, In (a,tp,v) cells -> ~In (fst a) (V293_tcb_call_blocks bi bn b1 b2)).
Proof.
  intros M cells. destruct (HalfPermMap.bounded M) as [bound Below].
  set (base:=Pos.max bound (Pos.succ (V293_cells_upper cells))).
  exists base. exists (Pos.succ base). exists (Pos.succ (Pos.succ base)). exists (Pos.succ (Pos.succ (Pos.succ base))).
  assert (LT : (V293_cells_upper cells<base)%positive).
  { unfold base. eapply Pos.lt_le_trans;[apply Pos.lt_succ_diag_r | apply Pos.le_max_r]. }
  assert (Fresh : forall b, (base<=b)%positive -> fresh M b).
  { intros b B l i E [v Read];subst l. apply (Pos.lt_irrefl b).
    eapply Pos.lt_le_trans;[eapply Below;exact Read | ].
    eapply Pos.le_trans;[unfold base;apply Pos.le_max_l | exact B]. }
  split.
  - unfold V293_tcb_call_blocks. repeat constructor;cbn;intuition lia.
  - repeat split;try (apply Fresh;lia).
    intros a tp v Member Inside. pose proof (V293_cells_upper_bound cells a tp v Member) as Bound.
    unfold V293_tcb_call_blocks in Inside. cbn in Inside. destruct Inside as [E | [E | [E | [E | E]]]];try contradiction.
    all: apply (Pos.lt_irrefl (fst a));eapply Pos.le_lt_trans;[exact Bound | ];
      eapply Pos.lt_le_trans;[exact LT | ];rewrite <-E;lia.
Qed.

(* Generic scalar slots are instantiated by the literal configured ten-field
   Misc function in the independent probe. No intermediate state is a premise. *)
Theorem V293_OSInit_three_calls : forall slots oldtcbs oldprios frame P ks ge caller M ir aux O op
  misc ready tcbs clear dest size group rows prio high top current ri
  bg br bpr bh btop bcur table priorities list_head free_head ix ix_next ptcb1 ptcb2 bt bp bl bf
  vg vlo vhi vp vh vt vc vl vf,
  Forall V293_init_scalar slots ->
  P misc=Some (Tvoid,dnil,dnil,sseq (V293_init_program slots) sret) ->
  P ready=Some (V293_InitRdyList_function group rows prio high top current ri) ->
  P tcbs=Some (V293_InitTCBList_function clear table priorities list_head free_head ix ix_next ptcb1 ptcb2) ->
  P clear=Some (V293_MemClr_function dest size) -> dest<>size ->
  ix<ix_next -> ix_next<ptcb1 -> ptcb1<ptcb2 ->
  (forall bi, V293_rdy_env ge (V293_rdy_locals ri bi)
    group rows prio high top current ri bg br bpr bh btop bcur bi) ->
  (forall bi bn b1 b2, V293_tcb_link_env ge (V293_tcb_call_locals ix ix_next ptcb1 ptcb2 bi bn b1 b2)
    table list_head free_head ix ix_next ptcb1 ptcb2 bt bl bf bi bn b1 b2) ->
  (forall bi bn b1 b2, get (V293_tcb_call_locals ix ix_next ptcb1 ptcb2 bi bn b1 b2) priorities=None) ->
  get ge priorities=Some (bp,V293_tcb_prio_table_type) ->
  length oldtcbs=728%nat -> length oldprios=52%nat ->
  (ge,emp,M,ir,aux,O,op) |= V293_init_resources slots false
    (V293_rdy_raw_cells
      (V293_rdy_globals bg br bpr bh btop bcur vg vlo vhi vp vh vt vc++
       V293_clr_bytes bt 0 oldtcbs++V293_clr_bytes bp 0 oldprios++V293_tcb_call_heads bl bf vl vf++frame) Atrue) ->
  exists Mmisc Mrdy Mf bri bi bn b1 b2,
    cstepstar P (curs (V293_init_three_calls misc ready tcbs),(kenil,ks)) (ge,caller,M)
      (curs (sskip None),(kenil,ks)) (ge,caller,Mf) /\
    cstepstar P (curs (scall misc nil),(kenil,kseq (sseq (scall ready nil) (scall tcbs nil)) ks)) (ge,caller,M)
      (curs (sskip None),(kenil,kseq (sseq (scall ready nil) (scall tcbs nil)) ks)) (ge,caller,Mmisc) /\
    cstepstar P (curs (scall ready nil),(kenil,kseq (scall tcbs nil) ks)) (ge,caller,Mmisc)
      (curs (sskip None),(kenil,kseq (scall tcbs nil) ks)) (ge,caller,Mrdy) /\
    cstepstar P (curs (scall tcbs nil),(kenil,ks)) (ge,caller,Mrdy)
      (curs (sskip None),(kenil,ks)) (ge,caller,Mf) /\
    (ge,caller,Mf,ir,aux,O,op) |= V293_rdy_raw_cells
      (V293_tcb_call_result bl bf bt bp
        (V293_rdy_globals bg br bpr bh btop bcur
          (Vint32 Int.zero) (Vint32 Int.zero) (Vint32 Int.zero) (Vint32 Int.zero) (Vint32 Int.zero) Vnull Vnull++
         V293_misc_zero_cells slots++frame)) Atrue /\
    get Mrdy (bri,0)=None /\
    (forall c tp k, In (c,tp) [(bi,Tint8);(bn,Tint8);(b1,Tptr V293_tcb_type);(b2,Tptr V293_tcb_type)] ->
      (k<typelen tp)%nat -> get Mf (c,Z.of_nat k)=None).
Proof.
  intros slots oldtcbs oldprios frame P ks ge caller M ir aux O op
    misc ready tcbs clear dest size group rows prio high top current ri
    bg br bpr bh btop bcur table priorities list_head free_head ix ix_next ptcb1 ptcb2 bt bp bl bf
    vg vlo vhi vp vh vt vc vl vf Scalar Misc Ready TCB Clear DS IX IN PN REnv CEnv NPrio GPrio LT LP Owned.
  set (rg:=V293_rdy_globals bg br bpr bh btop bcur vg vlo vhi vp vh vt vc).
  set (rz:=V293_rdy_globals bg br bpr bh btop bcur
    (Vint32 Int.zero) (Vint32 Int.zero) (Vint32 Int.zero) (Vint32 Int.zero) (Vint32 Int.zero) Vnull Vnull).
  set (tz:=V293_clr_bytes bt 0 oldtcbs++V293_clr_bytes bp 0 oldprios++V293_tcb_call_heads bl bf vl vf).
  set (mz:=V293_misc_zero_cells slots).
  assert (Initial : (ge,emp,M,ir,aux,O,op) |= V293_init_resources slots false (V293_rdy_raw_cells (rg++tz++frame) Atrue)).
  { unfold rg,tz. repeat rewrite <-app_assoc. exact Owned. }
  clear Owned;rename Initial into Owned.
  destruct (V293_init_slots_call slots P (kseq (sseq (scall ready nil) (scall tcbs nil)) ks) _
    ge caller M ir aux O op misc Scalar Misc Owned) as (Mmisc&MiscExec&MiscFinal).
  apply V293_init_resources_raw in MiscFinal.
  assert (ReadyStart : (ge,V293_rdy_locals ri 1%positive,Mmisc,ir,aux,O,op) |=
    V293_rdy_raw_cells rg (V293_rdy_raw_cells (mz++tz++frame) Atrue)).
  { rewrite <-V293_raw_cells_append.
    eapply V293_raw_cells_environment;[right;reflexivity | ].
    repeat rewrite V293_raw_cells_append in *. apply V293_raw_cells_swap in MiscFinal. exact MiscFinal. }
  destruct (V293_init_fresh_four Mmisc (rz++mz++tz++frame)) as (bri&unused1&unused2&unused3&ND&Fresh&F1&F2&F3&AwayReady).
  assert (StartR : (ge,V293_rdy_locals ri bri,Mmisc,ir,aux,O,op) |=
    V293_rdy_raw_cells rg (V293_rdy_raw_cells (mz++tz++frame) Atrue)).
  { repeat rewrite <-V293_raw_cells_append in *. eapply V293_raw_cells_environment;[right;reflexivity | exact ReadyStart]. }
  destruct (V293_OS_InitRdyList_call_return P (kseq (scall tcbs nil) ks) ge caller Mmisc ir aux O op
    (V293_rdy_raw_cells (mz++tz++frame) Atrue) ready
    group rows prio high top current ri bg br bpr bh btop bcur bri vg vlo vhi vp vh vt vc
    Ready Fresh (REnv bri) StartR) as (MsR&Mrdy&ReadyExec&ReadyFinal&ReadyPreserve&ReadyRemoved).
  assert (ReadyOwned : (ge,caller,Mrdy,ir,aux,O,op) |= V293_rdy_raw_cells (rz++mz++tz++frame) Atrue).
  { eapply V293_raw_cells_return_many with (freed:=([bri])) (M:=MsR) (le:=V293_rdy_locals ri bri)
        (R:=V293_rdy_raw_cells ([((bri,0),Tint8,Vint32 (Int.repr 2))]) Atrue).
    - intros a tp v Member [Eq | Bad];[ | contradiction].
      apply (AwayReady a tp v Member). unfold V293_tcb_call_blocks. left;exact Eq.
    - intros c i Outside. apply ReadyPreserve. intro E;apply Outside;left;symmetry;exact E.
    - change ((ge,V293_rdy_locals ri bri,MsR,ir,aux,O,op) |=
        V293_rdy_raw_cells (rz++[((bri,0),Tint8,Vint32 (Int.repr 2))])
          (V293_rdy_raw_cells (mz++tz++frame) Atrue)) in ReadyFinal.
      rewrite V293_raw_cells_append in ReadyFinal.
      apply (V293_raw_cells_mono rz _ _
        (V293_raw_cells_swap ([((bri,0),Tint8,Vint32 (Int.repr 2))]) (mz++tz++frame) Atrue)) in ReadyFinal.
      rewrite <-V293_raw_cells_append in ReadyFinal. exact ReadyFinal. }
  set (rest:=rz++mz++frame).
  set (result:=V293_tcb_call_result bl bf bt bp rest).
  destruct (V293_init_fresh_four Mrdy result)
    as (bi&bn&b1&b2&TND&Fi&Fn&Fb1&Fb2&AwayTCB).
  assert (TCBStart : (ge,caller,Mrdy,ir,aux,O,op) |= V293_rdy_raw_cells (tz++rest) Atrue).
  { unfold rest. repeat rewrite V293_raw_cells_append in *.
    apply (V293_raw_cells_mono rz _ _ (V293_raw_cells_swap mz tz _)) in ReadyOwned.
    apply (V293_raw_cells_swap rz tz _) in ReadyOwned. exact ReadyOwned. }
  destruct (V293_OS_InitTCBList_call_return oldtcbs oldprios rest P ks ge caller Mrdy ir aux O op
    tcbs clear dest size table priorities list_head free_head ix ix_next ptcb1 ptcb2 bt bp bl bf bi bn b1 b2 vl vf
    TCB Clear DS IX IN PN TND Fi Fn Fb1 Fb2 (CEnv bi bn b1 b2) (NPrio bi bn b1 b2) GPrio LT LP)
      as (MsT&Mf&TCBExec&TCBFinal&Returned&TCBPreserve&Removed).
  - intros a tp v Member. exact (AwayTCB a tp v Member).
  - unfold tz in TCBStart. repeat rewrite <-app_assoc in TCBStart. exact TCBStart.
  - exists Mmisc. exists Mrdy. exists Mf. exists bri. exists bi. exists bn. exists b1. exists b2.
    split.
    + unfold V293_init_three_calls. eapply c_stepstarn. { eapply stmt_step;[reflexivity | apply sseq_step]. }
      eapply V293_cstepstar_trans;[exact MiscExec | ].
      eapply c_stepstarn. { eapply stmt_step;[reflexivity | constructor]. }
      eapply c_stepstarn. { eapply stmt_step;[reflexivity | apply sseq_step]. }
      eapply V293_cstepstar_trans;[exact ReadyExec | ].
      eapply c_stepstarn. { eapply stmt_step;[reflexivity | constructor]. }
      exact TCBExec.
    + split;[exact MiscExec | ]. split;[exact ReadyExec | ]. split;[exact TCBExec | ].
      split;[exact Returned | ]. split;[ | exact Removed].
      exact ReadyRemoved.
Qed.
Print Assumptions V293_OSInit_three_calls.
