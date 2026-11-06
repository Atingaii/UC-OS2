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
Require Import CertiOS.certiucos.v293.code.V293OSInitEventChain.
Require Import CertiOS.certiucos.v293.code.V293OSInitEventList.
Require Import CertiOS.certiucos.v293.proofs.V293InitChain.
Require Import CertiOS.certiucos.v293.proofs.V293InitEventList.

Require Import CertiOS.certiucos.v293.code.V293OSInitFlagChain.
Require Import CertiOS.certiucos.v293.proofs.V293InitEventChain.
Require Import CertiOS.certiucos.v293.code.V293OSFlagInit.
Require Import CertiOS.certiucos.v293.proofs.V293FlagInit.
(* Only the entry memory is a premise; Mtcb and all four Flag-local fresh blocks are constructed. *)
Theorem V293_OSInit_five_calls : forall slots oldtcbs oldprios oldevents oldflags frame P ks ge caller M ir aux O op
  misc ready tcbs clear dest size group rows prio high top current ri
  bg br bpr bh btop bcur table priorities list_head free_head ix ix_next ptcb1 ptcb2 bt bp bl bf
  vg vlo vhi vp vh vt vc vl vf
  events etable ehead ei en ep1 ep2 ebt ebf evf
  flags ftable fhead fi fn fp1 fp2 fbt fbf fvf,
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
  P events=Some (V293_InitEventList_function clear etable ehead ei en ep1 ep2) ->
  ei<en -> en<ep1 -> ep1<ep2 ->
  (forall bi bn b1 b2, V293_event_link_env ge
    (V293_event_call_locals ei en ep1 ep2 bi bn b1 b2)
    etable ehead ei en ep1 ep2 ebt ebf bi bn b1 b2) ->
  length oldevents=32%nat ->
  P flags=Some (V293_FlagInit_function clear ftable fhead fi fn fp1 fp2) ->
  fi<fn -> fn<fp1 -> fp1<fp2 ->
  (forall bi bn b1 b2, V293_flag_link_env ge
    (V293_flag_call_locals fi fn fp1 fp2 bi bn b1 b2)
    ftable fhead fi fn fp1 fp2 fbt fbf bi bn b1 b2) ->
  length oldflags=60%nat ->
  (ge,emp,M,ir,aux,O,op) |= V293_init_resources slots false
    (V293_rdy_raw_cells
      (V293_rdy_globals bg br bpr bh btop bcur vg vlo vhi vp vh vt vc++
       V293_clr_bytes bt 0 oldtcbs++V293_clr_bytes bp 0 oldprios++V293_tcb_call_heads bl bf vl vf++
       V293_clr_bytes ebt 0 oldevents++V293_event_call_head ebf evf++
       V293_clr_bytes fbt 0 oldflags++V293_flag_call_head fbf fvf++frame) Atrue) ->
  exists Mevent Mf bi bn b1 b2,
    cstepstar P (curs (V293_init_five_calls misc ready tcbs events flags),(kenil,ks)) (ge,caller,M)
      (curs (sskip None),(kenil,ks)) (ge,caller,Mf) /\
    cstepstar P (curs (V293_init_four_calls misc ready tcbs events),(kenil,kseq (scall flags nil) ks)) (ge,caller,M)
      (curs (sskip None),(kenil,kseq (scall flags nil) ks)) (ge,caller,Mevent) /\
    cstepstar P (curs (scall flags nil),(kenil,ks)) (ge,caller,Mevent)
      (curs (sskip None),(kenil,ks)) (ge,caller,Mf) /\
    fresh Mevent bi /\ fresh Mevent bn /\ fresh Mevent b1 /\ fresh Mevent b2 /\
    (ge,caller,Mf,ir,aux,O,op) |= V293_rdy_raw_cells
      (V293_flag_call_result fbf fbt
       (V293_event_call_result ebf ebt
        (V293_tcb_call_result bl bf bt bp
          (V293_rdy_globals bg br bpr bh btop bcur
            (Vint32 Int.zero) (Vint32 Int.zero) (Vint32 Int.zero) (Vint32 Int.zero) (Vint32 Int.zero) Vnull Vnull++
           V293_misc_zero_cells slots++frame)))) Atrue /\
    (forall c tp k, In (c,tp) [(bi,Tint16);(bn,Tint16);(b1,Tptr V293_flag_type);(b2,Tptr V293_flag_type)] ->
      (k<typelen tp)%nat -> get Mf (c,Z.of_nat k)=None).
Proof.
  intros slots oldtcbs oldprios oldevents oldflags frame P ks ge caller M ir aux O op
    misc ready tcbs clear dest size group rows prio high top current ri
    bg br bpr bh btop bcur table priorities list_head free_head ix ix_next ptcb1 ptcb2 bt bp bl bf
    vg vlo vhi vp vh vt vc vl vf events etable ehead ei en ep1 ep2 ebt ebf evf
    flags ftable fhead fi fn fp1 fp2 fbt fbf fvf
    Scalar Misc Ready TCB Clear DS IX IN PN REnv CEnv NPrio GPrio LT LP
    Event EI EN EP EEnv LE Flag FI FN FP FEnv LF Owned.
  set (flold:=V293_clr_bytes fbt 0 oldflags++V293_flag_call_head fbf fvf).
  destruct (V293_OSInit_four_calls slots oldtcbs oldprios oldevents (flold++frame) P
    (kseq (scall flags nil) ks) ge caller M ir aux O op
    misc ready tcbs clear dest size group rows prio high top current ri
    bg br bpr bh btop bcur table priorities list_head free_head ix ix_next ptcb1 ptcb2 bt bp bl bf
    vg vlo vhi vp vh vt vc vl vf events etable ehead ei en ep1 ep2 ebt ebf evf
    Scalar Misc Ready TCB Clear DS IX IN PN REnv CEnv NPrio GPrio LT LP Event EI EN EP EEnv LE)
    as (Mtcb&Mevent&ebi&ebn&eb1&eb2&Prefix&ThreeExec&EventExec&EFi&EFn&EF1&EF2&EventFinal&ERemoved).
  - unfold flold. repeat rewrite <-app_assoc. exact Owned.
  - set (rz:=V293_rdy_globals bg br bpr bh btop bcur
      (Vint32 Int.zero) (Vint32 Int.zero) (Vint32 Int.zero) (Vint32 Int.zero) (Vint32 Int.zero) Vnull Vnull).
    set (mz:=V293_misc_zero_cells slots).
    set (before:=V293_event_call_result ebf ebt (V293_tcb_call_result bl bf bt bp (rz++mz))).
    set (rest:=V293_event_call_result ebf ebt (V293_tcb_call_result bl bf bt bp (rz++mz++frame))).
    assert (FlagStart : (ge,caller,Mevent,ir,aux,O,op) |= V293_rdy_raw_cells (flold++rest) Atrue).
    { assert (H : (ge,caller,Mevent,ir,aux,O,op) |=
        V293_rdy_raw_cells before (V293_rdy_raw_cells flold (V293_rdy_raw_cells frame Atrue))).
      { repeat rewrite <-V293_raw_cells_append.
        unfold before,rz,mz,V293_event_call_result,V293_tcb_call_result.
        repeat rewrite <-app_assoc in *;exact EventFinal. }
      apply V293_raw_cells_swap in H.
      repeat rewrite <-V293_raw_cells_append in H.
      unfold rest,before,V293_event_call_result,V293_tcb_call_result in *.
      repeat rewrite <-app_assoc in *;exact H. }
    destruct (V293_init_fresh_four Mevent (V293_flag_call_result fbf fbt rest))
      as (bi&bn&b1&b2&ND&Fbi&Fbn&Fb1&Fb2&Away).
    change (NoDup (V293_flag_call_blocks bi bn b1 b2)) in ND.
    destruct (V293_OS_FlagInit_call_return oldflags rest P ks ge caller Mevent ir aux O op
      flags clear dest size ftable fhead fi fn fp1 fp2 fbt fbf bi bn b1 b2 fvf
      Flag Clear DS FI FN FP ND Fbi Fbn Fb1 Fb2 (FEnv bi bn b1 b2) LF)
      as (Ms&Mf&FlagExec&FlagFinal&Returned&Preserve&Removed).
    + exact Away.
    + unfold flold in FlagStart. repeat rewrite <-app_assoc in FlagStart;exact FlagStart.
    + exists Mevent. exists Mf. exists bi. exists bn. exists b1. exists b2.
      split.
      * unfold V293_init_five_calls.
        eapply c_stepstarn. { eapply stmt_step;[reflexivity | apply sseq_step]. }
        eapply V293_cstepstar_trans;[exact Prefix | ].
        eapply c_stepstarn. { eapply stmt_step;[reflexivity | constructor]. }
        exact FlagExec.
      * split;[exact Prefix | ]. split;[exact FlagExec | ].
        split;[exact Fbi | ]. split;[exact Fbn | ]. split;[exact Fb1 | ]. split;[exact Fb2 | ].
        split;[exact Returned | exact Removed].
Qed.
Print Assumptions V293_OSInit_five_calls.
