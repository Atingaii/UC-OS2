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
Require Import CertiOS.certiucos.v293.code.V293OSInitMemChain.
Require Import CertiOS.certiucos.v293.proofs.V293InitFlagChain.
Require Import CertiOS.certiucos.v293.code.V293OSMemInit.
Require Import CertiOS.certiucos.v293.proofs.V293MemInit.
Require Import CertiOS.certiucos.v293.code.V293OSInitQChain.
Require Import CertiOS.certiucos.v293.proofs.V293InitMemChain.
Require Import CertiOS.certiucos.v293.code.V293OSQInit.
Require Import CertiOS.certiucos.v293.proofs.V293QInit.
(* Only the entry memory is a premise; Msix and all four Q-local fresh blocks are constructed. *)
Theorem V293_OSInit_seven_calls : forall slots oldtcbs oldprios oldevents oldflags oldmems oldqueues frame P ks ge caller M ir aux O op
  misc ready tcbs clear dest size group rows prio high top current ri
  bg br bpr bh btop bcur table priorities list_head free_head ix ix_next ptcb1 ptcb2 bt bp bl bf
  vg vlo vhi vp vh vt vc vl vf
  events etable ehead ei en ep1 ep2 ebt ebf evf
  flags ftable fhead fi fn fp1 fp2 fbt fbf fvf
  mems mtable mhead mp mi mbt mbf mvf
  queues qtable qhead qi qn qp1 qp2 qbt qbf qvf,
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
  P mems=Some (V293_MemInit_function clear mtable mhead mp mi) ->
  mp<mi ->
  (forall bp bi, V293_mem_link_env ge (V293_mem_call_locals mp mi bp bi)
    mtable mhead mp mi mbt mbf bp bi) ->
  length oldmems=100%nat ->
  P queues=Some (V293_QInit_function clear qtable qhead qi qn qp1 qp2) ->
  qi<qn -> qn<qp1 -> qp1<qp2 ->
  (forall bi bn b1 b2, V293_q_link_env ge
    (V293_q_call_locals qi qn qp1 qp2 bi bn b1 b2)
    qtable qhead qi qn qp1 qp2 qbt qbf bi bn b1 b2) ->
  length oldqueues=96%nat ->
  (ge,emp,M,ir,aux,O,op) |= V293_init_resources slots false
    (V293_rdy_raw_cells
      (V293_rdy_globals bg br bpr bh btop bcur vg vlo vhi vp vh vt vc++
       V293_clr_bytes bt 0 oldtcbs++V293_clr_bytes bp 0 oldprios++V293_tcb_call_heads bl bf vl vf++
       V293_clr_bytes ebt 0 oldevents++V293_event_call_head ebf evf++
       V293_clr_bytes fbt 0 oldflags++V293_flag_call_head fbf fvf++
       V293_clr_bytes mbt 0 oldmems++V293_mem_call_head mbf mvf++
       V293_clr_bytes qbt 0 oldqueues++V293_q_call_head qbf qvf++frame) Atrue) ->
  exists Msix Mf bi bn b1 b2,
    cstepstar P (curs (V293_init_seven_calls misc ready tcbs events flags mems queues),(kenil,ks)) (ge,caller,M)
      (curs (sskip None),(kenil,ks)) (ge,caller,Mf) /\
    cstepstar P (curs (V293_init_six_calls misc ready tcbs events flags mems),(kenil,kseq (scall queues nil) ks)) (ge,caller,M)
      (curs (sskip None),(kenil,kseq (scall queues nil) ks)) (ge,caller,Msix) /\
    cstepstar P (curs (scall queues nil),(kenil,ks)) (ge,caller,Msix)
      (curs (sskip None),(kenil,ks)) (ge,caller,Mf) /\
    fresh Msix bi /\ fresh Msix bn /\ fresh Msix b1 /\ fresh Msix b2 /\
    NoDup (V293_q_call_blocks bi bn b1 b2) /\
    (ge,caller,Mf,ir,aux,O,op) |= V293_rdy_raw_cells
      (V293_q_call_result qbf qbt
       (V293_mem_call_result mbf mbt
        (V293_flag_call_result fbf fbt
         (V293_event_call_result ebf ebt
          (V293_tcb_call_result bl bf bt bp
           (V293_rdy_globals bg br bpr bh btop bcur
            (Vint32 Int.zero) (Vint32 Int.zero) (Vint32 Int.zero) (Vint32 Int.zero) (Vint32 Int.zero) Vnull Vnull++
            V293_misc_zero_cells slots++frame)))))) Atrue /\
    (forall c tp k, In (c,tp) [(bi,Tint16);(bn,Tint16);(b1,Tptr V293_q_type);(b2,Tptr V293_q_type)] ->
      (k<typelen tp)%nat -> get Mf (c,Z.of_nat k)=None).
Proof.
  intros slots oldtcbs oldprios oldevents oldflags oldmems oldqueues frame P ks ge caller M ir aux O op
    misc ready tcbs clear dest size group rows prio high top current ri
    bg br bpr bh btop bcur table priorities list_head free_head ix ix_next ptcb1 ptcb2 bt bp bl bf
    vg vlo vhi vp vh vt vc vl vf events etable ehead ei en ep1 ep2 ebt ebf evf
    flags ftable fhead fi fn fp1 fp2 fbt fbf fvf
    mems mtable mhead mp mi mbt mbf mvf
    queues qtable qhead qi qn qp1 qp2 qbt qbf qvf
    Scalar Misc Ready TCB Clear DS IX IN PN REnv CEnv NPrio GPrio LT LP
    Event EI EN EP EEnv LE Flag FI FN FP FEnv LF Mem MP MEnv LM
    Queue QI QN QP QEnv LQ Owned.
  set (qold:=V293_clr_bytes qbt 0 oldqueues++V293_q_call_head qbf qvf).
  destruct (V293_OSInit_six_calls slots oldtcbs oldprios oldevents oldflags oldmems (qold++frame) P
    (kseq (scall queues nil) ks) ge caller M ir aux O op
    misc ready tcbs clear dest size group rows prio high top current ri
    bg br bpr bh btop bcur table priorities list_head free_head ix ix_next ptcb1 ptcb2 bt bp bl bf
    vg vlo vhi vp vh vt vc vl vf events etable ehead ei en ep1 ep2 ebt ebf evf
    flags ftable fhead fi fn fp1 fp2 fbt fbf fvf
    mems mtable mhead mp mi mbt mbf mvf
    Scalar Misc Ready TCB Clear DS IX IN PN REnv CEnv NPrio GPrio LT LP
    Event EI EN EP EEnv LE Flag FI FN FP FEnv LF Mem MP MEnv LM)
    as (Mflag&Msix&mpl&mil&Prefix&FiveExec&MemExec&MFp&MFi&MDistinct&SixFinal&MRemoved).
  - unfold qold. repeat rewrite <-app_assoc. exact Owned.
  - set (rz:=V293_rdy_globals bg br bpr bh btop bcur
      (Vint32 Int.zero) (Vint32 Int.zero) (Vint32 Int.zero) (Vint32 Int.zero) (Vint32 Int.zero) Vnull Vnull).
    set (mz:=V293_misc_zero_cells slots).
    set (before:=V293_mem_call_result mbf mbt (V293_flag_call_result fbf fbt
      (V293_event_call_result ebf ebt (V293_tcb_call_result bl bf bt bp (rz++mz))))).
    set (rest:=V293_mem_call_result mbf mbt (V293_flag_call_result fbf fbt
      (V293_event_call_result ebf ebt (V293_tcb_call_result bl bf bt bp (rz++mz++frame))))).
    assert (QueueStart : (ge,caller,Msix,ir,aux,O,op) |= V293_rdy_raw_cells (qold++rest) Atrue).
    { assert (H : (ge,caller,Msix,ir,aux,O,op) |=
        V293_rdy_raw_cells before (V293_rdy_raw_cells qold (V293_rdy_raw_cells frame Atrue))).
      { repeat rewrite <-V293_raw_cells_append.
        unfold before,rz,mz,V293_mem_call_result,V293_flag_call_result,V293_event_call_result,V293_tcb_call_result.
        repeat rewrite <-app_assoc in *;exact SixFinal. }
      apply V293_raw_cells_swap in H.
      repeat rewrite <-V293_raw_cells_append in H.
      unfold rest,before,V293_mem_call_result,V293_flag_call_result,V293_event_call_result,V293_tcb_call_result in *.
      repeat rewrite <-app_assoc in *;exact H. }
    destruct (V293_init_fresh_four Msix (V293_q_call_result qbf qbt rest))
      as (bi&bn&b1&b2&ND&Fbi&Fbn&Fb1&Fb2&Away).
    change (NoDup (V293_q_call_blocks bi bn b1 b2)) in ND.
    destruct (V293_OS_QInit_call_return oldqueues rest P ks ge caller Msix ir aux O op
      queues clear dest size qtable qhead qi qn qp1 qp2 qbt qbf bi bn b1 b2 qvf
      Queue Clear DS QI QN QP ND Fbi Fbn Fb1 Fb2 (QEnv bi bn b1 b2) LQ)
      as (Ms&Mf&QueueExec&QueueFinal&Returned&Preserve&Removed).
    + exact Away.
    + unfold qold in QueueStart. repeat rewrite <-app_assoc in QueueStart;exact QueueStart.
    + exists Msix. exists Mf. exists bi. exists bn. exists b1. exists b2.
      split.
      * unfold V293_init_seven_calls.
        eapply c_stepstarn. { eapply stmt_step;[reflexivity | apply sseq_step]. }
        eapply V293_cstepstar_trans;[exact Prefix | ].
        eapply c_stepstarn. { eapply stmt_step;[reflexivity | constructor]. }
        exact QueueExec.
      * split;[exact Prefix | ]. split;[exact QueueExec | ].
        split;[exact Fbi | ]. split;[exact Fbn | ]. split;[exact Fb1 | ]. split;[exact Fb2 | ].
        split;[exact ND | ]. split;[exact Returned | exact Removed].
Qed.
Print Assumptions V293_OSInit_seven_calls.
