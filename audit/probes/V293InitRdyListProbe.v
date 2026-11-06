(* Independent finite initial heap; no assumption of an already running task. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSInitRdyList.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.
Definition RdyGE : env := set (set (set (set (set (set emp
  11%Z (81%positive,Tint8)) 12%Z (82%positive,Tarray Tint8 2))
  13%Z (83%positive,Tint8)) 14%Z (84%positive,Tint8))
  15%Z (85%positive,Tptr V293_tcb_type)) 16%Z (86%positive,Tptr V293_tcb_type).
Definition RdyLE := V293_rdy_locals 17%Z 87%positive.
Definition RdyState M := V293_wstate RdyGE RdyLE M.
Definition RdyBytes a tp v := V293_encoded_memory (fst a) (snd a) true (encode_val tp v).
Definition RdyFrame := Amapsto (99%positive,0%Z) Tint32 true (Vint32 (Int.repr 123)).
Fixpoint RdyMem (cells : list (addr * type * val)) : mem :=
  match cells with
  | [] => RdyBytes (99%positive,0%Z) Tint32 (Vint32 (Int.repr 123))
  | (a,tp,v)::tail => merge (RdyBytes a tp v) (RdyMem tail)
  end.
Definition RdyCells : list (addr * type * val) :=
  [((81%positive,0%Z),Tint8,Vint32 (Int.repr 7));
   ((82%positive,0%Z),Tint8,Vint32 (Int.repr 3));
   ((82%positive,1%Z),Tint8,Vundef);
   ((83%positive,0%Z),Tint8,Vint32 (Int.repr 5));
   ((84%positive,0%Z),Tint8,Vint32 (Int.repr 9));
   ((85%positive,0%Z),Tptr V293_tcb_type,Vptr (91%positive,Int.zero));
   ((86%positive,0%Z),Tptr V293_tcb_type,Vptr (92%positive,Int.zero))].
Ltac RdyApart b :=
  apply map_join_merge;apply map_disjoint;intros [other off];
  destruct (Pos.eq_dec other b);[subst other;right;left | left];
  unfold RdyBytes;cbn [fst snd];
  repeat rewrite map_merge_semp by reflexivity;
  repeat rewrite V293_encoded_memory_outside by (left;congruence);reflexivity.
Lemma RdyEnvironment : V293_rdy_env RdyGE RdyLE 11%Z 12%Z 13%Z 14%Z 15%Z 16%Z 17%Z
  81%positive 82%positive 83%positive 84%positive 85%positive 86%positive 87%positive.
Proof. vm_compute;repeat split;reflexivity. Qed.
Lemma RdyFresh : fresh (RdyMem RdyCells) 87%positive.
Proof.
  intros l off -> [v E]. unfold RdyCells in E. cbn [RdyMem] in E. unfold RdyBytes in E.
  repeat rewrite map_merge_semp in E by reflexivity.
  repeat rewrite V293_encoded_memory_outside in E by (left;discriminate). discriminate.
Qed.
Theorem RdyLiteralEntry : RdyState (RdyMem RdyCells) |= V293_rdy_raw_cells
  (V293_rdy_globals 81%positive 82%positive 83%positive 84%positive 85%positive 86%positive
    (Vint32 (Int.repr 7)) (Vint32 (Int.repr 3)) Vundef (Vint32 (Int.repr 5))
    (Vint32 (Int.repr 9)) (Vptr (91%positive,Int.zero)) (Vptr (92%positive,Int.zero))) RdyFrame.
Proof.
  unfold RdyState,V293_rdy_globals,V293_rdy_cells,RdyCells.
  cbn [firstn V293_rdy_raw_cells RdyMem].
  eapply V293_wstate_star with (m1:=RdyBytes (81%positive,0%Z) Tint8 (Vint32 (Int.repr 7)));
    [RdyApart 81%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
  eapply V293_wstate_star with (m1:=RdyBytes (82%positive,0%Z) Tint8 (Vint32 (Int.repr 3))).
  - apply map_join_merge;apply map_disjoint;intros [other off].
    destruct (Pos.eq_dec other 82%positive) as [E | E].
    + subst other. destruct (Z.eq_dec off 0) as [F | F].
      * subst off. right;left. unfold RdyBytes;cbn [fst snd].
        repeat rewrite map_merge_semp by reflexivity.
        repeat rewrite V293_encoded_memory_outside by
          (first [left;discriminate | right;left;cbn;lia]). reflexivity.
      * left. apply V293_encoded_memory_outside. right. cbn. lia.
    + left. apply V293_encoded_memory_outside. left;exact E.
  - split;[apply V293_encoded_memory_mapsto | reflexivity].
  - eapply V293_wstate_star with (m1:=RdyBytes (82%positive,1%Z) Tint8 Vundef);
      [RdyApart 82%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
    eapply V293_wstate_star with (m1:=RdyBytes (83%positive,0%Z) Tint8 (Vint32 (Int.repr 5)));
      [RdyApart 83%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
    eapply V293_wstate_star with (m1:=RdyBytes (84%positive,0%Z) Tint8 (Vint32 (Int.repr 9)));
      [RdyApart 84%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
    eapply V293_wstate_star with (m1:=RdyBytes (85%positive,0%Z) (Tptr V293_tcb_type) (Vptr (91%positive,Int.zero)));
      [RdyApart 85%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
    eapply V293_wstate_star with (m1:=RdyBytes (86%positive,0%Z) (Tptr V293_tcb_type) (Vptr (92%positive,Int.zero)));
      [RdyApart 86%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
    split;[apply V293_encoded_memory_mapsto | reflexivity].
Qed.
(* Independent literal AST: no production helper on the right-hand side. *)
Theorem RdyLiteralAST : V293_InitRdyList_function 11%Z 12%Z 13%Z 14%Z 15%Z 16%Z 17%Z =
  (Tvoid,dnil,dcons 17%Z Tint8 dnil,
  sseq
  (sseq (sassign (evar 11%Z) (ecast (econst32 Int.zero) Tint8))
  (sseq (sassign (evar 17%Z) (ecast (econst32 Int.zero) Tint8))
  (sseq (swhile (ebinop olt (ecast (evar 17%Z) Tint32) (econst32 (Int.repr 2)))
    (sseq (sassign (earrayelem (evar 12%Z) (evar 17%Z)) (ecast (econst32 Int.zero) Tint8))
      (sassign (evar 17%Z) (ecast (ebinop oplus (ecast (evar 17%Z) Tint32) (econst32 Int.one)) Tint8))))
  (sseq (sassign (evar 13%Z) (ecast (econst32 Int.zero) Tint8))
  (sseq (sassign (evar 14%Z) (ecast (econst32 Int.zero) Tint8))
  (sseq (sassign (evar 15%Z) (ecast enull (Tptr V293_tcb_type)))
        (sassign (evar 16%Z) (ecast enull (Tptr V293_tcb_type))))))))) sret).
Proof. reflexivity. Qed.
Definition RdyFinalCells := V293_rdy_final_cells 81%positive 82%positive 83%positive
  84%positive 85%positive 86%positive 87%positive.
Theorem RdyLiteralFinal : forall M,
  RdyState M |= V293_rdy_raw_cells RdyFinalCells RdyFrame ->
  load Tint8 M (81%positive,0%Z)=Some (Vint32 Int.zero) /\
  load Tint8 M (82%positive,0%Z)=Some (Vint32 Int.zero) /\
  load Tint8 M (82%positive,1%Z)=Some (Vint32 Int.zero) /\
  load Tint8 M (83%positive,0%Z)=Some (Vint32 Int.zero) /\
  load Tint8 M (84%positive,0%Z)=Some (Vint32 Int.zero) /\
  load (Tptr V293_tcb_type) M (85%positive,0%Z)=Some Vnull /\
  load Tint8 M (87%positive,0%Z)=Some (Vint32 (Int.repr 2)) /\
  load Tint32 M (99%positive,0%Z)=Some (Vint32 (Int.repr 123)) /\
  load (Tptr V293_tcb_type) M (86%positive,0%Z)=Some Vnull.
Proof.
  intros M Owned. repeat split;
    try solve [match goal with |- load ?tp M ?a=Some ?v =>
      exact (V293_rdy_raw_load RdyFinalCells RdyFrame a tp v (RdyState M)
        ltac:(unfold RdyFinalCells,V293_rdy_final_cells,V293_rdy_cells;cbn;auto 20) eq_refl Owned) end].
  unfold RdyFinalCells,V293_rdy_final_cells,V293_rdy_cells in Owned.
  cbn [V293_rdy_raw_cells] in Owned.
  change (load Tint32 (getmem (RdyState M)) (99%positive,0%Z)=Some (Vint32 (Int.repr 123))).
  do 8 (eapply V293_record_star_load_r;[ | exact Owned];clear Owned;intros ? Owned).
  destruct Owned as [Points Empty]. eapply mapstoval_load;[reflexivity | exact Points].
Qed.
Theorem RdyConcreteCall : forall P ks caller,
  P 2000%Z=Some (V293_InitRdyList_function 11%Z 12%Z 13%Z 14%Z 15%Z 16%Z 17%Z) ->
  exists Ms Mf,
    cstepstar P (curs (scall 2000%Z nil),(kenil,ks)) (RdyGE,caller,RdyMem RdyCells)
      (curs (sskip None),(kenil,ks)) (RdyGE,caller,Mf) /\
    RdyState Ms |= V293_rdy_raw_cells RdyFinalCells RdyFrame /\
    (forall b off, b<>87%positive -> get Mf (b,off)=get Ms (b,off)) /\
    get Mf (87%positive,0%Z)=None.
Proof.
  intros P ks caller Program. eapply V293_OS_InitRdyList_call_return;
    [exact Program | exact RdyFresh | exact RdyEnvironment | exact RdyLiteralEntry].
Qed.
(* Global readback after actual free, not only in the pre-return memory. *)
Theorem RdyFullLiteralExecution : forall P ks caller,
  P 2000%Z=Some (V293_InitRdyList_function 11%Z 12%Z 13%Z 14%Z 15%Z 16%Z 17%Z) ->
  exists Mf,
    cstepstar P (curs (scall 2000%Z nil),(kenil,ks)) (RdyGE,caller,RdyMem RdyCells)
      (curs (sskip None),(kenil,ks)) (RdyGE,caller,Mf) /\
    load Tint8 Mf (81%positive,0%Z)=Some (Vint32 Int.zero) /\
    load Tint8 Mf (82%positive,0%Z)=Some (Vint32 Int.zero) /\
    load Tint8 Mf (82%positive,1%Z)=Some (Vint32 Int.zero) /\
    load Tint8 Mf (83%positive,0%Z)=Some (Vint32 Int.zero) /\
    load Tint8 Mf (84%positive,0%Z)=Some (Vint32 Int.zero) /\
    load (Tptr V293_tcb_type) Mf (85%positive,0%Z)=Some Vnull /\
    load (Tptr V293_tcb_type) Mf (86%positive,0%Z)=Some Vnull /\
    load Tint32 Mf (99%positive,0%Z)=Some (Vint32 (Int.repr 123)) /\
    get Mf (87%positive,0%Z)=None.
Proof.
  intros P ks caller Program.
  destruct (RdyConcreteCall P ks caller Program) as (Ms & Mf & Exec & Final & Preserve & Removed).
  pose proof (RdyLiteralFinal _ Final) as Reads.
  unfold load,loadm in Reads.
  exists Mf. split;[exact Exec | ]. repeat split;try exact Removed;
    (unfold load,loadm;rewrite (V293_loadbytes_ext _ Ms Mf);
    [tauto | intros k K;apply Preserve;discriminate]).
Qed.
Print Assumptions RdyLiteralEntry.
Print Assumptions RdyLiteralAST.
Print Assumptions RdyLiteralFinal.
Print Assumptions RdyFullLiteralExecution.
