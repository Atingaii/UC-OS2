(* Whole call: independently encoded finite entry, absent callee locals, nonempty shadowed caller. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSInitQChain.
Require Import CertiOS.certiucos.v293.proofs.V293InitQChain.
Require Import CertiOS.certiucos.v293.code.V293OSQInit.
Require Import CertiOS.certiucos.v293.proofs.V293QInit.
Require Import CertiOS.certiucos.v293.code.V293OSInitMemChain.
Require Import CertiOS.certiucos.v293.proofs.V293InitMemChain.
Require Import CertiOS.certiucos.v293.code.V293OSMemInit.
Require Import CertiOS.certiucos.v293.proofs.V293MemInit.
Require Import CertiOS.certiucos.v293.code.V293OSInitFlagChain.
Require Import CertiOS.certiucos.v293.proofs.V293InitFlagChain.
Require Import CertiOS.certiucos.v293.code.V293OSFlagInit.
Require Import CertiOS.certiucos.v293.proofs.V293FlagInit.
Require Import CertiOS.certiucos.v293.code.V293OSInitEventChain.
Require Import CertiOS.certiucos.v293.proofs.V293InitEventChain.
Require Import CertiOS.certiucos.v293.code.V293OSInitEventList.
Require Import CertiOS.certiucos.v293.proofs.V293InitEventList.
Require Import CertiOS.certiucos.v293.code.V293OSInitChain.
Require Import CertiOS.certiucos.v293.proofs.V293InitChain.
Require Import CertiOS.certiucos.v293.code.V293OSInitMisc.
Require Import CertiOS.certiucos.v293.code.V293OSInitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293InitMisc.
Require Import CertiOS.certiucos.v293.code.V293OSInitTCBList.
Require Import CertiOS.certiucos.v293.code.V293OSInitTCBCall.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBCall.
Require Import CertiOS.certiucos.v293.code.V293OSInitTCBClear.
Require Import CertiOS.certiucos.v293.code.V293OSMemClr.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBList.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBClear.
Require Import CertiOS.certiucos.v293.proofs.V293MemClr.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293NullBytes.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Coq.Sorting.Permutation Lia.
Import ListNotations.
Local Open Scope Z_scope.
Definition SevenSlots := V293_InitMisc_slots 1001%Z 1002%Z 1003%Z 1004%Z 1005%Z 1006%Z 1007%Z 1008%Z 1009%Z 1010%Z 181%positive 182%positive 183%positive 184%positive 185%positive 186%positive 187%positive 188%positive 189%positive 190%positive.
Definition SevenGE : env := fold_right
  (fun d e=>set e (init_name d) (init_block d,init_type d))
  (set (set (set (set (set (set (set (set (set (set (set (set
  (set (set (set (set (set (set emp 45%Z (198%positive,V293_q_table_type)) 46%Z (199%positive,Tptr V293_q_type)) 39%Z (196%positive,V293_mem_table_type)) 40%Z (197%positive,Tptr V293_mem_type)) 37%Z (194%positive,V293_flag_table_type)) 38%Z (195%positive,Tptr V293_flag_type)) 35%Z (192%positive,V293_event_table_type)) 36%Z (193%positive,Tptr V293_event_type)) 31%Z (82%positive,Tarray V293_tcb_type 13))
   32%Z (84%positive,Tarray (Tptr V293_tcb_type) 13))
   33%Z (94%positive,Tptr V293_tcb_type)) 34%Z (95%positive,Tptr V293_tcb_type))
   21%Z (161%positive,Tint8)) 22%Z (162%positive,Tarray Tint8 2))
   23%Z (163%positive,Tint8)) 24%Z (164%positive,Tint8))
   25%Z (165%positive,Tptr V293_tcb_type)) 26%Z (166%positive,Tptr V293_tcb_type)) SevenSlots.
Definition SevenTCB := V293_encoded_memory 82%positive 0 true (repeat Undef 728).
Definition SevenPrio := V293_encoded_memory 84%positive 0 true (repeat (Byte (Byte.repr 255)) 52).
Definition SevenHeads : list V293_record_cell :=
  [((94%positive,0),Tptr V293_tcb_type,Vptr (121%positive,Int.zero));
   ((95%positive,0),Tptr V293_tcb_type,Vptr (122%positive,Int.zero))].
Definition SevenReady : list V293_record_cell :=
 [((161%positive,0),Tint8,Vint32 (Int.repr 7));
  ((162%positive,0),Tint8,Vint32 (Int.repr 3));
  ((162%positive,1),Tint8,Vundef);
  ((163%positive,0),Tint8,Vint32 (Int.repr 5));
  ((164%positive,0),Tint8,Vint32 (Int.repr 9));
  ((165%positive,0),Tptr V293_tcb_type,Vptr (211%positive,Int.zero));
  ((166%positive,0),Tptr V293_tcb_type,Vptr (212%positive,Int.zero))].
Definition SevenEventHead := V293_event_call_head 193%positive (Vptr (213%positive,Int.zero)).
Definition SevenFlagHead := V293_flag_call_head 195%positive (Vptr (214%positive,Int.zero)).
Definition SevenMemHead := V293_mem_call_head 197%positive (Vptr (215%positive,Int.zero)).
Definition SevenQHead := V293_q_call_head 199%positive (Vptr (216%positive,Int.zero)).
Definition SevenKernelCells := SevenHeads++SevenReady++SevenEventHead++SevenFlagHead++SevenMemHead++SevenQHead.
Definition SevenQTable := V293_encoded_memory 198%positive 0 true (repeat (Byte (Byte.repr 255)) 96).
Definition SevenQBytes := V293_clr_bytes 198%positive 0 (repeat (Vint32 (Int.repr 255)) 96).
Definition SevenMemTable := V293_encoded_memory 196%positive 0 true (repeat (Byte (Byte.repr 255)) 100).
Definition SevenMemBytes := V293_clr_bytes 196%positive 0 (repeat (Vint32 (Int.repr 255)) 100).
Definition SevenFlag := V293_encoded_memory 194%positive 0 true (repeat (Byte (Byte.repr 255)) 60).
Definition SevenFlagBytes := V293_clr_bytes 194%positive 0 (repeat (Vint32 (Int.repr 255)) 60).
Definition SevenEvent := V293_encoded_memory 192%positive 0 true (repeat (Byte (Byte.repr 255)) 32).
Definition SevenEventBytes := V293_clr_bytes 192%positive 0 (repeat (Vint32 (Int.repr 255)) 32).
Definition SevenFrame : list V293_record_cell :=
  [((82%positive,728),Tint8,Vint32 (Int.repr 17));
   ((84%positive,52),Tint8,Vint32 (Int.repr 29));
   ((99%positive,0),Tint32,Vint32 (Int.repr 123));
   ((110%positive,0),Tint32,Vint32 (Int.repr 7))].
Fixpoint SevenMem (cells : list V293_record_cell) : mem :=
  match cells with []=>emp | ((b,off),tp,v)::tail=>
    merge (V293_encoded_memory b off true (encode_val tp v)) (SevenMem tail) end.
Definition SevenMemory := merge SevenQTable (merge SevenMemTable (merge SevenFlag (merge SevenEvent (merge SevenTCB (merge SevenPrio (SevenMem (SevenKernelCells++SevenFrame))))))).
Definition SevenCaller : env := set emp 41%Z (110%positive,Tint32).
Definition SevenState M := V293_wstate SevenGE SevenCaller M.

Lemma SevenConstantRange : forall n v byte ge le b off,
  encode_val Tint8 v=[byte] ->
  V293_wstate ge le (V293_encoded_memory b off true (repeat byte n)) |=
    V293_rdy_raw_cells (V293_clr_bytes b off (repeat v n)) Aemp.
Proof.
  induction n as [ | n IH];intros v byte ge le b off Encoding.
  - split;reflexivity.
  - cbn [repeat V293_clr_bytes V293_rdy_raw_cells].
    eapply V293_wstate_star;[apply V293_encoded_memory_join | | apply IH;exact Encoding].
    split;[ | reflexivity]. exists [byte]. split;[exact Encoding | ].
    exists (sig (b,off) (true,byte)). exists (emp:mem). split;[apply map_join_emp | ]. split;reflexivity.
Qed.
Ltac SevenOutside :=
  unfold SevenQTable,SevenMemTable,SevenFlag,SevenEvent,SevenTCB,SevenPrio;
  cbn [SevenKernelCells SevenHeads SevenReady SevenEventHead V293_event_call_head SevenFlagHead V293_flag_call_head SevenMemHead V293_mem_call_head SevenQHead V293_q_call_head SevenFrame SevenMem app];
  repeat first [rewrite V293_encoded_memory_outside by
    (first [left;congruence | right;rewrite ?repeat_length;cbn [length encode_val inj_bytes encode_int];lia])
    | rewrite map_merge_semp by reflexivity];
  reflexivity.
Ltac SevenApart b :=
  apply map_join_merge;apply map_disjoint;intros [other off];
  destruct (Pos.eq_dec other b);[subst other;right;left | left];
  repeat first [rewrite V293_encoded_memory_outside by (left;congruence)
    | rewrite map_merge_semp by reflexivity];reflexivity.
Lemma SevenLiteralEntry : SevenState SevenMemory |= V293_rdy_raw_cells
  (SevenQBytes++SevenMemBytes++SevenFlagBytes++SevenEventBytes++V293_clr_bytes 82%positive 0 (repeat Vundef 728)++
   V293_clr_bytes 84%positive 0 (repeat (Vint32 (Int.repr 255)) 52)++SevenKernelCells++SevenFrame) Atrue.
Proof.
  unfold SevenState,SevenMemory. repeat rewrite V293_raw_cells_append.
  apply (V293_raw_cells_join SevenQBytes
    (V293_rdy_raw_cells (SevenMemBytes++SevenFlagBytes++SevenEventBytes++V293_clr_bytes 82%positive 0 (repeat Vundef 728)++
      V293_clr_bytes 84%positive 0 (repeat (Vint32 (Int.repr 255)) 52)++SevenKernelCells++SevenFrame) Atrue)).
  eapply V293_wstate_star with (m1:=SevenQTable).
  { apply map_join_merge;apply map_disjoint;intros [b i].
    destruct (Pos.eq_dec b 198%positive) as [B|B].
    - subst b. right;left;SevenOutside.
    - left. unfold SevenQTable. apply V293_encoded_memory_outside;left;exact B. }
  { unfold SevenQBytes,SevenQTable;apply SevenConstantRange;reflexivity. }
  repeat rewrite V293_raw_cells_append.
  apply (V293_raw_cells_join SevenMemBytes
    (V293_rdy_raw_cells (SevenFlagBytes++SevenEventBytes++V293_clr_bytes 82%positive 0 (repeat Vundef 728)++
      V293_clr_bytes 84%positive 0 (repeat (Vint32 (Int.repr 255)) 52)++SevenKernelCells++SevenFrame) Atrue)).
  eapply V293_wstate_star with (m1:=SevenMemTable).
  { apply map_join_merge;apply map_disjoint;intros [b i].
    destruct (Pos.eq_dec b 196%positive) as [B|B].
    - subst b. right;left;SevenOutside.
    - left. unfold SevenMemTable. apply V293_encoded_memory_outside;left;exact B. }
  { unfold SevenMemBytes,SevenMemTable;apply SevenConstantRange;reflexivity. }
  repeat rewrite V293_raw_cells_append.
  apply (V293_raw_cells_join SevenFlagBytes
    (V293_rdy_raw_cells (SevenEventBytes++V293_clr_bytes 82%positive 0 (repeat Vundef 728)++
      V293_clr_bytes 84%positive 0 (repeat (Vint32 (Int.repr 255)) 52)++SevenKernelCells++SevenFrame) Atrue)).
  eapply V293_wstate_star with (m1:=SevenFlag).
  { apply map_join_merge;apply map_disjoint;intros [b i].
    destruct (Pos.eq_dec b 194%positive) as [B|B].
    - subst b. right;left;SevenOutside.
    - left. unfold SevenFlag. apply V293_encoded_memory_outside;left;exact B. }
  { unfold SevenFlagBytes,SevenFlag;apply SevenConstantRange;reflexivity. }
  repeat rewrite V293_raw_cells_append.
  apply (V293_raw_cells_join SevenEventBytes
    (V293_rdy_raw_cells (V293_clr_bytes 82%positive 0 (repeat Vundef 728))
      (V293_rdy_raw_cells (V293_clr_bytes 84%positive 0 (repeat (Vint32 (Int.repr 255)) 52))
        (V293_rdy_raw_cells SevenKernelCells (V293_rdy_raw_cells SevenFrame Atrue))))).
  eapply V293_wstate_star with (m1:=SevenEvent).
  { apply map_join_merge;apply map_disjoint;intros [b i].
    destruct (Pos.eq_dec b 192%positive) as [B|B].
    - subst b. right;left;SevenOutside.
    - left. unfold SevenEvent. apply V293_encoded_memory_outside;left;exact B. }
  { unfold SevenEventBytes,SevenEvent;apply SevenConstantRange;reflexivity. }
  apply (V293_raw_cells_join (V293_clr_bytes 82%positive 0 (repeat Vundef 728))
    (V293_rdy_raw_cells (V293_clr_bytes 84%positive 0 (repeat (Vint32 (Int.repr 255)) 52))
      (V293_rdy_raw_cells SevenKernelCells (V293_rdy_raw_cells SevenFrame Atrue)))).
  eapply V293_wstate_star with (m1:=SevenTCB).
  - apply map_join_merge;apply map_disjoint;intros [b i].
    destruct (Pos.eq_dec b 82%positive) as [B|B].
    + subst b. destruct (Z_lt_dec i 728) as [I|I].
      * right;left;SevenOutside.
      * left. unfold SevenTCB. apply V293_encoded_memory_outside. right;right. rewrite repeat_length;lia.
    + left. unfold SevenTCB. apply V293_encoded_memory_outside;left;exact B.
  - unfold SevenTCB;apply SevenConstantRange;reflexivity.
  - apply (V293_raw_cells_join (V293_clr_bytes 84%positive 0 (repeat (Vint32 (Int.repr 255)) 52))
      (V293_rdy_raw_cells SevenKernelCells (V293_rdy_raw_cells SevenFrame Atrue))).
    eapply V293_wstate_star with (m1:=SevenPrio).
    + apply map_join_merge;apply map_disjoint;intros [b i].
      destruct (Pos.eq_dec b 84%positive) as [B|B].
      * subst b. destruct (Z_lt_dec i 52) as [I|I].
        -- right;left;SevenOutside.
        -- left. unfold SevenPrio. apply V293_encoded_memory_outside. right;right. rewrite repeat_length;lia.
      * left. unfold SevenPrio. apply V293_encoded_memory_outside;left;exact B.
    + unfold SevenPrio;apply SevenConstantRange;reflexivity.
    + cbn [SevenKernelCells SevenHeads SevenReady SevenEventHead V293_event_call_head SevenFlagHead V293_flag_call_head SevenMemHead V293_mem_call_head SevenQHead V293_q_call_head SevenFrame SevenMem app V293_rdy_raw_cells].
      eapply V293_wstate_star with (m1:=V293_encoded_memory 94%positive 0 true (encode_val (Tptr V293_tcb_type) (Vptr (121%positive,Int.zero))));
        [SevenApart 94%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
      eapply V293_wstate_star with (m1:=V293_encoded_memory 95%positive 0 true (encode_val (Tptr V293_tcb_type) (Vptr (122%positive,Int.zero))));
        [SevenApart 95%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
      eapply V293_wstate_star with (m1:=V293_encoded_memory 161%positive 0 true (encode_val (Tint8) (Vint32 (Int.repr 7)))).
      { SevenApart 161%positive. }
      { split;[apply V293_encoded_memory_mapsto | reflexivity]. }
      eapply V293_wstate_star with (m1:=V293_encoded_memory 162%positive 0 true (encode_val (Tint8) (Vint32 (Int.repr 3)))).
      { apply map_join_merge;apply map_disjoint;intros [other off].
        destruct (Pos.eq_dec other 162%positive) as [E | E].
        + subst other. destruct (Z.eq_dec off 0) as [F | F].
          * subst off. right;left.
            repeat first [rewrite V293_encoded_memory_outside by
              (first [left;congruence | right;left;cbn [length encode_val];lia])
              | rewrite map_merge_semp by reflexivity]. reflexivity.
          * left. apply V293_encoded_memory_outside. right;change (off<0 \/ 1<=off);lia.
        + left. apply V293_encoded_memory_outside;left;exact E. }
      { split;[apply V293_encoded_memory_mapsto | reflexivity]. }
      eapply V293_wstate_star with (m1:=V293_encoded_memory 162%positive 1 true (encode_val (Tint8) (Vundef))).
      { SevenApart 162%positive. }
      { split;[apply V293_encoded_memory_mapsto | reflexivity]. }
      eapply V293_wstate_star with (m1:=V293_encoded_memory 163%positive 0 true (encode_val (Tint8) (Vint32 (Int.repr 5)))).
      { SevenApart 163%positive. }
      { split;[apply V293_encoded_memory_mapsto | reflexivity]. }
      eapply V293_wstate_star with (m1:=V293_encoded_memory 164%positive 0 true (encode_val (Tint8) (Vint32 (Int.repr 9)))).
      { SevenApart 164%positive. }
      { split;[apply V293_encoded_memory_mapsto | reflexivity]. }
      eapply V293_wstate_star with (m1:=V293_encoded_memory 165%positive 0 true (encode_val (Tptr V293_tcb_type) (Vptr (211%positive,Int.zero)))).
      { SevenApart 165%positive. }
      { split;[apply V293_encoded_memory_mapsto | reflexivity]. }
      eapply V293_wstate_star with (m1:=V293_encoded_memory 166%positive 0 true (encode_val (Tptr V293_tcb_type) (Vptr (212%positive,Int.zero)))).
      { SevenApart 166%positive. }
      { split;[apply V293_encoded_memory_mapsto | reflexivity]. }
      eapply V293_wstate_star with (m1:=V293_encoded_memory 193%positive 0 true (encode_val (Tptr V293_event_type) (Vptr (213%positive,Int.zero))));
        [SevenApart 193%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
      eapply V293_wstate_star with (m1:=V293_encoded_memory 195%positive 0 true (encode_val (Tptr V293_flag_type) (Vptr (214%positive,Int.zero))));
        [SevenApart 195%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
      eapply V293_wstate_star with (m1:=V293_encoded_memory 197%positive 0 true (encode_val (Tptr V293_mem_type) (Vptr (215%positive,Int.zero))));
        [SevenApart 197%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
      eapply V293_wstate_star with (m1:=V293_encoded_memory 199%positive 0 true (encode_val (Tptr V293_q_type) (Vptr (216%positive,Int.zero))));
        [SevenApart 199%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
      eapply V293_wstate_star with (m1:=V293_encoded_memory 82%positive 728 true (encode_val (Tint8) (Vint32 (Int.repr 17))));
        [SevenApart 82%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
      eapply V293_wstate_star with (m1:=V293_encoded_memory 84%positive 52 true (encode_val (Tint8) (Vint32 (Int.repr 29))));
        [SevenApart 84%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
      eapply V293_wstate_star with (m1:=V293_encoded_memory 99%positive 0 true (encode_val (Tint32) (Vint32 (Int.repr 123))));
        [SevenApart 99%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
      eapply V293_wstate_star with (m1:=V293_encoded_memory 110%positive 0 true (encode_val Tint32 (Vint32 (Int.repr 7))));
        [SevenApart 110%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
      exact I.
Qed.
Definition SevenTail := V293_rdy_globals 161%positive 162%positive 163%positive 164%positive 165%positive 166%positive
  (Vint32 (Int.repr 7)) (Vint32 (Int.repr 3)) Vundef (Vint32 (Int.repr 5))
  (Vint32 (Int.repr 9)) (Vptr (211%positive,Int.zero)) (Vptr (212%positive,Int.zero))++
  V293_clr_bytes 82%positive 0 (repeat Vundef 728)++
  V293_clr_bytes 84%positive 0 (repeat (Vint32 (Int.repr 255)) 52)++SevenHeads++SevenEventBytes++SevenEventHead++SevenFlagBytes++SevenFlagHead++SevenMemBytes++SevenMemHead++SevenQBytes++SevenQHead++SevenFrame.
Definition SevenMiscCells : list (block*type*val) :=
 [(181%positive,Tint32,Vint32 (Int.repr 57));
  (182%positive,Tint8,Vint32 (Int.repr 3));
  (183%positive,Tint8,Vint32 (Int.repr 2));
  (184%positive,Tint8,Vint32 (Int.repr 9));
  (185%positive,Tint8,Vint32 Int.one);
  (186%positive,Tint32,Vint32 (Int.repr 42));
  (187%positive,Tint32,Vundef);
  (188%positive,Tint32,Vundef);
  (189%positive,Tint32,Vint32 (Int.repr 100));
  (190%positive,Tint8,Vint32 Int.one)].
Fixpoint SevenMiscMem cells : mem := match cells with
 | []=>SevenMemory | (b,tp,v)::tail=>merge (V293_encoded_memory b 0 true (encode_val tp v)) (SevenMiscMem tail) end.
Definition SevenEntryMemory := SevenMiscMem SevenMiscCells.
Lemma SevenRawTail : SevenState SevenMemory |= V293_rdy_raw_cells SevenTail Atrue.
Proof.
 pose proof SevenLiteralEntry as H.
 unfold SevenTail. change (SevenState SevenMemory |= V293_rdy_raw_cells
  (SevenReady++V293_clr_bytes 82%positive 0 (repeat Vundef 728)++
   V293_clr_bytes 84%positive 0 (repeat (Vint32 (Int.repr 255)) 52)++SevenHeads++
   SevenEventBytes++SevenEventHead++SevenFlagBytes++SevenFlagHead++SevenMemBytes++SevenMemHead++SevenQBytes++SevenQHead++SevenFrame) Atrue).
 eapply V293_raw_cells_permutation;[ | exact H].
 unfold SevenKernelCells. repeat rewrite <-app_assoc.
 eapply Permutation_trans with (l':=(SevenReady++SevenQBytes++SevenMemBytes++SevenFlagBytes++SevenEventBytes++(V293_clr_bytes 82%positive 0 (repeat Vundef 728))++(V293_clr_bytes 84%positive 0 (repeat (Vint32 (Int.repr 255)) 52))++SevenHeads++SevenEventHead++SevenFlagHead++SevenMemHead++SevenQHead++SevenFrame)).
 { pose proof (Permutation_app_tail (SevenEventHead++SevenFlagHead++SevenMemHead++SevenQHead++SevenFrame) (Permutation_app_comm (SevenQBytes++SevenMemBytes++SevenFlagBytes++SevenEventBytes++(V293_clr_bytes 82%positive 0 (repeat Vundef 728))++(V293_clr_bytes 84%positive 0 (repeat (Vint32 (Int.repr 255)) 52))++SevenHeads) SevenReady)) as P.
   repeat rewrite <-app_assoc in P;exact P. }
 apply Permutation_app_head.
 eapply Permutation_trans with (l':=((V293_clr_bytes 82%positive 0 (repeat Vundef 728))++SevenQBytes++SevenMemBytes++SevenFlagBytes++SevenEventBytes++(V293_clr_bytes 84%positive 0 (repeat (Vint32 (Int.repr 255)) 52))++SevenHeads++SevenEventHead++SevenFlagHead++SevenMemHead++SevenQHead++SevenFrame)).
 { pose proof (Permutation_app_tail ((V293_clr_bytes 84%positive 0 (repeat (Vint32 (Int.repr 255)) 52))++SevenHeads++SevenEventHead++SevenFlagHead++SevenMemHead++SevenQHead++SevenFrame) (Permutation_app_comm (SevenQBytes++SevenMemBytes++SevenFlagBytes++SevenEventBytes) (V293_clr_bytes 82%positive 0 (repeat Vundef 728)))) as P.
   repeat rewrite <-app_assoc in P;exact P. }
 apply Permutation_app_head.
 eapply Permutation_trans with (l':=((V293_clr_bytes 84%positive 0 (repeat (Vint32 (Int.repr 255)) 52))++SevenQBytes++SevenMemBytes++SevenFlagBytes++SevenEventBytes++SevenHeads++SevenEventHead++SevenFlagHead++SevenMemHead++SevenQHead++SevenFrame)).
 { pose proof (Permutation_app_tail (SevenHeads++SevenEventHead++SevenFlagHead++SevenMemHead++SevenQHead++SevenFrame) (Permutation_app_comm (SevenQBytes++SevenMemBytes++SevenFlagBytes++SevenEventBytes) (V293_clr_bytes 84%positive 0 (repeat (Vint32 (Int.repr 255)) 52)))) as P.
   repeat rewrite <-app_assoc in P;exact P. }
 apply Permutation_app_head.
 eapply Permutation_trans with (l':=(SevenHeads++SevenQBytes++SevenMemBytes++SevenFlagBytes++SevenEventBytes++SevenEventHead++SevenFlagHead++SevenMemHead++SevenQHead++SevenFrame)).
 { pose proof (Permutation_app_tail (SevenEventHead++SevenFlagHead++SevenMemHead++SevenQHead++SevenFrame) (Permutation_app_comm (SevenQBytes++SevenMemBytes++SevenFlagBytes++SevenEventBytes) SevenHeads)) as P.
   repeat rewrite <-app_assoc in P;exact P. }
 apply Permutation_app_head.
 eapply Permutation_trans with (l':=(SevenEventBytes++SevenQBytes++SevenMemBytes++SevenFlagBytes++SevenEventHead++SevenFlagHead++SevenMemHead++SevenQHead++SevenFrame)).
 { pose proof (Permutation_app_tail (SevenEventHead++SevenFlagHead++SevenMemHead++SevenQHead++SevenFrame) (Permutation_app_comm (SevenQBytes++SevenMemBytes++SevenFlagBytes) SevenEventBytes)) as P.
   repeat rewrite <-app_assoc in P;exact P. }
 apply Permutation_app_head.
 eapply Permutation_trans with (l':=(SevenEventHead++SevenQBytes++SevenMemBytes++SevenFlagBytes++SevenFlagHead++SevenMemHead++SevenQHead++SevenFrame)).
 { pose proof (Permutation_app_tail (SevenFlagHead++SevenMemHead++SevenQHead++SevenFrame) (Permutation_app_comm (SevenQBytes++SevenMemBytes++SevenFlagBytes) SevenEventHead)) as P.
   repeat rewrite <-app_assoc in P;exact P. }
 apply Permutation_app_head.
 eapply Permutation_trans with (l':=(SevenFlagBytes++SevenQBytes++SevenMemBytes++SevenFlagHead++SevenMemHead++SevenQHead++SevenFrame)).
 { pose proof (Permutation_app_tail (SevenFlagHead++SevenMemHead++SevenQHead++SevenFrame) (Permutation_app_comm (SevenQBytes++SevenMemBytes) SevenFlagBytes)) as P.
   repeat rewrite <-app_assoc in P;exact P. }
 apply Permutation_app_head.
 eapply Permutation_trans with (l':=(SevenFlagHead++SevenQBytes++SevenMemBytes++SevenMemHead++SevenQHead++SevenFrame)).
 { pose proof (Permutation_app_tail (SevenMemHead++SevenQHead++SevenFrame) (Permutation_app_comm (SevenQBytes++SevenMemBytes) SevenFlagHead)) as P.
   repeat rewrite <-app_assoc in P;exact P. }
 apply Permutation_app_head.
 eapply Permutation_trans with (l':=(SevenMemBytes++SevenQBytes++SevenMemHead++SevenQHead++SevenFrame)).
 { pose proof (Permutation_app_tail (SevenMemHead++SevenQHead++SevenFrame) (Permutation_app_comm (SevenQBytes) SevenMemBytes)) as P.
   repeat rewrite <-app_assoc in P;exact P. }
 apply Permutation_app_head.
 eapply Permutation_trans with (l':=(SevenMemHead++SevenQBytes++SevenQHead++SevenFrame)).
 { pose proof (Permutation_app_tail (SevenQHead++SevenFrame) (Permutation_app_comm (SevenQBytes) SevenMemHead)) as P.
   repeat rewrite <-app_assoc in P;exact P. }
 apply Permutation_app_head.
 reflexivity.
Qed.
Lemma SevenSlotEntry : forall x tp b v,
 get SevenGE x=Some (b,tp) ->
 V293_wstate SevenGE emp (V293_encoded_memory b 0 true (encode_val tp v)) |=
  V293_init_binding (Build_V293_init_slot x tp b) ** V293_init_memory (Build_V293_init_slot x tp b) false.
Proof.
 intros x tp b v Env. eapply V293_wstate_star with (m1:=emp) (m2:=V293_encoded_memory b 0 true (encode_val tp v)).
 - apply map_join_comm;apply map_join_emp.
 - split.
   + exists b. split;[exact Env | ]. repeat split;reflexivity.
   + split;[intros [w E];change (None=Some w) in E;discriminate | split;reflexivity].
 - exists v. split;[apply V293_encoded_memory_mapsto | reflexivity].
Qed.
Theorem SevenLiteralFullEntry : V293_wstate SevenGE emp SevenEntryMemory |=
  V293_init_resources SevenSlots false (V293_rdy_raw_cells SevenTail Atrue).
Proof.
 unfold SevenEntryMemory,SevenMiscCells,SevenSlots,V293_InitMisc_slots.
 cbn [SevenMiscMem V293_init_resources].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 181%positive 0 true (encode_val (Tint32) (Vint32 (Int.repr 57)))).
 { apply map_join_merge;apply map_disjoint;intros [other off].
   destruct (Pos.eq_dec other 181%positive);[subst other;right;left | left];
   unfold SevenMemory,SevenQTable,SevenMemTable,SevenFlag,SevenEvent,SevenTCB,SevenPrio;cbn [SevenKernelCells SevenHeads SevenReady SevenEventHead V293_event_call_head SevenFlagHead V293_flag_call_head SevenMemHead V293_mem_call_head SevenQHead V293_q_call_head SevenFrame SevenMem app];
   repeat first [rewrite V293_encoded_memory_outside by (left;congruence)
     | rewrite map_merge_semp by reflexivity];reflexivity. }
 { apply SevenSlotEntry;vm_compute;reflexivity. }
 eapply V293_wstate_star with (m1:=V293_encoded_memory 182%positive 0 true (encode_val (Tint8) (Vint32 (Int.repr 3)))).
 { apply map_join_merge;apply map_disjoint;intros [other off].
   destruct (Pos.eq_dec other 182%positive);[subst other;right;left | left];
   unfold SevenMemory,SevenQTable,SevenMemTable,SevenFlag,SevenEvent,SevenTCB,SevenPrio;cbn [SevenKernelCells SevenHeads SevenReady SevenEventHead V293_event_call_head SevenFlagHead V293_flag_call_head SevenMemHead V293_mem_call_head SevenQHead V293_q_call_head SevenFrame SevenMem app];
   repeat first [rewrite V293_encoded_memory_outside by (left;congruence)
     | rewrite map_merge_semp by reflexivity];reflexivity. }
 { apply SevenSlotEntry;vm_compute;reflexivity. }
 eapply V293_wstate_star with (m1:=V293_encoded_memory 183%positive 0 true (encode_val (Tint8) (Vint32 (Int.repr 2)))).
 { apply map_join_merge;apply map_disjoint;intros [other off].
   destruct (Pos.eq_dec other 183%positive);[subst other;right;left | left];
   unfold SevenMemory,SevenQTable,SevenMemTable,SevenFlag,SevenEvent,SevenTCB,SevenPrio;cbn [SevenKernelCells SevenHeads SevenReady SevenEventHead V293_event_call_head SevenFlagHead V293_flag_call_head SevenMemHead V293_mem_call_head SevenQHead V293_q_call_head SevenFrame SevenMem app];
   repeat first [rewrite V293_encoded_memory_outside by (left;congruence)
     | rewrite map_merge_semp by reflexivity];reflexivity. }
 { apply SevenSlotEntry;vm_compute;reflexivity. }
 eapply V293_wstate_star with (m1:=V293_encoded_memory 184%positive 0 true (encode_val (Tint8) (Vint32 (Int.repr 9)))).
 { apply map_join_merge;apply map_disjoint;intros [other off].
   destruct (Pos.eq_dec other 184%positive);[subst other;right;left | left];
   unfold SevenMemory,SevenQTable,SevenMemTable,SevenFlag,SevenEvent,SevenTCB,SevenPrio;cbn [SevenKernelCells SevenHeads SevenReady SevenEventHead V293_event_call_head SevenFlagHead V293_flag_call_head SevenMemHead V293_mem_call_head SevenQHead V293_q_call_head SevenFrame SevenMem app];
   repeat first [rewrite V293_encoded_memory_outside by (left;congruence)
     | rewrite map_merge_semp by reflexivity];reflexivity. }
 { apply SevenSlotEntry;vm_compute;reflexivity. }
 eapply V293_wstate_star with (m1:=V293_encoded_memory 185%positive 0 true (encode_val (Tint8) (Vint32 Int.one))).
 { apply map_join_merge;apply map_disjoint;intros [other off].
   destruct (Pos.eq_dec other 185%positive);[subst other;right;left | left];
   unfold SevenMemory,SevenQTable,SevenMemTable,SevenFlag,SevenEvent,SevenTCB,SevenPrio;cbn [SevenKernelCells SevenHeads SevenReady SevenEventHead V293_event_call_head SevenFlagHead V293_flag_call_head SevenMemHead V293_mem_call_head SevenQHead V293_q_call_head SevenFrame SevenMem app];
   repeat first [rewrite V293_encoded_memory_outside by (left;congruence)
     | rewrite map_merge_semp by reflexivity];reflexivity. }
 { apply SevenSlotEntry;vm_compute;reflexivity. }
 eapply V293_wstate_star with (m1:=V293_encoded_memory 186%positive 0 true (encode_val (Tint32) (Vint32 (Int.repr 42)))).
 { apply map_join_merge;apply map_disjoint;intros [other off].
   destruct (Pos.eq_dec other 186%positive);[subst other;right;left | left];
   unfold SevenMemory,SevenQTable,SevenMemTable,SevenFlag,SevenEvent,SevenTCB,SevenPrio;cbn [SevenKernelCells SevenHeads SevenReady SevenEventHead V293_event_call_head SevenFlagHead V293_flag_call_head SevenMemHead V293_mem_call_head SevenQHead V293_q_call_head SevenFrame SevenMem app];
   repeat first [rewrite V293_encoded_memory_outside by (left;congruence)
     | rewrite map_merge_semp by reflexivity];reflexivity. }
 { apply SevenSlotEntry;vm_compute;reflexivity. }
 eapply V293_wstate_star with (m1:=V293_encoded_memory 187%positive 0 true (encode_val (Tint32) (Vundef))).
 { apply map_join_merge;apply map_disjoint;intros [other off].
   destruct (Pos.eq_dec other 187%positive);[subst other;right;left | left];
   unfold SevenMemory,SevenQTable,SevenMemTable,SevenFlag,SevenEvent,SevenTCB,SevenPrio;cbn [SevenKernelCells SevenHeads SevenReady SevenEventHead V293_event_call_head SevenFlagHead V293_flag_call_head SevenMemHead V293_mem_call_head SevenQHead V293_q_call_head SevenFrame SevenMem app];
   repeat first [rewrite V293_encoded_memory_outside by (left;congruence)
     | rewrite map_merge_semp by reflexivity];reflexivity. }
 { apply SevenSlotEntry;vm_compute;reflexivity. }
 eapply V293_wstate_star with (m1:=V293_encoded_memory 188%positive 0 true (encode_val (Tint32) (Vundef))).
 { apply map_join_merge;apply map_disjoint;intros [other off].
   destruct (Pos.eq_dec other 188%positive);[subst other;right;left | left];
   unfold SevenMemory,SevenQTable,SevenMemTable,SevenFlag,SevenEvent,SevenTCB,SevenPrio;cbn [SevenKernelCells SevenHeads SevenReady SevenEventHead V293_event_call_head SevenFlagHead V293_flag_call_head SevenMemHead V293_mem_call_head SevenQHead V293_q_call_head SevenFrame SevenMem app];
   repeat first [rewrite V293_encoded_memory_outside by (left;congruence)
     | rewrite map_merge_semp by reflexivity];reflexivity. }
 { apply SevenSlotEntry;vm_compute;reflexivity. }
 eapply V293_wstate_star with (m1:=V293_encoded_memory 189%positive 0 true (encode_val (Tint32) (Vint32 (Int.repr 100)))).
 { apply map_join_merge;apply map_disjoint;intros [other off].
   destruct (Pos.eq_dec other 189%positive);[subst other;right;left | left];
   unfold SevenMemory,SevenQTable,SevenMemTable,SevenFlag,SevenEvent,SevenTCB,SevenPrio;cbn [SevenKernelCells SevenHeads SevenReady SevenEventHead V293_event_call_head SevenFlagHead V293_flag_call_head SevenMemHead V293_mem_call_head SevenQHead V293_q_call_head SevenFrame SevenMem app];
   repeat first [rewrite V293_encoded_memory_outside by (left;congruence)
     | rewrite map_merge_semp by reflexivity];reflexivity. }
 { apply SevenSlotEntry;vm_compute;reflexivity. }
 eapply V293_wstate_star with (m1:=V293_encoded_memory 190%positive 0 true (encode_val (Tint8) (Vint32 Int.one))).
 { apply map_join_merge;apply map_disjoint;intros [other off].
   destruct (Pos.eq_dec other 190%positive);[subst other;right;left | left];
   unfold SevenMemory,SevenQTable,SevenMemTable,SevenFlag,SevenEvent,SevenTCB,SevenPrio;cbn [SevenKernelCells SevenHeads SevenReady SevenEventHead V293_event_call_head SevenFlagHead V293_flag_call_head SevenMemHead V293_mem_call_head SevenQHead V293_q_call_head SevenFrame SevenMem app];
   repeat first [rewrite V293_encoded_memory_outside by (left;congruence)
     | rewrite map_merge_semp by reflexivity];reflexivity. }
 { apply SevenSlotEntry;vm_compute;reflexivity. }
 eapply V293_raw_cells_environment;[right;reflexivity | exact SevenRawTail].
Qed.
Definition SevenProgram f :=
 if Z.eq_dec f 201%Z then Some (V293_InitMisc_function 1001%Z 1002%Z 1003%Z 1004%Z 1005%Z 1006%Z 1007%Z 1008%Z 1009%Z 1010%Z)
 else if Z.eq_dec f 202%Z then Some (V293_InitRdyList_function 21%Z 22%Z 23%Z 24%Z 25%Z 26%Z 41%Z)
 else if Z.eq_dec f 203%Z then Some (V293_InitTCBList_function 204%Z 31%Z 32%Z 33%Z 34%Z 41%Z 42%Z 43%Z 44%Z)
 else if Z.eq_dec f 205%Z then Some (V293_InitEventList_function 204%Z 35%Z 36%Z 41%Z 42%Z 43%Z 44%Z)
 else if Z.eq_dec f 206%Z then Some (V293_FlagInit_function 204%Z 37%Z 38%Z 41%Z 42%Z 43%Z 44%Z)
 else if Z.eq_dec f 207%Z then Some (V293_MemInit_function 204%Z 39%Z 40%Z 41%Z 42%Z)
 else if Z.eq_dec f 208%Z then Some (V293_QInit_function 204%Z 45%Z 46%Z 41%Z 42%Z 43%Z 44%Z)
 else if Z.eq_dec f 204%Z then Some (V293_MemClr_function 11%Z 12%Z) else None.
Lemma SevenLiteralOrder : V293_init_seven_calls 201%Z 202%Z 203%Z 205%Z 206%Z 207%Z 208%Z =
 sseq (sseq (sseq (sseq (sseq (scall 201%Z nil) (sseq (scall 202%Z nil) (scall 203%Z nil))) (scall 205%Z nil)) (scall 206%Z nil)) (scall 207%Z nil)) (scall 208%Z nil).
Proof. reflexivity. Qed.
Definition SevenReadyZero := V293_rdy_globals 161%positive 162%positive 163%positive
  164%positive 165%positive 166%positive (Vint32 Int.zero) (Vint32 Int.zero)
  (Vint32 Int.zero) (Vint32 Int.zero) (Vint32 Int.zero) Vnull Vnull.
Definition SevenExtraCells := SevenReadyZero++V293_misc_zero_cells SevenSlots++SevenFrame.
Definition SevenFinalCells := V293_q_call_result 199%positive 198%positive
 (V293_mem_call_result 197%positive 196%positive
 (V293_flag_call_result 195%positive 194%positive
 (V293_event_call_result 193%positive 192%positive
  (V293_tcb_call_result 94%positive 95%positive 82%positive 84%positive SevenExtraCells)))).
Definition SevenChecks := V293_q_call_result 199%positive 198%positive []++
 V293_mem_call_result 197%positive 196%positive []++
 V293_flag_call_result 195%positive 194%positive []++
 V293_event_call_result 193%positive 192%positive []++
 V293_tcb_call_heads 94%positive 95%positive Vnull (Vptr (82%positive,Int.zero))++
 V293_tcb_linked_next 82%positive++V293_null_pointer_cells 84%positive 0 13++SevenExtraCells.
Lemma SevenCheckCount : length SevenChecks=293%nat.
Proof. reflexivity. Qed.
Lemma SevenChecksValid : forall a tp v, In (a,tp,v) SevenChecks -> rule_type_val_match tp v=true.
Proof.
 intros a tp v Member.
 cbn [SevenChecks V293_q_call_result V293_q_call_head V293_q_linked V293_q_untouched_cells V293_mem_call_result V293_mem_call_head V293_mem_linked V293_mem_untouched_cells V293_flag_call_result V293_flag_call_head V293_flag_linked V293_flag_untouched_cells V293_event_call_result V293_event_call_head V293_event_linked
   V293_event_untouched_cells V293_clr_bytes repeat
   V293_tcb_call_heads V293_tcb_linked_next V293_null_pointer_cells seq map
   SevenExtraCells SevenReadyZero V293_rdy_globals V293_misc_zero_cells SevenSlots
   V293_InitMisc_slots SevenFrame init_block init_type app] in Member.
 repeat (destruct Member as [E | Member];[inversion E;subst;reflexivity | ]);contradiction.
Qed.
Lemma SevenChecksInFinal : forall a tp v, In (a,tp,v) SevenChecks -> In (a,tp,v) SevenFinalCells.
Proof.
 intros a tp v Member.
 unfold SevenChecks,SevenFinalCells,V293_q_call_result,V293_mem_call_result,V293_flag_call_result,V293_event_call_result,V293_tcb_call_result in *.
 repeat rewrite in_app_iff in *;cbn [In] in *;tauto.
Qed.
Lemma SevenExtraCount : length SevenExtraCells=21%nat.
Proof. reflexivity. Qed.
Lemma SevenExtrasValid : forall a tp v,
 In (a,tp,v) SevenExtraCells -> rule_type_val_match tp v=true.
Proof.
 intros a tp v Member.
 cbn [SevenExtraCells SevenReadyZero V293_rdy_globals V293_misc_zero_cells SevenSlots
   V293_InitMisc_slots SevenFrame map app init_block init_type] in Member.
 repeat (destruct Member as [E | Member];[inversion E;subst;reflexivity | ]);contradiction.
Qed.
Lemma SevenReadyEnvironment : forall bi,
 V293_rdy_env SevenGE (V293_rdy_locals 41%Z bi) 21%Z 22%Z 23%Z 24%Z 25%Z 26%Z 41%Z
 161%positive 162%positive 163%positive 164%positive 165%positive 166%positive bi.
Proof. intro bi. repeat split;reflexivity. Qed.
Lemma SevenTCBEnvironment : forall bi bn b1 b2,
 V293_tcb_link_env SevenGE (V293_tcb_call_locals 41%Z 42%Z 43%Z 44%Z bi bn b1 b2)
 31%Z 33%Z 34%Z 41%Z 42%Z 43%Z 44%Z 82%positive 94%positive 95%positive bi bn b1 b2.
Proof. intros. repeat split;reflexivity. Qed.
Lemma SevenEventEnvironment : forall bi bn b1 b2,
 V293_event_link_env SevenGE (V293_event_call_locals 41%Z 42%Z 43%Z 44%Z bi bn b1 b2)
 35%Z 36%Z 41%Z 42%Z 43%Z 44%Z 192%positive 193%positive bi bn b1 b2.
Proof. intros. repeat split;reflexivity. Qed.
Lemma SevenFlagEnvironment : forall bi bn b1 b2,
 V293_flag_link_env SevenGE (V293_flag_call_locals 41%Z 42%Z 43%Z 44%Z bi bn b1 b2)
 37%Z 38%Z 41%Z 42%Z 43%Z 44%Z 194%positive 195%positive bi bn b1 b2.
Proof. intros. repeat split;reflexivity. Qed.
Lemma SevenMemEnvironment : forall bp bi,
 V293_mem_link_env SevenGE (V293_mem_call_locals 41%Z 42%Z bp bi)
 39%Z 40%Z 41%Z 42%Z 196%positive 197%positive bp bi.
Proof. intros. repeat split;reflexivity. Qed.
Lemma SevenQEnvironment : forall bi bn b1 b2,
 V293_q_link_env SevenGE (V293_q_call_locals 41%Z 42%Z 43%Z 44%Z bi bn b1 b2)
 45%Z 46%Z 41%Z 42%Z 43%Z 44%Z 198%positive 199%positive bi bn b1 b2.
Proof. intros. repeat split;reflexivity. Qed.
Theorem SevenConcreteExecution : forall ks, exists Msix Mf bi bn b1 b2,
 cstepstar SevenProgram (curs (V293_init_seven_calls 201%Z 202%Z 203%Z 205%Z 206%Z 207%Z 208%Z),(kenil,ks))
   (SevenGE,SevenCaller,SevenEntryMemory) (curs (sskip None),(kenil,ks)) (SevenGE,SevenCaller,Mf) /\
 SevenState Mf |= V293_rdy_raw_cells SevenFinalCells Atrue /\
 (forall a tp v, In (a,tp,v) SevenChecks -> load tp Mf a=Some v) /\
 cstepstar SevenProgram (curs (V293_init_six_calls 201%Z 202%Z 203%Z 205%Z 206%Z 207%Z),
   (kenil,kseq (scall 208%Z nil) ks)) (SevenGE,SevenCaller,SevenEntryMemory)
   (curs (sskip None),(kenil,kseq (scall 208%Z nil) ks)) (SevenGE,SevenCaller,Msix) /\
 cstepstar SevenProgram (curs (scall 208%Z nil),(kenil,ks)) (SevenGE,SevenCaller,Msix)
   (curs (sskip None),(kenil,ks)) (SevenGE,SevenCaller,Mf) /\ fresh Msix bi /\ fresh Msix bn /\ fresh Msix b1 /\ fresh Msix b2 /\ NoDup (V293_q_call_blocks bi bn b1 b2) /\
 (forall c tp k, In (c,tp) [(bi,Tint16);(bn,Tint16);(b1,Tptr V293_q_type);(b2,Tptr V293_q_type)] ->
   (k<typelen tp)%nat -> get Mf (c,Z.of_nat k)=None).
Proof.
 intro ks.
 destruct (V293_OSInit_seven_calls SevenSlots (repeat Vundef 728)
   (repeat (Vint32 (Int.repr 255)) 52) (repeat (Vint32 (Int.repr 255)) 32) (repeat (Vint32 (Int.repr 255)) 60) (repeat (Vint32 (Int.repr 255)) 100) (repeat (Vint32 (Int.repr 255)) 96) SevenFrame
   SevenProgram ks SevenGE SevenCaller SevenEntryMemory
   (fun _=>false) (false,nil,nil) emp (spec_done None)
   201%Z 202%Z 203%Z 204%Z 11%Z 12%Z 21%Z 22%Z 23%Z 24%Z 25%Z 26%Z 41%Z
   161%positive 162%positive 163%positive 164%positive 165%positive 166%positive
   31%Z 32%Z 33%Z 34%Z 41%Z 42%Z 43%Z 44%Z 82%positive 84%positive 94%positive 95%positive
   (Vint32 (Int.repr 7)) (Vint32 (Int.repr 3)) Vundef (Vint32 (Int.repr 5))
   (Vint32 (Int.repr 9)) (Vptr (211%positive,Int.zero)) (Vptr (212%positive,Int.zero))
   (Vptr (121%positive,Int.zero)) (Vptr (122%positive,Int.zero))
   205%Z 35%Z 36%Z 41%Z 42%Z 43%Z 44%Z 192%positive 193%positive (Vptr (213%positive,Int.zero))
   206%Z 37%Z 38%Z 41%Z 42%Z 43%Z 44%Z 194%positive 195%positive (Vptr (214%positive,Int.zero))
   207%Z 39%Z 40%Z 41%Z 42%Z 196%positive 197%positive (Vptr (215%positive,Int.zero))
   208%Z 45%Z 46%Z 41%Z 42%Z 43%Z 44%Z 198%positive 199%positive (Vptr (216%positive,Int.zero))
   ltac:(unfold SevenSlots,V293_InitMisc_slots;repeat (apply Forall_cons;[unfold V293_init_scalar;cbn;auto | ]);apply Forall_nil)
   ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)
   ltac:(discriminate) ltac:(lia) ltac:(lia) ltac:(lia)
   SevenReadyEnvironment SevenTCBEnvironment ltac:(intros;reflexivity) ltac:(reflexivity)
   ltac:(apply repeat_length) ltac:(apply repeat_length)
   ltac:(reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) SevenEventEnvironment ltac:(apply repeat_length)
   ltac:(reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) SevenFlagEnvironment ltac:(apply repeat_length)
   ltac:(reflexivity) ltac:(lia) SevenMemEnvironment ltac:(apply repeat_length)
   ltac:(reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) SevenQEnvironment ltac:(apply repeat_length)
   SevenLiteralFullEntry)
   as (Msix&Mf&bi&bn&b1&b2&Exec&Prefix&Queue&Fi&Fn&F1&F2&ND&Owned&Freed).
 exists Msix. exists Mf. exists bi. exists bn. exists b1. exists b2.
 split;[exact Exec | ]. split;[exact Owned | ]. split.
 - intros a tp v Member. change (load tp (getmem (SevenState Mf)) a=Some v).
   eapply (V293_rdy_raw_load SevenFinalCells Atrue);
     [apply SevenChecksInFinal;exact Member | exact (SevenChecksValid a tp v Member) | exact Owned].
 - split;[exact Prefix | ]. split;[exact Queue | ].
   split;[exact Fi | ]. split;[exact Fn | ]. split;[exact F1 | ]. split;[exact F2 | ]. split;[exact ND | exact Freed].
Qed.
Theorem SevenReturnConnections : forall ks, exists Mf,
 cstepstar SevenProgram (curs (V293_init_seven_calls 201%Z 202%Z 203%Z 205%Z 206%Z 207%Z 208%Z),(kenil,ks))
   (SevenGE,SevenCaller,SevenEntryMemory) (curs (sskip None),(kenil,ks)) (SevenGE,SevenCaller,Mf) /\
 load (Tcom_ptr 414%Z) Mf (198%positive,0)=Some (Vptr (198%positive,Int.repr 24)) /\
 load (Tptr V293_q_type) Mf (199%positive,0)=Some (Vptr (198%positive,Int.zero)) /\
 load Tint8 Mf (198%positive,4)=Some (Vint32 Int.zero) /\
 load Tint8 Mf (198%positive,8)=Some (Vint32 Int.zero) /\
 load (Tcom_ptr 414%Z) Mf (198%positive,72)=Some Vnull /\
 load (Tptr Tvoid) Mf (196%positive,4)=Some (Vptr (196%positive,Int.repr 20)) /\
 load Tint8 Mf (161%positive,0)=Some (Vint32 Int.zero) /\
 load Tint32 Mf (99%positive,0)=Some (Vint32 (Int.repr 123)) /\
 load Tint32 Mf (110%positive,0)=Some (Vint32 (Int.repr 7)).
Proof.
 intro ks. destruct (SevenConcreteExecution ks)
   as (Msix&Mf&bi&bn&b1&b2&Exec&Owned&Loads&Prefix&Queue&Fi&Fn&F1&F2&ND&Freed).
 exists Mf. split;[exact Exec | ]. repeat split;
 apply Loads;vm_compute;tauto.
Qed.
Print Assumptions SevenConcreteExecution.
