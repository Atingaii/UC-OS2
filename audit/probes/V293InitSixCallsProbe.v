(* Whole call: independently encoded finite entry, absent callee locals, nonempty shadowed caller. *)
Require Import CertiOS.framework.include_frm.
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
Definition SixSlots := V293_InitMisc_slots 1001%Z 1002%Z 1003%Z 1004%Z 1005%Z 1006%Z 1007%Z 1008%Z 1009%Z 1010%Z 181%positive 182%positive 183%positive 184%positive 185%positive 186%positive 187%positive 188%positive 189%positive 190%positive.
Definition SixGE : env := fold_right
  (fun d e=>set e (init_name d) (init_block d,init_type d))
  (set (set (set (set (set (set (set (set (set (set
  (set (set (set (set (set (set emp 39%Z (196%positive,V293_mem_table_type)) 40%Z (197%positive,Tptr V293_mem_type)) 37%Z (194%positive,V293_flag_table_type)) 38%Z (195%positive,Tptr V293_flag_type)) 35%Z (192%positive,V293_event_table_type)) 36%Z (193%positive,Tptr V293_event_type)) 31%Z (82%positive,Tarray V293_tcb_type 13))
   32%Z (84%positive,Tarray (Tptr V293_tcb_type) 13))
   33%Z (94%positive,Tptr V293_tcb_type)) 34%Z (95%positive,Tptr V293_tcb_type))
   21%Z (161%positive,Tint8)) 22%Z (162%positive,Tarray Tint8 2))
   23%Z (163%positive,Tint8)) 24%Z (164%positive,Tint8))
   25%Z (165%positive,Tptr V293_tcb_type)) 26%Z (166%positive,Tptr V293_tcb_type)) SixSlots.
Definition SixTCB := V293_encoded_memory 82%positive 0 true (repeat Undef 728).
Definition SixPrio := V293_encoded_memory 84%positive 0 true (repeat (Byte (Byte.repr 255)) 52).
Definition SixHeads : list V293_record_cell :=
  [((94%positive,0),Tptr V293_tcb_type,Vptr (121%positive,Int.zero));
   ((95%positive,0),Tptr V293_tcb_type,Vptr (122%positive,Int.zero))].
Definition SixReady : list V293_record_cell :=
 [((161%positive,0),Tint8,Vint32 (Int.repr 7));
  ((162%positive,0),Tint8,Vint32 (Int.repr 3));
  ((162%positive,1),Tint8,Vundef);
  ((163%positive,0),Tint8,Vint32 (Int.repr 5));
  ((164%positive,0),Tint8,Vint32 (Int.repr 9));
  ((165%positive,0),Tptr V293_tcb_type,Vptr (211%positive,Int.zero));
  ((166%positive,0),Tptr V293_tcb_type,Vptr (212%positive,Int.zero))].
Definition SixEventHead := V293_event_call_head 193%positive (Vptr (213%positive,Int.zero)).
Definition SixFlagHead := V293_flag_call_head 195%positive (Vptr (214%positive,Int.zero)).
Definition SixMemHead := V293_mem_call_head 197%positive (Vptr (215%positive,Int.zero)).
Definition SixKernelCells := SixHeads++SixReady++SixEventHead++SixFlagHead++SixMemHead.
Definition SixMemTable := V293_encoded_memory 196%positive 0 true (repeat (Byte (Byte.repr 255)) 100).
Definition SixMemBytes := V293_clr_bytes 196%positive 0 (repeat (Vint32 (Int.repr 255)) 100).
Definition SixFlag := V293_encoded_memory 194%positive 0 true (repeat (Byte (Byte.repr 255)) 60).
Definition SixFlagBytes := V293_clr_bytes 194%positive 0 (repeat (Vint32 (Int.repr 255)) 60).
Definition SixEvent := V293_encoded_memory 192%positive 0 true (repeat (Byte (Byte.repr 255)) 32).
Definition SixEventBytes := V293_clr_bytes 192%positive 0 (repeat (Vint32 (Int.repr 255)) 32).
Definition SixFrame : list V293_record_cell :=
  [((82%positive,728),Tint8,Vint32 (Int.repr 17));
   ((84%positive,52),Tint8,Vint32 (Int.repr 29));
   ((99%positive,0),Tint32,Vint32 (Int.repr 123));
   ((110%positive,0),Tint32,Vint32 (Int.repr 7))].
Fixpoint SixMem (cells : list V293_record_cell) : mem :=
  match cells with []=>emp | ((b,off),tp,v)::tail=>
    merge (V293_encoded_memory b off true (encode_val tp v)) (SixMem tail) end.
Definition SixMemory := merge SixMemTable (merge SixFlag (merge SixEvent (merge SixTCB (merge SixPrio (SixMem (SixKernelCells++SixFrame)))))).
Definition SixCaller : env := set emp 41%Z (110%positive,Tint32).
Definition SixState M := V293_wstate SixGE SixCaller M.

Lemma SixConstantRange : forall n v byte ge le b off,
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
Ltac SixOutside :=
  unfold SixMemTable,SixFlag,SixEvent,SixTCB,SixPrio;
  cbn [SixKernelCells SixHeads SixReady SixEventHead V293_event_call_head SixFlagHead V293_flag_call_head SixMemHead V293_mem_call_head SixFrame SixMem app];
  repeat first [rewrite V293_encoded_memory_outside by
    (first [left;congruence | right;rewrite ?repeat_length;cbn [length encode_val inj_bytes encode_int];lia])
    | rewrite map_merge_semp by reflexivity];
  reflexivity.
Ltac SixApart b :=
  apply map_join_merge;apply map_disjoint;intros [other off];
  destruct (Pos.eq_dec other b);[subst other;right;left | left];
  repeat first [rewrite V293_encoded_memory_outside by (left;congruence)
    | rewrite map_merge_semp by reflexivity];reflexivity.
Lemma SixLiteralEntry : SixState SixMemory |= V293_rdy_raw_cells
  (SixMemBytes++SixFlagBytes++SixEventBytes++V293_clr_bytes 82%positive 0 (repeat Vundef 728)++
   V293_clr_bytes 84%positive 0 (repeat (Vint32 (Int.repr 255)) 52)++SixKernelCells++SixFrame) Atrue.
Proof.
  unfold SixState,SixMemory. repeat rewrite V293_raw_cells_append.
  apply (V293_raw_cells_join SixMemBytes
    (V293_rdy_raw_cells (SixFlagBytes++SixEventBytes++V293_clr_bytes 82%positive 0 (repeat Vundef 728)++
      V293_clr_bytes 84%positive 0 (repeat (Vint32 (Int.repr 255)) 52)++SixKernelCells++SixFrame) Atrue)).
  eapply V293_wstate_star with (m1:=SixMemTable).
  { apply map_join_merge;apply map_disjoint;intros [b i].
    destruct (Pos.eq_dec b 196%positive) as [B|B].
    - subst b. right;left;SixOutside.
    - left. unfold SixMemTable. apply V293_encoded_memory_outside;left;exact B. }
  { unfold SixMemBytes,SixMemTable;apply SixConstantRange;reflexivity. }
  repeat rewrite V293_raw_cells_append.
  apply (V293_raw_cells_join SixFlagBytes
    (V293_rdy_raw_cells (SixEventBytes++V293_clr_bytes 82%positive 0 (repeat Vundef 728)++
      V293_clr_bytes 84%positive 0 (repeat (Vint32 (Int.repr 255)) 52)++SixKernelCells++SixFrame) Atrue)).
  eapply V293_wstate_star with (m1:=SixFlag).
  { apply map_join_merge;apply map_disjoint;intros [b i].
    destruct (Pos.eq_dec b 194%positive) as [B|B].
    - subst b. right;left;SixOutside.
    - left. unfold SixFlag. apply V293_encoded_memory_outside;left;exact B. }
  { unfold SixFlagBytes,SixFlag;apply SixConstantRange;reflexivity. }
  repeat rewrite V293_raw_cells_append.
  apply (V293_raw_cells_join SixEventBytes
    (V293_rdy_raw_cells (V293_clr_bytes 82%positive 0 (repeat Vundef 728))
      (V293_rdy_raw_cells (V293_clr_bytes 84%positive 0 (repeat (Vint32 (Int.repr 255)) 52))
        (V293_rdy_raw_cells SixKernelCells (V293_rdy_raw_cells SixFrame Atrue))))).
  eapply V293_wstate_star with (m1:=SixEvent).
  { apply map_join_merge;apply map_disjoint;intros [b i].
    destruct (Pos.eq_dec b 192%positive) as [B|B].
    - subst b. right;left;SixOutside.
    - left. unfold SixEvent. apply V293_encoded_memory_outside;left;exact B. }
  { unfold SixEventBytes,SixEvent;apply SixConstantRange;reflexivity. }
  apply (V293_raw_cells_join (V293_clr_bytes 82%positive 0 (repeat Vundef 728))
    (V293_rdy_raw_cells (V293_clr_bytes 84%positive 0 (repeat (Vint32 (Int.repr 255)) 52))
      (V293_rdy_raw_cells SixKernelCells (V293_rdy_raw_cells SixFrame Atrue)))).
  eapply V293_wstate_star with (m1:=SixTCB).
  - apply map_join_merge;apply map_disjoint;intros [b i].
    destruct (Pos.eq_dec b 82%positive) as [B|B].
    + subst b. destruct (Z_lt_dec i 728) as [I|I].
      * right;left;SixOutside.
      * left. unfold SixTCB. apply V293_encoded_memory_outside. right;right. rewrite repeat_length;lia.
    + left. unfold SixTCB. apply V293_encoded_memory_outside;left;exact B.
  - unfold SixTCB;apply SixConstantRange;reflexivity.
  - apply (V293_raw_cells_join (V293_clr_bytes 84%positive 0 (repeat (Vint32 (Int.repr 255)) 52))
      (V293_rdy_raw_cells SixKernelCells (V293_rdy_raw_cells SixFrame Atrue))).
    eapply V293_wstate_star with (m1:=SixPrio).
    + apply map_join_merge;apply map_disjoint;intros [b i].
      destruct (Pos.eq_dec b 84%positive) as [B|B].
      * subst b. destruct (Z_lt_dec i 52) as [I|I].
        -- right;left;SixOutside.
        -- left. unfold SixPrio. apply V293_encoded_memory_outside. right;right. rewrite repeat_length;lia.
      * left. unfold SixPrio. apply V293_encoded_memory_outside;left;exact B.
    + unfold SixPrio;apply SixConstantRange;reflexivity.
    + cbn [SixKernelCells SixHeads SixReady SixEventHead V293_event_call_head SixFlagHead V293_flag_call_head SixMemHead V293_mem_call_head SixFrame SixMem app V293_rdy_raw_cells].
      eapply V293_wstate_star with (m1:=V293_encoded_memory 94%positive 0 true (encode_val (Tptr V293_tcb_type) (Vptr (121%positive,Int.zero))));
        [SixApart 94%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
      eapply V293_wstate_star with (m1:=V293_encoded_memory 95%positive 0 true (encode_val (Tptr V293_tcb_type) (Vptr (122%positive,Int.zero))));
        [SixApart 95%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
      eapply V293_wstate_star with (m1:=V293_encoded_memory 161%positive 0 true (encode_val (Tint8) (Vint32 (Int.repr 7)))).
      { SixApart 161%positive. }
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
      { SixApart 162%positive. }
      { split;[apply V293_encoded_memory_mapsto | reflexivity]. }
      eapply V293_wstate_star with (m1:=V293_encoded_memory 163%positive 0 true (encode_val (Tint8) (Vint32 (Int.repr 5)))).
      { SixApart 163%positive. }
      { split;[apply V293_encoded_memory_mapsto | reflexivity]. }
      eapply V293_wstate_star with (m1:=V293_encoded_memory 164%positive 0 true (encode_val (Tint8) (Vint32 (Int.repr 9)))).
      { SixApart 164%positive. }
      { split;[apply V293_encoded_memory_mapsto | reflexivity]. }
      eapply V293_wstate_star with (m1:=V293_encoded_memory 165%positive 0 true (encode_val (Tptr V293_tcb_type) (Vptr (211%positive,Int.zero)))).
      { SixApart 165%positive. }
      { split;[apply V293_encoded_memory_mapsto | reflexivity]. }
      eapply V293_wstate_star with (m1:=V293_encoded_memory 166%positive 0 true (encode_val (Tptr V293_tcb_type) (Vptr (212%positive,Int.zero)))).
      { SixApart 166%positive. }
      { split;[apply V293_encoded_memory_mapsto | reflexivity]. }
      eapply V293_wstate_star with (m1:=V293_encoded_memory 193%positive 0 true (encode_val (Tptr V293_event_type) (Vptr (213%positive,Int.zero))));
        [SixApart 193%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
      eapply V293_wstate_star with (m1:=V293_encoded_memory 195%positive 0 true (encode_val (Tptr V293_flag_type) (Vptr (214%positive,Int.zero))));
        [SixApart 195%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
      eapply V293_wstate_star with (m1:=V293_encoded_memory 197%positive 0 true (encode_val (Tptr V293_mem_type) (Vptr (215%positive,Int.zero))));
        [SixApart 197%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
      eapply V293_wstate_star with (m1:=V293_encoded_memory 82%positive 728 true (encode_val (Tint8) (Vint32 (Int.repr 17))));
        [SixApart 82%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
      eapply V293_wstate_star with (m1:=V293_encoded_memory 84%positive 52 true (encode_val (Tint8) (Vint32 (Int.repr 29))));
        [SixApart 84%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
      eapply V293_wstate_star with (m1:=V293_encoded_memory 99%positive 0 true (encode_val (Tint32) (Vint32 (Int.repr 123))));
        [SixApart 99%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
      eapply V293_wstate_star with (m1:=V293_encoded_memory 110%positive 0 true (encode_val Tint32 (Vint32 (Int.repr 7))));
        [SixApart 110%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
      exact I.
Qed.
Definition SixTail := V293_rdy_globals 161%positive 162%positive 163%positive 164%positive 165%positive 166%positive
  (Vint32 (Int.repr 7)) (Vint32 (Int.repr 3)) Vundef (Vint32 (Int.repr 5))
  (Vint32 (Int.repr 9)) (Vptr (211%positive,Int.zero)) (Vptr (212%positive,Int.zero))++
  V293_clr_bytes 82%positive 0 (repeat Vundef 728)++
  V293_clr_bytes 84%positive 0 (repeat (Vint32 (Int.repr 255)) 52)++SixHeads++SixEventBytes++SixEventHead++SixFlagBytes++SixFlagHead++SixMemBytes++SixMemHead++SixFrame.
Definition SixMiscCells : list (block*type*val) :=
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
Fixpoint SixMiscMem cells : mem := match cells with
 | []=>SixMemory | (b,tp,v)::tail=>merge (V293_encoded_memory b 0 true (encode_val tp v)) (SixMiscMem tail) end.
Definition SixEntryMemory := SixMiscMem SixMiscCells.
Lemma SixRawTail : SixState SixMemory |= V293_rdy_raw_cells SixTail Atrue.
Proof.
 pose proof SixLiteralEntry as H.
 unfold SixTail. change (SixState SixMemory |= V293_rdy_raw_cells
  (SixReady++V293_clr_bytes 82%positive 0 (repeat Vundef 728)++
   V293_clr_bytes 84%positive 0 (repeat (Vint32 (Int.repr 255)) 52)++SixHeads++
   SixEventBytes++SixEventHead++SixFlagBytes++SixFlagHead++SixMemBytes++SixMemHead++SixFrame) Atrue).
 eapply V293_raw_cells_permutation;[ | exact H].
 unfold SixKernelCells. repeat rewrite <-app_assoc.
 eapply Permutation_trans with (l':=(SixReady++SixMemBytes++SixFlagBytes++SixEventBytes++(V293_clr_bytes 82%positive 0 (repeat Vundef 728))++(V293_clr_bytes 84%positive 0 (repeat (Vint32 (Int.repr 255)) 52))++SixHeads++SixEventHead++SixFlagHead++SixMemHead++SixFrame)).
 { pose proof (Permutation_app_tail (SixEventHead++SixFlagHead++SixMemHead++SixFrame) (Permutation_app_comm (SixMemBytes++SixFlagBytes++SixEventBytes++(V293_clr_bytes 82%positive 0 (repeat Vundef 728))++(V293_clr_bytes 84%positive 0 (repeat (Vint32 (Int.repr 255)) 52))++SixHeads) SixReady)) as P.
   repeat rewrite <-app_assoc in P;exact P. }
 apply Permutation_app_head.
 eapply Permutation_trans with (l':=((V293_clr_bytes 82%positive 0 (repeat Vundef 728))++SixMemBytes++SixFlagBytes++SixEventBytes++(V293_clr_bytes 84%positive 0 (repeat (Vint32 (Int.repr 255)) 52))++SixHeads++SixEventHead++SixFlagHead++SixMemHead++SixFrame)).
 { pose proof (Permutation_app_tail ((V293_clr_bytes 84%positive 0 (repeat (Vint32 (Int.repr 255)) 52))++SixHeads++SixEventHead++SixFlagHead++SixMemHead++SixFrame) (Permutation_app_comm (SixMemBytes++SixFlagBytes++SixEventBytes) (V293_clr_bytes 82%positive 0 (repeat Vundef 728)))) as P.
   repeat rewrite <-app_assoc in P;exact P. }
 apply Permutation_app_head.
 eapply Permutation_trans with (l':=((V293_clr_bytes 84%positive 0 (repeat (Vint32 (Int.repr 255)) 52))++SixMemBytes++SixFlagBytes++SixEventBytes++SixHeads++SixEventHead++SixFlagHead++SixMemHead++SixFrame)).
 { pose proof (Permutation_app_tail (SixHeads++SixEventHead++SixFlagHead++SixMemHead++SixFrame) (Permutation_app_comm (SixMemBytes++SixFlagBytes++SixEventBytes) (V293_clr_bytes 84%positive 0 (repeat (Vint32 (Int.repr 255)) 52)))) as P.
   repeat rewrite <-app_assoc in P;exact P. }
 apply Permutation_app_head.
 eapply Permutation_trans with (l':=(SixHeads++SixMemBytes++SixFlagBytes++SixEventBytes++SixEventHead++SixFlagHead++SixMemHead++SixFrame)).
 { pose proof (Permutation_app_tail (SixEventHead++SixFlagHead++SixMemHead++SixFrame) (Permutation_app_comm (SixMemBytes++SixFlagBytes++SixEventBytes) SixHeads)) as P.
   repeat rewrite <-app_assoc in P;exact P. }
 apply Permutation_app_head.
 eapply Permutation_trans with (l':=(SixEventBytes++SixMemBytes++SixFlagBytes++SixEventHead++SixFlagHead++SixMemHead++SixFrame)).
 { pose proof (Permutation_app_tail (SixEventHead++SixFlagHead++SixMemHead++SixFrame) (Permutation_app_comm (SixMemBytes++SixFlagBytes) SixEventBytes)) as P.
   repeat rewrite <-app_assoc in P;exact P. }
 apply Permutation_app_head.
 eapply Permutation_trans with (l':=(SixEventHead++SixMemBytes++SixFlagBytes++SixFlagHead++SixMemHead++SixFrame)).
 { pose proof (Permutation_app_tail (SixFlagHead++SixMemHead++SixFrame) (Permutation_app_comm (SixMemBytes++SixFlagBytes) SixEventHead)) as P.
   repeat rewrite <-app_assoc in P;exact P. }
 apply Permutation_app_head.
 eapply Permutation_trans with (l':=(SixFlagBytes++SixMemBytes++SixFlagHead++SixMemHead++SixFrame)).
 { pose proof (Permutation_app_tail (SixFlagHead++SixMemHead++SixFrame) (Permutation_app_comm (SixMemBytes) SixFlagBytes)) as P.
   repeat rewrite <-app_assoc in P;exact P. }
 apply Permutation_app_head.
 eapply Permutation_trans with (l':=(SixFlagHead++SixMemBytes++SixMemHead++SixFrame)).
 { pose proof (Permutation_app_tail (SixMemHead++SixFrame) (Permutation_app_comm (SixMemBytes) SixFlagHead)) as P.
   repeat rewrite <-app_assoc in P;exact P. }
 apply Permutation_app_head.
 reflexivity.
Qed.
Lemma SixSlotEntry : forall x tp b v,
 get SixGE x=Some (b,tp) ->
 V293_wstate SixGE emp (V293_encoded_memory b 0 true (encode_val tp v)) |=
  V293_init_binding (Build_V293_init_slot x tp b) ** V293_init_memory (Build_V293_init_slot x tp b) false.
Proof.
 intros x tp b v Env. eapply V293_wstate_star with (m1:=emp) (m2:=V293_encoded_memory b 0 true (encode_val tp v)).
 - apply map_join_comm;apply map_join_emp.
 - split.
   + exists b. split;[exact Env | ]. repeat split;reflexivity.
   + split;[intros [w E];change (None=Some w) in E;discriminate | split;reflexivity].
 - exists v. split;[apply V293_encoded_memory_mapsto | reflexivity].
Qed.
Theorem SixLiteralFullEntry : V293_wstate SixGE emp SixEntryMemory |=
  V293_init_resources SixSlots false (V293_rdy_raw_cells SixTail Atrue).
Proof.
 unfold SixEntryMemory,SixMiscCells,SixSlots,V293_InitMisc_slots.
 cbn [SixMiscMem V293_init_resources].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 181%positive 0 true (encode_val (Tint32) (Vint32 (Int.repr 57)))).
 { apply map_join_merge;apply map_disjoint;intros [other off].
   destruct (Pos.eq_dec other 181%positive);[subst other;right;left | left];
   unfold SixMemory,SixMemTable,SixFlag,SixEvent,SixTCB,SixPrio;cbn [SixKernelCells SixHeads SixReady SixEventHead V293_event_call_head SixFlagHead V293_flag_call_head SixMemHead V293_mem_call_head SixFrame SixMem app];
   repeat first [rewrite V293_encoded_memory_outside by (left;congruence)
     | rewrite map_merge_semp by reflexivity];reflexivity. }
 { apply SixSlotEntry;vm_compute;reflexivity. }
 eapply V293_wstate_star with (m1:=V293_encoded_memory 182%positive 0 true (encode_val (Tint8) (Vint32 (Int.repr 3)))).
 { apply map_join_merge;apply map_disjoint;intros [other off].
   destruct (Pos.eq_dec other 182%positive);[subst other;right;left | left];
   unfold SixMemory,SixMemTable,SixFlag,SixEvent,SixTCB,SixPrio;cbn [SixKernelCells SixHeads SixReady SixEventHead V293_event_call_head SixFlagHead V293_flag_call_head SixMemHead V293_mem_call_head SixFrame SixMem app];
   repeat first [rewrite V293_encoded_memory_outside by (left;congruence)
     | rewrite map_merge_semp by reflexivity];reflexivity. }
 { apply SixSlotEntry;vm_compute;reflexivity. }
 eapply V293_wstate_star with (m1:=V293_encoded_memory 183%positive 0 true (encode_val (Tint8) (Vint32 (Int.repr 2)))).
 { apply map_join_merge;apply map_disjoint;intros [other off].
   destruct (Pos.eq_dec other 183%positive);[subst other;right;left | left];
   unfold SixMemory,SixMemTable,SixFlag,SixEvent,SixTCB,SixPrio;cbn [SixKernelCells SixHeads SixReady SixEventHead V293_event_call_head SixFlagHead V293_flag_call_head SixMemHead V293_mem_call_head SixFrame SixMem app];
   repeat first [rewrite V293_encoded_memory_outside by (left;congruence)
     | rewrite map_merge_semp by reflexivity];reflexivity. }
 { apply SixSlotEntry;vm_compute;reflexivity. }
 eapply V293_wstate_star with (m1:=V293_encoded_memory 184%positive 0 true (encode_val (Tint8) (Vint32 (Int.repr 9)))).
 { apply map_join_merge;apply map_disjoint;intros [other off].
   destruct (Pos.eq_dec other 184%positive);[subst other;right;left | left];
   unfold SixMemory,SixMemTable,SixFlag,SixEvent,SixTCB,SixPrio;cbn [SixKernelCells SixHeads SixReady SixEventHead V293_event_call_head SixFlagHead V293_flag_call_head SixMemHead V293_mem_call_head SixFrame SixMem app];
   repeat first [rewrite V293_encoded_memory_outside by (left;congruence)
     | rewrite map_merge_semp by reflexivity];reflexivity. }
 { apply SixSlotEntry;vm_compute;reflexivity. }
 eapply V293_wstate_star with (m1:=V293_encoded_memory 185%positive 0 true (encode_val (Tint8) (Vint32 Int.one))).
 { apply map_join_merge;apply map_disjoint;intros [other off].
   destruct (Pos.eq_dec other 185%positive);[subst other;right;left | left];
   unfold SixMemory,SixMemTable,SixFlag,SixEvent,SixTCB,SixPrio;cbn [SixKernelCells SixHeads SixReady SixEventHead V293_event_call_head SixFlagHead V293_flag_call_head SixMemHead V293_mem_call_head SixFrame SixMem app];
   repeat first [rewrite V293_encoded_memory_outside by (left;congruence)
     | rewrite map_merge_semp by reflexivity];reflexivity. }
 { apply SixSlotEntry;vm_compute;reflexivity. }
 eapply V293_wstate_star with (m1:=V293_encoded_memory 186%positive 0 true (encode_val (Tint32) (Vint32 (Int.repr 42)))).
 { apply map_join_merge;apply map_disjoint;intros [other off].
   destruct (Pos.eq_dec other 186%positive);[subst other;right;left | left];
   unfold SixMemory,SixMemTable,SixFlag,SixEvent,SixTCB,SixPrio;cbn [SixKernelCells SixHeads SixReady SixEventHead V293_event_call_head SixFlagHead V293_flag_call_head SixMemHead V293_mem_call_head SixFrame SixMem app];
   repeat first [rewrite V293_encoded_memory_outside by (left;congruence)
     | rewrite map_merge_semp by reflexivity];reflexivity. }
 { apply SixSlotEntry;vm_compute;reflexivity. }
 eapply V293_wstate_star with (m1:=V293_encoded_memory 187%positive 0 true (encode_val (Tint32) (Vundef))).
 { apply map_join_merge;apply map_disjoint;intros [other off].
   destruct (Pos.eq_dec other 187%positive);[subst other;right;left | left];
   unfold SixMemory,SixMemTable,SixFlag,SixEvent,SixTCB,SixPrio;cbn [SixKernelCells SixHeads SixReady SixEventHead V293_event_call_head SixFlagHead V293_flag_call_head SixMemHead V293_mem_call_head SixFrame SixMem app];
   repeat first [rewrite V293_encoded_memory_outside by (left;congruence)
     | rewrite map_merge_semp by reflexivity];reflexivity. }
 { apply SixSlotEntry;vm_compute;reflexivity. }
 eapply V293_wstate_star with (m1:=V293_encoded_memory 188%positive 0 true (encode_val (Tint32) (Vundef))).
 { apply map_join_merge;apply map_disjoint;intros [other off].
   destruct (Pos.eq_dec other 188%positive);[subst other;right;left | left];
   unfold SixMemory,SixMemTable,SixFlag,SixEvent,SixTCB,SixPrio;cbn [SixKernelCells SixHeads SixReady SixEventHead V293_event_call_head SixFlagHead V293_flag_call_head SixMemHead V293_mem_call_head SixFrame SixMem app];
   repeat first [rewrite V293_encoded_memory_outside by (left;congruence)
     | rewrite map_merge_semp by reflexivity];reflexivity. }
 { apply SixSlotEntry;vm_compute;reflexivity. }
 eapply V293_wstate_star with (m1:=V293_encoded_memory 189%positive 0 true (encode_val (Tint32) (Vint32 (Int.repr 100)))).
 { apply map_join_merge;apply map_disjoint;intros [other off].
   destruct (Pos.eq_dec other 189%positive);[subst other;right;left | left];
   unfold SixMemory,SixMemTable,SixFlag,SixEvent,SixTCB,SixPrio;cbn [SixKernelCells SixHeads SixReady SixEventHead V293_event_call_head SixFlagHead V293_flag_call_head SixMemHead V293_mem_call_head SixFrame SixMem app];
   repeat first [rewrite V293_encoded_memory_outside by (left;congruence)
     | rewrite map_merge_semp by reflexivity];reflexivity. }
 { apply SixSlotEntry;vm_compute;reflexivity. }
 eapply V293_wstate_star with (m1:=V293_encoded_memory 190%positive 0 true (encode_val (Tint8) (Vint32 Int.one))).
 { apply map_join_merge;apply map_disjoint;intros [other off].
   destruct (Pos.eq_dec other 190%positive);[subst other;right;left | left];
   unfold SixMemory,SixMemTable,SixFlag,SixEvent,SixTCB,SixPrio;cbn [SixKernelCells SixHeads SixReady SixEventHead V293_event_call_head SixFlagHead V293_flag_call_head SixMemHead V293_mem_call_head SixFrame SixMem app];
   repeat first [rewrite V293_encoded_memory_outside by (left;congruence)
     | rewrite map_merge_semp by reflexivity];reflexivity. }
 { apply SixSlotEntry;vm_compute;reflexivity. }
 eapply V293_raw_cells_environment;[right;reflexivity | exact SixRawTail].
Qed.
Definition SixProgram f :=
 if Z.eq_dec f 201%Z then Some (V293_InitMisc_function 1001%Z 1002%Z 1003%Z 1004%Z 1005%Z 1006%Z 1007%Z 1008%Z 1009%Z 1010%Z)
 else if Z.eq_dec f 202%Z then Some (V293_InitRdyList_function 21%Z 22%Z 23%Z 24%Z 25%Z 26%Z 41%Z)
 else if Z.eq_dec f 203%Z then Some (V293_InitTCBList_function 204%Z 31%Z 32%Z 33%Z 34%Z 41%Z 42%Z 43%Z 44%Z)
 else if Z.eq_dec f 205%Z then Some (V293_InitEventList_function 204%Z 35%Z 36%Z 41%Z 42%Z 43%Z 44%Z)
 else if Z.eq_dec f 206%Z then Some (V293_FlagInit_function 204%Z 37%Z 38%Z 41%Z 42%Z 43%Z 44%Z)
 else if Z.eq_dec f 207%Z then Some (V293_MemInit_function 204%Z 39%Z 40%Z 41%Z 42%Z)
 else if Z.eq_dec f 204%Z then Some (V293_MemClr_function 11%Z 12%Z) else None.
Lemma SixLiteralOrder : V293_init_six_calls 201%Z 202%Z 203%Z 205%Z 206%Z 207%Z =
 sseq (sseq (sseq (sseq (scall 201%Z nil) (sseq (scall 202%Z nil) (scall 203%Z nil))) (scall 205%Z nil)) (scall 206%Z nil)) (scall 207%Z nil).
Proof. reflexivity. Qed.
Definition SixReadyZero := V293_rdy_globals 161%positive 162%positive 163%positive
  164%positive 165%positive 166%positive (Vint32 Int.zero) (Vint32 Int.zero)
  (Vint32 Int.zero) (Vint32 Int.zero) (Vint32 Int.zero) Vnull Vnull.
Definition SixExtraCells := SixReadyZero++V293_misc_zero_cells SixSlots++SixFrame.
Definition SixFinalCells := V293_mem_call_result 197%positive 196%positive
 (V293_flag_call_result 195%positive 194%positive
 (V293_event_call_result 193%positive 192%positive
  (V293_tcb_call_result 94%positive 95%positive 82%positive 84%positive SixExtraCells))).
Definition SixChecks := V293_mem_call_result 197%positive 196%positive []++
 V293_flag_call_result 195%positive 194%positive []++
 V293_event_call_result 193%positive 192%positive []++
 V293_tcb_call_heads 94%positive 95%positive Vnull (Vptr (82%positive,Int.zero))++
 V293_tcb_linked_next 82%positive++V293_null_pointer_cells 84%positive 0 13++SixExtraCells.
Lemma SixCheckCount : length SixChecks=208%nat.
Proof. reflexivity. Qed.
Lemma SixChecksValid : forall a tp v, In (a,tp,v) SixChecks -> rule_type_val_match tp v=true.
Proof.
 intros a tp v Member.
 cbn [SixChecks V293_mem_call_result V293_mem_call_head V293_mem_linked V293_mem_untouched_cells V293_flag_call_result V293_flag_call_head V293_flag_linked V293_flag_untouched_cells V293_event_call_result V293_event_call_head V293_event_linked
   V293_event_untouched_cells V293_clr_bytes repeat
   V293_tcb_call_heads V293_tcb_linked_next V293_null_pointer_cells seq map
   SixExtraCells SixReadyZero V293_rdy_globals V293_misc_zero_cells SixSlots
   V293_InitMisc_slots SixFrame init_block init_type app] in Member.
 repeat (destruct Member as [E | Member];[inversion E;subst;reflexivity | ]);contradiction.
Qed.
Lemma SixChecksInFinal : forall a tp v, In (a,tp,v) SixChecks -> In (a,tp,v) SixFinalCells.
Proof.
 intros a tp v Member.
 unfold SixChecks,SixFinalCells,V293_mem_call_result,V293_flag_call_result,V293_event_call_result,V293_tcb_call_result in *.
 repeat rewrite in_app_iff in *;cbn [In] in *;tauto.
Qed.
Lemma SixExtraCount : length SixExtraCells=21%nat.
Proof. reflexivity. Qed.
Lemma SixExtrasValid : forall a tp v,
 In (a,tp,v) SixExtraCells -> rule_type_val_match tp v=true.
Proof.
 intros a tp v Member.
 cbn [SixExtraCells SixReadyZero V293_rdy_globals V293_misc_zero_cells SixSlots
   V293_InitMisc_slots SixFrame map app init_block init_type] in Member.
 repeat (destruct Member as [E | Member];[inversion E;subst;reflexivity | ]);contradiction.
Qed.
Lemma SixReadyEnvironment : forall bi,
 V293_rdy_env SixGE (V293_rdy_locals 41%Z bi) 21%Z 22%Z 23%Z 24%Z 25%Z 26%Z 41%Z
 161%positive 162%positive 163%positive 164%positive 165%positive 166%positive bi.
Proof. intro bi. repeat split;reflexivity. Qed.
Lemma SixTCBEnvironment : forall bi bn b1 b2,
 V293_tcb_link_env SixGE (V293_tcb_call_locals 41%Z 42%Z 43%Z 44%Z bi bn b1 b2)
 31%Z 33%Z 34%Z 41%Z 42%Z 43%Z 44%Z 82%positive 94%positive 95%positive bi bn b1 b2.
Proof. intros. repeat split;reflexivity. Qed.
Lemma SixEventEnvironment : forall bi bn b1 b2,
 V293_event_link_env SixGE (V293_event_call_locals 41%Z 42%Z 43%Z 44%Z bi bn b1 b2)
 35%Z 36%Z 41%Z 42%Z 43%Z 44%Z 192%positive 193%positive bi bn b1 b2.
Proof. intros. repeat split;reflexivity. Qed.
Lemma SixFlagEnvironment : forall bi bn b1 b2,
 V293_flag_link_env SixGE (V293_flag_call_locals 41%Z 42%Z 43%Z 44%Z bi bn b1 b2)
 37%Z 38%Z 41%Z 42%Z 43%Z 44%Z 194%positive 195%positive bi bn b1 b2.
Proof. intros. repeat split;reflexivity. Qed.
Lemma SixMemEnvironment : forall bp bi,
 V293_mem_link_env SixGE (V293_mem_call_locals 41%Z 42%Z bp bi)
 39%Z 40%Z 41%Z 42%Z 196%positive 197%positive bp bi.
Proof. intros. repeat split;reflexivity. Qed.
Theorem SixConcreteExecution : forall ks, exists Mflag Mf bpl bil,
 cstepstar SixProgram (curs (V293_init_six_calls 201%Z 202%Z 203%Z 205%Z 206%Z 207%Z),(kenil,ks))
   (SixGE,SixCaller,SixEntryMemory) (curs (sskip None),(kenil,ks)) (SixGE,SixCaller,Mf) /\
 SixState Mf |= V293_rdy_raw_cells SixFinalCells Atrue /\
 (forall a tp v, In (a,tp,v) SixChecks -> load tp Mf a=Some v) /\
 cstepstar SixProgram (curs (V293_init_five_calls 201%Z 202%Z 203%Z 205%Z 206%Z),
   (kenil,kseq (scall 207%Z nil) ks)) (SixGE,SixCaller,SixEntryMemory)
   (curs (sskip None),(kenil,kseq (scall 207%Z nil) ks)) (SixGE,SixCaller,Mflag) /\
 cstepstar SixProgram (curs (scall 207%Z nil),(kenil,ks)) (SixGE,SixCaller,Mflag)
   (curs (sskip None),(kenil,ks)) (SixGE,SixCaller,Mf) /\ fresh Mflag bpl /\ fresh Mflag bil /\ bpl<>bil /\
 (forall c tp k, In (c,tp) [(bpl,Tptr V293_mem_type);(bil,Tint16)] ->
   (k<typelen tp)%nat -> get Mf (c,Z.of_nat k)=None).
Proof.
 intro ks.
 destruct (V293_OSInit_six_calls SixSlots (repeat Vundef 728)
   (repeat (Vint32 (Int.repr 255)) 52) (repeat (Vint32 (Int.repr 255)) 32) (repeat (Vint32 (Int.repr 255)) 60) (repeat (Vint32 (Int.repr 255)) 100) SixFrame
   SixProgram ks SixGE SixCaller SixEntryMemory
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
   ltac:(unfold SixSlots,V293_InitMisc_slots;repeat (apply Forall_cons;[unfold V293_init_scalar;cbn;auto | ]);apply Forall_nil)
   ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)
   ltac:(discriminate) ltac:(lia) ltac:(lia) ltac:(lia)
   SixReadyEnvironment SixTCBEnvironment ltac:(intros;reflexivity) ltac:(reflexivity)
   ltac:(apply repeat_length) ltac:(apply repeat_length)
   ltac:(reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) SixEventEnvironment ltac:(apply repeat_length)
   ltac:(reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) SixFlagEnvironment ltac:(apply repeat_length)
   ltac:(reflexivity) ltac:(lia) SixMemEnvironment ltac:(apply repeat_length)
   SixLiteralFullEntry)
   as (Mflag&Mf&bpl&bil&Exec&Prefix&Mem&Fp&Fi&Distinct&Owned&Freed).
 exists Mflag. exists Mf. exists bpl. exists bil.
 split;[exact Exec | ]. split;[exact Owned | ]. split.
 - intros a tp v Member. change (load tp (getmem (SixState Mf)) a=Some v).
   eapply (V293_rdy_raw_load SixFinalCells Atrue);
     [apply SixChecksInFinal;exact Member | exact (SixChecksValid a tp v Member) | exact Owned].
 - split;[exact Prefix | ]. split;[exact Mem | ].
   split;[exact Fp | ]. split;[exact Fi | ]. split;[exact Distinct | exact Freed].
Qed.
Theorem SixReturnConnections : forall ks, exists Mf,
 cstepstar SixProgram (curs (V293_init_six_calls 201%Z 202%Z 203%Z 205%Z 206%Z 207%Z),(kenil,ks))
   (SixGE,SixCaller,SixEntryMemory) (curs (sskip None),(kenil,ks)) (SixGE,SixCaller,Mf) /\
 load (Tptr Tvoid) Mf (196%positive,4)=Some (Vptr (196%positive,Int.repr 20)) /\
 load (Tptr V293_mem_type) Mf (197%positive,0)=Some (Vptr (196%positive,Int.zero)) /\
 load Tint8 Mf (161%positive,0)=Some (Vint32 Int.zero) /\
 load Tint32 Mf (99%positive,0)=Some (Vint32 (Int.repr 123)) /\
 load (Tptr Tvoid) Mf (196%positive,84)=Some Vnull /\
 load Tint32 Mf (110%positive,0)=Some (Vint32 (Int.repr 7)).
Proof.
 intro ks. destruct (SixConcreteExecution ks)
   as (Mflag&Mf&bpl&bil&Exec&Owned&Loads&Prefix&Mem&Fp&Fi&Distinct&Freed).
 exists Mf. split;[exact Exec | ]. repeat split;
 apply Loads;vm_compute;tauto.
Qed.
Print Assumptions SixConcreteExecution.

(* Prospective single-factor ablation: delete only the sixth call. *)
Theorem SixWithoutMemCall : forall ks, exists Mflag,
 cstepstar SixProgram (curs (V293_init_five_calls 201%Z 202%Z 203%Z 205%Z 206%Z),(kenil,ks))
   (SixGE,SixCaller,SixEntryMemory) (curs (sskip None),(kenil,ks)) (SixGE,SixCaller,Mflag) /\
 load Tint8 Mflag (196%positive,0)=Some (Vint32 (Int.repr 255)) /\
 load (Tptr V293_mem_type) Mflag (197%positive,0)=Some (Vptr (215%positive,Int.zero)) /\
 load Tint8 Mflag (194%positive,0)=Some (Vint32 Int.zero) /\
 load Tint8 Mflag (161%positive,0)=Some (Vint32 Int.zero) /\
 load Tint32 Mflag (99%positive,0)=Some (Vint32 (Int.repr 123)).
Proof.
 intro ks.
 destruct (V293_OSInit_five_calls SixSlots (repeat Vundef 728)
   (repeat (Vint32 (Int.repr 255)) 52) (repeat (Vint32 (Int.repr 255)) 32) (repeat (Vint32 (Int.repr 255)) 60) (SixMemBytes++SixMemHead++SixFrame)
   SixProgram ks SixGE SixCaller SixEntryMemory
   (fun _=>false) (false,nil,nil) emp (spec_done None)
   201%Z 202%Z 203%Z 204%Z 11%Z 12%Z 21%Z 22%Z 23%Z 24%Z 25%Z 26%Z 41%Z
   161%positive 162%positive 163%positive 164%positive 165%positive 166%positive
   31%Z 32%Z 33%Z 34%Z 41%Z 42%Z 43%Z 44%Z 82%positive 84%positive 94%positive 95%positive
   (Vint32 (Int.repr 7)) (Vint32 (Int.repr 3)) Vundef (Vint32 (Int.repr 5))
   (Vint32 (Int.repr 9)) (Vptr (211%positive,Int.zero)) (Vptr (212%positive,Int.zero))
   (Vptr (121%positive,Int.zero)) (Vptr (122%positive,Int.zero))
   205%Z 35%Z 36%Z 41%Z 42%Z 43%Z 44%Z 192%positive 193%positive (Vptr (213%positive,Int.zero))
   206%Z 37%Z 38%Z 41%Z 42%Z 43%Z 44%Z 194%positive 195%positive (Vptr (214%positive,Int.zero))
   ltac:(unfold SixSlots,V293_InitMisc_slots;repeat (apply Forall_cons;[unfold V293_init_scalar;cbn;auto | ]);apply Forall_nil)
   ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)
   ltac:(discriminate) ltac:(lia) ltac:(lia) ltac:(lia)
   SixReadyEnvironment SixTCBEnvironment ltac:(intros;reflexivity) ltac:(reflexivity)
   ltac:(apply repeat_length) ltac:(apply repeat_length)
   ltac:(reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) SixEventEnvironment ltac:(apply repeat_length)
   ltac:(reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) SixFlagEnvironment ltac:(apply repeat_length)
   SixLiteralFullEntry)
   as (Mevent&Mf&bi&bn&b1&b2&Exec&Prefix&Event&Fi&Fn&F1&F2&Owned&Freed).

 exists Mf. split;[exact Exec | ].
 set (result:=V293_flag_call_result 195%positive 194%positive
   (V293_event_call_result 193%positive 192%positive
    (V293_tcb_call_result 94%positive 95%positive 82%positive 84%positive
     (SixReadyZero++V293_misc_zero_cells SixSlots++SixMemBytes++SixMemHead++SixFrame)))).
 change (SixState Mf |= V293_rdy_raw_cells result Atrue) in Owned.
 assert (Load : forall a tp v, In (a,tp,v) result -> rule_type_val_match tp v=true -> load tp Mf a=Some v).
 { intros a tp v Member Valid. change (load tp (getmem (SixState Mf)) a=Some v).
   eapply (V293_rdy_raw_load result Atrue);eassumption. }
 split.
 - apply Load;[unfold result,V293_flag_call_result,V293_event_call_result,V293_tcb_call_result;
     do 10 (apply in_or_app;right);apply in_or_app;right;apply in_or_app;right;
     apply in_or_app;left;left;reflexivity | reflexivity].
 - split.
   + apply Load;[unfold result,V293_flag_call_result,V293_event_call_result,V293_tcb_call_result;
       do 10 (apply in_or_app;right);apply in_or_app;right;apply in_or_app;right;
       apply in_or_app;right;apply in_or_app;left;left;reflexivity | reflexivity].
   + split.
     * apply Load;[unfold result,V293_flag_call_result;
         apply in_or_app;right;apply in_or_app;left;left;reflexivity | reflexivity].
     * split.
       -- apply Load;[unfold result,V293_flag_call_result,V293_event_call_result,V293_tcb_call_result;
           do 10 (apply in_or_app;right);apply in_or_app;left;left;reflexivity | reflexivity].
       -- apply Load;[unfold result,V293_flag_call_result,V293_event_call_result,V293_tcb_call_result;
           do 10 (apply in_or_app;right);do 4 (apply in_or_app;right);
           unfold SixFrame;right;right;left;reflexivity | reflexivity].
Qed.
Print Assumptions SixWithoutMemCall.
