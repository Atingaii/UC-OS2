(* Whole call: independently encoded finite entry, absent callee locals, nonempty shadowed caller. *)
Require Import CertiOS.framework.include_frm.
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
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope Z_scope.
Definition ChainSlots := V293_InitMisc_slots 1001%Z 1002%Z 1003%Z 1004%Z 1005%Z 1006%Z 1007%Z 1008%Z 1009%Z 1010%Z 181%positive 182%positive 183%positive 184%positive 185%positive 186%positive 187%positive 188%positive 189%positive 190%positive.
Definition ChainGE : env := fold_right
  (fun d e=>set e (init_name d) (init_block d,init_type d))
  (set (set (set (set (set (set
  (set (set (set (set emp 31%Z (82%positive,Tarray V293_tcb_type 13))
   32%Z (84%positive,Tarray (Tptr V293_tcb_type) 13))
   33%Z (94%positive,Tptr V293_tcb_type)) 34%Z (95%positive,Tptr V293_tcb_type))
   21%Z (161%positive,Tint8)) 22%Z (162%positive,Tarray Tint8 2))
   23%Z (163%positive,Tint8)) 24%Z (164%positive,Tint8))
   25%Z (165%positive,Tptr V293_tcb_type)) 26%Z (166%positive,Tptr V293_tcb_type)) ChainSlots.
Definition ChainTCB := V293_encoded_memory 82%positive 0 true (repeat Undef 728).
Definition ChainPrio := V293_encoded_memory 84%positive 0 true (repeat (Byte (Byte.repr 255)) 52).
Definition ChainHeads : list V293_record_cell :=
  [((94%positive,0),Tptr V293_tcb_type,Vptr (121%positive,Int.zero));
   ((95%positive,0),Tptr V293_tcb_type,Vptr (122%positive,Int.zero))].
Definition ChainReady : list V293_record_cell :=
 [((161%positive,0),Tint8,Vint32 (Int.repr 7));
  ((162%positive,0),Tint8,Vint32 (Int.repr 3));
  ((162%positive,1),Tint8,Vundef);
  ((163%positive,0),Tint8,Vint32 (Int.repr 5));
  ((164%positive,0),Tint8,Vint32 (Int.repr 9));
  ((165%positive,0),Tptr V293_tcb_type,Vptr (211%positive,Int.zero));
  ((166%positive,0),Tptr V293_tcb_type,Vptr (212%positive,Int.zero))].
Definition ChainKernelCells := ChainHeads++ChainReady.
Definition ChainFrame : list V293_record_cell :=
  [((82%positive,728),Tint8,Vint32 (Int.repr 17));
   ((84%positive,52),Tint8,Vint32 (Int.repr 29));
   ((99%positive,0),Tint32,Vint32 (Int.repr 123));
   ((110%positive,0),Tint32,Vint32 (Int.repr 7))].
Fixpoint ChainMem (cells : list V293_record_cell) : mem :=
  match cells with []=>emp | ((b,off),tp,v)::tail=>
    merge (V293_encoded_memory b off true (encode_val tp v)) (ChainMem tail) end.
Definition ChainMemory := merge ChainTCB (merge ChainPrio (ChainMem (ChainKernelCells++ChainFrame))).
Definition ChainCaller : env := set emp 41%Z (110%positive,Tint32).
Definition ChainState M := V293_wstate ChainGE ChainCaller M.

Lemma ChainConstantRange : forall n v byte ge le b off,
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
Ltac ChainOutside :=
  unfold ChainTCB,ChainPrio;
  cbn [ChainKernelCells ChainHeads ChainReady ChainFrame ChainMem app];
  repeat first [rewrite V293_encoded_memory_outside by
    (first [left;congruence | right;rewrite ?repeat_length;cbn [length encode_val inj_bytes encode_int];lia])
    | rewrite map_merge_semp by reflexivity];
  reflexivity.
Ltac ChainApart b :=
  apply map_join_merge;apply map_disjoint;intros [other off];
  destruct (Pos.eq_dec other b);[subst other;right;left | left];
  repeat first [rewrite V293_encoded_memory_outside by (left;congruence)
    | rewrite map_merge_semp by reflexivity];reflexivity.
Lemma ChainLiteralEntry : ChainState ChainMemory |= V293_rdy_raw_cells
  (V293_clr_bytes 82%positive 0 (repeat Vundef 728)++
   V293_clr_bytes 84%positive 0 (repeat (Vint32 (Int.repr 255)) 52)++ChainKernelCells++ChainFrame) Atrue.
Proof.
  unfold ChainState,ChainMemory. repeat rewrite V293_raw_cells_append.
  apply (V293_raw_cells_join (V293_clr_bytes 82%positive 0 (repeat Vundef 728))
    (V293_rdy_raw_cells (V293_clr_bytes 84%positive 0 (repeat (Vint32 (Int.repr 255)) 52))
      (V293_rdy_raw_cells ChainKernelCells (V293_rdy_raw_cells ChainFrame Atrue)))).
  eapply V293_wstate_star with (m1:=ChainTCB).
  - apply map_join_merge;apply map_disjoint;intros [b i].
    destruct (Pos.eq_dec b 82%positive) as [B|B].
    + subst b. destruct (Z_lt_dec i 728) as [I|I].
      * right;left;ChainOutside.
      * left. unfold ChainTCB. apply V293_encoded_memory_outside. right;right. rewrite repeat_length;lia.
    + left. unfold ChainTCB. apply V293_encoded_memory_outside;left;exact B.
  - unfold ChainTCB;apply ChainConstantRange;reflexivity.
  - apply (V293_raw_cells_join (V293_clr_bytes 84%positive 0 (repeat (Vint32 (Int.repr 255)) 52))
      (V293_rdy_raw_cells ChainKernelCells (V293_rdy_raw_cells ChainFrame Atrue))).
    eapply V293_wstate_star with (m1:=ChainPrio).
    + apply map_join_merge;apply map_disjoint;intros [b i].
      destruct (Pos.eq_dec b 84%positive) as [B|B].
      * subst b. destruct (Z_lt_dec i 52) as [I|I].
        -- right;left;ChainOutside.
        -- left. unfold ChainPrio. apply V293_encoded_memory_outside. right;right. rewrite repeat_length;lia.
      * left. unfold ChainPrio. apply V293_encoded_memory_outside;left;exact B.
    + unfold ChainPrio;apply ChainConstantRange;reflexivity.
    + cbn [ChainKernelCells ChainHeads ChainReady ChainFrame ChainMem app V293_rdy_raw_cells].
      eapply V293_wstate_star with (m1:=V293_encoded_memory 94%positive 0 true (encode_val (Tptr V293_tcb_type) (Vptr (121%positive,Int.zero))));
        [ChainApart 94%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
      eapply V293_wstate_star with (m1:=V293_encoded_memory 95%positive 0 true (encode_val (Tptr V293_tcb_type) (Vptr (122%positive,Int.zero))));
        [ChainApart 95%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
      eapply V293_wstate_star with (m1:=V293_encoded_memory 161%positive 0 true (encode_val (Tint8) (Vint32 (Int.repr 7)))).
      { ChainApart 161%positive. }
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
      { ChainApart 162%positive. }
      { split;[apply V293_encoded_memory_mapsto | reflexivity]. }
      eapply V293_wstate_star with (m1:=V293_encoded_memory 163%positive 0 true (encode_val (Tint8) (Vint32 (Int.repr 5)))).
      { ChainApart 163%positive. }
      { split;[apply V293_encoded_memory_mapsto | reflexivity]. }
      eapply V293_wstate_star with (m1:=V293_encoded_memory 164%positive 0 true (encode_val (Tint8) (Vint32 (Int.repr 9)))).
      { ChainApart 164%positive. }
      { split;[apply V293_encoded_memory_mapsto | reflexivity]. }
      eapply V293_wstate_star with (m1:=V293_encoded_memory 165%positive 0 true (encode_val (Tptr V293_tcb_type) (Vptr (211%positive,Int.zero)))).
      { ChainApart 165%positive. }
      { split;[apply V293_encoded_memory_mapsto | reflexivity]. }
      eapply V293_wstate_star with (m1:=V293_encoded_memory 166%positive 0 true (encode_val (Tptr V293_tcb_type) (Vptr (212%positive,Int.zero)))).
      { ChainApart 166%positive. }
      { split;[apply V293_encoded_memory_mapsto | reflexivity]. }
      eapply V293_wstate_star with (m1:=V293_encoded_memory 82%positive 728 true (encode_val (Tint8) (Vint32 (Int.repr 17))));
        [ChainApart 82%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
      eapply V293_wstate_star with (m1:=V293_encoded_memory 84%positive 52 true (encode_val (Tint8) (Vint32 (Int.repr 29))));
        [ChainApart 84%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
      eapply V293_wstate_star with (m1:=V293_encoded_memory 99%positive 0 true (encode_val (Tint32) (Vint32 (Int.repr 123))));
        [ChainApart 99%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
      eapply V293_wstate_star with (m1:=V293_encoded_memory 110%positive 0 true (encode_val Tint32 (Vint32 (Int.repr 7))));
        [ChainApart 110%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
      exact I.
Qed.
Definition ChainTail := V293_rdy_globals 161%positive 162%positive 163%positive 164%positive 165%positive 166%positive
  (Vint32 (Int.repr 7)) (Vint32 (Int.repr 3)) Vundef (Vint32 (Int.repr 5))
  (Vint32 (Int.repr 9)) (Vptr (211%positive,Int.zero)) (Vptr (212%positive,Int.zero))++
  V293_clr_bytes 82%positive 0 (repeat Vundef 728)++
  V293_clr_bytes 84%positive 0 (repeat (Vint32 (Int.repr 255)) 52)++ChainHeads++ChainFrame.
Definition ChainMiscCells : list (block*type*val) :=
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
Fixpoint ChainMiscMem cells : mem := match cells with
 | []=>ChainMemory | (b,tp,v)::tail=>merge (V293_encoded_memory b 0 true (encode_val tp v)) (ChainMiscMem tail) end.
Definition ChainEntryMemory := ChainMiscMem ChainMiscCells.
Lemma ChainRawTail : ChainState ChainMemory |= V293_rdy_raw_cells ChainTail Atrue.
Proof.
  pose proof ChainLiteralEntry as H. unfold ChainTail.
  change (ChainState ChainMemory |= V293_rdy_raw_cells
    (ChainReady++V293_clr_bytes 82%positive 0 (repeat Vundef 728)++
     V293_clr_bytes 84%positive 0 (repeat (Vint32 (Int.repr 255)) 52)++ChainHeads++ChainFrame) Atrue).
  unfold ChainKernelCells in H. repeat rewrite V293_raw_cells_append in *.
  apply (V293_raw_cells_mono _ _ _ (V293_raw_cells_mono _ _ _ (V293_raw_cells_swap _ _ _))) in H.
  apply (V293_raw_cells_mono _ _ _ (V293_raw_cells_swap _ _ _)) in H.
  apply V293_raw_cells_swap in H. exact H.
Qed.
Lemma ChainSlotEntry : forall x tp b v,
 get ChainGE x=Some (b,tp) ->
 V293_wstate ChainGE emp (V293_encoded_memory b 0 true (encode_val tp v)) |=
  V293_init_binding (Build_V293_init_slot x tp b) ** V293_init_memory (Build_V293_init_slot x tp b) false.
Proof.
 intros x tp b v Env. eapply V293_wstate_star with (m1:=emp) (m2:=V293_encoded_memory b 0 true (encode_val tp v)).
 - apply map_join_comm;apply map_join_emp.
 - split.
   + exists b. split;[exact Env | ]. repeat split;reflexivity.
   + split;[intros [w E];change (None=Some w) in E;discriminate | split;reflexivity].
 - exists v. split;[apply V293_encoded_memory_mapsto | reflexivity].
Qed.
Theorem ChainLiteralFullEntry : V293_wstate ChainGE emp ChainEntryMemory |=
  V293_init_resources ChainSlots false (V293_rdy_raw_cells ChainTail Atrue).
Proof.
 unfold ChainEntryMemory,ChainMiscCells,ChainSlots,V293_InitMisc_slots.
 cbn [ChainMiscMem V293_init_resources].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 181%positive 0 true (encode_val (Tint32) (Vint32 (Int.repr 57)))).
 { apply map_join_merge;apply map_disjoint;intros [other off].
   destruct (Pos.eq_dec other 181%positive);[subst other;right;left | left];
   unfold ChainMemory,ChainTCB,ChainPrio;cbn [ChainKernelCells ChainHeads ChainReady ChainFrame ChainMem app];
   repeat first [rewrite V293_encoded_memory_outside by (left;congruence)
     | rewrite map_merge_semp by reflexivity];reflexivity. }
 { apply ChainSlotEntry;vm_compute;reflexivity. }
 eapply V293_wstate_star with (m1:=V293_encoded_memory 182%positive 0 true (encode_val (Tint8) (Vint32 (Int.repr 3)))).
 { apply map_join_merge;apply map_disjoint;intros [other off].
   destruct (Pos.eq_dec other 182%positive);[subst other;right;left | left];
   unfold ChainMemory,ChainTCB,ChainPrio;cbn [ChainKernelCells ChainHeads ChainReady ChainFrame ChainMem app];
   repeat first [rewrite V293_encoded_memory_outside by (left;congruence)
     | rewrite map_merge_semp by reflexivity];reflexivity. }
 { apply ChainSlotEntry;vm_compute;reflexivity. }
 eapply V293_wstate_star with (m1:=V293_encoded_memory 183%positive 0 true (encode_val (Tint8) (Vint32 (Int.repr 2)))).
 { apply map_join_merge;apply map_disjoint;intros [other off].
   destruct (Pos.eq_dec other 183%positive);[subst other;right;left | left];
   unfold ChainMemory,ChainTCB,ChainPrio;cbn [ChainKernelCells ChainHeads ChainReady ChainFrame ChainMem app];
   repeat first [rewrite V293_encoded_memory_outside by (left;congruence)
     | rewrite map_merge_semp by reflexivity];reflexivity. }
 { apply ChainSlotEntry;vm_compute;reflexivity. }
 eapply V293_wstate_star with (m1:=V293_encoded_memory 184%positive 0 true (encode_val (Tint8) (Vint32 (Int.repr 9)))).
 { apply map_join_merge;apply map_disjoint;intros [other off].
   destruct (Pos.eq_dec other 184%positive);[subst other;right;left | left];
   unfold ChainMemory,ChainTCB,ChainPrio;cbn [ChainKernelCells ChainHeads ChainReady ChainFrame ChainMem app];
   repeat first [rewrite V293_encoded_memory_outside by (left;congruence)
     | rewrite map_merge_semp by reflexivity];reflexivity. }
 { apply ChainSlotEntry;vm_compute;reflexivity. }
 eapply V293_wstate_star with (m1:=V293_encoded_memory 185%positive 0 true (encode_val (Tint8) (Vint32 Int.one))).
 { apply map_join_merge;apply map_disjoint;intros [other off].
   destruct (Pos.eq_dec other 185%positive);[subst other;right;left | left];
   unfold ChainMemory,ChainTCB,ChainPrio;cbn [ChainKernelCells ChainHeads ChainReady ChainFrame ChainMem app];
   repeat first [rewrite V293_encoded_memory_outside by (left;congruence)
     | rewrite map_merge_semp by reflexivity];reflexivity. }
 { apply ChainSlotEntry;vm_compute;reflexivity. }
 eapply V293_wstate_star with (m1:=V293_encoded_memory 186%positive 0 true (encode_val (Tint32) (Vint32 (Int.repr 42)))).
 { apply map_join_merge;apply map_disjoint;intros [other off].
   destruct (Pos.eq_dec other 186%positive);[subst other;right;left | left];
   unfold ChainMemory,ChainTCB,ChainPrio;cbn [ChainKernelCells ChainHeads ChainReady ChainFrame ChainMem app];
   repeat first [rewrite V293_encoded_memory_outside by (left;congruence)
     | rewrite map_merge_semp by reflexivity];reflexivity. }
 { apply ChainSlotEntry;vm_compute;reflexivity. }
 eapply V293_wstate_star with (m1:=V293_encoded_memory 187%positive 0 true (encode_val (Tint32) (Vundef))).
 { apply map_join_merge;apply map_disjoint;intros [other off].
   destruct (Pos.eq_dec other 187%positive);[subst other;right;left | left];
   unfold ChainMemory,ChainTCB,ChainPrio;cbn [ChainKernelCells ChainHeads ChainReady ChainFrame ChainMem app];
   repeat first [rewrite V293_encoded_memory_outside by (left;congruence)
     | rewrite map_merge_semp by reflexivity];reflexivity. }
 { apply ChainSlotEntry;vm_compute;reflexivity. }
 eapply V293_wstate_star with (m1:=V293_encoded_memory 188%positive 0 true (encode_val (Tint32) (Vundef))).
 { apply map_join_merge;apply map_disjoint;intros [other off].
   destruct (Pos.eq_dec other 188%positive);[subst other;right;left | left];
   unfold ChainMemory,ChainTCB,ChainPrio;cbn [ChainKernelCells ChainHeads ChainReady ChainFrame ChainMem app];
   repeat first [rewrite V293_encoded_memory_outside by (left;congruence)
     | rewrite map_merge_semp by reflexivity];reflexivity. }
 { apply ChainSlotEntry;vm_compute;reflexivity. }
 eapply V293_wstate_star with (m1:=V293_encoded_memory 189%positive 0 true (encode_val (Tint32) (Vint32 (Int.repr 100)))).
 { apply map_join_merge;apply map_disjoint;intros [other off].
   destruct (Pos.eq_dec other 189%positive);[subst other;right;left | left];
   unfold ChainMemory,ChainTCB,ChainPrio;cbn [ChainKernelCells ChainHeads ChainReady ChainFrame ChainMem app];
   repeat first [rewrite V293_encoded_memory_outside by (left;congruence)
     | rewrite map_merge_semp by reflexivity];reflexivity. }
 { apply ChainSlotEntry;vm_compute;reflexivity. }
 eapply V293_wstate_star with (m1:=V293_encoded_memory 190%positive 0 true (encode_val (Tint8) (Vint32 Int.one))).
 { apply map_join_merge;apply map_disjoint;intros [other off].
   destruct (Pos.eq_dec other 190%positive);[subst other;right;left | left];
   unfold ChainMemory,ChainTCB,ChainPrio;cbn [ChainKernelCells ChainHeads ChainReady ChainFrame ChainMem app];
   repeat first [rewrite V293_encoded_memory_outside by (left;congruence)
     | rewrite map_merge_semp by reflexivity];reflexivity. }
 { apply ChainSlotEntry;vm_compute;reflexivity. }
 eapply V293_raw_cells_environment;[right;reflexivity | exact ChainRawTail].
Qed.
Definition ChainProgram f :=
 if Z.eq_dec f 201%Z then Some (V293_InitMisc_function 1001%Z 1002%Z 1003%Z 1004%Z 1005%Z 1006%Z 1007%Z 1008%Z 1009%Z 1010%Z)
 else if Z.eq_dec f 202%Z then Some (V293_InitRdyList_function 21%Z 22%Z 23%Z 24%Z 25%Z 26%Z 41%Z)
 else if Z.eq_dec f 203%Z then Some (V293_InitTCBList_function 204%Z 31%Z 32%Z 33%Z 34%Z 41%Z 42%Z 43%Z 44%Z)
 else if Z.eq_dec f 204%Z then Some (V293_MemClr_function 11%Z 12%Z) else None.
Lemma ChainLiteralOrder : V293_init_three_calls 201%Z 202%Z 203%Z =
 sseq (scall 201%Z nil) (sseq (scall 202%Z nil) (scall 203%Z nil)).
Proof. reflexivity. Qed.

Definition ChainReadyZero := V293_rdy_globals 161%positive 162%positive 163%positive
  164%positive 165%positive 166%positive (Vint32 Int.zero) (Vint32 Int.zero)
  (Vint32 Int.zero) (Vint32 Int.zero) (Vint32 Int.zero) Vnull Vnull.
Definition ChainExtraCells := ChainReadyZero++V293_misc_zero_cells ChainSlots++ChainFrame.
Definition ChainFinalCells := V293_tcb_call_result 94%positive 95%positive 82%positive 84%positive ChainExtraCells.
Lemma ChainExtraCount : length ChainExtraCells=21%nat.
Proof. reflexivity. Qed.
Lemma ChainExtrasValid : forall a tp v,
 In (a,tp,v) ChainExtraCells -> rule_type_val_match tp v=true.
Proof.
 intros a tp v Member.
 cbn [ChainExtraCells ChainReadyZero V293_rdy_globals V293_misc_zero_cells ChainSlots
   V293_InitMisc_slots ChainFrame map app init_block init_type] in Member.
 repeat (destruct Member as [E | Member];[inversion E;subst;reflexivity | ]);contradiction.
Qed.
Lemma ChainReadyEnvironment : forall bi,
 V293_rdy_env ChainGE (V293_rdy_locals 41%Z bi) 21%Z 22%Z 23%Z 24%Z 25%Z 26%Z 41%Z
 161%positive 162%positive 163%positive 164%positive 165%positive 166%positive bi.
Proof. intro bi. repeat split;reflexivity. Qed.
Lemma ChainTCBEnvironment : forall bi bn b1 b2,
 V293_tcb_link_env ChainGE (V293_tcb_call_locals 41%Z 42%Z 43%Z 44%Z bi bn b1 b2)
 31%Z 33%Z 34%Z 41%Z 42%Z 43%Z 44%Z 82%positive 94%positive 95%positive bi bn b1 b2.
Proof. intros. repeat split;reflexivity. Qed.
Ltac ChainRead H :=
  lazymatch goal with |- load ?tp ?M ?a=Some ?v =>
    change (load tp (getmem (ChainState M)) a=Some v);
    eapply (V293_rdy_raw_load ChainFinalCells Atrue);[ | reflexivity | exact H]
  end.
(* The 49 load instances are 12 links, last NULL, two heads, thirteen
   priority slots, seven ready cells, ten Misc cells and four frame cells. *)
Theorem ChainConcreteExecution : forall ks, exists Mmisc Mrdy Mf bri bi bn b1 b2,
 cstepstar ChainProgram (curs (V293_init_three_calls 201%Z 202%Z 203%Z),(kenil,ks))
   (ChainGE,ChainCaller,ChainEntryMemory) (curs (sskip None),(kenil,ks)) (ChainGE,ChainCaller,Mf) /\
 ChainState Mf |= V293_rdy_raw_cells ChainFinalCells Atrue /\
 (forall i, (i<12)%nat -> load (Tcom_ptr 410) Mf (82%positive,56*Z.of_nat i+20)=
    Some (Vptr (82%positive,Int.repr (56*Z.of_nat (S i))))) /\
 load (Tcom_ptr 410) Mf (82%positive,692)=Some Vnull /\
 load (Tptr V293_tcb_type) Mf (94%positive,0)=Some Vnull /\
 load (Tptr V293_tcb_type) Mf (95%positive,0)=Some (Vptr (82%positive,Int.zero)) /\
 (forall p, (p<13)%nat -> load (Tptr V293_tcb_type) Mf (84%positive,4*Z.of_nat p)=Some Vnull) /\
 (forall a tp v, In (a,tp,v) ChainExtraCells -> load tp Mf a=Some v) /\
 get Mrdy (bri,0)=None /\
 (forall c tp k, In (c,tp) [(bi,Tint8);(bn,Tint8);(b1,Tptr V293_tcb_type);(b2,Tptr V293_tcb_type)] ->
   (k<typelen tp)%nat -> get Mf (c,Z.of_nat k)=None) /\
 cstepstar ChainProgram (curs (scall 201%Z nil),
   (kenil,kseq (sseq (scall 202%Z nil) (scall 203%Z nil)) ks)) (ChainGE,ChainCaller,ChainEntryMemory)
   (curs (sskip None),(kenil,kseq (sseq (scall 202%Z nil) (scall 203%Z nil)) ks)) (ChainGE,ChainCaller,Mmisc).
Proof.
 intro ks.
 destruct (V293_OSInit_three_calls ChainSlots (repeat Vundef 728)
   (repeat (Vint32 (Int.repr 255)) 52) ChainFrame ChainProgram ks ChainGE ChainCaller ChainEntryMemory
   (fun _=>false) (false,nil,nil) emp (spec_done None)
   201%Z 202%Z 203%Z 204%Z 11%Z 12%Z 21%Z 22%Z 23%Z 24%Z 25%Z 26%Z 41%Z
   161%positive 162%positive 163%positive 164%positive 165%positive 166%positive
   31%Z 32%Z 33%Z 34%Z 41%Z 42%Z 43%Z 44%Z 82%positive 84%positive 94%positive 95%positive
   (Vint32 (Int.repr 7)) (Vint32 (Int.repr 3)) Vundef (Vint32 (Int.repr 5))
   (Vint32 (Int.repr 9)) (Vptr (211%positive,Int.zero)) (Vptr (212%positive,Int.zero))
   (Vptr (121%positive,Int.zero)) (Vptr (122%positive,Int.zero))
   ltac:(unfold ChainSlots,V293_InitMisc_slots;repeat (apply Forall_cons;[unfold V293_init_scalar;cbn;auto | ]);apply Forall_nil)
   ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)
   ltac:(discriminate) ltac:(lia) ltac:(lia) ltac:(lia)
   ChainReadyEnvironment ChainTCBEnvironment ltac:(intros;reflexivity) ltac:(reflexivity)
   ltac:(apply repeat_length) ltac:(apply repeat_length) ChainLiteralFullEntry)
   as (Mmisc&Mrdy&Mf&bri&bi&bn&b1&b2&Exec&MiscExec&ReadyExec&TCBExec&Final&ReadyFreed&TCBFreed).
 exists Mmisc. exists Mrdy. exists Mf. exists bri. exists bi. exists bn. exists b1. exists b2.
 split;[exact Exec | ]. split;[exact Final | ].
 split.
 - intros i Small. ChainRead Final. unfold ChainFinalCells,V293_tcb_call_result.
   apply in_or_app;right. apply in_or_app;left. unfold V293_tcb_linked_next.
   apply in_or_app;left. apply in_map_iff. exists i. split;[reflexivity | apply in_seq;lia].
 - split.
   + ChainRead Final. unfold ChainFinalCells,V293_tcb_call_result.
     apply in_or_app;right. apply in_or_app;left. unfold V293_tcb_linked_next.
     apply in_or_app;right;left;reflexivity.
   + split.
     * ChainRead Final. unfold ChainFinalCells,V293_tcb_call_result. apply in_or_app;left;left;reflexivity.
     * split.
       -- ChainRead Final. unfold ChainFinalCells,V293_tcb_call_result. apply in_or_app;left;right;left;reflexivity.
       -- split.
          ++ intros p Small. ChainRead Final. unfold ChainFinalCells,V293_tcb_call_result.
             do 3 (apply in_or_app;right). apply in_or_app;left.
             replace (4*Z.of_nat p) with (0+4*Z.of_nat p) by lia.
             apply V293_null_pointer_member;exact Small.
          ++ split.
             ** intros a tp v Member. pose proof (ChainExtrasValid a tp v Member) as Valid. change (load tp (getmem (ChainState Mf)) a=Some v).
                eapply (V293_rdy_raw_load ChainFinalCells Atrue);[ | exact Valid | exact Final].
                unfold ChainFinalCells,V293_tcb_call_result. do 4 (apply in_or_app;right). exact Member.
             ** split;[exact ReadyFreed | ]. split;[exact TCBFreed | exact MiscExec].
Qed.
(* Single final-conclusion controls; unchanged execution proof and fixture. *)
Theorem ChainReturnConnections : forall ks, exists Mf,
 cstepstar ChainProgram (curs (V293_init_three_calls 201%Z 202%Z 203%Z),(kenil,ks))
   (ChainGE,ChainCaller,ChainEntryMemory) (curs (sskip None),(kenil,ks)) (ChainGE,ChainCaller,Mf) /\
 load Tint32 Mf (181%positive,0)=Some (Vint32 Int.zero) /\
 load Tint8 Mf (161%positive,0)=Some (Vint32 Int.zero) /\
 load Tint32 Mf (99%positive,0)=Some (Vint32 (Int.repr 123)).
Proof.
 intro ks. destruct (ChainConcreteExecution ks)
  as (Mmisc&Mrdy&Mf&bri&bi&bn&b1&b2&Exec&Owned&Links&Last&Head&Free&Prios&Extras&ReadyFreed&TCBFreed&MiscExec).
 exists Mf. split;[exact Exec | ]. split.
 - apply Extras;vm_compute;tauto.
 - split.
   + apply Extras;vm_compute;tauto.
   + apply Extras;vm_compute;tauto.
Qed.
Print Assumptions ChainLiteralFullEntry.
Print Assumptions ChainLiteralOrder.
Print Assumptions ChainConcreteExecution.
Print Assumptions ChainReturnConnections.
