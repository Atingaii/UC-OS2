(* Whole call: independently encoded finite entry, absent callee locals, nonempty shadowed caller. *)
Require Import CertiOS.framework.include_frm.
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
Definition FiveSlots := V293_InitMisc_slots 1001%Z 1002%Z 1003%Z 1004%Z 1005%Z 1006%Z 1007%Z 1008%Z 1009%Z 1010%Z 181%positive 182%positive 183%positive 184%positive 185%positive 186%positive 187%positive 188%positive 189%positive 190%positive.
Definition FiveGE : env := fold_right
  (fun d e=>set e (init_name d) (init_block d,init_type d))
  (set (set (set (set (set (set (set (set
  (set (set (set (set (set (set emp 37%Z (194%positive,V293_flag_table_type)) 38%Z (195%positive,Tptr V293_flag_type)) 35%Z (192%positive,V293_event_table_type)) 36%Z (193%positive,Tptr V293_event_type)) 31%Z (82%positive,Tarray V293_tcb_type 13))
   32%Z (84%positive,Tarray (Tptr V293_tcb_type) 13))
   33%Z (94%positive,Tptr V293_tcb_type)) 34%Z (95%positive,Tptr V293_tcb_type))
   21%Z (161%positive,Tint8)) 22%Z (162%positive,Tarray Tint8 2))
   23%Z (163%positive,Tint8)) 24%Z (164%positive,Tint8))
   25%Z (165%positive,Tptr V293_tcb_type)) 26%Z (166%positive,Tptr V293_tcb_type)) FiveSlots.
Definition FiveTCB := V293_encoded_memory 82%positive 0 true (repeat Undef 728).
Definition FivePrio := V293_encoded_memory 84%positive 0 true (repeat (Byte (Byte.repr 255)) 52).
Definition FiveHeads : list V293_record_cell :=
  [((94%positive,0),Tptr V293_tcb_type,Vptr (121%positive,Int.zero));
   ((95%positive,0),Tptr V293_tcb_type,Vptr (122%positive,Int.zero))].
Definition FiveReady : list V293_record_cell :=
 [((161%positive,0),Tint8,Vint32 (Int.repr 7));
  ((162%positive,0),Tint8,Vint32 (Int.repr 3));
  ((162%positive,1),Tint8,Vundef);
  ((163%positive,0),Tint8,Vint32 (Int.repr 5));
  ((164%positive,0),Tint8,Vint32 (Int.repr 9));
  ((165%positive,0),Tptr V293_tcb_type,Vptr (211%positive,Int.zero));
  ((166%positive,0),Tptr V293_tcb_type,Vptr (212%positive,Int.zero))].
Definition FiveEventHead := V293_event_call_head 193%positive (Vptr (213%positive,Int.zero)).
Definition FiveFlagHead := V293_flag_call_head 195%positive (Vptr (214%positive,Int.zero)).
Definition FiveKernelCells := FiveHeads++FiveReady++FiveEventHead++FiveFlagHead.
Definition FiveFlag := V293_encoded_memory 194%positive 0 true (repeat (Byte (Byte.repr 255)) 60).
Definition FiveFlagBytes := V293_clr_bytes 194%positive 0 (repeat (Vint32 (Int.repr 255)) 60).
Definition FiveEvent := V293_encoded_memory 192%positive 0 true (repeat (Byte (Byte.repr 255)) 32).
Definition FiveEventBytes := V293_clr_bytes 192%positive 0 (repeat (Vint32 (Int.repr 255)) 32).
Definition FiveFrame : list V293_record_cell :=
  [((82%positive,728),Tint8,Vint32 (Int.repr 17));
   ((84%positive,52),Tint8,Vint32 (Int.repr 29));
   ((99%positive,0),Tint32,Vint32 (Int.repr 123));
   ((110%positive,0),Tint32,Vint32 (Int.repr 7))].
Fixpoint FiveMem (cells : list V293_record_cell) : mem :=
  match cells with []=>emp | ((b,off),tp,v)::tail=>
    merge (V293_encoded_memory b off true (encode_val tp v)) (FiveMem tail) end.
Definition FiveMemory := merge FiveFlag (merge FiveEvent (merge FiveTCB (merge FivePrio (FiveMem (FiveKernelCells++FiveFrame))))).
Definition FiveCaller : env := set emp 41%Z (110%positive,Tint32).
Definition FiveState M := V293_wstate FiveGE FiveCaller M.

Lemma FiveConstantRange : forall n v byte ge le b off,
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
Ltac FiveOutside :=
  unfold FiveFlag,FiveEvent,FiveTCB,FivePrio;
  cbn [FiveKernelCells FiveHeads FiveReady FiveEventHead V293_event_call_head FiveFlagHead V293_flag_call_head FiveFrame FiveMem app];
  repeat first [rewrite V293_encoded_memory_outside by
    (first [left;congruence | right;rewrite ?repeat_length;cbn [length encode_val inj_bytes encode_int];lia])
    | rewrite map_merge_semp by reflexivity];
  reflexivity.
Ltac FiveApart b :=
  apply map_join_merge;apply map_disjoint;intros [other off];
  destruct (Pos.eq_dec other b);[subst other;right;left | left];
  repeat first [rewrite V293_encoded_memory_outside by (left;congruence)
    | rewrite map_merge_semp by reflexivity];reflexivity.
Lemma FiveLiteralEntry : FiveState FiveMemory |= V293_rdy_raw_cells
  (FiveFlagBytes++FiveEventBytes++V293_clr_bytes 82%positive 0 (repeat Vundef 728)++
   V293_clr_bytes 84%positive 0 (repeat (Vint32 (Int.repr 255)) 52)++FiveKernelCells++FiveFrame) Atrue.
Proof.
  unfold FiveState,FiveMemory. repeat rewrite V293_raw_cells_append.
  apply (V293_raw_cells_join FiveFlagBytes
    (V293_rdy_raw_cells (FiveEventBytes++V293_clr_bytes 82%positive 0 (repeat Vundef 728)++
      V293_clr_bytes 84%positive 0 (repeat (Vint32 (Int.repr 255)) 52)++FiveKernelCells++FiveFrame) Atrue)).
  eapply V293_wstate_star with (m1:=FiveFlag).
  { apply map_join_merge;apply map_disjoint;intros [b i].
    destruct (Pos.eq_dec b 194%positive) as [B|B].
    - subst b. right;left;FiveOutside.
    - left. unfold FiveFlag. apply V293_encoded_memory_outside;left;exact B. }
  { unfold FiveFlagBytes,FiveFlag;apply FiveConstantRange;reflexivity. }
  repeat rewrite V293_raw_cells_append.
  apply (V293_raw_cells_join FiveEventBytes
    (V293_rdy_raw_cells (V293_clr_bytes 82%positive 0 (repeat Vundef 728))
      (V293_rdy_raw_cells (V293_clr_bytes 84%positive 0 (repeat (Vint32 (Int.repr 255)) 52))
        (V293_rdy_raw_cells FiveKernelCells (V293_rdy_raw_cells FiveFrame Atrue))))).
  eapply V293_wstate_star with (m1:=FiveEvent).
  { apply map_join_merge;apply map_disjoint;intros [b i].
    destruct (Pos.eq_dec b 192%positive) as [B|B].
    - subst b. right;left;FiveOutside.
    - left. unfold FiveEvent. apply V293_encoded_memory_outside;left;exact B. }
  { unfold FiveEventBytes,FiveEvent;apply FiveConstantRange;reflexivity. }
  apply (V293_raw_cells_join (V293_clr_bytes 82%positive 0 (repeat Vundef 728))
    (V293_rdy_raw_cells (V293_clr_bytes 84%positive 0 (repeat (Vint32 (Int.repr 255)) 52))
      (V293_rdy_raw_cells FiveKernelCells (V293_rdy_raw_cells FiveFrame Atrue)))).
  eapply V293_wstate_star with (m1:=FiveTCB).
  - apply map_join_merge;apply map_disjoint;intros [b i].
    destruct (Pos.eq_dec b 82%positive) as [B|B].
    + subst b. destruct (Z_lt_dec i 728) as [I|I].
      * right;left;FiveOutside.
      * left. unfold FiveTCB. apply V293_encoded_memory_outside. right;right. rewrite repeat_length;lia.
    + left. unfold FiveTCB. apply V293_encoded_memory_outside;left;exact B.
  - unfold FiveTCB;apply FiveConstantRange;reflexivity.
  - apply (V293_raw_cells_join (V293_clr_bytes 84%positive 0 (repeat (Vint32 (Int.repr 255)) 52))
      (V293_rdy_raw_cells FiveKernelCells (V293_rdy_raw_cells FiveFrame Atrue))).
    eapply V293_wstate_star with (m1:=FivePrio).
    + apply map_join_merge;apply map_disjoint;intros [b i].
      destruct (Pos.eq_dec b 84%positive) as [B|B].
      * subst b. destruct (Z_lt_dec i 52) as [I|I].
        -- right;left;FiveOutside.
        -- left. unfold FivePrio. apply V293_encoded_memory_outside. right;right. rewrite repeat_length;lia.
      * left. unfold FivePrio. apply V293_encoded_memory_outside;left;exact B.
    + unfold FivePrio;apply FiveConstantRange;reflexivity.
    + cbn [FiveKernelCells FiveHeads FiveReady FiveEventHead V293_event_call_head FiveFlagHead V293_flag_call_head FiveFrame FiveMem app V293_rdy_raw_cells].
      eapply V293_wstate_star with (m1:=V293_encoded_memory 94%positive 0 true (encode_val (Tptr V293_tcb_type) (Vptr (121%positive,Int.zero))));
        [FiveApart 94%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
      eapply V293_wstate_star with (m1:=V293_encoded_memory 95%positive 0 true (encode_val (Tptr V293_tcb_type) (Vptr (122%positive,Int.zero))));
        [FiveApart 95%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
      eapply V293_wstate_star with (m1:=V293_encoded_memory 161%positive 0 true (encode_val (Tint8) (Vint32 (Int.repr 7)))).
      { FiveApart 161%positive. }
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
      { FiveApart 162%positive. }
      { split;[apply V293_encoded_memory_mapsto | reflexivity]. }
      eapply V293_wstate_star with (m1:=V293_encoded_memory 163%positive 0 true (encode_val (Tint8) (Vint32 (Int.repr 5)))).
      { FiveApart 163%positive. }
      { split;[apply V293_encoded_memory_mapsto | reflexivity]. }
      eapply V293_wstate_star with (m1:=V293_encoded_memory 164%positive 0 true (encode_val (Tint8) (Vint32 (Int.repr 9)))).
      { FiveApart 164%positive. }
      { split;[apply V293_encoded_memory_mapsto | reflexivity]. }
      eapply V293_wstate_star with (m1:=V293_encoded_memory 165%positive 0 true (encode_val (Tptr V293_tcb_type) (Vptr (211%positive,Int.zero)))).
      { FiveApart 165%positive. }
      { split;[apply V293_encoded_memory_mapsto | reflexivity]. }
      eapply V293_wstate_star with (m1:=V293_encoded_memory 166%positive 0 true (encode_val (Tptr V293_tcb_type) (Vptr (212%positive,Int.zero)))).
      { FiveApart 166%positive. }
      { split;[apply V293_encoded_memory_mapsto | reflexivity]. }
      eapply V293_wstate_star with (m1:=V293_encoded_memory 193%positive 0 true (encode_val (Tptr V293_event_type) (Vptr (213%positive,Int.zero))));
        [FiveApart 193%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
      eapply V293_wstate_star with (m1:=V293_encoded_memory 195%positive 0 true (encode_val (Tptr V293_flag_type) (Vptr (214%positive,Int.zero))));
        [FiveApart 195%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
      eapply V293_wstate_star with (m1:=V293_encoded_memory 82%positive 728 true (encode_val (Tint8) (Vint32 (Int.repr 17))));
        [FiveApart 82%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
      eapply V293_wstate_star with (m1:=V293_encoded_memory 84%positive 52 true (encode_val (Tint8) (Vint32 (Int.repr 29))));
        [FiveApart 84%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
      eapply V293_wstate_star with (m1:=V293_encoded_memory 99%positive 0 true (encode_val (Tint32) (Vint32 (Int.repr 123))));
        [FiveApart 99%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
      eapply V293_wstate_star with (m1:=V293_encoded_memory 110%positive 0 true (encode_val Tint32 (Vint32 (Int.repr 7))));
        [FiveApart 110%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
      exact I.
Qed.
Definition FiveTail := V293_rdy_globals 161%positive 162%positive 163%positive 164%positive 165%positive 166%positive
  (Vint32 (Int.repr 7)) (Vint32 (Int.repr 3)) Vundef (Vint32 (Int.repr 5))
  (Vint32 (Int.repr 9)) (Vptr (211%positive,Int.zero)) (Vptr (212%positive,Int.zero))++
  V293_clr_bytes 82%positive 0 (repeat Vundef 728)++
  V293_clr_bytes 84%positive 0 (repeat (Vint32 (Int.repr 255)) 52)++FiveHeads++FiveEventBytes++FiveEventHead++FiveFlagBytes++FiveFlagHead++FiveFrame.
Definition FiveMiscCells : list (block*type*val) :=
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
Fixpoint FiveMiscMem cells : mem := match cells with
 | []=>FiveMemory | (b,tp,v)::tail=>merge (V293_encoded_memory b 0 true (encode_val tp v)) (FiveMiscMem tail) end.
Definition FiveEntryMemory := FiveMiscMem FiveMiscCells.
Lemma FiveRawTail : FiveState FiveMemory |= V293_rdy_raw_cells FiveTail Atrue.
Proof.
  pose proof FiveLiteralEntry as H0.
  assert (H : FiveState FiveMemory |= V293_rdy_raw_cells
    (FiveEventBytes++V293_clr_bytes 82%positive 0 (repeat Vundef 728)++
     V293_clr_bytes 84%positive 0 (repeat (Vint32 (Int.repr 255)) 52)++
     FiveHeads++FiveReady++FiveEventHead++FiveFlagBytes++FiveFlagHead++FiveFrame) Atrue).
  { eapply V293_raw_cells_permutation;[ | exact H0].
    unfold FiveKernelCells. repeat rewrite app_assoc.
    apply Permutation_app_tail. apply Permutation_app_tail.
    pose proof (Permutation_app_comm FiveFlagBytes
      (FiveEventBytes++V293_clr_bytes 82%positive 0 (repeat Vundef 728)++
       V293_clr_bytes 84%positive 0 (repeat (Vint32 (Int.repr 255)) 52)++
       FiveHeads++FiveReady++FiveEventHead)) as Perm.
    repeat rewrite <-app_assoc in *. exact Perm. }
  unfold FiveTail.
  repeat rewrite V293_raw_cells_append in *.
  assert (Perm : forall s,
    s |= V293_rdy_raw_cells FiveEventBytes
      (V293_rdy_raw_cells (V293_clr_bytes 82%positive 0 (repeat Vundef 728))
       (V293_rdy_raw_cells (V293_clr_bytes 84%positive 0 (repeat (Vint32 (Int.repr 255)) 52))
        (V293_rdy_raw_cells FiveHeads
         (V293_rdy_raw_cells FiveReady (V293_rdy_raw_cells FiveEventHead (V293_rdy_raw_cells FiveFlagBytes (V293_rdy_raw_cells FiveFlagHead (V293_rdy_raw_cells FiveFrame Atrue)))))))) ->
    s |= V293_rdy_raw_cells FiveReady
      (V293_rdy_raw_cells (V293_clr_bytes 82%positive 0 (repeat Vundef 728))
       (V293_rdy_raw_cells (V293_clr_bytes 84%positive 0 (repeat (Vint32 (Int.repr 255)) 52))
        (V293_rdy_raw_cells FiveHeads
         (V293_rdy_raw_cells FiveEventBytes (V293_rdy_raw_cells FiveEventHead (V293_rdy_raw_cells FiveFlagBytes (V293_rdy_raw_cells FiveFlagHead (V293_rdy_raw_cells FiveFrame Atrue))))))))).
  { intros st K.
    apply (V293_raw_cells_swap FiveEventBytes _ _) in K.
    apply (V293_raw_cells_mono _ _ _ (V293_raw_cells_swap FiveEventBytes _ _)) in K.
    apply (V293_raw_cells_mono _ _ _ (V293_raw_cells_mono _ _ _ (V293_raw_cells_swap FiveEventBytes _ _))) in K.
    apply (V293_raw_cells_mono _ _ _ (V293_raw_cells_mono _ _ _
      (V293_raw_cells_mono _ _ _ (V293_raw_cells_swap FiveEventBytes FiveReady _)))) in K.
    apply (V293_raw_cells_mono _ _ _ (V293_raw_cells_mono _ _ _ (V293_raw_cells_swap FiveHeads FiveReady _))) in K.
    apply (V293_raw_cells_mono _ _ _ (V293_raw_cells_swap _ FiveReady _)) in K.
    apply V293_raw_cells_swap in K;exact K. }
  apply Perm;exact H.
Qed.
Lemma FiveSlotEntry : forall x tp b v,
 get FiveGE x=Some (b,tp) ->
 V293_wstate FiveGE emp (V293_encoded_memory b 0 true (encode_val tp v)) |=
  V293_init_binding (Build_V293_init_slot x tp b) ** V293_init_memory (Build_V293_init_slot x tp b) false.
Proof.
 intros x tp b v Env. eapply V293_wstate_star with (m1:=emp) (m2:=V293_encoded_memory b 0 true (encode_val tp v)).
 - apply map_join_comm;apply map_join_emp.
 - split.
   + exists b. split;[exact Env | ]. repeat split;reflexivity.
   + split;[intros [w E];change (None=Some w) in E;discriminate | split;reflexivity].
 - exists v. split;[apply V293_encoded_memory_mapsto | reflexivity].
Qed.
Theorem FiveLiteralFullEntry : V293_wstate FiveGE emp FiveEntryMemory |=
  V293_init_resources FiveSlots false (V293_rdy_raw_cells FiveTail Atrue).
Proof.
 unfold FiveEntryMemory,FiveMiscCells,FiveSlots,V293_InitMisc_slots.
 cbn [FiveMiscMem V293_init_resources].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 181%positive 0 true (encode_val (Tint32) (Vint32 (Int.repr 57)))).
 { apply map_join_merge;apply map_disjoint;intros [other off].
   destruct (Pos.eq_dec other 181%positive);[subst other;right;left | left];
   unfold FiveMemory,FiveFlag,FiveEvent,FiveTCB,FivePrio;cbn [FiveKernelCells FiveHeads FiveReady FiveEventHead V293_event_call_head FiveFlagHead V293_flag_call_head FiveFrame FiveMem app];
   repeat first [rewrite V293_encoded_memory_outside by (left;congruence)
     | rewrite map_merge_semp by reflexivity];reflexivity. }
 { apply FiveSlotEntry;vm_compute;reflexivity. }
 eapply V293_wstate_star with (m1:=V293_encoded_memory 182%positive 0 true (encode_val (Tint8) (Vint32 (Int.repr 3)))).
 { apply map_join_merge;apply map_disjoint;intros [other off].
   destruct (Pos.eq_dec other 182%positive);[subst other;right;left | left];
   unfold FiveMemory,FiveFlag,FiveEvent,FiveTCB,FivePrio;cbn [FiveKernelCells FiveHeads FiveReady FiveEventHead V293_event_call_head FiveFlagHead V293_flag_call_head FiveFrame FiveMem app];
   repeat first [rewrite V293_encoded_memory_outside by (left;congruence)
     | rewrite map_merge_semp by reflexivity];reflexivity. }
 { apply FiveSlotEntry;vm_compute;reflexivity. }
 eapply V293_wstate_star with (m1:=V293_encoded_memory 183%positive 0 true (encode_val (Tint8) (Vint32 (Int.repr 2)))).
 { apply map_join_merge;apply map_disjoint;intros [other off].
   destruct (Pos.eq_dec other 183%positive);[subst other;right;left | left];
   unfold FiveMemory,FiveFlag,FiveEvent,FiveTCB,FivePrio;cbn [FiveKernelCells FiveHeads FiveReady FiveEventHead V293_event_call_head FiveFlagHead V293_flag_call_head FiveFrame FiveMem app];
   repeat first [rewrite V293_encoded_memory_outside by (left;congruence)
     | rewrite map_merge_semp by reflexivity];reflexivity. }
 { apply FiveSlotEntry;vm_compute;reflexivity. }
 eapply V293_wstate_star with (m1:=V293_encoded_memory 184%positive 0 true (encode_val (Tint8) (Vint32 (Int.repr 9)))).
 { apply map_join_merge;apply map_disjoint;intros [other off].
   destruct (Pos.eq_dec other 184%positive);[subst other;right;left | left];
   unfold FiveMemory,FiveFlag,FiveEvent,FiveTCB,FivePrio;cbn [FiveKernelCells FiveHeads FiveReady FiveEventHead V293_event_call_head FiveFlagHead V293_flag_call_head FiveFrame FiveMem app];
   repeat first [rewrite V293_encoded_memory_outside by (left;congruence)
     | rewrite map_merge_semp by reflexivity];reflexivity. }
 { apply FiveSlotEntry;vm_compute;reflexivity. }
 eapply V293_wstate_star with (m1:=V293_encoded_memory 185%positive 0 true (encode_val (Tint8) (Vint32 Int.one))).
 { apply map_join_merge;apply map_disjoint;intros [other off].
   destruct (Pos.eq_dec other 185%positive);[subst other;right;left | left];
   unfold FiveMemory,FiveFlag,FiveEvent,FiveTCB,FivePrio;cbn [FiveKernelCells FiveHeads FiveReady FiveEventHead V293_event_call_head FiveFlagHead V293_flag_call_head FiveFrame FiveMem app];
   repeat first [rewrite V293_encoded_memory_outside by (left;congruence)
     | rewrite map_merge_semp by reflexivity];reflexivity. }
 { apply FiveSlotEntry;vm_compute;reflexivity. }
 eapply V293_wstate_star with (m1:=V293_encoded_memory 186%positive 0 true (encode_val (Tint32) (Vint32 (Int.repr 42)))).
 { apply map_join_merge;apply map_disjoint;intros [other off].
   destruct (Pos.eq_dec other 186%positive);[subst other;right;left | left];
   unfold FiveMemory,FiveFlag,FiveEvent,FiveTCB,FivePrio;cbn [FiveKernelCells FiveHeads FiveReady FiveEventHead V293_event_call_head FiveFlagHead V293_flag_call_head FiveFrame FiveMem app];
   repeat first [rewrite V293_encoded_memory_outside by (left;congruence)
     | rewrite map_merge_semp by reflexivity];reflexivity. }
 { apply FiveSlotEntry;vm_compute;reflexivity. }
 eapply V293_wstate_star with (m1:=V293_encoded_memory 187%positive 0 true (encode_val (Tint32) (Vundef))).
 { apply map_join_merge;apply map_disjoint;intros [other off].
   destruct (Pos.eq_dec other 187%positive);[subst other;right;left | left];
   unfold FiveMemory,FiveFlag,FiveEvent,FiveTCB,FivePrio;cbn [FiveKernelCells FiveHeads FiveReady FiveEventHead V293_event_call_head FiveFlagHead V293_flag_call_head FiveFrame FiveMem app];
   repeat first [rewrite V293_encoded_memory_outside by (left;congruence)
     | rewrite map_merge_semp by reflexivity];reflexivity. }
 { apply FiveSlotEntry;vm_compute;reflexivity. }
 eapply V293_wstate_star with (m1:=V293_encoded_memory 188%positive 0 true (encode_val (Tint32) (Vundef))).
 { apply map_join_merge;apply map_disjoint;intros [other off].
   destruct (Pos.eq_dec other 188%positive);[subst other;right;left | left];
   unfold FiveMemory,FiveFlag,FiveEvent,FiveTCB,FivePrio;cbn [FiveKernelCells FiveHeads FiveReady FiveEventHead V293_event_call_head FiveFlagHead V293_flag_call_head FiveFrame FiveMem app];
   repeat first [rewrite V293_encoded_memory_outside by (left;congruence)
     | rewrite map_merge_semp by reflexivity];reflexivity. }
 { apply FiveSlotEntry;vm_compute;reflexivity. }
 eapply V293_wstate_star with (m1:=V293_encoded_memory 189%positive 0 true (encode_val (Tint32) (Vint32 (Int.repr 100)))).
 { apply map_join_merge;apply map_disjoint;intros [other off].
   destruct (Pos.eq_dec other 189%positive);[subst other;right;left | left];
   unfold FiveMemory,FiveFlag,FiveEvent,FiveTCB,FivePrio;cbn [FiveKernelCells FiveHeads FiveReady FiveEventHead V293_event_call_head FiveFlagHead V293_flag_call_head FiveFrame FiveMem app];
   repeat first [rewrite V293_encoded_memory_outside by (left;congruence)
     | rewrite map_merge_semp by reflexivity];reflexivity. }
 { apply FiveSlotEntry;vm_compute;reflexivity. }
 eapply V293_wstate_star with (m1:=V293_encoded_memory 190%positive 0 true (encode_val (Tint8) (Vint32 Int.one))).
 { apply map_join_merge;apply map_disjoint;intros [other off].
   destruct (Pos.eq_dec other 190%positive);[subst other;right;left | left];
   unfold FiveMemory,FiveFlag,FiveEvent,FiveTCB,FivePrio;cbn [FiveKernelCells FiveHeads FiveReady FiveEventHead V293_event_call_head FiveFlagHead V293_flag_call_head FiveFrame FiveMem app];
   repeat first [rewrite V293_encoded_memory_outside by (left;congruence)
     | rewrite map_merge_semp by reflexivity];reflexivity. }
 { apply FiveSlotEntry;vm_compute;reflexivity. }
 eapply V293_raw_cells_environment;[right;reflexivity | exact FiveRawTail].
Qed.
Definition FiveProgram f :=
 if Z.eq_dec f 201%Z then Some (V293_InitMisc_function 1001%Z 1002%Z 1003%Z 1004%Z 1005%Z 1006%Z 1007%Z 1008%Z 1009%Z 1010%Z)
 else if Z.eq_dec f 202%Z then Some (V293_InitRdyList_function 21%Z 22%Z 23%Z 24%Z 25%Z 26%Z 41%Z)
 else if Z.eq_dec f 203%Z then Some (V293_InitTCBList_function 204%Z 31%Z 32%Z 33%Z 34%Z 41%Z 42%Z 43%Z 44%Z)
 else if Z.eq_dec f 205%Z then Some (V293_InitEventList_function 204%Z 35%Z 36%Z 41%Z 42%Z 43%Z 44%Z)
 else if Z.eq_dec f 206%Z then Some (V293_FlagInit_function 204%Z 37%Z 38%Z 41%Z 42%Z 43%Z 44%Z)
 else if Z.eq_dec f 204%Z then Some (V293_MemClr_function 11%Z 12%Z) else None.
Lemma FiveLiteralOrder : V293_init_five_calls 201%Z 202%Z 203%Z 205%Z 206%Z =
 sseq (sseq (sseq (scall 201%Z nil) (sseq (scall 202%Z nil) (scall 203%Z nil))) (scall 205%Z nil)) (scall 206%Z nil).
Proof. reflexivity. Qed.
Definition FiveReadyZero := V293_rdy_globals 161%positive 162%positive 163%positive
  164%positive 165%positive 166%positive (Vint32 Int.zero) (Vint32 Int.zero)
  (Vint32 Int.zero) (Vint32 Int.zero) (Vint32 Int.zero) Vnull Vnull.
Definition FiveExtraCells := FiveReadyZero++V293_misc_zero_cells FiveSlots++FiveFrame.
Definition FiveFinalCells := V293_flag_call_result 195%positive 194%positive
 (V293_event_call_result 193%positive 192%positive
  (V293_tcb_call_result 94%positive 95%positive 82%positive 84%positive FiveExtraCells)).
Definition FiveChecks := V293_flag_call_result 195%positive 194%positive []++
 V293_event_call_result 193%positive 192%positive []++
 V293_tcb_call_heads 94%positive 95%positive Vnull (Vptr (82%positive,Int.zero))++
 V293_tcb_linked_next 82%positive++V293_null_pointer_cells 84%positive 0 13++FiveExtraCells.
Lemma FiveCheckCount : length FiveChecks=122%nat.
Proof. reflexivity. Qed.
Lemma FiveChecksValid : forall a tp v, In (a,tp,v) FiveChecks -> rule_type_val_match tp v=true.
Proof.
 intros a tp v Member.
 cbn [FiveChecks V293_flag_call_result V293_flag_call_head V293_flag_linked V293_flag_untouched_cells V293_event_call_result V293_event_call_head V293_event_linked
   V293_event_untouched_cells V293_clr_bytes repeat
   V293_tcb_call_heads V293_tcb_linked_next V293_null_pointer_cells seq map
   FiveExtraCells FiveReadyZero V293_rdy_globals V293_misc_zero_cells FiveSlots
   V293_InitMisc_slots FiveFrame init_block init_type app] in Member.
 repeat (destruct Member as [E | Member];[inversion E;subst;reflexivity | ]);contradiction.
Qed.
Lemma FiveChecksInFinal : forall a tp v, In (a,tp,v) FiveChecks -> In (a,tp,v) FiveFinalCells.
Proof.
 intros a tp v Member.
 unfold FiveChecks,FiveFinalCells,V293_flag_call_result,V293_event_call_result,V293_tcb_call_result in *.
 repeat rewrite in_app_iff in *;cbn [In] in *;tauto.
Qed.
Lemma FiveExtraCount : length FiveExtraCells=21%nat.
Proof. reflexivity. Qed.
Lemma FiveExtrasValid : forall a tp v,
 In (a,tp,v) FiveExtraCells -> rule_type_val_match tp v=true.
Proof.
 intros a tp v Member.
 cbn [FiveExtraCells FiveReadyZero V293_rdy_globals V293_misc_zero_cells FiveSlots
   V293_InitMisc_slots FiveFrame map app init_block init_type] in Member.
 repeat (destruct Member as [E | Member];[inversion E;subst;reflexivity | ]);contradiction.
Qed.
Lemma FiveReadyEnvironment : forall bi,
 V293_rdy_env FiveGE (V293_rdy_locals 41%Z bi) 21%Z 22%Z 23%Z 24%Z 25%Z 26%Z 41%Z
 161%positive 162%positive 163%positive 164%positive 165%positive 166%positive bi.
Proof. intro bi. repeat split;reflexivity. Qed.
Lemma FiveTCBEnvironment : forall bi bn b1 b2,
 V293_tcb_link_env FiveGE (V293_tcb_call_locals 41%Z 42%Z 43%Z 44%Z bi bn b1 b2)
 31%Z 33%Z 34%Z 41%Z 42%Z 43%Z 44%Z 82%positive 94%positive 95%positive bi bn b1 b2.
Proof. intros. repeat split;reflexivity. Qed.
Lemma FiveEventEnvironment : forall bi bn b1 b2,
 V293_event_link_env FiveGE (V293_event_call_locals 41%Z 42%Z 43%Z 44%Z bi bn b1 b2)
 35%Z 36%Z 41%Z 42%Z 43%Z 44%Z 192%positive 193%positive bi bn b1 b2.
Proof. intros. repeat split;reflexivity. Qed.
Lemma FiveFlagEnvironment : forall bi bn b1 b2,
 V293_flag_link_env FiveGE (V293_flag_call_locals 41%Z 42%Z 43%Z 44%Z bi bn b1 b2)
 37%Z 38%Z 41%Z 42%Z 43%Z 44%Z 194%positive 195%positive bi bn b1 b2.
Proof. intros. repeat split;reflexivity. Qed.
Theorem FiveConcreteExecution : forall ks, exists Mevent Mf bi bn b1 b2,
 cstepstar FiveProgram (curs (V293_init_five_calls 201%Z 202%Z 203%Z 205%Z 206%Z),(kenil,ks))
   (FiveGE,FiveCaller,FiveEntryMemory) (curs (sskip None),(kenil,ks)) (FiveGE,FiveCaller,Mf) /\
 FiveState Mf |= V293_rdy_raw_cells FiveFinalCells Atrue /\
 (forall a tp v, In (a,tp,v) FiveChecks -> load tp Mf a=Some v) /\
 cstepstar FiveProgram (curs (V293_init_four_calls 201%Z 202%Z 203%Z 205%Z),
   (kenil,kseq (scall 206%Z nil) ks)) (FiveGE,FiveCaller,FiveEntryMemory)
   (curs (sskip None),(kenil,kseq (scall 206%Z nil) ks)) (FiveGE,FiveCaller,Mevent) /\
 cstepstar FiveProgram (curs (scall 206%Z nil),(kenil,ks)) (FiveGE,FiveCaller,Mevent)
   (curs (sskip None),(kenil,ks)) (FiveGE,FiveCaller,Mf) /\ fresh Mevent bi /\ fresh Mevent bn /\ fresh Mevent b1 /\ fresh Mevent b2 /\
 (forall c tp k, In (c,tp) [(bi,Tint16);(bn,Tint16);(b1,Tptr V293_flag_type);(b2,Tptr V293_flag_type)] ->
   (k<typelen tp)%nat -> get Mf (c,Z.of_nat k)=None).
Proof.
 intro ks.
 destruct (V293_OSInit_five_calls FiveSlots (repeat Vundef 728)
   (repeat (Vint32 (Int.repr 255)) 52) (repeat (Vint32 (Int.repr 255)) 32) (repeat (Vint32 (Int.repr 255)) 60) FiveFrame
   FiveProgram ks FiveGE FiveCaller FiveEntryMemory
   (fun _=>false) (false,nil,nil) emp (spec_done None)
   201%Z 202%Z 203%Z 204%Z 11%Z 12%Z 21%Z 22%Z 23%Z 24%Z 25%Z 26%Z 41%Z
   161%positive 162%positive 163%positive 164%positive 165%positive 166%positive
   31%Z 32%Z 33%Z 34%Z 41%Z 42%Z 43%Z 44%Z 82%positive 84%positive 94%positive 95%positive
   (Vint32 (Int.repr 7)) (Vint32 (Int.repr 3)) Vundef (Vint32 (Int.repr 5))
   (Vint32 (Int.repr 9)) (Vptr (211%positive,Int.zero)) (Vptr (212%positive,Int.zero))
   (Vptr (121%positive,Int.zero)) (Vptr (122%positive,Int.zero))
   205%Z 35%Z 36%Z 41%Z 42%Z 43%Z 44%Z 192%positive 193%positive (Vptr (213%positive,Int.zero))
   206%Z 37%Z 38%Z 41%Z 42%Z 43%Z 44%Z 194%positive 195%positive (Vptr (214%positive,Int.zero))
   ltac:(unfold FiveSlots,V293_InitMisc_slots;repeat (apply Forall_cons;[unfold V293_init_scalar;cbn;auto | ]);apply Forall_nil)
   ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)
   ltac:(discriminate) ltac:(lia) ltac:(lia) ltac:(lia)
   FiveReadyEnvironment FiveTCBEnvironment ltac:(intros;reflexivity) ltac:(reflexivity)
   ltac:(apply repeat_length) ltac:(apply repeat_length)
   ltac:(reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) FiveEventEnvironment ltac:(apply repeat_length)
   ltac:(reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) FiveFlagEnvironment ltac:(apply repeat_length)
   FiveLiteralFullEntry)
   as (Mevent&Mf&bi&bn&b1&b2&Exec&Prefix&Event&Fi&Fn&F1&F2&Owned&Freed).
 exists Mevent. exists Mf. exists bi. exists bn. exists b1. exists b2.
 split;[exact Exec | ]. split;[exact Owned | ]. split.
 - intros a tp v Member. change (load tp (getmem (FiveState Mf)) a=Some v).
   eapply (V293_rdy_raw_load FiveFinalCells Atrue);
     [apply FiveChecksInFinal;exact Member | exact (FiveChecksValid a tp v Member) | exact Owned].
 - split;[exact Prefix | ]. split;[exact Event | ].
   split;[exact Fi | ]. split;[exact Fn | ]. split;[exact F1 | ]. split;[exact F2 | exact Freed].
Qed.
Theorem FiveReturnConnections : forall ks, exists Mf,
 cstepstar FiveProgram (curs (V293_init_five_calls 201%Z 202%Z 203%Z 205%Z 206%Z),(kenil,ks))
   (FiveGE,FiveCaller,FiveEntryMemory) (curs (sskip None),(kenil,ks)) (FiveGE,FiveCaller,Mf) /\
 load (Tptr Tvoid) Mf (194%positive,4)=Some (Vptr (194%positive,Int.repr 12)) /\
 load (Tptr V293_flag_type) Mf (195%positive,0)=Some (Vptr (194%positive,Int.zero)) /\
 load Tint8 Mf (161%positive,0)=Some (Vint32 Int.zero) /\
 load Tint32 Mf (99%positive,0)=Some (Vint32 (Int.repr 123)) /\
 load (Tptr Tvoid) Mf (194%positive,52)=Some Vnull /\
 load Tint32 Mf (110%positive,0)=Some (Vint32 (Int.repr 7)).
Proof.
 intro ks. destruct (FiveConcreteExecution ks)
   as (Mevent&Mf&bi&bn&b1&b2&Exec&Owned&Loads&Prefix&Event&Fi&Fn&F1&F2&Freed).
 exists Mf. split;[exact Exec | ]. split.
 - apply Loads;vm_compute;tauto.
 - split.
   + apply Loads;vm_compute;tauto.
   + split.
     * apply Loads;vm_compute;tauto.
     * split.
       -- apply Loads;vm_compute;tauto.
       -- split.
          ++ apply Loads;vm_compute;tauto.
          ++ apply Loads;vm_compute;tauto.
Qed.
Print Assumptions FiveLiteralFullEntry.
Print Assumptions FiveLiteralOrder.
Print Assumptions FiveConcreteExecution.
Print Assumptions FiveReturnConnections.


(* Prospective single-factor ablation: delete only the fifth call. *)
Theorem FiveWithoutFlagCall : forall ks, exists Mevent,
 cstepstar FiveProgram (curs (V293_init_four_calls 201%Z 202%Z 203%Z 205%Z),(kenil,ks))
   (FiveGE,FiveCaller,FiveEntryMemory) (curs (sskip None),(kenil,ks)) (FiveGE,FiveCaller,Mevent) /\
 load Tint8 Mevent (194%positive,0)=Some (Vint32 (Int.repr 255)) /\
 load (Tptr V293_flag_type) Mevent (195%positive,0)=Some (Vptr (214%positive,Int.zero)) /\
 load Tint8 Mevent (192%positive,0)=Some (Vint32 Int.zero) /\
 load Tint8 Mevent (161%positive,0)=Some (Vint32 Int.zero) /\
 load Tint32 Mevent (99%positive,0)=Some (Vint32 (Int.repr 123)).
Proof.
 intro ks.
 destruct (V293_OSInit_four_calls FiveSlots (repeat Vundef 728)
   (repeat (Vint32 (Int.repr 255)) 52) (repeat (Vint32 (Int.repr 255)) 32) (FiveFlagBytes++FiveFlagHead++FiveFrame)
   FiveProgram ks FiveGE FiveCaller FiveEntryMemory
   (fun _=>false) (false,nil,nil) emp (spec_done None)
   201%Z 202%Z 203%Z 204%Z 11%Z 12%Z 21%Z 22%Z 23%Z 24%Z 25%Z 26%Z 41%Z
   161%positive 162%positive 163%positive 164%positive 165%positive 166%positive
   31%Z 32%Z 33%Z 34%Z 41%Z 42%Z 43%Z 44%Z 82%positive 84%positive 94%positive 95%positive
   (Vint32 (Int.repr 7)) (Vint32 (Int.repr 3)) Vundef (Vint32 (Int.repr 5))
   (Vint32 (Int.repr 9)) (Vptr (211%positive,Int.zero)) (Vptr (212%positive,Int.zero))
   (Vptr (121%positive,Int.zero)) (Vptr (122%positive,Int.zero))
   205%Z 35%Z 36%Z 41%Z 42%Z 43%Z 44%Z 192%positive 193%positive (Vptr (213%positive,Int.zero))
   ltac:(unfold FiveSlots,V293_InitMisc_slots;repeat (apply Forall_cons;[unfold V293_init_scalar;cbn;auto | ]);apply Forall_nil)
   ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)
   ltac:(discriminate) ltac:(lia) ltac:(lia) ltac:(lia)
   FiveReadyEnvironment FiveTCBEnvironment ltac:(intros;reflexivity) ltac:(reflexivity)
   ltac:(apply repeat_length) ltac:(apply repeat_length)
   ltac:(reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) FiveEventEnvironment ltac:(apply repeat_length)
   FiveLiteralFullEntry)
   as (Mtcb&Mf&bi&bn&b1&b2&Exec&Prefix&Event&Fi&Fn&F1&F2&Owned&Freed).

 exists Mf. split;[exact Exec | ].
 set (result:=V293_event_call_result 193%positive 192%positive
   (V293_tcb_call_result 94%positive 95%positive 82%positive 84%positive
    (FiveReadyZero++V293_misc_zero_cells FiveSlots++FiveFlagBytes++FiveFlagHead++FiveFrame))).
 change (FiveState Mf |= V293_rdy_raw_cells result Atrue) in Owned.
 assert (Load : forall a tp v, In (a,tp,v) result -> rule_type_val_match tp v=true -> load tp Mf a=Some v).
 { intros a tp v Member Valid. change (load tp (getmem (FiveState Mf)) a=Some v).
   eapply (V293_rdy_raw_load result Atrue);eassumption. }
 split.
 - apply Load;[unfold result,V293_event_call_result,V293_tcb_call_result;
     do 7 (apply in_or_app;right);apply in_or_app;right;apply in_or_app;right;
     apply in_or_app;left;left;reflexivity | reflexivity].
 - split.
   + apply Load;[unfold result,V293_event_call_result,V293_tcb_call_result;
       do 7 (apply in_or_app;right);apply in_or_app;right;apply in_or_app;right;
       apply in_or_app;right;apply in_or_app;left;left;reflexivity | reflexivity].
   + split.
     * apply Load;[unfold result,V293_event_call_result;
         apply in_or_app;right;apply in_or_app;left;left;reflexivity | reflexivity].
     * split.
       -- apply Load;[unfold result,V293_event_call_result,V293_tcb_call_result;
           do 7 (apply in_or_app;right);apply in_or_app;left;left;reflexivity | reflexivity].
       -- apply Load;[unfold result,V293_event_call_result,V293_tcb_call_result;
           do 7 (apply in_or_app;right);do 4 (apply in_or_app;right);
           unfold FiveFrame;right;right;left;reflexivity | reflexivity].
Qed.
Print Assumptions FiveWithoutFlagCall.
