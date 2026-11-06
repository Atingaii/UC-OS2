(* Whole call: independently encoded finite entry, absent callee locals, nonempty shadowed caller. *)
Require Import CertiOS.framework.include_frm.
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
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope Z_scope.
Definition FourSlots := V293_InitMisc_slots 1001%Z 1002%Z 1003%Z 1004%Z 1005%Z 1006%Z 1007%Z 1008%Z 1009%Z 1010%Z 181%positive 182%positive 183%positive 184%positive 185%positive 186%positive 187%positive 188%positive 189%positive 190%positive.
Definition FourGE : env := fold_right
  (fun d e=>set e (init_name d) (init_block d,init_type d))
  (set (set (set (set (set (set
  (set (set (set (set (set (set emp 35%Z (192%positive,V293_event_table_type)) 36%Z (193%positive,Tptr V293_event_type)) 31%Z (82%positive,Tarray V293_tcb_type 13))
   32%Z (84%positive,Tarray (Tptr V293_tcb_type) 13))
   33%Z (94%positive,Tptr V293_tcb_type)) 34%Z (95%positive,Tptr V293_tcb_type))
   21%Z (161%positive,Tint8)) 22%Z (162%positive,Tarray Tint8 2))
   23%Z (163%positive,Tint8)) 24%Z (164%positive,Tint8))
   25%Z (165%positive,Tptr V293_tcb_type)) 26%Z (166%positive,Tptr V293_tcb_type)) FourSlots.
Definition FourTCB := V293_encoded_memory 82%positive 0 true (repeat Undef 728).
Definition FourPrio := V293_encoded_memory 84%positive 0 true (repeat (Byte (Byte.repr 255)) 52).
Definition FourHeads : list V293_record_cell :=
  [((94%positive,0),Tptr V293_tcb_type,Vptr (121%positive,Int.zero));
   ((95%positive,0),Tptr V293_tcb_type,Vptr (122%positive,Int.zero))].
Definition FourReady : list V293_record_cell :=
 [((161%positive,0),Tint8,Vint32 (Int.repr 7));
  ((162%positive,0),Tint8,Vint32 (Int.repr 3));
  ((162%positive,1),Tint8,Vundef);
  ((163%positive,0),Tint8,Vint32 (Int.repr 5));
  ((164%positive,0),Tint8,Vint32 (Int.repr 9));
  ((165%positive,0),Tptr V293_tcb_type,Vptr (211%positive,Int.zero));
  ((166%positive,0),Tptr V293_tcb_type,Vptr (212%positive,Int.zero))].
Definition FourEventHead := V293_event_call_head 193%positive (Vptr (213%positive,Int.zero)).
Definition FourKernelCells := FourHeads++FourReady++FourEventHead.
Definition FourEvent := V293_encoded_memory 192%positive 0 true (repeat (Byte (Byte.repr 255)) 32).
Definition FourEventBytes := V293_clr_bytes 192%positive 0 (repeat (Vint32 (Int.repr 255)) 32).
Definition FourFrame : list V293_record_cell :=
  [((82%positive,728),Tint8,Vint32 (Int.repr 17));
   ((84%positive,52),Tint8,Vint32 (Int.repr 29));
   ((99%positive,0),Tint32,Vint32 (Int.repr 123));
   ((110%positive,0),Tint32,Vint32 (Int.repr 7))].
Fixpoint FourMem (cells : list V293_record_cell) : mem :=
  match cells with []=>emp | ((b,off),tp,v)::tail=>
    merge (V293_encoded_memory b off true (encode_val tp v)) (FourMem tail) end.
Definition FourMemory := merge FourEvent (merge FourTCB (merge FourPrio (FourMem (FourKernelCells++FourFrame)))).
Definition FourCaller : env := set emp 41%Z (110%positive,Tint32).
Definition FourState M := V293_wstate FourGE FourCaller M.

Lemma FourConstantRange : forall n v byte ge le b off,
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
Ltac FourOutside :=
  unfold FourEvent,FourTCB,FourPrio;
  cbn [FourKernelCells FourHeads FourReady FourEventHead V293_event_call_head FourFrame FourMem app];
  repeat first [rewrite V293_encoded_memory_outside by
    (first [left;congruence | right;rewrite ?repeat_length;cbn [length encode_val inj_bytes encode_int];lia])
    | rewrite map_merge_semp by reflexivity];
  reflexivity.
Ltac FourApart b :=
  apply map_join_merge;apply map_disjoint;intros [other off];
  destruct (Pos.eq_dec other b);[subst other;right;left | left];
  repeat first [rewrite V293_encoded_memory_outside by (left;congruence)
    | rewrite map_merge_semp by reflexivity];reflexivity.
Lemma FourLiteralEntry : FourState FourMemory |= V293_rdy_raw_cells
  (FourEventBytes++V293_clr_bytes 82%positive 0 (repeat Vundef 728)++
   V293_clr_bytes 84%positive 0 (repeat (Vint32 (Int.repr 255)) 52)++FourKernelCells++FourFrame) Atrue.
Proof.
  unfold FourState,FourMemory. repeat rewrite V293_raw_cells_append.
  apply (V293_raw_cells_join FourEventBytes
    (V293_rdy_raw_cells (V293_clr_bytes 82%positive 0 (repeat Vundef 728))
      (V293_rdy_raw_cells (V293_clr_bytes 84%positive 0 (repeat (Vint32 (Int.repr 255)) 52))
        (V293_rdy_raw_cells FourKernelCells (V293_rdy_raw_cells FourFrame Atrue))))).
  eapply V293_wstate_star with (m1:=FourEvent).
  { apply map_join_merge;apply map_disjoint;intros [b i].
    destruct (Pos.eq_dec b 192%positive) as [B|B].
    - subst b. right;left;FourOutside.
    - left. unfold FourEvent. apply V293_encoded_memory_outside;left;exact B. }
  { unfold FourEventBytes,FourEvent;apply FourConstantRange;reflexivity. }
  apply (V293_raw_cells_join (V293_clr_bytes 82%positive 0 (repeat Vundef 728))
    (V293_rdy_raw_cells (V293_clr_bytes 84%positive 0 (repeat (Vint32 (Int.repr 255)) 52))
      (V293_rdy_raw_cells FourKernelCells (V293_rdy_raw_cells FourFrame Atrue)))).
  eapply V293_wstate_star with (m1:=FourTCB).
  - apply map_join_merge;apply map_disjoint;intros [b i].
    destruct (Pos.eq_dec b 82%positive) as [B|B].
    + subst b. destruct (Z_lt_dec i 728) as [I|I].
      * right;left;FourOutside.
      * left. unfold FourTCB. apply V293_encoded_memory_outside. right;right. rewrite repeat_length;lia.
    + left. unfold FourTCB. apply V293_encoded_memory_outside;left;exact B.
  - unfold FourTCB;apply FourConstantRange;reflexivity.
  - apply (V293_raw_cells_join (V293_clr_bytes 84%positive 0 (repeat (Vint32 (Int.repr 255)) 52))
      (V293_rdy_raw_cells FourKernelCells (V293_rdy_raw_cells FourFrame Atrue))).
    eapply V293_wstate_star with (m1:=FourPrio).
    + apply map_join_merge;apply map_disjoint;intros [b i].
      destruct (Pos.eq_dec b 84%positive) as [B|B].
      * subst b. destruct (Z_lt_dec i 52) as [I|I].
        -- right;left;FourOutside.
        -- left. unfold FourPrio. apply V293_encoded_memory_outside. right;right. rewrite repeat_length;lia.
      * left. unfold FourPrio. apply V293_encoded_memory_outside;left;exact B.
    + unfold FourPrio;apply FourConstantRange;reflexivity.
    + cbn [FourKernelCells FourHeads FourReady FourEventHead V293_event_call_head FourFrame FourMem app V293_rdy_raw_cells].
      eapply V293_wstate_star with (m1:=V293_encoded_memory 94%positive 0 true (encode_val (Tptr V293_tcb_type) (Vptr (121%positive,Int.zero))));
        [FourApart 94%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
      eapply V293_wstate_star with (m1:=V293_encoded_memory 95%positive 0 true (encode_val (Tptr V293_tcb_type) (Vptr (122%positive,Int.zero))));
        [FourApart 95%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
      eapply V293_wstate_star with (m1:=V293_encoded_memory 161%positive 0 true (encode_val (Tint8) (Vint32 (Int.repr 7)))).
      { FourApart 161%positive. }
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
      { FourApart 162%positive. }
      { split;[apply V293_encoded_memory_mapsto | reflexivity]. }
      eapply V293_wstate_star with (m1:=V293_encoded_memory 163%positive 0 true (encode_val (Tint8) (Vint32 (Int.repr 5)))).
      { FourApart 163%positive. }
      { split;[apply V293_encoded_memory_mapsto | reflexivity]. }
      eapply V293_wstate_star with (m1:=V293_encoded_memory 164%positive 0 true (encode_val (Tint8) (Vint32 (Int.repr 9)))).
      { FourApart 164%positive. }
      { split;[apply V293_encoded_memory_mapsto | reflexivity]. }
      eapply V293_wstate_star with (m1:=V293_encoded_memory 165%positive 0 true (encode_val (Tptr V293_tcb_type) (Vptr (211%positive,Int.zero)))).
      { FourApart 165%positive. }
      { split;[apply V293_encoded_memory_mapsto | reflexivity]. }
      eapply V293_wstate_star with (m1:=V293_encoded_memory 166%positive 0 true (encode_val (Tptr V293_tcb_type) (Vptr (212%positive,Int.zero)))).
      { FourApart 166%positive. }
      { split;[apply V293_encoded_memory_mapsto | reflexivity]. }
      eapply V293_wstate_star with (m1:=V293_encoded_memory 193%positive 0 true (encode_val (Tptr V293_event_type) (Vptr (213%positive,Int.zero))));
        [FourApart 193%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
      eapply V293_wstate_star with (m1:=V293_encoded_memory 82%positive 728 true (encode_val (Tint8) (Vint32 (Int.repr 17))));
        [FourApart 82%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
      eapply V293_wstate_star with (m1:=V293_encoded_memory 84%positive 52 true (encode_val (Tint8) (Vint32 (Int.repr 29))));
        [FourApart 84%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
      eapply V293_wstate_star with (m1:=V293_encoded_memory 99%positive 0 true (encode_val (Tint32) (Vint32 (Int.repr 123))));
        [FourApart 99%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
      eapply V293_wstate_star with (m1:=V293_encoded_memory 110%positive 0 true (encode_val Tint32 (Vint32 (Int.repr 7))));
        [FourApart 110%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
      exact I.
Qed.
Definition FourTail := V293_rdy_globals 161%positive 162%positive 163%positive 164%positive 165%positive 166%positive
  (Vint32 (Int.repr 7)) (Vint32 (Int.repr 3)) Vundef (Vint32 (Int.repr 5))
  (Vint32 (Int.repr 9)) (Vptr (211%positive,Int.zero)) (Vptr (212%positive,Int.zero))++
  V293_clr_bytes 82%positive 0 (repeat Vundef 728)++
  V293_clr_bytes 84%positive 0 (repeat (Vint32 (Int.repr 255)) 52)++FourHeads++FourEventBytes++FourEventHead++FourFrame.
Definition FourMiscCells : list (block*type*val) :=
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
Fixpoint FourMiscMem cells : mem := match cells with
 | []=>FourMemory | (b,tp,v)::tail=>merge (V293_encoded_memory b 0 true (encode_val tp v)) (FourMiscMem tail) end.
Definition FourEntryMemory := FourMiscMem FourMiscCells.
Lemma FourRawTail : FourState FourMemory |= V293_rdy_raw_cells FourTail Atrue.
Proof.
  pose proof FourLiteralEntry as H.
  unfold FourTail,FourKernelCells in *.
  repeat rewrite V293_raw_cells_append in *.
  assert (Perm : forall s,
    s |= V293_rdy_raw_cells FourEventBytes
      (V293_rdy_raw_cells (V293_clr_bytes 82%positive 0 (repeat Vundef 728))
       (V293_rdy_raw_cells (V293_clr_bytes 84%positive 0 (repeat (Vint32 (Int.repr 255)) 52))
        (V293_rdy_raw_cells FourHeads
         (V293_rdy_raw_cells FourReady (V293_rdy_raw_cells FourEventHead (V293_rdy_raw_cells FourFrame Atrue)))))) ->
    s |= V293_rdy_raw_cells FourReady
      (V293_rdy_raw_cells (V293_clr_bytes 82%positive 0 (repeat Vundef 728))
       (V293_rdy_raw_cells (V293_clr_bytes 84%positive 0 (repeat (Vint32 (Int.repr 255)) 52))
        (V293_rdy_raw_cells FourHeads
         (V293_rdy_raw_cells FourEventBytes (V293_rdy_raw_cells FourEventHead (V293_rdy_raw_cells FourFrame Atrue))))))).
  { intros st K.
    apply (V293_raw_cells_swap FourEventBytes _ _) in K.
    apply (V293_raw_cells_mono _ _ _ (V293_raw_cells_swap FourEventBytes _ _)) in K.
    apply (V293_raw_cells_mono _ _ _ (V293_raw_cells_mono _ _ _ (V293_raw_cells_swap FourEventBytes _ _))) in K.
    apply (V293_raw_cells_mono _ _ _ (V293_raw_cells_mono _ _ _
      (V293_raw_cells_mono _ _ _ (V293_raw_cells_swap FourEventBytes FourReady _)))) in K.
    apply (V293_raw_cells_mono _ _ _ (V293_raw_cells_mono _ _ _ (V293_raw_cells_swap FourHeads FourReady _))) in K.
    apply (V293_raw_cells_mono _ _ _ (V293_raw_cells_swap _ FourReady _)) in K.
    apply V293_raw_cells_swap in K;exact K. }
  apply Perm;exact H.
Qed.
Lemma FourSlotEntry : forall x tp b v,
 get FourGE x=Some (b,tp) ->
 V293_wstate FourGE emp (V293_encoded_memory b 0 true (encode_val tp v)) |=
  V293_init_binding (Build_V293_init_slot x tp b) ** V293_init_memory (Build_V293_init_slot x tp b) false.
Proof.
 intros x tp b v Env. eapply V293_wstate_star with (m1:=emp) (m2:=V293_encoded_memory b 0 true (encode_val tp v)).
 - apply map_join_comm;apply map_join_emp.
 - split.
   + exists b. split;[exact Env | ]. repeat split;reflexivity.
   + split;[intros [w E];change (None=Some w) in E;discriminate | split;reflexivity].
 - exists v. split;[apply V293_encoded_memory_mapsto | reflexivity].
Qed.
Theorem FourLiteralFullEntry : V293_wstate FourGE emp FourEntryMemory |=
  V293_init_resources FourSlots false (V293_rdy_raw_cells FourTail Atrue).
Proof.
 unfold FourEntryMemory,FourMiscCells,FourSlots,V293_InitMisc_slots.
 cbn [FourMiscMem V293_init_resources].
 eapply V293_wstate_star with (m1:=V293_encoded_memory 181%positive 0 true (encode_val (Tint32) (Vint32 (Int.repr 57)))).
 { apply map_join_merge;apply map_disjoint;intros [other off].
   destruct (Pos.eq_dec other 181%positive);[subst other;right;left | left];
   unfold FourMemory,FourEvent,FourTCB,FourPrio;cbn [FourKernelCells FourHeads FourReady FourEventHead V293_event_call_head FourFrame FourMem app];
   repeat first [rewrite V293_encoded_memory_outside by (left;congruence)
     | rewrite map_merge_semp by reflexivity];reflexivity. }
 { apply FourSlotEntry;vm_compute;reflexivity. }
 eapply V293_wstate_star with (m1:=V293_encoded_memory 182%positive 0 true (encode_val (Tint8) (Vint32 (Int.repr 3)))).
 { apply map_join_merge;apply map_disjoint;intros [other off].
   destruct (Pos.eq_dec other 182%positive);[subst other;right;left | left];
   unfold FourMemory,FourEvent,FourTCB,FourPrio;cbn [FourKernelCells FourHeads FourReady FourEventHead V293_event_call_head FourFrame FourMem app];
   repeat first [rewrite V293_encoded_memory_outside by (left;congruence)
     | rewrite map_merge_semp by reflexivity];reflexivity. }
 { apply FourSlotEntry;vm_compute;reflexivity. }
 eapply V293_wstate_star with (m1:=V293_encoded_memory 183%positive 0 true (encode_val (Tint8) (Vint32 (Int.repr 2)))).
 { apply map_join_merge;apply map_disjoint;intros [other off].
   destruct (Pos.eq_dec other 183%positive);[subst other;right;left | left];
   unfold FourMemory,FourEvent,FourTCB,FourPrio;cbn [FourKernelCells FourHeads FourReady FourEventHead V293_event_call_head FourFrame FourMem app];
   repeat first [rewrite V293_encoded_memory_outside by (left;congruence)
     | rewrite map_merge_semp by reflexivity];reflexivity. }
 { apply FourSlotEntry;vm_compute;reflexivity. }
 eapply V293_wstate_star with (m1:=V293_encoded_memory 184%positive 0 true (encode_val (Tint8) (Vint32 (Int.repr 9)))).
 { apply map_join_merge;apply map_disjoint;intros [other off].
   destruct (Pos.eq_dec other 184%positive);[subst other;right;left | left];
   unfold FourMemory,FourEvent,FourTCB,FourPrio;cbn [FourKernelCells FourHeads FourReady FourEventHead V293_event_call_head FourFrame FourMem app];
   repeat first [rewrite V293_encoded_memory_outside by (left;congruence)
     | rewrite map_merge_semp by reflexivity];reflexivity. }
 { apply FourSlotEntry;vm_compute;reflexivity. }
 eapply V293_wstate_star with (m1:=V293_encoded_memory 185%positive 0 true (encode_val (Tint8) (Vint32 Int.one))).
 { apply map_join_merge;apply map_disjoint;intros [other off].
   destruct (Pos.eq_dec other 185%positive);[subst other;right;left | left];
   unfold FourMemory,FourEvent,FourTCB,FourPrio;cbn [FourKernelCells FourHeads FourReady FourEventHead V293_event_call_head FourFrame FourMem app];
   repeat first [rewrite V293_encoded_memory_outside by (left;congruence)
     | rewrite map_merge_semp by reflexivity];reflexivity. }
 { apply FourSlotEntry;vm_compute;reflexivity. }
 eapply V293_wstate_star with (m1:=V293_encoded_memory 186%positive 0 true (encode_val (Tint32) (Vint32 (Int.repr 42)))).
 { apply map_join_merge;apply map_disjoint;intros [other off].
   destruct (Pos.eq_dec other 186%positive);[subst other;right;left | left];
   unfold FourMemory,FourEvent,FourTCB,FourPrio;cbn [FourKernelCells FourHeads FourReady FourEventHead V293_event_call_head FourFrame FourMem app];
   repeat first [rewrite V293_encoded_memory_outside by (left;congruence)
     | rewrite map_merge_semp by reflexivity];reflexivity. }
 { apply FourSlotEntry;vm_compute;reflexivity. }
 eapply V293_wstate_star with (m1:=V293_encoded_memory 187%positive 0 true (encode_val (Tint32) (Vundef))).
 { apply map_join_merge;apply map_disjoint;intros [other off].
   destruct (Pos.eq_dec other 187%positive);[subst other;right;left | left];
   unfold FourMemory,FourEvent,FourTCB,FourPrio;cbn [FourKernelCells FourHeads FourReady FourEventHead V293_event_call_head FourFrame FourMem app];
   repeat first [rewrite V293_encoded_memory_outside by (left;congruence)
     | rewrite map_merge_semp by reflexivity];reflexivity. }
 { apply FourSlotEntry;vm_compute;reflexivity. }
 eapply V293_wstate_star with (m1:=V293_encoded_memory 188%positive 0 true (encode_val (Tint32) (Vundef))).
 { apply map_join_merge;apply map_disjoint;intros [other off].
   destruct (Pos.eq_dec other 188%positive);[subst other;right;left | left];
   unfold FourMemory,FourEvent,FourTCB,FourPrio;cbn [FourKernelCells FourHeads FourReady FourEventHead V293_event_call_head FourFrame FourMem app];
   repeat first [rewrite V293_encoded_memory_outside by (left;congruence)
     | rewrite map_merge_semp by reflexivity];reflexivity. }
 { apply FourSlotEntry;vm_compute;reflexivity. }
 eapply V293_wstate_star with (m1:=V293_encoded_memory 189%positive 0 true (encode_val (Tint32) (Vint32 (Int.repr 100)))).
 { apply map_join_merge;apply map_disjoint;intros [other off].
   destruct (Pos.eq_dec other 189%positive);[subst other;right;left | left];
   unfold FourMemory,FourEvent,FourTCB,FourPrio;cbn [FourKernelCells FourHeads FourReady FourEventHead V293_event_call_head FourFrame FourMem app];
   repeat first [rewrite V293_encoded_memory_outside by (left;congruence)
     | rewrite map_merge_semp by reflexivity];reflexivity. }
 { apply FourSlotEntry;vm_compute;reflexivity. }
 eapply V293_wstate_star with (m1:=V293_encoded_memory 190%positive 0 true (encode_val (Tint8) (Vint32 Int.one))).
 { apply map_join_merge;apply map_disjoint;intros [other off].
   destruct (Pos.eq_dec other 190%positive);[subst other;right;left | left];
   unfold FourMemory,FourEvent,FourTCB,FourPrio;cbn [FourKernelCells FourHeads FourReady FourEventHead V293_event_call_head FourFrame FourMem app];
   repeat first [rewrite V293_encoded_memory_outside by (left;congruence)
     | rewrite map_merge_semp by reflexivity];reflexivity. }
 { apply FourSlotEntry;vm_compute;reflexivity. }
 eapply V293_raw_cells_environment;[right;reflexivity | exact FourRawTail].
Qed.
Definition FourProgram f :=
 if Z.eq_dec f 201%Z then Some (V293_InitMisc_function 1001%Z 1002%Z 1003%Z 1004%Z 1005%Z 1006%Z 1007%Z 1008%Z 1009%Z 1010%Z)
 else if Z.eq_dec f 202%Z then Some (V293_InitRdyList_function 21%Z 22%Z 23%Z 24%Z 25%Z 26%Z 41%Z)
 else if Z.eq_dec f 203%Z then Some (V293_InitTCBList_function 204%Z 31%Z 32%Z 33%Z 34%Z 41%Z 42%Z 43%Z 44%Z)
 else if Z.eq_dec f 205%Z then Some (V293_InitEventList_function 204%Z 35%Z 36%Z 41%Z 42%Z 43%Z 44%Z)
 else if Z.eq_dec f 204%Z then Some (V293_MemClr_function 11%Z 12%Z) else None.
Lemma FourLiteralOrder : V293_init_four_calls 201%Z 202%Z 203%Z 205%Z =
 sseq (sseq (scall 201%Z nil) (sseq (scall 202%Z nil) (scall 203%Z nil))) (scall 205%Z nil).
Proof. reflexivity. Qed.
Definition FourReadyZero := V293_rdy_globals 161%positive 162%positive 163%positive
  164%positive 165%positive 166%positive (Vint32 Int.zero) (Vint32 Int.zero)
  (Vint32 Int.zero) (Vint32 Int.zero) (Vint32 Int.zero) Vnull Vnull.
Definition FourExtraCells := FourReadyZero++V293_misc_zero_cells FourSlots++FourFrame.
Definition FourFinalCells := V293_event_call_result 193%positive 192%positive
  (V293_tcb_call_result 94%positive 95%positive 82%positive 84%positive FourExtraCells).
Definition FourChecks := V293_event_call_result 193%positive 192%positive []++
 V293_tcb_call_heads 94%positive 95%positive Vnull (Vptr (82%positive,Int.zero))++
 V293_tcb_linked_next 82%positive++V293_null_pointer_cells 84%positive 0 13++FourExtraCells.
Lemma FourCheckCount : length FourChecks=76%nat.
Proof. reflexivity. Qed.
Lemma FourChecksValid : forall a tp v, In (a,tp,v) FourChecks -> rule_type_val_match tp v=true.
Proof.
 intros a tp v Member.
 cbn [FourChecks V293_event_call_result V293_event_call_head V293_event_linked
   V293_event_untouched_cells V293_clr_bytes repeat
   V293_tcb_call_heads V293_tcb_linked_next V293_null_pointer_cells seq map
   FourExtraCells FourReadyZero V293_rdy_globals V293_misc_zero_cells FourSlots
   V293_InitMisc_slots FourFrame init_block init_type app] in Member.
 repeat (destruct Member as [E | Member];[inversion E;subst;reflexivity | ]);contradiction.
Qed.
Lemma FourChecksInFinal : forall a tp v, In (a,tp,v) FourChecks -> In (a,tp,v) FourFinalCells.
Proof.
 intros a tp v Member.
 unfold FourChecks,FourFinalCells,V293_event_call_result,V293_tcb_call_result in *.
 repeat rewrite in_app_iff in *;cbn [In] in *;tauto.
Qed.
Lemma FourExtraCount : length FourExtraCells=21%nat.
Proof. reflexivity. Qed.
Lemma FourExtrasValid : forall a tp v,
 In (a,tp,v) FourExtraCells -> rule_type_val_match tp v=true.
Proof.
 intros a tp v Member.
 cbn [FourExtraCells FourReadyZero V293_rdy_globals V293_misc_zero_cells FourSlots
   V293_InitMisc_slots FourFrame map app init_block init_type] in Member.
 repeat (destruct Member as [E | Member];[inversion E;subst;reflexivity | ]);contradiction.
Qed.
Lemma FourReadyEnvironment : forall bi,
 V293_rdy_env FourGE (V293_rdy_locals 41%Z bi) 21%Z 22%Z 23%Z 24%Z 25%Z 26%Z 41%Z
 161%positive 162%positive 163%positive 164%positive 165%positive 166%positive bi.
Proof. intro bi. repeat split;reflexivity. Qed.
Lemma FourTCBEnvironment : forall bi bn b1 b2,
 V293_tcb_link_env FourGE (V293_tcb_call_locals 41%Z 42%Z 43%Z 44%Z bi bn b1 b2)
 31%Z 33%Z 34%Z 41%Z 42%Z 43%Z 44%Z 82%positive 94%positive 95%positive bi bn b1 b2.
Proof. intros. repeat split;reflexivity. Qed.
Lemma FourEventEnvironment : forall bi bn b1 b2,
 V293_event_link_env FourGE (V293_event_call_locals 41%Z 42%Z 43%Z 44%Z bi bn b1 b2)
 35%Z 36%Z 41%Z 42%Z 43%Z 44%Z 192%positive 193%positive bi bn b1 b2.
Proof. intros. repeat split;reflexivity. Qed.
Theorem FourConcreteExecution : forall ks, exists Mtcb Mf bi bn b1 b2,
 cstepstar FourProgram (curs (V293_init_four_calls 201%Z 202%Z 203%Z 205%Z),(kenil,ks))
   (FourGE,FourCaller,FourEntryMemory) (curs (sskip None),(kenil,ks)) (FourGE,FourCaller,Mf) /\
 FourState Mf |= V293_rdy_raw_cells FourFinalCells Atrue /\
 (forall a tp v, In (a,tp,v) FourChecks -> load tp Mf a=Some v) /\
 cstepstar FourProgram (curs (V293_init_three_calls 201%Z 202%Z 203%Z),
   (kenil,kseq (scall 205%Z nil) ks)) (FourGE,FourCaller,FourEntryMemory)
   (curs (sskip None),(kenil,kseq (scall 205%Z nil) ks)) (FourGE,FourCaller,Mtcb) /\
 cstepstar FourProgram (curs (scall 205%Z nil),(kenil,ks)) (FourGE,FourCaller,Mtcb)
   (curs (sskip None),(kenil,ks)) (FourGE,FourCaller,Mf) /\ fresh Mtcb bi /\ fresh Mtcb bn /\ fresh Mtcb b1 /\ fresh Mtcb b2 /\
 (forall c tp k, In (c,tp) [(bi,Tint16);(bn,Tint16);(b1,Tptr V293_event_type);(b2,Tptr V293_event_type)] ->
   (k<typelen tp)%nat -> get Mf (c,Z.of_nat k)=None).
Proof.
 intro ks.
 destruct (V293_OSInit_four_calls FourSlots (repeat Vundef 728)
   (repeat (Vint32 (Int.repr 255)) 52) (repeat (Vint32 (Int.repr 255)) 32) FourFrame
   FourProgram ks FourGE FourCaller FourEntryMemory
   (fun _=>false) (false,nil,nil) emp (spec_done None)
   201%Z 202%Z 203%Z 204%Z 11%Z 12%Z 21%Z 22%Z 23%Z 24%Z 25%Z 26%Z 41%Z
   161%positive 162%positive 163%positive 164%positive 165%positive 166%positive
   31%Z 32%Z 33%Z 34%Z 41%Z 42%Z 43%Z 44%Z 82%positive 84%positive 94%positive 95%positive
   (Vint32 (Int.repr 7)) (Vint32 (Int.repr 3)) Vundef (Vint32 (Int.repr 5))
   (Vint32 (Int.repr 9)) (Vptr (211%positive,Int.zero)) (Vptr (212%positive,Int.zero))
   (Vptr (121%positive,Int.zero)) (Vptr (122%positive,Int.zero))
   205%Z 35%Z 36%Z 41%Z 42%Z 43%Z 44%Z 192%positive 193%positive (Vptr (213%positive,Int.zero))
   ltac:(unfold FourSlots,V293_InitMisc_slots;repeat (apply Forall_cons;[unfold V293_init_scalar;cbn;auto | ]);apply Forall_nil)
   ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)
   ltac:(discriminate) ltac:(lia) ltac:(lia) ltac:(lia)
   FourReadyEnvironment FourTCBEnvironment ltac:(intros;reflexivity) ltac:(reflexivity)
   ltac:(apply repeat_length) ltac:(apply repeat_length)
   ltac:(reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) FourEventEnvironment ltac:(apply repeat_length)
   FourLiteralFullEntry)
   as (Mtcb&Mf&bi&bn&b1&b2&Exec&Prefix&Event&Fi&Fn&F1&F2&Owned&Freed).
 exists Mtcb. exists Mf. exists bi. exists bn. exists b1. exists b2.
 split;[exact Exec | ]. split;[exact Owned | ]. split.
 - intros a tp v Member. change (load tp (getmem (FourState Mf)) a=Some v).
   eapply (V293_rdy_raw_load FourFinalCells Atrue);
     [apply FourChecksInFinal;exact Member | exact (FourChecksValid a tp v Member) | exact Owned].
 - split;[exact Prefix | ]. split;[exact Event | ].
   split;[exact Fi | ]. split;[exact Fn | ]. split;[exact F1 | ]. split;[exact F2 | exact Freed].
Qed.
Theorem FourReturnConnections : forall ks, exists Mf,
 cstepstar FourProgram (curs (V293_init_four_calls 201%Z 202%Z 203%Z 205%Z),(kenil,ks))
   (FourGE,FourCaller,FourEntryMemory) (curs (sskip None),(kenil,ks)) (FourGE,FourCaller,Mf) /\
 load (Tptr Tvoid) Mf (192%positive,4)=Some (Vptr (192%positive,Int.repr 16)) /\
 load (Tptr V293_event_type) Mf (193%positive,0)=Some (Vptr (192%positive,Int.zero)) /\
 load Tint8 Mf (161%positive,0)=Some (Vint32 Int.zero) /\
 load Tint32 Mf (99%positive,0)=Some (Vint32 (Int.repr 123)) /\
 load (Tptr Tvoid) Mf (192%positive,20)=Some Vnull /\
 load Tint32 Mf (110%positive,0)=Some (Vint32 (Int.repr 7)).
Proof.
 intro ks. destruct (FourConcreteExecution ks)
   as (Mtcb&Mf&bi&bn&b1&b2&Exec&Owned&Loads&Prefix&Event&Fi&Fn&F1&F2&Freed).
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
Print Assumptions FourLiteralFullEntry.
Print Assumptions FourLiteralOrder.
Print Assumptions FourConcreteExecution.
Print Assumptions FourReturnConnections.

(* Prospective single-factor ablation: remove only the fourth call. *)
Theorem FourWithoutEventCall : forall ks, exists Mtcb,
 cstepstar FourProgram (curs (V293_init_three_calls 201%Z 202%Z 203%Z),(kenil,ks))
   (FourGE,FourCaller,FourEntryMemory) (curs (sskip None),(kenil,ks)) (FourGE,FourCaller,Mtcb) /\
 load Tint8 Mtcb (192%positive,0)=Some (Vint32 (Int.repr 255)) /\
 load (Tptr V293_event_type) Mtcb (193%positive,0)=Some (Vptr (213%positive,Int.zero)) /\
 load Tint8 Mtcb (161%positive,0)=Some (Vint32 Int.zero) /\
 load Tint32 Mtcb (99%positive,0)=Some (Vint32 (Int.repr 123)).
Proof.
 intro ks.
 destruct (V293_OSInit_three_calls FourSlots (repeat Vundef 728)
   (repeat (Vint32 (Int.repr 255)) 52) (FourEventBytes++FourEventHead++FourFrame) FourProgram ks FourGE FourCaller FourEntryMemory
   (fun _=>false) (false,nil,nil) emp (spec_done None)
   201%Z 202%Z 203%Z 204%Z 11%Z 12%Z 21%Z 22%Z 23%Z 24%Z 25%Z 26%Z 41%Z
   161%positive 162%positive 163%positive 164%positive 165%positive 166%positive
   31%Z 32%Z 33%Z 34%Z 41%Z 42%Z 43%Z 44%Z 82%positive 84%positive 94%positive 95%positive
   (Vint32 (Int.repr 7)) (Vint32 (Int.repr 3)) Vundef (Vint32 (Int.repr 5))
   (Vint32 (Int.repr 9)) (Vptr (211%positive,Int.zero)) (Vptr (212%positive,Int.zero))
   (Vptr (121%positive,Int.zero)) (Vptr (122%positive,Int.zero))
   ltac:(unfold FourSlots,V293_InitMisc_slots;repeat (apply Forall_cons;[unfold V293_init_scalar;cbn;auto | ]);apply Forall_nil)
   ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)
   ltac:(discriminate) ltac:(lia) ltac:(lia) ltac:(lia)
   FourReadyEnvironment FourTCBEnvironment ltac:(intros;reflexivity) ltac:(reflexivity)
   ltac:(apply repeat_length) ltac:(apply repeat_length) FourLiteralFullEntry)
   as (Mmisc&Mrdy&Mf&bri&bi&bn&b1&b2&Exec&MiscExec&ReadyExec&TCBExec&Final&ReadyFreed&TCBFreed).

 exists Mf. split;[exact Exec | ].
 set (result:=V293_tcb_call_result 94%positive 95%positive 82%positive 84%positive
   (FourReadyZero++V293_misc_zero_cells FourSlots++FourEventBytes++FourEventHead++FourFrame)).
 change (FourState Mf |= V293_rdy_raw_cells result Atrue) in Final.
 assert (Load : forall a tp v, In (a,tp,v) result -> rule_type_val_match tp v=true -> load tp Mf a=Some v).
 { intros a tp v Member Valid. change (load tp (getmem (FourState Mf)) a=Some v).
   eapply (V293_rdy_raw_load result Atrue);eassumption. }
 split.
 - apply Load;[unfold result,V293_tcb_call_result;do 4 (apply in_or_app;right);
     apply in_or_app;right;apply in_or_app;right;apply in_or_app;left;left;reflexivity | reflexivity].
 - split.
   + apply Load;[unfold result,V293_tcb_call_result;do 4 (apply in_or_app;right);
       apply in_or_app;right;apply in_or_app;right;apply in_or_app;right;apply in_or_app;left;left;reflexivity | reflexivity].
   + split.
     * apply Load;[unfold result,V293_tcb_call_result;do 4 (apply in_or_app;right);
         apply in_or_app;left;left;reflexivity | reflexivity].
     * apply Load;[unfold result,V293_tcb_call_result;do 4 (apply in_or_app;right);
         apply in_or_app;right;apply in_or_app;right;apply in_or_app;right;apply in_or_app;right;
         unfold FourFrame;right;right;left;reflexivity | reflexivity].
Qed.
Print Assumptions FourWithoutEventCall.
