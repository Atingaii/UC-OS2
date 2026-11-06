Require Import CertiOS.certiucos.v293.proofs.V293InitTCBFinitePool.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFiniteAllocator.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
(* Whole call: independently encoded finite entry, absent callee locals, nonempty shadowed caller. *)
Require Import CertiOS.framework.include_frm.
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
Definition IPGE : env := set (set (set (set emp
  31%Z (82%positive,Tarray V293_tcb_type 13))
  32%Z (84%positive,Tarray (Tptr V293_tcb_type) 13))
  33%Z (94%positive,Tptr V293_tcb_type)) 34%Z (95%positive,Tptr V293_tcb_type).
Definition IPLE : env := set (set (set (set emp
  41%Z (90%positive,Tint8)) 42%Z (91%positive,Tint8))
  43%Z (92%positive,Tptr V293_tcb_type)) 44%Z (93%positive,Tptr V293_tcb_type).
Definition IPTCB := V293_encoded_memory 82%positive 0 true (repeat Undef 728).
Definition IPPrio := V293_encoded_memory 84%positive 0 true (repeat (Byte (Byte.repr 255)) 52).
Definition IPLocals : list V293_record_cell :=
  [((94%positive,0),Tptr V293_tcb_type,Vptr (121%positive,Int.zero));
   ((95%positive,0),Tptr V293_tcb_type,Vptr (122%positive,Int.zero))].
Definition IPFrame : list V293_record_cell :=
  [((82%positive,728),Tint8,Vint32 (Int.repr 17));
   ((84%positive,52),Tint8,Vint32 (Int.repr 29));
   ((99%positive,0),Tint32,Vint32 (Int.repr 123));
   ((110%positive,0),Tint32,Vint32 (Int.repr 7))].
Fixpoint IPMem (cells : list V293_record_cell) : mem :=
  match cells with []=>emp | ((b,off),tp,v)::tail=>
    merge (V293_encoded_memory b off true (encode_val tp v)) (IPMem tail) end.
Definition IPMemory := merge IPTCB (merge IPPrio (IPMem (IPLocals++IPFrame))).
Definition IPCaller : env := set emp 41%Z (110%positive,Tint32).
Definition IPState M := V293_wstate IPGE IPCaller M.

Lemma IPConstantRange : forall n v byte ge le b off,
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
Ltac IPOutside :=
  unfold IPTCB,IPPrio;
  cbn [IPLocals IPFrame IPMem app];
  repeat rewrite map_merge_semp by reflexivity;
  repeat rewrite V293_encoded_memory_outside by
    (first [left;congruence | right;rewrite ?repeat_length;cbn [length encode_val inj_bytes encode_int];lia]);
  reflexivity.
Ltac IPApart b :=
  apply map_join_merge;apply map_disjoint;intros [other off];
  destruct (Pos.eq_dec other b);[subst other;right;left | left];
  repeat rewrite map_merge_semp by reflexivity;
  repeat rewrite V293_encoded_memory_outside by (left;congruence);reflexivity.
Lemma IPLiteralEntry : IPState IPMemory |= V293_rdy_raw_cells
  (V293_clr_bytes 82%positive 0 (repeat Vundef 728)++
   V293_clr_bytes 84%positive 0 (repeat (Vint32 (Int.repr 255)) 52)++IPLocals++IPFrame) Atrue.
Proof.
  unfold IPState,IPMemory. repeat rewrite V293_raw_cells_append.
  apply (V293_raw_cells_join (V293_clr_bytes 82%positive 0 (repeat Vundef 728))
    (V293_rdy_raw_cells (V293_clr_bytes 84%positive 0 (repeat (Vint32 (Int.repr 255)) 52))
      (V293_rdy_raw_cells IPLocals (V293_rdy_raw_cells IPFrame Atrue)))).
  eapply V293_wstate_star with (m1:=IPTCB).
  - apply map_join_merge;apply map_disjoint;intros [b i].
    destruct (Pos.eq_dec b 82%positive) as [B|B].
    + subst b. destruct (Z_lt_dec i 728) as [I|I].
      * right;left;IPOutside.
      * left. unfold IPTCB. apply V293_encoded_memory_outside. right;right. rewrite repeat_length;lia.
    + left. unfold IPTCB. apply V293_encoded_memory_outside;left;exact B.
  - unfold IPTCB;apply IPConstantRange;reflexivity.
  - apply (V293_raw_cells_join (V293_clr_bytes 84%positive 0 (repeat (Vint32 (Int.repr 255)) 52))
      (V293_rdy_raw_cells IPLocals (V293_rdy_raw_cells IPFrame Atrue))).
    eapply V293_wstate_star with (m1:=IPPrio).
    + apply map_join_merge;apply map_disjoint;intros [b i].
      destruct (Pos.eq_dec b 84%positive) as [B|B].
      * subst b. destruct (Z_lt_dec i 52) as [I|I].
        -- right;left;IPOutside.
        -- left. unfold IPPrio. apply V293_encoded_memory_outside. right;right. rewrite repeat_length;lia.
      * left. unfold IPPrio. apply V293_encoded_memory_outside;left;exact B.
    + unfold IPPrio;apply IPConstantRange;reflexivity.
    + cbn [IPLocals IPFrame IPMem app V293_rdy_raw_cells].
      eapply V293_wstate_star with (m1:=V293_encoded_memory 94%positive 0 true (encode_val (Tptr V293_tcb_type) (Vptr (121%positive,Int.zero))));
        [IPApart 94%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
      eapply V293_wstate_star with (m1:=V293_encoded_memory 95%positive 0 true (encode_val (Tptr V293_tcb_type) (Vptr (122%positive,Int.zero))));
        [IPApart 95%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
      eapply V293_wstate_star with (m1:=V293_encoded_memory 82%positive 728 true (encode_val (Tint8) (Vint32 (Int.repr 17))));
        [IPApart 82%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
      eapply V293_wstate_star with (m1:=V293_encoded_memory 84%positive 52 true (encode_val (Tint8) (Vint32 (Int.repr 29))));
        [IPApart 84%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
      eapply V293_wstate_star with (m1:=V293_encoded_memory 99%positive 0 true (encode_val (Tint32) (Vint32 (Int.repr 123))));
        [IPApart 99%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
      eapply V293_wstate_star with (m1:=V293_encoded_memory 110%positive 0 true (encode_val Tint32 (Vint32 (Int.repr 7))));
        [IPApart 110%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
      exact I.
Qed.
Definition IPProgram f :=
  if Z.eq_dec f 100%Z then Some (V293_InitTCBList_function 101%Z 31%Z 32%Z 33%Z 34%Z 41%Z 42%Z 43%Z 44%Z)
  else if Z.eq_dec f 101%Z then Some (V293_MemClr_function 11%Z 12%Z) else None.
Lemma IPEnvironment : V293_tcb_link_env IPGE IPLE 31%Z 33%Z 34%Z 41%Z 42%Z 43%Z 44%Z
  82%positive 94%positive 95%positive 90%positive 91%positive 92%positive 93%positive.
Proof. vm_compute;repeat split;reflexivity. Qed.
Lemma IPAbsentLocals : forall b, In b [90%positive;91%positive;92%positive;93%positive] -> fresh IPMemory b.
Proof.
  intros b Member a i E [v Read];subst a.
  assert (Absent : get IPMemory (b,i)=None).
  { destruct Member as [E|[E|[E|[E|E]]]];try contradiction;subst b;
      unfold IPMemory;IPOutside. }
  change (get IPMemory (b,i)=Some v) in Read.
  assert (Conflict : None=Some v) by (etransitivity;[symmetry;exact Absent|exact Read]).
  discriminate Conflict.
Qed.
Lemma IPLiteralAST : V293_InitTCBList_function 101%Z 31%Z 32%Z 33%Z 34%Z 41%Z 42%Z 43%Z 44%Z =
(Tvoid,dnil,dcons 41%Z Tint8 (dcons 42%Z Tint8 (dcons 43%Z (Tptr V293_tcb_type) (dcons 44%Z (Tptr V293_tcb_type) dnil))), sseq
(sseq (sseq (scall 101%Z [(ecast (eaddrof (earrayelem (evar 31%Z) (econst32 Int.zero))) (Tptr Tint8));(ecast (econst32 (Int.repr 728)) Tint16)]) (scall 101%Z [(ecast (eaddrof (earrayelem (evar 32%Z) (econst32 Int.zero))) (Tptr Tint8));(ecast (econst32 (Int.repr 52)) Tint16)])) (sseq (sassign (evar 41%Z) (ecast (econst32 Int.zero) Tint8)) (sseq (swhile (ebinop olt (ecast (evar 41%Z) Tint32) (econst32 (Int.repr 12))) (sseq (sassign (evar 42%Z) (ecast (ebinop oplus (ecast (evar 41%Z) Tint32) (econst32 Int.one)) Tint8)) (sseq (sassign (evar 43%Z) (eaddrof (earrayelem (evar 31%Z) (evar 41%Z)))) (sseq (sassign (evar 44%Z) (eaddrof (earrayelem (evar 31%Z) (evar 42%Z)))) (sseq (sassign (efield (ederef (evar 43%Z)) 7%Z) (evar 44%Z)) (sassign (evar 41%Z) (ecast (ebinop oplus (ecast (evar 41%Z) Tint32) (econst32 Int.one)) Tint8))))))) (sseq (sassign (evar 43%Z) (eaddrof (earrayelem (evar 31%Z) (evar 41%Z)))) (sseq (sassign (efield (ederef (evar 43%Z)) 7%Z) (ecast enull (Tptr V293_tcb_type))) (sseq (sassign (evar 33%Z) (ecast enull (Tptr V293_tcb_type))) (sassign (evar 34%Z) (eaddrof (earrayelem (evar 31%Z) (econst32 Int.zero)))))))))) sret).
Proof. reflexivity. Qed.
Definition IPFinalCells := V293_tcb_call_result 94%positive 95%positive 82%positive 84%positive IPFrame.
Lemma IPAway : forall a tp v, In (a,tp,v) IPFinalCells ->
  ~In (fst a) (V293_tcb_call_blocks 90%positive 91%positive 92%positive 93%positive).
Proof.
  intros a tp v Member. unfold IPFinalCells,V293_tcb_call_result in Member.
  repeat rewrite in_app_iff in Member. destruct Member as [H|[H|[H|[H|H]]]].
  - cbn [V293_tcb_call_heads] in H. destruct H as [E|[E|E]];try contradiction;inversion E;subst;cbn;intuition congruence.
  - unfold V293_tcb_linked_next in H. apply in_app_iff in H. destruct H as [H|[E|E]];try contradiction.
    + apply in_map_iff in H. destruct H as [i [E Hi]]. inversion E;subst;cbn;intuition congruence.
    + inversion E;subst;cbn;intuition congruence.
  - assert (fst a=82%positive).
    { clear -H. remember 13%nat as n in H. remember 0%Z as off in H. clear Heqn Heqoff. revert off H.
      induction n;intros off H;cbn [V293_tcb_untouched_cells] in H;[contradiction| ].
      repeat rewrite in_app_iff in H. destruct H as [H|[H|H]];
        [eapply V293_clr_bytes_blocks;exact H|eapply V293_clr_bytes_blocks;exact H|eapply IHn;exact H]. }
    rewrite H0;cbn;intuition congruence.
  - unfold V293_null_pointer_cells in H.
    repeat (destruct H as [E|H];[inversion E;subst;cbn;intuition congruence| ]);contradiction.
  - cbn [IPFrame] in H. destruct H as [E|[E|[E|[E|E]]]];try contradiction;inversion E;subst;cbn;intuition congruence.
Qed.
Ltac IPRead H :=
  lazymatch goal with |- load ?tp ?M ?a=Some ?v =>
    change (load tp (getmem (IPState M)) a=Some v);
    eapply (V293_rdy_raw_load IPFinalCells Atrue);[ | reflexivity | exact H]
  end.
Theorem IPConcreteExecution : forall ks, exists Ms Mf,
  cstepstar IPProgram (curs (scall 100%Z nil),(kenil,ks))
    (IPGE,IPCaller,IPMemory) (curs (sskip None),(kenil,ks)) (IPGE,IPCaller,Mf) /\
  IPState Mf |= V293_rdy_raw_cells IPFinalCells Atrue /\
  (forall i, (i<12)%nat -> load (Tcom_ptr 410) Mf (82%positive,56*Z.of_nat i+20)=
    Some (Vptr (82%positive,Int.repr (56*Z.of_nat (S i))))) /\
  load (Tcom_ptr 410) Mf (82%positive,692)=Some Vnull /\
  load (Tptr V293_tcb_type) Mf (94%positive,0)=Some Vnull /\
  load (Tptr V293_tcb_type) Mf (95%positive,0)=Some (Vptr (82%positive,Int.zero)) /\
  (forall p, (p<13)%nat -> load (Tptr V293_tcb_type) Mf (84%positive,4*Z.of_nat p)=Some Vnull) /\
  load Tint8 Mf (82%positive,0)=Some (Vint32 Int.zero) /\
  load Tint8 Mf (82%positive,728)=Some (Vint32 (Int.repr 17)) /\
  load Tint8 Mf (84%positive,52)=Some (Vint32 (Int.repr 29)) /\
  load Tint32 Mf (99%positive,0)=Some (Vint32 (Int.repr 123)) /\
  load Tint32 Mf (110%positive,0)=Some (Vint32 (Int.repr 7)) /\
  (forall b tp k, In (b,tp) [(90%positive,Tint8);(91%positive,Tint8);(92%positive,Tptr V293_tcb_type);(93%positive,Tptr V293_tcb_type)] ->
    (k<typelen tp)%nat -> get Mf (b,Z.of_nat k)=None) /\
  load Tint8 Ms (90%positive,0)=Some (Vint32 (Int.repr 12)) /\
  evalval (evar 41%Z) (IPGE,IPCaller,Mf)=Some (Vint32 (Int.repr 7)).
Proof.
  intro ks.
  destruct (V293_OS_InitTCBList_call_return (repeat Vundef 728)
    (repeat (Vint32 (Int.repr 255)) 52) IPFrame IPProgram ks IPGE IPCaller IPMemory
    (fun _=>false) (false,nil,nil) emp (spec_done None)
    100%Z 101%Z 11%Z 12%Z 31%Z 32%Z 33%Z 34%Z 41%Z 42%Z 43%Z 44%Z
    82%positive 84%positive 94%positive 95%positive 90%positive 91%positive 92%positive 93%positive
    (Vptr (121%positive,Int.zero)) (Vptr (122%positive,Int.zero))
    ltac:(reflexivity) ltac:(reflexivity) ltac:(discriminate)
    ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(repeat constructor;cbn;intuition congruence)
    ltac:(apply IPAbsentLocals;cbn;auto) ltac:(apply IPAbsentLocals;cbn;auto)
    ltac:(apply IPAbsentLocals;cbn;auto) ltac:(apply IPAbsentLocals;cbn;auto)
    IPEnvironment ltac:(reflexivity) ltac:(reflexivity)
    ltac:(apply repeat_length) ltac:(apply repeat_length) IPAway IPLiteralEntry)
    as (Ms&Mf&Exec&PreFree&Final&Preserve&Removed).
  exists Ms. exists Mf. split;[exact Exec| ]. split;[exact Final| ].
  split.
  - intros i Small. IPRead Final. unfold IPFinalCells,V293_tcb_call_result.
    apply in_or_app;right. apply in_or_app;left.
    unfold V293_tcb_linked_next. apply in_or_app;left.
    apply in_map_iff. exists i. split;[reflexivity|apply in_seq;lia].
  - split.
    + IPRead Final. unfold IPFinalCells,V293_tcb_call_result.
      apply in_or_app;right. apply in_or_app;left.
      unfold V293_tcb_linked_next. apply in_or_app;right;left;reflexivity.
    + split.
      * IPRead Final. unfold IPFinalCells,V293_tcb_call_result. apply in_or_app;left;left;reflexivity.
      * split.
        -- IPRead Final. unfold IPFinalCells,V293_tcb_call_result. apply in_or_app;left;right;left;reflexivity.
        -- split.
           ++ intros p Small. IPRead Final. unfold IPFinalCells,V293_tcb_call_result.
              apply in_or_app;right. apply in_or_app;right. apply in_or_app;right. apply in_or_app;left.
              replace (4*Z.of_nat p) with (0+4*Z.of_nat p) by lia.
              apply V293_null_pointer_member;exact Small.
           ++ split.
              ** IPRead Final. unfold IPFinalCells,V293_tcb_call_result.
                 apply in_or_app;right. apply in_or_app;right. apply in_or_app;left.
                 cbn [V293_tcb_untouched_cells]. apply in_or_app;left;left;reflexivity.
              ** assert (FrameRead : forall a tp v, In (a,tp,v) IPFrame -> rule_type_val_match tp v=true -> load tp Mf a=Some v).
                 { intros a tp v Member Valid. change (load tp (getmem (IPState Mf)) a=Some v).
                   eapply (V293_rdy_raw_load IPFinalCells Atrue);[ | exact Valid|exact Final].
                   unfold IPFinalCells,V293_tcb_call_result. do 4 (apply in_or_app;right). exact Member. }
                 repeat split.
                 --- apply FrameRead;[left;reflexivity|reflexivity].
                 --- apply FrameRead;[right;left;reflexivity|reflexivity].
                 --- apply FrameRead;[right;right;left;reflexivity|reflexivity].
                 --- apply FrameRead;[right;right;right;left;reflexivity|reflexivity].
                 --- exact Removed.
                 --- change (load Tint8 (getmem (V293_wstate IPGE IPLE Ms)) (90%positive,0)=Some (Vint32 (Int.repr 12))).
                     eapply V293_rdy_raw_load;[ | reflexivity|exact PreFree].
                     unfold V293_tcb_link_final,V293_tcb_link_locals. apply in_or_app;left;left;reflexivity.
                 --- cbn [evalval evaladdr get_smem get_genv get_lenv IPCaller].
                     change (load Tint32 Mf (110%positive,0)=Some (Vint32 (Int.repr 7))).
                     apply FrameRead;[right;right;right;left;reflexivity|reflexivity].
Qed.
Print Assumptions IPLiteralEntry.
Print Assumptions IPLiteralAST.
Print Assumptions IPConcreteExecution.


(* The actual same returned Mf, not a second execution or a pre-assumed pool. *)
Theorem IPActualCallFinitePool : forall ks, exists Mf,
 cstepstar IPProgram(curs(scall 100%Z nil),(kenil,ks))
 (IPGE,IPCaller,IPMemory)(curs(sskip None),(kenil,ks))(IPGE,IPCaller,Mf) /\
 IPState Mf |= V293_tcb_site_free_pool 82%positive 95%positive **
 V293_init_tcb_pool_rest 94%positive 84%positive IPFrame /\
 IPState Mf |= V293_rdy_raw_cells IPFinalCells Atrue /\
 (forall i,(i<12)%nat -> load(Tcom_ptr 410)Mf(82%positive,56*Z.of_nat i+20)=
  Some(Vptr(82%positive,Int.repr(56*Z.of_nat(S i))))) /\
 load(Tcom_ptr 410)Mf(82%positive,692)=Some Vnull /\
 load(Tptr V293_tcb_type)Mf(95%positive,0)=Some(Vptr(82%positive,Int.zero)).
Proof.
 intro ks. destruct(IPConcreteExecution ks)as(Ms&Mf&Exec&Raw&Links&Last&Active&Head&Rest).
 exists Mf. split;[exact Exec| ]. split.
 - apply V293_tcb_call_result_pool;exact Raw.
 - split;[exact Raw| ]. split;[exact Links| ]. split;assumption.
Qed.
Theorem IPStableInterfaceChecked : forall ks, exists Mf,
 cstepstar IPProgram(curs(scall 100%Z nil),(kenil,ks))
 (IPGE,IPCaller,IPMemory)(curs(sskip None),(kenil,ks))(IPGE,IPCaller,Mf) /\
 IPState Mf |= V293_tcb_site_free_pool 82%positive 95%positive **
 V293_init_tcb_pool_rest 94%positive 84%positive IPFrame /\
 (forall b tp k,In(b,tp)[(90%positive,Tint8);(91%positive,Tint8);
 (92%positive,Tptr V293_tcb_type);(93%positive,Tptr V293_tcb_type)] ->
 (k<typelen tp)%nat -> get Mf(b,Z.of_nat k)=None).
Proof.
 intro ks. exact(V293_OS_InitTCBList_call_finite_pool (repeat Vundef 728)
    (repeat (Vint32 (Int.repr 255)) 52) IPFrame IPProgram ks IPGE IPCaller IPMemory
    (fun _=>false) (false,nil,nil) emp (spec_done None)
    100%Z 101%Z 11%Z 12%Z 31%Z 32%Z 33%Z 34%Z 41%Z 42%Z 43%Z 44%Z
    82%positive 84%positive 94%positive 95%positive 90%positive 91%positive 92%positive 93%positive
    (Vptr (121%positive,Int.zero)) (Vptr (122%positive,Int.zero))
    ltac:(reflexivity) ltac:(reflexivity) ltac:(discriminate)
    ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(repeat constructor;cbn;intuition congruence)
    ltac:(apply IPAbsentLocals;cbn;auto) ltac:(apply IPAbsentLocals;cbn;auto)
    ltac:(apply IPAbsentLocals;cbn;auto) ltac:(apply IPAbsentLocals;cbn;auto)
    IPEnvironment ltac:(reflexivity) ltac:(reflexivity)
    ltac:(apply repeat_length) ltac:(apply repeat_length) IPAway IPLiteralEntry).
Qed.

Fixpoint IPWalk (n:nat)(M:mem)(head:val) : option val :=
 match n with O=>Some head|S n=>
 match head with Vnull=>Some Vnull|Vptr(b,off)=>
 match load(Tcom_ptr 410)M(b,Int.unsigned off+20)with
 Some next=>IPWalk n M next|None=>None end|_=>None end end.
Lemma IPWalkAt : forall n M off next,
 0<=off<=Int.max_unsigned ->
 load(Tcom_ptr 410)M(82%positive,off+20)=Some next ->
 IPWalk(S n)M(Vptr(82%positive,Int.repr off))=IPWalk n M next.
Proof.
 intros n M off next Bound Read.
 change((match load(Tcom_ptr 410)M(82%positive,Int.unsigned(Int.repr off)+20)with
 Some v=>IPWalk n M v|None=>None end)=IPWalk n M next).
 rewrite Int.unsigned_repr by exact Bound. cbv delta [block] in *. rewrite Read. reflexivity.
Qed.
Lemma IPActualThirteenReachable : forall M,
 (forall i,(i<12)%nat -> load(Tcom_ptr 410)M(82%positive,56*Z.of_nat i+20)=
 Some(Vptr(82%positive,Int.repr(56*Z.of_nat(S i))))) ->
 load(Tcom_ptr 410)M(82%positive,692)=Some Vnull ->
 IPWalk 12 M(Vptr(82%positive,Int.zero))=Some(Vptr(82%positive,Int.repr 672)) /\
 IPWalk 13 M(Vptr(82%positive,Int.zero))=Some Vnull.
Proof.
 intros M Links Last. split.
 - change(IPWalk 12 M(Vptr(82%positive,Int.repr 0))=Some(Vptr(82%positive,Int.repr 672))).
   pose proof(Links 0%nat ltac:(lia))as E.
   change(load(Tcom_ptr 410)M(82%positive,20)=Some(Vptr(82%positive,Int.repr 56)))in E.
   rewrite(IPWalkAt 11 M 0 _ ltac:(vm_compute;intuition congruence) E). clear E.
   pose proof(Links 1%nat ltac:(lia))as E.
   change(load(Tcom_ptr 410)M(82%positive,76)=Some(Vptr(82%positive,Int.repr 112)))in E.
   rewrite(IPWalkAt 10 M 56 _ ltac:(vm_compute;intuition congruence) E). clear E.
   pose proof(Links 2%nat ltac:(lia))as E.
   change(load(Tcom_ptr 410)M(82%positive,132)=Some(Vptr(82%positive,Int.repr 168)))in E.
   rewrite(IPWalkAt 9 M 112 _ ltac:(vm_compute;intuition congruence) E). clear E.
   pose proof(Links 3%nat ltac:(lia))as E.
   change(load(Tcom_ptr 410)M(82%positive,188)=Some(Vptr(82%positive,Int.repr 224)))in E.
   rewrite(IPWalkAt 8 M 168 _ ltac:(vm_compute;intuition congruence) E). clear E.
   pose proof(Links 4%nat ltac:(lia))as E.
   change(load(Tcom_ptr 410)M(82%positive,244)=Some(Vptr(82%positive,Int.repr 280)))in E.
   rewrite(IPWalkAt 7 M 224 _ ltac:(vm_compute;intuition congruence) E). clear E.
   pose proof(Links 5%nat ltac:(lia))as E.
   change(load(Tcom_ptr 410)M(82%positive,300)=Some(Vptr(82%positive,Int.repr 336)))in E.
   rewrite(IPWalkAt 6 M 280 _ ltac:(vm_compute;intuition congruence) E). clear E.
   pose proof(Links 6%nat ltac:(lia))as E.
   change(load(Tcom_ptr 410)M(82%positive,356)=Some(Vptr(82%positive,Int.repr 392)))in E.
   rewrite(IPWalkAt 5 M 336 _ ltac:(vm_compute;intuition congruence) E). clear E.
   pose proof(Links 7%nat ltac:(lia))as E.
   change(load(Tcom_ptr 410)M(82%positive,412)=Some(Vptr(82%positive,Int.repr 448)))in E.
   rewrite(IPWalkAt 4 M 392 _ ltac:(vm_compute;intuition congruence) E). clear E.
   pose proof(Links 8%nat ltac:(lia))as E.
   change(load(Tcom_ptr 410)M(82%positive,468)=Some(Vptr(82%positive,Int.repr 504)))in E.
   rewrite(IPWalkAt 3 M 448 _ ltac:(vm_compute;intuition congruence) E). clear E.
   pose proof(Links 9%nat ltac:(lia))as E.
   change(load(Tcom_ptr 410)M(82%positive,524)=Some(Vptr(82%positive,Int.repr 560)))in E.
   rewrite(IPWalkAt 2 M 504 _ ltac:(vm_compute;intuition congruence) E). clear E.
   pose proof(Links 10%nat ltac:(lia))as E.
   change(load(Tcom_ptr 410)M(82%positive,580)=Some(Vptr(82%positive,Int.repr 616)))in E.
   rewrite(IPWalkAt 1 M 560 _ ltac:(vm_compute;intuition congruence) E). clear E.
   pose proof(Links 11%nat ltac:(lia))as E.
   change(load(Tcom_ptr 410)M(82%positive,636)=Some(Vptr(82%positive,Int.repr 672)))in E.
   rewrite(IPWalkAt 0 M 616 _ ltac:(vm_compute;intuition congruence) E). clear E.
   reflexivity.
 - change(IPWalk 13 M(Vptr(82%positive,Int.repr 0))=Some Vnull).
   pose proof(Links 0%nat ltac:(lia))as E.
   change(load(Tcom_ptr 410)M(82%positive,20)=Some(Vptr(82%positive,Int.repr 56)))in E.
   rewrite(IPWalkAt 12 M 0 _ ltac:(vm_compute;intuition congruence) E). clear E.
   pose proof(Links 1%nat ltac:(lia))as E.
   change(load(Tcom_ptr 410)M(82%positive,76)=Some(Vptr(82%positive,Int.repr 112)))in E.
   rewrite(IPWalkAt 11 M 56 _ ltac:(vm_compute;intuition congruence) E). clear E.
   pose proof(Links 2%nat ltac:(lia))as E.
   change(load(Tcom_ptr 410)M(82%positive,132)=Some(Vptr(82%positive,Int.repr 168)))in E.
   rewrite(IPWalkAt 10 M 112 _ ltac:(vm_compute;intuition congruence) E). clear E.
   pose proof(Links 3%nat ltac:(lia))as E.
   change(load(Tcom_ptr 410)M(82%positive,188)=Some(Vptr(82%positive,Int.repr 224)))in E.
   rewrite(IPWalkAt 9 M 168 _ ltac:(vm_compute;intuition congruence) E). clear E.
   pose proof(Links 4%nat ltac:(lia))as E.
   change(load(Tcom_ptr 410)M(82%positive,244)=Some(Vptr(82%positive,Int.repr 280)))in E.
   rewrite(IPWalkAt 8 M 224 _ ltac:(vm_compute;intuition congruence) E). clear E.
   pose proof(Links 5%nat ltac:(lia))as E.
   change(load(Tcom_ptr 410)M(82%positive,300)=Some(Vptr(82%positive,Int.repr 336)))in E.
   rewrite(IPWalkAt 7 M 280 _ ltac:(vm_compute;intuition congruence) E). clear E.
   pose proof(Links 6%nat ltac:(lia))as E.
   change(load(Tcom_ptr 410)M(82%positive,356)=Some(Vptr(82%positive,Int.repr 392)))in E.
   rewrite(IPWalkAt 6 M 336 _ ltac:(vm_compute;intuition congruence) E). clear E.
   pose proof(Links 7%nat ltac:(lia))as E.
   change(load(Tcom_ptr 410)M(82%positive,412)=Some(Vptr(82%positive,Int.repr 448)))in E.
   rewrite(IPWalkAt 5 M 392 _ ltac:(vm_compute;intuition congruence) E). clear E.
   pose proof(Links 8%nat ltac:(lia))as E.
   change(load(Tcom_ptr 410)M(82%positive,468)=Some(Vptr(82%positive,Int.repr 504)))in E.
   rewrite(IPWalkAt 4 M 448 _ ltac:(vm_compute;intuition congruence) E). clear E.
   pose proof(Links 9%nat ltac:(lia))as E.
   change(load(Tcom_ptr 410)M(82%positive,524)=Some(Vptr(82%positive,Int.repr 560)))in E.
   rewrite(IPWalkAt 3 M 504 _ ltac:(vm_compute;intuition congruence) E). clear E.
   pose proof(Links 10%nat ltac:(lia))as E.
   change(load(Tcom_ptr 410)M(82%positive,580)=Some(Vptr(82%positive,Int.repr 616)))in E.
   rewrite(IPWalkAt 2 M 560 _ ltac:(vm_compute;intuition congruence) E). clear E.
   pose proof(Links 11%nat ltac:(lia))as E.
   change(load(Tcom_ptr 410)M(82%positive,636)=Some(Vptr(82%positive,Int.repr 672)))in E.
   rewrite(IPWalkAt 1 M 616 _ ltac:(vm_compute;intuition congruence) E). clear E.
   rewrite(IPWalkAt 0 M 672 Vnull ltac:(vm_compute;intuition congruence) Last). reflexivity.
Qed.
Definition IPAfterFirst :=
 skipn 1(V293_tcb_linked_next 82%positive)++V293_tcb_untouched_cells 82%positive 0 13++
 V293_null_pointer_cells 84%positive 0 13++IPFrame.
(* Change exactly one physical Next cell. All other bytes, including the
   unreachable 12 nodes, cleared payload, heads/priorities/frame stay fixed.
   A fuel bound is not an exact reachable-node count: no claim that the
   refined pool itself is false after truncation. *)
Theorem IPFirstNextNullAblation : forall M,
 IPState M |= V293_rdy_raw_cells IPFinalCells Atrue ->
 exists Bad,
 store(Tcom_ptr 410)M(82%positive,20)Vnull=Some Bad /\
 (forall b j,b<>82%positive \/ j<20 \/ 24<=j -> get Bad(b,j)=get M(b,j)) /\
 load(Tcom_ptr 410)Bad(82%positive,20)=Some Vnull /\
 load(Tcom_ptr 410)Bad(82%positive,76)=Some(Vptr(82%positive,Int.repr 112)) /\
 IPWalk 1 M(Vptr(82%positive,Int.zero))=Some(Vptr(82%positive,Int.repr 56)) /\
 IPWalk 1 Bad(Vptr(82%positive,Int.zero))=Some Vnull /\
 IPWalk 12 Bad(Vptr(82%positive,Int.zero))<>Some(Vptr(82%positive,Int.repr 672)).
Proof.
 intros M Raw. cbv delta [block] in *.
 assert(First:load(Tcom_ptr 410)M(82%positive,20)=Some(Vptr(82%positive,Int.repr 56))).
 { IPRead Raw. unfold IPFinalCells,V293_tcb_call_result,V293_tcb_linked_next.
   apply in_or_app;right. apply in_or_app;left. apply in_or_app;left. left;reflexivity. }
 change(IPState M |= V293_rdy_raw_cells(V293_tcb_call_heads 94%positive 95%positive Vnull
 (Vptr(82%positive,Int.zero))++((82%positive,20),Tcom_ptr 410,Vptr(82%positive,Int.repr 56))::IPAfterFirst)Atrue)in Raw.
 apply V293_rdy_cell_out in Raw.
 destruct(V293_tick_raw_slot_update (82%positive,20) (Tcom_ptr 410) (Vptr(82%positive,Int.repr 56)) Vnull _ _ _ _ _ _ _ _ ltac:(reflexivity) Raw)
 as(Bad&Store&Updated).
 unfold V293_owned_record_cell in Updated. apply astar_assoc_elim in Updated.
 apply astar_l_apure_elim in Updated. destruct Updated as[Typed Updated].
 apply V293_rdy_cell_in in Updated.
 assert(NextNull:load(Tcom_ptr 410)Bad(82%positive,20)=Some Vnull).
 { change(load(Tcom_ptr 410)(getmem(IPState Bad))(82%positive,20)=Some Vnull).
   eapply V293_rdy_raw_load;[ |reflexivity|exact Updated].
   apply in_or_app;right;left;reflexivity. }
 assert(Second:load(Tcom_ptr 410)Bad(82%positive,76)=Some(Vptr(82%positive,Int.repr 112))).
 { change(load(Tcom_ptr 410)(getmem(IPState Bad))(82%positive,76)=Some(Vptr(82%positive,Int.repr 112))).
   eapply V293_rdy_raw_load;[ |reflexivity|exact Updated].
   apply in_or_app;right;right. unfold IPAfterFirst. apply in_or_app;left. left;reflexivity. }
 exists Bad. split;[exact Store| ]. split.
 - intros b j Away. eapply V293_storebytes_outside;[exact Store|exact Away].
 - split;[exact NextNull| ]. split;[exact Second| ].
   split;[cbn [IPWalk];rewrite Int.unsigned_zero,Z.add_0_l;cbv delta [block] in *;rewrite First;reflexivity| ].
   split;cbn [IPWalk];rewrite Int.unsigned_zero,Z.add_0_l;cbv delta [block] in *;rewrite NextNull;cbn [IPWalk];congruence.
Qed.
Print Assumptions IPActualCallFinitePool.
Print Assumptions IPStableInterfaceChecked.
Print Assumptions IPActualThirteenReachable.
Print Assumptions IPFirstNextNullAblation.
