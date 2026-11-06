(* Constructive finite old/Vundef byte range, with same-block guards. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSMemClr.
Require Import CertiOS.certiucos.v293.proofs.V293MemClr.
Require Import CertiOS.certiucos.v293.proofs.V293NullBytes.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.certiucos.v293.proofs.V293MemClrCall.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope Z_scope.
Definition CallCaller : env := set (set emp 21%Z (71%positive,Tptr Tint8)) 22%Z (73%positive,Tint16).
Definition CallLE := V293_clr_locals 11%Z 12%Z 81%positive 83%positive.
Definition CallState le M := V293_wstate emp le M.
Definition CallBytes a tp v := V293_encoded_memory (fst a) (snd a) true (encode_val tp v).
Fixpoint CallMem (cells : list V293_record_cell) : mem :=
  match cells with
  | [] => CallBytes (99%positive,0) Tint32 (Vint32 (Int.repr 123))
  | (a,tp,v)::tail => merge (CallBytes a tp v) (CallMem tail)
  end.
Definition CallOld : list val := [Vint32 (Int.repr 255);Vundef;Vint32 (Int.repr 7);Vint32 (Int.repr 1)].
Definition CallGuards : list V293_record_cell :=
  [((82%positive,4),Tint8,Vint32 (Int.repr 17));((82%positive,9),Tint8,Vint32 (Int.repr 29));
   ((71%positive,0),Tptr Tint8,Vptr (82%positive,Int.repr 5));((73%positive,0),Tint16,Vint32 (Int.repr 4))].
Definition CallFrame := V293_rdy_raw_cells CallGuards
  (Amapsto (99%positive,0) Tint32 true (Vint32 (Int.repr 123))).
Definition CallInitial := V293_clr_bytes 82%positive 5 CallOld.
Definition CallM := CallMem (CallInitial++CallGuards).
Ltac CallOutside :=
  unfold CallBytes;cbn [fst snd];repeat rewrite map_merge_semp by reflexivity;
  repeat rewrite V293_encoded_memory_outside by
    (first [left;congruence | right;cbn;lia]);reflexivity.
Ltac CallUnique b :=
  apply map_join_merge;apply map_disjoint;intros [other off];
  destruct (Pos.eq_dec other b);[subst other;right;left;CallOutside | left;apply V293_encoded_memory_outside;left;assumption].
Ltac CallByte b x :=
  apply map_join_merge;apply map_disjoint;intros [other off];
  destruct (Pos.eq_dec other b) as [E | E];
  [subst other;destruct (Z.eq_dec off x) as [F | F];
    [subst off;right;left;CallOutside |
     left;apply V293_encoded_memory_outside;right;cbn;lia] |
   left;apply V293_encoded_memory_outside;left;exact E].
Theorem CallLiteralEntry : forall le, CallState le CallM |= V293_rdy_raw_cells CallInitial CallFrame.
Proof.
  intro le. unfold CallState,CallM,CallInitial,CallOld,CallGuards,CallFrame.
  cbn [V293_clr_bytes V293_rdy_raw_cells CallMem app length].
  eapply V293_wstate_star with (m1:=CallBytes (82%positive,5) Tint8 (Vint32 (Int.repr 255)));
    [CallByte 82%positive 5 | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
  eapply V293_wstate_star with (m1:=CallBytes (82%positive,6) Tint8 (Vundef));
    [CallByte 82%positive 6 | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
  eapply V293_wstate_star with (m1:=CallBytes (82%positive,7) Tint8 (Vint32 (Int.repr 7)));
    [CallByte 82%positive 7 | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
  eapply V293_wstate_star with (m1:=CallBytes (82%positive,8) Tint8 (Vint32 (Int.repr 1)));
    [CallByte 82%positive 8 | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
  eapply V293_wstate_star with (m1:=CallBytes (82%positive,4) Tint8 (Vint32 (Int.repr 17)));
    [CallByte 82%positive 4 | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
  eapply V293_wstate_star with (m1:=CallBytes (82%positive,9) Tint8 (Vint32 (Int.repr 29)));
    [CallUnique 82%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
  eapply V293_wstate_star with (m1:=CallBytes (71%positive,0) (Tptr Tint8) (Vptr (82%positive,Int.repr 5)));
    [CallUnique 71%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
  eapply V293_wstate_star with (m1:=CallBytes (73%positive,0) Tint16 (Vint32 (Int.repr 4)));
    [CallUnique 73%positive | split;[apply V293_encoded_memory_mapsto | reflexivity] | ].
  split;[apply V293_encoded_memory_mapsto | reflexivity].
Qed.
Theorem CallLiteralAST : V293_MemClr_function 11%Z 12%Z =
  (Tvoid,dcons 11%Z (Tptr Tint8) (dcons 12%Z Tint16 dnil),dnil,
    sseq (swhile (ebinop olt (econst32 Int.zero) (ecast (evar 12%Z) Tint32))
      (sseq (sassign (ederef (evar 11%Z)) (ecast (econst32 Int.zero) Tint8))
        (sseq (sassign (evar 11%Z) (ebinop oplus (evar 11%Z) (econst32 Int.one)))
          (sassign (evar 12%Z) (ecast
            (ebinop ominus (ecast (evar 12%Z) Tint32) (econst32 Int.one)) Tint16))))) sret).
Proof. reflexivity. Qed.

Theorem CallFreshParameters : fresh CallM 81%positive /\ fresh CallM 83%positive.
Proof.
  split;intros a i E [v Read];subst a.
  - assert (Absent : get CallM (81%positive,i)=None) by
      (unfold CallM,CallInitial,CallOld,CallGuards;cbn [V293_clr_bytes CallMem app];CallOutside).
    assert (Bad : None=Some v) by (etransitivity;[symmetry;exact Absent | exact Read]). discriminate.
  - assert (Absent : get CallM (83%positive,i)=None) by
      (unfold CallM,CallInitial,CallOld,CallGuards;cbn [V293_clr_bytes CallMem app];CallOutside).
    assert (Bad : None=Some v) by (etransitivity;[symmetry;exact Absent | exact Read]). discriminate.
Qed.

Theorem CallConcreteExecution : forall P ks,
  P 101%Z=Some (V293_MemClr_function 11%Z 12%Z) ->
  exists Mf,
    cstepstar P (curs (scall 101%Z [evar 21%Z;evar 22%Z]),(kenil,ks)) (emp,CallCaller,CallM)
      (curs (sskip None),(kenil,ks)) (emp,CallCaller,Mf) /\
    load (Tptr Tint8) Mf (82%positive,5)=Some Vnull /\
    load (Tptr Tint8) Mf (71%positive,0)=Some (Vptr (82%positive,Int.repr 5)) /\
    load Tint16 Mf (73%positive,0)=Some (Vint32 (Int.repr 4)) /\
    load Tint8 Mf (82%positive,4)=Some (Vint32 (Int.repr 17)) /\
    load Tint8 Mf (82%positive,9)=Some (Vint32 (Int.repr 29)) /\
    load Tint32 Mf (99%positive,0)=Some (Vint32 (Int.repr 123)) /\
    (forall k, (k<4)%nat -> get Mf (81%positive,Z.of_nat k)=None) /\
    (forall k, (k<2)%nat -> get Mf (83%positive,Z.of_nat k)=None).
Proof.
  intros P ks Program.
  pose proof (CallLiteralEntry CallCaller) as Initial.
  assert (CallerPtr : load (Tptr Tint8) CallM (71%positive,0)=Some (Vptr (82%positive,Int.repr 5))).
  { eapply (V293_rdy_raw_load (CallInitial++CallGuards)
      (Amapsto (99%positive,0) Tint32 true (Vint32 (Int.repr 123))) _ _ _ (CallState CallCaller CallM));
      [unfold CallInitial,CallOld,CallGuards;cbn;auto 12 | reflexivity | exact Initial]. }
  assert (CallerSize : load Tint16 CallM (73%positive,0)=Some (Vint32 (Int.repr 4))).
  { eapply (V293_rdy_raw_load (CallInitial++CallGuards)
      (Amapsto (99%positive,0) Tint32 true (Vint32 (Int.repr 123))) _ _ _ (CallState CallCaller CallM));
      [unfold CallInitial,CallOld,CallGuards;cbn;auto 12 | reflexivity | exact Initial]. }
  destruct CallFreshParameters as [FreshPtr FreshSize].
  destruct (V293_OS_MemClr_call_return CallOld P ks emp CallCaller CallM (fun _=>false)
    (false,nil,nil) emp (spec_done None) CallFrame 101%Z 11%Z 12%Z 81%positive 83%positive
    82%positive 5 (evar 21%Z) (evar 22%Z) Program ltac:(discriminate) ltac:(discriminate)
    FreshSize FreshPtr
    ltac:(vm_compute;reflexivity) ltac:(cbn [evalval get_lenv get_genv get_mem];
      change (load (Tptr Tint8) CallM (71%positive,0)=Some (Vptr (82%positive,Int.repr 5)));exact CallerPtr)
    ltac:(vm_compute;reflexivity) ltac:(cbn [evalval get_lenv get_genv get_mem];
      change (load Tint16 CallM (73%positive,0)=Some (Vint32 (Int.repr 4)));exact CallerSize)
    ltac:(cbn [CallOld length];lia) ltac:(lia) ltac:(change (5+4<=4294967295);lia)
    (CallLiteralEntry CallLE)) as (Ms&Mf&Exec&Owned&Preserve&PtrGone&SizeGone).
  assert (Typed : CallState CallLE Ms |= V293_rdy_raw_cells
    (V293_clr_params 81%positive 83%positive 82%positive 9 0 ++
      ((82%positive,5),Tptr Tint8,Vnull)::CallGuards)
    (Amapsto (99%positive,0) Tint32 true (Vint32 (Int.repr 123)))).
  { change (CallState CallLE Ms |= V293_rdy_raw_cells
      (V293_clr_params 81%positive 83%positive 82%positive 9 0 ++
       V293_clr_bytes 82%positive 5 (repeat (Vint32 Int.zero) 4)) CallFrame) in Owned.
    rewrite V293_raw_cells_append in Owned. unfold V293_clr_params in Owned.
    cbn [V293_rdy_raw_cells] in Owned.
    eapply astar_mono;[intros st H;exact H | | exact Owned].
    intros st H. eapply astar_mono;[intros st' H';exact H' | | exact H].
    apply V293_zero4_null_owned. }
  exists Mf. split;[exact Exec | ].
  assert (Loads : forall a tp v,
    In (a,tp,v) (((82%positive,5),Tptr Tint8,Vnull)::CallGuards) ->
    rule_type_val_match tp v=true -> load tp Mf a=Some v).
  { intros [b i] tp v Member Valid.
    assert (Away : b<>81%positive /\ b<>83%positive).
    { unfold CallGuards in Member. cbn in Member.
      destruct Member as [E | [E | [E | [E | [E | Bad]]]]];
        try contradiction;inversion E;subst;split;discriminate. }
    destruct Away as [B1 B2].
    etransitivity;[apply V293_load_block_frame;intro j;apply Preserve;assumption | ].
    eapply (V293_rdy_raw_load
      (V293_clr_params 81%positive 83%positive 82%positive 9 0 ++
        ((82%positive,5),Tptr Tint8,Vnull)::CallGuards)
      (Amapsto (99%positive,0) Tint32 true (Vint32 (Int.repr 123))) _ _ _ (CallState CallLE Ms));
      [apply in_or_app;right;exact Member | exact Valid | exact Typed]. }
  split;[apply Loads;[left;reflexivity | reflexivity] | ].
  split;[apply Loads;[right;right;right;left;reflexivity | reflexivity] | ].
  split;[apply Loads;[right;right;right;right;left;reflexivity | reflexivity] | ].
  split;[apply Loads;[right;left;reflexivity | reflexivity] | ].
  split;[apply Loads;[right;right;left;reflexivity | reflexivity] | ].
  split.
  - etransitivity;[apply V293_load_block_frame;intro j;apply Preserve;discriminate | ].
    change (load Tint32 (getmem (CallState CallLE Ms)) (99%positive,0)=Some (Vint32 (Int.repr 123))).
    unfold V293_clr_params,CallGuards in Typed. cbn [app V293_rdy_raw_cells] in Typed.
    do 7 (eapply V293_star_load_r;[ | exact Typed];clear Typed;intros ? Typed).
    destruct Typed as [Point Empty]. eapply mapstoval_load;[reflexivity | exact Point].
  - split;[exact PtrGone | exact SizeGone].
Qed.
Print Assumptions CallLiteralEntry.
Print Assumptions CallLiteralAST.
Print Assumptions CallFreshParameters.
Print Assumptions CallConcreteExecution.

(* A total, concrete one-function program discharges the program premise;
   this is a satisfiable local call fixture, not the complete kernel program. *)
Definition CallProgram (f : fid) : option function :=
  if Z.eq_dec f 101%Z then Some (V293_MemClr_function 11%Z 12%Z) else None.
Theorem CallProgramLookup : CallProgram 101%Z=Some (V293_MemClr_function 11%Z 12%Z).
Proof. reflexivity. Qed.
Theorem CallConcreteInstance : forall ks,
  exists Mf,
    cstepstar CallProgram (curs (scall 101%Z [evar 21%Z;evar 22%Z]),(kenil,ks))
      (emp,CallCaller,CallM) (curs (sskip None),(kenil,ks)) (emp,CallCaller,Mf) /\
    load (Tptr Tint8) Mf (82%positive,5)=Some Vnull /\
    (forall k, (k<4)%nat -> get Mf (81%positive,Z.of_nat k)=None) /\
    (forall k, (k<2)%nat -> get Mf (83%positive,Z.of_nat k)=None).
Proof.
  intro ks. destruct (CallConcreteExecution CallProgram ks CallProgramLookup)
    as (Mf&Exec&Null&CallerPtr&CallerSize&LowGuard&HighGuard&Extra&PtrGone&SizeGone).
  exists Mf. split;[exact Exec | ]. split;[exact Null | ]. split;assumption.
Qed.
Print Assumptions CallProgramLookup.
Print Assumptions CallConcreteInstance.
