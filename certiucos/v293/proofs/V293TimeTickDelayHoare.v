(* Direct rules for the unchanged os_core.c:986-1002 delay/expiry AST.
   No execution/evaluator oracle is a premise of the public fragment theorem.
   This is not the hook, loop, ISR, or whole-function contract. *)
Require Import CertiOS.certiucos.v293.proofs.V293TCBFieldsHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLoop.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickExpiry.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.certiucos.v293.code.V293OSTimeTick.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickTraversal.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickCountdown.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.framework.proof.soundness.
Require CertiOS.framework.proof.simulation.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition V293_tick_delay_env (ptcb rows group : var) bc br bg (ge le : env) :=
 @get var (block*type) env EnvMap le ptcb=Some(bc,Tptr V293_tcb_type) /\
 @get var (block*type) env EnvMap le rows=None /\ @get var (block*type) env EnvMap ge rows=Some(br,Tarray Tint8 2) /\
 @get var (block*type) env EnvMap le group=None /\ @get var (block*type) env EnvMap ge group=Some(bg,Tint8).

Lemma V293_tick_raw_field_eval : forall cells R ptcb bc bt base field delta tp v s,
 (forall st, st |= R -> get (getlenv st) ptcb=Some(bc,Tptr V293_tcb_type)) ->
 In ((bc,0%Z),Tptr V293_tcb_type,Vptr(bt,Int.repr base)) cells ->
 In ((bt,(base+delta)%Z),tp,v) cells -> rule_type_val_match tp v=true ->
 (0<=base)%Z -> (0<=delta)%Z -> (base+delta<=Int.max_unsigned)%Z ->
 ftype field V293_tcb_fields=Some tp ->
 field_offset field V293_tcb_fields=Some(Int.repr delta) ->
 s |= V293_rdy_raw_cells cells R ->
 evaltype (V293_tick_field ptcb field) (getsmem s)=Some tp /\
 evalval (V293_tick_field ptcb field) (getsmem s)=Some v.
Proof.
 intros cells R ptcb bc bt base field delta tp v s Env Pointer Cell Valid Base Delta Limit Ft Fo Owned.
 destruct s as [[[[[[ge le] M] ir] aux] O] op].
 eapply V293_tick_field_eval with (bc:=bc) (bt:=bt) (base:=base) (delta:=delta);
  [ | |exact Ft|exact Fo|exact Base|exact Delta|exact Limit| ].
 - exact (V293_raw_cells_frame_env cells R (fun ge le => get le ptcb=Some(bc,Tptr V293_tcb_type)) Env (ge,le,M,ir,aux,O,op) Owned).
 - eapply (V293_rdy_raw_load cells R _ _ _ (ge,le,M,ir,aux,O,op));[exact Pointer|reflexivity|exact Owned].
 - eapply (V293_rdy_raw_load cells R _ _ _ (ge,le,M,ir,aux,O,op));eassumption.
Qed.

Lemma V293_tick_known_if_hoare : forall Spec sd li I r ri tid p q e yes no (flag : bool),
 (p ==> Rv e @ Tint32 == Vint32 (if flag then Int.one else Int.zero)) ->
 InfRules Spec sd li I r ri p (if flag then yes else no) q tid ->
 InfRules Spec sd li I r ri p (sif e yes no) q tid.
Proof.
 intros Spec sd li I r ri tid p q e yes no flag Eval Branch.
 eapply if_rule with (tp:=Tint32).
 - intros s HS. eexists;apply Eval;exact HS.
 - destruct flag.
   + eapply conseq_rule;[intros s [HS _];exact HS|intros s HS;exact HS|exact Branch].
   + eapply conseq_rule with (p:=Afalse);[ |intros s HS;exact HS|apply pfalse_rule].
     intros s [HS [v [V B]]]. destruct (Eval s HS) as [E _]. rewrite E in V. inversion V;subst v. discriminate B.
 - destruct flag.
   + eapply conseq_rule with (p:=Afalse);[ |intros s HS;exact HS|apply pfalse_rule].
     intros s [HS [v [V B]]]. destruct (Eval s HS) as [E _]. rewrite E in V. inversion V;subst v. discriminate B.
   + eapply conseq_rule;[intros s [HS _];exact HS|intros s HS;exact HS|exact Branch].
Qed.

Lemma V293_tick_known_ift_hoare : forall Spec sd li I r ri tid p q e body (flag : bool),
 (p ==> Rv e @ Tint32 == Vint32 (if flag then Int.one else Int.zero)) ->
 (if flag then InfRules Spec sd li I r ri p body q tid else p ==> q) ->
 InfRules Spec sd li I r ri p (sifthen e body) q tid.
Proof.
 intros Spec sd li I r ri tid p q e body flag Eval Branch.
 eapply ift_rule with (tp:=Tint32).
 - intros s HS. eexists;apply Eval;exact HS.
 - intros s [HS [v [V B]]]. destruct flag.
   + destruct (Eval s HS) as [E _]. rewrite E in V. inversion V;subst v. discriminate B.
   + apply Branch;exact HS.
 - destruct flag.
   + eapply conseq_rule;[intros s [HS _];exact HS|intros s HS;exact HS|exact Branch].
   + eapply conseq_rule with (p:=Afalse);[ |intros s HS;exact HS|apply pfalse_rule].
     intros s [HS [v [V B]]]. destruct (Eval s HS) as [E _]. rewrite E in V. inversion V;subst v. discriminate B.
Qed.

Lemma V293_tick_mask_guard_types : forall ge le M stat,
 evaltype stat (ge,le,M)=Some Tint8 ->
 evaltype (V293_tick_ne (ebinop obitand (ecast stat Tint32) (econst32 (Int.repr 55))) 0) (ge,le,M)=Some Tint32 /\
 evaltype (V293_tick_eq (ebinop obitand (ecast stat Tint32) (econst32 (Int.repr 8))) 0) (ge,le,M)=Some Tint32.
Proof.
 intros ge le M stat T. unfold V293_tick_ne,V293_tick_eq.
 cbn [evaltype]. rewrite T. split;reflexivity.
Qed.

(* The following local tactics only select existing cells/rules. They do not
   extend the language, operational semantics, or trusted rule constructors. *)
Local Ltac tick_load Owned n :=
 let Read := fresh "CellLoad" in
 lazymatch type of Owned with
 | ?st |= V293_rdy_raw_cells ?cells ?R =>
   let cell := eval cbn in (nth n cells ((1%positive,0%Z),Tint8,Vundef)) in
   lazymatch cell with (?a,?tp,?v) =>
    assert (Read : load tp (getmem st) a=Some v) by
     (eapply (V293_rdy_raw_load cells R a tp v st);
      [cbn [V293_tick_expiry_cells app In];tauto|first [reflexivity|apply V293_byte_type;lia]|exact Owned])
   end
 end.
Local Ltac tick_env Env Owned :=
 pose proof (V293_raw_cells_frame_env _ _ _ Env _ Owned) as Bindings;
 cbn [V293_tick_delay_env getgenv getlenv get_smem get_lenv get_genv] in Bindings;
 destruct Bindings as (Bind&Nr&Gr&Ng&Gg).
Local Ltac tick_field Env Base Owned localblock taskblock taskbase fld off typ value valid :=
 lazymatch type of Owned with ?state |= V293_rdy_raw_cells ?cs ?fr =>
 eapply V293_tick_raw_field_eval with (cells:=cs) (R:=fr) (s:=state) (bc:=localblock) (bt:=taskblock) (base:=taskbase) (field:=fld) (delta:=off) (v:=value) (tp:=typ);
 [intros st HS;exact (proj1 (Env st HS))|cbn [V293_tick_expiry_cells app In];tauto|cbn [V293_tick_expiry_cells app In];tauto|
  exact valid|exact Base|lia|lia|reflexivity|reflexivity|exact Owned]
 end.
Local Ltac tick_store HR n rt v :=
 lazymatch goal with
 | |- InfRules ?Spec ?sd ?li ?I ?r ?ri (<||?aop||> ** V293_rdy_raw_cells ?cells ?R) ?stmt ?q ?tid =>
   let before := eval cbn in (firstn n cells) in
   let cell := eval cbn in (nth n cells ((1%positive,0%Z),Tint8,Vundef)) in
   let after := eval cbn in (skipn (S n) cells) in
   lazymatch cell with (?a,?tp,?old) =>
    let updated := eval cbn [app] in (before++(a,tp,v)::after) in
    let one := ltac:(eapply (V293_raw_assign_hoare Spec sd li I r ri tid aop before a tp old after v _ _ rt R);
     [cbn [snd];apply Int.unsigned_repr;lia|apply eq_int;auto| |exact HR]) in
    lazymatch stmt with
    | sseq (sassign _ _) _ => eapply seq_rule with (p':=<||aop||> ** V293_rdy_raw_cells updated R);[one| ]
    | sassign _ _ => one
    end
   end
 end.

Lemma V293_tick_expiry_fragment_hoare : forall Spec sd li I r ri tid aop R
 ptcb rows group bc bt base delay next s pend y x bg g br row,
 (0<=base)%Z -> (base+54<=Int.max_unsigned)%Z ->
 s<256 -> pend<256 -> y<2 -> x<8 -> g<256 -> row<256 ->
 (forall st, st |= R -> V293_tick_delay_env ptcb rows group bc br bg (getgenv st) (getlenv st)) ->
 (R ==> CurLINV li tid) ->
 InfRules Spec sd li I r ri
 (<||aop||> ** V293_rdy_raw_cells
  (V293_tick_expiry_cells bc bt base (bt,Int.repr base) delay next s pend y x bg g br row) R)
 (V293_tick_expiry ptcb rows group)
 (<||aop||> ** V293_rdy_raw_cells
  (V293_tick_expiry_cells bc bt base (bt,Int.repr base) delay next
   (V293_tick_expired_stat s) (V293_tick_expired_pend s) y x bg
   (V293_tick_expired_group s g y) br (V293_tick_expired_row s row x)) R) tid.
Proof.
 intros Spec sd li I r ri tid aop R ptcb rows group bc bt base delay next s pend y x bg g br row
 Base Limit S Pend Y X G Row Env HR.
 destruct (V293_tick_status_arithmetic s S) as [A55 [A8 [Clear ClearBound]]].
 assert (ExpiredBound : V293_tick_expired_stat s<256).
 { unfold V293_tick_expired_stat;destruct (V293_tick_waiting s);assumption. }
 unfold V293_tick_expiry. cbn beta iota zeta.
 eapply seq_rule with (p':=<||aop||> ** V293_rdy_raw_cells
  (V293_tick_expiry_cells bc bt base (bt,Int.repr base) delay next
   (V293_tick_expired_stat s) (V293_tick_expired_pend s) y x bg g br row) R).
 - eapply V293_tick_known_if_hoare with (flag:=V293_tick_waiting s).
   + intros st HS. apply astar_l_aop'_elim in HS as [_ Owned].
     destruct st as [[[[[[ge le] M] ir] aux] O] op].
     assert (Stat : evaltype (V293_tick_field ptcb 14%Z) (ge,le,M)=Some Tint8 /\
       evalval (V293_tick_field ptcb 14%Z) (ge,le,M)=Some(V293_byteval s)).
     { tick_field Env Base Owned bc bt base 14%Z 48%Z Tint8 (V293_byteval s) (V293_byte_type s S). }
     destruct Stat as [St Sv]. cbn [sat getsmem get_smem]. split.
     * apply V293_tick_pending_test_eval;assumption.
     * split;[exact (proj1 (V293_tick_mask_guard_types ge le M _ St))|discriminate].
   + destruct (V293_tick_waiting s) eqn:Wait;
      unfold V293_tick_expired_stat,V293_tick_expired_pend;rewrite Wait;
      unfold V293_tick_expiry_cells;cbn beta iota zeta.
     * tick_store HR 3 Tint8 (V293_byteval (Nat.land s 200)).
       { intros st Owned. destruct st as [[[[[[ge le] M] ir] aux] O] op].
         tick_env Env Owned. tick_load Owned 0.
         destruct (V293_tcb_init_field_address ge le M ptcb bc bt base 14%Z 48%Z Tint8
          Bind CellLoad eq_refl eq_refl Base ltac:(lia) ltac:(lia)) as [Ty Addr].
         assert (Stat : evaltype (V293_tick_field ptcb 14%Z) (ge,le,M)=Some Tint8 /\
           evalval (V293_tick_field ptcb 14%Z) (ge,le,M)=Some(V293_byteval s)).
         { tick_field Env Base Owned bc bt base 14%Z 48%Z Tint8 (V293_byteval s) (V293_byte_type s S). }
         destruct Stat as [St Sv].
         destruct (V293_tick_clear_status_eval ge le M _ s S St Sv) as [Ct Cv].
         cbn [sat getsmem get_smem]. repeat split;try assumption;discriminate. }
       tick_store HR 4 Tint8 (V293_byteval 1).
       { intros st Owned. destruct st as [[[[[[ge le] M] ir] aux] O] op].
         tick_env Env Owned. tick_load Owned 0.
         destruct (V293_tcb_init_field_address ge le M ptcb bc bt base 15%Z 49%Z Tint8
          Bind CellLoad eq_refl eq_refl Base ltac:(lia) ltac:(lia)) as [Ty Addr].
         cbn [sat getsmem get_smem]. repeat split;try assumption;reflexivity || discriminate. }
     * tick_store HR 4 Tint8 (V293_byteval 0).
       { intros st Owned. destruct st as [[[[[[ge le] M] ir] aux] O] op].
         tick_env Env Owned. tick_load Owned 0.
         destruct (V293_tcb_init_field_address ge le M ptcb bc bt base 15%Z 49%Z Tint8
          Bind CellLoad eq_refl eq_refl Base ltac:(lia) ltac:(lia)) as [Ty Addr].
         cbn [sat getsmem get_smem]. repeat split;try assumption;reflexivity || discriminate. }
 - eapply V293_tick_known_ift_hoare with (flag:=V293_tick_wakes s).
   + intros st HS. apply astar_l_aop'_elim in HS as [_ Owned].
     destruct st as [[[[[[ge le] M] ir] aux] O] op].
     assert (Stat : evaltype (V293_tick_field ptcb 14%Z) (ge,le,M)=Some Tint8 /\
       evalval (V293_tick_field ptcb 14%Z) (ge,le,M)=Some(V293_byteval (V293_tick_expired_stat s))).
     { tick_field Env Base Owned bc bt base 14%Z 48%Z Tint8 (V293_byteval (V293_tick_expired_stat s))
       (V293_byte_type _ ExpiredBound). }
     destruct Stat as [St Sv]. cbn [sat getsmem get_smem]. split.
     * apply V293_tick_suspend_test_eval;assumption.
     * split;[exact (proj2 (V293_tick_mask_guard_types ge le M _ St))|discriminate].
   + destruct (V293_tick_wakes s) eqn:Wake;
      unfold V293_tick_expired_group,V293_tick_expired_row;rewrite Wake.
     * unfold V293_tick_expiry_cells;cbn beta iota zeta.
       tick_store HR 8 Tint8 (V293_byteval (Nat.setbit g y)).
       { intros st Owned. destruct st as [[[[[[ge le] M] ir] aux] O] op].
         tick_env Env Owned. tick_load Owned 8.
         assert (By : evaltype (V293_tick_field ptcb 20%Z) (ge,le,M)=Some Tint8 /\
           evalval (V293_tick_field ptcb 20%Z) (ge,le,M)=Some(V293_byteval (2^y))).
         { tick_field Env Base Owned bc bt base 20%Z 54%Z Tint8 (V293_byteval (2^y))
           (V293_byte_type (2^y) ltac:(pose proof (V293_mask_byte_value y ltac:(lia)) as [B _];exact B)). }
         destruct By as [Byt Byv].
         destruct (V293_mask_byte_value y ltac:(lia)) as [_ ByEq]. rewrite ByEq in Byv.
         assert (Gt : evaltype (evar group) (ge,le,M)=Some Tint8).
         { cbn [evaltype get_lenv get_genv]. rewrite Ng. rewrite Gg. reflexivity. }
         assert (Ga : evaladdr (evar group) (ge,le,M)=Some(Vptr(bg,Int.repr 0))).
         { cbn [evaladdr get_lenv get_genv];rewrite Ng,Gg;reflexivity. }
         assert (Gv : evalval (evar group) (ge,le,M)=Some(V293_byteval g)).
         { cbn [evalval evaltype get_lenv get_genv get_mem];rewrite Ng,Gg;exact CellLoad. }
         destruct (V293_task_prio_byte_expr_eval ge le M _ _ g y G ltac:(lia) Gt Byt Gv Byv)
           as [_ [Gst [_ Gsv]]].
         cbn [sat getsmem get_smem]. repeat split;try assumption;discriminate. }
       tick_store HR 9 Tint8 (V293_byteval (Nat.setbit row x)).
       { intros st Owned. destruct st as [[[[[[ge le] M] ir] aux] O] op].
         tick_env Env Owned. tick_load Owned 9.
         assert (Yi : evaltype (V293_tick_field ptcb 18%Z) (ge,le,M)=Some Tint8 /\
           evalval (V293_tick_field ptcb 18%Z) (ge,le,M)=Some(V293_byteval y)).
         { tick_field Env Base Owned bc bt base 18%Z 52%Z Tint8 (V293_byteval y) (V293_byte_type y ltac:(lia)). }
         destruct Yi as [Yt Yv].
         assert (Bx : evaltype (V293_tick_field ptcb 19%Z) (ge,le,M)=Some Tint8 /\
           evalval (V293_tick_field ptcb 19%Z) (ge,le,M)=Some(V293_byteval (2^x))).
         { tick_field Env Base Owned bc bt base 19%Z 53%Z Tint8 (V293_byteval (2^x))
            (V293_byte_type (2^x) ltac:(pose proof (V293_mask_byte_value x X) as [B _];exact B)). }
         destruct Bx as [Bxt Bxv].
         destruct (V293_mask_byte_value x X) as [_ BxEq]. rewrite BxEq in Bxv.
         assert (At : evaltype (evar rows) (ge,le,M)=Some(Tarray Tint8 2)).
         { cbn [evaltype get_lenv get_genv];rewrite Nr,Gr;reflexivity. }
         assert (Av : evalval (evar rows) (ge,le,M)=Some(Vptr(br,Int.repr 0))).
         { cbn [evalval evaltype get_lenv get_genv];rewrite Nr,Gr;reflexivity. }
         destruct (V293_byte_array_offset_eval ge le M _ _ br 0%Z y _ At Av Yt Yv
           ltac:(lia) ltac:(change (0+Z.of_nat y<=4294967295)%Z;lia) Y CellLoad)
           as [Rt [Ra RowValue]].
         destruct (V293_task_prio_byte_expr_eval ge le M _ _ row x Row X Rt Bxt RowValue Bxv)
           as [_ [Rst [_ Rsv]]].
         cbn [sat getsmem get_smem]. repeat split;try assumption;discriminate. }
     * intros st HS;exact HS.
Qed.

Lemma V293_tick_delay_test_eval : forall ge le M e n,
 evaltype e (ge,le,M)=Some Tint32 -> evalval e (ge,le,M)=Some(Vint32 n) ->
 evaltype (V293_tick_eq e 0) (ge,le,M)=Some Tint32 /\
 evalval (V293_tick_eq e 0) (ge,le,M)=Some(Vint32 (if Int.eq n Int.zero then Int.one else Int.zero)) /\
 evaltype (V293_tick_ne e 0) (ge,le,M)=Some Tint32 /\
 evalval (V293_tick_ne e 0) (ge,le,M)=Some(Vint32 (if Int.eq n Int.zero then Int.zero else Int.one)).
Proof.
 intros ge le M e n T V. unfold V293_tick_ne,V293_tick_eq.
 cbn [evalval evaltype]. rewrite T,V. split;[reflexivity| ]. split.
 - change ((if Int.eq n Int.zero then Some(Vint32 Int.one) else Some(Vint32 Int.zero)) =
     Some(Vint32 (if Int.eq n Int.zero then Int.one else Int.zero))).
   destruct (Int.eq n Int.zero);reflexivity.
 - split;[reflexivity| ].
   change ((match (if Int.eq n Int.zero then Some(Vint32 Int.one) else Some(Vint32 Int.zero))
     with Some v => notint v | None => None end)=
     Some(Vint32 (if Int.eq n Int.zero then Int.zero else Int.one))).
   destruct (Int.eq n Int.zero);reflexivity.
Qed.

Lemma V293_tick_delay_sub_eval : forall ge le M e d,
 (0<=d<=Int.max_unsigned)%Z ->
 evaltype e (ge,le,M)=Some Tint32 -> evalval e (ge,le,M)=Some(Vint32 (Int.repr d)) ->
 evaltype (ebinop ominus e (econst32 Int.one)) (ge,le,M)=Some Tint32 /\
 evalval (ebinop ominus e (econst32 Int.one)) (ge,le,M)=Some(Vint32 (Int.repr (d-1))).
Proof.
 intros ge le M e d Bound T V. cbn [evaltype evalval]. rewrite T,V.
 split;[reflexivity| ]. change (Some(Vint32 (Int.sub (Int.repr d) Int.one))=Some(Vint32 (Int.repr (d-1)))).
 unfold Int.sub. rewrite Int.unsigned_repr by lia.
 rewrite Int.unsigned_one. reflexivity.
Qed.

(* Stable entry for every unsigned delay and every physical status byte.
   The environment and CurLINV are explicit resources of the unchanged frame;
   neither execution nor expression evaluation is assumed by this theorem. *)
Theorem V293_tick_delay_fragment_hoare : forall Spec sd li I r ri tid aop R
 ptcb rows group bc bt base d next s pend y x bg g br row,
 (0<=base)%Z -> (base+54<=Int.max_unsigned)%Z -> (0<=d<=Int.max_unsigned)%Z ->
 s<256 -> pend<256 -> y<2 -> x<8 -> g<256 -> row<256 ->
 (forall st, st |= R -> V293_tick_delay_env ptcb rows group bc br bg (getgenv st) (getlenv st)) ->
 (R ==> CurLINV li tid) ->
 InfRules Spec sd li I r ri
 (<||aop||> ** V293_rdy_raw_cells
  (V293_tick_expiry_cells bc bt base (bt,Int.repr base) (Int.repr d) next s pend y x bg g br row) R)
 (V293_tick_delay ptcb rows group)
 (<||aop||> ** V293_rdy_raw_cells
  (V293_tick_expiry_cells bc bt base (bt,Int.repr base) (Int.repr (V293_tick_after_delay d)) next
   (V293_tick_after_stat d s) (V293_tick_after_pend d pend s) y x bg
   (V293_tick_after_group d s g y) br (V293_tick_after_row d s row x)) R) tid.
Proof.
 intros Spec sd li I r ri tid aop R ptcb rows group bc bt base d next s pend y x bg g br row
 Base Limit D S Pend Y X G Row Env HR.
 assert (NE : forall z, (0<z<=Int.max_unsigned)%Z -> Int.eq (Int.repr z) Int.zero=false).
 { intros z B. apply Int.eq_false. intro E. apply (f_equal Int.unsigned) in E.
   rewrite Int.unsigned_repr,Int.unsigned_zero in E by lia. lia. }
 unfold V293_tick_delay.
 eapply V293_tick_known_ift_hoare with (flag:=negb (Z.eqb d 0)).
 - intros st HS. apply astar_l_aop'_elim in HS as [_ Owned].
   destruct st as [[[[[[ge le] M] ir] aux] O] op].
   assert (Delay : evaltype (V293_tick_field ptcb 13%Z) (ge,le,M)=Some Tint32 /\
     evalval (V293_tick_field ptcb 13%Z) (ge,le,M)=Some(Vint32 (Int.repr d))).
   { tick_field Env Base Owned bc bt base 13%Z 44%Z Tint32 (Vint32 (Int.repr d)) (eq_refl true). }
   destruct Delay as [Dt Dv].
   destruct (V293_tick_delay_test_eval ge le M _ _ Dt Dv) as [_ [_ [Nt Nv]]].
   cbn [sat getsmem get_smem]. split;[ | split;[exact Nt|discriminate]].
   destruct (Z.eqb d 0) eqn:E0.
   + apply Z.eqb_eq in E0;subst d;exact Nv.
   + rewrite NE in Nv by (apply Z.eqb_neq in E0;lia). exact Nv.
 - destruct (Z.eqb d 0) eqn:E0;cbn [negb].
   + apply Z.eqb_eq in E0;subst d. intros st HS;exact HS.
   + assert (Positive : (0<d)%Z) by (apply Z.eqb_neq in E0;lia).
     unfold V293_tick_after_delay;rewrite E0.
     unfold V293_tick_expiry_cells;cbn beta iota zeta.
     tick_store HR 1 Tint32 (Vint32 (Int.repr (d-1))).
     { intros st Owned. destruct st as [[[[[[ge le] M] ir] aux] O] op].
       tick_env Env Owned. tick_load Owned 0.
       destruct (V293_tcb_init_field_address ge le M ptcb bc bt base 13%Z 44%Z Tint32
         Bind CellLoad eq_refl eq_refl Base ltac:(lia) ltac:(lia)) as [Ty Addr].
       assert (Delay : evaltype (V293_tick_field ptcb 13%Z) (ge,le,M)=Some Tint32 /\
         evalval (V293_tick_field ptcb 13%Z) (ge,le,M)=Some(Vint32 (Int.repr d))).
       { tick_field Env Base Owned bc bt base 13%Z 44%Z Tint32 (Vint32 (Int.repr d)) (eq_refl true). }
       destruct Delay as [Dt Dv].
       destruct (V293_tick_delay_sub_eval ge le M _ d D Dt Dv) as [Subt Subv].
       cbn [sat getsmem get_smem]. repeat split;try assumption;discriminate. }
     eapply V293_tick_known_ift_hoare with (flag:=Z.eqb d 1).
     * intros st HS. apply astar_l_aop'_elim in HS as [_ Owned].
       destruct st as [[[[[[ge le] M] ir] aux] O] op].
       assert (Delay : evaltype (V293_tick_field ptcb 13%Z) (ge,le,M)=Some Tint32 /\
         evalval (V293_tick_field ptcb 13%Z) (ge,le,M)=Some(Vint32 (Int.repr (d-1)))).
       { tick_field Env Base Owned bc bt base 13%Z 44%Z Tint32 (Vint32 (Int.repr (d-1))) (eq_refl true). }
       destruct Delay as [Dt Dv].
       destruct (V293_tick_delay_test_eval ge le M _ _ Dt Dv) as [Et [Ev _]].
       cbn [sat getsmem get_smem]. split;[ | split;[exact Et|discriminate]].
       destruct (Z.eqb d 1) eqn:E1.
       -- apply Z.eqb_eq in E1;subst d;exact Ev.
       -- rewrite NE in Ev by (apply Z.eqb_neq in E1;lia). exact Ev.
     * unfold V293_tick_after_stat,V293_tick_after_pend,V293_tick_after_group,V293_tick_after_row.
       destruct (Z.eqb d 1);cbn beta iota zeta.
       -- apply V293_tick_expiry_fragment_hoare;assumption.
       -- intros st HS;exact HS.
Qed.

Theorem V293_tick_delay_fragment_semantics : forall Spec sd li I r ri tid aop R
 ptcb rows group bc bt base d next s pend y x bg g br row,
 (0<=base)%Z -> (base+54<=Int.max_unsigned)%Z -> (0<=d<=Int.max_unsigned)%Z ->
 s<256 -> pend<256 -> y<2 -> x<8 -> g<256 -> row<256 ->
 (forall st, st |= R -> V293_tick_delay_env ptcb rows group bc br bg (getgenv st) (getlenv st)) ->
 (R ==> CurLINV li tid) ->
 simulation.RuleSem Spec sd li I r ri
 (<||aop||> ** V293_rdy_raw_cells
  (V293_tick_expiry_cells bc bt base (bt,Int.repr base) (Int.repr d) next s pend y x bg g br row) R)
 (V293_tick_delay ptcb rows group)
 (<||aop||> ** V293_rdy_raw_cells
  (V293_tick_expiry_cells bc bt base (bt,Int.repr base) (Int.repr (V293_tick_after_delay d)) next
   (V293_tick_after_stat d s) (V293_tick_after_pend d pend s) y x bg
   (V293_tick_after_group d s g y) br (V293_tick_after_row d s row x)) R) tid.
Proof. intros. apply RuleSound. apply V293_tick_delay_fragment_hoare;assumption. Qed.

Print Assumptions V293_tick_delay_fragment_semantics.
Print Assumptions V293_tick_expiry_fragment_hoare.
Print Assumptions V293_tick_delay_fragment_hoare.
