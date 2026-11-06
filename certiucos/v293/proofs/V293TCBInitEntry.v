(* Full normalized function entry to the first successful-branch hook.
   No hook body is invented; missing hook means no local step at that call. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitFunction.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitPrefix.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBCall.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBClear.
Require Import CertiOS.certiucos.v293.proofs.V293NullBytes.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBList.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope Z_scope.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFunction.
Require Import CertiOS.certiucos.v293.proofs.V293InitChain.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.

(* Evaluated-argument entry through allocation/local initialization. No branch
   outcome or intermediate memory is supplied by the caller. *)
Lemma V293_tcb_call_prologue : forall P ks ge caller M ir aux O op enabled si ci
 f hook_init hook_create b1 b2 b3 b4 b5 b6 b7 b8 b9 v1 v2 v3 v4 v5 v6 v7 frame,
 P f=Some (V293_TCBInit_function hook_init hook_create) ->
 NoDup (V293_tcb_function_blocks b1 b2 b3 b4 b5 b6 b7 b8 b9) ->
 (forall b, In b (V293_tcb_function_blocks b1 b2 b3 b4 b5 b6 b7 b8 b9) -> fresh M b) ->
 V293_tcb_function_values_valid v1 v2 v3 v4 v5 v6 v7 ->
 (ge,caller,M,ir,aux,O,op) |= V293_rdy_raw_cells frame Atrue ->
 exists Mi,
 V293_local_steps P
  (curs(sfexec f [v7;v6;v5;v4;v3;v2;v1] V293_TCBInit_argument_types),(kenil,ks))
  ((ge,caller,M),ir,(enabled,si,ci))
  (curs(V293_TCBInit_prefix 91%Z 108%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z
    (V293_TCBInit_success_suffix hook_init hook_create)),
    (kenil,kcall f (V293_TCBInit_function_body hook_init hook_create) caller ks))
  ((ge,V293_tcb_function_env b1 b2 b3 b4 b5 b6 b7 b8 b9,Mi),ir,(enabled,si,ci)) /\
 (ge,V293_tcb_function_env b1 b2 b3 b4 b5 b6 b7 b8 b9,Mi,ir,aux,O,op) |=
 V293_rdy_raw_cells (V293_tcb_function_cells b1 b2 b3 b4 b5 b6 b7 b8 b9
 v1 v2 v3 v4 v5 v6 v7 Vundef (Vint32 Int.zero)++frame) Atrue.
Proof.
 intros P ks ge caller M ir aux O op enabled si ci f hook_init hook_create
 b1 b2 b3 b4 b5 b6 b7 b8 b9 v1 v2 v3 v4 v5 v6 v7 frame Program ND Fresh Valid Owned.
 set (le:=V293_tcb_function_env b1 b2 b3 b4 b5 b6 b7 b8 b9).
 pose proof ND as ND0. unfold V293_tcb_function_blocks in ND0.
 inversion ND0 as [ | a1 tail1 N1 Rest1];subst;clear ND0.
 inversion Rest1 as [ | a2 tail2 N2 Rest2];subst;clear Rest1.
 inversion Rest2 as [ | a3 tail3 N3 Rest3];subst;clear Rest2.
 inversion Rest3 as [ | a4 tail4 N4 Rest4];subst;clear Rest3.
 inversion Rest4 as [ | a5 tail5 N5 Rest5];subst;clear Rest4.
 inversion Rest5 as [ | a6 tail6 N6 Rest6];subst;clear Rest5.
 inversion Rest6 as [ | a7 tail7 N7 Rest7];subst;clear Rest6.
 inversion Rest7 as [ | a8 tail8 N8 Rest8];subst;clear Rest7.
 inversion Rest8 as [ | a9 tail9 N9 Rest9];subst;clear Rest8.
 cbn in N1,N2,N3,N4,N5,N6,N7,N8,N9.
 assert (D1_2 : b1<>b2) by (clear -N1;intro E;subst;tauto).
 assert (D1_3 : b1<>b3) by (clear -N1;intro E;subst;tauto).
 assert (D1_4 : b1<>b4) by (clear -N1;intro E;subst;tauto).
 assert (D1_5 : b1<>b5) by (clear -N1;intro E;subst;tauto).
 assert (D1_6 : b1<>b6) by (clear -N1;intro E;subst;tauto).
 assert (D1_7 : b1<>b7) by (clear -N1;intro E;subst;tauto).
 assert (D1_8 : b1<>b8) by (clear -N1;intro E;subst;tauto).
 assert (D1_9 : b1<>b9) by (clear -N1;intro E;subst;tauto).
 assert (D2_3 : b2<>b3) by (clear -N2;intro E;subst;tauto).
 assert (D2_4 : b2<>b4) by (clear -N2;intro E;subst;tauto).
 assert (D2_5 : b2<>b5) by (clear -N2;intro E;subst;tauto).
 assert (D2_6 : b2<>b6) by (clear -N2;intro E;subst;tauto).
 assert (D2_7 : b2<>b7) by (clear -N2;intro E;subst;tauto).
 assert (D2_8 : b2<>b8) by (clear -N2;intro E;subst;tauto).
 assert (D2_9 : b2<>b9) by (clear -N2;intro E;subst;tauto).
 assert (D3_4 : b3<>b4) by (clear -N3;intro E;subst;tauto).
 assert (D3_5 : b3<>b5) by (clear -N3;intro E;subst;tauto).
 assert (D3_6 : b3<>b6) by (clear -N3;intro E;subst;tauto).
 assert (D3_7 : b3<>b7) by (clear -N3;intro E;subst;tauto).
 assert (D3_8 : b3<>b8) by (clear -N3;intro E;subst;tauto).
 assert (D3_9 : b3<>b9) by (clear -N3;intro E;subst;tauto).
 assert (D4_5 : b4<>b5) by (clear -N4;intro E;subst;tauto).
 assert (D4_6 : b4<>b6) by (clear -N4;intro E;subst;tauto).
 assert (D4_7 : b4<>b7) by (clear -N4;intro E;subst;tauto).
 assert (D4_8 : b4<>b8) by (clear -N4;intro E;subst;tauto).
 assert (D4_9 : b4<>b9) by (clear -N4;intro E;subst;tauto).
 assert (D5_6 : b5<>b6) by (clear -N5;intro E;subst;tauto).
 assert (D5_7 : b5<>b7) by (clear -N5;intro E;subst;tauto).
 assert (D5_8 : b5<>b8) by (clear -N5;intro E;subst;tauto).
 assert (D5_9 : b5<>b9) by (clear -N5;intro E;subst;tauto).
 assert (D6_7 : b6<>b7) by (clear -N6;intro E;subst;tauto).
 assert (D6_8 : b6<>b8) by (clear -N6;intro E;subst;tauto).
 assert (D6_9 : b6<>b9) by (clear -N6;intro E;subst;tauto).
 assert (D7_8 : b7<>b8) by (clear -N7;intro E;subst;tauto).
 assert (D7_9 : b7<>b9) by (clear -N7;intro E;subst;tauto).
 assert (D8_9 : b8<>b9) by (clear -N8;intro E;subst;tauto).
 destruct Valid as (V1 & V2 & V3 & V4 & V5 & V6 & V7).
 assert (H0 : (ge,le,M,ir,aux,O,op) |= V293_rdy_raw_cells (frame) Atrue).
 { eapply V293_raw_cells_environment;[right;reflexivity|exact Owned]. }
 assert (F1 : fresh M b7).
 { apply Fresh. clear - b1 b2 b3 b4 b5 b6 b7 b8 b9;unfold V293_tcb_function_blocks;cbn;tauto. }
 pose proof (V293_tick_allocate_frame ge le M ir aux O op b7 Tint16 _ F1 H0) as A1.
 destruct (V293_tick_raw_slot_update (b7,0) Tint16 Vundef v7
  _ _ _ _ _ _ _ _ V7 A1) as (M1 & Store1 & Updated1).
 assert (H1 : (ge,le,M1,ir,aux,O,op) |= Amapsto (b7,0) Tint16 true v7 ** (V293_rdy_raw_cells (frame) Atrue)).
 { unfold V293_owned_record_cell in Updated1. apply astar_assoc_elim in Updated1.
   apply astar_l_apure_elim in Updated1. exact (proj2 Updated1). }
 assert (F2 : fresh M1 b6).
 { eapply V293_tcb_fresh_alloc_store with (M:=M) (b:=b7) (tp:=Tint16) (v:=v7);[congruence| |exact Store1]. apply Fresh. clear - b1 b2 b3 b4 b5 b6 b7 b8 b9;unfold V293_tcb_function_blocks;cbn;tauto. }
 pose proof (V293_tick_allocate_frame ge le M1 ir aux O op b6 (Tptr Tvoid) _ F2 H1) as A2.
 destruct (V293_tick_raw_slot_update (b6,0) (Tptr Tvoid) Vundef v6
  _ _ _ _ _ _ _ _ V6 A2) as (M2 & Store2 & Updated2).
 assert (H2 : (ge,le,M2,ir,aux,O,op) |= Amapsto (b6,0) (Tptr Tvoid) true v6 ** (Amapsto (b7,0) Tint16 true v7 ** (V293_rdy_raw_cells (frame) Atrue))).
 { unfold V293_owned_record_cell in Updated2. apply astar_assoc_elim in Updated2.
   apply astar_l_apure_elim in Updated2. exact (proj2 Updated2). }
 assert (F3 : fresh M2 b5).
 { eapply V293_tcb_fresh_alloc_store with (M:=M1) (b:=b6) (tp:=(Tptr Tvoid)) (v:=v6);[congruence| |exact Store2]. eapply V293_tcb_fresh_alloc_store with (M:=M) (b:=b7) (tp:=Tint16) (v:=v7);[congruence| |exact Store1]. apply Fresh. clear - b1 b2 b3 b4 b5 b6 b7 b8 b9;unfold V293_tcb_function_blocks;cbn;tauto. }
 pose proof (V293_tick_allocate_frame ge le M2 ir aux O op b5 Tint32 _ F3 H2) as A3.
 destruct (V293_tick_raw_slot_update (b5,0) Tint32 Vundef v5
  _ _ _ _ _ _ _ _ V5 A3) as (M3 & Store3 & Updated3).
 assert (H3 : (ge,le,M3,ir,aux,O,op) |= Amapsto (b5,0) Tint32 true v5 ** (Amapsto (b6,0) (Tptr Tvoid) true v6 ** (Amapsto (b7,0) Tint16 true v7 ** (V293_rdy_raw_cells (frame) Atrue)))).
 { unfold V293_owned_record_cell in Updated3. apply astar_assoc_elim in Updated3.
   apply astar_l_apure_elim in Updated3. exact (proj2 Updated3). }
 assert (F4 : fresh M3 b4).
 { eapply V293_tcb_fresh_alloc_store with (M:=M2) (b:=b5) (tp:=Tint32) (v:=v5);[congruence| |exact Store3]. eapply V293_tcb_fresh_alloc_store with (M:=M1) (b:=b6) (tp:=(Tptr Tvoid)) (v:=v6);[congruence| |exact Store2]. eapply V293_tcb_fresh_alloc_store with (M:=M) (b:=b7) (tp:=Tint16) (v:=v7);[congruence| |exact Store1]. apply Fresh. clear - b1 b2 b3 b4 b5 b6 b7 b8 b9;unfold V293_tcb_function_blocks;cbn;tauto. }
 pose proof (V293_tick_allocate_frame ge le M3 ir aux O op b4 Tint16 _ F4 H3) as A4.
 destruct (V293_tick_raw_slot_update (b4,0) Tint16 Vundef v4
  _ _ _ _ _ _ _ _ V4 A4) as (M4 & Store4 & Updated4).
 assert (H4 : (ge,le,M4,ir,aux,O,op) |= Amapsto (b4,0) Tint16 true v4 ** (Amapsto (b5,0) Tint32 true v5 ** (Amapsto (b6,0) (Tptr Tvoid) true v6 ** (Amapsto (b7,0) Tint16 true v7 ** (V293_rdy_raw_cells (frame) Atrue))))).
 { unfold V293_owned_record_cell in Updated4. apply astar_assoc_elim in Updated4.
   apply astar_l_apure_elim in Updated4. exact (proj2 Updated4). }
 assert (F5 : fresh M4 b3).
 { eapply V293_tcb_fresh_alloc_store with (M:=M3) (b:=b4) (tp:=Tint16) (v:=v4);[congruence| |exact Store4]. eapply V293_tcb_fresh_alloc_store with (M:=M2) (b:=b5) (tp:=Tint32) (v:=v5);[congruence| |exact Store3]. eapply V293_tcb_fresh_alloc_store with (M:=M1) (b:=b6) (tp:=(Tptr Tvoid)) (v:=v6);[congruence| |exact Store2]. eapply V293_tcb_fresh_alloc_store with (M:=M) (b:=b7) (tp:=Tint16) (v:=v7);[congruence| |exact Store1]. apply Fresh. clear - b1 b2 b3 b4 b5 b6 b7 b8 b9;unfold V293_tcb_function_blocks;cbn;tauto. }
 pose proof (V293_tick_allocate_frame ge le M4 ir aux O op b3 (Tptr Tint32) _ F5 H4) as A5.
 destruct (V293_tick_raw_slot_update (b3,0) (Tptr Tint32) Vundef v3
  _ _ _ _ _ _ _ _ V3 A5) as (M5 & Store5 & Updated5).
 assert (H5 : (ge,le,M5,ir,aux,O,op) |= Amapsto (b3,0) (Tptr Tint32) true v3 ** (Amapsto (b4,0) Tint16 true v4 ** (Amapsto (b5,0) Tint32 true v5 ** (Amapsto (b6,0) (Tptr Tvoid) true v6 ** (Amapsto (b7,0) Tint16 true v7 ** (V293_rdy_raw_cells (frame) Atrue)))))).
 { unfold V293_owned_record_cell in Updated5. apply astar_assoc_elim in Updated5.
   apply astar_l_apure_elim in Updated5. exact (proj2 Updated5). }
 assert (F6 : fresh M5 b2).
 { eapply V293_tcb_fresh_alloc_store with (M:=M4) (b:=b3) (tp:=(Tptr Tint32)) (v:=v3);[congruence| |exact Store5]. eapply V293_tcb_fresh_alloc_store with (M:=M3) (b:=b4) (tp:=Tint16) (v:=v4);[congruence| |exact Store4]. eapply V293_tcb_fresh_alloc_store with (M:=M2) (b:=b5) (tp:=Tint32) (v:=v5);[congruence| |exact Store3]. eapply V293_tcb_fresh_alloc_store with (M:=M1) (b:=b6) (tp:=(Tptr Tvoid)) (v:=v6);[congruence| |exact Store2]. eapply V293_tcb_fresh_alloc_store with (M:=M) (b:=b7) (tp:=Tint16) (v:=v7);[congruence| |exact Store1]. apply Fresh. clear - b1 b2 b3 b4 b5 b6 b7 b8 b9;unfold V293_tcb_function_blocks;cbn;tauto. }
 pose proof (V293_tick_allocate_frame ge le M5 ir aux O op b2 (Tptr Tint32) _ F6 H5) as A6.
 destruct (V293_tick_raw_slot_update (b2,0) (Tptr Tint32) Vundef v2
  _ _ _ _ _ _ _ _ V2 A6) as (M6 & Store6 & Updated6).
 assert (H6 : (ge,le,M6,ir,aux,O,op) |= Amapsto (b2,0) (Tptr Tint32) true v2 ** (Amapsto (b3,0) (Tptr Tint32) true v3 ** (Amapsto (b4,0) Tint16 true v4 ** (Amapsto (b5,0) Tint32 true v5 ** (Amapsto (b6,0) (Tptr Tvoid) true v6 ** (Amapsto (b7,0) Tint16 true v7 ** (V293_rdy_raw_cells (frame) Atrue))))))).
 { unfold V293_owned_record_cell in Updated6. apply astar_assoc_elim in Updated6.
   apply astar_l_apure_elim in Updated6. exact (proj2 Updated6). }
 assert (F7 : fresh M6 b1).
 { eapply V293_tcb_fresh_alloc_store with (M:=M5) (b:=b2) (tp:=(Tptr Tint32)) (v:=v2);[congruence| |exact Store6]. eapply V293_tcb_fresh_alloc_store with (M:=M4) (b:=b3) (tp:=(Tptr Tint32)) (v:=v3);[congruence| |exact Store5]. eapply V293_tcb_fresh_alloc_store with (M:=M3) (b:=b4) (tp:=Tint16) (v:=v4);[congruence| |exact Store4]. eapply V293_tcb_fresh_alloc_store with (M:=M2) (b:=b5) (tp:=Tint32) (v:=v5);[congruence| |exact Store3]. eapply V293_tcb_fresh_alloc_store with (M:=M1) (b:=b6) (tp:=(Tptr Tvoid)) (v:=v6);[congruence| |exact Store2]. eapply V293_tcb_fresh_alloc_store with (M:=M) (b:=b7) (tp:=Tint16) (v:=v7);[congruence| |exact Store1]. apply Fresh. clear - b1 b2 b3 b4 b5 b6 b7 b8 b9;unfold V293_tcb_function_blocks;cbn;tauto. }
 pose proof (V293_tick_allocate_frame ge le M6 ir aux O op b1 Tint8 _ F7 H6) as A7.
 destruct (V293_tick_raw_slot_update (b1,0) Tint8 Vundef v1
  _ _ _ _ _ _ _ _ V1 A7) as (M7 & Store7 & Updated7).
 assert (H7 : (ge,le,M7,ir,aux,O,op) |= Amapsto (b1,0) Tint8 true v1 ** (Amapsto (b2,0) (Tptr Tint32) true v2 ** (Amapsto (b3,0) (Tptr Tint32) true v3 ** (Amapsto (b4,0) Tint16 true v4 ** (Amapsto (b5,0) Tint32 true v5 ** (Amapsto (b6,0) (Tptr Tvoid) true v6 ** (Amapsto (b7,0) Tint16 true v7 ** (V293_rdy_raw_cells (frame) Atrue)))))))).
 { unfold V293_owned_record_cell in Updated7. apply astar_assoc_elim in Updated7.
   apply astar_l_apure_elim in Updated7. exact (proj2 Updated7). }
 assert (F8 : fresh M7 b8).
 { eapply V293_tcb_fresh_alloc_store with (M:=M6) (b:=b1) (tp:=Tint8) (v:=v1);[congruence| |exact Store7]. eapply V293_tcb_fresh_alloc_store with (M:=M5) (b:=b2) (tp:=(Tptr Tint32)) (v:=v2);[congruence| |exact Store6]. eapply V293_tcb_fresh_alloc_store with (M:=M4) (b:=b3) (tp:=(Tptr Tint32)) (v:=v3);[congruence| |exact Store5]. eapply V293_tcb_fresh_alloc_store with (M:=M3) (b:=b4) (tp:=Tint16) (v:=v4);[congruence| |exact Store4]. eapply V293_tcb_fresh_alloc_store with (M:=M2) (b:=b5) (tp:=Tint32) (v:=v5);[congruence| |exact Store3]. eapply V293_tcb_fresh_alloc_store with (M:=M1) (b:=b6) (tp:=(Tptr Tvoid)) (v:=v6);[congruence| |exact Store2]. eapply V293_tcb_fresh_alloc_store with (M:=M) (b:=b7) (tp:=Tint16) (v:=v7);[congruence| |exact Store1]. apply Fresh. clear - b1 b2 b3 b4 b5 b6 b7 b8 b9;unfold V293_tcb_function_blocks;cbn;tauto. }
 pose proof (V293_tick_allocate_frame ge le M7 ir aux O op b8 (Tptr V293_tcb_type) _ F8 H7) as A8.
 set (M8:=allocb M7 b8 0 (typelen (Tptr V293_tcb_type))).
 pose proof A8 as H8.
 assert (F9 : fresh M8 b9).
 { unfold M8. apply V293_tcb_fresh_after_alloc;[congruence| ]. eapply V293_tcb_fresh_alloc_store with (M:=M6) (b:=b1) (tp:=Tint8) (v:=v1);[congruence| |exact Store7]. eapply V293_tcb_fresh_alloc_store with (M:=M5) (b:=b2) (tp:=(Tptr Tint32)) (v:=v2);[congruence| |exact Store6]. eapply V293_tcb_fresh_alloc_store with (M:=M4) (b:=b3) (tp:=(Tptr Tint32)) (v:=v3);[congruence| |exact Store5]. eapply V293_tcb_fresh_alloc_store with (M:=M3) (b:=b4) (tp:=Tint16) (v:=v4);[congruence| |exact Store4]. eapply V293_tcb_fresh_alloc_store with (M:=M2) (b:=b5) (tp:=Tint32) (v:=v5);[congruence| |exact Store3]. eapply V293_tcb_fresh_alloc_store with (M:=M1) (b:=b6) (tp:=(Tptr Tvoid)) (v:=v6);[congruence| |exact Store2]. eapply V293_tcb_fresh_alloc_store with (M:=M) (b:=b7) (tp:=Tint16) (v:=v7);[congruence| |exact Store1]. apply Fresh. clear - b1 b2 b3 b4 b5 b6 b7 b8 b9;unfold V293_tcb_function_blocks;cbn;tauto. }
 pose proof (V293_tick_allocate_frame ge le M8 ir aux O op b9 Tint32 _ F9 H8) as A9.
 set (M9:=allocb M8 b9 0 (typelen Tint32)).
 pose proof A9 as H9.
 assert (SavedBinding : get le 109%Z=Some(b9,Tint32)).
 { unfold le,V293_tcb_function_env. apply map_get_set. }
 assert (PtcbBinding : get le 108%Z=Some(b8,Tptr V293_tcb_type)).
 { unfold le,V293_tcb_function_env. rewrite map_get_set' by discriminate;apply map_get_set. }
 assert (FreeLocal : get le 91%Z=None).
 { unfold le,V293_tcb_function_env. repeat rewrite map_get_set' by discriminate. apply map_emp_get. }
 assert (Hraw : (ge,le,M9,ir,aux,O,op) |= V293_rdy_raw_cells
  (V293_tcb_function_cells b1 b2 b3 b4 b5 b6 b7 b8 b9 v1 v2 v3 v4 v5 v6 v7 Vundef Vundef ++ frame) Atrue).
 { exact H9. }
 unfold V293_tcb_function_cells in Hraw. cbn [app] in Hraw.
 assert (SavedTy : evaltype (evar 109%Z) (ge,le,M9)=Some Tint32) by V293_rdy_eval.
 assert (SavedAddr : evaladdr (evar 109%Z) (ge,le,M9)=Some(Vptr(b9,Int.repr 0))) by V293_rdy_eval.
 destruct (V293_rdy_assign nil (b9,0) Tint32 Vundef
  (tl (V293_tcb_function_cells b1 b2 b3 b4 b5 b6 b7 b8 b9 v1 v2 v3 v4 v5 v6 v7 Vundef Vundef)++frame)
  (Vint32 Int.zero) (evar 109%Z) (econst32 Int.zero) Tint32 Atrue P ge le M9 ir aux O op
  SavedTy SavedAddr eq_refl eq_refl ltac:(apply eq_int;auto) eq_refl eq_refl Hraw)
  as (M10 & Init & H10).
 set (body:=V293_TCBInit_function_body hook_init hook_create).
 exists M10. split.
 - eapply V293_local_cons.
   { apply ostc_step. eapply stmt_step;[reflexivity| ].
     eapply sfexec_step with (d1:=V293_TCBInit_parameters) (d2:=V293_TCBInit_locals);
     [reflexivity|reflexivity|exact Program|repeat split| ].
     change ((if rule_type_val_match Tint16 v7 then
      if rule_type_val_match (Tptr Tvoid) v6 then
      if rule_type_val_match Tint32 v5 then
      if rule_type_val_match Tint16 v4 then
      if rule_type_val_match (Tptr Tint32) v3 then
      if rule_type_val_match (Tptr Tint32) v2 then
      if rule_type_val_match Tint8 v1 then true else false else false else false else false else false else false else false)=true).
     rewrite V1,V2,V3,V4,V5,V6,V7;reflexivity. }
  eapply V293_local_cons. { apply ostc_step. eapply stmt_step;[reflexivity| ].
   eapply sallocp_step;[reflexivity|reflexivity| |apply map_get_set|exact Store1].
   exists b7. repeat split;try reflexivity;try exact F1.
   intros [v E]. repeat rewrite map_get_set' in E by discriminate. rewrite map_emp_get in E;discriminate. }
  eapply V293_local_cons. { apply ostc_step. eapply stmt_step;[reflexivity| ].
   eapply sallocp_step;[reflexivity|reflexivity| |apply map_get_set|exact Store2].
   exists b6. repeat split;try reflexivity;try exact F2.
   intros [v E]. repeat rewrite map_get_set' in E by discriminate. rewrite map_emp_get in E;discriminate. }
  eapply V293_local_cons. { apply ostc_step. eapply stmt_step;[reflexivity| ].
   eapply sallocp_step;[reflexivity|reflexivity| |apply map_get_set|exact Store3].
   exists b5. repeat split;try reflexivity;try exact F3.
   intros [v E]. repeat rewrite map_get_set' in E by discriminate. rewrite map_emp_get in E;discriminate. }
  eapply V293_local_cons. { apply ostc_step. eapply stmt_step;[reflexivity| ].
   eapply sallocp_step;[reflexivity|reflexivity| |apply map_get_set|exact Store4].
   exists b4. repeat split;try reflexivity;try exact F4.
   intros [v E]. repeat rewrite map_get_set' in E by discriminate. rewrite map_emp_get in E;discriminate. }
  eapply V293_local_cons. { apply ostc_step. eapply stmt_step;[reflexivity| ].
   eapply sallocp_step;[reflexivity|reflexivity| |apply map_get_set|exact Store5].
   exists b3. repeat split;try reflexivity;try exact F5.
   intros [v E]. repeat rewrite map_get_set' in E by discriminate. rewrite map_emp_get in E;discriminate. }
  eapply V293_local_cons. { apply ostc_step. eapply stmt_step;[reflexivity| ].
   eapply sallocp_step;[reflexivity|reflexivity| |apply map_get_set|exact Store6].
   exists b2. repeat split;try reflexivity;try exact F6.
   intros [v E]. repeat rewrite map_get_set' in E by discriminate. rewrite map_emp_get in E;discriminate. }
  eapply V293_local_cons. { apply ostc_step. eapply stmt_step;[reflexivity| ].
   eapply sallocp_step;[reflexivity|reflexivity| |apply map_get_set|exact Store7].
   exists b1. repeat split;try reflexivity;try exact F7.
   intros [v E]. repeat rewrite map_get_set' in E by discriminate. rewrite map_emp_get in E;discriminate. }
  eapply V293_local_cons. { apply ostc_step. eapply stmt_step;[reflexivity| ].
   eapply salloclv_step;[reflexivity|reflexivity| ].
   exists b8. repeat split;try reflexivity;try exact F8.
   intros [v E]. repeat rewrite map_get_set' in E by discriminate. rewrite map_emp_get in E;discriminate. }
  eapply V293_local_cons. { apply ostc_step. eapply stmt_step;[reflexivity| ].
   eapply salloclv_step;[reflexivity|reflexivity| ].
   exists b9. repeat split;try reflexivity;try exact F9.
   intros [v E]. repeat rewrite map_get_set' in E by discriminate. rewrite map_emp_get in E;discriminate. }
   eapply V293_local_cons. { apply ostc_step. eapply stmt_step;[reflexivity|apply sallocend_step]. }
   change (V293_local_steps P
    (curs(V293_TCBInit_function_body hook_init hook_create),(kenil,kcall f body caller ks))
    ((ge,le,M9),ir,(enabled,si,ci))
    (curs(V293_TCBInit_prefix 91%Z 108%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z
      (V293_TCBInit_success_suffix hook_init hook_create)),(kenil,kcall f body caller ks))
    ((ge,le,M10),ir,(enabled,si,ci))).
   unfold V293_TCBInit_function_body at 1.
   eapply V293_local_cons. { apply ostc_step. eapply stmt_step;[reflexivity|apply sseq_step]. }
   eapply V293_local_trans. { apply V293_csteps_local. apply Init. }
   eapply V293_local_cons. { apply ostc_step. eapply stmt_step;[reflexivity|apply sskip_step]. }
   apply V293_local_refl.
 - exact H10.
Qed.

Lemma V293_tcb_fresh_nine : forall M,
 exists b1 b2 b3 b4 b5 b6 b7 b8 b9,
 NoDup (V293_tcb_function_blocks b1 b2 b3 b4 b5 b6 b7 b8 b9) /\
 (forall b, In b (V293_tcb_function_blocks b1 b2 b3 b4 b5 b6 b7 b8 b9) -> fresh M b).
Proof.
 intros M. destruct (HalfPermMap.bounded M) as [bound Below].
 exists bound. exists (Pos.succ bound). exists (Pos.succ (Pos.succ bound)). exists
 (Pos.succ (Pos.succ (Pos.succ bound))). exists
 (Pos.succ (Pos.succ (Pos.succ (Pos.succ bound)))). exists
 (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ bound))))). exists
 (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ bound)))))). exists
 (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ bound))))))). exists
 (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ bound)))))))).
 split.
 - clear Below. unfold V293_tcb_function_blocks. repeat constructor;cbn;intuition lia.
 - intros b Member a i E [v Read];subst a.
   assert (Small : (b<bound)%positive) by (eapply Below;exact Read).
   unfold V293_tcb_function_blocks in Member. cbn in Member.
   repeat destruct Member as [Same|Member];try contradiction;subst b;lia.
Qed.

(* This is exactly the tail of the retained full source-mapped success suffix,
   not a replacement hook body. *)
Definition V293_tcb_after_init_hook hook_init hook_create :=
 match V293_TCBInit_success_suffix hook_init hook_create with
 | sseq _ tail => tail | _ => sskip None end.
Definition V293_tcb_first_hook_cont f hook_init hook_create caller ks :=
 kseq (V293_tcb_after_init_hook hook_init hook_create)
  (kseq V293_TCBInit_empty
   (kcall f (V293_TCBInit_function_body hook_init hook_create) caller ks)).

(* Stable interface: actual evaluated-argument function entry to the first
   actual hook invocation. All nine blocks are constructed from M. *)
Theorem V293_OS_TCBInit_call_to_first_hook : forall P ks ge caller M ir aux O op enabled si ci
 f hook_init hook_create bf bt base p top bottom identity size ext options next old frame,
 P f=Some (V293_TCBInit_function hook_init hook_create) ->
 get ge 91%Z=Some (bf,Tptr V293_tcb_type) ->
 (p<13)%nat -> (0<=base)%Z -> (base+55<=Int.max_unsigned)%Z ->
 V293_tcb_init_values_valid top bottom identity size ext options ->
 rule_type_val_match (Tptr V293_tcb_type) next=true ->
 (ge,caller,M,ir,aux,O,op) |= V293_rdy_raw_cells
 (V293_tcb_init_old_fields bt base old ++
  V293_tcb_prefix_links bf bt base (Vptr (bt,Int.repr base)) next ++frame) Atrue ->
 exists b1 b2 b3 b4 b5 b6 b7 b8 b9 Mf,
 NoDup (V293_tcb_function_blocks b1 b2 b3 b4 b5 b6 b7 b8 b9) /\
 V293_local_steps P
  (curs(sfexec f [options;ext;size;identity;bottom;top;V293_byteval p]
    V293_TCBInit_argument_types),(kenil,ks))
  ((ge,caller,M),ir,(enabled,si,ci))
  (curs(sfexec hook_init (Vptr(bt,Int.repr base)::nil) (Tptr V293_tcb_type::nil)),
   (kenil,V293_tcb_first_hook_cont f hook_init hook_create caller ks))
  ((ge,V293_tcb_function_env b1 b2 b3 b4 b5 b6 b7 b8 b9,Mf),ir,(enabled,si,ci)) /\
 (ge,V293_tcb_function_env b1 b2 b3 b4 b5 b6 b7 b8 b9,Mf,ir,aux,O,op) |=
 V293_rdy_raw_cells
 (V293_tcb_init_final_fields bt base p top bottom identity size ext options ++
  V293_tcb_init_input_cells b8 b1 b2 b3 b4 b5 b6 b7 bt base p top bottom identity size ext options ++
  V293_tcb_prefix_links bf bt base next next ++((b9,0),Tint32,Vint32 Int.zero)::frame) Atrue /\
 (P hook_init=None -> ~ exists C' state',
  loststep P
  (curs(sfexec hook_init (Vptr(bt,Int.repr base)::nil) (Tptr V293_tcb_type::nil)),
   (kenil,V293_tcb_first_hook_cont f hook_init hook_create caller ks))
  ((ge,V293_tcb_function_env b1 b2 b3 b4 b5 b6 b7 b8 b9,Mf),ir,(enabled,si,ci)) C' state').
Proof.
 intros P ks ge caller M ir aux O op enabled si ci f hook_init hook_create bf bt base
 p top bottom identity size ext options next old frame Program Global Range Base Bound Valid Next Owned.
 destruct (V293_tcb_fresh_nine M) as (b1&b2&b3&b4&b5&b6&b7&b8&b9&ND&Fresh).
 set (le:=V293_tcb_function_env b1 b2 b3 b4 b5 b6 b7 b8 b9).
 assert (Values : V293_tcb_function_values_valid (V293_byteval p) top bottom identity size ext options).
 { unfold V293_tcb_function_values_valid. unfold V293_tcb_init_values_valid in Valid.
   split;[apply V293_byte_type;lia|exact Valid]. }
 destruct (V293_tcb_call_prologue P ks ge caller M ir aux O op enabled si ci
  f hook_init hook_create b1 b2 b3 b4 b5 b6 b7 b8 b9
  (V293_byteval p) top bottom identity size ext options _ Program ND Fresh Values Owned)
 as (Mi&Prologue&Allocated).
 assert (Env : V293_tcb_init_env le 108%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z b8 b1 b2 b3 b4 b5 b6 b7).
 { unfold V293_tcb_init_env,le,V293_tcb_function_env. repeat split;
   repeat rewrite map_get_set' by discriminate;apply map_get_set. }
 assert (FreeLocal : get le 91%Z=None).
 { unfold le,V293_tcb_function_env. repeat rewrite map_get_set' by discriminate. apply map_emp_get. }
 assert (Start : (ge,le,Mi,ir,aux,O,op) |= V293_rdy_raw_cells
 (V293_tcb_init_old_fields bt base old ++
  V293_tcb_prefix_inputs b8 b1 b2 b3 b4 b5 b6 b7 Vundef p top bottom identity size ext options ++
  V293_tcb_prefix_links bf bt base (Vptr(bt,Int.repr base)) next)
 (V293_rdy_raw_cells (((b9,0),Tint32,Vint32 Int.zero)::frame) Atrue)).
 { unfold V293_tcb_function_cells,V293_tcb_prefix_inputs,V293_tcb_init_input_cells,
     V293_tcb_init_old_fields,V293_tcb_prefix_links in Allocated |- *.
   cbn [V293_rdy_raw_cells app tl] in Allocated |- *. clear -Allocated. sep auto. }
 destruct (V293_OS_TCBInit_prefix_execution P
  (kcall f (V293_TCBInit_function_body hook_init hook_create) caller ks) ge le Mi ir aux O op
  _ enabled si ci 91%Z 108%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z
  b8 b1 b2 b3 b4 b5 b6 b7 bf bt base p top bottom identity size ext options Vundef next old
  (V293_TCBInit_success_suffix hook_init hook_create) Range Base Bound FreeLocal Global Env Valid Next Start)
 as (Mf&Prefix&Final).
 assert (PtcbBinding : get le 108%Z=Some(b8,Tptr V293_tcb_type)) by exact (proj1 Env).
 V293_tcb_init_read Final 18%nat PtrRead.
 exists b1. exists b2. exists b3. exists b4. exists b5. exists b6. exists b7. exists b8. exists b9. exists Mf. split;[exact ND| ]. split.
 - eapply V293_local_trans;[exact Prologue| ].
   eapply V293_local_trans;[exact Prefix| ].
   unfold V293_TCBInit_success_suffix,V293_tcb_first_hook_cont,V293_tcb_after_init_hook.
   eapply V293_local_cons. { apply ostc_step. eapply stmt_step;[reflexivity|apply sseq_step]. }
   eapply V293_local_cons. { apply ostc_step. eapply stmt_step;[reflexivity| ].
     apply spcall_step with (t:=Tptr V293_tcb_type). V293_rdy_eval. }
   eapply V293_local_trans.
   { apply V293_csteps_local. apply V293_expr_steps. apply evalval_imply_estepstar.
     assert (HookValue : evalval (evar 108%Z) (ge,le,Mf)=Some(Vptr(bt,Int.repr base))) by V293_rdy_eval.
     exact HookValue. }
   eapply V293_local_cons. { apply ostc_step. eapply stmt_step;[reflexivity|apply svfevalnil_step]. }
   apply V293_local_refl.
 - split.
   + rewrite <-V293_raw_cells_append in Final. rewrite app_assoc. exact Final.
   + intros Missing. apply V293_missing_port_has_no_step. exact Missing.
Qed.
Print Assumptions V293_tcb_call_prologue.
Print Assumptions V293_tcb_fresh_nine.
Print Assumptions V293_OS_TCBInit_call_to_first_hook.
