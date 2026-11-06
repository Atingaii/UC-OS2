Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateExtPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateSuffix.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateTCBSuccess.
Require Import CertiOS.certiucos.v293.proofs.V293TCBCallSuccess.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPriorityHook.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitEntry.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateTCBEntry.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateStackEntry.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtSuffix.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtPrefix.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtCalls.
Require Import Coq.Lists.List Coq.Sorting.Permutation Lia.
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

Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtFunction.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateReturn.
Definition V293_create_function_env btask barg btop bp bi bb bz be bopt bs berr bc : env := set (set (set (set (set (set (set (set (set (set (set (set ((emp:env)) 204%Z (bopt,Tint16)) 208%Z (be,(Tptr Tvoid))) 207%Z (bz,Tint32)) 205%Z (bb,(Tptr Tint32))) 206%Z (bi,Tint16)) 101%Z (bp,Tint8)) 203%Z (btop,(Tptr Tint32))) 202%Z (barg,(Tptr Tvoid))) 201%Z (btask,Tint32)) 108%Z (bs,(Tptr Tint32))) 209%Z (berr,Tint8)) 109%Z (bc,Tint32).
Definition V293_create_function_blocks (btask barg btop bp bi bb bz be bopt bs berr bc : block) := [btask;barg;btop;bp;bi;bb;bz;be;bopt;bs;berr;bc].
Definition V293_create_function_cells btask barg btop bp bi bb bz be bopt bs berr bc v1 v2 v3 v4 v5 v6 v7 v8 v9 : list V293_record_cell := [((bc,0),Tint32,Vundef);((berr,0),Tint8,Vundef);((bs,0),(Tptr Tint32),Vundef);((btask,0),Tint32,v1);((barg,0),(Tptr Tvoid),v2);((btop,0),(Tptr Tint32),v3);((bp,0),Tint8,v4);((bi,0),Tint16,v5);((bb,0),(Tptr Tint32),v6);((bz,0),Tint32,v7);((be,0),(Tptr Tvoid),v8);((bopt,0),Tint16,v9)].
Definition V293_create_function_values_valid v1 v2 v3 v4 v5 v6 v7 v8 v9 :=
 rule_type_val_match Tint32 v1=true /\
 rule_type_val_match (Tptr Tvoid) v2=true /\
 rule_type_val_match (Tptr Tint32) v3=true /\
 rule_type_val_match Tint8 v4=true /\
 rule_type_val_match Tint16 v5=true /\
 rule_type_val_match (Tptr Tint32) v6=true /\
 rule_type_val_match Tint32 v7=true /\
 rule_type_val_match (Tptr Tvoid) v8=true /\
 rule_type_val_match Tint16 v9=true.
Lemma V293_create_function_layout : forall btask barg btop bp bi bb bz be bopt bs berr bc,
 getaddr(V293_create_function_env btask barg btop bp bi bb bz be bopt bs berr bc)=V293_create_local_addresses bp bc btask barg btop bopt bs bb bi bz be berr.
Proof.
 intros. unfold V293_create_function_env,V293_create_local_addresses.
 cbv [getaddr getaddrlist EnvMod.set EnvMod.lst EnvMod.set' EnvMod.emp EnvMod.emp' identspec.blt identspec.beq]. reflexivity.
Qed.
(* Actual sfexec -> parameter allocation/stores -> local allocation -> source
   body. In particular cpu_sr remains Vundef here; the body initializes it. *)
Theorem V293_create_call_prologue : forall P ks ge caller M ir aux O op enabled si ci
 f table nesting reserved running sched hook tcb btask barg btop bp bi bb bz be bopt bs berr bc v1 v2 v3 v4 v5 v6 v7 v8 v9 frame,
 P f=Some(V293_CreateExt_function table nesting reserved running sched hook tcb) ->
 NoDup(V293_create_function_blocks btask barg btop bp bi bb bz be bopt bs berr bc) ->
 (forall b, In b (V293_create_function_blocks btask barg btop bp bi bb bz be bopt bs berr bc) -> fresh M b) ->
 V293_create_function_values_valid v1 v2 v3 v4 v5 v6 v7 v8 v9 ->
 (ge,caller,M,ir,aux,O,op) |= V293_rdy_raw_cells frame Atrue ->
 exists Mi,
 V293_local_steps P
 (curs(sfexec f [v9;v8;v7;v6;v5;v4;v3;v2;v1] V293_CreateExt_argument_types),(kenil,ks))
 ((ge,caller,M),ir,(enabled,si,ci))
 (curs(V293_CreateExt_body table nesting reserved running sched hook tcb),(kenil,kcall f (V293_CreateExt_body table nesting reserved running sched hook tcb) caller ks))
 ((ge,V293_create_function_env btask barg btop bp bi bb bz be bopt bs berr bc,Mi),ir,(enabled,si,ci)) /\
 (ge,V293_create_function_env btask barg btop bp bi bb bz be bopt bs berr bc,Mi,ir,aux,O,op) |=
 V293_rdy_raw_cells (V293_create_function_cells btask barg btop bp bi bb bz be bopt bs berr bc v1 v2 v3 v4 v5 v6 v7 v8 v9++frame) Atrue.
Proof.
 intros P ks ge caller M ir aux O op enabled si ci f table nesting reserved running sched hook tcb
 btask barg btop bp bi bb bz be bopt bs berr bc v1 v2 v3 v4 v5 v6 v7 v8 v9 frame Program ND Fresh Valid Owned.
 set (le:=V293_create_function_env btask barg btop bp bi bb bz be bopt bs berr bc).
 pose proof ND as ND0. unfold V293_create_function_blocks in ND0.
 inversion ND0 as [ | a0 tail0 N0 Rest1];subst;clear ND0.
 inversion Rest1 as [ | a1 tail1 N1 Rest2];subst;clear Rest1.
 inversion Rest2 as [ | a2 tail2 N2 Rest3];subst;clear Rest2.
 inversion Rest3 as [ | a3 tail3 N3 Rest4];subst;clear Rest3.
 inversion Rest4 as [ | a4 tail4 N4 Rest5];subst;clear Rest4.
 inversion Rest5 as [ | a5 tail5 N5 Rest6];subst;clear Rest5.
 inversion Rest6 as [ | a6 tail6 N6 Rest7];subst;clear Rest6.
 inversion Rest7 as [ | a7 tail7 N7 Rest8];subst;clear Rest7.
 inversion Rest8 as [ | a8 tail8 N8 Rest9];subst;clear Rest8.
 inversion Rest9 as [ | a9 tail9 N9 Rest10];subst;clear Rest9.
 inversion Rest10 as [ | a10 tail10 N10 Rest11];subst;clear Rest10.
 inversion Rest11 as [ | a11 tail11 N11 Rest12];subst;clear Rest11.
 cbn in N0,N1,N2,N3,N4,N5,N6,N7,N8,N9,N10,N11.
 assert (D_btask_barg : btask<>barg) by (clear -N0;intro E;subst;tauto).
 assert (D_btask_btop : btask<>btop) by (clear -N0;intro E;subst;tauto).
 assert (D_btask_bp : btask<>bp) by (clear -N0;intro E;subst;tauto).
 assert (D_btask_bi : btask<>bi) by (clear -N0;intro E;subst;tauto).
 assert (D_btask_bb : btask<>bb) by (clear -N0;intro E;subst;tauto).
 assert (D_btask_bz : btask<>bz) by (clear -N0;intro E;subst;tauto).
 assert (D_btask_be : btask<>be) by (clear -N0;intro E;subst;tauto).
 assert (D_btask_bopt : btask<>bopt) by (clear -N0;intro E;subst;tauto).
 assert (D_btask_bs : btask<>bs) by (clear -N0;intro E;subst;tauto).
 assert (D_btask_berr : btask<>berr) by (clear -N0;intro E;subst;tauto).
 assert (D_btask_bc : btask<>bc) by (clear -N0;intro E;subst;tauto).
 assert (D_barg_btop : barg<>btop) by (clear -N1;intro E;subst;tauto).
 assert (D_barg_bp : barg<>bp) by (clear -N1;intro E;subst;tauto).
 assert (D_barg_bi : barg<>bi) by (clear -N1;intro E;subst;tauto).
 assert (D_barg_bb : barg<>bb) by (clear -N1;intro E;subst;tauto).
 assert (D_barg_bz : barg<>bz) by (clear -N1;intro E;subst;tauto).
 assert (D_barg_be : barg<>be) by (clear -N1;intro E;subst;tauto).
 assert (D_barg_bopt : barg<>bopt) by (clear -N1;intro E;subst;tauto).
 assert (D_barg_bs : barg<>bs) by (clear -N1;intro E;subst;tauto).
 assert (D_barg_berr : barg<>berr) by (clear -N1;intro E;subst;tauto).
 assert (D_barg_bc : barg<>bc) by (clear -N1;intro E;subst;tauto).
 assert (D_btop_bp : btop<>bp) by (clear -N2;intro E;subst;tauto).
 assert (D_btop_bi : btop<>bi) by (clear -N2;intro E;subst;tauto).
 assert (D_btop_bb : btop<>bb) by (clear -N2;intro E;subst;tauto).
 assert (D_btop_bz : btop<>bz) by (clear -N2;intro E;subst;tauto).
 assert (D_btop_be : btop<>be) by (clear -N2;intro E;subst;tauto).
 assert (D_btop_bopt : btop<>bopt) by (clear -N2;intro E;subst;tauto).
 assert (D_btop_bs : btop<>bs) by (clear -N2;intro E;subst;tauto).
 assert (D_btop_berr : btop<>berr) by (clear -N2;intro E;subst;tauto).
 assert (D_btop_bc : btop<>bc) by (clear -N2;intro E;subst;tauto).
 assert (D_bp_bi : bp<>bi) by (clear -N3;intro E;subst;tauto).
 assert (D_bp_bb : bp<>bb) by (clear -N3;intro E;subst;tauto).
 assert (D_bp_bz : bp<>bz) by (clear -N3;intro E;subst;tauto).
 assert (D_bp_be : bp<>be) by (clear -N3;intro E;subst;tauto).
 assert (D_bp_bopt : bp<>bopt) by (clear -N3;intro E;subst;tauto).
 assert (D_bp_bs : bp<>bs) by (clear -N3;intro E;subst;tauto).
 assert (D_bp_berr : bp<>berr) by (clear -N3;intro E;subst;tauto).
 assert (D_bp_bc : bp<>bc) by (clear -N3;intro E;subst;tauto).
 assert (D_bi_bb : bi<>bb) by (clear -N4;intro E;subst;tauto).
 assert (D_bi_bz : bi<>bz) by (clear -N4;intro E;subst;tauto).
 assert (D_bi_be : bi<>be) by (clear -N4;intro E;subst;tauto).
 assert (D_bi_bopt : bi<>bopt) by (clear -N4;intro E;subst;tauto).
 assert (D_bi_bs : bi<>bs) by (clear -N4;intro E;subst;tauto).
 assert (D_bi_berr : bi<>berr) by (clear -N4;intro E;subst;tauto).
 assert (D_bi_bc : bi<>bc) by (clear -N4;intro E;subst;tauto).
 assert (D_bb_bz : bb<>bz) by (clear -N5;intro E;subst;tauto).
 assert (D_bb_be : bb<>be) by (clear -N5;intro E;subst;tauto).
 assert (D_bb_bopt : bb<>bopt) by (clear -N5;intro E;subst;tauto).
 assert (D_bb_bs : bb<>bs) by (clear -N5;intro E;subst;tauto).
 assert (D_bb_berr : bb<>berr) by (clear -N5;intro E;subst;tauto).
 assert (D_bb_bc : bb<>bc) by (clear -N5;intro E;subst;tauto).
 assert (D_bz_be : bz<>be) by (clear -N6;intro E;subst;tauto).
 assert (D_bz_bopt : bz<>bopt) by (clear -N6;intro E;subst;tauto).
 assert (D_bz_bs : bz<>bs) by (clear -N6;intro E;subst;tauto).
 assert (D_bz_berr : bz<>berr) by (clear -N6;intro E;subst;tauto).
 assert (D_bz_bc : bz<>bc) by (clear -N6;intro E;subst;tauto).
 assert (D_be_bopt : be<>bopt) by (clear -N7;intro E;subst;tauto).
 assert (D_be_bs : be<>bs) by (clear -N7;intro E;subst;tauto).
 assert (D_be_berr : be<>berr) by (clear -N7;intro E;subst;tauto).
 assert (D_be_bc : be<>bc) by (clear -N7;intro E;subst;tauto).
 assert (D_bopt_bs : bopt<>bs) by (clear -N8;intro E;subst;tauto).
 assert (D_bopt_berr : bopt<>berr) by (clear -N8;intro E;subst;tauto).
 assert (D_bopt_bc : bopt<>bc) by (clear -N8;intro E;subst;tauto).
 assert (D_bs_berr : bs<>berr) by (clear -N9;intro E;subst;tauto).
 assert (D_bs_bc : bs<>bc) by (clear -N9;intro E;subst;tauto).
 assert (D_berr_bc : berr<>bc) by (clear -N10;intro E;subst;tauto).
 destruct Valid as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9).
 assert (H0 : (ge,le,M,ir,aux,O,op) |= V293_rdy_raw_cells frame Atrue).
 { eapply V293_raw_cells_environment;[right;reflexivity|exact Owned]. }
 assert (F1 : fresh M bopt).
 { apply Fresh. clear - btask barg btop bp bi bb bz be bopt bs berr bc;unfold V293_create_function_blocks;cbn;tauto. }
 pose proof(V293_tick_allocate_frame ge le M ir aux O op bopt Tint16 _ F1 H0) as A1.
 destruct(V293_tick_raw_slot_update (bopt,0) Tint16 Vundef v9
 _ _ _ _ _ _ _ _ V9 A1) as (M1&Store1&Updated1).
 assert (H1 : (ge,le,M1,ir,aux,O,op) |= Amapsto (bopt,0) Tint16 true v9 ** (V293_rdy_raw_cells frame Atrue)).
 { unfold V293_owned_record_cell in Updated1. apply astar_assoc_elim in Updated1. apply astar_l_apure_elim in Updated1. exact(proj2 Updated1). }
 assert (F2 : fresh M1 be).
 { eapply V293_tcb_fresh_alloc_store with (M:=M) (b:=bopt) (tp:=Tint16) (v:=v9);[congruence| |exact Store1]. apply Fresh. clear - btask barg btop bp bi bb bz be bopt bs berr bc;unfold V293_create_function_blocks;cbn;tauto. }
 pose proof(V293_tick_allocate_frame ge le M1 ir aux O op be (Tptr Tvoid) _ F2 H1) as A2.
 destruct(V293_tick_raw_slot_update (be,0) (Tptr Tvoid) Vundef v8
 _ _ _ _ _ _ _ _ V8 A2) as (M2&Store2&Updated2).
 assert (H2 : (ge,le,M2,ir,aux,O,op) |= Amapsto (be,0) (Tptr Tvoid) true v8 ** (Amapsto (bopt,0) Tint16 true v9 ** (V293_rdy_raw_cells frame Atrue))).
 { unfold V293_owned_record_cell in Updated2. apply astar_assoc_elim in Updated2. apply astar_l_apure_elim in Updated2. exact(proj2 Updated2). }
 assert (F3 : fresh M2 bz).
 { eapply V293_tcb_fresh_alloc_store with (M:=M1) (b:=be) (tp:=(Tptr Tvoid)) (v:=v8);[congruence| |exact Store2]. eapply V293_tcb_fresh_alloc_store with (M:=M) (b:=bopt) (tp:=Tint16) (v:=v9);[congruence| |exact Store1]. apply Fresh. clear - btask barg btop bp bi bb bz be bopt bs berr bc;unfold V293_create_function_blocks;cbn;tauto. }
 pose proof(V293_tick_allocate_frame ge le M2 ir aux O op bz Tint32 _ F3 H2) as A3.
 destruct(V293_tick_raw_slot_update (bz,0) Tint32 Vundef v7
 _ _ _ _ _ _ _ _ V7 A3) as (M3&Store3&Updated3).
 assert (H3 : (ge,le,M3,ir,aux,O,op) |= Amapsto (bz,0) Tint32 true v7 ** (Amapsto (be,0) (Tptr Tvoid) true v8 ** (Amapsto (bopt,0) Tint16 true v9 ** (V293_rdy_raw_cells frame Atrue)))).
 { unfold V293_owned_record_cell in Updated3. apply astar_assoc_elim in Updated3. apply astar_l_apure_elim in Updated3. exact(proj2 Updated3). }
 assert (F4 : fresh M3 bb).
 { eapply V293_tcb_fresh_alloc_store with (M:=M2) (b:=bz) (tp:=Tint32) (v:=v7);[congruence| |exact Store3]. eapply V293_tcb_fresh_alloc_store with (M:=M1) (b:=be) (tp:=(Tptr Tvoid)) (v:=v8);[congruence| |exact Store2]. eapply V293_tcb_fresh_alloc_store with (M:=M) (b:=bopt) (tp:=Tint16) (v:=v9);[congruence| |exact Store1]. apply Fresh. clear - btask barg btop bp bi bb bz be bopt bs berr bc;unfold V293_create_function_blocks;cbn;tauto. }
 pose proof(V293_tick_allocate_frame ge le M3 ir aux O op bb (Tptr Tint32) _ F4 H3) as A4.
 destruct(V293_tick_raw_slot_update (bb,0) (Tptr Tint32) Vundef v6
 _ _ _ _ _ _ _ _ V6 A4) as (M4&Store4&Updated4).
 assert (H4 : (ge,le,M4,ir,aux,O,op) |= Amapsto (bb,0) (Tptr Tint32) true v6 ** (Amapsto (bz,0) Tint32 true v7 ** (Amapsto (be,0) (Tptr Tvoid) true v8 ** (Amapsto (bopt,0) Tint16 true v9 ** (V293_rdy_raw_cells frame Atrue))))).
 { unfold V293_owned_record_cell in Updated4. apply astar_assoc_elim in Updated4. apply astar_l_apure_elim in Updated4. exact(proj2 Updated4). }
 assert (F5 : fresh M4 bi).
 { eapply V293_tcb_fresh_alloc_store with (M:=M3) (b:=bb) (tp:=(Tptr Tint32)) (v:=v6);[congruence| |exact Store4]. eapply V293_tcb_fresh_alloc_store with (M:=M2) (b:=bz) (tp:=Tint32) (v:=v7);[congruence| |exact Store3]. eapply V293_tcb_fresh_alloc_store with (M:=M1) (b:=be) (tp:=(Tptr Tvoid)) (v:=v8);[congruence| |exact Store2]. eapply V293_tcb_fresh_alloc_store with (M:=M) (b:=bopt) (tp:=Tint16) (v:=v9);[congruence| |exact Store1]. apply Fresh. clear - btask barg btop bp bi bb bz be bopt bs berr bc;unfold V293_create_function_blocks;cbn;tauto. }
 pose proof(V293_tick_allocate_frame ge le M4 ir aux O op bi Tint16 _ F5 H4) as A5.
 destruct(V293_tick_raw_slot_update (bi,0) Tint16 Vundef v5
 _ _ _ _ _ _ _ _ V5 A5) as (M5&Store5&Updated5).
 assert (H5 : (ge,le,M5,ir,aux,O,op) |= Amapsto (bi,0) Tint16 true v5 ** (Amapsto (bb,0) (Tptr Tint32) true v6 ** (Amapsto (bz,0) Tint32 true v7 ** (Amapsto (be,0) (Tptr Tvoid) true v8 ** (Amapsto (bopt,0) Tint16 true v9 ** (V293_rdy_raw_cells frame Atrue)))))).
 { unfold V293_owned_record_cell in Updated5. apply astar_assoc_elim in Updated5. apply astar_l_apure_elim in Updated5. exact(proj2 Updated5). }
 assert (F6 : fresh M5 bp).
 { eapply V293_tcb_fresh_alloc_store with (M:=M4) (b:=bi) (tp:=Tint16) (v:=v5);[congruence| |exact Store5]. eapply V293_tcb_fresh_alloc_store with (M:=M3) (b:=bb) (tp:=(Tptr Tint32)) (v:=v6);[congruence| |exact Store4]. eapply V293_tcb_fresh_alloc_store with (M:=M2) (b:=bz) (tp:=Tint32) (v:=v7);[congruence| |exact Store3]. eapply V293_tcb_fresh_alloc_store with (M:=M1) (b:=be) (tp:=(Tptr Tvoid)) (v:=v8);[congruence| |exact Store2]. eapply V293_tcb_fresh_alloc_store with (M:=M) (b:=bopt) (tp:=Tint16) (v:=v9);[congruence| |exact Store1]. apply Fresh. clear - btask barg btop bp bi bb bz be bopt bs berr bc;unfold V293_create_function_blocks;cbn;tauto. }
 pose proof(V293_tick_allocate_frame ge le M5 ir aux O op bp Tint8 _ F6 H5) as A6.
 destruct(V293_tick_raw_slot_update (bp,0) Tint8 Vundef v4
 _ _ _ _ _ _ _ _ V4 A6) as (M6&Store6&Updated6).
 assert (H6 : (ge,le,M6,ir,aux,O,op) |= Amapsto (bp,0) Tint8 true v4 ** (Amapsto (bi,0) Tint16 true v5 ** (Amapsto (bb,0) (Tptr Tint32) true v6 ** (Amapsto (bz,0) Tint32 true v7 ** (Amapsto (be,0) (Tptr Tvoid) true v8 ** (Amapsto (bopt,0) Tint16 true v9 ** (V293_rdy_raw_cells frame Atrue))))))).
 { unfold V293_owned_record_cell in Updated6. apply astar_assoc_elim in Updated6. apply astar_l_apure_elim in Updated6. exact(proj2 Updated6). }
 assert (F7 : fresh M6 btop).
 { eapply V293_tcb_fresh_alloc_store with (M:=M5) (b:=bp) (tp:=Tint8) (v:=v4);[congruence| |exact Store6]. eapply V293_tcb_fresh_alloc_store with (M:=M4) (b:=bi) (tp:=Tint16) (v:=v5);[congruence| |exact Store5]. eapply V293_tcb_fresh_alloc_store with (M:=M3) (b:=bb) (tp:=(Tptr Tint32)) (v:=v6);[congruence| |exact Store4]. eapply V293_tcb_fresh_alloc_store with (M:=M2) (b:=bz) (tp:=Tint32) (v:=v7);[congruence| |exact Store3]. eapply V293_tcb_fresh_alloc_store with (M:=M1) (b:=be) (tp:=(Tptr Tvoid)) (v:=v8);[congruence| |exact Store2]. eapply V293_tcb_fresh_alloc_store with (M:=M) (b:=bopt) (tp:=Tint16) (v:=v9);[congruence| |exact Store1]. apply Fresh. clear - btask barg btop bp bi bb bz be bopt bs berr bc;unfold V293_create_function_blocks;cbn;tauto. }
 pose proof(V293_tick_allocate_frame ge le M6 ir aux O op btop (Tptr Tint32) _ F7 H6) as A7.
 destruct(V293_tick_raw_slot_update (btop,0) (Tptr Tint32) Vundef v3
 _ _ _ _ _ _ _ _ V3 A7) as (M7&Store7&Updated7).
 assert (H7 : (ge,le,M7,ir,aux,O,op) |= Amapsto (btop,0) (Tptr Tint32) true v3 ** (Amapsto (bp,0) Tint8 true v4 ** (Amapsto (bi,0) Tint16 true v5 ** (Amapsto (bb,0) (Tptr Tint32) true v6 ** (Amapsto (bz,0) Tint32 true v7 ** (Amapsto (be,0) (Tptr Tvoid) true v8 ** (Amapsto (bopt,0) Tint16 true v9 ** (V293_rdy_raw_cells frame Atrue)))))))).
 { unfold V293_owned_record_cell in Updated7. apply astar_assoc_elim in Updated7. apply astar_l_apure_elim in Updated7. exact(proj2 Updated7). }
 assert (F8 : fresh M7 barg).
 { eapply V293_tcb_fresh_alloc_store with (M:=M6) (b:=btop) (tp:=(Tptr Tint32)) (v:=v3);[congruence| |exact Store7]. eapply V293_tcb_fresh_alloc_store with (M:=M5) (b:=bp) (tp:=Tint8) (v:=v4);[congruence| |exact Store6]. eapply V293_tcb_fresh_alloc_store with (M:=M4) (b:=bi) (tp:=Tint16) (v:=v5);[congruence| |exact Store5]. eapply V293_tcb_fresh_alloc_store with (M:=M3) (b:=bb) (tp:=(Tptr Tint32)) (v:=v6);[congruence| |exact Store4]. eapply V293_tcb_fresh_alloc_store with (M:=M2) (b:=bz) (tp:=Tint32) (v:=v7);[congruence| |exact Store3]. eapply V293_tcb_fresh_alloc_store with (M:=M1) (b:=be) (tp:=(Tptr Tvoid)) (v:=v8);[congruence| |exact Store2]. eapply V293_tcb_fresh_alloc_store with (M:=M) (b:=bopt) (tp:=Tint16) (v:=v9);[congruence| |exact Store1]. apply Fresh. clear - btask barg btop bp bi bb bz be bopt bs berr bc;unfold V293_create_function_blocks;cbn;tauto. }
 pose proof(V293_tick_allocate_frame ge le M7 ir aux O op barg (Tptr Tvoid) _ F8 H7) as A8.
 destruct(V293_tick_raw_slot_update (barg,0) (Tptr Tvoid) Vundef v2
 _ _ _ _ _ _ _ _ V2 A8) as (M8&Store8&Updated8).
 assert (H8 : (ge,le,M8,ir,aux,O,op) |= Amapsto (barg,0) (Tptr Tvoid) true v2 ** (Amapsto (btop,0) (Tptr Tint32) true v3 ** (Amapsto (bp,0) Tint8 true v4 ** (Amapsto (bi,0) Tint16 true v5 ** (Amapsto (bb,0) (Tptr Tint32) true v6 ** (Amapsto (bz,0) Tint32 true v7 ** (Amapsto (be,0) (Tptr Tvoid) true v8 ** (Amapsto (bopt,0) Tint16 true v9 ** (V293_rdy_raw_cells frame Atrue))))))))).
 { unfold V293_owned_record_cell in Updated8. apply astar_assoc_elim in Updated8. apply astar_l_apure_elim in Updated8. exact(proj2 Updated8). }
 assert (F9 : fresh M8 btask).
 { eapply V293_tcb_fresh_alloc_store with (M:=M7) (b:=barg) (tp:=(Tptr Tvoid)) (v:=v2);[congruence| |exact Store8]. eapply V293_tcb_fresh_alloc_store with (M:=M6) (b:=btop) (tp:=(Tptr Tint32)) (v:=v3);[congruence| |exact Store7]. eapply V293_tcb_fresh_alloc_store with (M:=M5) (b:=bp) (tp:=Tint8) (v:=v4);[congruence| |exact Store6]. eapply V293_tcb_fresh_alloc_store with (M:=M4) (b:=bi) (tp:=Tint16) (v:=v5);[congruence| |exact Store5]. eapply V293_tcb_fresh_alloc_store with (M:=M3) (b:=bb) (tp:=(Tptr Tint32)) (v:=v6);[congruence| |exact Store4]. eapply V293_tcb_fresh_alloc_store with (M:=M2) (b:=bz) (tp:=Tint32) (v:=v7);[congruence| |exact Store3]. eapply V293_tcb_fresh_alloc_store with (M:=M1) (b:=be) (tp:=(Tptr Tvoid)) (v:=v8);[congruence| |exact Store2]. eapply V293_tcb_fresh_alloc_store with (M:=M) (b:=bopt) (tp:=Tint16) (v:=v9);[congruence| |exact Store1]. apply Fresh. clear - btask barg btop bp bi bb bz be bopt bs berr bc;unfold V293_create_function_blocks;cbn;tauto. }
 pose proof(V293_tick_allocate_frame ge le M8 ir aux O op btask Tint32 _ F9 H8) as A9.
 destruct(V293_tick_raw_slot_update (btask,0) Tint32 Vundef v1
 _ _ _ _ _ _ _ _ V1 A9) as (M9&Store9&Updated9).
 assert (H9 : (ge,le,M9,ir,aux,O,op) |= Amapsto (btask,0) Tint32 true v1 ** (Amapsto (barg,0) (Tptr Tvoid) true v2 ** (Amapsto (btop,0) (Tptr Tint32) true v3 ** (Amapsto (bp,0) Tint8 true v4 ** (Amapsto (bi,0) Tint16 true v5 ** (Amapsto (bb,0) (Tptr Tint32) true v6 ** (Amapsto (bz,0) Tint32 true v7 ** (Amapsto (be,0) (Tptr Tvoid) true v8 ** (Amapsto (bopt,0) Tint16 true v9 ** (V293_rdy_raw_cells frame Atrue)))))))))).
 { unfold V293_owned_record_cell in Updated9. apply astar_assoc_elim in Updated9. apply astar_l_apure_elim in Updated9. exact(proj2 Updated9). }
 assert (F10 : fresh M9 bs).
 { eapply V293_tcb_fresh_alloc_store with (M:=M8) (b:=btask) (tp:=Tint32) (v:=v1);[congruence| |exact Store9]. eapply V293_tcb_fresh_alloc_store with (M:=M7) (b:=barg) (tp:=(Tptr Tvoid)) (v:=v2);[congruence| |exact Store8]. eapply V293_tcb_fresh_alloc_store with (M:=M6) (b:=btop) (tp:=(Tptr Tint32)) (v:=v3);[congruence| |exact Store7]. eapply V293_tcb_fresh_alloc_store with (M:=M5) (b:=bp) (tp:=Tint8) (v:=v4);[congruence| |exact Store6]. eapply V293_tcb_fresh_alloc_store with (M:=M4) (b:=bi) (tp:=Tint16) (v:=v5);[congruence| |exact Store5]. eapply V293_tcb_fresh_alloc_store with (M:=M3) (b:=bb) (tp:=(Tptr Tint32)) (v:=v6);[congruence| |exact Store4]. eapply V293_tcb_fresh_alloc_store with (M:=M2) (b:=bz) (tp:=Tint32) (v:=v7);[congruence| |exact Store3]. eapply V293_tcb_fresh_alloc_store with (M:=M1) (b:=be) (tp:=(Tptr Tvoid)) (v:=v8);[congruence| |exact Store2]. eapply V293_tcb_fresh_alloc_store with (M:=M) (b:=bopt) (tp:=Tint16) (v:=v9);[congruence| |exact Store1]. apply Fresh. clear - btask barg btop bp bi bb bz be bopt bs berr bc;unfold V293_create_function_blocks;cbn;tauto. }
 pose proof(V293_tick_allocate_frame ge le M9 ir aux O op bs (Tptr Tint32) _ F10 H9) as A10.
 set (M10:=allocb M9 bs 0 (typelen (Tptr Tint32))).
 pose proof A10 as H10.
 assert (F11 : fresh M10 berr).
 { unfold M10. apply V293_tcb_fresh_after_alloc;[congruence| ]. eapply V293_tcb_fresh_alloc_store with (M:=M8) (b:=btask) (tp:=Tint32) (v:=v1);[congruence| |exact Store9]. eapply V293_tcb_fresh_alloc_store with (M:=M7) (b:=barg) (tp:=(Tptr Tvoid)) (v:=v2);[congruence| |exact Store8]. eapply V293_tcb_fresh_alloc_store with (M:=M6) (b:=btop) (tp:=(Tptr Tint32)) (v:=v3);[congruence| |exact Store7]. eapply V293_tcb_fresh_alloc_store with (M:=M5) (b:=bp) (tp:=Tint8) (v:=v4);[congruence| |exact Store6]. eapply V293_tcb_fresh_alloc_store with (M:=M4) (b:=bi) (tp:=Tint16) (v:=v5);[congruence| |exact Store5]. eapply V293_tcb_fresh_alloc_store with (M:=M3) (b:=bb) (tp:=(Tptr Tint32)) (v:=v6);[congruence| |exact Store4]. eapply V293_tcb_fresh_alloc_store with (M:=M2) (b:=bz) (tp:=Tint32) (v:=v7);[congruence| |exact Store3]. eapply V293_tcb_fresh_alloc_store with (M:=M1) (b:=be) (tp:=(Tptr Tvoid)) (v:=v8);[congruence| |exact Store2]. eapply V293_tcb_fresh_alloc_store with (M:=M) (b:=bopt) (tp:=Tint16) (v:=v9);[congruence| |exact Store1]. apply Fresh. clear - btask barg btop bp bi bb bz be bopt bs berr bc;unfold V293_create_function_blocks;cbn;tauto. }
 pose proof(V293_tick_allocate_frame ge le M10 ir aux O op berr Tint8 _ F11 H10) as A11.
 set (M11:=allocb M10 berr 0 (typelen Tint8)).
 pose proof A11 as H11.
 assert (F12 : fresh M11 bc).
 { unfold M11. apply V293_tcb_fresh_after_alloc;[congruence| ]. unfold M10. apply V293_tcb_fresh_after_alloc;[congruence| ]. eapply V293_tcb_fresh_alloc_store with (M:=M8) (b:=btask) (tp:=Tint32) (v:=v1);[congruence| |exact Store9]. eapply V293_tcb_fresh_alloc_store with (M:=M7) (b:=barg) (tp:=(Tptr Tvoid)) (v:=v2);[congruence| |exact Store8]. eapply V293_tcb_fresh_alloc_store with (M:=M6) (b:=btop) (tp:=(Tptr Tint32)) (v:=v3);[congruence| |exact Store7]. eapply V293_tcb_fresh_alloc_store with (M:=M5) (b:=bp) (tp:=Tint8) (v:=v4);[congruence| |exact Store6]. eapply V293_tcb_fresh_alloc_store with (M:=M4) (b:=bi) (tp:=Tint16) (v:=v5);[congruence| |exact Store5]. eapply V293_tcb_fresh_alloc_store with (M:=M3) (b:=bb) (tp:=(Tptr Tint32)) (v:=v6);[congruence| |exact Store4]. eapply V293_tcb_fresh_alloc_store with (M:=M2) (b:=bz) (tp:=Tint32) (v:=v7);[congruence| |exact Store3]. eapply V293_tcb_fresh_alloc_store with (M:=M1) (b:=be) (tp:=(Tptr Tvoid)) (v:=v8);[congruence| |exact Store2]. eapply V293_tcb_fresh_alloc_store with (M:=M) (b:=bopt) (tp:=Tint16) (v:=v9);[congruence| |exact Store1]. apply Fresh. clear - btask barg btop bp bi bb bz be bopt bs berr bc;unfold V293_create_function_blocks;cbn;tauto. }
 pose proof(V293_tick_allocate_frame ge le M11 ir aux O op bc Tint32 _ F12 H11) as A12.
 set (M12:=allocb M11 bc 0 (typelen Tint32)).
 pose proof A12 as H12.
 exists M12. split.
 - eapply V293_local_cons. { apply ostc_step. eapply stmt_step;[reflexivity| ].
   eapply sfexec_step with (d1:=V293_CreateExt_parameters) (d2:=V293_CreateExt_locals);[reflexivity|reflexivity|exact Program|repeat split| ].
   change ((if rule_type_val_match Tint16 v9 then if rule_type_val_match (Tptr Tvoid) v8 then if rule_type_val_match Tint32 v7 then if rule_type_val_match (Tptr Tint32) v6 then if rule_type_val_match Tint16 v5 then if rule_type_val_match Tint8 v4 then if rule_type_val_match (Tptr Tint32) v3 then if rule_type_val_match (Tptr Tvoid) v2 then if rule_type_val_match Tint32 v1 then true else false else false else false else false else false else false else false else false else false)=true).
   rewrite V1,V2,V3,V4,V5,V6,V7,V8,V9;reflexivity. }
   eapply V293_local_cons. { apply ostc_step. eapply stmt_step;[reflexivity| ].
    eapply sallocp_step;[reflexivity|reflexivity| |apply map_get_set|exact Store1].
    exists bopt. repeat split;try reflexivity;try exact F1.
    intros [v E]. repeat rewrite map_get_set' in E by discriminate. rewrite map_emp_get in E;discriminate. }
   eapply V293_local_cons. { apply ostc_step. eapply stmt_step;[reflexivity| ].
    eapply sallocp_step;[reflexivity|reflexivity| |apply map_get_set|exact Store2].
    exists be. repeat split;try reflexivity;try exact F2.
    intros [v E]. repeat rewrite map_get_set' in E by discriminate. rewrite map_emp_get in E;discriminate. }
   eapply V293_local_cons. { apply ostc_step. eapply stmt_step;[reflexivity| ].
    eapply sallocp_step;[reflexivity|reflexivity| |apply map_get_set|exact Store3].
    exists bz. repeat split;try reflexivity;try exact F3.
    intros [v E]. repeat rewrite map_get_set' in E by discriminate. rewrite map_emp_get in E;discriminate. }
   eapply V293_local_cons. { apply ostc_step. eapply stmt_step;[reflexivity| ].
    eapply sallocp_step;[reflexivity|reflexivity| |apply map_get_set|exact Store4].
    exists bb. repeat split;try reflexivity;try exact F4.
    intros [v E]. repeat rewrite map_get_set' in E by discriminate. rewrite map_emp_get in E;discriminate. }
   eapply V293_local_cons. { apply ostc_step. eapply stmt_step;[reflexivity| ].
    eapply sallocp_step;[reflexivity|reflexivity| |apply map_get_set|exact Store5].
    exists bi. repeat split;try reflexivity;try exact F5.
    intros [v E]. repeat rewrite map_get_set' in E by discriminate. rewrite map_emp_get in E;discriminate. }
   eapply V293_local_cons. { apply ostc_step. eapply stmt_step;[reflexivity| ].
    eapply sallocp_step;[reflexivity|reflexivity| |apply map_get_set|exact Store6].
    exists bp. repeat split;try reflexivity;try exact F6.
    intros [v E]. repeat rewrite map_get_set' in E by discriminate. rewrite map_emp_get in E;discriminate. }
   eapply V293_local_cons. { apply ostc_step. eapply stmt_step;[reflexivity| ].
    eapply sallocp_step;[reflexivity|reflexivity| |apply map_get_set|exact Store7].
    exists btop. repeat split;try reflexivity;try exact F7.
    intros [v E]. repeat rewrite map_get_set' in E by discriminate. rewrite map_emp_get in E;discriminate. }
   eapply V293_local_cons. { apply ostc_step. eapply stmt_step;[reflexivity| ].
    eapply sallocp_step;[reflexivity|reflexivity| |apply map_get_set|exact Store8].
    exists barg. repeat split;try reflexivity;try exact F8.
    intros [v E]. repeat rewrite map_get_set' in E by discriminate. rewrite map_emp_get in E;discriminate. }
   eapply V293_local_cons. { apply ostc_step. eapply stmt_step;[reflexivity| ].
    eapply sallocp_step;[reflexivity|reflexivity| |apply map_get_set|exact Store9].
    exists btask. repeat split;try reflexivity;try exact F9.
    intros [v E]. repeat rewrite map_get_set' in E by discriminate. rewrite map_emp_get in E;discriminate. }
   eapply V293_local_cons. { apply ostc_step. eapply stmt_step;[reflexivity| ].
    eapply salloclv_step;[reflexivity|reflexivity| ].
    exists bs. repeat split;try reflexivity;try exact F10.
    intros [v E]. repeat rewrite map_get_set' in E by discriminate. rewrite map_emp_get in E;discriminate. }
   eapply V293_local_cons. { apply ostc_step. eapply stmt_step;[reflexivity| ].
    eapply salloclv_step;[reflexivity|reflexivity| ].
    exists berr. repeat split;try reflexivity;try exact F11.
    intros [v E]. repeat rewrite map_get_set' in E by discriminate. rewrite map_emp_get in E;discriminate. }
   eapply V293_local_cons. { apply ostc_step. eapply stmt_step;[reflexivity| ].
    eapply salloclv_step;[reflexivity|reflexivity| ].
    exists bc. repeat split;try reflexivity;try exact F12.
    intros [v E]. repeat rewrite map_get_set' in E by discriminate. rewrite map_emp_get in E;discriminate. }
   eapply V293_local_cons. { apply ostc_step. eapply stmt_step;[reflexivity|apply sallocend_step]. }
   apply V293_local_refl.
 - exact H12.
Qed.
Print Assumptions V293_create_call_prologue.

(* Stable complete conditional call interface. Fresh/distinct input blocks and
   pure survivor separation are explicit; allocated memory/layout are produced
   by real steps, never supplied as premises. Hook implementations stay open. *)
Theorem V293_OSTaskCreateExt_success_call_under_hooks : forall P retks caller f ge M ir aux O op
 enabled si ci table nesting reserved running sched hook tcb bp bn bc bt br p
 btask barg btop bopt target argv topv optv bs bb bi bz be berr bottomv idv sizev extv value
 hi hc bf block base bh bg rows count bo obase present next oldfields prev g r n back frame brun,
 let le:=V293_create_function_env btask barg btop bp bi bb bz be bopt bs berr bc in
 let body:=V293_CreateExt_body table nesting reserved running sched hook tcb in
 let ks:=kcall f body caller retks in
 let rest:=V293_TaskCreateExt_suffix table 101%Z 209%Z running sched in
 let kept:=((brun,0),Tint8,Vint32 Int.zero)::frame in
 let addresses:=V293_create_local_addresses bp bc btask barg btop bopt bs bb bi bz be berr in
 let live:=V293_tcb_creation_result bf bt block base bh bg rows count bo obase present p
 value bottomv idv sizev extv optv next g r n (((bn,0),Tint8,V293_byteval 0)::kept) in
 P f=Some(V293_CreateExt_function table nesting reserved running sched hook tcb) ->
 NoDup(V293_create_function_blocks btask barg btop bp bi bb bz be bopt bs berr bc) ->
 (forall b, In b (V293_create_function_blocks btask barg btop bp bi bb bz be bopt bs berr bc) -> fresh M b) ->
 (forall a tp v, In(a,tp,v) live -> ~In(fst a)(map fst addresses)) ->
 get le running=None -> get ge running=Some(brun,Tint8) ->
 get le nesting=None -> get ge nesting=Some(bn,Tint8) ->
 get le table=None -> get ge table=Some(bt,Tarray(Tptr V293_tcb_type)13) ->
 get le reserved=None -> get ge reserved=Some(br,Tint8) ->
 (p<13)%nat -> 0<=target<=Int.max_unsigned ->
 V293_stack_argument_valid argv topv optv ->
 V293_tcb_init_values_valid value bottomv idv sizev extv optv ->
 P tcb=Some(V293_TCBInit_function hi hc) ->
 get ge 91%Z=Some(bf,Tptr V293_tcb_type) ->
 get ge 92%Z=Some(bt,Tarray(Tptr V293_tcb_type)13) ->
 get ge 93%Z=Some(bh,Tptr V293_tcb_type) -> get ge 94%Z=Some(bg,Tint8) ->
 get ge 95%Z=Some(rows,Tarray Tint8 2) -> get ge 96%Z=Some(count,Tint8) ->
 0<=base -> base+55<=Int.max_unsigned -> 0<=obase -> obase+24<=Int.max_unsigned ->
 (g<256)%nat -> (r<256)%nat -> (n<255)%nat ->
 rule_type_val_match (Tptr V293_tcb_type) next=true ->
 (forall b1 b2 b3 b4 b5 b6 b7 b8 b9,
  NoDup (V293_tcb_function_blocks b1 b2 b3 b4 b5 b6 b7 b8 b9) ->
  V293_tcb_creation_hook_return P hi block base (V293_tcb_first_hook_cont tcb hi hc le (V293_create_TCB_cont 209%Z rest ks))
   ge (V293_tcb_function_env b1 b2 b3 b4 b5 b6 b7 b8 b9) ir aux O op enabled si ci
   (V293_tcb_hook_cells b1 b2 b3 b4 b5 b6 b7 b8 b9 bf bt block base p
    value bottomv idv sizev extv optv next (Vptr(br,Int.zero))
    (V293_tcb_creation_tail block base bh bg rows count bo obase present p prev g r n back++(V293_create_caller_cells bp bn bc p btask barg btop bopt target argv topv optv bs bb bi bz be berr value bottomv idv sizev extv Vundef++kept)))) ->
 (forall b1 b2 b3 b4 b5 b6 b7 b8 b9,
  NoDup (V293_tcb_function_blocks b1 b2 b3 b4 b5 b6 b7 b8 b9) ->
  V293_tcb_creation_hook_return P hc block base (V293_tcb_second_hook_cont tcb hi hc le (V293_create_TCB_cont 209%Z rest ks))
   ge (V293_tcb_function_env b1 b2 b3 b4 b5 b6 b7 b8 b9) ir aux O op enabled si ci
   (V293_tcb_hook_cells b1 b2 b3 b4 b5 b6 b7 b8 b9 bf bt block base p
    value bottomv idv sizev extv optv next (Vptr(block,Int.repr base))
    (V293_tcb_creation_tail block base bh bg rows count bo obase present p prev g r n back++(V293_create_caller_cells bp bn bc p btask barg btop bopt target argv topv optv bs bb bi bz be berr value bottomv idv sizev extv Vundef++kept)))) ->
 V293_create_stack_return P hook [optv;topv;argv;V293_task_selector target]
 (V293_create_stack_cont 108%Z 209%Z tcb 101%Z 205%Z 206%Z 207%Z 208%Z 204%Z rest ks)
 ge le ir aux O op (V293_rdy_raw_cells (V293_create_TCB_support bf block base bh bg rows count bo obase present p next oldfields prev g r n back kept) Atrue) enabled si ci
 (V293_create_bridge_cells bp bn bc bt p (Vint32 Int.zero) (Vptr(br,Int.zero))
 btask barg btop bopt target argv topv optv bs bb bi bz be berr Vundef bottomv idv sizev extv Vundef) value ->
 (ge,caller,M,ir,aux,O,op) |= V293_rdy_raw_cells
 ([((bn,0),Tint8,V293_byteval 0);((bt,4*Z.of_nat p),Tptr V293_tcb_type,Vnull)]++
 V293_create_TCB_support bf block base bh bg rows count bo obase present p next oldfields prev g r n back kept) Atrue ->
 exists Mbridge, exists b1 b2 b3 b4 b5 b6 b7 b8 b9 Mf, exists Mr,
 NoDup (V293_tcb_function_blocks b1 b2 b3 b4 b5 b6 b7 b8 b9) /\
 (forall b, In b (V293_tcb_function_blocks b1 b2 b3 b4 b5 b6 b7 b8 b9) -> fresh Mbridge b) /\
 V293_local_steps P
 (curs(sfexec f [optv;extv;sizev;bottomv;idv;V293_byteval p;topv;argv;V293_task_selector target] V293_CreateExt_argument_types),(kenil,retks))
 ((ge,caller,M),ir,(enabled,si,ci))
 (curs(sfexec tcb [optv;extv;sizev;idv;bottomv;value;V293_byteval p] V293_TCBInit_argument_types),(kenil,V293_create_TCB_cont 209%Z rest ks))
 ((ge,le,Mbridge),ir,(enabled,si,ci)) /\
 V293_local_steps P
 (curs(sfexec f [optv;extv;sizev;bottomv;idv;V293_byteval p;topv;argv;V293_task_selector target] V293_CreateExt_argument_types),(kenil,retks))
 ((ge,caller,M),ir,(enabled,si,ci))
 (curs(sskip(Some(Vint32 Int.zero))),(kenil,retks))
 ((ge,caller,Mr),ir,(enabled,si,ci)) /\
 (ge,caller,Mr,ir,aux,O,op) |= V293_rdy_raw_cells live Atrue /\
 (forall b tp k, In (b,tp) (V293_tcb_function_addresses b1 b2 b3 b4 b5 b6 b7 b8 b9) ->
 (k<typelen tp)%nat -> get Mr (b,Z.of_nat k)=None) /\
 (forall b tp k, In(b,tp) addresses -> (k<typelen tp)%nat -> get Mr(b,Z.of_nat k)=None) /\
 (forall b i, ~In b(map fst addresses) -> get Mr(b,i)=get Mf(b,i)).
Proof.
 intros P retks caller f ge M ir aux O op enabled si ci table nesting reserved running sched hook tcb bp bn bc bt br p
 btask barg btop bopt target argv topv optv bs bb bi bz be berr bottomv idv sizev extv value
 hi hc bf block base bh bg rows count bo obase present next oldfields prev g r n back frame brun
 le body ks rest kept addresses live Function ND Fresh Away
 Nr Gr Nn Gn Nt Gt Nres Gres Range Target ArgValid Valid Program
 FreeGlobal TableGlobal HeadGlobal GroupGlobal RowsGlobal CountGlobal Base Bound OldBase OldBound G Row Count Next
 Hook1 Hook2 HookReturn Owned.
 assert (Values : V293_create_function_values_valid
 (V293_task_selector target) argv topv (V293_byteval p) idv bottomv sizev extv optv).
 { unfold V293_create_function_values_valid.
   destruct ArgValid as (Arg&Top&Opt). destruct Valid as (Value&Bottom&Id&Size&Ext&Options).
   repeat split;try assumption;try reflexivity. apply V293_byte_type;lia. }
 destruct(V293_create_call_prologue P retks ge caller M ir aux O op enabled si ci f
 table nesting reserved running sched hook tcb btask barg btop bp bi bb bz be bopt bs berr bc
 (V293_task_selector target) argv topv (V293_byteval p) idv bottomv sizev extv optv _
 Function ND Fresh Values Owned) as (Mi&Allocate&Allocated).
 assert (Layout : getaddr le=addresses) by apply V293_create_function_layout.
 assert (AddressND : NoDup(map fst addresses)).
 { unfold addresses,V293_create_local_addresses. cbn [map fst].
   eapply Permutation_NoDup;[ |exact ND].
   unfold V293_create_function_blocks.
   change (Permutation (btask :: barg :: btop :: bp :: bi :: bb :: bz :: be :: bopt :: bs :: berr :: bc :: nil) ((bp :: bs :: bc :: nil)++btask::(barg :: btop :: bopt :: bb :: bi :: bz :: be :: berr :: nil))).
   apply Permutation_cons_app. cbn [app].
   change (Permutation (barg :: btop :: bp :: bi :: bb :: bz :: be :: bopt :: bs :: berr :: bc :: nil) ((bp :: bs :: bc :: nil)++barg::(btop :: bopt :: bb :: bi :: bz :: be :: berr :: nil))).
   apply Permutation_cons_app. cbn [app].
   change (Permutation (btop :: bp :: bi :: bb :: bz :: be :: bopt :: bs :: berr :: bc :: nil) ((bp :: bs :: bc :: nil)++btop::(bopt :: bb :: bi :: bz :: be :: berr :: nil))).
   apply Permutation_cons_app. cbn [app].
   change (Permutation (bp :: bi :: bb :: bz :: be :: bopt :: bs :: berr :: bc :: nil) (nil++bp::(bs :: bc :: bopt :: bb :: bi :: bz :: be :: berr :: nil))).
   apply Permutation_cons_app. cbn [app].
   change (Permutation (bi :: bb :: bz :: be :: bopt :: bs :: berr :: bc :: nil) ((bs :: bc :: bopt :: bb :: nil)++bi::(bz :: be :: berr :: nil))).
   apply Permutation_cons_app. cbn [app].
   change (Permutation (bb :: bz :: be :: bopt :: bs :: berr :: bc :: nil) ((bs :: bc :: bopt :: nil)++bb::(bz :: be :: berr :: nil))).
   apply Permutation_cons_app. cbn [app].
   change (Permutation (bz :: be :: bopt :: bs :: berr :: bc :: nil) ((bs :: bc :: bopt :: nil)++bz::(be :: berr :: nil))).
   apply Permutation_cons_app. cbn [app].
   change (Permutation (be :: bopt :: bs :: berr :: bc :: nil) ((bs :: bc :: bopt :: nil)++be::(berr :: nil))).
   apply Permutation_cons_app. cbn [app].
   change (Permutation (bopt :: bs :: berr :: bc :: nil) ((bs :: bc :: nil)++bopt::(berr :: nil))).
   apply Permutation_cons_app. cbn [app].
   change (Permutation (bs :: berr :: bc :: nil) (nil++bs::(bc :: berr :: nil))).
   apply Permutation_cons_app. cbn [app].
   change (Permutation (berr :: bc :: nil) ((bc :: nil)++berr::nil)).
   apply Permutation_cons_app. cbn [app].
   change (Permutation (bc :: nil) (nil++bc::nil)).
   apply Permutation_cons_app. cbn [app].
   apply Permutation_refl. }
 assert (Bp : get le 101%Z=Some(bp,Tint8)).
 { unfold le,V293_create_function_env. repeat rewrite map_get_set' by discriminate;apply map_get_set. }
 assert (Bc : get le 109%Z=Some(bc,Tint32)).
 { unfold le,V293_create_function_env;apply map_get_set. }
 assert (ArgEnv : V293_stack_argument_env le 201%Z 202%Z 203%Z 204%Z btask barg btop bopt).
 { unfold V293_stack_argument_env,le,V293_create_function_env. repeat split;repeat rewrite map_get_set' by discriminate;apply map_get_set. }
 assert (Env : V293_create_TCB_env le 108%Z 205%Z 206%Z 207%Z 208%Z 209%Z bs bb bi bz be berr).
 { unfold V293_create_TCB_env,le,V293_create_function_env. repeat split;repeat rewrite map_get_set' by discriminate;apply map_get_set. }
 assert (BodyOwned : (ge,le,Mi,ir,aux,O,op) |= V293_rdy_raw_cells
 (V293_create_bridge_cells bp bn bc bt p Vundef Vnull
 btask barg btop bopt target argv topv optv bs bb bi bz be berr Vundef bottomv idv sizev extv Vundef)
 (V293_rdy_raw_cells (V293_create_TCB_support bf block base bh bg rows count bo obase present p next oldfields prev g r n back kept) Atrue)).
 { unfold V293_create_function_cells,V293_create_bridge_cells,V293_create_prefix_cells,
   V293_stack_argument_cells,V293_create_bridge_extra in Allocated |- *.
   cbn [app V293_rdy_raw_cells] in Allocated |- *. clear -Allocated. sep auto. }
 destruct(V293_OSTaskCreateExt_success_return_under_hooks
 P ks caller f body retks ge le Mi ir aux O op enabled si ci table 101%Z nesting 109%Z reserved bp bn bc bt br p Vundef
 108%Z hook 201%Z 202%Z 203%Z 204%Z btask barg btop bopt target argv topv optv
 209%Z tcb 205%Z 206%Z 207%Z 208%Z bs bb bi bz be berr Vundef bottomv idv sizev extv Vundef value
 hi hc bf block base bh bg rows count bo obase present next oldfields prev g r n back frame running sched brun
 Layout AddressND eq_refl Away Nr Gr Bp Bc Nn Gn Nt Gt Nres Gres Range Target ArgEnv ArgValid Env Valid
 Program FreeGlobal TableGlobal HeadGlobal GroupGlobal RowsGlobal CountGlobal Base Bound OldBase OldBound G Row Count Next
 Hook1 Hook2 HookReturn BodyOwned)
 as (Mbridge&b1&b2&b3&b4&b5&b6&b7&b8&b9&Mf&Mr&TCBND&TCBFresh&Prefix&Exec&Final&TCBRemoved&Removed&Outside).
 exists Mbridge. exists b1. exists b2. exists b3. exists b4. exists b5. exists b6. exists b7. exists b8. exists b9. exists Mf. exists Mr.
 split;[exact TCBND| ]. split;[exact TCBFresh| ]. split.
 - eapply V293_local_trans;[exact Allocate|exact Prefix].
 - split.
   + eapply V293_local_trans;[exact Allocate|exact Exec].
   + split;[exact Final| ]. split;[exact TCBRemoved| ]. split;assumption.
Qed.
Print Assumptions V293_OSTaskCreateExt_success_call_under_hooks.
