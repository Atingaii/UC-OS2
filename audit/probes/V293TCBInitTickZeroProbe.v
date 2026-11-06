(* Reuse the existing finite initializer entry, with no assumed successful
   execution. The separate candidate family tests only interface sufficiency. *)
Require Import CertiOS.audit.probes.V293TCBInitFieldsProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitTickZero.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293StartRecord.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBClear.
Require Import CertiOS.certiucos.v293.proofs.V293NullBytes.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickTraversal.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInit.
Require Import CertiOS.certiucos.v293.code.V293OSTimeTick.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.
Definition TZnext:=(501%positive,Int.repr 56).
Definition TZframe:=V293_rdy_raw_cells(tl InitFrame)Aemp.
Definition TZpost M:=InitState M |=
 V293_owned_record_cell((201%positive,0%Z),Tptr V293_tcb_type,Vptr TZnext) **
 (V293_tick_zero_node 301%positive 8 TZnext **
 (V293_owned_task_record(301%positive,Int.repr 8)(Int.repr 11)rdy Vnull **
 V293_rdy_raw_cells
 (V293_tcb_tick_spares 301%positive 8 (Vptr(401%positive,Int.repr 508))
  (Vptr(401%positive,Int.zero))(Vint32(Int.repr 65534))(Vint32(Int.repr 128))Vnull(Vint32(Int.repr 3)))
 (V293_rdy_raw_cells(tl(InitInputs 11))TZframe))).

Lemma TZentry : InitState(InitEntry 11) |=V293_rdy_raw_cells
 (InitOld++InitInputs 11)
 (V293_owned_record_cell((301%positive,28%Z),Tcom_ptr 410%Z,Vptr TZnext) **TZframe).
Proof.
 pose proof(InitLiteralEntry 11)as Held.
 rewrite V293_raw_cells_append in Held.
 rewrite V293_raw_cells_append in Held.
 rewrite V293_raw_cells_append.
 eapply V293_raw_cells_mono;[ |exact Held].
 apply V293_raw_cells_mono.
 intros s H;unfold InitFrame in H;cbn[V293_rdy_raw_cells]in H.
 unfold V293_owned_record_cell,TZframe;cbn[InitFrame tl V293_rdy_raw_cells].
 eapply astar_mono;[ |intros st HS;exact HS|exact H].
 intros st HS;apply astar_l_apure_intro;[exact HS|reflexivity].
Qed.

Theorem TZactual_init_then_tick : forall P ki kt,exists Mi Mf,
 cstepstar P(curs(V293_TCBInit_fields 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z 108%Z),(kenil,ki))
 ((emp:env),InitLE,InitEntry 11)(curs(sskip None),(kenil,ki))((emp:env),InitLE,Mi) /\
 load Tint32 Mi(301%positive,52%Z)=Some(Vint32 Int.zero) /\
 V293_local_steps P(curs(V293_tick_iteration 101%Z 900%Z 901%Z),(kenil,kt))
 (((emp:env),InitLE,Mi),(fun _:hid=>false),(false,nil,nil))
 (curs(sskip None),(kenil,kt))(((emp:env),InitLE,Mf),(fun _:hid=>false),(false,nil,nil)) /\
 store(Tptr V293_tcb_type)Mi(201%positive,0%Z)(Vptr TZnext)=Some Mf /\
 TZpost Mf /\
 load(Tptr V293_tcb_type)Mf(201%positive,0%Z)=Some(Vptr TZnext) /\
 (forall b i,b<>201%positive \/(i<0)%Z \/(4<=i)%Z ->get Mf(b,i)=get Mi(b,i)).
Proof.
 intros P ki kt.
 exact(V293_TCBInit_fields_then_zero_iteration P ki kt(emp:env)InitLE(InitEntry 11)
 (fun _:hid=>false)false nil nil(emp:osabst)(spec_done None)TZframe
 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z 108%Z 900%Z 901%Z
 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive 208%positive
 301%positive 8 11 (Vptr(401%positive,Int.repr 508))(Vptr(401%positive,Int.zero))
 (Vint32(Int.repr 65534))(Vint32(Int.repr 128))Vnull(Vint32(Int.repr 3))
 (fun _:Z=>Vundef)TZnext ltac:(lia)ltac:(lia)ltac:(change(8+55<=4294967295)%Z;lia)
 InitEnvironment(InitValues 11)TZentry).
Qed.

(* Only delay44 varies. No candidate is claimed to be a reachable initialized
   task; the positive execution above uses the original entry, not this family. *)
Definition TZcanonical:list V293_record_cell:=
 [((301%positive,58%Z),Tint8,V293_byteval 11);
  ((301%positive,60%Z),Tint8,V293_byteval 1);
  ((301%positive,59%Z),Tint8,V293_byteval 3);
  ((301%positive,62%Z),Tint8,V293_byteval 2);
  ((301%positive,61%Z),Tint8,V293_byteval 8);
  ((301%positive,40%Z),Tptr Tvoid,Vnull);
  ((301%positive,56%Z),Tint8,V293_byteval 0)].
Definition TZcells d:list V293_record_cell:=TZcanonical++
 [((301%positive,52%Z),Tint32,Vint32 d);
  ((301%positive,28%Z),Tcom_ptr 410%Z,Vptr TZnext);
  ((201%positive,0%Z),Tptr V293_tcb_type,Vptr(301%positive,Int.repr 8));
  ((601%positive,0%Z),Tint32,Vint32(Int.repr 77))].
Definition TZcandidate d:=InitMemory(TZcells d).
Definition TZcandidate_owned d:=
 V293_owned_task_record(301%positive,Int.repr 8)(Int.repr 11)rdy Vnull **
 (V293_owned_record_cell((301%positive,52%Z),Tint32,Vint32 d) **
 (V293_owned_record_cell((301%positive,28%Z),Tcom_ptr 410%Z,Vptr TZnext) **
 (V293_owned_record_cell((201%positive,0%Z),Tptr V293_tcb_type,Vptr(301%positive,Int.repr 8)) **
 V293_owned_record_cell((601%positive,0%Z),Tint32,Vint32(Int.repr 77))))).

Ltac TZoutside :=
  repeat first [rewrite V293_encoded_memory_outside by
    (first [left;congruence | right;cbn [length TZnext V293_byteval encode_val typelen list_repeat inj_pointer inj_bytes encode_int List.map];lia])
    | rewrite map_merge_semp by reflexivity];reflexivity.
Ltac TZapart b start count :=
  apply map_join_merge;apply map_disjoint;intros [other off];
  destruct (Pos.eq_dec other b) as [B|B];
  [subst other;destruct (Z_lt_dec off start) as [Low|Low];
    [left;apply V293_encoded_memory_outside;right;left;exact Low |
     destruct (Z_lt_dec off (start+count)) as [Inside|Outside];
     [right;left;TZoutside | left;apply V293_encoded_memory_outside;right;right;
       cbn [length TZnext V293_byteval encode_val typelen list_repeat inj_pointer inj_bytes encode_int List.map];lia]] |
   left;apply V293_encoded_memory_outside;left;exact B].

Lemma TZcandidate_literal : forall d,InitState(TZcandidate d) |=V293_rdy_raw_cells(TZcells d)Aemp.
Proof.
 intro d;unfold InitState,TZcandidate.
 cbn[TZcells TZcanonical app InitMemory V293_rdy_raw_cells].
 repeat match goal with
 |-V293_wstate _ _ (merge(V293_encoded_memory ?b ?off true ?bytes)_) |=_ =>
 let count:=eval cbn[length TZnext V293_byteval encode_val typelen list_repeat inj_pointer inj_bytes encode_int List.map] in (Z.of_nat(length bytes)) in
 eapply V293_wstate_star with(m1:=V293_encoded_memory b off true bytes);
 [TZapart b off count|split;[apply V293_encoded_memory_mapsto|reflexivity]| ]
 end.
 split;reflexivity.
Qed.

Lemma TZcandidate_valid : forall d,InitState(TZcandidate d) |=TZcandidate_owned d.
Proof.
 intro d;pose proof(TZcandidate_literal d)as Held.
 apply(V293_raw_record_ownership(TZcells d)Aemp ltac:(unfold TZcells,TZcanonical;repeat constructor;reflexivity))in Held.
 assert(Layout:TZcanonical=V293_record_layout(301%positive,Int.repr 8)11 rdy Vnull 0)by reflexivity.
 unfold TZcells in Held;rewrite Layout in Held.
 assert(Cells:InitState(TZcandidate d) |=
 V293_owned_record_cells(V293_record_layout(301%positive,Int.repr 8)11 rdy Vnull 0) **
 (V293_owned_record_cell((301%positive,52%Z),Tint32,Vint32 d) **
 (V293_owned_record_cell((301%positive,28%Z),Tcom_ptr 410%Z,Vptr TZnext) **
 (V293_owned_record_cell((201%positive,0%Z),Tptr V293_tcb_type,Vptr(301%positive,Int.repr 8)) **
 V293_owned_record_cell((601%positive,0%Z),Tint32,Vint32(Int.repr 77)))))).
 { cbn[V293_record_layout V293_owned_record_cells app fst snd]in Held|-*;clear -Held;sep auto. }
 unfold TZcandidate_owned;eapply astar_mono;[ |intros st HS;exact HS|exact Cells].
 intros st HS;exists 11;exists 0;apply astar_l_apure_intro;[exact HS|repeat split;try reflexivity;lia].
Qed.

Lemma TZcandidate_delay : forall d,load Tint32(TZcandidate d)(301%positive,52%Z)=Some(Vint32 d).
Proof.
 intro d;change(load Tint32(getmem(InitState(TZcandidate d)))(301%positive,52%Z)=Some(Vint32 d)).
 eapply V293_rdy_raw_load;[ |reflexivity|apply TZcandidate_literal].
 unfold TZcells;apply in_or_app;right;left;reflexivity.
Qed.

Theorem TZready_record_insufficient :
 InitState(TZcandidate(Int.repr 3)) |=TZcandidate_owned(Int.repr 3) /\
 ~(InitState(TZcandidate(Int.repr 3)) |=V293_tick_zero_node 301%positive 8 TZnext **Atrue).
Proof.
 split;[apply TZcandidate_valid| ].
 intro Held;unfold V293_tick_zero_node in Held.
 assert(Zero:load Tint32(TZcandidate(Int.repr 3))(301%positive,52%Z)=Some(Vint32 Int.zero)).
 { change(load Tint32(getmem(InitState(TZcandidate(Int.repr 3))))(301%positive,52%Z)=Some(Vint32 Int.zero)).
   eapply V293_record_star_load_l;[ |exact Held];eapply V293_record_star_load_l;apply V293_owned_record_cell_load. }
 rewrite TZcandidate_delay in Zero;discriminate.
Qed.

Theorem TZzero_gate_passes :
 InitState(TZcandidate Int.zero) |=TZcandidate_owned Int.zero /\
 InitState(TZcandidate Int.zero) |=V293_tick_zero_node 301%positive 8 TZnext **Atrue.
Proof.
 split;[apply TZcandidate_valid| ].
 pose proof(TZcandidate_valid Int.zero)as Held.
 unfold TZcandidate_owned,V293_tick_zero_node in *;clear -Held;sep auto.
Qed.

Lemma TZmerge_lookup : forall (left1 left2 right1 right2:mem) a,
 get left1 a=get left2 a ->get right1 a=get right2 a ->
 get(merge left1 right1)a=get(merge left2 right2)a.
Proof.
 intros left1 left2 right1 right2 a Left Right.
 rewrite !map_merge_semp by reflexivity;rewrite Left,Right;reflexivity.
Qed.

(* The complete finite memory differs only in the four bytes of delay44. *)
Theorem TZsingle_factor_outside : forall d1 d2 b i,
 b<>301%positive \/(i<52)%Z \/(56<=i)%Z ->
 get(TZcandidate d1)(b,i)=get(TZcandidate d2)(b,i).
Proof.
 intros d1 d2 b i Outside.
 unfold TZcandidate,TZcells,TZcanonical.
 cbn[app InitMemory].
 do 7(eapply TZmerge_lookup;[reflexivity| ]).
 eapply TZmerge_lookup;[ |reflexivity].
 transitivity(@None (bool*memval)).
 - apply V293_encoded_memory_outside.
   cbn[length encode_val inj_bytes encode_int];exact Outside.
 - symmetry;apply V293_encoded_memory_outside.
   cbn[length encode_val inj_bytes encode_int];exact Outside.
Qed.
