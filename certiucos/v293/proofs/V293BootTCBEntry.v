(* The original initializer's exact bytes supply the first TCB call.
   No running-task invariant or Hook-return premise is used. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBFinitePool.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBCall.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBList.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBClear.
Require Import CertiOS.certiucos.v293.proofs.V293NullBytes.
Require Import CertiOS.certiucos.v293.proofs.V293MemClr.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitPrefix.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope Z_scope.

Definition V293_boot_tcb_old (delta:Z) : val :=
 if in_dec Z.eq_dec delta [0;4;8;28;32;36] then Vnull else Vint32 Int.zero.
Definition V293_boot_tcb_spares b base : list V293_record_cell :=
 [((b,base+24),Tcom_ptr 410,Vnull);((b,base+40),Tint16,Vint32 Int.zero);
  ((b,base+42),Tint8,Vint32 Int.zero);((b,base+43),Tint8,Vint32 Int.zero)].

Lemma V293_boot_zero_payload_fields : forall b base R,
 V293_rdy_raw_cells
 (V293_clr_bytes b base(repeat(Vint32 Int.zero)20)++
  V293_clr_bytes b(base+24)(repeat(Vint32 Int.zero)32))R ==>
 V293_rdy_raw_cells(V293_tcb_init_old_fields b base V293_boot_tcb_old++
  V293_boot_tcb_spares b base)R.
Proof.
 intros b base R s H. rewrite V293_raw_cells_append in H.
 pose proof(V293_init_zero_run_fold
 (Tptr Tint32::Tptr Tvoid::Tptr Tint32::Tint32::Tint16::Tint16::nil)
 b base _ ltac:(repeat constructor;reflexivity) s H)as K.
 assert(Tail:V293_rdy_raw_cells(V293_clr_bytes b(base+24)(repeat(Vint32 Int.zero)32))R ==>
 V293_rdy_raw_cells(V293_init_zero_run b(base+24)
 (Tcom_ptr 410::Tcom_ptr 411::Tptr Tvoid::Tcom_ptr 412::Tint16::Tint8::Tint8::Tint32::
  Tint8::Tint8::Tint8::Tint8::Tint8::Tint8::Tint8::Tint8::nil))R).
 { exact(V293_init_zero_run_fold
   (Tcom_ptr 410::Tcom_ptr 411::Tptr Tvoid::Tcom_ptr 412::Tint16::Tint8::Tint8::Tint32::
    Tint8::Tint8::Tint8::Tint8::Tint8::Tint8::Tint8::Tint8::nil)
   b(base+24)R ltac:(repeat constructor;reflexivity)). }
 pose proof(V293_raw_cells_mono _ _ _ Tail s K)as J.
 cbn[V293_init_zero_run V293_init_zero_value typelen Z.of_nat]in J.
 repeat rewrite <-Z.add_assoc in J. cbn[Z.add]in J.
 unfold V293_tcb_init_old_fields,V293_boot_tcb_spares,V293_boot_tcb_old.
 cbn[in_dec Z.eq_dec V293_rdy_raw_cells app]in J|-*.
 rewrite Z.add_0_r. clear -J;sep auto.
Qed.

(* All twelve unallocated records, all priority slots and all caller bytes
   remain explicit; only the first record's payload is retyped. *)
Definition V293_boot_tcb_frame bh bt bp frame :=
 V293_boot_tcb_spares bt 0++
 [((bh,0),Tptr V293_tcb_type,Vnull)]++
 tl(V293_tcb_linked_next bt)++V293_tcb_untouched_cells bt 56 12++
 V293_null_pointer_cells bp 0 13++frame.
Lemma V293_boot_first_tcb_entry : forall bh bf bt bp frame,
 V293_rdy_raw_cells(V293_tcb_call_result bh bf bt bp frame)Atrue ==>
 V293_rdy_raw_cells
 (V293_tcb_init_old_fields bt 0 V293_boot_tcb_old++
  V293_tcb_prefix_links bf bt 0(Vptr(bt,Int.zero))(Vptr(bt,Int.repr 56))++
  V293_boot_tcb_frame bh bt bp frame)Atrue.
Proof.
 intros bh bf bt bp frame s H.
 set(rest:=V293_rdy_raw_cells(tl(V293_tcb_linked_next bt))
  (V293_rdy_raw_cells(V293_tcb_untouched_cells bt 56 12)
   (V293_rdy_raw_cells(V293_null_pointer_cells bp 0 13++frame)Atrue))).
 assert(K:s |= Amapsto(bh,0)(Tptr V293_tcb_type)true Vnull **
  (Amapsto(bf,0)(Tptr V293_tcb_type)true(Vptr(bt,Int.zero)) **
   (Amapsto(bt,20)(Tcom_ptr 410)true(Vptr(bt,Int.repr 56)) **
    V293_rdy_raw_cells
     (V293_clr_bytes bt 0(repeat(Vint32 Int.zero)20)++
      V293_clr_bytes bt 24(repeat(Vint32 Int.zero)32))rest))).
 { unfold V293_tcb_call_result,V293_tcb_call_heads in H.
   repeat rewrite V293_raw_cells_append in H.
   change(s |= Amapsto(bh,0)(Tptr V293_tcb_type)true Vnull **
    (Amapsto(bf,0)(Tptr V293_tcb_type)true(Vptr(bt,Int.zero)) **
    (Amapsto(bt,20)(Tcom_ptr 410)true(Vptr(bt,Int.repr 56)) **
    V293_rdy_raw_cells(tl(V293_tcb_linked_next bt))
    (V293_rdy_raw_cells
     (V293_clr_bytes bt 0(repeat(Vint32 Int.zero)20)++
      V293_clr_bytes bt 24(repeat(Vint32 Int.zero)32))
     (V293_rdy_raw_cells(V293_tcb_untouched_cells bt 56 12)
      (V293_rdy_raw_cells(V293_null_pointer_cells bp 0 13++frame)Atrue))))))in H.
   eapply astar_mono;[intros st HS;exact HS| |exact H].
   apply astar_mono;[intros st HS;exact HS| ].
   apply astar_mono;[intros st HS;exact HS| ].
   unfold rest. apply V293_raw_cells_swap. }
 assert(J:s |= Amapsto(bh,0)(Tptr V293_tcb_type)true Vnull **
  (Amapsto(bf,0)(Tptr V293_tcb_type)true(Vptr(bt,Int.zero)) **
   (Amapsto(bt,20)(Tcom_ptr 410)true(Vptr(bt,Int.repr 56)) **
    V293_rdy_raw_cells(V293_tcb_init_old_fields bt 0 V293_boot_tcb_old++
     V293_boot_tcb_spares bt 0)rest))).
 { eapply astar_mono;[intros st HS;exact HS| |exact K].
   apply astar_mono;[intros st HS;exact HS| ].
   apply astar_mono;[intros st HS;exact HS| ].
   apply V293_boot_zero_payload_fields. }
 repeat rewrite V293_raw_cells_append in J|-*.
 unfold V293_tcb_prefix_links. cbn[V293_rdy_raw_cells].
 unfold V293_boot_tcb_frame. repeat rewrite V293_raw_cells_append.
 change(s |= V293_rdy_raw_cells(V293_tcb_init_old_fields bt 0 V293_boot_tcb_old)
  (Amapsto(bf,0)(Tptr V293_tcb_type)true(Vptr(bt,Int.zero)) **
  (Amapsto(bt,20)(Tcom_ptr 410)true(Vptr(bt,Int.repr 56)) **
  V293_rdy_raw_cells(V293_boot_tcb_spares bt 0)
  (Amapsto(bh,0)(Tptr V293_tcb_type)true Vnull ** rest)))).
 unfold V293_tcb_init_old_fields,V293_boot_tcb_spares in J|-*.
 cbn[V293_rdy_raw_cells]in J|-*. clear -J;sep auto.
Qed.
Print Assumptions V293_boot_zero_payload_fields.
Print Assumptions V293_boot_first_tcb_entry.
