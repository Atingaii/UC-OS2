(* Inline the two exact code/spec entries, rather than checking names alone. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeSourceAPI.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.
Require Import CertiOS.certiucos.v293.proofs.V293TimeGetAPI.
Require Import CertiOS.certiucos.v293.proofs.V293TimeSetAPI.
Require Import CertiOS.certiucos.v293.proofs.V293TimeShared.
Require Import CertiOS.certiucos.v293.proofs.V293TimeSharedSet.
Require Import CertiOS.certiucos.v293.proofs.V293TimeNamesGood.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.framework.include_frm.
Local Open Scope Z_scope.

Theorem TSchecked_component : forall fget fset now ticks saved bn Spec lg,
  fget <> fset -> ticks <> saved -> now <> ticks -> now <> saved ->
  GoodI (V293_time_shared_inv bn) V293_scheduler (V293_time_names_li now bn) /\
  APIRule
    (fun f => if Z.eq_dec f fget then
      Some (Tint32,dnil,dcons ticks Tint32 (dcons saved Tint32 dnil),
        sseq (sassign (evar saved) (econst32 Int.zero))
          (sseq (sseq (sprim encrit)
            (sseq (sassign (evar ticks) (evar now)) (sprim excrit)))
            (srete (evar ticks))))
      else if Z.eq_dec f fset then
      Some (Tvoid,dcons ticks Tint32 dnil,dcons saved Tint32 dnil,
        sseq (sassign (evar saved) (econst32 Int.zero))
          (sseq (sseq (sprim encrit)
            (sseq (sassign (evar now) (evar ticks)) (sprim excrit))) sret))
      else None)
    (fun f => if Z.eq_dec f fget then Some (fun _ => V293_time_get_action,(Tint32,nil))
      else if Z.eq_dec f fset then
      Some (fun vl => match vl with
        | (Vint32 n)::nil => spec_prim (Vint32 n::nil) V293_time_set_step
        | _ => END None end,(Tvoid,Tint32::nil))
      else None)
    Spec V293_scheduler (V293_time_names_li now bn) (V293_time_shared_inv bn) lg.
Proof. exact V293_source_time_coherent. Qed.

Theorem TSbuilders_nonempty : forall n li tid lg,
  (exists pre post,
    Some pre = BuildPreA' (V293_source_time_program 11 12 41 42 43) 11
      V293_TimeGet_api nil li tid lg /\
    Some post = BuildRetA' (V293_source_time_program 11 12 41 42 43) 11
      V293_TimeGet_api nil li tid lg) /\
  (exists pre post,
    Some pre = BuildPreA' (V293_source_time_program 11 12 41 42 43) 12
      V293_TimeSet_api (Vint32 n::nil) li tid lg /\
    Some post = BuildRetA' (V293_source_time_program 11 12 41 42 43) 12
      V293_TimeSet_api (Vint32 n::nil) li tid lg).
Proof.
  intros. split;unfold BuildPreA',BuildRetA',V293_source_time_program;
    cbn; eexists;eexists;split;reflexivity.
Qed.
