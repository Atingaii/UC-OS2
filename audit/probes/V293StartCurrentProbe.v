(* The literal memory is reused, not an assumed execution or current task.
   The new production call uses reserved OSTCBCur=60. The alias ablation
   separately keeps the old current=107 program identical in both arms. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSStart.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.proofs.V293Start.
Require Import CertiOS.certiucos.v293.proofs.V293StartCurrent.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBClear.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.audit.probes.V293StartProbe.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition CurrentGE : env := set StartGE OSTCBCur (84%positive,Tptr V293_tcb_type).
Definition CurrentBody := V293_OSStart_body 108%Z 901%Z 105%Z 103%Z 109%Z 106%Z OSTCBCur 902%Z.
Definition CurrentProgram : progunit := fun f=>
 if Z.eqb f 900 then Some (V293_OSStart_function 108%Z 901%Z 105%Z 103%Z 109%Z 106%Z OSTCBCur 902%Z)
 else if Z.eqb f 901 then Some (V293_OSSchedNew_function 100%Z 101%Z 102%Z 103%Z 104%Z) else None.
Definition CurrentState M : RstateOP :=
 (CurrentGE,(emp:env),M,(fun _=>false),(false,nil,nil),StartAbs,spec_done None).
Definition CurrentOthers := V293_start_other_cells 81%positive 82%positive 83%positive
  85%positive 86%positive 12 StartTarget StartFrame.

Theorem CurrentLiteralEntry :
 CurrentState (StartMem (StartCells false)) |= V293_rdy_raw_cells (StartCells false) Atrue.
Proof.
 eapply V293_raw_cells_environment;[right;reflexivity | exact (StartLiteralEntry false)].
Qed.

Theorem CurrentNoInitialTask : forall t,
 ~ CurrentState (StartMem (StartCells false)) |= CurTid t ** Atrue.
Proof.
 intros t Held.
 destruct (V293_shared_current_read _ _ _ _ _ _ _ _ _ Held) as (b&tp&Binding&Read).
 change (Some (84%positive,Tptr V293_tcb_type)=Some (b,Tptr tp)) in Binding.
 inversion Binding;subst b tp.
 assert (Null : load (Tptr V293_tcb_type) (StartMem (StartCells false)) (84%positive,0%Z)=Some Vnull).
 { eapply V293_start_owned_load;[ | |exact (StartLiteralEntry false)];
   [unfold StartCells,V293_start_cells;do 3 right;left;reflexivity | reflexivity]. }
 change (load (Tptr V293_tcb_type) (StartMem (StartCells false)) (84%positive,0%Z)=Some(Vptr t)) in Read.
 congruence.
Qed.

Theorem CurrentColdCall : exists Mf,
 cstepstar CurrentProgram (curs (scall 900%Z nil),(kenil,kstop))
 (CurrentGE,StartCaller,StartMem (StartCells false))
 (curs (sfexec 902%Z nil nil),(kenil,kseq sret (kcall 900%Z CurrentBody StartCaller kstop)))
 (CurrentGE,(emp:env),Mf) /\
 CurrentState Mf |= CurTid StartTarget ** CurTid StartTarget ** V293_rdy_raw_cells CurrentOthers Atrue.
Proof.
 eapply (V293_OSStart_call_establishes_current StartFrame CurrentProgram kstop CurrentGE StartCaller
  (StartMem (StartCells false)) (fun _=>false) (false,nil,nil) StartAbs (spec_done None)
  900%Z 108%Z 901%Z 105%Z 103%Z 109%Z 106%Z 902%Z
  100%Z 101%Z 102%Z 104%Z 85%positive 82%positive 81%positive 86%positive
  83%positive 84%positive 1%positive 2%positive 3%positive 0 16
  (Vint32(Int.repr 7)) (Vint32(Int.repr 8)) Vnull Vnull StartTarget);
 try reflexivity;try lia.
 - exact StartNonempty.
 - apply StartInputReads.
 - exact CurrentLiteralEntry.
Qed.

Theorem CurrentHighestCall : exists target message Mf,
 get StartTasks target=Some(Int.repr 12,rdy,message) /\ V293_scheduler StartAbs target /\
 cstepstar CurrentProgram (curs (scall 900%Z nil),(kenil,kstop))
 (CurrentGE,StartCaller,StartMem (StartCells false))
 (curs (sfexec 902%Z nil nil),(kenil,kseq sret (kcall 900%Z CurrentBody StartCaller kstop)))
 (CurrentGE,(emp:env),Mf) /\
 CurrentState Mf |= CurTid target ** CurTid target **
 V293_rdy_raw_cells (V293_start_other_cells 81%positive 82%positive 83%positive
   85%positive 86%positive 12 target StartFrame) Atrue.
Proof.
 eapply (V293_OSStart_highest_establishes_current StartEntries StartTasks StartFrame CurrentProgram
  kstop CurrentGE StartCaller (StartMem (StartCells false)) (fun _=>false) (false,nil,nil)
  StartAbs (spec_done None) 900%Z 108%Z 901%Z 105%Z 103%Z 109%Z 106%Z 902%Z
  100%Z 101%Z 102%Z 104%Z 85%positive 82%positive 81%positive 86%positive
  83%positive 84%positive 1%positive 2%positive 3%positive 0 16
  (Vint32(Int.repr 7)) (Vint32(Int.repr 8)) Vnull Vnull);
 try reflexivity;try lia.
 - exact StartNonempty.
 - exact StartBitmap.
 - exact StartTable.
 - apply StartInputReads.
 - exact CurrentLiteralEntry.
Qed.

Theorem CurrentPortMissing : CurrentProgram 902%Z=None.
Proof. reflexivity. Qed.

(* Single-factor binding experiment: identical program and initial memory. *)
Theorem CurrentAliasCall : exists Mf,
 cstepstar StartProgram (curs (scall 900%Z nil),(kenil,kstop))
 (CurrentGE,StartCaller,StartMem (StartCells false))
 (curs (sfexec 902%Z nil nil),(kenil,kseq sret (kcall 900%Z StartBody StartCaller kstop)))
 (CurrentGE,(emp:env),Mf) /\
 CurrentState Mf |= CurTid StartTarget ** CurTid StartTarget ** V293_rdy_raw_cells CurrentOthers Atrue.
Proof.
 destruct (V293_OSStart_call_to_port StartFrame StartProgram kstop CurrentGE StartCaller
  (StartMem (StartCells false)) (fun _=>false) (false,nil,nil) StartAbs (spec_done None)
  900%Z 108%Z 901%Z 105%Z 103%Z 109%Z 106%Z 107%Z 902%Z
  100%Z 101%Z 102%Z 104%Z 85%positive 82%positive 81%positive 86%positive
  83%positive 84%positive 1%positive 2%positive 3%positive 0 16
  (Vint32(Int.repr 7)) (Vint32(Int.repr 8)) Vnull Vnull StartTarget)
 as (Mf&Exec&Final);try reflexivity;try lia.
 - exact StartNonempty.
 - apply StartInputReads.
 - exact CurrentLiteralEntry.
 - exists Mf. split;[exact Exec | ]. eapply V293_start_final_current;[reflexivity | exact Final].
Qed.

Theorem CurrentWithoutBinding : forall M t,
 ~ StartState M |= CurTid t ** Atrue.
Proof.
 intros M t Held.
 destruct (V293_shared_current_read _ _ _ _ _ _ _ _ _ Held) as (b&tp&Binding&Read).
 change (None=Some (b,Tptr tp)) in Binding. discriminate.
Qed.

Theorem CurrentDecoyCall : exists Mf,
 cstepstar StartProgram (curs (scall 900%Z nil),(kenil,kstop))
 (StartGE,StartCaller,StartMem (StartCells false))
 (curs (sfexec 902%Z nil nil),(kenil,kseq sret (kcall 900%Z StartBody StartCaller kstop)))
 (StartGE,(emp:env),Mf) /\ StartState Mf |= V293_rdy_raw_cells StartFinal Atrue /\
 (forall t, ~ StartState Mf |= CurTid t ** Atrue).
Proof.
 destruct StartColdCall as (Mf&Exec&Owned). exists Mf.
 split;[exact Exec | ]. split;[exact Owned | ]. apply CurrentWithoutBinding.
Qed.

Theorem CurrentBindingOnlyFactor : forall name,
 name<>OSTCBCur -> get CurrentGE name=get StartGE name.
Proof. intros name Different. unfold CurrentGE. apply map_get_set';congruence. Qed.

Theorem CurrentPostReads : forall M,
 CurrentState M |= CurTid StartTarget ** CurTid StartTarget ** V293_rdy_raw_cells CurrentOthers Atrue ->
 load (Tptr V293_tcb_type) M (84%positive,0%Z)=Some(Vptr StartTarget) /\
 load Tint8 M (85%positive,0%Z)=Some(Vint32 Int.zero) /\
 load Tint32 M (99%positive,0%Z)=Some(Vint32(Int.repr 123)).
Proof.
 intros M Owned.
 assert (One : CurrentState M |= CurTid StartTarget ** Atrue) by (clear -Owned;sep auto).
 destruct (V293_shared_current_read _ _ _ _ _ _ _ _ _ One) as (b&tp&Binding&Read).
 change (Some (84%positive,Tptr V293_tcb_type)=Some (b,Tptr tp)) in Binding.
 inversion Binding;subst b tp.
 split;[exact Read | ].
 assert (Others : CurrentState M |= V293_rdy_raw_cells CurrentOthers Atrue ** Atrue)
   by (clear -Owned;sep auto).
 split.
 - change (load Tint8 (getmem (CurrentState M)) (85%positive,0%Z)=Some(Vint32 Int.zero)).
   eapply V293_star_load_l;[ | exact Others]. intros st HS.
   eapply V293_rdy_raw_load;[ | reflexivity | exact HS].
   unfold CurrentOthers,V293_start_other_cells,StartFrame;simpl;tauto.
 - change (load Tint32 (getmem (CurrentState M)) (99%positive,0%Z)=Some(Vint32(Int.repr 123))).
   eapply V293_star_load_l;[ | exact Others]. intros st HS.
   eapply V293_rdy_raw_load;[ | reflexivity | exact HS].
   unfold CurrentOthers,V293_start_other_cells,StartFrame;simpl;tauto.
Qed.

Theorem CurrentSameMf : exists Mf,
 cstepstar CurrentProgram (curs (scall 900%Z nil),(kenil,kstop))
 (CurrentGE,StartCaller,StartMem (StartCells false))
 (curs (sfexec 902%Z nil nil),(kenil,kseq sret (kcall 900%Z CurrentBody StartCaller kstop)))
 (CurrentGE,(emp:env),Mf) /\
 (CurrentState Mf |= CurTid StartTarget ** CurTid StartTarget ** V293_rdy_raw_cells CurrentOthers Atrue) /\
 load (Tptr V293_tcb_type) Mf (84%positive,0%Z)=Some(Vptr StartTarget) /\
 load Tint8 Mf (85%positive,0%Z)=Some(Vint32 Int.zero) /\
 load Tint32 Mf (99%positive,0%Z)=Some(Vint32(Int.repr 123)).
Proof.
 destruct CurrentColdCall as (Mf&Exec&Owned). exists Mf.
 split;[exact Exec | ]. split;[exact Owned | ]. apply CurrentPostReads;exact Owned.
Qed.

Print Assumptions CurrentNoInitialTask.
Print Assumptions CurrentColdCall.
Print Assumptions CurrentHighestCall.
Print Assumptions CurrentAliasCall.
Print Assumptions CurrentDecoyCall.
Print Assumptions CurrentPostReads.
Print Assumptions CurrentSameMf.
