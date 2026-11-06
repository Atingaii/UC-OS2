(* Original critical/guard wrapper, using the AST already present in
   V293CriticalReturn. The external macro abstraction remains explicit. *)
Require Import CertiOS.certiucos.v293.proofs.V293LocalGlobalTrace.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.code.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.code.V293OSSchedDispatch.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.framework.include_frm.
Require Import Coq.Lists.List Lia.
Local Open Scope nat_scope.

Definition V293_sched_control interrupt lock body :=
  sseq (sprim encrit)
    (sseq (V293_OSSched_guards interrupt lock body) (sseq (sprim excrit) sret)).

Lemma V293_sched_control_exact : forall saved interrupt lock schednew table high target current counter,
  V293_OSSched_success_body saved interrupt lock schednew table high target current counter =
  sseq (sassign (evar saved) (econst32 Int.zero))
    (V293_sched_control interrupt lock
      (sseq (V293_OSSched_unlocked_prefix schednew table high target)
        (V293_OSSched_change high current counter (sprim (switch target))))).
Proof. reflexivity. Qed.

(* Reads actual independent byte cells. No supplied evaluation oracle, and
   no callee/ready contract is needed when either source guard is nonzero. *)
Theorem V293_sched_control_enter : forall P ks ge le M ir enabled si ci
    interrupt lock bi bl ni nl body,
  ni<256 -> nl<256 ->
  get le interrupt=None -> get ge interrupt=Some (bi,Tint8) ->
  get le lock=None -> get ge lock=Some (bl,Tint8) ->
  load Tint8 M (bi,0%Z)=Some (V293_byteval ni) ->
  load Tint8 M (bl,0%Z)=Some (V293_byteval nl) ->
  V293_local_steps P (curs (V293_sched_control interrupt lock body),(kenil,ks))
    ((ge,le,M),ir,(enabled,si,ci))
    (curs (if Nat.eqb ni 0 && Nat.eqb nl 0 then body else sskip None),
      (kenil,kseq (sseq (sprim excrit) sret) ks))
    ((ge,le,M),ir,(false,si,enabled::ci)).
Proof.
  intros P ks ge le M ir enabled si ci interrupt lock bi bl ni nl body
    Ni Nl IN IG LN LG IL LL.
  pose proof (V293_success_global_byte_eq ge le M interrupt bi ni 0 Ni ltac:(lia) IN IG IL) as EI.
  pose proof (V293_success_global_byte_eq ge le M lock bl nl 0 Nl ltac:(lia) LN LG LL) as EL.
  change (evalval (V293_OSSched_zero interrupt) (ge,le,M)=
    Some (Vint32 (if Nat.eqb ni 0 then Int.one else Int.zero))) in EI.
  change (evalval (V293_OSSched_zero lock) (ge,le,M)=
    Some (Vint32 (if Nat.eqb nl 0 then Int.one else Int.zero))) in EL.
  unfold V293_sched_control.
  eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity | apply sseq_step]. }
  eapply V293_local_cons. { apply encrit_step; reflexivity. }
  eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity | apply sskip_step]. }
  eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity | apply sseq_step]. }
  unfold V293_OSSched_guards.
  eapply V293_local_trans.
  { apply V293_csteps_local. eapply V293_entry_if_select. exact EI. }
  destruct (Nat.eqb ni 0); cbn [andb].
  - apply V293_csteps_local. eapply V293_entry_if_select. exact EL.
  - apply V293_local_refl.
Qed.

(* Finishing a non-switch branch actually pops the caller's saved IE.
   Stop at the original sret, not a fabricated function return. *)
Theorem V293_sched_control_exit : forall P ks ge le M ir active saved si ci,
  V293_local_steps P
    (SKIP,(kenil,kseq (sseq (sprim excrit) sret) ks))
    ((ge,le,M),ir,(active,si,saved::ci))
    (curs sret,(kenil,ks)) ((ge,le,M),ir,(saved,si,ci)).
Proof.
  intros. eapply V293_local_cons.
  { apply ostc_step. eapply stmt_step; [reflexivity | apply sskip_step]. }
  eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity | apply sseq_step]. }
  eapply V293_local_cons. { apply excrit_step; reflexivity. }
  eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity | apply sskip_step]. }
  apply V293_local_refl.
Qed.

(* Only delete encrit: excrit is not automatically a no-op. This control
   measures a real pop and wrong IE restoration when an outer frame exists;
   with an empty original stack the very same endpoint has no loststep. *)
Theorem V293_missing_enter_control : forall P ks m ir enabled outer si ci,
  loststep P (curs (sprim excrit),(kenil,ks)) (m,ir,(enabled,si,outer::ci))
    (SKIP,(kenil,ks)) (m,ir,(outer,si,ci)) /\
  (enabled<>outer -> (outer,si,ci)<>(enabled,si,outer::ci)) /\
  ~ (exists C' st', loststep P (curs (sprim excrit),(kenil,ks))
      (m,ir,(enabled,si,nil)) C' st').
Proof.
  intros. split; [apply excrit_step; reflexivity | ]. split.
  - intros Different Equal. apply Different. congruence.
  - intros (C' & st' & Step). inversion Step; subst; try discriminate.
    match goal with H : cstep _ _ _ _ _ |- _ =>
      inversion H; subst; try discriminate
    end.
    all: match goal with E : (curs (sprim excrit),_) = (_,_) |- _ =>
      inversion E; subst; clear E end.
    + match goal with H : estep _ _ _ _ _ _ |- _ => inversion H end.
    + match goal with H : sstep _ _ _ _ _ _ _ |- _ => inversion H end.
Qed.

(* SWINV does not own the critical stack. Transport only that stack, leaving
   its IE=false, ISR map, interrupt stack, memory and abstract state fixed. *)
Lemma V293_ready_critical_stack : forall br bg bp ct R ge le M ir si ci ci' O op,
  GoodInvAsrt R ->
  (ge,le,M,ir,(false,si,ci),O,op) |= SWINVt (V293_ready_inv br bg bp) ct ** R ->
  (ge,le,M,ir,(false,si,ci'),O,op) |= SWINVt (V293_ready_inv br bg bp) ct ** R.
Proof.
  intros br bg bp ct R ge le M ir si ci ci' O op Good Held.
  apply sat_split in Held. destruct Held as (m1&m2&o1&o2&JM&JO&Inv&Rest).
  unfold SWINVt in Inv. apply sat_split in Inv.
  destruct Inv as (mf&mt&oflags&ot&JMI&JOI&Switch&Current).
  apply V293_ready_switch_open in Switch. apply sat_split in Switch.
  destruct Switch as (mflags&mc&ofl&oc&JMF&JOF&Flags&Core).
  apply sat_split'. exists m1. exists m2. exists o1. exists o2.
  split; [exact JM | ]. split; [exact JO | ]. split.
  - unfold SWINVt. apply sat_split'. exists mf. exists mt. exists oflags. exists ot.
    split; [exact JMI | ]. split; [exact JOI | ]. split; [ | exact Current].
    apply V293_ready_switch_close. apply sat_split'.
    exists mflags. exists mc. exists ofl. exists oc.
    split; [exact JMF | ]. split; [exact JOF | ]. split; [exact Flags | ].
    eapply V293_ready_core_aux; exact Core.
  - eapply good_inv_prop; [exact Good | exact Rest].
Qed.
