Require Import CertiOS.certiucos.v293.code.V293OSIntExit.
Require Import CertiOS.certiucos.v293.code.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFieldsHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickDelayHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.framework.proof.soundness.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.
Definition V293_exit_cells := V293_interrupt_cells.
Definition V293_exit_depth (nest:nat) := Nat.pred nest.
Definition V293_exit_enabled nest lock := Nat.eqb(V293_exit_depth nest)0 && Nat.eqb lock 0.
Lemma V293_exit_positive : forall n,n<256 ->
 Int.ltu Int.zero (Int.repr(Z.of_nat n))=negb(Nat.eqb n 0).
Proof.
 intros n Hn. unfold Int.ltu.
 rewrite Int.unsigned_repr by(unfold Int.max_unsigned,Int.modulus,Int.wordsize;simpl;lia).
 change ((if zlt 0 (Z.of_nat n) then true else false)=negb(Nat.eqb n 0)).
 destruct n; [reflexivity| ]. simpl Nat.eqb. simpl negb.
 destruct(zlt 0 (Z.of_nat(S n)));[reflexivity|lia].
Qed.
Lemma V293_exit_byte_sub : forall n,0<n -> n<256 ->
 Int.modu (Int.sub (Int.repr(Z.of_nat n)) Int.one) (Int.repr Byte.modulus)=
 Int.repr(Z.of_nat(V293_exit_depth n)).
Proof.
 intros n P B. unfold Int.sub.
 rewrite Int.unsigned_repr by(unfold Int.max_unsigned,Int.modulus,Int.wordsize;simpl;lia).
 change (Int.modu(Int.repr(Z.of_nat n-1))(Int.repr 256)=Int.repr(Z.of_nat(V293_exit_depth n))).
 unfold Int.modu. rewrite !Int.unsigned_repr by(unfold Int.max_unsigned,Int.modulus,Int.wordsize;simpl;lia).
 change (Int.repr((Z.of_nat n-1) mod 256)=Int.repr(Z.of_nat(V293_exit_depth n))).
 rewrite Z.mod_small by lia. unfold V293_exit_depth. f_equal;lia.
Qed.
Lemma V293_exit_owned_eval : forall nesting lock bn bl nest locked R s,
 nest<256 -> locked<256 ->
 (forall st,st |= R -> V293_interrupt_env nesting lock bn bl (getgenv st)(getlenv st)) ->
 s |= V293_rdy_raw_cells(V293_exit_cells bn bl nest locked)R ->
 (evalval(V293_OSIntExit_positive nesting)(getsmem s)=
   Some(Vint32(if negb(Nat.eqb nest 0)then Int.one else Int.zero)) /\
  evaltype(V293_OSIntExit_positive nesting)(getsmem s)=Some Tint32) /\
 (evaladdr(evar nesting)(getsmem s)=Some(Vptr(bn,Int.zero)) /\
  evaltype(evar nesting)(getsmem s)=Some Tint8) /\
 (0<nest -> evalval(V293_OSIntExit_previous nesting)(getsmem s)=Some(V293_byteval(V293_exit_depth nest)) /\
  evaltype(V293_OSIntExit_previous nesting)(getsmem s)=Some Tint8) /\
 (evalval(V293_OSSched_zero nesting)(getsmem s)=Some(Vint32(if Nat.eqb nest 0 then Int.one else Int.zero)) /\
  evaltype(V293_OSSched_zero nesting)(getsmem s)=Some Tint32) /\
 (evalval(V293_OSSched_zero lock)(getsmem s)=Some(Vint32(if Nat.eqb locked 0 then Int.one else Int.zero)) /\
  evaltype(V293_OSSched_zero lock)(getsmem s)=Some Tint32).
Proof.
 intros nesting lock bn bl nest locked R s Hn Hl Env Owned.
 pose proof(V293_raw_cells_frame_env _ _ _ Env _ Owned)as(Nn&Gn&Nl&Gl).
 assert(Ln:load Tint8(getmem s)(bn,0%Z)=Some(V293_byteval nest)).
 { eapply(V293_rdy_raw_load(V293_exit_cells bn bl nest locked)R _ _ _ s);
   [cbn[V293_exit_cells V293_interrupt_cells In];tauto|apply V293_byte_type;exact Hn|exact Owned]. }
 assert(Ll:load Tint8(getmem s)(bl,0%Z)=Some(V293_byteval locked)).
 { eapply(V293_rdy_raw_load(V293_exit_cells bn bl nest locked)R _ _ _ s);
   [cbn[V293_exit_cells V293_interrupt_cells In];tauto|apply V293_byte_type;exact Hl|exact Owned]. }
 destruct s as [[[[[[ge le] M] ir] aux] O] op].
 cbn[getgenv getlenv getmem get_smem get_genv get_lenv get_mem]in Nn,Gn,Nl,Gl,Ln,Ll.
 unfold V293_OSIntExit_positive,V293_OSIntExit_previous,V293_OSSched_zero.
 cbn[getsmem get_smem evalval evaltype evaladdr get_lenv get_genv].
 rewrite Nn,Nl,Gn,Gl. cbn -[load]. rewrite Ln,Ll. unfold V293_byteval.
 cbn[cast_eval bop_eval val_eq bop_type cmp_val cmpu].
 rewrite V293_exit_positive by exact Hn.
 rewrite !V293_guard_eq_zero by assumption.
 repeat split;try (destruct(negb(Nat.eqb nest 0));reflexivity);
 try(destruct(Nat.eqb nest 0);reflexivity);try(destruct(Nat.eqb locked 0);reflexivity).
 change (Some(Vint32(Int.modu(Int.sub(Int.repr(Z.of_nat nest))Int.one)(Int.repr Byte.modulus)))=
  Some(Vint32(Int.repr(Z.of_nat(V293_exit_depth nest))))).
 rewrite V293_exit_byte_sub by assumption. reflexivity.
Qed.

Theorem V293_OSIntExit_decrement_hoare : forall Spec sd li I r ri tid aop nesting lock bn bl nest locked R,
 nest<256 -> locked<256 ->
 (forall st,st |= R -> V293_interrupt_env nesting lock bn bl(getgenv st)(getlenv st)) ->
 (R ==> CurLINV li tid) ->
 InfRules Spec sd li I r ri
 (<||aop||> ** V293_rdy_raw_cells(V293_exit_cells bn bl nest locked)R)
 (V293_OSIntExit_decrement nesting)
 (<||aop||> ** V293_rdy_raw_cells(V293_exit_cells bn bl(V293_exit_depth nest)locked)R)tid.
Proof.
 intros Spec sd li I r ri tid aop nesting lock bn bl nest locked R Hn Hl Env Linv.
 unfold V293_OSIntExit_decrement.
 eapply V293_tick_known_ift_hoare with(flag:=negb(Nat.eqb nest 0)).
 - intros s HS. apply astar_l_aop'_elim in HS as[_ Owned].
   destruct(V293_exit_owned_eval _ _ _ _ _ _ _ s Hn Hl Env Owned)as[[V T] Rest].
   split;[exact V|split;[exact T|discriminate]].
 - destruct nest as [ | n]; [intros s HS;exact HS| ].
   change(InfRules Spec sd li I r ri
    (<||aop||> ** V293_rdy_raw_cells([]++((bn,0%Z),Tint8,V293_byteval(S n))::[((bl,0%Z),Tint8,V293_byteval locked)])R)
    (sassign(evar nesting)(V293_OSIntExit_previous nesting))
    (<||aop||> ** V293_rdy_raw_cells([]++((bn,0%Z),Tint8,V293_byteval n)::[((bl,0%Z),Tint8,V293_byteval locked)])R)tid).
   eapply V293_raw_assign_hoare with(rt:=Tint8).
   + reflexivity.
   + apply eq_int;auto.
   + intros s Owned. destruct(V293_exit_owned_eval _ _ _ _ _ _ _ s Hn Hl Env Owned)as[_ [[A T] [Prev Rest]]].
     destruct(Prev ltac:(lia))as[V TV]. split;[split;assumption|split;[exact V|split;[exact TV|discriminate]]].
   + exact Linv.
Qed.

(* Both source branches are retained; the empty trace branch really steps. *)
Lemma V293_exit_known_if : forall Spec sd li I r ri tid p q e yes no(flag:bool),
 (p ==> Rv e @ Tint32 == Vint32(if flag then Int.one else Int.zero)) ->
 InfRules Spec sd li I r ri p (if flag then yes else no)q tid ->
 InfRules Spec sd li I r ri p(sif e yes no)q tid.
Proof.
 intros Spec sd li I r ri tid p q e yes no flag Eval Branch.
 eapply if_rule with(tp:=Tint32).
 - intros s HS. eexists;apply Eval;exact HS.
 - destruct flag.
   + eapply conseq_rule;[intros s[HS _];exact HS|intros s HS;exact HS|exact Branch].
   + eapply conseq_rule with(p:=Afalse);[ |intros s HS;exact HS|apply pfalse_rule].
     intros s[HS[v[V B]]]. destruct(Eval s HS)as[E _]. rewrite E in V. inversion V;subst v. discriminate B.
 - destruct flag.
   + eapply conseq_rule with(p:=Afalse);[ |intros s HS;exact HS|apply pfalse_rule].
     intros s[HS[v[V B]]]. destruct(Eval s HS)as[E _]. rewrite E in V. inversion V;subst v. discriminate B.
   + eapply conseq_rule;[intros s[HS _];exact HS|intros s HS;exact HS|exact Branch].
Qed.

(* The dispatch premise is required only on the actual enabled branch. It is
   not a proof of the CPU hook, interrupt return, or the whole function. *)
Theorem V293_OSIntExit_nesting_dispatch_hoare : forall Spec sd li I r ri tid aop
 nesting lock bn bl nest locked R dispatch q,
 nest<256 -> locked<256 ->
 (forall st,st |= R -> V293_interrupt_env nesting lock bn bl(getgenv st)(getlenv st)) ->
 (R ==> CurLINV li tid) ->
 (V293_exit_depth nest=0 -> locked=0 ->
  InfRules Spec sd li I r ri
   (<||aop||> ** V293_rdy_raw_cells(V293_exit_cells bn bl(V293_exit_depth nest)locked)R) dispatch q tid) ->
 InfRules Spec sd li I r ri
 (<||aop||> ** V293_rdy_raw_cells(V293_exit_cells bn bl nest locked)R)
 (V293_OSIntExit_nesting_dispatch nesting lock dispatch)
 (if V293_exit_enabled nest locked then q else
  <||aop||> ** V293_rdy_raw_cells(V293_exit_cells bn bl(V293_exit_depth nest)locked)R)tid.
Proof.
 intros Spec sd li I r ri tid aop nesting lock bn bl nest locked R dispatch q Hn Hl Env Linv Dispatch.
 unfold V293_OSIntExit_nesting_dispatch.
 eapply seq_rule with(p':=<||aop||> ** V293_rdy_raw_cells(V293_exit_cells bn bl(V293_exit_depth nest)locked)R).
 - eapply V293_OSIntExit_decrement_hoare; eassumption.
 - assert(B:V293_exit_depth nest<256)by(unfold V293_exit_depth;lia).
   assert(E:forall s,s |= <||aop||> ** V293_rdy_raw_cells(V293_exit_cells bn bl(V293_exit_depth nest)locked)R ->
    (s |= Rv(V293_OSSched_zero nesting)@Tint32==Vint32(if Nat.eqb(V293_exit_depth nest)0 then Int.one else Int.zero)) /\
    (s |= Rv(V293_OSSched_zero lock)@Tint32==Vint32(if Nat.eqb locked 0 then Int.one else Int.zero))).
   { intros s HS. apply astar_l_aop'_elim in HS as[_ Owned].
     destruct(V293_exit_owned_eval _ _ _ _ _ _ _ s B Hl Env Owned)as[_ [_ [_ [[N NT][L LT]]]]].
     split;split;[exact N|split;[exact NT|discriminate]|exact L|split;[exact LT|discriminate]]. }
   unfold V293_OSIntExit_guards,V293_exit_enabled.
   eapply V293_exit_known_if with(flag:=Nat.eqb(V293_exit_depth nest)0).
   + intros s HS;exact(proj1(E s HS)).
   + destruct(Nat.eqb(V293_exit_depth nest)0)eqn:En;[ |apply skip_rule].
     eapply V293_exit_known_if with(flag:=Nat.eqb locked 0).
     * intros s HS;exact(proj2(E s HS)).
     * destruct(Nat.eqb locked 0)eqn:El;[ |apply skip_rule].
       apply Dispatch;apply Nat.eqb_eq;assumption.
Qed.

Lemma V293_exit_enabled_iff : forall nest locked,
 V293_exit_enabled nest locked=true <-> nest<=1 /\ locked=0.
Proof.
 intros nest locked. unfold V293_exit_enabled,V293_exit_depth.
 rewrite Bool.andb_true_iff,!Nat.eqb_eq. lia.
Qed.
Theorem V293_OSIntExit_disabled_hoare : forall Spec sd li I r ri tid aop
 nesting lock bn bl nest locked R dispatch,
 nest<256 -> locked<256 -> (2<=nest \/ 0<locked) ->
 (forall st,st |= R -> V293_interrupt_env nesting lock bn bl(getgenv st)(getlenv st)) ->
 (R ==> CurLINV li tid) ->
 InfRules Spec sd li I r ri
 (<||aop||> ** V293_rdy_raw_cells(V293_exit_cells bn bl nest locked)R)
 (V293_OSIntExit_nesting_dispatch nesting lock dispatch)
 (<||aop||> ** V293_rdy_raw_cells(V293_exit_cells bn bl(V293_exit_depth nest)locked)R)tid.
Proof.
 intros Spec sd li I r ri tid aop nesting lock bn bl nest locked R dispatch Hn Hl Off Env Linv.
 assert(E:V293_exit_enabled nest locked=false).
 { destruct(V293_exit_enabled nest locked)eqn:E;[ |reflexivity].
   apply V293_exit_enabled_iff in E. lia. }
 pose proof(V293_OSIntExit_nesting_dispatch_hoare Spec sd li I r ri tid aop
  nesting lock bn bl nest locked R dispatch Afalse Hn Hl Env Linv)as H.
 rewrite E in H. apply H. intros N L. exfalso. unfold V293_exit_depth in N;lia.
Qed.
Theorem V293_OSIntExit_nesting_dispatch_semantics : forall Spec sd li I r ri tid aop
 nesting lock bn bl nest locked R dispatch q,
 nest<256 -> locked<256 ->
 (forall st,st |= R -> V293_interrupt_env nesting lock bn bl(getgenv st)(getlenv st)) ->
 (R ==> CurLINV li tid) ->
 (V293_exit_depth nest=0 -> locked=0 ->
  InfRules Spec sd li I r ri
   (<||aop||> ** V293_rdy_raw_cells(V293_exit_cells bn bl(V293_exit_depth nest)locked)R) dispatch q tid) ->
 simulation.RuleSem Spec sd li I r ri
 (<||aop||> ** V293_rdy_raw_cells(V293_exit_cells bn bl nest locked)R)
 (V293_OSIntExit_nesting_dispatch nesting lock dispatch)
 (if V293_exit_enabled nest locked then q else
  <||aop||> ** V293_rdy_raw_cells(V293_exit_cells bn bl(V293_exit_depth nest)locked)R)tid.
Proof. intros. apply RuleSound. eapply V293_OSIntExit_nesting_dispatch_hoare; eassumption. Qed.
