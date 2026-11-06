(* Preserve the existing strong core when extending names and allocating API
   locals. Context transport is not a machine transition or initialization. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeReadyAPI.
Require Import CertiOS.certiucos.v293.proofs.V293TimeReadyShared.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List.
Local Open Scope nat_scope.

Lemma V293_current_entry_context : forall t ge le M ir aux O op ge' le' ir' aux' op',
  get ge' OSTCBCur=get ge OSTCBCur ->
  (ge,le,M,ir,aux,O,op) |= CurTid t ->
  (ge',le',M,ir',aux',O,op') |= CurTid t.
Proof.
  intros t ge le M ir aux O op ge' le' ir' aux' op' Same [tp [b H]].
  apply sat_split in H. destruct H as (m1&m2&o1&o2&JM&JO&Name&Bytes).
  exists tp. exists b. apply sat_split'.
  exists m1. exists m2. exists o1. exists o2.
  split;[exact JM | ]. split;[exact JO | ]. split;[ | exact Bytes].
  destruct Name as [b' [GE [Address [EM EO]]]].
  exists b'. split;[ | repeat split;assumption].
  change (get ge' OSTCBCur=Some(b',Tptr tp)). rewrite Same. exact GE.
Qed.

Theorem V293_time_ready_entry_context : forall br bg bp bn ge le M ir aux O op
    ge' le' ir' aux' op',
  get ge' OSTCBCur=get ge OSTCBCur ->
  (ge,le,M,ir,aux,O,op) |= V293_time_ready_core br bg bp bn ->
  (ge',le',M,ir',aux',O,op') |= V293_time_ready_core br bg bp bn.
Proof.
  intros br bg bp bn ge le M ir aux O op ge' le' ir' aux' op' Same [n H].
  exists n. apply sat_split in H.
  destruct H as (m1&m2&o1&o2&JM&JO&Fields&Clock).
  apply sat_split'. exists m1. exists m2. exists o1. exists o2.
  split;[exact JM | ]. split;[exact JO | ]. split;[ | exact Clock].
  destruct Fields as [t [ts [es Fields]]]. exists t. exists ts. exists es.
  apply sat_split in Fields. destruct Fields as (ma&mb&oa&ob&JM'&JO'&Shared&Ready).
  apply sat_split'. exists ma. exists mb. exists oa. exists ob.
  split;[exact JM' | ]. split;[exact JO' | ]. split.
  - apply sat_split in Shared. destruct Shared as (mc&md&oc&od&JM''&JO''&Current&Abstract).
    apply sat_split'. exists mc. exists md. exists oc. exists od.
    split;[exact JM'' | ]. split;[exact JO'' | ]. split;[ | exact Abstract].
    eapply V293_current_entry_context;[exact Same | exact Current].
  - eapply V293_ready_payload_context;exact Ready.
Qed.

Theorem V293_time_ready_entry_halves : forall br bg bp bn t,
  SWINVt (V293_time_ready_inv br bg bp bn) t ==>
    V293_time_ready_core br bg bp bn ** CurTid t.
Proof.
  intros br bg bp bn t s H. unfold SWINVt in H.
  assert (Opened : s |= (V293_shared_flags ** V293_time_ready_switch_core br bg bp bn) ** CurTid t).
  { eapply astar_mono;[apply V293_time_ready_switch_open | intros st H0;exact H0 | exact H]. }
  assert (FlagsEmpty : V293_shared_flags ==> Aemp).
  { intros st Flags. unfold V293_shared_flags in Flags.
    apply astar_l_aemp_elim.
    eapply astar_mono with (P:=isrclr ** Aie false)(Q:=EX k : hid, ATopis k);[ | intros st0 [k [_ Empty]];exact Empty | exact Flags].
    intros st0 Two. apply astar_l_aemp_elim.
    eapply astar_mono with (P:=isrclr)(Q:=Aie false);[ | intros st1 [_ Empty];exact Empty | exact Two].
    intros st1 [r [Flag Clear]]. exact (proj2 Flag). }
  assert (Pack : s |= V293_shared_flags ** (V293_time_ready_core br bg bp bn ** CurTid t)).
  { unfold V293_time_ready_switch_core,V293_time_ready_switch_fields,
      V293_time_ready_core,V293_time_ready_fields in Opened |- *. sep auto. }
  apply astar_l_aemp_elim.
  eapply astar_mono;[exact FlagsEmpty | intros st H0;exact H0 | exact Pack].
Qed.
