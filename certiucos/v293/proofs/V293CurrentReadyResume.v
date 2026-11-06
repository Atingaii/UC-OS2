(* Post-switch resource transfer. The transient pre-switch state need not
   close the current guard. Suspended code is not assumed to have ended. *)
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCurrentInvariant.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyStorageInvariant.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.framework.proof.simulation.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.join_prop.
Require Import CertiOS.tactics.basetac.perm_map_lemmas.
Require Import Coq.Logic.FunctionalExtensionality.

Section CurrentReadyResume.
Variables br bg bp : block.
Variable target : var.
Variable tp : type.
Variable cells : list(addr*type).
Variable bc : block.
Let B := V293_ready_storage_inv br bg bp target tp cells.
Let G := V293_ready_current_inv br bg bp target tp cells bc.

Lemma V293_current_positive_isr : forall n k,
 starinv_isr B (S k) n = starinv_isr G (S k) n.
Proof.
 induction n;intros k;simpl starinv_isr;[reflexivity|rewrite IHn;reflexivity].
Qed.

Lemma V293_current_ieoff_equal : inv_ieoff B = inv_ieoff G.
Proof.
 unfold inv_ieoff,invlth_isr.
 f_equal;f_equal;apply functional_extensionality;intro k.
 replace(k+1)%nat with(S k)by lia.
 rewrite V293_current_positive_isr;reflexivity.
Qed.

Lemma V293_current_off_INV : forall st,
 getie(gettaskst st)=false -> st|=INV B -> st|=INV G.
Proof.
 intros st Off Held;destruct st as[[[[[[ge le] M] ir] [[ie si] cs]] O]ab].
 cbn in Off;subst ie.
 unfold INV in *;apply sat_split in Held.
 destruct Held as(m1&m2&o1&o2&JM&JO&Top&[On|Off]).
 - unfold inv_ieon in On;apply sat_split in On.
   destruct On as(a&b&c&d&J1&J2&Enabled&Rest).
   destruct Enabled as[Bad _];discriminate Bad.
 - apply sat_split';exists m1;exists m2;exists o1;exists o2.
   split;[exact JM| ];split;[exact JO| ];split;[exact Top| ].
   right;rewrite <-V293_current_ieoff_equal;exact Off.
Qed.

(* This is the original framework transfer, applied only after current-task
   handoff. Both totals are preserved; no extra shared ownership is created. *)
Theorem V293_current_ready_transfer : forall o o' Ol Os Ms Mc t t' S,
 getie o=false -> good_is_S S ->
 disjoint Ol Os -> disjoint Mc Ms ->
 (forall ab,(substaskst o Ms,Os,ab)|=INV B) ->
 (forall ab,(substaskst o Mc,Ol,ab)|=SWINVt B t') ->
 sched_self V293_scheduler Ol ->
 projS S t=Some o -> projS S t'=Some o' ->
 exists Mr Ms' Or Os',
 disjoint Mr Ms' /\ merge Mr Ms'=merge Mc Ms /\
 disjoint Or Os' /\ merge Or Os'=merge Ol Os /\
 (forall ab,(substaskst o' Ms',Os',ab)|=INV G) /\
 (forall ab,(substaskst o' Mr,Or,ab)|=RDYINV G t').
Proof.
 intros o o' Ol Os Ms Mc t t' S Off Good DO DM Inv Switch Highest P P'.
 assert(NewInv:forall ab,(substaskst o Ms,Os,ab)|=INV G).
 { intro ab;apply V293_current_off_INV;[destruct o as[[[[ge le]M]ir]aux];exact Off|apply Inv]. }
 assert(NewSwitch:forall ab,(substaskst o Mc,Ol,ab)|=SWINVt G t').
 { intro ab;destruct o as[[[[ge le]M]ir]aux].
   eapply V293_current_switch_highest;[apply Switch|exact Highest]. }
 eapply swi_rdy_inv';eassumption.
Qed.

(* The saved contract has exactly the RDYINV / private-frame shape used by
   the original global simulation. It remains an explicit proof obligation. *)
Theorem V293_current_resume_saved : forall pl ph Cl Ch lasrt P
 o o' Ol Os Ms Mc Mp Op t t' S,
 getie o=false -> good_is_S S ->
 disjoint Ol Os -> disjoint Mc Ms ->
 disjoint(merge Mc Ms)Mp -> disjoint(merge Ol Os)Op ->
 (forall ab,(substaskst o Ms,Os,ab)|=INV B) ->
 (forall ab,(substaskst o Mc,Ol,ab)|=SWINVt B t') ->
 sched_self V293_scheduler Ol ->
 projS S t=Some o -> projS S t'=Some o' ->
 (forall Mr Or,
   (forall ab,(RdyChange(substaskst o' Mr),Or,ab)|=RDYINV G t') ->
   disjoint Mr Mp -> disjoint Or Op ->
   TaskSim pl Cl (RdyChange(substaskst o'(merge Mr Mp)))
     ph Ch (merge Or Op) lasrt G P t') ->
 exists Mr Ms' Or Os',
 disjoint Mr Ms' /\ merge Mr Ms'=merge Mc Ms /\
 disjoint Or Os' /\ merge Or Os'=merge Ol Os /\
 disjoint Mr Mp /\ disjoint Or Op /\
 (forall ab,(substaskst o' Ms',Os',ab)|=INV G) /\
 (forall ab,(substaskst o' Mr,Or,ab)|=RDYINV G t') /\
 TaskSim pl Cl (substaskst o'(merge Mr Mp))
   ph Ch (merge Or Op) lasrt G P t'.
Proof.
 intros pl ph Cl Ch lasrt P o o' Ol Os Ms Mc Mp Op t t' S
 Off Good DO DM FrameM FrameO Inv Switch Highest Proj Proj' Saved.
 destruct(V293_current_ready_transfer o o' Ol Os Ms Mc t t' S
 Off Good DO DM Inv Switch Highest Proj Proj')as(Mr&Ms'&Or&Os'&DM'&EM&DO'&EO&Inv'&Ready).
 assert(PrivateM:disjoint Mr Mp).
 { apply mem_disjoint_merge_disjoint1 with(m2:=Ms');rewrite EM;exact FrameM. }
 assert(PrivateO:disjoint Or Op).
 { eapply osabst_disjoint_join_disjoint with(o2:=Os')(o3:=merge Or Os');[rewrite EO;exact FrameO|apply map_join_merge;exact DO']. }
 pose proof(rdyinv_isremp o' Or G Mr t' Ready)as Clear.
 exists Mr;exists Ms';exists Or;exists Os'.
 split;[exact DM'| ];split;[exact EM| ];split;[exact DO'| ];split;[exact EO| ];
 split;[exact PrivateM| ];split;[exact PrivateO| ];split;[exact Inv'| ];split;[exact Ready| ].
 rewrite <-(Clear(merge Mr Mp));apply Saved;[intro ab;rewrite Clear;apply Ready|exact PrivateM|exact PrivateO].
Qed.
End CurrentReadyResume.
