(* Original trace refinement contracts, with the entire low world generalized. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.framework.proof.simulation.
Require Import CertiOS.framework.proof.oscorrectness.
Require Import CertiOS.tactics.base_tac.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Import DeprecatedTactic.

Lemma V293_progsim_imply_eref_aux : forall  (E : evtrace) (lp: lprog) (lt : tasks)
 (cs : clientst) (os : osstate) (t: tid), LETr (lp, lt, cs, os, t) E ->
  (forall 
 (hp: hprog) (ht: tasks) (bs : osabst) , ProgSim lp lt os  hp ht bs cs t ->
   HETr (hp, ht, cs, bs) E).
Proof.
introv HLe.
remember (lp, lt, cs, os, t) as lw in HLe.
revert lp lt cs os t Heqlw.
induction HLe; intros lp0 lt0 cs0 os0 t0 Heq; inversion Heq; subst; clear Heq.
introv Hsim.
constructors.
introv Hsim.
inverts keep Hsim.
lets Hk : H1 H.
destruct Hk as (Th' & O' &  Hstep & Hpsim).
eapply  Hstepstar_no_ev.
eauto.
eapply IHHLe; eauto.
eauto.

introv Hsim.
inverts keep Hsim.
lets (Th' & O' & Hstep & Hpsim) : H2 H.
eapply  Hstepstar_with_ev.
eauto.
eapply IHHLe; eauto.
eauto.
introv Hsim.
inverts keep Hsim.
lets Hk : H3 H.
inverts Hk.
destruct H4 as (T'& cst' & O' & Hp & Ha).
eapply  Hstepstar_no_ev.
eauto.
constructors.
eauto.
Qed.

Theorem V293_progsim_imply_eref : forall lw hw, prog_sim lw hw ->  etrace_subset lw hw.
Proof.
introv Hpsim.
deslw lw.
deshw hw.
unfolds in Hpsim.
lets (Hp1 & Hp2 & Hp3) : Hpsim.
unfolds.
introv Hle.
simpls. 
eapply  V293_progsim_imply_eref_aux; eauto.

rewrite <- Hp2.
eauto.

rewrite <- Hp2.
eauto.
Qed.
