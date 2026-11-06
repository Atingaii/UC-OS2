(* An independently established saved contract for a finite, nonterminal
   client. No API correctness or saved TaskSim is assumed. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.simulation.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.join_prop.
Require Import CertiOS.certiucos.v293.proofs.V293CurrentReadyResume.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyStorageInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCurrentInvariant.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.

Definition V293_skip_client_code:code:=
 (curs(sseq(sskip None)(sskip None)),(kenil,kstop)).
Definition V293_skip_client_next:code:=
 (SKIP,(kenil,kseq(sskip None)kstop)).
Definition V293_skip_client_state(C:code):Prop:=
 C=V293_skip_client_code \/ C=V293_skip_client_next \/ C=(SKIP,(kenil,kstop)).

Lemma V293_skip_client_not_os : forall C pu,
 V293_skip_client_state C ->~InOS C pu.
Proof.
 intros C pu Cases;destruct Cases as[-> | [-> | ->]];
 unfold InOS;intros(c&ke&ks&E&H);inversion E;subst;
 destruct H as[(f&vl&fc&tl&Bad&Lookup)|[(f&le&ks'&tp&d1&d2&s&s'&Bad&Lookup)|Bad]];
 cbn in *;congruence.
Qed.
Lemma V293_skip_client_cstep : forall C pu m C' m',
 V293_skip_client_state C ->cstep pu C m C' m' ->
 V293_skip_client_state C' /\ m'=m /\ forall pu',cstep pu' C m C' m.
Proof.
 intros C pu m C' m' Cases Step;destruct Cases as[-> | [-> | ->]];
 unfold V293_skip_client_code,V293_skip_client_next in *;inversion Step;subst;
 repeat match goal with H:(_,_) = (_,_) |- _=>inversion H;clear H;subst end;
 match goal with
 | H:estep _ _ _ _ _ _ |- _ =>inversion H;subst;try discriminate
 | H:sstep _ _ _ _ _ _ _ |- _ =>inversion H;subst;try discriminate
 end.
 - split;[right;left;reflexivity|split;[reflexivity|intro;eapply stmt_step;[reflexivity|apply sseq_step]]].
 - split;[right;right;reflexivity|split;[reflexivity|intro;eapply stmt_step;[reflexivity|apply sskip_step]]].
Qed.
Lemma V293_skip_client_no_event : forall C pu m C' m' ev,
 V293_skip_client_state C ->~cstepev pu C m C' m' ev.
Proof.
 intros C pu m C' m' ev Cases Step;destruct Cases as[-> | [-> | ->]];
 inversion Step;subst;
 match goal with H:sstepev _ _ _ _ _ _ _ _ |- _=>inversion H;subst;discriminate end.
Qed.
Lemma V293_skip_client_no_hapi : forall C A O C' O',
 V293_skip_client_state C ->~hapistep A C O C' O'.
Proof.
 intros C A O C' O' Cases Step;destruct Cases as[-> | [-> | ->]];
 inversion Step;subst;discriminate.
Qed.
Lemma V293_skip_client_match_low : forall pc po pi ip A C C' cst cst' o o' t O,
 V293_skip_client_state C ->
 ltstep(pc,(po,pi,ip))t C cst o C' cst' o' ->
 V293_skip_client_state C' /\ o'=o /\ htstep(pc,A)t C cst O C' cst' O.
Proof.
 intros pc po pi ip A C C' cst cst' o o' t O Cases Step;inversion Step;subst.
 - match goal with H:cstep _ _ _ _ _ |- _=>
   destruct(V293_skip_client_cstep _ _ _ _ _ Cases H)as[Next[Equal Any]] end.
   inversion Equal;subst;split;[exact Next|split;[reflexivity| ]].
   eapply htclt_step;try reflexivity;[apply Any|eassumption].
 - exfalso;eapply V293_skip_client_not_os;eassumption.
Qed.
Lemma V293_skip_client_match_high : forall pc po pi ip A C C' cst cst' t O O' o,
 V293_skip_client_state C ->
 htstep(pc,A)t C cst O C' cst' O' ->
 ltstep(pc,(po,pi,ip))t C cst o C' cst' o.
Proof.
 intros pc po pi ip A C C' cst cst' t O O' o Cases Step;inversion Step;subst.
 - match goal with H:cstep _ _ _ _ _ |- _=>
   destruct(V293_skip_client_cstep _ _ _ _ _ Cases H)as[Next[Equal Any]] end.
   inversion Equal;subst;eapply clt_step;try reflexivity;try eassumption.
   + apply Any.
   + apply V293_skip_client_not_os;exact Cases.
 - exfalso;eapply V293_skip_client_no_hapi;eassumption.
Qed.
Lemma V293_skip_client_no_low_event : forall pc po pi ip C cst o C' cst' o' ev t,
 V293_skip_client_state C ->~ltstepev(pc,(po,pi,ip))t C cst o C' cst' o' ev.
Proof.
 intros pc po pi ip C cst o C' cst' o' ev t Cases Step;inversion Step;subst.
 eapply V293_skip_client_no_event;eassumption.
Qed.
Lemma V293_skip_client_no_high_event : forall pc A C cst O C' cst' O' ev t,
 V293_skip_client_state C ->~htstepev(pc,A)t C cst O C' cst' O' ev.
Proof.
 intros pc A C cst O C' cst' O' ev t Cases Step;inversion Step;subst.
 eapply V293_skip_client_no_event;eassumption.
Qed.
Lemma V293_skip_client_match_abort : forall pc po pi ip A C cst o t O,
 V293_skip_client_state C ->~IsEnd C ->
 ltstepabt(pc,(po,pi,ip))t C cst o ->htstepabtstar(pc,A)t C cst O.
Proof.
 intros pc po pi ip A C cst o t O Cases End Bad.
 inversion Bad;subst;apply htabtstar;exists C;exists cst;exists O;split;[apply ht_starO| ].
 eapply htstep_abt;[reflexivity|exact End| | | | | ].
 - destruct Cases as[-> | [-> | ->]];intros(a&b&c&d&e&BadShape);discriminate.
 - destruct Cases as[-> | [-> | ->]];intros(a&b&c&BadShape);discriminate.
 - destruct Cases as[-> | [-> | ->]];intros(a&b&BadShape);discriminate.
 - intros(C'&cst'&O'&Step).
   match goal with H:~(_ \/ _) |- _=>apply H;left end.
   exists C';exists o;exists cst';eapply V293_skip_client_match_high;eassumption.
 - intros(C'&cst'&O'&ev&Step);eapply V293_skip_client_no_high_event;eassumption.
Qed.

Lemma V293_init_curlinv : forall li t o O,
 InitTaskSt li t(o,O) ->satp o O(CurLINV li t).
Proof.
 intros li t o O[Held Empty]ab;specialize(Held ab).
 unfold CurLINV;exists init_lg;sep auto.
Qed.

Theorem V293_skip_client_TaskSim : forall pc po pi ip A C o O li I t,
 V293_skip_client_state C ->InitTaskSt li t(o,O) ->
 TaskSim(pc,(po,pi,ip))C o(pc,A)C O li I(InitTaskSt li t)t.
Proof.
 cofix CIH;intros pc po pi ip A C o O li I t Cases Init.
 pose proof(V293_init_curlinv _ _ _ _ Init)as Local.
 apply task_sim.
 - intros Cl' Ms Mf cst cst' o'' Os o2 OO Inv JM JO Step.
   destruct(V293_skip_client_match_low _ _ _ _ A _ _ _ _ _ _ _ OO Cases Step)
    as[Next[Equal Match]];subst o''.
   exists Cl';exists OO;exists o;exists Ms;exists O;exists Os.
   split;[eapply ht_starS;[exact Match|apply ht_starO]| ].
   split;[exact JM| ];split;[exact JO| ];split;[exact Inv| ];split;[exact Local| ].
   apply CIH;assumption.
 - intros Cl' Ms Mf cst cst' o'' Os o2 OO ev Inv JM JO Step.
   exfalso;eapply V293_skip_client_no_low_event;eassumption.
 - intros Ms ks x Os OO Eq;destruct Cases as[-> | [-> | ->]];discriminate.
 - intros Ms Os OO End Inv DM JO.
   exists O;exists Os;exists C;exists OO.
   split;[exact End| ];split;[intro;apply ht_starO| ];split;[exact JO| ];
   split;[exact Inv| ];split;[exact Local|exact Init].
 - intros cst o' Ms Os Mf OO Of OOO End Switch Stk Free Inv JM JO JO' Bad.
   eapply V293_skip_client_match_abort;eassumption.
 - intros Ms Os e1 e2 e3 ks OO Eq;destruct Cases as[-> | [-> | ->]];discriminate.
 - intros Ms Os e ks OO Eq;destruct Cases as[-> | [-> | ->]];discriminate.
Qed.

Theorem V293_skip_client_saved : forall pc po pi ip A ge Mp Op li I t,
 satp(ge,emp,Mp,empisr,(true,nil,nil))Op(LINV li t init_lg) ->
 forall Mr Or,
 (forall ab,(RdyChange(ge,emp,Mr,empisr,(true,nil,nil)),Or,ab)|=RDYINV I t) ->
 disjoint Mr Mp ->disjoint Or Op ->
 TaskSim(pc,(po,pi,ip))V293_skip_client_code
 (RdyChange(ge,emp,merge Mr Mp,empisr,(true,nil,nil)))
 (pc,A)V293_skip_client_code(merge Or Op)li I(InitTaskSt li t)t.
Proof.
 intros pc po pi ip A ge Mp Op li I t Private Mr Or Ready DM DO.
 apply V293_skip_client_TaskSim;[left;reflexivity| ].
 split;[ |reflexivity].
 eapply crt_init;[exact DM|exact DO|exact Ready|exact Private].
Qed.

Section CurrentSkipResume.
Variables br bg bp : block.
Variable target : var.
Variable tp : type.
Variable cells : list(addr*type).
Variable bc : block.
Let B:=V293_ready_storage_inv br bg bp target tp cells.
Let G:=V293_ready_current_inv br bg bp target tp cells bc.

(* Unlike the general resume interface, this interface has no saved TaskSim
   hypothesis. It is restricted to the finite initial-state client above. *)
Theorem V293_current_skip_resume : forall pc po pi ip A li
 o Ol Os Ms Mc Mp Op t t' S ge M,
 getie o=false ->good_is_S S ->
 disjoint Ol Os ->disjoint Mc Ms ->
 disjoint(merge Mc Ms)Mp ->disjoint(merge Ol Os)Op ->
 (forall ab,(substaskst o Ms,Os,ab)|=INV B) ->
 (forall ab,(substaskst o Mc,Ol,ab)|=SWINVt B t') ->
 sched_self V293_scheduler Ol ->
 projS S t=Some o ->projS S t'=Some(ge,emp,M,empisr,(true,nil,nil)) ->
 satp(ge,emp,Mp,empisr,(true,nil,nil))Op(LINV li t' init_lg) ->
 exists Mr Ms' Or Os',
 disjoint Mr Ms' /\ merge Mr Ms'=merge Mc Ms /\
 disjoint Or Os' /\ merge Or Os'=merge Ol Os /\
 disjoint Mr Mp /\ disjoint Or Op /\
 (forall ab,(ge,emp,Ms',empisr,(true,nil,nil),Os',ab)|=INV G) /\
 (forall ab,(ge,emp,Mr,empisr,(true,nil,nil),Or,ab)|=RDYINV G t') /\
 TaskSim(pc,(po,pi,ip))V293_skip_client_code
 (ge,emp,merge Mr Mp,empisr,(true,nil,nil))
 (pc,A)V293_skip_client_code(merge Or Op)li G(InitTaskSt li t')t'.
Proof.
 intros pc po pi ip A li o Ol Os Ms Mc Mp Op t t' S ge M
 Off Good DO DM FrameM FrameO Inv Switch High Proj Proj' Private.
 apply(V293_current_resume_saved br bg bp target tp cells bc
 (pc,(po,pi,ip))(pc,A)V293_skip_client_code V293_skip_client_code li
 (InitTaskSt li t')o(ge,emp,M,empisr,(true,nil,nil))Ol Os Ms Mc Mp Op t t' S);
 try assumption.
 intros Mr Or Ready DMr DOr.
 apply V293_skip_client_saved;assumption.
Qed.
End CurrentSkipResume.
