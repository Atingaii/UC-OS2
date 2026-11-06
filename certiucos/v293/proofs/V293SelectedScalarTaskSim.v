(* Original TaskSim for the selected scalar expression continuation.
   Shape restriction only; no new execution relation or arithmetic claim. *)
Require Import CertiOS.certiucos.v293.proofs.V293ReturnClientTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293CurrentReturnInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCurrentInvariant.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.simulation.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.

Definition V293_scalar_client_state(C:code):Prop:=
 (exists i u ty,C=(cure(econst32 i),(keop1 u ty kenil,kseq(sskip None)kstop))) \/
 (exists v u ty,C=(curs(sskip(Some v)),(keop1 u ty kenil,kseq(sskip None)kstop))) \/
 (exists v,C=(curs(sskip(Some v)),(kenil,kseq(sskip None)kstop))) \/
 C=(SKIP,(kenil,kstop)).

Lemma V293_scalar_client_not_os : forall C pu,
 V293_scalar_client_state C ->~InOS C pu.
Proof.
 intros C pu Cases;destruct Cases as[(i&u&ty&->) | [(v&u&ty&->) | [(v&->) | ->]]];
 unfold InOS;intros(c&ke&ks&E&H);inversion E;subst;
 destruct H as[(f&vl&fc&tl&Bad&Lookup)|[(f&le&ks'&tp&d1&d2&s&s'&Bad&Lookup)|Bad]];
 cbn in *;congruence.
Qed.
Lemma V293_scalar_client_cstep : forall C pu m C' m',
 V293_scalar_client_state C ->cstep pu C m C' m' ->
 V293_scalar_client_state C' /\ m'=m /\ forall pu',cstep pu' C m C' m.
Proof.
 intros C pu m C' m' Cases Step;destruct Cases as[(i&u&ty&->) | [(v&u&ty&->) | [(v&->) | ->]]];
 inversion Step;subst;
 repeat match goal with H:(_,_) = (_,_) |- _=>inversion H;clear H;subst end;
 match goal with
 | H:estep _ _ _ _ _ _ |- _ =>inversion H;subst;try discriminate
 | H:sstep _ _ _ _ _ _ _ |- _ =>inversion H;subst;try discriminate
 end.
 - split;[right;left;eauto|split;[reflexivity|intro;eapply expr_step;[reflexivity|apply ec32_step]]].
 - split;[right;right;left;eauto|split;[reflexivity|intro;eapply expr_step;[reflexivity|eapply evuop_step;eassumption]]].
 - split;[right;right;right;reflexivity|split;[reflexivity|intro;eapply stmt_step;[reflexivity|apply svseq_step]]].
Qed.
Lemma V293_scalar_client_no_event : forall C pu m C' m' ev,
 V293_scalar_client_state C ->~cstepev pu C m C' m' ev.
Proof.
 intros C pu m C' m' ev Cases Step;destruct Cases as[(i&u&ty&->) | [(v&u&ty&->) | [(v&->) | ->]]];
 inversion Step;subst;
 match goal with H:sstepev _ _ _ _ _ _ _ _ |- _=>inversion H;subst;discriminate end.
Qed.
Lemma V293_scalar_client_no_hapi : forall C A O C' O',
 V293_scalar_client_state C ->~hapistep A C O C' O'.
Proof.
 intros C A O C' O' Cases Step;destruct Cases as[(i&u&ty&->) | [(v&u&ty&->) | [(v&->) | ->]]];
 inversion Step;subst;discriminate.
Qed.
Lemma V293_scalar_client_match_low : forall pc po pi ip A C C' cst cst' o o' t O,
 V293_scalar_client_state C ->
 ltstep(pc,(po,pi,ip))t C cst o C' cst' o' ->
 V293_scalar_client_state C' /\ o'=o /\ htstep(pc,A)t C cst O C' cst' O.
Proof.
 intros pc po pi ip A C C' cst cst' o o' t O Cases Step;inversion Step;subst.
 - match goal with H:cstep _ _ _ _ _ |- _=>
   destruct(V293_scalar_client_cstep _ _ _ _ _ Cases H)as[Next[Equal Any]] end.
   inversion Equal;subst;split;[exact Next|split;[reflexivity| ]].
   eapply htclt_step;try reflexivity;[apply Any|eassumption].
 - exfalso;eapply V293_scalar_client_not_os;eassumption.
Qed.
Lemma V293_scalar_client_match_high : forall pc po pi ip A C C' cst cst' t O O' o,
 V293_scalar_client_state C ->
 htstep(pc,A)t C cst O C' cst' O' ->
 ltstep(pc,(po,pi,ip))t C cst o C' cst' o.
Proof.
 intros pc po pi ip A C C' cst cst' t O O' o Cases Step;inversion Step;subst.
 - match goal with H:cstep _ _ _ _ _ |- _=>
   destruct(V293_scalar_client_cstep _ _ _ _ _ Cases H)as[Next[Equal Any]] end.
   inversion Equal;subst;eapply clt_step;try reflexivity;try eassumption.
   + apply Any.
   + apply V293_scalar_client_not_os;exact Cases.
 - exfalso;eapply V293_scalar_client_no_hapi;eassumption.
Qed.
Lemma V293_scalar_client_no_low_event : forall pc po pi ip C cst o C' cst' o' ev t,
 V293_scalar_client_state C ->~ltstepev(pc,(po,pi,ip))t C cst o C' cst' o' ev.
Proof.
 intros pc po pi ip C cst o C' cst' o' ev t Cases Step;inversion Step;subst.
 eapply V293_scalar_client_no_event;eassumption.
Qed.
Lemma V293_scalar_client_no_high_event : forall pc A C cst O C' cst' O' ev t,
 V293_scalar_client_state C ->~htstepev(pc,A)t C cst O C' cst' O' ev.
Proof.
 intros pc A C cst O C' cst' O' ev t Cases Step;inversion Step;subst.
 eapply V293_scalar_client_no_event;eassumption.
Qed.
Lemma V293_scalar_client_match_abort : forall pc po pi ip A C cst o t O,
 V293_scalar_client_state C ->~IsEnd C ->
 ltstepabt(pc,(po,pi,ip))t C cst o ->htstepabtstar(pc,A)t C cst O.
Proof.
 intros pc po pi ip A C cst o t O Cases End Bad.
 inversion Bad;subst;apply htabtstar;exists C;exists cst;exists O;split;[apply ht_starO| ].
 eapply htstep_abt;[reflexivity|exact End| | | | | ].
 - destruct Cases as[(i&u&ty&->) | [(v&u&ty&->) | [(v&->) | ->]]];intros(a&b&c&d&e&BadShape);discriminate.
 - destruct Cases as[(i&u&ty&->) | [(v&u&ty&->) | [(v&->) | ->]]];intros(a&b&c&BadShape);discriminate.
 - destruct Cases as[(i&u&ty&->) | [(v&u&ty&->) | [(v&->) | ->]]];intros(a&b&BadShape);discriminate.
 - intros(C'&cst'&O'&Step).
   match goal with H:~(_ \/ _) |- _=>apply H;left end.
   exists C';exists o;exists cst';eapply V293_scalar_client_match_high;eassumption.
 - intros(C'&cst'&O'&ev&Step);eapply V293_scalar_client_no_high_event;eassumption.
Qed.

Theorem V293_scalar_client_TaskSim : forall pc po pi ip A C o O li I P t,
 V293_scalar_client_state C ->satp o O(CurLINV li t) ->P(o,O) ->
 TaskSim(pc,(po,pi,ip))C o(pc,A)C O li I P t.
Proof.
 cofix CIH;intros pc po pi ip A C o O li I P t Cases Local Post.
 apply task_sim.
 - intros Cl' Ms Mf cst cst' o'' Os o2 OO Inv JM JO Step.
   destruct(V293_scalar_client_match_low _ _ _ _ A _ _ _ _ _ _ _ OO Cases Step)
    as[Next[Equal Match]];subst o''.
   exists Cl';exists OO;exists o;exists Ms;exists O;exists Os.
   split;[eapply ht_starS;[exact Match|apply ht_starO]| ].
   split;[exact JM| ];split;[exact JO| ];split;[exact Inv| ];split;[exact Local| ].
   apply CIH;assumption.
 - intros Cl' Ms Mf cst cst' o'' Os o2 OO ev Inv JM JO Step.
   exfalso;eapply V293_scalar_client_no_low_event;eassumption.
 - intros Ms ks x Os OO Eq;destruct Cases as[(i&u&ty&->) | [(v&u&ty&->) | [(v&->) | ->]]];discriminate.
 - intros Ms Os OO End Inv DM JO.
   exists O;exists Os;exists C;exists OO.
   split;[exact End| ];split;[intro;apply ht_starO| ];split;[exact JO| ];
   split;[exact Inv| ];split;[exact Local|exact Post].
 - intros cst o' Ms Os Mf OO Of OOO End Switch Stk Free Inv JM JO JO' Bad.
   eapply V293_scalar_client_match_abort;eassumption.
 - intros Ms Os e1 e2 e3 ks OO Eq;destruct Cases as[(i&u&ty&->) | [(v&u&ty&->) | [(v&->) | ->]]];discriminate.
 - intros Ms Os e ks OO Eq;destruct Cases as[(i&u&ty&->) | [(v&u&ty&->) | [(v&->) | ->]]];discriminate.
Qed.

Section ScalarClient.
Variables br bg bp : block.
Variable target : var.
Variable tp : type.
Variable cells : list(addr*type).
Variable cache : block.
Let G:=V293_ready_current_inv br bg bp target tp cells cache.
Let Core:=V293_ready_current_core br bg bp target tp cells cache.

(* Shared, target-owned and external resources exactly cover the input.
   R is not installed as the target's local invariant. No TaskSim is assumed. *)
Theorem V293_scalar_current_TaskSim : forall pc po pi ip A C li lg t R
 ge le M ir enabled si ci O op,
 V293_scalar_client_state C ->
 (forall i,ir i=false) ->(enabled=false ->gettopis si<=INUM) ->
 (ge,le,M,ir,(enabled,si,ci),O,op)|=
 Core **(CurTid t **(LINV li t lg **R)) ->
 exists Ms Mt Mf Mtail Os Ot Of Otail,
 join Mt Mf Mtail /\join Ms Mtail M /\
 join Ot Of Otail /\join Os Otail O /\
 satp(ge,le,Ms,ir,(enabled,si,ci))Os(INV G) /\
 satp(ge,le,Mt,ir,(enabled,si,ci))Ot(RDYINV G t **LINV li t lg) /\
 (ge,le,Mf,ir,(enabled,si,ci),Of,op)|=R /\
 TaskSim(pc,(po,pi,ip))C(ge,le,Mt,ir,(enabled,si,ci))
 (pc,A)C Ot li G
 (fun s=>satp(fst s)(snd s)(RDYINV G t **LINV li t lg))t.
Proof.
 intros pc po pi ip A C li lg t R ge le M ir enabled si ci O op Cases Clear Bound Held.
 pose proof(V293_current_return_invariants br bg bp target tp cells cache
 t(LINV li t lg **R)ge le M ir enabled si ci O op Clear Bound Held)as Partition.
 assert(Packed:(ge,le,M,ir,(enabled,si,ci),O,op)|=
 INV G **((RDYINV G t **LINV li t lg) **R))by(sep auto).
 apply sat_split in Packed;destruct Packed as(Ms&Mtail&Os&Otail&JM&JO&Shared&Rest).
 apply sat_split in Rest;destruct Rest as(Mt&Mf&Ot&Of&JMt&JOt&Task&Frame).
 assert(TaskAll:satp(ge,le,Mt,ir,(enabled,si,ci))Ot(RDYINV G t **LINV li t lg)).
 { intro ab;apply sat_split in Task;destruct Task as(mr&ml&orr&ol&JM'&JO'&Ready&Private).
   apply sat_split';exists mr;exists ml;exists orr;exists ol.
   split;[exact JM'| ];split;[exact JO'| ];split.
   - eapply V293_return_ready_all_operations;exact Ready.
   - eapply linv_aop_irev';exact Private. }
 exists Ms;exists Mt;exists Mf;exists Mtail;exists Os;exists Ot;exists Of;exists Otail.
 split;[exact JMt| ];split;[exact JM| ];split;[exact JOt| ];split;[exact JO| ];split.
 - intro ab;eapply INV_irrev_prop;exact Shared.
 - split;[exact TaskAll| ];split;[exact Frame| ].
   apply V293_scalar_client_TaskSim;[exact Cases| |exact TaskAll].
   eapply V293_return_ready_local;exact TaskAll.
Qed.
End ScalarClient.
