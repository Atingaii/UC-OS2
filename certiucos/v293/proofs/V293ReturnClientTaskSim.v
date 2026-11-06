(* Return-state TaskSim, without pretending that a resumed caller is a
   freshly initialized task. The exact RDYINV/LINV packet is retained. *)
Require Import CertiOS.certiucos.v293.proofs.V293CurrentReturnInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCurrentInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293ClientSkipTaskSim.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.simulation.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.

Lemma V293_return_client_coinduction : forall pc po pi ip A C o O li I P t,
 V293_skip_client_state C ->satp o O(CurLINV li t) ->P(o,O) ->
 TaskSim(pc,(po,pi,ip))C o(pc,A)C O li I P t.
Proof.
 cofix CIH;intros pc po pi ip A C o O li I P t Cases Local Post.
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
   split;[exact Inv| ];split;[exact Local|exact Post].
 - intros cst o' Ms Os Mf OO Of OOO End Switch Stk Free Inv JM JO JO' Bad.
   eapply V293_skip_client_match_abort;eassumption.
 - intros Ms Os e1 e2 e3 ks OO Eq;destruct Cases as[-> | [-> | ->]];discriminate.
 - intros Ms Os e ks OO Eq;destruct Cases as[-> | [-> | ->]];discriminate.
Qed.

Lemma V293_return_ready_all_operations : forall ge le M ir aux O op I t,
 (ge,le,M,ir,aux,O,op)|=RDYINV I t ->
 satp(ge,le,M,ir,aux)O(RDYINV I t).
Proof.
 intros ge le M ir aux O op I t Held ab.
 unfold RDYINV in *;destruct Held as[On|Off].
 - left;exact On.
 - right;eapply swinv_aop_irev;exact Off.
Qed.

Lemma V293_return_ready_local : forall o O li I lg t,
 satp o O(RDYINV I t **LINV li t lg) ->satp o O(CurLINV li t).
Proof.
 intros [[[[ge le]M]ir]aux] O li I lg t Held ab.
 specialize(Held ab);apply sat_split in Held.
 destruct Held as(mr&ml&orr&ol&JM&JO&Ready&Private).
 assert(Current:(ge,le,mr,ir,aux,orr,ab)|=CurTid t **Atrue).
 { unfold RDYINV in Ready;destruct Ready as[On|Off].
   - fold(CurTid t)in On;sep auto.
   - unfold SWINVt in Off;fold(CurTid t)in Off;sep auto. }
 assert(Packed:(ge,le,M,ir,aux,O,ab)|=(CurTid t **Atrue) **LINV li t lg).
 { apply sat_split';exists mr;exists ml;exists orr;exists ol.
   split;[exact JM| ];split;[exact JO| ];split;assumption. }
 unfold CurLINV;exists lg;clear Ready Private Current;sep auto.
Qed.

Section ReturnClient.
Variables br bg bp : block.
Variable target : var.
Variable tp : type.
Variable cells : list(addr*type).
Variable cache : block.
Let G:=V293_ready_current_inv br bg bp target tp cells cache.
Let Core:=V293_ready_current_core br bg bp target tp cells cache.

(* Shared, target-owned and external resources exactly cover the input.
   R is not installed as the target's local invariant. No TaskSim is assumed. *)
Theorem V293_return_client_TaskSim : forall pc po pi ip A C li lg t R
 ge le M ir enabled si ci O op,
 V293_skip_client_state C ->
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
   apply V293_return_client_coinduction;[exact Cases| |exact TaskAll].
   eapply V293_return_ready_local;exact TaskAll.
Qed.
End ReturnClient.
