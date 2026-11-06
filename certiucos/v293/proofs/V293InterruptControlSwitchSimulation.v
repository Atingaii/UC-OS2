(* A cutpoint forward match, using only the original low/high switch rules.
   Controls remain observations of owned bytes, not a new ProgSim state. *)
Require Import CertiOS.certiucos.v293.proofs.V293InterruptControlScheduler.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptFixedControlSpec.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptControlRetention.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptQuietBuilder.
Require Import CertiOS.certiucos.v293.proofs.V293ReadySwitchStep.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293SwitchProgSim.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.simulation.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Local Open Scope nat_scope.

Lemma V293_switch_owned_capture : forall br bg bp brun bn bl current r n l R
 ge le M ir aux O op,
 r<256 ->n<256 ->l<256 ->
 (ge,le,M,ir,aux,O,op)|=SWINVt(V293_ready_inv br bg bp)current **
 (V293_irq_controls brun bn bl r n l **R) ->
 V293_control_capture brun bn bl(ge,le,M,ir,aux,O,op)=
 Some(O,V293_control r n l).
Proof.
 intros br bg bp brun bn bl current r n l R ge le M ir aux O op RR RN RL Held.
 apply V293_control_capture_owned;try assumption.
 unfold V293_irq_controls in *;sep auto.
Qed.

Section SwitchMatch.
Variables br bg bp brun bn bl:block.
Variables pc po pi:progunit.
Variable ip:intunit.
Variable api:osapispec.
Variable ints:osintspec.
Variable sd:ossched.
Variables T Th:tasks.
Variable cst:clientst.
Variables current next:tid.
Variable target:var.
Variable ks:stmtcont.
Variable ke:exprcont.
Variable hks:stmtcont.
Variable tail:spec_code.
Variables ge le:env.
Variable les:cltenvs.
Variable M:mem.
Variable ir:isr.
Variable aus:ltaskstset.
Variable si:is.
Variable cs:cs.
Variables bt bc:block.
Variable tp:type.
Variable O:osabst.
Variable op:spec_code.
Variable R:asrt.
Variables r n l:nat.
Let P:lprog:=(pc,(po,pi,ip)).
Let Ph:hprog:=(pc,(api,ints,sd)).
Let S:osstate:=(ge,les,M,ir,aus).
Let Tf:=set T current(SKIP,(kenil,ks)).
Let Thf:=set Th current(curs(hapi_code tail),(ke,hks)).
Let Of:=set O curtid(oscurt next).
Let c:=V293_control r n l.
Hypothesis RR:r<256.
Hypothesis RN:n<256.
Hypothesis RL:l<256.
Hypothesis Local:get les current=Some le.
Hypothesis Aux:get aus current=Some((false,si,cs):localst).
Hypothesis Code:get T current=Some(curs(sprim(switch target)),(kenil,ks)).
Hypothesis Target:get ge target=Some(bt,Tptr tp).
Hypothesis Read:load(Tptr tp)M(bt,0%Z)=Some(Vptr next).
Hypothesis Current:get ge OSTCBCur=Some(bc,Tptr tp).
Hypothesis Cur:get O curtid=Some(oscurt current).
Hypothesis Selected:sd O next.
Hypothesis HighCode:get Th current=Some(curs(hapi_code(sched;;tail)),(ke,hks)).
Hypothesis Held:(ge,le,M,ir,(false,si,cs),O,op)|=
 SWINVt(V293_ready_inv br bg bp)current **(V293_irq_controls brun bn bl r n l **R).

(* Ownership constructs the store and low step. Every low successor is that
   same state, matched by the original high step. No finite-step premise. *)
Theorem V293_control_switch_forward : exists Mf,
 lpstep P T cst S current Tf cst(ge,les,Mf,ir,aus)next /\
 store(Tptr tp)M(bc,0%Z)(Vptr next)=Some Mf /\
 hpstep Ph Th cst O Thf cst Of /\
 V293_control_run_step sd(V293_control_Core(sched;;tail))(O,c)(Some(current,next))
 (V293_control_Core tail)(Of,c) /\
 (ge,le,Mf,ir,(false,si,cs),Of,op)|=
 SWINVt(V293_ready_inv br bg bp)next **(V293_irq_controls brun bn bl r n l **R) /\
 V293_control_capture brun bn bl(ge,le,Mf,ir,(false,si,cs),Of,op)=Some(Of,c) /\
 load(Tptr tp)Mf(bc,0%Z)=Some(Vptr next) /\get Of curtid=Some(oscurt next) /\
 (forall T' cst' S' t',lpstep P T cst S current T' cst' S' t' ->
   T'=Tf /\cst'=cst /\S'=(ge,les,Mf,ir,aus) /\t'=next) /\
 (forall T' cst' S' t' ev,~lpstepev P T cst S current T' cst' S' t' ev) /\
 ~lpstepabt P T cst S current /\
 (forall other,other<>current ->get Tf other=get T other /\get Thf other=get Th other) /\
 (forall key,key<>curtid ->get Of key=get O key) /\
 (forall b i,b<>bc \/(i<0)%Z \/(4<=i)%Z ->get Mf(b,i)=get M(b,i)).
Proof.
 destruct(V293_ready_switch_step br bg bp pc po pi ip T cst ks current next target bt bc
 ge le les M ir(false,si,cs)aus O op(V293_irq_controls brun bn bl r n l **R)tp
 Local Aux Code Target Read Current Held)
 as(Mf&Step&Store&After&Physical&OldCode&Other&Outside).
 assert(Event:V293_control_run_step sd(V293_control_Core(sched;;tail))(O,c)(Some(current,next))
 (V293_control_Core tail)(Of,c))by(constructor;assumption).
 destruct(V293_control_switch_hpstep pc api ints sd Th cst ke hks _ _ _ _ _ _ _ _ Event HighCode)
 as(High&Controls&Abstract&AbsFrame&TaskFrame).
 exists Mf;split;[exact Step| ];split;[exact Store| ];split;[exact High| ];split;[exact Event| ].
 split;[exact After| ];split.
 - eapply V293_switch_owned_capture;try eassumption.
 - split;[exact Physical| ];split;[exact Abstract| ];split.
   + eapply V293_switch_all_successors;try eassumption.
   + split.
     * eapply V293_switch_no_output;try eassumption.
     * split.
       -- eapply V293_switch_no_abort;try eassumption.
       -- split;[intros;split;[apply Other;assumption|apply TaskFrame;assumption]| ].
          split;assumption.
Qed.

(* This is the original ProgSim constructor, NOT soundness of a product-state
   framework. The continuation remains an explicit independent obligation. *)
Theorem V293_control_switch_progsim :
 (forall Mf,store(Tptr tp)M(bc,0%Z)(Vptr next)=Some Mf ->
   (ge,le,Mf,ir,(false,si,cs),Of,op)|=
    SWINVt(V293_ready_inv br bg bp)next **(V293_irq_controls brun bn bl r n l **R) ->
   V293_control_capture brun bn bl(ge,le,Mf,ir,(false,si,cs),Of,op)=Some(Of,c) ->
   ProgSim P Tf(ge,les,Mf,ir,aus)Ph Thf Of cst next) ->
 ProgSim P T S Ph Th O cst current.
Proof.
 intro Post.
 destruct V293_control_switch_forward
 as(Mf&Step&Store&High&Event&After&Captured&Physical&Abstract&All&Output&NoAbort&Frames).
 eapply V293_switch_progsim with(le:=le)(Mf:=Mf)(next:=next)(bt:=bt)(bc:=bc)(tp:=tp)
 (si:=si)(cs:=cs)(Thf:=Thf)(Of:=Of);try eassumption.
 - eapply hp_stepS;[exact High|apply hp_stepO].
 - apply Post;assumption.
Qed.
End SwitchMatch.
