(* Match the client call before using the proved OS API entry. *)
Require Import CertiOS.certiucos.v293.proofs.V293ExitActiveCallTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293InvariantPendingTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293ClientSkipTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyStorageInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293PendingReturnTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBoundarySwitch.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.code.V293OSIntExit.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.certiucos.v293.proofs.V293HandoffProgSim.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.simulation.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStoragePrefix.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrent.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Lemma V293_client_nil_call_cstep : forall p f ks m Cf mf,
 cstep p(curs(scall f nil),(kenil,ks))m Cf mf ->
 Cf=(curs(sfexec f nil nil),(kenil,ks)) /\ mf=m /\
 (forall p',cstep p'(curs(scall f nil),(kenil,ks))m Cf m).
Proof.
 intros p f ks m Cf mf Step;inversion Step;subst;
 match goal with
 | H:estep _ _ _ _ _ _ |- _ =>inversion H;subst;try discriminate
 | H:sstep _ _ _ _ _ _ _ |- _ =>inversion H;subst;try discriminate
 end.
 repeat match goal with E:(_,_) = (_,_) |- _=>inversion E;clear E;subst end.
 repeat split;try reflexivity;intro p';eapply stmt_step;[reflexivity|apply snpcall_step].
Qed.

Lemma V293_client_nil_call_low : forall pc po pi ip A f ks t cst cst' o o' O Cf,
 ~InOS(curs(scall f nil),(kenil,ks))(pumerge po pi) ->
 ltstep(pc,(po,pi,ip))t(curs(scall f nil),(kenil,ks))cst o Cf cst' o' ->
 o'=o /\ Cf=(curs(sfexec f nil nil),(kenil,ks)) /\
 htstep(pc,A)t(curs(scall f nil),(kenil,ks))cst O Cf cst' O.
Proof.
 intros pc po pi ip A f ks t cst cst' o o' O Cf Outside Step;inversion Step;subst;
 repeat match goal with E:(_,_) = (_,_) |- _=>inversion E;clear E;subst end.
 - match goal with H:cstep _ _ _ _ _ |- _ =>
   destruct(V293_client_nil_call_cstep _ _ _ _ _ _ H)as[Code[Equal Any]]end.
   inversion Equal;subst;split;[reflexivity| ];split;[reflexivity| ].
   eapply htclt_step;try reflexivity;[apply Any|eassumption].
 - contradiction.
Qed.

Lemma V293_client_nil_call_high : forall pc po pi ip A f ks t cst cst' O O' o Cf,
 ~InOS(curs(scall f nil),(kenil,ks))(pumerge po pi) ->
 htstep(pc,A)t(curs(scall f nil),(kenil,ks))cst O Cf cst' O' ->
 ltstep(pc,(po,pi,ip))t(curs(scall f nil),(kenil,ks))cst o Cf cst' o.
Proof.
 intros pc po pi ip A f ks t cst cst' O O' o Cf Outside Step;inversion Step;subst;
 repeat match goal with E:(_,_) = (_,_) |- _=>inversion E;clear E;subst end.
 - match goal with H:cstep _ _ _ _ _ |- _ =>
   destruct(V293_client_nil_call_cstep _ _ _ _ _ _ H)as[Code[Equal Any]]end.
   inversion Equal;subst;eapply clt_step;try reflexivity;try eassumption;apply Any.
 - match goal with H:hapistep _ _ _ _ _ |- _ =>inversion H;subst;discriminate end.
Qed.

Lemma V293_client_nil_call_no_event : forall p f ks m Cf mf ev,
 ~cstepev p(curs(scall f nil),(kenil,ks))m Cf mf ev.
Proof. intros p f ks m Cf mf ev Step;inversion Step;subst;
 match goal with H:sstepev _ _ _ _ _ _ _ _ |- _ =>inversion H;subst;discriminate end. Qed.

Lemma V293_client_nil_call_abort : forall pc po pi ip A f ks t cst o O,
 ~InOS(curs(scall f nil),(kenil,ks))(pumerge po pi) ->
 ltstepabt(pc,(po,pi,ip))t(curs(scall f nil),(kenil,ks))cst o ->
 htstepabtstar(pc,A)t(curs(scall f nil),(kenil,ks))cst O.
Proof.
 intros pc po pi ip A f ks t cst o O Outside Bad.
 inversion Bad;subst;apply htabtstar.
 exists(curs(scall f nil),(kenil,ks));exists cst;exists O;split;[apply ht_starO| ].
 eapply htstep_abt;[reflexivity| | | | | | ].
 - intros(v&E);discriminate E.
 - intros(a&b&c&d&e&E);discriminate E.
 - intros(a&b&c&E);discriminate E.
 - intros(a&b&E);discriminate E.
 - intros(C'&cst'&O'&Step).
   match goal with H:~(_ \/ _) |- _ =>apply H;left end.
   exists C';exists o;exists cst';eapply V293_client_nil_call_high;eassumption.
 - intros(C'&cst'&O'&ev&Step);inversion Step;subst.
   eapply V293_client_nil_call_no_event;eassumption.
Qed.

Lemma V293_client_nil_api_enter : forall pc A f ks t cst O,
 fst(fst A)f=Some((fun _:vallist=>spec_seq sched(spec_done None)),(Tvoid,nil)) ->
 htstep(pc,A)t(curs(sfexec f nil nil),(kenil,ks))cst O
 (curs(hapi_code(spec_seq sched(spec_done None))),(kenil,ks))cst O.
Proof.
 intros pc [[B C]D] f ks t cst O Bind.
 eapply hapi_step;[reflexivity| ].
 eapply hapienter_step with(vl:=nil)(tl:=nil)(tp:=Tvoid)
 (r:=fun _:vallist=>spec_seq sched(spec_done None));try reflexivity;exact Bind.
Qed.

Lemma V293_client_nil_call_bridge : forall pc po pi ip A f ks o O li I Post t,
 ~InOS(curs(scall f nil),(kenil,ks))(pumerge po pi) ->
 fst(fst A)f=Some((fun _:vallist=>spec_seq sched(spec_done None)),(Tvoid,nil)) ->
 satp o O(CurLINV li t) ->
 TaskSim(pc,(po,pi,ip))(curs(sfexec f nil nil),(kenil,ks))o
 (pc,A)(curs(hapi_code(spec_seq sched(spec_done None))),(kenil,ks))O li I Post t ->
 TaskSim(pc,(po,pi,ip))(curs(scall f nil),(kenil,ks))o
 (pc,A)(curs(scall f nil),(kenil,ks))O li I Post t.
Proof.
 intros pc po pi ip A f ks o O li I Post t Outside Bind Local API.
 apply task_sim.
 - intros Cf Ms Mf cst cst' ofull Os o2 OO Inv JM JO Low.
   destruct(V293_client_nil_call_low _ _ _ _ A _ _ _ _ _ _ _ OO _ Outside Low)
   as[Same[Code Match]];subst ofull Cf.
   exists(curs(hapi_code(spec_seq sched(spec_done None))),(kenil,ks));
   exists OO;exists o;exists Ms;exists O;exists Os.
   split.
   + eapply ht_starS;[exact Match| ];eapply ht_starS;
     [apply V293_client_nil_api_enter;exact Bind|apply ht_starO].
   + split;[exact JM| ];split;[exact JO| ];split;[exact Inv| ];split;assumption.
 - intros Cf Ms Mf cst cst' ofull Os o2 OO ev Inv JM JO Low.
   inversion Low;subst;eapply False_ind;eapply V293_client_nil_call_no_event;eassumption.
 - intros Ms k x Os OO E;discriminate E.
 - intros Ms Os OO(v&E);discriminate E.
 - intros cst o2 Ms Os Mf OO Of OOO NE NS NI NF Inv JM JO JO' Bad.
   eapply V293_client_nil_call_abort;eassumption.
 - intros Ms Os e1 e2 e3 k OO E;discriminate E.
 - intros Ms Os e k OO E;discriminate E.
Qed.

Lemma V293_client_nil_call_outside : forall f ks pu,
 V293_skip_client_state(SKIP,(kenil,ks)) ->
 ~InOS(curs(scall f nil),(kenil,ks))pu.
Proof.
 intros f ks pu Cases Inside.
 eapply V293_skip_client_not_os;[exact Cases| ].
 destruct Inside as(c&ke&ks'&E&Ctx);inversion E;subst.
 do 3 eexists;split;[reflexivity| ].
 destruct Ctx as[(f'&vl&fc&tl&Bad&Lookup)|Ctx];[discriminate Bad|right;exact Ctx].
Qed.

Section ClientCall.
Variables br bg bp bt bc bh bo bk bn bl bu : block.
Variable rest : list(addr*type).
Variable target : var.
Variable t : tid.
Variable nc : nat.
Variable oldtarget : val.
Variable c : int32.
Let Cells:=((bc,0%Z),Tint8)::((bh,0%Z),Tint8)::((bk,0%Z),Tint32)::
 (V293_array_cells bt 0%Z 1%Z Tint8(length V293_ready_table)++
 (((bn,0%Z),Tint8)::((bl,0%Z),Tint8)::((bu,0%Z),Tint8)::rest)).
Let G:=V293_ready_storage_inv br bg bp target V293_tcb_type Cells.

Theorem V293_exit_client_call_TaskSim : forall pc po pi ip A ge M ir ci O op
 table high current counter f caller tail saved
 helper unmap group rows y oldhigh tasks running nesting lock n,
 getsched(pc,A)=V293_scheduler ->
 fst(fst A)f=Some((fun _:vallist=>spec_seq sched(spec_done None)),(Tvoid,nil)) ->
 po f=Some(V293_exit_boundary_function running nesting lock saved table high target current counter helper
 (V293_interrupt_handoff high current target)) ->
 V293_skip_client_state(SKIP,(kenil,tail)) ->
 po helper=Some(V293_OSSchedNew_function unmap group rows high y) ->
 y<>unmap ->y<>group ->y<>rows ->y<>high ->
 get ge unmap=Some(bt,Tarray Tint8 256) ->get ge group=Some(bg,Tint8) ->
 get ge rows=Some(br,Tarray Tint8 2) ->get ge high=Some(bh,Tint8) ->
 saved<>table ->saved<>target ->saved<>high ->saved<>current ->saved<>counter ->
 get ge table=Some(bp,Tarray(Tptr V293_tcb_type)13) ->
 get ge current=Some(bc,Tint8) ->get ge counter=Some(bk,Tint32) ->
 get ge target=Some(bo,Tptr V293_tcb_type) ->
 get O abstcblsid=Some(abstcblist tasks) ->
 V293_current_task tasks t nc ->~V293_highest_ready tasks t ->
 n<=1 ->saved<>running ->saved<>nesting ->saved<>lock ->
 get ge running=Some(bu,Tint8) ->get ge nesting=Some(bn,Tint8) ->get ge lock=Some(bl,Tint8) ->
 (ge,caller,M,ir,(false,nil,ci),O,op)|=V293_exit_active_resource br bg bp bt bc bh bo bk bn bl bu rest t nc oldtarget c n oldhigh ->
 TaskSim(pc,(po,pi,ip))
 (curs(scall f nil),(kenil,tail))
 (ge,caller,M,ir,(false,nil,ci))
 (pc,A)(curs(scall f nil),(kenil,tail))O V293_shared_li G
 (fun st=>satp(fst st)(snd st)(RDYINV G t **LINV V293_shared_li t nil))t.
Proof.
 intros pc po pi ip A ge M ir ci O op table high current counter f caller tail saved
 helper unmap group rows y oldhigh tasks running nesting lock n Sched APIBind Bind Cases Helper YU YG YR YH GU GG GR GH
 ST SO SH SC SK TG CG KG OG Map Current NotHighest Bound SU SN SL UG NG LG Held.
 eapply V293_client_nil_call_bridge.
 - apply V293_client_nil_call_outside;exact Cases.
 - exact APIBind.
 - eapply V293_pending_local with(op:=op);eapply V293_exit_active_current;exact Held.
 - unfold G,Cells;eapply V293_exit_active_call_TaskSim with(op:=op)(nc:=nc)
   (oldtarget:=oldtarget)(c:=c)(oldhigh:=oldhigh)(tasks:=tasks)
   (unmap:=unmap)(group:=group)(rows:=rows)(y:=y);eassumption.
Qed.
End ClientCall.
