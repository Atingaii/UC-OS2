(* One stack Hook entry can expose several exact logical instances.  Transport
   changes only logical call arguments, never the statement, state assertions,
   return assertion or physical argument vector.  No new inference rule. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateRejectInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateSuccessInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateEmptyInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TCBUnifiedInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TCBSnapshotInternal.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.certiucos.v293.proofs.V293TCBSuccessInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEmptyInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateStackCall.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateStackSuccess.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateStackEntry.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateTCBCall.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtFunction.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitFunction.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition V293_spec_instances (old new:funspec) : Prop :=
 forall f fp fq tp tl, old f=Some(fp,fq,(tp,tl)) ->
 exists np nq instantiate,
 new f=Some(np,nq,(tp,tl)) /\
 (retpost fq -> retpost nq) /\
 (forall vl (lg:list logicvar) tid, getasrt(np vl (instantiate lg) tid)=getasrt(fp vl lg tid)) /\
 (forall vl result lg tid,
   getasrt(nq vl result (instantiate lg) tid)=getasrt(fq vl result lg tid)).

Lemma V293_InfRules_spec_instances : forall old sd li I r ri pre body post tid,
 InfRules old sd li I r ri pre body post tid ->
 forall new, V293_spec_instances old new ->
 InfRules new sd li I r ri pre body post tid.
Proof.
 intros old sd li I r ri pre body post tid Proof.
 induction Proof;intros New Embed;try solve[econstructor;eauto].
 - destruct(Embed _ _ _ _ _ H0)as[np[nq[inst[Lookup[Ret[PreEq PostEq]]]]]].
   eapply conseq_rule with(q:=EX v,POST[nq,vl,v,inst logicl,t] ** p).
   + intros s Hs;exact Hs.
   + intros s[v Hs]. exists v. rewrite PostEq in Hs. exact Hs.
   + eapply call_rule with(pre:=np)(post:=nq)(logicl:=inst logicl)(vl:=vl)(tp:=tp)(tl:=tl).
     * exact H.
     * exact Lookup.
     * rewrite PreEq;exact H1.
     * exact H2.
     * exact H3.
     * rewrite PreEq;exact H4.
     * intros s[v Hs]. apply H5. exists v. rewrite PostEq in Hs;exact Hs.
 - destruct(Embed _ _ _ _ _ H1)as[np[nq[inst[Lookup[Ret[PreEq PostEq]]]]]].
   eapply conseq_rule with(q:=EX v,POST[nq,vl,Some v,inst logicl,t] ** PV l @ tp|->v ** p).
   + intros s Hs;exact Hs.
   + intros s[v Hs]. exists v. rewrite PostEq in Hs;exact Hs.
   + eapply calle_rule with(pre:=np)(post:=nq)(logicl:=inst logicl)(vl:=vl)(tp:=tp)(tl:=tl)(v':=v').
     * exact H.
     * apply Ret;exact H0.
     * exact Lookup.
     * rewrite PreEq;exact H2.
     * exact H3.
     * exact H4.
     * exact H5.
     * rewrite PreEq;exact H6.
     * intros s[v Hs]. apply H7. exists v. rewrite PostEq in Hs;exact Hs.
 - destruct(Embed _ _ _ _ _ H1)as[np[nq[inst[Lookup[Ret[PreEq PostEq]]]]]].
   eapply conseq_rule with(q:=EX v,POST[nq,vl,Some v,inst logicl,tid] ** LV x @ t|->v ** p).
   + intros s Hs;exact Hs.
   + intros s[v Hs]. exists v. rewrite PostEq in Hs;exact Hs.
   + eapply calle_rule_lvar with(pre:=np)(post:=nq)(logicl:=inst logicl)(vl:=vl)(tp:=tp)(tl:=tl)(v':=v').
     * exact H.
     * apply Ret;exact H0.
     * exact Lookup.
     * rewrite PreEq;exact H2.
     * exact H3.
     * exact H4.
     * rewrite PreEq;exact H5.
     * intros s[v Hs]. apply H6. exists v. rewrite PostEq in Hs;exact Hs.
Qed.

(* The Boolean is a proof-only resource-instance tag, not a C branch oracle.
   Both alternatives still own the exact memory deciding the real C guards. *)
Definition V293_create_stack_cases_fpre (empty ready:fpre) : fpre :=
 fun vl lg tid=>match lg with
 | logic_ie false::tail=>empty vl tail tid
 | logic_ie true::tail=>ready vl tail tid
 | _=>@mkfunasrt Afalse Logic.I
 end.
Definition V293_create_stack_cases_fpost (empty ready:fpost) : fpost :=
 fun vl result lg tid=>match lg with
 | logic_ie false::tail=>empty vl result tail tid
 | logic_ie true::tail=>ready vl result tail tid
 | _=>@mkfunasrt Afalse Logic.I
 end.
Lemma V293_create_stack_cases_retpost : forall empty ready,
 retpost empty -> retpost ready ->
 retpost(V293_create_stack_cases_fpost empty ready).
Proof.
 intros empty ready Empty Ready s vl result lg tid H.
 destruct lg as [ | tag tail];[contradiction| ].
 destruct tag as [x|x|enabled|x|x|x|x|x|x|x|x|x|x];try contradiction. destruct enabled;[eapply Ready|eapply Empty];exact H.
Qed.
Definition V293_spec_replace (Spec:funspec) f entry : funspec :=
 fun name=>if Z.eq_dec name f then Some entry else Spec name.
Lemma V293_create_stack_cases_embed : forall Spec hook ep eq rp rq tp tl,
 Spec hook=Some(V293_create_stack_cases_fpre ep rp,
 V293_create_stack_cases_fpost eq rq,(tp,tl)) ->
 retpost eq -> retpost rq -> forall ready:bool,
 V293_spec_instances
 (V293_spec_replace Spec hook
   ((if ready then rp else ep),(if ready then rq else eq),(tp,tl))) Spec.
Proof.
 intros Spec hook ep eq rp rq tp tl Hook Empty Ready branch f fp fq rt args Lookup.
 unfold V293_spec_replace in Lookup. destruct(Z.eq_dec f hook)as[Same|Different].
 - subst f. inversion Lookup;subst fp fq rt args.
   exists(V293_create_stack_cases_fpre ep rp).
   exists(V293_create_stack_cases_fpost eq rq).
   exists(fun lg=>logic_ie branch::lg). split;[exact Hook| ].
   split;[intro;apply V293_create_stack_cases_retpost;assumption| ].
   split;intros;destruct branch;reflexivity.
 - exists fp. exists fq. exists(fun lg:list logicvar=>lg).
   split;[exact Lookup| ]. split;[auto| ]. split;intros;reflexivity.
Qed.

Lemma V293_create_guarded_builder_rule : forall P f Spec sd li I tid body vl lg
 (condition:Prop) (fp:fpre) (fq:fpost) pre post,
 (condition -> forall p q, Some p=BuildPreI P f vl lg fp tid ->
  Some q=BuildRetI P f vl lg fq tid ->
  InfRules Spec sd li I q Afalse p body Afalse tid) ->
 Some pre=BuildPreI P f vl lg (V293_tcb_guard_fpre condition fp) tid ->
 Some post=BuildRetI P f vl lg (V293_tcb_guard_fpost condition fq) tid ->
 InfRules Spec sd li I post Afalse pre body Afalse tid.
Proof.
 intros P f Spec sd li I tid body vl lg condition fp fq pre post Contract Pre Post.
 unfold BuildPreI in Pre.
 destruct(P f) as [[[[rt d1] d2] b] | ] eqn:Code;[ |discriminate].
 destruct(dl_vl_match d1 (rev vl)) eqn:Typed;[ |discriminate].
 destruct(buildp(revlcons d1 d2)vl) as [locals | ] eqn:Cells;[ |discriminate].
 cbn [V293_tcb_guard_fpre getasrt] in Pre. inversion Pre;subst pre.
 unfold BuildRetI in Post. rewrite Code in Post.
 destruct(buildq(revlcons d1 d2)) as [returned | ] eqn:ReturnCells;[ |discriminate].
 cbn [V293_tcb_guard_fpost getasrt] in Post. inversion Post;subst post.
 eapply conseq_rule with (p:=(locals ** getasrt(fp(rev vl)lg tid) **
 A_dom_lenv(getlenvdom(revlcons d1 d2))) ** [|condition|]).
 - intros s H. clear -H. sep auto.
 - intros s H;exact H.
 - apply pure_split_rule. intro Saved.
   eapply r_conseq_rule with (r:=fun result=>returned ** getasrt(fq(rev vl)result lg tid) **
     A_dom_lenv(getlenvdom(revlcons d1 d2))).
   + intros result s H.
     assert(K:s |= [|condition|] ** (returned ** getasrt(fq(rev vl)result lg tid) **
       A_dom_lenv(getlenvdom(revlcons d1 d2)))).
     { apply astar_l_apure_intro;[exact H|exact Saved]. }
     clear -K. sep auto.
   + intros s H;exact H.
   + apply (Contract Saved).
     * unfold BuildPreI. rewrite Code,Typed,Cells. reflexivity.
     * unfold BuildRetI. rewrite Code,ReturnCells. reflexivity.
Qed.

Section TaskCreateUnion.
Variables (table bnest breserved bg bt bh bgrp br bn oldblock brun:block).
Variables (base oldbase:Z) (old:Z->val) (present:bool).
Variables (p g row n nesting:nat) (occupied:addrval).
Variables (oldprev oldback next top bottom identity size ext options argv inputtop:val).
Variable target:Z.
Variables (R Rbefore:asrt) (aop:absop) (isr:isr) (is:is) (cs:cs).
Variables (good:GoodFunAsrt R) (gb:GoodFunAsrt Rbefore).
Variable tid:tid.

Definition V293_create_union_tcb_pre := V293_tcb_snapshot_fpre(Vptr(bt,Int.repr base))
 (V293_tcb_empty_fpre bg R aop isr is cs good)
 (V293_tcb_success_fpre table(Vptr(breserved,Int.zero))bg bt base old p top bottom identity size ext options next
 bh bgrp br bn oldblock oldbase present oldprev g row n oldback R aop isr is cs good).
Definition V293_create_union_tcb_post := V293_tcb_snapshot_fpost(Vptr(bt,Int.repr base))
 (V293_tcb_empty_fpost bg R aop isr is cs good)
 (V293_tcb_success_fpost table bg bt base p top bottom identity size ext options next
 bh bgrp br bn oldblock oldbase present g row n R aop isr is cs good).
Definition V293_create_union_stack_empty_pre :=
 V293_create_stack_fpre bg Rbefore aop isr is cs gb(V293_create_stack_values target argv inputtop options).
Definition V293_create_union_stack_empty_post :=
 V293_create_stack_fpost bg R aop isr is cs good(V293_create_stack_values target argv inputtop options)top.
Definition V293_create_union_stack_ready_pre :=
 V293_create_stack_resource_fpre
 (@mkfunasrt
 (V293_tcb_success_external table bg bh bgrp br bn
 (V293_tcb_success_pre_owned table(Vptr(breserved,Int.zero))bg bt base old next
 bh bgrp br bn oldblock oldbase present p oldprev g row n oldback)R aop isr is cs)
 (V293_tcb_success_external_good table bg bh bgrp br bn
 (V293_tcb_success_pre_owned table(Vptr(breserved,Int.zero))bg bt base old next
 bh bgrp br bn oldblock oldbase present p oldprev g row n oldback)R aop isr is cs good))
 (V293_create_stack_values target argv inputtop options).
Definition V293_create_union_stack_ready_post := V293_create_stack_resource_fpost
 (V293_create_union_tcb_pre(V293_tcb_success_arguments p top bottom identity size ext options)
 [logic_val(Vptr(bt,Int.repr base))]tid)
 (V293_create_stack_values target argv inputtop options)top.
Definition V293_create_union_stack_pre := V293_create_stack_cases_fpre
 V293_create_union_stack_empty_pre V293_create_union_stack_ready_pre.
Definition V293_create_union_stack_post := V293_create_stack_cases_fpost
 V293_create_union_stack_empty_post V293_create_union_stack_ready_post.

Definition V293_create_union_reject_pre k := V293_tcb_guard_fpre
 (V293_create_rejection_valid k p nesting)
 (V293_create_reject_fpre k table bnest p nesting occupied target argv inputtop
 identity bottom size ext options Rbefore aop isr is cs gb).
Definition V293_create_union_reject_post k := V293_tcb_guard_fpost
 (V293_create_rejection_valid k p nesting)
 (V293_create_reject_fpost k table bnest p nesting occupied Rbefore aop isr is cs gb).
Definition V293_create_allocation_valid := p<13 /\
 V293_stack_argument_valid argv inputtop options /\
 V293_tcb_init_values_valid top bottom identity size ext options.
Definition V293_create_union_empty_pre := V293_tcb_guard_fpre V293_create_allocation_valid
 (V293_create_empty_fpre table bnest breserved bg p target argv inputtop identity bottom size ext options
 Rbefore aop isr is cs gb).
Definition V293_create_union_empty_post := V293_tcb_guard_fpost V293_create_allocation_valid
 (V293_create_empty_fpost table bnest breserved bg p R aop isr is cs good).
Definition V293_create_union_ready_pre := V293_tcb_guard_fpre V293_create_allocation_valid
 (V293_create_success_fpre table bg bh bgrp br bn bnest breserved brun
 (V293_tcb_success_pre_owned table Vnull bg bt base old next bh bgrp br bn oldblock oldbase
 present p oldprev g row n oldback)p target argv inputtop identity bottom size ext options
 R aop isr is cs good).
Definition V293_create_union_ready_post := V293_tcb_guard_fpost V293_create_allocation_valid
 (V293_create_success_fpost bnest breserved brun V293_create_union_tcb_post
 (V293_tcb_success_arguments p top bottom identity size ext options)(Vptr(bt,Int.repr base))).

(* A spatial disjunction, not a ghost selector for the caller's path. *)
Definition V293_create_unified_fpre : fpre := V293_tcb_union_fpre
 (V293_create_union_reject_pre V293_create_bad_priority)
 (V293_tcb_union_fpre(V293_create_union_reject_pre V293_create_from_isr)
 (V293_tcb_union_fpre(V293_create_union_reject_pre V293_create_occupied_priority)
 (V293_tcb_union_fpre V293_create_union_empty_pre V293_create_union_ready_pre))).
Definition V293_create_unified_fpost : fpost := V293_tcb_union_fpost
 (V293_create_union_reject_post V293_create_bad_priority)
 (V293_tcb_union_fpost(V293_create_union_reject_post V293_create_from_isr)
 (V293_tcb_union_fpost(V293_create_union_reject_post V293_create_occupied_priority)
 (V293_tcb_union_fpost V293_create_union_empty_post V293_create_union_ready_post))).

Lemma V293_create_union_stack_return : retpost V293_create_union_stack_post.
Proof.
 apply V293_create_stack_cases_retpost.
 - apply V293_create_stack_retpost.
 - apply V293_create_stack_resource_retpost.
Qed.

(* The public contract requires only one lookup per called symbol.  Earlier
   branch contracts are transported into this same Spec, not assumed. *)
Theorem V293_OSTaskCreateExt_unified_internal_contract : forall P creator Spec sd li I
 f hook sched vl lg pre post,
 GoodFrm Rbefore -> GoodFrm R ->
 (Rbefore ==> CurLINV li tid) -> (R ==> CurLINV li tid) -> hook<>f ->
 Spec hook=Some(V293_create_union_stack_pre,V293_create_union_stack_post,
 (Tptr Tint32,rev V293_stack_argument_types)) ->
 Spec f=Some(V293_create_union_tcb_pre,V293_create_union_tcb_post,
 (Tint8,rev V293_TCBInit_argument_types)) ->
 P creator=Some(V293_CreateExt_function 92%Z 99%Z 97%Z 98%Z sched hook f) ->
 Some pre=BuildPreI P creator vl lg V293_create_unified_fpre tid ->
 Some post=BuildRetI P creator vl lg V293_create_unified_fpost tid ->
 InfRules Spec sd li I post Afalse pre
 (V293_CreateExt_body 92%Z 99%Z 97%Z 98%Z sched hook f) Afalse tid.
Proof.
 intros P creator Spec sd li I f hook sched vl lg pre post
 BeforeFrame Frame HBefore HR Distinct Hook TCB Code Pre Post.
 assert(Reject:forall k rp rq,
 Some rp=BuildPreI P creator vl lg(V293_create_union_reject_pre k)tid ->
 Some rq=BuildRetI P creator vl lg(V293_create_union_reject_post k)tid ->
 InfRules Spec sd li I rq Afalse rp
 (V293_CreateExt_body 92%Z 99%Z 97%Z 98%Z sched hook f)Afalse tid).
 { intros k rp rq RP RQ.
   unfold V293_create_union_reject_pre in RP. unfold V293_create_union_reject_post in RQ.
   eapply V293_create_guarded_builder_rule with(P:=P)(f:=creator)(vl:=vl)(lg:=lg);[ |exact RP|exact RQ].
   intros Range bp bq BP BQ.
   eapply V293_OSTaskCreateExt_rejection_internal_contract with(good:=gb);
   eassumption. }
 unfold V293_create_unified_fpre in Pre. unfold V293_create_unified_fpost in Post.
 eapply V293_tcb_union_builder_rule;[apply Reject| |exact Pre|exact Post].
 intros p1 q1 P1 Q1.
 eapply V293_tcb_union_builder_rule;[apply Reject| |exact P1|exact Q1].
 intros p2 q2 P2 Q2.
 eapply V293_tcb_union_builder_rule;[apply Reject| |exact P2|exact Q2].
 intros p3 q3 P3 Q3.
 eapply V293_tcb_union_builder_rule;[ | |exact P3|exact Q3].
 - intros ep eq EP EQ.
   unfold V293_create_union_empty_pre in EP. unfold V293_create_union_empty_post in EQ.
   eapply V293_create_guarded_builder_rule with(P:=P)(f:=creator)(vl:=vl)(lg:=lg);[ |exact EP|exact EQ].
   intros [Range[StackValid Valid]] bp bq BP BQ.
   let Old:=constr:(V293_spec_replace Spec hook
    (V293_create_union_stack_empty_pre,V293_create_union_stack_empty_post,
     (Tptr Tint32,rev V293_stack_argument_types))) in
   eapply V293_InfRules_spec_instances with(old:=Old).
   + eapply V293_OSTaskCreateExt_empty_internal_contract with
     (good:=good)(gb:=gb)(slot:=Vptr(breserved,Int.zero))(bt:=bt)(base:=base)(old:=old)(next:=next)
     (bh:=bh)(bgrp:=bgrp)(br:=br)(bn:=bn)(oldblock:=oldblock)(oldbase:=oldbase)
     (present:=present)(oldprev:=oldprev)(g:=g)(row:=row)(n:=n)(oldback:=oldback).
     * exact BeforeFrame.
     * exact Frame.
     * exact Range.
     * exact StackValid.
     * exact HBefore.
     * exact Valid.
     * exact HR.
     * unfold V293_spec_replace. destruct(Z.eq_dec hook hook);[reflexivity|contradiction].
     * unfold V293_spec_replace. destruct(Z.eq_dec f hook);[congruence|exact TCB].
     * exact Code.
     * exact BP.
     * exact BQ.
   + apply V293_create_stack_cases_embed with(ready:=false)
     (rp:=V293_create_union_stack_ready_pre)(rq:=V293_create_union_stack_ready_post).
     * exact Hook.
     * apply V293_create_stack_retpost.
     * apply V293_create_stack_resource_retpost.
 - intros rp rq RP RQ.
   unfold V293_create_union_ready_pre in RP. unfold V293_create_union_ready_post in RQ.
   eapply V293_create_guarded_builder_rule with(P:=P)(f:=creator)(vl:=vl)(lg:=lg);[ |exact RP|exact RQ].
   intros [Range[StackValid Valid]] bp bq BP BQ.
   let Old:=constr:(V293_spec_replace Spec hook
    (V293_create_union_stack_ready_pre,V293_create_union_stack_ready_post,
     (Tptr Tint32,rev V293_stack_argument_types))) in
   eapply V293_InfRules_spec_instances with(old:=Old).
   + eapply V293_OSTaskCreateExt_success_internal_contract with(good:=good)
     (bt:=bt)(base:=base)(old:=old)(next:=next)(bh:=bh)(bgrp:=bgrp)(br:=br)(bn:=bn)
     (oldblock:=oldblock)(oldbase:=oldbase)(present:=present)(oldprev:=oldprev)
     (g:=g)(row:=row)(n:=n)(oldback:=oldback).
     * exact Frame.
     * exact Range.
     * exact StackValid.
     * exact Valid.
     * exact HR.
     * unfold V293_spec_replace. destruct(Z.eq_dec hook hook);[reflexivity|contradiction].
     * unfold V293_spec_replace. destruct(Z.eq_dec f hook);[congruence|exact TCB].
     * exact Code.
     * exact BP.
     * exact BQ.
   + apply V293_create_stack_cases_embed with(ready:=true)
     (ep:=V293_create_union_stack_empty_pre)(eq:=V293_create_union_stack_empty_post).
     * exact Hook.
     * apply V293_create_stack_retpost.
     * apply V293_create_stack_resource_retpost.
Qed.
End TaskCreateUnion.
Print Assumptions V293_OSTaskCreateExt_unified_internal_contract.

