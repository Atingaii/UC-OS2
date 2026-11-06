(* Actual pointer-argument calls from the configured OSIntExit. The caller's
   local name is a frame; callee resources can change and contain the saved
   cell, interrupt state and token. No external implementation is supplied. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.code.V293OSIntExit.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope nat_scope.

Definition V293_saved_pointer_fpre (owner:tid) (resource:addrval -> asrt)
 (good:forall address,GoodFunAsrt(resource address)) : fpre :=
 fun vl lg t => match vl with
 | [Vptr address] => @mkfunasrt
     ([|lg=[] /\ t=owner|] ** resource address)(conj I(good address))
 | _ => @mkfunasrt Afalse I
 end.
Definition V293_saved_pointer_fpost (owner:tid) (resource:addrval -> asrt)
 (good:forall address,GoodFunAsrt(resource address)) : fpost :=
 fun vl result lg t => match vl with
 | [Vptr address] => @mkfunasrt
     ([|lg=[] /\ t=owner /\ result=None|] ** resource address)(conj I(good address))
 | _ => @mkfunasrt Afalse I
 end.

(* Both the value and its pointer type are obtained from the actual binding,
   not assumed as an expression-evaluation premise. *)
Lemma V293_saved_pointer_argument : forall saved bs R,
 Alvarenv saved Tint32(bs,0%Z) ** R ==>
 Rvl [eaddrof(evar saved)] @ [Tptr Tint32] == [Vptr(bs,Int.zero)].
Proof.
 intros saved bs R s Held.
 destruct(V293_time_binding_star true saved bs R s Held)as[A T].
 change(evalval(eaddrof(evar saved))(getsmem s)=Some(Vptr(bs,Int.zero)) /\
  evaltype(eaddrof(evar saved))(getsmem s)=Some(Tptr Tint32) /\
  True /\ Vptr(bs,Int.zero)<>Vundef).
 destruct s as [[[[[[ge le] M] ir] aux] O] op].
 cbn[getsmem get_smem]in A,T|-*.
 assert(AT:evaltype(eaddrof(evar saved))(ge,le,M)=Some(Tptr Tint32)).
 { change(match evaltype(evar saved)(ge,le,M) with Some tp=>Some(Tptr tp)|None=>None end=Some(Tptr Tint32)).
   rewrite T;reflexivity. }
 split.
 - change(match evaltype(eaddrof(evar saved))(ge,le,M) with
   |Some _=>evaladdr(evar saved)(ge,le,M)|None=>None end=Some(Vptr(bs,Int.zero))).
   rewrite AT;exact A.
 - split;[exact AT|split;[exact I|discriminate]].
Qed.

Theorem V293_saved_pointer_call : forall Spec sd li I r ri tid callee saved bs frame
 (before after:addrval -> asrt)
 (before_good:forall address,GoodFunAsrt(before address))
 (after_good:forall address,GoodFunAsrt(after address)),
 GoodFrm frame ->
 (before(bs,Int.zero) ==> CurLINV li tid) ->
 (after(bs,Int.zero) ==> CurLINV li tid) ->
 Spec callee=Some(V293_saved_pointer_fpre tid before before_good,
  V293_saved_pointer_fpost tid after after_good,(Tvoid,[Tptr Tint32])) ->
 InfRules Spec sd li I r ri
 (before(bs,Int.zero) ** (Alvarenv saved Tint32(bs,0%Z) ** frame))
 (scall callee [eaddrof(evar saved)])
 (after(bs,Int.zero) ** (Alvarenv saved Tint32(bs,0%Z) ** frame))tid.
Proof.
 intros Spec sd li I r ri tid callee saved bs frame before after BG AG Frame BL AL Lookup.
 eapply conseq_rule with(q:=EX result:option val,
   getasrt(V293_saved_pointer_fpost tid after AG [Vptr(bs,Int.zero)]result [] tid) **
   (Alvarenv saved Tint32(bs,0%Z) ** frame)).
 - intros s H;exact H.
 - intros s[result H];cbn[V293_saved_pointer_fpost getasrt]in H;clear -H;sep auto.
 - eapply call_rule with(pre:=V293_saved_pointer_fpre tid before BG)
   (post:=V293_saved_pointer_fpost tid after AG)(vl:=[Vptr(bs,Int.zero)])
   (logicl:=[])(tp:=Tvoid)(tl:=[Tptr Tint32])
   (p:=Alvarenv saved Tint32(bs,0%Z) ** frame).
   + cbn[GoodFrm];tauto.
   + exact Lookup.
   + intros s H;cbn[V293_saved_pointer_fpre getasrt];clear -H;sep auto.
   + intros s H. eapply V293_saved_pointer_argument.
     clear -H;sep auto.
   + reflexivity.
   + cbn[V293_saved_pointer_fpre getasrt]. apply V293_star_CurLINV_r;exact BL.
   + intros s[result H];cbn[V293_saved_pointer_fpost getasrt]in H.
     eapply V293_star_CurLINV_r;[exact AL|exact H].
Qed.

(* The cell moves into the callee resource. Its local binding does not. *)
Definition V293_saved_pointer_resource aop value shared address : asrt :=
 <||aop||> ** (PV address @ Tint32 |-> value ** shared).
Lemma V293_saved_pointer_resource_good : forall aop value shared,
 GoodFunAsrt shared -> forall address,
 GoodFunAsrt(V293_saved_pointer_resource aop value shared address).
Proof. intros;cbn[V293_saved_pointer_resource Aptrmapsto GoodFunAsrt];tauto. Qed.
Lemma V293_saved_pointer_resource_local : forall aop value shared address li tid,
 (shared ==> CurLINV li tid) ->
 V293_saved_pointer_resource aop value shared address ==> CurLINV li tid.
Proof.
 intros aop value shared address li tid Local. unfold V293_saved_pointer_resource.
 eapply V293_star_CurLINV_r with(p:=<||aop||>).
 eapply V293_star_CurLINV_r with(p:=PV address @ Tint32 |-> value);exact Local.
Qed.
Lemma V293_saved_pointer_local_excluded : forall saved bs,
 ~GoodFunAsrt(Alvarenv saved Tint32(bs,0%Z)).
Proof. intros saved bs H;exact H. Qed.

Theorem V293_OSIntExit_saved_initialize : forall Spec sd li I r ri tid aop shared frame saved bs old,
 (shared ==> CurLINV li tid) ->
 InfRules Spec sd li I r ri
 (<||aop||> ** (V293_time_cell true saved bs old ** (shared ** frame)))
 (sassign(evar saved)(econst32 Int.zero))
 (V293_saved_pointer_resource aop(Vint32 Int.zero)shared(bs,Int.zero) **
  (Alvarenv saved Tint32(bs,0%Z) ** frame))tid.
Proof.
 intros Spec sd li I r ri tid aop shared frame saved bs old Local.
 eapply conseq_rule with(q:=<||aop||> **
  (V293_time_cell true saved bs(Vint32 Int.zero) ** (shared ** frame))).
 - intros s H;exact H.
 - unfold V293_time_cell,V293_time_binding,V293_saved_pointer_resource.
   intros s Held;clear -Held;sep auto.
 - apply V293_time_zero. apply V293_star_CurLINV_l;assumption.
Qed.

(* This is exactly the enabled branch inside the original body. The only
   statement proof supplied by the caller is the actual nesting/dispatch
   middle; enter and exit are discharged by the pointer call rule. Contract
   lookup is not evidence of the external callee's implementation. *)
Theorem V293_OSIntExit_critical_calls : forall Spec sd li I r ri tid saved bs frame
 nesting lock table high target current counter sched_id enter exit int_switch
 (entry acquired leaving restored:addrval -> asrt)
 (EG:forall address,GoodFunAsrt(entry address))
 (AG:forall address,GoodFunAsrt(acquired address))
 (LG:forall address,GoodFunAsrt(leaving address))
 (RG:forall address,GoodFunAsrt(restored address)),
 GoodFrm frame ->
 (entry(bs,Int.zero) ==> CurLINV li tid) ->
 (acquired(bs,Int.zero) ==> CurLINV li tid) ->
 (leaving(bs,Int.zero) ==> CurLINV li tid) ->
 (restored(bs,Int.zero) ==> CurLINV li tid) ->
 Spec enter=Some(V293_saved_pointer_fpre tid entry EG,
  V293_saved_pointer_fpost tid acquired AG,(Tvoid,[Tptr Tint32])) ->
 Spec exit=Some(V293_saved_pointer_fpre tid leaving LG,
  V293_saved_pointer_fpost tid restored RG,(Tvoid,[Tptr Tint32])) ->
 InfRules Spec sd li I r ri
 (acquired(bs,Int.zero) ** (Alvarenv saved Tint32(bs,0%Z) ** frame))
 (V293_OSIntExit_nesting_dispatch nesting lock
   (V293_OSIntExit_dispatch table high target current counter sched_id int_switch))
 (leaving(bs,Int.zero) ** (Alvarenv saved Tint32(bs,0%Z) ** frame))tid ->
 InfRules Spec sd li I r ri
 (entry(bs,Int.zero) ** (Alvarenv saved Tint32(bs,0%Z) ** frame))
 (sseq(scall enter [eaddrof(evar saved)])
   (sseq(V293_OSIntExit_nesting_dispatch nesting lock
     (V293_OSIntExit_dispatch table high target current counter sched_id int_switch))
     (scall exit [eaddrof(evar saved)])))
 (restored(bs,Int.zero) ** (Alvarenv saved Tint32(bs,0%Z) ** frame))tid.
Proof.
 intros Spec sd li I r ri tid saved bs frame nesting lock table high target current counter
 sched_id enter exit int_switch entry acquired leaving restored EG AG LG RG F EL AL LL RL E X Middle.
 eapply seq_rule with(p':=acquired(bs,Int.zero) ** (Alvarenv saved Tint32(bs,0%Z) ** frame)).
 - eapply V293_saved_pointer_call with(before_good:=EG)(after_good:=AG);eassumption.
 - eapply seq_rule with(p':=leaving(bs,Int.zero) ** (Alvarenv saved Tint32(bs,0%Z) ** frame));[exact Middle| ].
   eapply V293_saved_pointer_call with(before_good:=LG)(after_good:=RG);eassumption.
Qed.
