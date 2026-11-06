(* Actual TaskCreateExt call site: C-order argument reads and err receiver. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.proofs.V293TCBSnapshotInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TCBSuccessInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEmptyInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TCBHookCall.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitFunction.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtCalls.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

(* These are CALLER identifiers. In particular 108 holds a stack pointer,
   not the callee's 108 TCB local. No caller-local address enters fpre/fpost. *)
Definition V293_create_tcb_arguments p top bottom identity size ext options F :=
 LV 101%Z @ Tint8 |-> V293_byteval p **
 LV 108%Z @ (Tptr Tint32) |-> top **
 LV 205%Z @ (Tptr Tint32) |-> bottom **
 LV 206%Z @ Tint16 |-> identity **
 LV 207%Z @ Tint32 |-> size **
 LV 208%Z @ (Tptr Tvoid) |-> ext **
 LV 204%Z @ Tint16 |-> options ** F.

Lemma V293_create_tcb_arguments_good : forall p top bottom identity size ext options F,
 GoodFrm F -> GoodFrm(V293_create_tcb_arguments p top bottom identity size ext options F).
Proof.
 intros. unfold V293_create_tcb_arguments,Alvarmapsto,Aptrmapsto.
 cbn [GoodFrm]. repeat split;auto.
Qed.

Theorem V293_create_tcb_arguments_read : forall p top bottom identity size ext options F,
 p<256 -> V293_tcb_init_values_valid top bottom identity size ext options ->
 V293_create_tcb_arguments p top bottom identity size ext options F ==>
 Rvl [evar 101%Z;evar 108%Z;evar 205%Z;evar 206%Z;evar 207%Z;evar 208%Z;evar 204%Z]
 @ (rev V293_TCBInit_argument_types) ==
 V293_tcb_success_arguments p top bottom identity size ext options.
Proof.
 intros p top bottom identity size ext options F Range Valid s Owned.
 unfold V293_tcb_init_values_valid in Valid.
 destruct Valid as [Top [Bottom [Identity [Size [Ext Options]]]]].
 unfold V293_create_tcb_arguments in Owned.
 assert(ReadPrio:s |= Rv(evar 101%Z) @ (Tint8) == (V293_byteval p)).
 { eapply lvar_rv with (perm:=true) (P:=LV 108%Z @ (Tptr Tint32) |-> (top) ** LV 205%Z @ (Tptr Tint32) |-> (bottom) ** LV 206%Z @ (Tint16) |-> (identity) ** LV 207%Z @ (Tint32) |-> (size) ** LV 208%Z @ (Tptr Tvoid) |-> (ext) ** LV 204%Z @ (Tint16) |-> (options) ** F).
   - clear -Owned. sep auto.
   - exact (V293_byte_type p Range). }
 assert(ReadTop:s |= Rv(evar 108%Z) @ (Tptr Tint32) == (top)).
 { eapply lvar_rv with (perm:=true) (P:=LV 101%Z @ (Tint8) |-> (V293_byteval p) ** LV 205%Z @ (Tptr Tint32) |-> (bottom) ** LV 206%Z @ (Tint16) |-> (identity) ** LV 207%Z @ (Tint32) |-> (size) ** LV 208%Z @ (Tptr Tvoid) |-> (ext) ** LV 204%Z @ (Tint16) |-> (options) ** F).
   - clear -Owned. sep auto.
   - exact (Top). }
 assert(ReadBottom:s |= Rv(evar 205%Z) @ (Tptr Tint32) == (bottom)).
 { eapply lvar_rv with (perm:=true) (P:=LV 101%Z @ (Tint8) |-> (V293_byteval p) ** LV 108%Z @ (Tptr Tint32) |-> (top) ** LV 206%Z @ (Tint16) |-> (identity) ** LV 207%Z @ (Tint32) |-> (size) ** LV 208%Z @ (Tptr Tvoid) |-> (ext) ** LV 204%Z @ (Tint16) |-> (options) ** F).
   - clear -Owned. sep auto.
   - exact (Bottom). }
 assert(ReadIdentity:s |= Rv(evar 206%Z) @ (Tint16) == (identity)).
 { eapply lvar_rv with (perm:=true) (P:=LV 101%Z @ (Tint8) |-> (V293_byteval p) ** LV 108%Z @ (Tptr Tint32) |-> (top) ** LV 205%Z @ (Tptr Tint32) |-> (bottom) ** LV 207%Z @ (Tint32) |-> (size) ** LV 208%Z @ (Tptr Tvoid) |-> (ext) ** LV 204%Z @ (Tint16) |-> (options) ** F).
   - clear -Owned. sep auto.
   - exact (Identity). }
 assert(ReadSize:s |= Rv(evar 207%Z) @ (Tint32) == (size)).
 { eapply lvar_rv with (perm:=true) (P:=LV 101%Z @ (Tint8) |-> (V293_byteval p) ** LV 108%Z @ (Tptr Tint32) |-> (top) ** LV 205%Z @ (Tptr Tint32) |-> (bottom) ** LV 206%Z @ (Tint16) |-> (identity) ** LV 208%Z @ (Tptr Tvoid) |-> (ext) ** LV 204%Z @ (Tint16) |-> (options) ** F).
   - clear -Owned. sep auto.
   - exact (Size). }
 assert(ReadExt:s |= Rv(evar 208%Z) @ (Tptr Tvoid) == (ext)).
 { eapply lvar_rv with (perm:=true) (P:=LV 101%Z @ (Tint8) |-> (V293_byteval p) ** LV 108%Z @ (Tptr Tint32) |-> (top) ** LV 205%Z @ (Tptr Tint32) |-> (bottom) ** LV 206%Z @ (Tint16) |-> (identity) ** LV 207%Z @ (Tint32) |-> (size) ** LV 204%Z @ (Tint16) |-> (options) ** F).
   - clear -Owned. sep auto.
   - exact (Ext). }
 assert(ReadOptions:s |= Rv(evar 204%Z) @ (Tint16) == (options)).
 { eapply lvar_rv with (perm:=true) (P:=LV 101%Z @ (Tint8) |-> (V293_byteval p) ** LV 108%Z @ (Tptr Tint32) |-> (top) ** LV 205%Z @ (Tptr Tint32) |-> (bottom) ** LV 206%Z @ (Tint16) |-> (identity) ** LV 207%Z @ (Tint32) |-> (size) ** LV 208%Z @ (Tptr Tvoid) |-> (ext) ** F).
   - clear -Owned. sep auto.
   - exact (Options). }
 cbn [sat getsmem] in ReadPrio,ReadTop,ReadBottom,ReadIdentity,ReadSize,ReadExt,ReadOptions.
 cbn [sat getsmem evalexprlist V293_TCBInit_argument_types rev app V293_tcb_success_arguments].
 tauto.
Qed.

Lemma V293_create_tcb_argument_types : forall p top bottom identity size ext options,
 p<256 -> V293_tcb_init_values_valid top bottom identity size ext options ->
 tl_vl_match (rev V293_TCBInit_argument_types)
 (V293_tcb_success_arguments p top bottom identity size ext options)=true.
Proof.
 intros p top bottom identity size ext options Range Valid.
 unfold V293_tcb_init_values_valid in Valid.
 destruct Valid as [Top [Bottom [Identity [Size [Ext Options]]]]].
 pose proof (V293_byte_type p Range) as Prio.
 change (type_val_match (Tint8) (V293_byteval p)=true) in Prio.
 change (type_val_match (Tptr Tint32) (top)=true) in Top.
 change (type_val_match (Tptr Tint32) (bottom)=true) in Bottom.
 change (type_val_match (Tint16) (identity)=true) in Identity.
 change (type_val_match (Tint32) (size)=true) in Size.
 change (type_val_match (Tptr Tvoid) (ext)=true) in Ext.
 change (type_val_match (Tint16) (options)=true) in Options.
 cbn [tl_vl_match V293_TCBInit_argument_types rev app V293_tcb_success_arguments].
 rewrite Prio,Top,Bottom,Identity,Size,Ext,Options. reflexivity.
Qed.

Lemma V293_create_snapshot_retpost : forall allocated empty ready,
 retpost empty -> retpost ready ->
 retpost(V293_tcb_snapshot_fpost allocated empty ready).
Proof.
 intros allocated empty ready Empty Ready s vl result lg tid H.
 destruct lg as [ | item [ | extra tail]];cbn [V293_tcb_snapshot_fpost getasrt] in H;
 try contradiction.
 destruct item;try contradiction. destruct v;try contradiction.
 - eapply Empty;exact H.
 - cbn [V293_tcb_guard_fpost getasrt] in H.
   apply astar_l_apure_elim in H. eapply Ready;exact(proj2 H).
Qed.

Lemma V293_create_snapshot_pre_linv : forall allocated empty ready vl lg tid li,
 (getasrt(empty vl lg tid) ==> CurLINV li tid) ->
 (getasrt(ready vl lg tid) ==> CurLINV li tid) ->
 getasrt(V293_tcb_snapshot_fpre allocated empty ready vl lg tid) ==> CurLINV li tid.
Proof.
 intros allocated empty ready vl lg tid li Empty Ready s H.
 destruct lg as [ | item [ | extra tail]];cbn [V293_tcb_snapshot_fpre getasrt] in H;
 try contradiction.
 destruct item;try contradiction. destruct v;try contradiction.
 - apply Empty;exact H.
 - cbn [V293_tcb_guard_fpre getasrt] in H.
   apply astar_l_apure_elim in H. apply Ready;exact(proj2 H).
Qed.
Lemma V293_create_snapshot_post_linv : forall allocated empty ready vl result lg tid li,
 (getasrt(empty vl result lg tid) ==> CurLINV li tid) ->
 (getasrt(ready vl result lg tid) ==> CurLINV li tid) ->
 getasrt(V293_tcb_snapshot_fpost allocated empty ready vl result lg tid) ==> CurLINV li tid.
Proof.
 intros allocated empty ready vl result lg tid li Empty Ready s H.
 destruct lg as [ | item [ | extra tail]];cbn [V293_tcb_snapshot_fpost getasrt] in H;
 try contradiction.
 destruct item;try contradiction. destruct v;try contradiction.
 - apply Empty;exact H.
 - cbn [V293_tcb_guard_fpost getasrt] in H.
   apply astar_l_apure_elim in H. apply Ready;exact(proj2 H).
Qed.

(* The only function boundary premise is the actual specification lookup.
   The callee body must still be checked under that SAME Spec for WFIFun. *)
Theorem V293_TaskCreateExt_TCB_snapshot_call : forall Spec sd li I r ri tid f
 table slot bg bt base old p top bottom identity size ext options next
 bh bgrp br bn oldblock oldbase present oldprev g row n oldback R aop isr is cs
 (good:GoodFunAsrt R) F saved olderr,
 GoodFrm F -> p<256 -> V293_tcb_init_values_valid top bottom identity size ext options ->
 (R ==> CurLINV li tid) ->
 let fp:=V293_tcb_snapshot_fpre (Vptr(bt,Int.repr base))
   (V293_tcb_empty_fpre bg R aop isr is cs good)
   (V293_tcb_success_fpre table slot bg bt base old p top bottom identity size ext options next
      bh bgrp br bn oldblock oldbase present oldprev g row n oldback R aop isr is cs good) in
 let fq:=V293_tcb_snapshot_fpost (Vptr(bt,Int.repr base))
   (V293_tcb_empty_fpost bg R aop isr is cs good)
   (V293_tcb_success_fpost table bg bt base p top bottom identity size ext options next
      bh bgrp br bn oldblock oldbase present g row n R aop isr is cs good) in
 Spec f=Some(fp,fq,(Tint8,rev V293_TCBInit_argument_types)) ->
 InfRules Spec sd li I r ri
 (getasrt(fp (V293_tcb_success_arguments p top bottom identity size ext options) [logic_val saved] tid) **
 LV 209%Z @ Tint8 |-> olderr **
 V293_create_tcb_arguments p top bottom identity size ext options F)
 (V293_TaskCreateExt_TCB_call 209%Z f 101%Z 108%Z 205%Z 206%Z 207%Z 208%Z 204%Z)
 (EX result:val,
 [|(saved=Vnull /\ result=Vint32(Int.repr 66)) \/
   (saved=Vptr(bt,Int.repr base) /\ result=Vint32 Int.zero)|] **
 (getasrt(fq (V293_tcb_success_arguments p top bottom identity size ext options) (Some result) [logic_val saved] tid) **
 LV 209%Z @ Tint8 |-> result **
 V293_create_tcb_arguments p top bottom identity size ext options F)) tid.
Proof.
 intros Spec sd li I r ri tid f table slot bg bt base old p top bottom identity size ext options next
 bh bgrp br bn oldblock oldbase present oldprev g row n oldback R aop isr is cs good F saved olderr
 Frame Range Valid HR fp fq Lookup.
 assert(EmptyLINV:V293_tcb_empty_external bg R aop isr is cs ==> CurLINV li tid).
 { unfold V293_tcb_empty_external. do 4 apply V293_star_CurLINV_r. exact HR. }
 assert(ReadyLINV:forall cells,
 V293_tcb_success_external table bg bh bgrp br bn cells R aop isr is cs ==> CurLINV li tid).
 { intro cells. unfold V293_tcb_success_external. apply V293_hook_resource_linv.
   apply V293_star_CurLINV_r. exact HR. }
 assert(Ret:retpost fq).
 { unfold fq. apply V293_create_snapshot_retpost;
   intros st args result ghosts task Owned;
   cbn [V293_tcb_empty_fpost V293_tcb_success_fpost getasrt] in Owned;
   apply astar_l_apure_elim in Owned;destruct Owned as [Code _];rewrite Code;discriminate. }
 unfold V293_TaskCreateExt_TCB_call.
 eapply conseq_rule with
 (p:=getasrt(fp (V293_tcb_success_arguments p top bottom identity size ext options) [logic_val saved] tid) **
 LV 209%Z @ Tint8 |-> olderr ** V293_create_tcb_arguments p top bottom identity size ext options F)
 (q:=EX result:val,
 getasrt(fq (V293_tcb_success_arguments p top bottom identity size ext options) (Some result) [logic_val saved] tid) **
 LV 209%Z @ Tint8 |-> result ** V293_create_tcb_arguments p top bottom identity size ext options F).
 - intros s H;exact H.
 - intros s [result H]. exists result.
   assert(Code:(saved=Vnull /\ result=Vint32(Int.repr 66)) \/
     (saved=Vptr(bt,Int.repr base) /\ result=Vint32 Int.zero)).
   { apply astar_prop in H. destruct H as [s1 [s2 [Owned _]]].
     assert(C:(saved=Vnull /\ Some result=Some(Vint32(Int.repr 66))) \/
       (saved=Vptr(bt,Int.repr base) /\ Some result=Some(Vint32 Int.zero))).
     { eapply V293_tcb_snapshot_post_code with (lg:=[logic_val saved])
       (vl:=V293_tcb_success_arguments p top bottom identity size ext options) (tid:=tid)
       (empty:=V293_tcb_empty_fpost bg R aop isr is cs good)
       (ready:=V293_tcb_success_fpost table bg bt base p top bottom identity size ext options next
       bh bgrp br bn oldblock oldbase present g row n R aop isr is cs good).
       - intros. eapply V293_tcb_empty_post_code with (good:=good);eassumption.
       - intros. eapply V293_tcb_success_post_code with (good:=good);eassumption.
       - reflexivity.
       - exact Owned. }
     destruct C as [[Equal Code]|[Equal Code]];inversion Code;subst;auto. }
   apply astar_l_apure_intro;assumption.
 - eapply calle_rule_lvar with (pre:=fp) (post:=fq) (tp:=Tint8)
   (tl:=rev V293_TCBInit_argument_types)
   (vl:=V293_tcb_success_arguments p top bottom identity size ext options)
   (logicl:=[logic_val saved]) (v':=olderr)
   (p:=V293_create_tcb_arguments p top bottom identity size ext options F).
   + apply V293_create_tcb_arguments_good. exact Frame.
   + exact Ret.
   + exact Lookup.
   + intros s H;exact H.
   + intros s H. unfold V293_create_tcb_arguments.
     eapply V293_create_tcb_arguments_read with
       (F:=getasrt(fp (V293_tcb_success_arguments p top bottom identity size ext options) [logic_val saved] tid) **
           LV 209%Z @ Tint8 |-> olderr ** F);[exact Range|exact Valid| ].
     unfold V293_create_tcb_arguments in *.
     clear -H. sep auto.
   + apply V293_create_tcb_argument_types;assumption.
   + unfold fp. apply V293_create_snapshot_pre_linv.
     * exact EmptyLINV.
     * cbn [V293_tcb_success_fpre getasrt]. apply V293_star_CurLINV_r. apply ReadyLINV.
   + intros s [result H]. unfold fq in H.
     eapply V293_create_snapshot_post_linv;[ | |exact H].
     * cbn [V293_tcb_empty_fpost getasrt]. apply V293_star_CurLINV_r. exact EmptyLINV.
     * cbn [V293_tcb_success_fpost getasrt]. apply V293_star_CurLINV_r. apply ReadyLINV.
Qed.
