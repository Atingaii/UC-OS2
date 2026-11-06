(* A single extended program and the same nonempty owned delay fixture.
   Entry is after cpu_sr initialization, not full caller reachability. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeDlyGlobalSwitch.
Require Import CertiOS.certiucos.v293.proofs.V293TimeDlySwitch.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyGlobalTrace.
Require Import CertiOS.certiucos.v293.proofs.V293LocalGlobalTrace.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyFullCall.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.code.V293OSTimeDlyCall.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.audit.probes.V293TimeDlySwitchProbe.
Require Import CertiOS.audit.probes.V293TimeDlySchedCallProbe.
Require Import CertiOS.audit.probes.V293TimeDlyEntryProbe.
Require Import CertiOS.audit.probes.V293TimeDlyTaskBridgeProbe.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.join_prop.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition DGfunction:=V293_dly_function 103%Z 106%Z 105%Z 400%Z 401%Z 110%Z 111%Z 112%Z 402%Z.
Definition DGbody:=V293_dly_full_body 103%Z 106%Z 105%Z 400%Z 401%Z 110%Z 111%Z 112%Z 402%Z.
Definition DGprogram:progunit:=fun f=>match DSprogram f with
 |Some fn=>Some fn|None=>if Z.eq_dec f 1200%Z then Some DGfunction else None end.
Definition DGprog:lprog:=((fun _=>None),(DGprogram,(fun _=>None),(fun _=>None))).
Definition DGouter:=kcall 1200%Z DGbody emp kstop.
Definition DGtasks:=set DWtasks OwnershipReady(SKIP,(kenil,DScontinuation##DGouter)).
Definition DGinitial c enabled bs:=V293_local_global_at DWtasks(DWenvs bs)(DWaux enabled)
 OwnershipReady(curs DEbody,(kenil,DGouter))
 ((DWge,DEle,DWmem c),(fun _=>false),(enabled,nil,nil)).

Lemma DGextends:forall f fn,DSprogram f=Some fn ->DGprogram f=Some fn.
Proof. intros f fn Bound;unfold DGprogram;rewrite Bound;reflexivity. Qed.

Lemma DGbindings:
 DGprogram 1200%Z=Some DGfunction /\DGprogram 112%Z=Some DSfunction /\
 DGprogram 113%Z=Some DShelper.
Proof. repeat split;reflexivity. Qed.

Theorem DGglobal_switch:forall c enabled,exists bs byblock Mcut Mf,
 V293_global_steps DGprog DWclient(DGinitial c enabled bs)
  (DGtasks,(DWge,DWenvs bs,Mf,(fun _=>false),DWaux enabled),OwnershipWaiting) /\
 V293_task_records Mf(DEblocked(Int.repr 3)) /\
 load(Tptr V293_tcb_type)Mf(10%positive,0%Z)=Some(Vptr OwnershipWaiting) /\
 load Tint32 Mf(85%positive,0%Z)=Some(Vint32(Int.add c Int.one)) /\
 load Tint8 Mf(84%positive,0%Z)=Some(V293_byteval 4) /\
 load Tint32 Mf(90%positive,0%Z)=Some(Vint32(Int.repr 99)) /\
 V293_bytes_writable Mf bs 0%Z 4 /\get Mf(byblock,0%Z)=None /\
 DWrun c enabled bs Mcut /\
 get DGtasks OwnershipReady=Some(SKIP,(kenil,DScontinuation##DGouter)) /\
 get DGtasks OwnershipWaiting=Some DWready /\
 get(DWenvs bs)OwnershipReady=Some(V293_cpu_lenv 501%Z bs) /\
 get(DWaux enabled)OwnershipReady=Some(false,nil,[enabled]) /\
 get(DWenvs bs)OwnershipWaiting=Some DEle /\
 get(DWaux enabled)OwnershipWaiting=Some(true,nil,nil).
Proof.
 intros c enabled;destruct(DWblocked_run c enabled)
 as(bs&byblock&Mcut&Run&Abstract&Records&Bitmap&High&Target&Count&Cache&Writable&Canary&CPU&Dead&Away).
 pose proof(V293_local_function_extension DSprogram DGprogram DGextends _ _ _ _ Run)as Extended.
 destruct(V293_dly_trace_switch_global DGprogram(fun _=>None)(fun _=>None)(fun _=>None)
 103%Z 106%Z 105%Z 400%Z 401%Z 110%Z 111%Z 112%Z 402%Z 1200%Z emp kstop
 DWtasks(DWenvs bs)(DWaux enabled)OwnershipReady OwnershipWaiting DWclient DWge DEle
 (DWmem c)Mcut(fun _=>false)enabled nil nil 116%Z 82%positive 10%positive V293_tcb_type
 DScontinuation(V293_cpu_lenv 501%Z bs)(false,nil,[enabled])
 eq_refl I Extended eq_refl Target eq_refl Writable)
 as(Mf&Global&Switch&Store&Current&Frame).
 cbn zeta in Global.
 cbn[V293_enclose V293_local_global_at V293_global_at]in Global.
 rewrite <-set_set_eq in Global.
 assert(Loc:set(DWenvs bs)OwnershipReady(V293_cpu_lenv 501%Z bs)=DWenvs bs)
 by(apply CltEnvMod.get_set_same;reflexivity).
 assert(Aux:TaskLStMod.set(DWaux enabled)OwnershipReady(false,nil,[enabled])=DWaux enabled)
 by(apply TaskLStMod.get_set_same;reflexivity).
 rewrite Loc in Global.
 change (V293_global_steps DGprog DWclient(DGinitial c enabled bs)
  (DGtasks,(DWge,DWenvs bs,Mf,(fun _=>false),
   TaskLStMod.set(DWaux enabled)OwnershipReady(false,nil,[enabled])),OwnershipWaiting)) in Global.
 rewrite Aux in Global.
 assert(Y:byblock<>10%positive).
 { intro E;destruct(Writable 0 ltac:(lia))as(v&Cell);cbn in Cell;rewrite <-E,Dead in Cell;discriminate. }
 exists bs;exists byblock;exists Mcut;exists Mf;split;[exact Global| ];split.
 - intros t pr st msg Get;eapply V293_task_record_frame;[ |apply Records;exact Get].
   intros i;apply Frame;left;destruct(DStask_blocks t pr st msg Get)as[E|E];subst t;discriminate.
 - split;[exact Current| ];split.
   + etransitivity;[apply V293_load_block_frame;intro i;apply Frame;left;discriminate|exact Count].
   + split.
     * etransitivity;[apply V293_load_block_frame;intro i;apply Frame;left;discriminate|exact Cache].
     * split.
       -- etransitivity;[apply V293_load_block_frame;intro i;apply Frame;left;discriminate|exact Canary].
       -- split.
          ++ intros k Range;destruct(CPU k Range)as(v&Cell);exists v;rewrite Frame by(left;exact Away);exact Cell.
          ++ split;[rewrite Frame by(left;exact Y);exact Dead| ];split;[exact Run|repeat split;reflexivity].
Qed.

Theorem DGboth_IE:
 (exists bs M,V293_global_steps DGprog DWclient(DGinitial Int.zero true bs)
  (DGtasks,(DWge,DWenvs bs,M,(fun _=>false),DWaux true),OwnershipWaiting)) /\
 (exists bs M,V293_global_steps DGprog DWclient(DGinitial Int.zero false bs)
  (DGtasks,(DWge,DWenvs bs,M,(fun _=>false),DWaux false),OwnershipWaiting)).
Proof.
 split;[destruct(DGglobal_switch Int.zero true)as(bs&byblock&Mcut&M&Trace&Rest)|
 destruct(DGglobal_switch Int.zero false)as(bs&byblock&Mcut&M&Trace&Rest)];
 exists bs;exists M;exact Trace.
Qed.

(* Only the helper binding is removed; the exact initial helper call is stuck.
   This checks call linkage, not any later resource or switch mechanism. *)
Definition DGwithout_helper:progunit:=fun f=>if Z.eq_dec f 113%Z then None else DGprogram f.
Lemma DGablation_only_helper:
 DGwithout_helper 113%Z=None /\
 (forall f,f<>113%Z ->DGwithout_helper f=DGprogram f).
Proof.
 split;[reflexivity|intros f Different;unfold DGwithout_helper;
 destruct(Z.eq_dec f 113%Z);[contradiction|reflexivity]].
Qed.
Theorem DGhelper_boundary:forall ks st,
 (exists C' st',loststep DGprogram(curs(sfexec 113%Z nil nil),(kenil,ks))st C' st') /\
 ~(exists C' st',loststep DGwithout_helper(curs(sfexec 113%Z nil nil),(kenil,ks))st C' st').
Proof.
 intros ks [[[[ge le]M]ir]aux];split.
 - eexists;eexists;apply ostc_step;eapply stmt_step;[reflexivity| ].
   eapply sfexec_step;[reflexivity|reflexivity|reflexivity|exact I|reflexivity].
 - eapply V293_missing_port_has_no_step;reflexivity.
Qed.

Theorem DGglobal_wrap:exists bs M,
 V293_global_steps DGprog DWclient(DGinitial(Int.repr Int.max_unsigned)true bs)
  (DGtasks,(DWge,DWenvs bs,M,(fun _=>false),DWaux true),OwnershipWaiting) /\
 load Tint32 M(85%positive,0%Z)=Some(Vint32 Int.zero).
Proof.
 destruct(DGglobal_switch(Int.repr Int.max_unsigned)true)
 as(bs&byblock&Mcut&M&Trace&Records&Current&Counter&Rest).
 exists bs;exists M;split;[exact Trace|rewrite DWcounter_wrap in Counter;exact Counter].
Qed.
