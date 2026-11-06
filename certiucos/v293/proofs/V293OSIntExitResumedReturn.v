(* Exact suspended OSIntExit continuation and its real return.
   An existing continuation is consumed, never installed by this theorem. *)
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBoundarySwitch.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyResumption.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyFullCall.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCallGlobal.
Require Import CertiOS.certiucos.v293.proofs.V293LocalGlobalTrace.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyGlobalTrace.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.framework.proof.join_prop.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.tactics.basetac.join_lib.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPointerCompare.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrent.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCacheContract.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import Coq.Lists.List Lia.
Require Import Coq.Relations.Relation_Operators.
Import ListNotations.
Local Open Scope nat_scope.

Theorem V293_int_exit_pending_return :
 forall pc po pi ip T les aus t cst ge M ir active enabled si ci O op R
 f body caller tail tau d1 d2 saved b v,
 po f=Some(tau,d1,d2,body) ->GoodInvAsrt R ->
 get T t=Some(SKIP,(kenil,kseq(sprim excrit)(kseq sret(kcall f body caller tail)))) ->
 get les t=Some(V293_cpu_lenv saved b) ->get aus t=Some(active,si,enabled::ci) ->
 (ge,V293_cpu_lenv saved b,M,ir,(active,si,enabled::ci),O,op)|=Amapsto(b,0%Z)Tint32 true v **R ->
 exists Mf,
 V293_global_steps(pc,(po,pi,ip))cst(T,(ge,les,M,ir,aus),t)
 (set T t(SKIP,(kenil,tail)),(ge,set les t caller,Mf,ir,set aus t(enabled,si,ci)),t) /\
 free Tint32 b M=Some Mf /\
 (ge,caller,Mf,ir,(enabled,si,ci),O,op)|=R /\
 (forall i,(0<=i<4)%Z ->get Mf(b,i)=None) /\
 (forall c i,c<>b ->get Mf(c,i)=get M(c,i)).
Proof.
 intros pc po pi ip T les aus t cst ge M ir active enabled si ci O op R
 f body caller tail tau d1 d2 saved b v Bind Good Code Env Aux Held.
 destruct(V293_cpu_release _ _ _ _ _ _ _ _ _ _ Held)as(Mf&Free&Rest&Removed&Frame).
 assert(Exit:V293_global_steps(pc,(po,pi,ip))cst
 (V293_local_global_at T les aus t
 (SKIP,(kenil,kseq(sprim excrit)(kseq sret(kcall f body caller tail))))
 ((ge,V293_cpu_lenv saved b,M),ir,(active,si,enabled::ci)))
 (V293_local_global_at T les aus t(curs sret,(kenil,kcall f body caller tail))
 ((ge,V293_cpu_lenv saved b,M),ir,(enabled,si,ci)))).
 { eapply V293_global_trans.
 - apply V293_loststep_global_single.
   + eapply V293_bound_continuation_inos;[exact Bind|reflexivity].
   + apply ostc_step;eapply stmt_step;[reflexivity|apply sskip_step].
 - eapply V293_global_trans.
   + apply V293_loststep_global_single.
     * eapply V293_bound_continuation_inos;[exact Bind|reflexivity].
     * apply excrit_step;reflexivity.
   + apply V293_loststep_global_single.
     * eapply V293_bound_continuation_inos;[exact Bind|reflexivity].
     * apply ostc_step;eapply stmt_step;[reflexivity|apply sskip_step]. }
 pose proof(V293_sched_global_return pc po pi ip T les aus t cst ge caller M Mf ir
 (enabled,si,ci)tail f body tau d1 d2 saved b Bind Free)as Return.
 assert(Trace:=V293_global_trans _ _ _ _ _ Exit Return).
 cbn[V293_local_global_at V293_global_at]in Trace.
 assert(TC:set T t(SKIP,(kenil,kseq(sprim excrit)(kseq sret(kcall f body caller tail))))=T)
 by(exact(TasksMod.get_set_same Code)).
 assert(EC:set les t(V293_cpu_lenv saved b)=les)by(exact(CltEnvMod.get_set_same Env)).
 assert(AC:set aus t(active,si,enabled::ci)=aus)by(exact(TaskLStMod.get_set_same Aux)).
 change(V293_global_steps(pc,(po,pi,ip))cst
 (set T t(SKIP,(kenil,kseq(sprim excrit)(kseq sret(kcall f body caller tail)))),
 (ge,set les t(V293_cpu_lenv saved b),M,ir,set aus t(active,si,enabled::ci)),t)
 (set T t(SKIP,(kenil,tail)),(ge,set les t caller,Mf,ir,set aus t(enabled,si,ci)),t))in Trace.
 rewrite TC,EC,AC in Trace.
 exists Mf;split;[exact Trace| ];split;[exact Free| ];split.
 - eapply good_inv_prop;[exact Good|exact Rest].
 - split;assumption.
Qed.

(* exint is an explicit handler instruction, NOT automatic kint popping. *)
Theorem V293_int_exit_pending_exint :
 forall pc po pi ip T les aus t cst ge M ir active enabled i si ci O op R
 f body caller tail tau d1 d2 saved b v interrupted ike interrupted_le,
 po f=Some(tau,d1,d2,body) ->GoodInvAsrt R ->
 get T t=Some(SKIP,(kenil,kseq(sprim excrit)(kseq sret(kcall f body caller
 (kseq(sprim exint)(kint interrupted ike interrupted_le tail)))))) ->
 get les t=Some(V293_cpu_lenv saved b) ->get aus t=Some(active,i::si,enabled::ci) ->
 (ge,V293_cpu_lenv saved b,M,ir,(active,i::si,enabled::ci),O,op)|=Amapsto(b,0%Z)Tint32 true v **R ->
 exists Mf,
 V293_global_steps(pc,(po,pi,ip))cst(T,(ge,les,M,ir,aus),t)
 (set T t(interrupted,(ike,tail)),
 (ge,set les t interrupted_le,Mf,ir,set aus t(true,si,ci)),t) /\
 free Tint32 b M=Some Mf /\
 (forall j,(0<=j<4)%Z ->get Mf(b,j)=None) /\
 (forall c j,c<>b ->get Mf(c,j)=get M(c,j)).
Proof.
 intros pc po pi ip T les aus t cst ge M ir active enabled i si ci O op R
 f body caller tail tau d1 d2 saved b v interrupted ike interrupted_le Bind Good Code Env Aux Held.
 set(K:=kseq(sprim exint)(kint interrupted ike interrupted_le tail)).
 destruct(V293_int_exit_pending_return pc po pi ip T les aus t cst ge M ir active enabled
 (i::si)ci O op R f body caller K tau d1 d2 saved b v Bind Good Code Env Aux Held)
 as(Mf&Return&Free&Rest&Removed&Frame).
 assert(Exit:V293_global_steps(pc,(po,pi,ip))cst
 (V293_local_global_at T les aus t(SKIP,(kenil,K))((ge,caller,Mf),ir,(enabled,i::si,ci)))
 (V293_local_global_at T les aus t(interrupted,(ike,tail))((ge,interrupted_le,Mf),ir,(true,si,ci)))).
 { eapply V293_global_trans.
 - apply V293_loststep_global_single.
   + exists SKIP;exists kenil;exists K;split;[reflexivity|right;right;discriminate].
   + apply ostc_step;eapply stmt_step;[reflexivity|apply sskip_step].
 - apply V293_loststep_global_single.
   + exists(curs(sprim exint));exists kenil;exists(kint interrupted ike interrupted_le tail).
     split;[reflexivity|right;right;discriminate].
   + eapply exint_step;reflexivity. }
 cbn[V293_local_global_at V293_global_at]in Exit.
 exists Mf;split.
 - eapply V293_global_trans;[exact Return|exact Exit].
 - split;[exact Free| ];split;assumption.
Qed.

Lemma V293_saved_cell_context : forall b v ge le M ir aux O op ge' le' ir' aux' op',
 (ge,le,M,ir,aux,O,op)|=Amapsto(b,0%Z)Tint32 true v **Atrue ->
 (ge',le',M,ir',aux',O,op')|=Amapsto(b,0%Z)Tint32 true v **Atrue.
Proof.
 intros b v ge le M ir aux O op ge' le' ir' aux' op' Held.
 apply sat_split in Held;destruct Held as(m1&m2&o1&o2&JM&JO&Cell&Rest).
 apply sat_split';exists m1;exists m2;exists o1;exists o2.
 split;[exact JM| ];split;[exact JO| ];split;[exact Cell|exact I].
Qed.

Theorem V293_OSIntExit_call_switch_resume :
  forall br bg bp P ks pc po pi ip T les aus cst interrupted ike interrupted_le ge caller M ir enabled si ci O op ct R tasks nc
 f sched_id unmap group rows high y table target nesting lock running saved current counter
 bt bh bo bn bl brun bc bcount c oldhigh oldtarget bcur nb nv ncaller ntail na ne nsi nci,
 P=pumerge po pi ->
 get T ct=Some(curs(scall f nil),(kenil,kint interrupted ike interrupted_le ks)) ->
 get les ct=Some caller ->get aus ct=Some(enabled,si,ci) ->
 goodks(pc,(po,pi,ip))ks ->
 po f=Some(V293_exit_boundary_function running nesting lock saved table high target current counter sched_id (V293_interrupt_handoff high current target)) ->
 P sched_id=Some(V293_OSSchedNew_function unmap group rows high y) ->
 ~In saved [unmap;group;rows;high;table;target;nesting;lock;running;current;counter] ->
 y<>unmap ->y<>group ->y<>rows ->y<>high ->y<>table ->bh<>bp ->bn<>bt ->
 get ge unmap=Some(bt,Tarray Tint8 256) ->get ge group=Some(bg,Tint8) ->
 get ge rows=Some(br,Tarray Tint8 2) ->get ge high=Some(bh,Tint8) ->
 get ge table=Some(bp,Tarray(Tptr V293_tcb_type)13) ->get ge target=Some(bo,Tptr V293_tcb_type) ->
 get ge nesting=Some(bn,Tint8) ->get ge lock=Some(bl,Tint8) ->
 get ge running=Some(brun,Tint8) ->get ge current=Some(bc,Tint8) ->get ge counter=Some(bcount,Tint32) ->
 get ge OSTCBCur=Some(bcur,Tptr V293_tcb_type) ->
 (forall t pr st msg,get tasks t=Some(pr,st,msg) ->
   exists C le aux,get T t=Some C /\ get les t=Some le /\ get aus t=Some aux) ->
 get O abstcblsid=Some(abstcblist tasks) ->V293_current_task tasks ct nc ->
 ~V293_highest_ready tasks ct ->GoodInvAsrt R ->
 nb<>bc ->nb<>bcur ->nb<>bcount ->
 (forall next,V293_highest_ready tasks next ->
 get T next=Some(SKIP,(kenil,kseq(sprim excrit)(kseq sret(kcall f
 (V293_exit_boundary_body running nesting lock saved table high target current counter sched_id
 (V293_interrupt_handoff high current target))ncaller ntail)))) /\
 get les next=Some(V293_cpu_lenv saved nb) /\ get aus next=Some(na,nsi,ne::nci)) ->
 (forall n,n<256 ->load Tint8 M(bt,Z.of_nat n)=Some(V293_byteval(V293_ready_lookup n))) ->
 (ge,caller,M,ir,(false,si,ci),O,op)|=SWINVt(V293_ready_inv br bg bp)ct **
 (V293_owned_record_cell((bh,0%Z),Tint8,oldhigh) **
 (V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,oldtarget) **
 (V293_owned_record_cell((bn,0%Z),Tint8,V293_byteval 1) **
 (V293_owned_record_cell((bl,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval nc) **
 (V293_owned_record_cell((brun,0%Z),Tint8,V293_byteval 1) **
 (V293_owned_record_cell((bcount,0%Z),Tint32,Vint32 c) **(Amapsto(nb,0%Z)Tint32 true nv **R)))))))) ->

 exists bs next nh Msw Mret,
 fresh M bs /\ next<>ct /\ nh<>nc /\
 V293_highest_ready tasks next /\V293_current_task tasks next nh /\
 V293_global_steps(pc,(po,pi,ip))cst(T,(ge,les,M,ir,aus),ct)
 (set(set T ct(SKIP,(kenil,kseq(sprim excrit)(kseq sret(kcall f
 (V293_exit_boundary_body running nesting lock saved table high target current counter sched_id
 (V293_interrupt_handoff high current target))caller(kint interrupted ike interrupted_le ks))))))
 next(SKIP,(kenil,ntail)),
 (ge,set(set les ct(V293_cpu_lenv saved bs))next ncaller,Mret,ir,
 set(set aus ct(false,si,enabled::ci))next(ne,nsi,nci)),next) /\
 free Tint32 nb Msw=Some Mret /\
 (forall i,(0<=i<4)%Z ->get Mret(nb,i)=None) /\
 (forall c i,c<>nb ->get Mret(c,i)=get Msw(c,i)) /\
 load(Tptr V293_tcb_type)Mret(bcur,0%Z)=Some(Vptr next) /\
 load Tint8 Mret(bc,0%Z)=Some(V293_byteval nh) /\
 load Tint32 Mret(bcount,0%Z)=Some(Vint32(Int.add c Int.one)) /\
 (forall k,k<4 ->exists v,get Mret(bs,Z.of_nat k)=Some(true,v)) /\
 get(set(set T ct(SKIP,(kenil,kseq(sprim excrit)(kseq sret(kcall f
 (V293_exit_boundary_body running nesting lock saved table high target current counter sched_id
 (V293_interrupt_handoff high current target))caller(kint interrupted ike interrupted_le ks))))))
 next(SKIP,(kenil,ntail)))ct=
 Some(SKIP,(kenil,kseq(sprim excrit)(kseq sret(kcall f
 (V293_exit_boundary_body running nesting lock saved table high target current counter sched_id
 (V293_interrupt_handoff high current target))caller(kint interrupted ike interrupted_le ks))))) /\
 get(set(set les ct(V293_cpu_lenv saved bs))next ncaller)ct=Some(V293_cpu_lenv saved bs) /\
 get(set(set aus ct(false,si,enabled::ci))next(ne,nsi,nci))ct=Some(false,si,enabled::ci).
Proof.
 intros br bg bp P ks pc po pi ip T les aus cst interrupted ike interrupted_le ge caller M ir enabled si ci O op ct R tasks nc
 f sched_id unmap group rows high y table target nesting lock running saved current counter
 bt bh bo bn bl brun bc bcount c oldhigh oldtarget bcur nb nv ncaller ntail na ne nsi nci
 Merge Code Env Aux GoodKs Program Scheduler Names YU YG YR YH YT HP NT
 GU GG GR GH GT GO GN GL GRun GC GCount GCur Domain Map Current NotHighest Good
 NBC NBCur NBCount Pending Lookup Held.
 assert(Merged:P f=Some(V293_exit_boundary_function running nesting lock saved table high target current counter sched_id
 (V293_interrupt_handoff high current target))).
 { rewrite Merge;unfold pumerge;rewrite Program;reflexivity. }
 assert(GoodFrame:GoodInvAsrt(Amapsto(nb,0%Z)Tint32 true nv **R))by(split;[exact I|exact Good]).
 assert(Initial:(ge,caller,M,ir,(false,si,ci),O,op)|=Amapsto(nb,0%Z)Tint32 true nv **Atrue).
 { sep auto. }
 destruct(V293_OSIntExit_boundary_switch true br bg bp P ks pc po pi ip T les aus cst
 interrupted ike interrupted_le ge caller M ir enabled si ci O op ct
 (Amapsto(nb,0%Z)Tint32 true nv **R)tasks nc
 f sched_id unmap group rows high y table target nesting lock running saved current counter
 bt bh bo bn bl brun bc bcount c oldhigh oldtarget bcur
 Merge Code Env Aux GoodKs Merged Scheduler Names YU YG YR YH YT HP NT
 GU GG GR GH GT GO GN GL GRun GC GCount GCur Domain Map Current NotHighest GoodFrame Lookup Held)
 as(bs&next&nh&Me&Ms&Msw&Fresh&Different&PrioDifferent&Highest&Next&Prefix&Post&Pointer&Cache&Count&Alive&Coherent&Copy&PointerStore&Bindings).
 destruct(Pending next Highest)as(NCode&NEnv&NAux).
 set(body:=V293_exit_boundary_body running nesting lock saved table high target current counter sched_id
 (V293_interrupt_handoff high current target))in *.
 set(old:=(SKIP,(kenil,kseq(sprim excrit)(kseq sret(kcall f body caller
 (kint interrupted ike interrupted_le ks))))):code)in *.
 assert(Saved:(ge,V293_cpu_lenv saved bs,Msw,ir,(false,si,enabled::ci),set O curtid(oscurt next),op)|=
 Amapsto(nb,0%Z)Tint32 true nv **Atrue).
 { clear Held Initial;sep auto. }
 assert(TargetSaved:(ge,V293_cpu_lenv saved nb,Msw,ir,(na,nsi,ne::nci),set O curtid(oscurt next),op)|=
 Amapsto(nb,0%Z)Tint32 true nv **Atrue).
 { eapply V293_saved_cell_context;exact Saved. }
 assert(TCode:get(set T ct old)next=Some(SKIP,(kenil,kseq(sprim excrit)(kseq sret(kcall f body ncaller ntail)))))
 by(rewrite map_get_set' by congruence;exact NCode).
 assert(TEnv:get(set les ct(V293_cpu_lenv saved bs))next=Some(V293_cpu_lenv saved nb))
 by(rewrite map_get_set' by congruence;exact NEnv).
 assert(TAux:get(set aus ct(false,si,enabled::ci))next=Some(na,nsi,ne::nci))
 by(rewrite map_get_set' by congruence;exact NAux).
 destruct(V293_int_exit_pending_return pc po pi ip(set T ct old)
 (set les ct(V293_cpu_lenv saved bs))(set aus ct(false,si,enabled::ci))next cst ge Msw ir
 na ne nsi nci(set O curtid(oscurt next))op Atrue f body ncaller ntail
 Tvoid dnil(dcons saved Tint32 dnil)saved nb nv Program I TCode TEnv TAux TargetSaved)
 as(Mret&Return&Free&Rest&Removed&Frame).
 assert(Apart:bs<>nb).
 { intro E;subst bs.
   destruct(V293_tick_raw_owned_writable nb Tint32 nv _ _ _ _ _ _ _ _ Initial 0 ltac:(cbn;lia))as(v&Byte).
   apply(Fresh(nb,0%Z)0%Z eq_refl);exists(true,v);exact Byte. }
 exists bs;exists next;exists nh;exists Msw;exists Mret.
 repeat first[assumption|split].
 - eapply V293_global_trans;[exact Prefix|exact Return].
 - etransitivity;[apply V293_load_block_frame;intro i;apply Frame;congruence|exact Pointer].
 - etransitivity;[apply V293_load_block_frame;intro i;apply Frame;congruence|exact Cache].
 - etransitivity;[apply V293_load_block_frame;intro i;apply Frame;congruence|exact Count].
 - intros k Bound;rewrite Frame by exact Apart;apply Alive;exact Bound.
 - rewrite map_get_set' by congruence;apply map_get_set.
 - rewrite map_get_set' by congruence;apply map_get_set.
 - rewrite map_get_set' by congruence;apply map_get_set.
Qed.

Theorem V293_int_exit_stack_ablation : forall pc po pi ip T les aus t cst ge M ir
    active enabled si ci O op R f body caller ks tau d1 d2 saved b v,
  po f=Some (tau,d1,d2,body) -> GoodInvAsrt R ->
  get T t=Some (SKIP,(kenil,kseq (sprim excrit) (kseq sret (kcall f body caller ks)))) ->
  get les t=Some (V293_cpu_lenv saved b) ->
  get aus t=Some (active,si,enabled::negb enabled::ci) ->
  (ge,V293_cpu_lenv saved b,M,ir,(active,si,enabled::negb enabled::ci),O,op) |=
    Amapsto (b,0%Z) Tint32 true v ** R ->
  exists Mf,
    V293_global_steps (pc,(po,pi,ip)) cst (T,(ge,les,M,ir,aus),t)
      (set T t (SKIP,(kenil,ks)),
       (ge,set les t caller,Mf,ir,set aus t (enabled,si,negb enabled::ci)),t) /\
    V293_global_steps (pc,(po,pi,ip)) cst
      (T,(ge,les,M,ir,set aus t (active,si,negb enabled::ci)),t)
      (set T t (SKIP,(kenil,ks)),
       (ge,set les t caller,Mf,ir,set aus t (negb enabled,si,ci)),t) /\
    free Tint32 b M=Some Mf /\
    set aus t (enabled,si,negb enabled::ci)<>set aus t (negb enabled,si,ci).
Proof.
  intros pc po pi ip T les aus t cst ge M ir active enabled si ci O op R
    f body caller ks tau d1 d2 saved b v Bind Good Code Local Aux Held.
  destruct (V293_int_exit_pending_return pc po pi ip T les aus t cst ge M ir
    active enabled si (negb enabled::ci) O op R f body caller ks tau d1 d2 saved b v
    Bind Good Code Local Aux Held) as (Mf & Positive & Free & Rest & Removed & Frame).
  assert (NegativeHeld : (ge,V293_cpu_lenv saved b,M,ir,(active,si,negb enabled::ci),O,op) |=
    Amapsto (b,0%Z) Tint32 true v ** R).
  { eapply good_inv_prop;[split;[exact I|exact Good]|exact Held]. }
  destruct (V293_int_exit_pending_return pc po pi ip T les
    (set aus t (active,si,negb enabled::ci)) t cst ge M ir active (negb enabled) si ci O op R
    f body caller ks tau d1 d2 saved b v Bind Good Code Local (map_get_set _ _ _) NegativeHeld)
    as (Mn & Negative & FreeN & RestN & RemovedN & FrameN).
  assert (Mn=Mf) by congruence. subst Mn.
  cbn in Negative. rewrite <- (set_set_eq _ _ _ _ aus t (negb enabled,si,ci) (active,si,negb enabled::ci)) in Negative.
  exists Mf. split;[exact Positive| ]. split;[exact Negative| ]. split;[exact Free| ].
  intro Same. pose proof (f_equal (fun a:ltaskstset=>get a t) Same) as Equal.
  change (get (set aus t (enabled,si,negb enabled::ci)) t=get (set aus t (negb enabled,si,ci)) t) in Equal.
  rewrite !map_get_set in Equal. destruct enabled;discriminate.
Qed.

Lemma V293_bare_kint_no_local_step : forall P interrupted ike interrupted_le tail st C' st',
 ~loststep P(SKIP,(kenil,kint interrupted ike interrupted_le tail))st C' st'.
Proof.
 intros P interrupted ike interrupted_le tail st C' st' Step.
 inversion Step;subst;try discriminate.
 match goal with H:cstep _ _ _ _ _ |- _ =>inversion H;subst;try discriminate end;
 repeat match goal with H:(_,_) =(_,_) |- _ =>inversion H;clear H;subst end;
 first[match goal with H:estep _ _ _ _ _ _ |- _ =>inversion H end|
 match goal with H:sstep _ _ _ _ _ _ _ |- _ =>inversion H end].
Qed.
