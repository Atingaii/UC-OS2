(* Shared storage survives an actual selected switch and pending return.
   The weak storage invariant is intentional at the copy/switch transient.
   The returned core, unlike SWINV, does not require IE to remain false. *)
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitSharedReclose.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitResumedReturn.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyStorageInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCurrentInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293CurrentHandoffPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyGlobalTrace.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyFullCall.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Relations.Relation_Operators.

Lemma V293_current_shared_open : forall br bg bp target tp cells cache t,
 SWINVt(V293_ready_current_inv br bg bp target tp cells cache)t ==>
 V293_ready_current_core br bg bp target tp cells cache ** CurTid t.
Proof.
 intros br bg bp target tp cells cache t st H.
 unfold SWINVt in H;fold(CurTid t)in H.
 eapply astar_mono in H;[ |apply V293_current_switch_open|intros s K;exact K].
 assert(Empty:V293_shared_flags ==> Aemp).
 { intros s Flags;unfold V293_shared_flags in Flags.
   apply astar_l_aemp_elim.
   eapply astar_mono with(P:=isrclr **Aie false)(Q:=EX k:hid,ATopis k);
   [ |intros s0[k[_ E]];exact E|exact Flags].
   intros s0 F;apply astar_l_aemp_elim.
   eapply astar_mono with(P:=isrclr)(Q:=Aie false);
   [ |intros s1[_ E];exact E|exact F].
   intros s1[r[Flag Clear]];exact(proj2 Flag). }
 apply astar_l_aemp_elim.
 eapply astar_mono;[exact Empty|intros s K;exact K| ].
 clear Empty;sep auto.
Qed.

Theorem V293_int_exit_shared_switch_return :
 forall br bg bp target tp cells cache pc po pi ip T les aus runner victim cst
 ge le M ir si ci O op R bt bc runks enabled vci
 f body caller tail tau d1 d2 saved b v,
 runner<>victim ->po f=Some(tau,d1,d2,body) ->GoodInvAsrt R ->
 get T runner=Some(curs(sprim(switch target)),(kenil,runks)) ->
 get les runner=Some le ->get aus runner=Some(false,si,ci) ->
 get T victim=Some(SKIP,(kenil,kseq(sprim excrit)(kseq sret(kcall f body caller tail)))) ->
 get les victim=Some(V293_cpu_lenv saved b) ->get aus victim=Some(false,si,enabled::vci) ->
 get ge target=Some(bt,Tptr tp) ->load(Tptr tp)M(bt,0%Z)=Some(Vptr victim) ->
 get ge OSTCBCur=Some(bc,Tptr tp) ->V293_scheduler O victim ->
 (ge,le,M,ir,(false,si,ci),O,op)|=
 SWINVt(V293_ready_storage_inv br bg bp target tp cells)runner **
 (Amapsto(b,0%Z)Tint32 true v **R) ->
 exists Ms Mf,
 lpstep(pc,(po,pi,ip))T cst(ge,les,M,ir,aus)runner
 (set T runner(SKIP,(kenil,runks)))cst(ge,les,Ms,ir,aus)victim /\
 V293_global_steps(pc,(po,pi,ip))cst(T,(ge,les,M,ir,aus),runner)
 (set(set T runner(SKIP,(kenil,runks)))victim(SKIP,(kenil,tail)),
 (ge,set les victim caller,Mf,ir,set aus victim(enabled,si,vci)),victim) /\
 store(Tptr tp)M(bc,0%Z)(Vptr victim)=Some Ms /\
 free Tint32 b Ms=Some Mf /\
 (ge,caller,Mf,ir,(enabled,si,vci),set O curtid(oscurt victim),op)|=
 V293_ready_current_core br bg bp target tp cells cache **(CurTid victim **R) /\
 load(Tptr tp)Mf(bc,0%Z)=Some(Vptr victim) /\
 (forall i,(0<=i<4)%Z ->get Mf(b,i)=None) /\
 (forall c i,c<>b ->c<>bc ->get Mf(c,i)=get M(c,i)).
Proof.
 intros br bg bp target tp cells cache pc po pi ip T les aus runner victim cst
 ge le M ir si ci O op R bt bc runks enabled vci
 f body caller tail tau d1 d2 saved b v Apart Bind Good Code Local Aux
 Pending Saved VictimAux Target Read Current Highest Held.
 destruct(V293_ready_storage_switch_step br bg bp target tp cells
 pc po pi ip T cst runks runner victim bt bc ge le les M ir(false,si,ci)aus O op
 (Amapsto(b,0%Z)Tint32 true v **R) Local Aux Code Target Read Current Held)
 as(Ms&Step&Store&Shared&Pointer&Outside).
 assert(Self:sched_self V293_scheduler(set O curtid(oscurt victim))).
 { exists victim;split;[apply map_get_set| ].
   destruct Highest as[ts[Map High]];exists ts;split;
   [rewrite map_get_set' by discriminate;exact Map|exact High]. }
 apply V293_current_handoff_switch_highest_frame with(bc:=cache)in Shared;[ |exact Self].
 eapply astar_mono in Shared;[ |apply V293_current_shared_open|intros s K;exact K].
 assert(Owned:(ge,V293_cpu_lenv saved b,Ms,ir,(false,si,enabled::vci),
 set O curtid(oscurt victim),op)|=
 Amapsto(b,0%Z)Tint32 true v **
 (V293_ready_current_core br bg bp target tp cells cache **(CurTid victim **R))).
 { eapply good_inv_prop with(le:=le)(ie:=false)(cs:=ci)(op:=op).
 - split;[exact I| ];split;[apply V293_current_core_good| ];split;
   [unfold CurTid,Agvarmapsto,Aptrmapsto;cbn;auto|exact Good].
 - clear Held;sep auto. }
 assert(Keep:get(set T runner(SKIP,(kenil,runks)))victim=
 Some(SKIP,(kenil,kseq(sprim excrit)(kseq sret(kcall f body caller tail))))).
 { rewrite map_get_set' by exact Apart;exact Pending. }
 destruct(V293_int_exit_pending_return pc po pi ip(set T runner(SKIP,(kenil,runks)))
 les aus victim cst ge Ms ir false enabled si vci(set O curtid(oscurt victim))op
 (V293_ready_current_core br bg bp target tp cells cache **(CurTid victim **R))
 f body caller tail tau d1 d2 saved b v Bind
 ltac:(split;[apply V293_current_core_good| ];split;
 [unfold CurTid,Agvarmapsto,Aptrmapsto;cbn;auto|exact Good])
 Keep Saved VictimAux Owned)as(Mf&Return&Free&Rest&Removed&Frame).
 assert(Physical:load(Tptr tp)Mf(bc,0%Z)=Some(Vptr victim)).
 { assert(Cur:(ge,caller,Mf,ir,(enabled,si,vci),set O curtid(oscurt victim),op)|=
   CurTid victim **Atrue)by(clear Owned Shared Held;sep auto).
   destruct(V293_shared_current_read _ _ _ _ _ _ _ _ _ Cur)as(b0&t0&Env&Load).
   change(get ge OSTCBCur=Some(b0,Tptr t0))in Env.
   rewrite Current in Env;inversion Env;subst;exact Load. }

 exists Ms;exists Mf;split;[exact Step| ];split.
 - unfold V293_global_steps;eapply rt1n_trans with
   (y:=(set T runner(SKIP,(kenil,runks)),(ge,les,Ms,ir,aus),victim));
   [exact Step|exact Return].
 - split;[exact Store| ];split;[exact Free| ];split;[exact Rest| ];
   split;[exact Physical| ];split;[exact Removed| ].
   intros c i NotLocal NotCurrent;rewrite Frame by exact NotLocal.
   apply Outside;left;exact NotCurrent.
Qed.
