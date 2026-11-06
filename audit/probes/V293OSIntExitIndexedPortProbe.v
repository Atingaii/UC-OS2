(* Concrete resource controls. These are assertions/Hoare proofs, not port executions. *)
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitIndexedPort.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitCriticalCalls.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitResourceBridge.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBuilders.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitDispatch.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterInternal.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.code.V293OSIntExit.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.audit.probes.V293OSIntExitBuildersProbe.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPrefix.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.
Definition IPcurrent t := V293_encoded_memory 6%positive 0 false(encode_val(Tptr Tvoid)(Vptr t)).
Definition IPmemory t v := merge(IPcurrent t)(BLsaved v).
Definition IPstate t v := V293_wstate V293_witness_ge BLle(IPmemory t v).
Definition IPresource lg t address : asrt :=
 match lg with
 | (cons (logic_val(Vint32 v)) nil) =>
   <||spec_done None||> ** (PV address @Tint32|->Vint32 v ** CurLINV V293_witness_li t)
 | _ => Afalse
 end.
Lemma IPgood : forall lg t address,GoodFunAsrt(IPresource lg t address).
Proof.
 intros lg t address;unfold IPresource.
 destruct lg as [ | x xs ];[exact I| ];destruct x;try exact I;destruct v;try exact I;destruct xs;[ |exact I].
 cbn[GoodFunAsrt Aptrmapsto];split;[exact I|split;[exact I| ]].
 apply V293_CurLINV_function_assertion;apply V293_witness_li_good.
Qed.
Lemma IPcurrent_owned : forall t,
 V293_wstate V293_witness_ge BLle(IPcurrent t) |= CurLINV V293_witness_li t.
Proof.
 intro t;exists(nil:list logicvar).
 eapply V293_wstate_star with(m1:=IPcurrent t)(m2:=emp);[apply map_join_emp| | ].
 - exists Tvoid;exists 6%positive.
   eapply V293_wstate_star with(m1:=emp)(m2:=IPcurrent t).
   + apply map_join_comm;apply map_join_emp.
   + exists 6%positive;split;[vm_compute;reflexivity|repeat split;reflexivity].
   + split;[apply V293_encoded_memory_mapsto|reflexivity].
 - eapply V293_wstate_star with(m1:=emp)(m2:=emp);[apply map_join_emp| |exact I].
   unfold LINV,V293_witness_li.
   eapply V293_wstate_star with(m1:=emp)(m2:=emp);[apply map_join_emp|split;reflexivity| ].
   split;[apply V293_witness_li_good|split;reflexivity].
Qed.
Lemma IPowned : forall t v,
 IPstate t(Vint32 v) |= IPresource(cons (logic_val(Vint32 v)) nil)t(15%positive,Int.zero) **
 (Alvarenv 120%Z Tint32(15%positive,0%Z) ** Aemp).
Proof.
 intros t v. unfold IPstate,IPmemory,IPresource.
 assert(H:V293_wstate V293_witness_ge BLle(merge(IPcurrent t)(BLsaved(Vint32 v))) |=
 <||spec_done None||> ** (CurLINV V293_witness_li t **
 (PV(15%positive,Int.zero)@Tint32|->Vint32 v **
 (Alvarenv 120%Z Tint32(15%positive,0%Z) ** Aemp)))).
 { apply astar_l_aop'_intro;[ |reflexivity].
   eapply V293_wstate_star with(m1:=IPcurrent t)(m2:=BLsaved(Vint32 v)).
   - apply map_join_merge;apply map_disjoint;intros[b i].
     destruct(Pos.eq_dec b 6%positive);[subst b;right;left|left];
     unfold IPcurrent,BLsaved;rewrite V293_encoded_memory_outside by(left;congruence);reflexivity.
   - apply IPcurrent_owned.
   - eapply V293_wstate_star with(m1:=BLsaved(Vint32 v))(m2:=emp);[apply map_join_emp| | ].
     + split;[apply V293_encoded_memory_mapsto|reflexivity].
     + apply astar_r_aemp_intro;eexists;split;[reflexivity|repeat split;reflexivity]. }
 clear -H;sep auto.
Qed.
Definition IPspec : funspec := fun f =>
 if Z.eq_dec f 201%Z then Some(V293_indexed_pointer_fpre IPresource IPgood,
 V293_indexed_pointer_fpost IPresource IPgood,(Tvoid,[Tptr Tint32]))else None.
Theorem IPtwo_tasks_one_spec : forall sd I r ri t v,
 InfRules IPspec sd V293_witness_li I r ri
 (IPresource(cons (logic_val(Vint32 v)) nil)t(15%positive,Int.zero) **
 (Alvarenv 120%Z Tint32(15%positive,0%Z) ** Aemp))
 (scall 201%Z[eaddrof(evar 120%Z)])
 (IPresource(cons (logic_val(Vint32 v)) nil)t(15%positive,Int.zero) **
 (Alvarenv 120%Z Tint32(15%positive,0%Z) ** Aemp))t.
Proof.
 intros;eapply V293_indexed_pointer_call with(BG:=IPgood)(AG:=IPgood)(lg:=(cons (logic_val(Vint32 v)) nil)).
 - exact Logic.I.
 - unfold IPresource;apply V293_saved_pointer_resource_local;intros s H;exact H.
 - unfold IPresource;apply V293_saved_pointer_resource_local;intros s H;exact H.
 - reflexivity.
Qed.
Theorem IPindependent_witnesses :
 ((IPstate(7%positive,Int.zero)(Vint32 Int.zero)) |=
  getasrt(V293_indexed_pointer_fpre IPresource IPgood[Vptr(15%positive,Int.zero)]
   (cons (logic_val(Vint32 Int.zero)) nil)(7%positive,Int.zero)) **
  (Alvarenv 120%Z Tint32(15%positive,0%Z) ** Aemp)) /\
 ((IPstate(9%positive,Int.zero)(Vint32 Int.one)) |=
  getasrt(V293_indexed_pointer_fpre IPresource IPgood[Vptr(15%positive,Int.zero)]
   (cons (logic_val(Vint32 Int.one)) nil)(9%positive,Int.zero)) **
  (Alvarenv 120%Z Tint32(15%positive,0%Z) ** Aemp)).
Proof. split;apply IPowned. Qed.
Lemma IPload : forall t v lg st,
 st |= IPresource lg t(15%positive,Int.zero) ->
 lg=(cons (logic_val(Vint32 v)) nil) ->
 load Tint32(getmem st)(15%positive,0%Z)=Some(Vint32 v).
Proof.
 intros t v lg st H E;subst lg;unfold IPresource in H.
 eapply V293_star_load_r;[ |exact H].
 intros s Hs;eapply V293_star_load_l;[ |exact Hs].
 intros s0 H0;eapply mapstoval_load;[reflexivity|exact(proj1 H0)].
Qed.
Theorem IPlogical_value_control :
 ~ (IPstate(7%positive,Int.zero)(Vint32 Int.zero) |=
 IPresource(cons (logic_val(Vint32 Int.one)) nil)(7%positive,Int.zero)(15%positive,Int.zero) ** Atrue).
Proof.
 intro H;pose proof(V293_star_load_l _ _ _ _ _ (fun s Hs=>IPload _ Int.one _ s Hs eq_refl) _ H)as E.
 assert(L:load Tint32(getmem(IPstate(7%positive,Int.zero)(Vint32 Int.zero)))(15%positive,0%Z)=Some(Vint32 Int.zero)).
 { eapply V293_star_load_l;[intros st Hs;eapply IPload;[exact Hs|reflexivity]|apply IPowned]. }
 rewrite L in E;discriminate.
Qed.
Theorem IPsaved_value_control :
 ~ (IPstate(7%positive,Int.zero)(Vint32 Int.one) |=
 IPresource(cons (logic_val(Vint32 Int.zero)) nil)(7%positive,Int.zero)(15%positive,Int.zero) ** Atrue).
Proof.
 intro H;pose proof(V293_star_load_l _ _ _ _ _ (fun s Hs=>IPload _ Int.zero _ s Hs eq_refl) _ H)as E.
 assert(L:load Tint32(getmem(IPstate(7%positive,Int.zero)(Vint32 Int.one)))(15%positive,0%Z)=Some(Vint32 Int.one)).
 { eapply V293_star_load_l;[intros st Hs;eapply IPload;[exact Hs|reflexivity]|apply IPowned]. }
 rewrite L in E;discriminate.
Qed.
Theorem IPsaved_frame : forall t v1 v2 b i,b<>15%positive ->
 get(IPmemory t v1)(b,i)=get(IPmemory t v2)(b,i).
Proof.
 intros;unfold IPmemory,BLsaved;repeat rewrite map_merge_semp by reflexivity;
 repeat rewrite V293_encoded_memory_outside by(left;assumption);reflexivity.
Qed.

(* Dynamic counter and current task are parameters in the SAME four families.
   This closed running case has nesting 2 -> 1, so no switch can be reached. *)
Definition IPshared t c n := V293_exit_physical_pre
 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive 0 16
 V293_witness_li t(spec_done None)Tvoid 8%positive 10%positive V293_idle_entries V293_idle_tasks
 13%positive 14%positive 11%positive 12%positive 0 n 0 Vnull c.
Definition IPacquired t c := V293_exit_acquired
 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive 0 16
 V293_witness_li t(spec_done None)Tvoid 8%positive 10%positive V293_idle_entries V293_idle_tasks
 13%positive 14%positive 11%positive 12%positive 0 2 0 Vnull c(Vint32 Int.zero).
Definition IPleaving t c := V293_exit_leaving
 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive 0 16
 V293_witness_li t(spec_done None)Tvoid 8%positive 10%positive V293_idle_entries V293_idle_tasks
 13%positive 14%positive 11%positive 12%positive 0 2 0 Vnull c(Vint32 Int.zero)(fun _=>Afalse).
Definition IPentryF lg t address := match lg with
 |(cons (logic_val(Vint32 c)) nil)=>V293_saved_pointer_resource(spec_done None)(Vint32 Int.zero)(IPshared t c 2)address
 |_=>Afalse end.
Definition IPacquiredF lg t address := match lg with
 |(cons (logic_val(Vint32 c)) nil)=>IPacquired t c address|_=>Afalse end.
Definition IPleavingF lg t address := match lg with
 |(cons (logic_val(Vint32 c)) nil)=>IPleaving t c address|_=>Afalse end.
Definition IPrestoredF lg t address := match lg with
 |(cons (logic_val(Vint32 c)) nil)=>V293_saved_pointer_resource(spec_done None)(Vint32 Int.zero)(IPshared t c 1)address
 |_=>Afalse end.
Ltac IPdecode := intros lg t address;destruct lg as [ | x xs ];[exact I| ];
 destruct x;try exact I;match goal with vv : val |- _ => destruct vv end;try exact I;destruct xs;[ |exact I].
Lemma IPentry_good : forall lg t address,GoodFunAsrt(IPentryF lg t address).
Proof.
 IPdecode;apply V293_saved_pointer_resource_good;unfold IPshared;
 apply V293_exit_physical_pre_good;apply V293_witness_li_good.
Qed.
Lemma IPacquired_good : forall lg t address,GoodFunAsrt(IPacquiredF lg t address).
Proof. IPdecode;unfold IPacquired;apply V293_exit_acquired_good;apply V293_witness_li_good. Qed.
Lemma IPleaving_good : forall lg t address,GoodFunAsrt(IPleavingF lg t address).
Proof. IPdecode;unfold IPleaving;apply V293_exit_leaving_good;[apply V293_witness_li_good|intro;exact I]. Qed.
Lemma IPrestored_good : forall lg t address,GoodFunAsrt(IPrestoredF lg t address).
Proof.
 IPdecode;apply V293_saved_pointer_resource_good;unfold IPshared;
 apply V293_exit_physical_pre_good;apply V293_witness_li_good.
Qed.
Definition IPrunningSpec : funspec := fun f =>
 if Z.eq_dec f 200%Z then Some(V293_sched_fpre 100%Z 101%Z 102%Z 103%Z
 1%positive 2%positive 3%positive 4%positive V293_witness_li V293_witness_li_good,
 V293_sched_fpost 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive
 V293_witness_li V293_witness_li_good,(Tvoid,[]))else
 if Z.eq_dec f 201%Z then Some(V293_indexed_pointer_fpre IPentryF IPentry_good,
 V293_indexed_pointer_fpost IPacquiredF IPacquired_good,(Tvoid,[Tptr Tint32]))else
 if Z.eq_dec f 202%Z then Some(V293_indexed_pointer_fpre IPleavingF IPleaving_good,
 V293_indexed_pointer_fpost IPrestoredF IPrestored_good,(Tvoid,[Tptr Tint32]))else None.
Definition IPbuilderpre c := V293_exit_builder_pre
 106%Z 107%Z 110%Z 111%Z 108%Z 109%Z 112%Z Tvoid 8%positive 10%positive
 13%positive 14%positive 11%positive 12%positive 16%positive
 (spec_done None)(IPshared V293_idle_tid c 2)Aemp 1 120%Z.
Definition IPbuilderpost c := V293_exit_builder_post
 106%Z 107%Z 110%Z 111%Z 108%Z 109%Z 112%Z Tvoid 8%positive 10%positive
 13%positive 14%positive 11%positive 12%positive 16%positive
 (spec_done None)(IPshared V293_idle_tid c 2)(IPshared V293_idle_tid c 1)Aemp 1 120%Z.
Theorem IPrunning_builder : forall sd I c,
 InfRules IPrunningSpec sd V293_witness_li I(IPbuilderpost c)Afalse(IPbuilderpre c)
 (V293_OSIntExit_body 112%Z 108%Z 109%Z 120%Z 106%Z 103%Z 107%Z 110%Z 111%Z
 200%Z 201%Z 202%Z 203%Z)Afalse V293_idle_tid.
Proof.
 intros sd I c.
 eapply V293_OSIntExit_indexed_builder_contract with(P:=BLprogram)(f:=300%Z)(vl:=nil)(lg:=nil)
 (entryF:=IPentryF)(acquiredF:=IPacquiredF)(leavingF:=IPleavingF)(restoredF:=IPrestoredF)
 (FEG:=IPentry_good)(FAG:=IPacquired_good)(FLG:=IPleaving_good)(FRG:=IPrestored_good)
 (enter_lg:=(cons (logic_val(Vint32 c)) nil))(exit_lg:=(cons (logic_val(Vint32 c)) nil))
 (unmap:=100%Z)(group:=101%Z)(rows:=102%Z)(bt:=1%positive)(bg:=2%positive)(br:=3%positive)(bh:=4%positive)
 (lo:=0)(hi:=16)(entries:=V293_idle_entries)(tasks:=V293_idle_tasks)(nc:=0)
 (aop:=spec_done None)(shared:=IPshared V293_idle_tid c 2)(output:=IPshared V293_idle_tid c 1)
 (extra:=Aemp)(run:=1)(token:=Vint32 Int.zero)(old:=Vnull)(c:=c)(nest:=2)(locked:=0)
 (switch_post:=fun _=>Afalse)(value:=Vint32 Int.zero)(Hli:=V293_witness_li_good)
 (GP:=ltac:(apply(V293_exit_builder_pre_good 106%Z 107%Z 110%Z 111%Z 108%Z 109%Z 112%Z
 Tvoid 8%positive 10%positive 13%positive 14%positive 11%positive 12%positive 16%positive
 (spec_done None)(IPshared V293_idle_tid c 2)Aemp 1);[unfold IPshared;apply V293_exit_physical_pre_good;apply V293_witness_li_good|exact Logic.I]))
 (GQ:=ltac:(intro result;apply(V293_exit_builder_post_good 106%Z 107%Z 110%Z 111%Z 108%Z 109%Z 112%Z
 Tvoid 8%positive 10%positive 13%positive 14%positive 11%positive 12%positive 16%positive
 (spec_done None)(IPshared V293_idle_tid c 2)(IPshared V293_idle_tid c 1)Aemp 1 result);try exact Logic.I;
 unfold IPshared;apply V293_exit_physical_pre_good;apply V293_witness_li_good));
 try discriminate;try reflexivity;try (intros;reflexivity);try lia.
 - exists 12;vm_compute;repeat split;lia.
 - exact(proj1 V293_idle_relations).
 - exact(proj2 V293_idle_relations).
 - unfold IPshared;apply V293_exit_physical_pre_local.
 - unfold IPshared;apply V293_exit_physical_pre_local.
 - intros bs s H;contradiction.
Qed.

(* One factor at a time: fixed heap vs task index; no earlier lookup rejection. *)
Lemma IPcurrent_load : forall expected actual v,
 IPstate actual(Vint32 v) |= CurTid expected ** Atrue ->
 load(Tptr Tvoid)(getmem(IPstate actual(Vint32 v)))(6%positive,0%Z)=Some(Vptr expected).
Proof.
 intros expected actual v H. unfold CurTid in H.
 apply astar_l_aexists_elim in H;destruct H as[tp H].
 unfold Agvarmapsto in H. apply astar_l_aexists_elim in H;destruct H as[b H].
 assert(G:get(getgenv(IPstate actual(Vint32 v)))OSTCBCur=Some(b,Tptr tp)).
 { eapply V293_star_env_l with(E:=fun ge _=>get ge OSTCBCur=Some(b,Tptr tp));[ |exact H]. intros st Hs.
   eapply V293_star_env_l with(E:=fun ge _=>get ge OSTCBCur=Some(b,Tptr tp));[ |exact Hs]. intros st0 H0.
   destruct H0 as[b0[G[E _]]];inversion E;subst b0;exact G. }
 change(Some(6%positive,Tptr Tvoid)=Some(b,Tptr tp))in G.
 inversion G;subst b tp.
 eapply V293_star_load_l;[ |exact H]. intros st Hs.
 eapply V293_star_load_r;[ |exact Hs]. intros st0 H0.
 eapply mapstoval_load;[reflexivity|exact(proj1 H0)].
Qed.
Theorem IPtask_index_control :
 ~ (IPstate(7%positive,Int.zero)(Vint32 Int.zero) |=
 IPresource(cons(logic_val(Vint32 Int.zero))nil)(9%positive,Int.zero)(15%positive,Int.zero) ** Atrue).
Proof.
 intro H.
 assert(C:IPstate(7%positive,Int.zero)(Vint32 Int.zero) |= CurTid(9%positive,Int.zero) ** Atrue).
 { unfold IPresource,CurLINV in H;clear -H;sep auto. }
 pose proof(IPcurrent_load _ _ _ C)as L.
 assert(G:IPstate(7%positive,Int.zero)(Vint32 Int.zero) |= CurTid(7%positive,Int.zero) ** Atrue).
 { pose proof(IPowned(7%positive,Int.zero)Int.zero)as Hs;unfold IPresource,CurLINV in Hs;clear -Hs;sep auto. }
 pose proof(IPcurrent_load _ _ _ G)as E;rewrite E in L;discriminate.
Qed.
Theorem IPtask_change_frame : forall t1 t2 v b i,b<>6%positive ->
 get(IPmemory t1 v)(b,i)=get(IPmemory t2 v)(b,i).
Proof.
 intros;unfold IPmemory,IPcurrent;repeat rewrite map_merge_semp by reflexivity;
 repeat rewrite V293_encoded_memory_outside by(left;assumption);reflexivity.
Qed.
Theorem IPold_owner_rejects : forall st,
 ~ (st |= getasrt(V293_saved_pointer_fpre(7%positive,Int.zero)
 (IPresource(cons(logic_val(Vint32 Int.zero))nil)(9%positive,Int.zero))
 (IPgood(cons(logic_val(Vint32 Int.zero))nil)(9%positive,Int.zero))
 [Vptr(15%positive,Int.zero)]nil(9%positive,Int.zero)) ** Atrue).
Proof.
 intros st H;cbn[V293_saved_pointer_fpre getasrt]in H.
 assert(Bad:st |= [|(nil:list logicvar)=nil /\ (9%positive,Int.zero)=(7%positive,Int.zero)|] ** Atrue).
 { clear -H;sep auto. }
 apply astar_l_apure_elim in Bad;destruct Bad as[[_ E] _];discriminate.
Qed.
Theorem IPold_empty_lg_rejects : forall st,
 ~ (st |= getasrt(V293_saved_pointer_fpre(7%positive,Int.zero)
 (IPresource(cons(logic_val(Vint32 Int.zero))nil)(7%positive,Int.zero))
 (IPgood(cons(logic_val(Vint32 Int.zero))nil)(7%positive,Int.zero))
 [Vptr(15%positive,Int.zero)](cons(logic_val(Vint32 Int.zero))nil)(7%positive,Int.zero)) ** Atrue).
Proof.
 intros st H;cbn[V293_saved_pointer_fpre getasrt]in H.
 assert(Bad:st |= [|(cons(logic_val(Vint32 Int.zero))nil)=nil /\
 (7%positive,Int.zero)=(7%positive,Int.zero)|] ** Atrue).
 { clear -H;sep auto. }
 apply astar_l_apure_elim in Bad;destruct Bad as[[E _] _];discriminate.
Qed.
Definition IPbigjoined c value := merge(BLmemory 0 Vnull 2 0 0 c)(BLsaved value).
Definition IPbigmemory c run value := merge(IPbigjoined c value)(BLrun run).
Definition IPbigstate c run value := V293_target_wstate BLge BLle(IPbigmemory c run value)V293_target_fixture_abs.
Lemma IPbig_saved_join : forall c value,
 join(BLmemory 0 Vnull 2 0 0 c)(BLsaved value)(IPbigjoined c value).
Proof.
 intros. apply map_join_merge;apply map_disjoint;intros[b i].
 destruct(Pos.eq_dec b 15%positive);[subst b;left;unfold BLmemory;BLoutside| ].
 right;left;unfold BLsaved;apply V293_encoded_memory_outside;left;exact n.
Qed.
Lemma IPbig_run_join : forall c run value,
 join(IPbigjoined c value)(BLrun run)(IPbigmemory c run value).
Proof.
 intros. apply map_join_merge;apply map_disjoint;intros[b i].
 destruct(Pos.eq_dec b 16%positive);[subst b;left|right;left;unfold BLrun;apply V293_encoded_memory_outside;left;exact n].
 unfold IPbigjoined,BLsaved,BLmemory;BLoutside.
Qed.
Lemma IPbig_owned : forall c run value, IPbigstate c run value |=
 ((IPshared V293_idle_tid c 2) ** PV(15%positive,Int.zero)@Tint32|->value) **
 (V293_guard_cell 112%Z 16%positive run **
  (Alvarenv 120%Z Tint32(15%positive,0%Z) ** (BLbindings ** Aemp))).
Proof.
 intros.
 assert(H:IPbigstate c run value |=
  (((IPshared V293_idle_tid c 2) ** PV(15%positive,Int.zero)@Tint32|->value) **
   V293_guard_cell 112%Z 16%positive run) **
  (Alvarenv 120%Z Tint32(15%positive,0%Z) ** (BLbindings ** Aemp))).
 { unfold IPbigstate. eapply V293_target_wstate_star with
 (m1:=IPbigmemory c run value)(m2:=emp)(o1:=V293_target_fixture_abs)(o2:=emp);try apply map_join_emp.
 - eapply V293_target_wstate_star with(m1:=IPbigjoined c value)(m2:=BLrun run)
   (o1:=V293_target_fixture_abs)(o2:=emp).
   + apply IPbig_run_join.
   + apply map_join_emp.
   + eapply V293_target_wstate_star with(m1:=BLmemory 0 Vnull 2 0 0 c)(m2:=BLsaved value)
     (o1:=V293_target_fixture_abs)(o2:=emp).
     * apply IPbig_saved_join.
     * apply map_join_emp.
     * eapply good_fun_asrt_absop with(p:=(IPshared V293_idle_tid c 2))(le:=emp).
       -- unfold IPshared;apply V293_exit_physical_pre_good;apply V293_witness_li_good.
       -- apply BLphysical_owned.
     * split;[apply V293_encoded_memory_mapsto|reflexivity].
   + apply BLrun_owned.
 - apply BLcaller_names. }
 clear -H;sep auto.
Qed.
Theorem IPrunning_pre_nonempty : forall c value,IPbigstate c 1 value |= IPbuilderpre c.
Proof.
 intros c value;pose proof(IPbig_owned c 1 value)as Held.
 apply astar_l_adomlenv_intro with(d:=cons(120%Z,Tint32)nil)in Held;[ |exact BLdomain].
 assert(U:IPbigstate c 1 value |=
 (BLbindings ** (Agvarenv 112%Z Tint8(16%positive,0%Z) //\\ A_notin_lenv 112%Z)) **
 ((PV(15%positive,Int.zero)@Tint32|->value ** Alvarenv 120%Z Tint32(15%positive,0%Z)) **
 ((IPshared V293_idle_tid c 2) ** (Amapsto(16%positive,0%Z)Tint8 false(V293_byteval 1) **
 V293_exit_builder_domain 120%Z)))).
 { unfold V293_exit_builder_domain,V293_guard_cell in *;clear -Held;sep auto. }
 eapply astar_mono in U.
 2:{ unfold BLbindings;apply V293_exit_builder_forget_names. }
 2:{ intros s0 H0;exact H0. }
 assert(Op:IPbigstate c 1 value |= <||spec_done None||> **
 (V293_exit_builder_globals 106%Z 107%Z 110%Z 111%Z 108%Z 109%Z 112%Z Tvoid 8%positive 10%positive 13%positive 14%positive 11%positive 12%positive 16%positive **
 ((PV(15%positive,Int.zero)@Tint32|->value ** Alvarenv 120%Z Tint32(15%positive,0%Z)) **
 ((IPshared V293_idle_tid c 2) ** (Amapsto(16%positive,0%Z)Tint8 false(V293_byteval 1) **
 V293_exit_builder_domain 120%Z))))).
 { apply astar_l_aop'_intro;[exact U|reflexivity]. }
 unfold IPbuilderpre,V293_exit_builder_pre,V293_exit_builder_external_pre,
 V293_exit_builder_cells,Alvarmapsto,Alvarenv',Aptrmapsto;clear -Op;sep auto.
Qed.

(* All lookups are absent and nil logical arguments select Afalse in every
   family. The run=0 guard must make these obligations irrelevant. *)
Definition IPoffpre c := V293_exit_builder_pre
 106%Z 107%Z 110%Z 111%Z 108%Z 109%Z 112%Z Tvoid 8%positive 10%positive
 13%positive 14%positive 11%positive 12%positive 16%positive
 (spec_done None)(IPshared V293_idle_tid c 2)Aemp 0 120%Z.
Definition IPoffpost c := V293_exit_builder_post
 106%Z 107%Z 110%Z 111%Z 108%Z 109%Z 112%Z Tvoid 8%positive 10%positive
 13%positive 14%positive 11%positive 12%positive 16%positive
 (spec_done None)(IPshared V293_idle_tid c 2)(IPshared V293_idle_tid c 1)Aemp 0 120%Z.
Theorem IPnot_running_builder : forall sd I c,
 InfRules(fun _=>None) sd V293_witness_li I(IPoffpost c)Afalse(IPoffpre c)
 (V293_OSIntExit_body 112%Z 108%Z 109%Z 120%Z 106%Z 103%Z 107%Z 110%Z 111%Z
 200%Z 201%Z 202%Z 203%Z)Afalse V293_idle_tid.
Proof.
 intros sd I c.
 eapply V293_OSIntExit_indexed_builder_contract with(P:=BLprogram)(f:=300%Z)(vl:=nil)(lg:=nil)
 (entryF:=IPentryF)(acquiredF:=IPacquiredF)(leavingF:=IPleavingF)(restoredF:=IPrestoredF)
 (FEG:=IPentry_good)(FAG:=IPacquired_good)(FLG:=IPleaving_good)(FRG:=IPrestored_good)
 (enter_lg:=nil)(exit_lg:=nil)
 (unmap:=100%Z)(group:=101%Z)(rows:=102%Z)(bt:=1%positive)(bg:=2%positive)(br:=3%positive)(bh:=4%positive)
 (lo:=0)(hi:=16)(entries:=V293_idle_entries)(tasks:=V293_idle_tasks)(nc:=0)
 (aop:=spec_done None)(shared:=IPshared V293_idle_tid c 2)(output:=IPshared V293_idle_tid c 1)
 (extra:=Aemp)(run:=0)(token:=Vint32 Int.zero)(old:=Vnull)(c:=c)(nest:=2)(locked:=0)
 (switch_post:=fun _=>Afalse)(value:=Vint32 Int.zero)(Hli:=V293_witness_li_good)
 (GP:=ltac:(apply(V293_exit_builder_pre_good 106%Z 107%Z 110%Z 111%Z 108%Z 109%Z 112%Z
 Tvoid 8%positive 10%positive 13%positive 14%positive 11%positive 12%positive 16%positive
 (spec_done None)(IPshared V293_idle_tid c 2)Aemp 0);[unfold IPshared;apply V293_exit_physical_pre_good;apply V293_witness_li_good|exact Logic.I]))
 (GQ:=ltac:(intro result;apply(V293_exit_builder_post_good 106%Z 107%Z 110%Z 111%Z 108%Z 109%Z 112%Z
 Tvoid 8%positive 10%positive 13%positive 14%positive 11%positive 12%positive 16%positive
 (spec_done None)(IPshared V293_idle_tid c 2)(IPshared V293_idle_tid c 1)Aemp 0 result);try exact Logic.I;
 unfold IPshared;apply V293_exit_physical_pre_good;apply V293_witness_li_good));
 try discriminate;try reflexivity;try (intros;discriminate);try lia.
 - exists 12;vm_compute;repeat split;lia.
 - exact(proj1 V293_idle_relations).
 - exact(proj2 V293_idle_relations).
 - unfold IPshared;apply V293_exit_physical_pre_local.
 - unfold IPshared;apply V293_exit_physical_pre_local.
 - intros bs s H;contradiction.
Qed.

