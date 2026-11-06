(* The actual old switch, with the existing weak storage invariant.
   Only resource premises are public; returning shared resources is universal. *)
Require Import CertiOS.certiucos.v293.proofs.V293StoragePendingTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293InvariantPendingTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyStorageInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293SwitchReturnTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitch.
Require Import CertiOS.certiucos.v293.proofs.V293ClientSkipTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293HandoffProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyFullCall.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.simulation.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.framework.proof.memory_prop.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Section SwitchReturn.
Variables br bg bp : block.
Variable target : var.
Variable tp : type.
Variable cells : list(addr*type).
Let G:=V293_ready_storage_inv br bg bp target tp cells.
Let Core:=V293_ready_storage_core br bg bp target tp cells.

Lemma V293_storage_resume_open : forall t ge le M ir ci O op,
 (ge,le,M,ir,(false,nil,ci),O,op)|=SWINVt G t ->
 (forall i,ir i=false) /\(ge,le,M,ir,(false,nil,ci),O,op)|=Core **CurTid t.
Proof.
 intros t ge le M ir ci O op Held;split.
 - eapply(V293_shared_clear_state ge le M ir (false,nil,ci) O op).
   unfold SWINVt,SWINV in Held;sep auto.
 - unfold SWINVt in Held;fold(CurTid t)in Held.
   eapply astar_mono in Held;[ |apply V293_ready_storage_switch_open|intros st H;exact H].
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
   eapply astar_mono;[exact Empty|intros st H;exact H| ].
   clear Empty;sep auto.
Qed.

(* ol is kept; the resumed shared memory and abstract state are universal. *)
Lemma V293_storage_resume_callback : forall pc po pi ip A t ge Ml ir top ci Ol op
 f body caller tail tau d1 d2 saved b v,
 po f=Some(tau,d1,d2,body) ->V293_skip_client_state(SKIP,(kenil,tail)) ->
 (ge,V293_cpu_lenv saved b,Ml,ir,(false,nil,top::ci),Ol,op)|=Amapsto(b,0%Z)Tint32 true v ->
 forall Mc Oc o' O',
 satp(ge,V293_cpu_lenv saved b,Mc,ir,(false,nil,top::ci))Oc(SWINVt G t) ->
 joinmem(ge,V293_cpu_lenv saved b,Ml,ir,(false,nil,top::ci))Mc o' ->
 join Ol Oc O' ->
 TaskSim(pc,(po,pi,ip))
 (SKIP,(kenil,kseq(sprim excrit)(kseq sret(kcall f body caller tail))))o'
 (pc,A)(curs(hapi_code(spec_done None)),(kenil,tail))O' V293_shared_li G
 (fun st=>satp(fst st)(snd st)(RDYINV G t **LINV V293_shared_li t nil))t.
Proof.
 intros pc po pi ip A t ge Ml ir top ci Ol op f body caller tail tau d1 d2 saved b v
 Bind Cases Saved Mc Oc o' O' Restored JM JO.
 destruct(V293_storage_resume_open t ge (V293_cpu_lenv saved b) Mc ir (top::ci) Oc op(Restored op))as[Clear CoreHeld].
 unfold joinmem in JM;destruct JM as(g&e&m1&m2&i&a&E1&E2&JM);inversion E1;subst g e m1 i a.
 subst o';rename m2 into Mall;
 assert(Owned:(ge,V293_cpu_lenv saved b,Mall,ir,(false,nil,top::ci),O',op)|=
 Amapsto(b,0%Z)Tint32 true v **(Core **CurTid t)).
 { apply sat_split';exists Ml;exists Mc;exists Ol;exists Oc;
   split;[exact JM| ];split;[exact JO| ];split;assumption. }
 apply V293_resume_high_done.
 eapply V293_storage_pending_TaskSim;[exact Bind|exact Cases|exact Clear|exact Owned].
Qed.

(* SWPRE is required on the shared part, not on the kept saved cell. *)
Theorem V293_storage_switch_TaskSim : forall pc po pi ip A t x ge M ir top ci O op
 f body caller tail tau d1 d2 saved b v,
 getsched(pc,A)=V293_scheduler ->
 po f=Some(tau,d1,d2,body) ->V293_skip_client_state(SKIP,(kenil,tail)) ->
 (ge,V293_cpu_lenv saved b,M,ir,(false,nil,top::ci),O,op)|=
 Amapsto(b,0%Z)Tint32 true v **(SWINVt G t //\\ SWPRE_NDEAD V293_scheduler x t) ->
 TaskSim(pc,(po,pi,ip))
 (curs(sprim(switch x)),(kenil,kseq(sprim excrit)(kseq sret(kcall f body caller tail))))
 (ge,V293_cpu_lenv saved b,M,ir,(false,nil,top::ci))
 (pc,A)(curs(hapi_code(spec_seq sched(spec_done None))),(kenil,tail))O V293_shared_li G
 (fun st=>satp(fst st)(snd st)(RDYINV G t **LINV V293_shared_li t nil))t.
Proof.
 intros pc po pi ip A t x ge M ir top ci O op f body caller tail tau d1 d2 saved b v Sched Bind Cases Held.
 apply sat_split in Held;destruct Held as(Ml&Mc&Ol&Oc&Partition&AbsPartition&Saved&[Shared Pre]).
 assert(SharedAll:satp(ge,V293_cpu_lenv saved b,Mc,ir,(false,nil,top::ci))Oc(SWINVt G t)).
 { intro ab;eapply swinv_aop_irev;exact Shared. }
 assert(PreAll:satp(ge,V293_cpu_lenv saved b,Mc,ir,(false,nil,top::ci))Oc(SWPRE_NDEAD(getsched(pc,A))x t)).
 { rewrite Sched;intro ab;destruct Pre as[SwitchPre Member];split.
   - eapply swpre_aop_irev;exact SwitchPre.
   - eapply good_inv_prop;[cbn[GoodInvAsrt];intros;repeat split;exact I|exact Member]. }
 apply task_sim.
 - intros Cf Ms Mf cst cst' ofull Os o2 OO Inv JM JO Low.
   inversion Low;subst;
   match goal with E:(pc,(po,pi,ip))=(_,(_,_,_)) |- _ =>inversion E;subst;clear E end;try contradiction;try match goal with H:cstep _ _ _ _ _ |- _ =>exfalso;eapply V293_cstep_not_primitive;[exact H|reflexivity]end.
   match goal with H:loststep _ _ _ _ _ |- _ =>inversion H;subst;try discriminate end.
   match goal with H:cstep _ _ _ _ _ |- _ =>exfalso;eapply V293_cstep_not_primitive;[exact H|reflexivity]end.
 - intros Cf Ms Mf cst cst' ofull Os o2 OO ev Inv JM JO Low.
   inversion Low;subst;
   match goal with E:(pc,(po,pi,ip))=(_,(_,_,_)) |- _ =>inversion E;subst;clear E end;try contradiction.
   match goal with H:cstepev _ _ _ _ _ _ |- _ =>inversion H;subst end;
   match goal with H:sstepev _ _ _ _ _ _ _ _ |- _ =>inversion H;subst;try discriminate end.
 - intros Ms ks y Os OO Eq Inv Disj JO;inversion Eq;subst y ks.
   destruct(V293_invariant_nil_empty G eq_refl _ _ _ _ _ _ Inv)as[EM EO];subst Ms Os.
   apply map_join_emp' in JO;subst OO.
   exists(curs(hapi_code(spec_seq sched(spec_done None))),(kenil,tail));
   exists(spec_done None);exists(kenil,tail);exists O;
   exists Mc;exists((ge,V293_cpu_lenv saved b,Ml,ir,(false,nil,top::ci)):taskst);
   exists O;exists(emp:osabst);exists Ol;exists Oc.
   split;[reflexivity| ];split;[intros;apply ht_starO| ];split.
   + unfold joinmem;do 6 eexists;split;[reflexivity| ];split;[reflexivity|exact Partition].
   + split;[apply map_join_emp| ];split;[exact AbsPartition| ];split;[exact Inv| ];split;[exact SharedAll| ];split.
     * intro ab;exists (nil: list logicvar).
       assert(Keep:(ge,V293_cpu_lenv saved b,Ml,ir,(false,nil,top::ci),Ol,ab)|=Aemp **Atrue).
       { apply astar_l_aemp_intro;exact I. }
       eapply astar_mono;[apply V293_switch_local_empty|intros st H;exact H|exact Keep].
     * left;split;[exact PreAll| ].
       intros Mc' Oc' o' O' Restore JoinMem JoinAbs.
       eapply V293_storage_resume_callback;[exact Bind|exact Cases|exact Saved|exact Restore|exact JoinMem|exact JoinAbs].
 - intros Ms Os OO(x0&Eq);discriminate Eq.
 - intros cst o2 Ms Os Mf OO Of OOO NE NS NI NF Inv JM JO JF Low.
   exfalso;apply NS;do 2 eexists;reflexivity.
 - intros Ms Os e1 e2 e3 ks OO Eq;discriminate Eq.
 - intros Ms Os e ks OO Eq;discriminate Eq.
Qed.
End SwitchReturn.
