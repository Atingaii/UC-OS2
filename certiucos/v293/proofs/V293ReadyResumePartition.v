(* Exact ready ownership in the original enabled/disabled resource partition.
   Resumption is universal over restored shared resources; no return execution
   or saved simulation is supplied as a premise. *)
Require Import CertiOS.certiucos.v293.proofs.V293ReadyOwnedGlobalSwitch.
Require Import CertiOS.certiucos.v293.proofs.V293InvariantPendingTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293SwitchReturnTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyFullCall.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitchPre.
Require Import CertiOS.certiucos.v293.proofs.V293ClientSkipTaskSim.
Require Import CertiOS.framework.proof.simulation.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.sep_combine_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Section ReadyResume.
Variables br bg bp : block.
Let G:=V293_ready_inv br bg bp.
Let C:=V293_ready_core br bg bp.

Lemma V293_ready_full_core_halves : forall t,
 V293_ready_full br bg bp t <==> C **CurTid t.
Proof.
 intros t s;split;intro Held.
 - unfold V293_ready_full in Held;sep normal in Held;sep destruct Held.
   assert(Packed:s|=(GV OSTCBCur@(Tptr x2)|->Vptr t) **
    (V293_shared_fields t x x0 x1 **V293_ready_payload br bg bp x))by(sep auto).
   eapply astar_mono in Packed;[ |apply GV_separate_rw|intros st H;exact H].
   unfold C,V293_ready_core,V293_shared_ready_records,CurTid;clear Held;sep auto.
 - unfold C,V293_ready_core,V293_shared_ready_records in Held;sep normal in Held;sep destruct Held.
   assert(E:x=t).
   { eapply(V293_shared_current_agree x t
     (V293_shared_fields x x0 x1 x2 **V293_ready_payload br bg bp x0)s);sep auto. }
   subst x.
   assert(Packed:s|=(CurTid t **CurTid t) **
    (V293_shared_fields t x0 x1 x2 **V293_ready_payload br bg bp x0))by(sep auto).
   eapply astar_mono in Packed;[ |apply V293_current_halves_write|intros st H;exact H].
   unfold V293_ready_full;clear Held;sep auto.
Qed.

Lemma V293_ready_resume_enabled_INV : forall ge le M ir si ci O op,
 (forall i,ir i=false) -> (ge,le,M,ir,(true,si,ci),O,op)|=C ->
 (ge,le,M,ir,(true,si,ci),O,op)|=INV G.
Proof.
 intros ge le M ir si ci O op Clear Core.
 change((ge,le,M,ir,(true,si,ci),O,op)|=Aemp **(inv_ieon G \\// inv_ieoff G)).
 apply astar_l_aemp_intro;left;unfold inv_ieon.
 apply sat_split';exists(emp:mem);exists M;exists(emp:osabst);exists O.
 split;[apply map_join_comm;apply map_join_emp| ];
 split;[apply map_join_comm;apply map_join_emp| ];split;[repeat split;reflexivity| ].
 unfold invlth_isr;eapply V293_shared_clear_noisr_close;[exact Clear| ].
 apply V293_ready_noisr_core;exact Core.
Qed.

Lemma V293_ready_resume_disabled_INV_empty : forall ge le ir si ci op,
 (forall i,ir i=false) ->gettopis si<=INUM ->
 (ge,le,(emp:mem),ir,(false,si,ci),(emp:osabst),op)|=INV G.
Proof.
 intros ge le ir si ci op Clear Bound.
 change((ge,le,(emp:mem),ir,(false,si,ci),(emp:osabst),op)|=
 Aemp **(inv_ieon G \\// inv_ieoff G)).
 apply astar_l_aemp_intro;right;unfold inv_ieoff.
 apply sat_split';exists(emp:mem);exists(emp:mem);exists(emp:osabst);exists(emp:osabst).
 split;[apply map_join_emp| ];split;[apply map_join_emp| ];split;[repeat split;reflexivity| ].
 exists(gettopis si);apply sat_split';exists(emp:mem);exists(emp:mem);exists(emp:osabst);exists(emp:osabst).
 split;[apply map_join_emp| ];split;[apply map_join_emp| ];split;[repeat split;reflexivity| ].
 destruct(proj1(Nat.lt_eq_cases (gettopis si) INUM)Bound)as[Less|Equal].
 - left;apply astar_l_apure_intro;[ |exact Less].
   unfold invlth_isr;replace(gettopis si+1)with(S(gettopis si))by lia.
   eapply V293_shared_clear_noisr_close;[exact Clear| ].
   apply V293_ready_noisr_tail;split;reflexivity.
 - right;split;[exact Equal|split;reflexivity].
Qed.

Lemma V293_ready_resume_disabled_SWINV : forall ge le M ir si ci O op,
 (forall i,ir i=false) -> (ge,le,M,ir,(false,si,ci),O,op)|=C ->
 (ge,le,M,ir,(false,si,ci),O,op)|=SWINV G.
Proof.
 intros ge le M ir si ci O op Clear Core.
 assert(Flags:(ge,le,(emp:mem),ir,(false,si,ci),(emp:osabst),op)|=isrclr **Aie false).
 { apply sat_split';exists(emp:mem);exists(emp:mem);exists(emp:osabst);exists(emp:osabst).
   split;[apply map_join_emp| ];split;[apply map_join_emp| ];split;[ |repeat split;reflexivity].
   exists ir;split;[repeat split;reflexivity|split;[exact Clear|split;reflexivity]]. }
 unfold SWINV;apply sat_split';exists(emp:mem);exists M;exists(emp:osabst);exists O.
 split;[apply map_join_comm;apply map_join_emp| ];
 split;[apply map_join_comm;apply map_join_emp| ];split;[exact Flags| ].
 exists(gettopis si);apply sat_split';exists(emp:mem);exists M;exists(emp:osabst);exists O.
 split;[apply map_join_comm;apply map_join_emp| ];
 split;[apply map_join_comm;apply map_join_emp| ];split;[repeat split;reflexivity| ].
 unfold invlth_isr;rewrite Nat.sub_0_r.
 eapply V293_shared_clear_noisr_close;[exact Clear| ].
 apply V293_ready_noisr_core;exact Core.
Qed.

(* This is a resource partition, not a claim that both sides own the core.
   The frame R is arbitrary and is neither weakened nor absorbed by Atrue. *)
Theorem V293_ready_resume_invariants : forall t R ge le M ir enabled si ci O op,
 (forall i,ir i=false) -> (enabled=false ->gettopis si<=INUM) ->
 (ge,le,M,ir,(enabled,si,ci),O,op)|=C **(CurTid t **R) ->
 (ge,le,M,ir,(enabled,si,ci),O,op)|=(INV G **RDYINV G t) **R.
Proof.
 intros t R ge le M ir enabled si ci O op Clear Bound Held.
 assert(Packed:(ge,le,M,ir,(enabled,si,ci),O,op)|=(C **CurTid t) **R)by(sep auto).
 apply sat_split in Packed;destruct Packed as(m1&m2&o1&o2&JM&JO&Live&Frame).
 apply sat_split';exists m1;exists m2;exists o1;exists o2.
 split;[exact JM| ];split;[exact JO| ];split;[ |exact Frame].
 destruct enabled.
 - apply sat_split in Live;destruct Live as(mc&mr&oc&orr&JM'&JO'&Core&Current).
   apply sat_split';exists mc;exists mr;exists oc;exists orr.
   split;[exact JM'| ];split;[exact JO'| ];split.
   + apply V293_ready_resume_enabled_INV;assumption.
   + left;apply sat_split';exists(emp:mem);exists mr;exists(emp:osabst);exists orr.
     split;[apply map_join_comm;apply map_join_emp| ];
     split;[apply map_join_comm;apply map_join_emp| ];split;[ |exact Current].
     split;[repeat split;reflexivity|exists ir;split;
     [repeat split;reflexivity|split;[exact Clear|split;reflexivity]]].
 - apply sat_split';exists(emp:mem);exists m1;exists(emp:osabst);exists o1.
   split;[apply map_join_comm;apply map_join_emp| ];
   split;[apply map_join_comm;apply map_join_emp| ];split.
   + apply V293_ready_resume_disabled_INV_empty;[exact Clear|apply Bound;reflexivity].
   + right;unfold SWINVt;fold(CurTid t).
     apply sat_split in Live;destruct Live as(mc&mr&oc&orr&JM'&JO'&Core&Current).
     apply sat_split';exists mc;exists mr;exists oc;exists orr.
     split;[exact JM'| ];split;[exact JO'| ];split;[ |exact Current].
     apply V293_ready_resume_disabled_SWINV;assumption.
Qed.

(* Public bridge: exactly the ready_full delivered by the real switch.
   The external frame is retained verbatim on the same total state. *)
Theorem V293_ready_full_runtime_partition : forall t R ge le M ir enabled si ci O op,
 (forall i,ir i=false) ->(enabled=false ->gettopis si<=INUM) ->
 (ge,le,M,ir,(enabled,si,ci),O,op)|=V293_ready_full br bg bp t **R ->
 (ge,le,M,ir,(enabled,si,ci),O,op)|=(INV G **RDYINV G t) **R.
Proof.
 intros t R ge le M ir enabled si ci O op Clear Bound Held.
 eapply astar_mono in Held;
 [ |intros st H;apply(proj1(V293_ready_full_core_halves t st));exact H|intros st H;exact H].
 apply V293_ready_resume_invariants;[exact Clear|exact Bound|clear -Held;sep auto].
Qed.

(* The selected task's enabled view must donate the core to shared INV.
   Merely leaving it all task-local is not a legal enabled partition. *)
Theorem V293_ready_enabled_empty_rejected : forall ge le ir si ci op,
 (forall i,ir i=false) ->
 ~((ge,le,(emp:mem),ir,(true,si,ci),(emp:osabst),op)|=INV G).
Proof.
 intros ge le ir si ci op Clear Held.
 change((ge,le,(emp:mem),ir,(true,si,ci),(emp:osabst),op)|=
 Aemp **(inv_ieon G \\// inv_ieoff G))in Held.
 apply astar_l_aemp_elim in Held;destruct Held as[On|Off].
 - unfold inv_ieon in On;apply sat_split in On.
   destruct On as(m1&m2&o1&o2&JM&JO&Flag&Rest).
   destruct Flag as[_[EM EO]];cbn in EM;change(o1=(emp:osabst))in EO;subst m1 o1.
   apply map_join_comm in JM,JO;apply map_join_emp' in JM,JO;subst m2 o2.
   unfold invlth_isr in Rest.
   apply invisr_imply_noisr' in Rest;[ |intros;apply Clear].
   apply V293_ready_noisr_core in Rest.
   destruct Rest as(t&ts&es&now&Core).
   pose proof(V293_shared_fields_core_get t ts es now(V293_ready_payload br bg bp ts)
    (ge,le,(emp:mem),ir,(true,si,ci),(emp:osabst),op)Core)as[Cur _].
   change(get(emp:osabst)curtid=Some(oscurt t))in Cur;rewrite map_emp_get in Cur;discriminate.
 - unfold inv_ieoff in Off;apply sat_split in Off.
   destruct Off as(m1&m2&o1&o2&JM&JO&Flag&Rest).
   destruct Flag as[Flag _];discriminate Flag.
Qed.

Theorem V293_ready_full_pending_TaskSim : forall pc po pi ip A t ge M ir top ci O op
 f body caller tail tau d1 d2 saved b v,
 po f=Some(tau,d1,d2,body) ->V293_skip_client_state(SKIP,(kenil,tail)) ->
 (forall i,ir i=false) ->
 (ge,V293_cpu_lenv saved b,M,ir,(false,nil,top::ci),O,op)|=
 Amapsto(b,0%Z)Tint32 true v **V293_ready_full br bg bp t ->
 TaskSim(pc,(po,pi,ip))
 (SKIP,(kenil,kseq(sprim excrit)(kseq sret(kcall f body caller tail))))
 (ge,V293_cpu_lenv saved b,M,ir,(false,nil,top::ci))
 (pc,A)(SKIP,(kenil,tail))O V293_shared_li G
 (fun st=>satp(fst st)(snd st)(RDYINV G t **LINV V293_shared_li t nil))t.
Proof.
 intros pc po pi ip A t ge M ir top ci O op f body caller tail tau d1 d2 saved b v Bind Cases Clear Held.
 assert(Packed:(ge,V293_cpu_lenv saved b,M,ir,(false,nil,top::ci),O,op)|=
 Amapsto(b,0%Z)Tint32 true v **(C **CurTid t)).
 { eapply astar_mono;[intros st H;exact H|intros st H;apply(proj1(V293_ready_full_core_halves t st));exact H|exact Held]. }
 eapply V293_invariant_pending_TaskSim;
 [reflexivity|apply V293_ready_core_good| | |exact Bind|exact Cases|exact Clear|exact Packed].
 - intros;apply V293_ready_resume_disabled_SWINV;assumption.
 - intros;apply V293_ready_resume_enabled_INV;assumption.
Qed.

(* Saved CPU local is kept, but restored memory and abstract state are not
   frozen to their pre-switch values. This is not a reachability theorem. *)
Theorem V293_ready_full_resume_callback : forall pc po pi ip A t ge Ml ir top ci Ol op
 f body caller tail tau d1 d2 saved b v,
 po f=Some(tau,d1,d2,body) ->V293_skip_client_state(SKIP,(kenil,tail)) ->
 (ge,V293_cpu_lenv saved b,Ml,ir,(false,nil,top::ci),Ol,op)|=Amapsto(b,0%Z)Tint32 true v ->
 forall Mc Oc o' O',
 satp(ge,V293_cpu_lenv saved b,Mc,ir,(false,nil,top::ci))Oc(SWINVt G t) ->
 joinmem(ge,V293_cpu_lenv saved b,Ml,ir,(false,nil,top::ci))Mc o' ->join Ol Oc O' ->
 TaskSim(pc,(po,pi,ip))
 (SKIP,(kenil,kseq(sprim excrit)(kseq sret(kcall f body caller tail))))o'
 (pc,A)(curs(hapi_code(spec_done None)),(kenil,tail))O' V293_shared_li G
 (fun st=>satp(fst st)(snd st)(RDYINV G t **LINV V293_shared_li t nil))t.
Proof.
 intros pc po pi ip A t ge Ml ir top ci Ol op f body caller tail tau d1 d2 saved b v
 Bind Cases Saved Mc Oc o' O' Restored JM JO.
 assert(Clear:forall i,ir i=false).
 { eapply(V293_shared_clear_state ge(V293_cpu_lenv saved b)Mc ir(false,nil,top::ci)Oc op).
   specialize(Restored op);unfold SWINVt,SWINV in Restored;clear -Restored;sep auto. }
 assert(Full:(ge,V293_cpu_lenv saved b,Mc,ir,(false,nil,top::ci),Oc,op)|=
 V293_ready_full br bg bp t).
 { apply astar_r_aemp_elim.
   eapply V293_owned_switch_active_view with(R:=Aemp);[exact I| ].
   apply astar_r_aemp_intro;apply Restored. }
 unfold joinmem in JM;destruct JM as(g&e&m1&m2&i&a&E1&E2&Join);inversion E1;subst g e m1 i a.
 subst o';rename m2 into Mall.
 assert(Owned:(ge,V293_cpu_lenv saved b,Mall,ir,(false,nil,top::ci),O',op)|=
 Amapsto(b,0%Z)Tint32 true v **V293_ready_full br bg bp t).
 { apply sat_split';exists Ml;exists Mc;exists Ol;exists Oc;
   split;[exact Join| ];split;[exact JO| ];split;assumption. }
 apply V293_resume_high_done.
 eapply V293_ready_full_pending_TaskSim;[exact Bind|exact Cases|exact Clear|exact Owned].
Qed.
End ReadyResume.
