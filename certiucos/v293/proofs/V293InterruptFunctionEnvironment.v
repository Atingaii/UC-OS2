Require Import CertiOS.certiucos.v293.proofs.V293ComponentLink.
Require Import CertiOS.certiucos.v293.proofs.V293TimeGetAPI.
Require Import CertiOS.certiucos.v293.proofs.V293TimeSetAPI.
Require Import CertiOS.certiucos.v293.proofs.V293OSVersionAPI.
(* A common internal environment for two source-bound bodies. This does not
   install an ISR or claim the complete kernel environment. *)
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TimeGetLink.
Require Import CertiOS.certiucos.v293.proofs.V293TimeNamesGood.
Require Import CertiOS.certiucos.v293.proofs.V293TimeShared.
Require Import CertiOS.certiucos.v293.code.V293OSIntEnter.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.toptheorem.
Require Import CertiOS.framework.proof.auxdef.
Require Import Coq.Lists.List.

Definition V293_irq_internal_unit enter sched running nesting unmap group rows high y : progunit :=
 pumerge(V293_OSIntEnter_unit enter running nesting)
 (V293_OSSchedNew_internal_unit sched unmap group rows high y).
Definition V293_irq_internal_spec enter sched running nesting unmap group rows high
 brun bn bt bg br bh li(Hli:GoodLInvAsrt li):funspec :=
 fun f => if Z.eq_dec f enter then Some
 (V293_interrupt_fpre running nesting brun bn li Hli,
  V293_interrupt_fpost running nesting brun bn li Hli,(Tvoid,nil))
 else V293_OSSchedNew_internal_spec sched unmap group rows high bt bg br bh li Hli f.

Lemma V293_irq_internal_domains : forall enter sched running nesting unmap group rows high y
 brun bn bt bg br bh li Hli,
 EqDom(V293_irq_internal_unit enter sched running nesting unmap group rows high y)
 (V293_irq_internal_spec enter sched running nesting unmap group rows high brun bn bt bg br bh li Hli).
Proof.
 intros. intros f. unfold V293_irq_internal_unit,V293_irq_internal_spec,pumerge,
 V293_OSIntEnter_unit,V293_OSSchedNew_internal_unit,V293_OSSchedNew_internal_spec.
 destruct(Z.eq_dec f enter), (Z.eq_dec f sched);split;intros[x H];try discriminate;eexists;reflexivity.
Qed.

Theorem V293_irq_internal_entries : forall enter sched running nesting unmap group rows high y,
 enter<>sched ->
 V293_irq_internal_unit enter sched running nesting unmap group rows high y enter=
 Some(V293_OSIntEnter_function running nesting) /\
 V293_irq_internal_unit enter sched running nesting unmap group rows high y sched=
 Some(V293_OSSchedNew_function unmap group rows high y).
Proof.
 intros. unfold V293_irq_internal_unit,pumerge,V293_OSIntEnter_unit,V293_OSSchedNew_internal_unit.
 repeat destruct Z.eq_dec;try congruence;split;reflexivity.
Qed.

(* Both contracts are rebuilt under this exact merged P and exact Spec.
   No singleton WFFunEnv or caller-provided body proof is assumed. *)
Theorem V293_irq_internal_WFFunEnv : forall enter sched running nesting unmap group rows high y
 brun bn bt bg br bh li Hli sd inv,
 enter<>sched ->unmap<>y ->group<>y ->rows<>y ->high<>y ->
 WFFunEnv(V293_irq_internal_unit enter sched running nesting unmap group rows high y)
 (V293_irq_internal_spec enter sched running nesting unmap group rows high brun bn bt bg br bh li Hli)
 sd li inv.
Proof.
 intros enter sched running nesting unmap group rows high y brun bn bt bg br bh li Hli sd inv
 Distinct UY GY RY HY. split;[apply V293_irq_internal_domains| ].
 intros f pre post t tl Lookup. unfold V293_irq_internal_spec in Lookup.
 destruct(Z.eq_dec f enter)as[E|NE].
 - inversion Lookup;subst pre post t tl. exists dnil. exists dnil.
   exists(V293_OSIntEnter_body running nesting). split.
   + unfold V293_irq_internal_unit,pumerge,V293_OSIntEnter_unit.
     destruct(Z.eq_dec f enter);[reflexivity|contradiction].
   + split;[constructor| ]. split;[reflexivity| ].
     intros vl p r lg tid Pre Post. eapply V293_OSIntEnter_internal_contract;try eassumption.
     unfold V293_irq_internal_unit,pumerge,V293_OSIntEnter_unit.
     destruct(Z.eq_dec f enter);[reflexivity|contradiction].
 - unfold V293_OSSchedNew_internal_spec in Lookup.
   destruct(Z.eq_dec f sched);[ |discriminate]. inversion Lookup;subst pre post t tl.
   exists dnil. exists(dcons y Tint8 dnil). exists(V293_OSSchedNew_body unmap group rows high y).
   split.
   + unfold V293_irq_internal_unit,pumerge,V293_OSIntEnter_unit,V293_OSSchedNew_internal_unit.
     destruct(Z.eq_dec f enter), (Z.eq_dec f sched);try contradiction;reflexivity.
   + split;[constructor| ]. split;[reflexivity| ].
     intros vl p r lg tid Pre Post. eapply V293_OSSchedNew_internal_contract;try eassumption.
     unfold V293_irq_internal_unit,pumerge,V293_OSIntEnter_unit,V293_OSSchedNew_internal_unit.
     destruct(Z.eq_dec f enter), (Z.eq_dec f sched);try contradiction;reflexivity.
Qed.

Lemma V293_irq_internal_WFIFun : forall enter sched running nesting unmap group rows high y
 brun bn bt bg br bh li Hli sd inv,
 enter<>sched ->unmap<>y ->group<>y ->rows<>y ->high<>y ->
 WFIFun(V293_irq_internal_unit enter sched running nesting unmap group rows high y)
 (V293_irq_internal_spec enter sched running nesting unmap group rows high brun bn bt bg br bh li Hli)
 sd inv li.
Proof.
 intros. destruct(V293_irq_internal_WFFunEnv enter sched running nesting unmap group rows high y
 brun bn bt bg br bh li Hli sd inv H H0 H1 H2 H3)as[Dom Body].
 split;[exact Dom| ]. intros f p q t tl Lookup.
 destruct(Body f p q t tl Lookup)as(d1&d2&s&Code&Types&Decls&Checked).
 exists d1;exists d2;exists s;auto.
Qed.

Lemma V293_irq_internal_syntax : forall enter sched running nesting unmap group rows high y,
 good_os_pu(V293_irq_internal_unit enter sched running nesting unmap group rows high y).
Proof.
 intros enter sched running nesting unmap group rows high y f t d1 d2 s Code.
 unfold V293_irq_internal_unit,pumerge,V293_OSIntEnter_unit,V293_OSSchedNew_internal_unit in Code.
 destruct(Z.eq_dec f enter), (Z.eq_dec f sched);try discriminate;
 inversion Code;subst;split;[reflexivity|repeat split|reflexivity|repeat split|reflexivity|repeat split].
Qed.

Lemma V293_irq_clock_disjoint : forall version settime gettime enter sched now ticks saved
 running nesting unmap group rows high y,
 enter<>version ->enter<>settime ->enter<>gettime ->
 sched<>version ->sched<>settime ->sched<>gettime ->
 no_fun_same(V293_clock_api_unit version settime gettime now ticks saved)
 (V293_irq_internal_unit enter sched running nesting unmap group rows high y).
Proof.
 intros. unfold no_fun_same,V293_clock_api_unit,V293_component_api_unit,V293_irq_internal_unit,pumerge,
 V293_OSVersion_api_unit,V293_TimeSet_api_unit,V293_TimeGet_api_unit,
 V293_OSIntEnter_unit,V293_OSSchedNew_internal_unit.
 split;intros f Bound;repeat destruct Z.eq_dec;congruence.
Qed.

(* This extends the existing partial clock component with real OSIntEnter,
   while keeping precisely the same name-local and shared-time invariant. *)
Theorem V293_irq_clock_components_checked : forall version settime gettime enter sched now ticks saved btime
 running nesting unmap group rows high y brun bn bt bg br bh lg,
 enter<>sched ->enter<>version ->enter<>settime ->enter<>gettime ->
 sched<>version ->sched<>settime ->sched<>gettime ->
 ticks<>saved ->now<>ticks ->now<>saved ->
 unmap<>y ->group<>y ->rows<>y ->high<>y ->
 let li:=V293_time_names_li now btime in
 let Spec:=V293_irq_internal_spec enter sched running nesting unmap group rows high
 brun bn bt bg br bh li(V293_time_names_local_good now btime)in
 GoodI(V293_time_shared_inv btime)V293_scheduler li /\
 WFAPI(V293_clock_api_unit version settime gettime now ticks saved)
 (V293_clock_api_spec version settime gettime)li Spec V293_scheduler(V293_time_shared_inv btime)lg /\
 WFFunEnv(V293_irq_internal_unit enter sched running nesting unmap group rows high y)
 Spec V293_scheduler li(V293_time_shared_inv btime) /\
 WFIFun(V293_irq_internal_unit enter sched running nesting unmap group rows high y)
 Spec V293_scheduler(V293_time_shared_inv btime)li /\
 no_fun_same(V293_clock_api_unit version settime gettime now ticks saved)
 (V293_irq_internal_unit enter sched running nesting unmap group rows high y).
Proof.
 intros version settime gettime enter sched now ticks saved btime running nesting unmap group rows high y
 brun bn bt bg br bh lg ES EV ET EG SV ST SG TS NT NS UY GY RY HY li Spec.
 split;[apply V293_time_names_good| ]. split.
 - apply V293_clock_WFAPI;try assumption.
   + apply V293_time_names_local_good.
   + apply V293_time_names_noabs.
   + apply V293_time_names_global.
 - split;[apply V293_irq_internal_WFFunEnv;assumption| ].
   split;[apply V293_irq_internal_WFIFun;assumption| ].
   apply V293_irq_clock_disjoint;assumption.
Qed.
