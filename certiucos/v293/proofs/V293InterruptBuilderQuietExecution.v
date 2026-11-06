(* Same program and builder heap for every non-dispatch branch.
   The saturated pair changes 255 to 254; it is not a memory identity. *)
Require Import CertiOS.certiucos.v293.proofs.V293InterruptBuilderNestedReturn.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptBuilderNestedExit.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptBuilderEnterResources.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptBuilderEnterCall.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptControlExecution.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptFixedControlSpec.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptControlRetention.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptQuietISRReturn.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptQuietBuilder.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptBindings.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptQuietContinuous.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitCallExecution.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitExecution.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyDynamic.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitInterruptGlobal.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptSourceRoundtrip.
Require Import CertiOS.certiucos.v293.proofs.V293LocalGlobalTrace.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyGlobalTrace.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.code.V293OSIntEnter.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterInternal.
Require Import CertiOS.certiucos.v293.code.V293OSIntExit.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.framework.proof.join_prop.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition V293_quiet_call_memory bn run nest M :=
 if Nat.eqb run 1 then V293_control_decrement_memory bn nest M else M.

(* Allocation, initialization, execution and free are all internal.
   This covers locked outermost, non-running and positive nested inputs. *)
Theorem V293_quiet_call_exact : forall P ks ge caller M ir enabled si ci
 f running nesting lock saved table high target current counter sched_id int_switch br bn bl run nest locked,
 P f=Some(V293_OSIntExit_abstract_function running nesting lock saved table high target current counter sched_id int_switch) ->
 saved<>running ->saved<>nesting ->saved<>lock ->
 run<256 ->nest<256 ->locked<256 ->
 V293_control_dispatch(V293_control run nest locked)=false ->br<>bn ->bl<>bn ->
 get ge running=Some(br,Tint8) ->get ge nesting=Some(bn,Tint8) ->get ge lock=Some(bl,Tint8) ->
 load Tint8 M(br,0%Z)=Some(V293_byteval run) ->
 load Tint8 M(bn,0%Z)=Some(V293_byteval nest) ->
 load Tint8 M(bl,0%Z)=Some(V293_byteval locked) ->
 (exists old,get M(bn,0%Z)=Some(true,old)) ->
 V293_local_steps P(curs(scall f nil),(kenil,ks))((ge,caller,M),ir,(enabled,si,ci))
 (curs(sskip None),(kenil,ks))((ge,caller,V293_quiet_call_memory bn run nest M),ir,(enabled,si,ci)).
Proof.
 intros P ks ge caller M ir enabled si ci f running nesting lock saved table high target current counter
 sched_id int_switch br bn bl run nest locked Program SR SN SL R N L Quiet BR BL GR GN GL LR LN LL[old Writable].
 destruct(memory_has_fresh_block M)as[bs Fresh].
 assert(BRfresh:bs<>br)by(eapply V293_success_load_not_fresh;eassumption).
 assert(BNfresh:bs<>bn)by(eapply V293_success_load_not_fresh;eassumption).
 assert(BLfresh:bs<>bl)by(eapply V293_success_load_not_fresh;eassumption).
 destruct(V293_success_scheduler_storage M bs Fresh)as[Ms[Init[W[Free Frame]]]].
 set(le:=set(emp:env)saved(bs,Tint32)).
 set(body:=V293_OSIntExit_abstract_body running nesting lock saved table high target current counter sched_id int_switch).
 assert(Saved:get le saved=Some(bs,Tint32))by(unfold le;apply map_get_set).
 assert(NR:get le running=None)by(unfold le;rewrite map_get_set' by exact SR;apply map_emp_get).
 assert(NN:get le nesting=None)by(unfold le;rewrite map_get_set' by exact SN;apply map_emp_get).
 assert(NL:get le lock=None)by(unfold le;rewrite map_get_set' by exact SL;apply map_emp_get).
 assert(R0:load Tint8 Ms(br,0%Z)=Some(V293_byteval run)).
 { etransitivity;[apply V293_load_block_frame;intro i;apply Frame;congruence|exact LR]. }
 assert(N0:load Tint8 Ms(bn,0%Z)=Some(V293_byteval nest)).
 { etransitivity;[apply V293_load_block_frame;intro i;apply Frame;congruence|exact LN]. }
 assert(L0:load Tint8 Ms(bl,0%Z)=Some(V293_byteval locked)).
 { etransitivity;[apply V293_load_block_frame;intro i;apply Frame;congruence|exact LL]. }
 assert(WN:get Ms(bn,0%Z)=Some(true,old))by(rewrite Frame by congruence;exact Writable).
 assert(Addr:getaddr le=[(bs,Tint32)])by(unfold le;reflexivity).
 assert(FreeFinal:free Tint32 bs(V293_quiet_call_memory bn run nest Ms)=
 Some(V293_quiet_call_memory bn run nest M)).
 { unfold V293_quiet_call_memory;destruct(Nat.eqb run 1);[destruct nest| ];
   cbn[V293_control_decrement_memory];try exact Free.
   eapply V293_nested_saved_free;eassumption. }
 pose proof(V293_nested_void_return_exact P(kcall f body caller ks)ge le caller
 (V293_quiet_call_memory bn run nest Ms)(V293_quiet_call_memory bn run nest M)
 f body ks bs eq_refl Addr FreeFinal)as Return.
 assert(BodyTrace:V293_local_steps P(curs body,(kenil,kcall f body caller ks))
 ((ge,le,allocb M bs 0%Z 4),ir,(enabled,si,ci))
 (curs(sskip None),(kenil,ks))((ge,caller,V293_quiet_call_memory bn run nest M),ir,(enabled,si,ci))).
 { unfold body,V293_OSIntExit_abstract_body.
   eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sseq_step]| ].
   eapply V293_local_trans.
   { apply V293_csteps_local;eapply V293_success_assign_zero;eassumption. }
   eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sskip_step]| ].
   eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sseq_step]| ].
   eapply V293_local_trans.
   { apply V293_csteps_local;eapply V293_entry_if_select with(flag:=Nat.eqb run 1).
     unfold V293_OSIntEnter_running;change Int.one with(Int.repr(Z.of_nat 1)).
     exact(V293_success_global_byte_eq ge le Ms running br run 1 R ltac:(lia)NR GR R0). }
   destruct(Nat.eqb run 1)eqn:Running.
   - apply Nat.eqb_eq in Running;subst run.
     cbn[V293_quiet_call_memory]in Return.
     assert(Obs:=V293_control_decrement_observation br bn bl Ms nest locked N L BR BL R0 N0 L0).
     destruct Obs as[NewN[NewL[Read Off]]].
     assert(Middle:cstepstar P
       (curs(V293_OSIntExit_nesting_dispatch nesting lock
       (V293_OSIntExit_dispatch table high target current counter sched_id int_switch)),
       (kenil,kseq(sprim excrit)(kseq sret(kcall f body caller ks))))
       (ge,le,Ms)(curs(sskip None),(kenil,kseq(sprim excrit)(kseq sret(kcall f body caller ks))))
       (ge,le,V293_control_decrement_memory bn nest Ms)).
     { unfold V293_OSIntExit_nesting_dispatch.
       eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply sseq_step]| ].
       eapply V293_cstepstar_trans.
       { eapply V293_control_decrement_execution;[exact N|exact NN|exact GN|exact N0|exists old;exact WN]. }
       eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply sskip_step]| ].
       unfold V293_control_dispatch in Quiet;cbn in Quiet.
       unfold V293_exit_enabled,V293_exit_depth in Quiet.
       pose proof(V293_control_guards_execution P
       (kseq(sprim excrit)(kseq sret(kcall f body caller ks)))ge le
       (V293_control_decrement_memory bn nest Ms)nesting lock bn bl(Nat.pred nest)locked
       (V293_OSIntExit_dispatch table high target current counter sched_id int_switch)
       ltac:(lia)L ltac:(unfold V293_interrupt_env;auto)NewN NewL)as Guard.
       rewrite Quiet in Guard;exact Guard. }
     eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sseq_step]| ].
     eapply V293_local_cons;[apply encrit_step;reflexivity| ].
     eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sskip_step]| ].
     eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sseq_step]| ].
     eapply V293_local_trans;[apply V293_csteps_local;exact Middle| ].
     eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sskip_step]| ].
     eapply V293_local_cons;[apply excrit_step;reflexivity| ].
     eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sskip_step]| ].
     apply V293_csteps_local;exact Return.
   - unfold V293_quiet_call_memory in Return;rewrite Running in Return.
     unfold V293_quiet_call_memory;rewrite Running.
     eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sskip_step]| ].
     apply V293_csteps_local;exact Return. }
 eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply snpcall_step]| ].
 eapply V293_local_cons.
 { apply ostc_step;eapply stmt_step;[reflexivity| ];eapply sfexec_step with(d1:=dnil)(d2:=dcons saved Tint32 dnil).
   - reflexivity.
   - reflexivity.
   - exact Program.
   - exact I.
   - reflexivity. }
 eapply V293_local_cons.
 { apply ostc_step;eapply stmt_step;[reflexivity| ];eapply salloclv_step;try reflexivity.
   exists bs;split;[exact Fresh| ];split;[reflexivity| ];split.
   - intros[v V];rewrite map_emp_get in V;discriminate.
   - reflexivity. }
 eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sallocend_step]| ].
 exact BodyTrace.
Qed.

Section BuilderQuiet.
Variables target running nesting lock:var.
Variables bt bg br bh bp bc bk brun bn bl:block.
Variable rest:list(addr*type).
Let li:=V293_irq_bound_li running nesting lock brun bn bl.
Let Inv0:=V293_ready_dynamic_exit_inv target bt bg br bh bp bc bk brun bn bl rest.
Let snapshot:=V293_irq_bound_snapshot target running nesting lock bt bg br bh bp bc bk brun bn bl rest.

Lemma V293_builder_snapshot_exit_memory : forall run nest locked aop enabled ir si ci t ge le M O,
 nest<256 ->
 (ge,le,M,ir,(enabled,si,ci),O,aop)|=snapshot run nest locked aop enabled ir si ci t ->
 (ge,le,V293_quiet_call_memory bn run nest M,ir,(enabled,si,ci),O,aop)|=
 snapshot run(V293_control_nesting(V293_control_exit(V293_control run nest locked)))locked aop enabled ir si ci t.
Proof.
 intros run nest locked aop enabled ir si ci t ge le M O Bound Held.
 unfold V293_quiet_call_memory,V293_control_exit;cbn[V293_control_nesting V293_control_running V293_control_lock].
 destruct(Nat.eqb run 1);[destruct nest as [ | n ]| ];cbn[V293_control_decrement_memory Nat.pred];try exact Held.
 set(Frame:=<||aop||> ** OS[ir,enabled,si,ci] **
   (Amapsto(brun,0%Z)Tint8 true(V293_byteval run) **
   (Amapsto(bl,0%Z)Tint8 true(V293_byteval locked) **
   (p_local li t nil ** Aemp **
    (V293_quiet_irq_kept target bt bg br bh bp bc bk rest ** A_dom_lenv nil))))).
 assert(Owned:(ge,le,M,ir,(enabled,si,ci),O,aop)|=Amapsto(bn,0%Z)Tint8 true(V293_byteval(S n)) **Frame).
 { unfold Frame,li;clear -Held;unfold snapshot,V293_irq_bound_snapshot,V293_enter_bound_external in Held;sep auto. }
 destruct(V293_builder_byte_writable _ _ _ _ Owned)as[v Writable].
 destruct(V293_tick_raw_slot_update(bn,0%Z)Tint8(V293_byteval(S n))(V293_byteval n)
 Frame ge le M ir(enabled,si,ci)O aop(V293_byte_type n ltac:(lia))Owned)as[Mf[Store Updated]].
 assert(Same:Mf=V293_put_byte M(bn,0%Z)n).
 { pose proof(V293_put_byte_store M(bn,0%Z)n v Writable);congruence. }
 subst Mf;clear Held Owned.
 unfold V293_owned_record_cell in Updated;apply astar_mono with
 (P':=Amapsto(bn,0%Z)Tint8 true(V293_byteval n))(Q':=Frame)in Updated.
 2:{ intros s K;apply astar_l_apure_elim in K;tauto. }
 2:{ intros s K;exact K. }
 unfold snapshot,V293_irq_bound_snapshot,V293_enter_bound_external,Frame,li in *;sep auto.
Qed.

(* Stable source-local interface: one input builder, one exact resulting heap,
   one fixed control trace. No quiet-filter assertion or execution premise. *)
Theorem V293_builder_quiet_execution : forall intspec i ir si t lg pre aop st P (sd:ossched)
 entry exit vector saved table high current counter sched_id int_switch c,
 intspec i=Some aop ->Some pre=BuildintPre i intspec ir si Inv0 li t lg ->st|=pre ->
 V293_control_capture brun bn bl st=Some(getabst st,c) ->
 V293_control_dispatch(V293_control_enter c)=false ->
 P entry=Some(V293_OSIntEnter_function running nesting) ->
 P exit=Some(V293_OSIntExit_abstract_function running nesting lock saved table high target current counter sched_id int_switch) ->
 saved<>running ->saved<>nesting ->saved<>lock ->
 i=Z.to_nat(Int.unsigned vector) ->(0<=Int.unsigned vector<Z.of_nat INUM)%Z ->
 let final:=V293_control_exit(V293_control_enter c)in
 let Mf:=V293_put_byte(getmem st)(bn,0%Z)(V293_control_nesting final)in
 V293_local_steps P(curs(V293_irq_source_wrapper entry exit vector),(kenil,kstop))(gettaskst st)
 (curs(sprim exint),(kenil,kstop))((getgenv st,emp,Mf),isrupd(isrupd ir i true)i false,(false,i::si,nil)) /\
 (getgenv st,emp,Mf,isrupd(isrupd ir i true)i false,(false,i::si,nil),getabst st,aop)|=
 snapshot(V293_control_running final)(V293_control_nesting final)(V293_control_lock final)
 aop false(isrupd(isrupd ir i true)i false)(i::si)nil t /\
 V293_control_capture brun bn bl
 (getgenv st,emp,Mf,isrupd(isrupd ir i true)i false,(false,i::si,nil),getabst st,aop)=Some(getabst st,final) /\
 V293_control_steps sd V293_fixed_control_handler(getabst st,c)
 (V293_control_Core(spec_done None))(getabst st,final) /\
 V293_control_valid final.
Proof.
 intros intspec i ir si t lg pre aop st P sd entry exit vector saved table high current counter sched_id int_switch
 c Lookup Pre Held Capture Quiet Enter Exit SR SN SL Vector Range.
 destruct(V293_builder_enter_prefix target running nesting lock bt bg br bh bp bc bk brun bn bl rest
 intspec i ir si t lg pre aop st P sd entry exit vector Lookup Pre Held Enter Vector Range)
 as[c0[Me[Valid[Captured[Prefix[After[Read[Step Frame]]]]]]]].
 rewrite Capture in Captured;inversion Captured;subst c0.
 pose proof(V293_control_enter_valid c Valid)as EnterValid.
 pose proof(V293_control_exit_valid _ EnterValid)as FinalValid.
 destruct c as[run nest locked];destruct EnterValid as[R[N L]].
 change(run<256)in R;change(V293_interrupt_nest_after run nest<256)in N;change(locked<256)in L.
 change((getgenv st,emp,Me,isrupd(isrupd ir i true)i false,(false,i::si,nil),getabst st,aop)|=
 snapshot run(V293_interrupt_nest_after run nest)locked aop false(isrupd(isrupd ir i true)i false)(i::si)nil t)in After.
 destruct(V293_builder_snapshot_memory target running nesting lock bt bg br bh bp bc bk brun bn bl rest
 run(V293_interrupt_nest_after run nest)locked aop false(isrupd(isrupd ir i true)i false)(i::si)nil t
 (getgenv st,emp,Me,isrupd(isrupd ir i true)i false,(false,i::si,nil),getabst st,aop)R N L After)
 as[GR[GN[GL[LR[LN[LL[W[BR BL]]]]]]]].
 pose proof(V293_quiet_call_exact P(kseq(sprim exint)kstop)(getgenv st)emp Me
 (isrupd(isrupd ir i true)i false)false(i::si)nil exit running nesting lock saved table high target current counter
 sched_id int_switch brun bn bl run(V293_interrupt_nest_after run nest)locked
 Exit SR SN SL R N L Quiet BR BL GR GN GL LR LN LL W)as ExitTrace.
 pose proof(V293_builder_snapshot_exit_memory run(V293_interrupt_nest_after run nest)locked aop false
 (isrupd(isrupd ir i true)i false)(i::si)nil t(getgenv st)emp Me(getabst st)N After)as Returned.
 set(final:=V293_control_exit(V293_control_enter(V293_control run nest locked))).
 set(Mf:=V293_quiet_call_memory bn run(V293_interrupt_nest_after run nest)Me)in *.
 assert(Same:Mf=V293_put_byte(getmem st)(bn,0%Z)(V293_control_nesting final)).
 { assert(ByteOwned:(getgenv st,emp,Mf,isrupd(isrupd ir i true)i false,(false,i::si,nil),getabst st,aop)|=
   Amapsto(bn,0%Z)Tint8 true(V293_byteval(V293_control_nesting final)) **Atrue).
   { clear -Returned;unfold snapshot,V293_irq_bound_snapshot,V293_enter_bound_external in Returned;sep auto. }
   apply V293_nested_owned_byte_get in ByteOwned.
   apply HalfPermMap.extensionality;intro a;destruct(map_dec_a a(bn,0%Z))as[E|E].
   - subst a;change(get Mf(bn,0%Z)=get(V293_put_byte(getmem st)(bn,0%Z)(V293_control_nesting final))(bn,0%Z)).
     unfold V293_put_byte;rewrite map_get_set;exact ByteOwned.
   - change(get Mf a=get(V293_put_byte(getmem st)(bn,0%Z)(V293_control_nesting final))a).
     rewrite V293_put_byte_other by exact E.
     unfold Mf,V293_quiet_call_memory;destruct(Nat.eqb run 1);[destruct(V293_interrupt_nest_after run nest)| ];
     cbn[V293_control_decrement_memory];try(rewrite V293_put_byte_other by exact E);apply Frame;exact E. }
 cbn zeta;fold final;rewrite <-Same.
 split.
 - eapply V293_local_trans;[exact Prefix| ];eapply V293_local_trans;[exact ExitTrace| ].
   eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sskip_step]|apply V293_local_refl].
 - split;[exact Returned| ];split.
   + change(V293_control_capture brun bn bl
       (getgenv st,emp,Mf,isrupd(isrupd ir i true)i false,(false,i::si,nil),getabst st,aop)=
       Some(getabst st,V293_control(V293_control_running final)(V293_control_nesting final)(V293_control_lock final))).
     pose proof(V293_control_capture_owned brun bn bl
       (V293_control_running final)(V293_control_nesting final)(V293_control_lock final)
       (getgenv st,emp,Mf,isrupd(isrupd ir i true)i false,(false,i::si,nil),getabst st,aop))as C.
     apply C;[exact(proj1 FinalValid)|exact(proj1(proj2 FinalValid))|exact(proj2(proj2 FinalValid))| ].
     eapply V293_irq_bound_snapshot_controls;exact Returned.
   + split;[ |exact FinalValid].
     pose proof(V293_fixed_control_handler_prefix sd(getabst st)(V293_control run nest locked)Valid)as Fixed.
     rewrite(V293_control_quiet_code _ Quiet)in Fixed;exact Fixed.
Qed.

Theorem V293_builder_quiet_return_ready : forall intspec i ir si t lg pre ret st P (sd:ossched)
 entry exit vector saved table high current counter sched_id int_switch c,
 intspec i=Some(spec_done None) ->
 Some pre=BuildintPre i intspec ir si Inv0 li t lg ->Some ret=BuildintRet i intspec ir si Inv0 li t lg ->st|=pre ->
 V293_control_capture brun bn bl st=Some(getabst st,c) ->V293_control_dispatch(V293_control_enter c)=false ->
 P entry=Some(V293_OSIntEnter_function running nesting) ->
 P exit=Some(V293_OSIntExit_abstract_function running nesting lock saved table high target current counter sched_id int_switch) ->
 saved<>running ->saved<>nesting ->saved<>lock ->
 i=Z.to_nat(Int.unsigned vector) ->(0<=Int.unsigned vector<Z.of_nat INUM)%Z ->
 let final:=V293_control_exit(V293_control_enter c)in
 let Mf:=V293_put_byte(getmem st)(bn,0%Z)(V293_control_nesting final)in
 V293_local_steps P(curs(V293_irq_source_wrapper entry exit vector),(kenil,kstop))(gettaskst st)
 (curs(sprim exint),(kenil,kstop))((getgenv st,emp,Mf),isrupd(isrupd ir i true)i false,(false,i::si,nil)) /\
 (getgenv st,emp,Mf,isrupd ir i false,(false,i::si,nil),getabst st,spec_done None)|=ret /\
 V293_control_steps sd V293_fixed_control_handler(getabst st,c)
 (V293_control_Core(spec_done None))(getabst st,final).
Proof.
 intros intspec i ir si t lg pre ret st P sd entry exit vector saved table high current counter sched_id int_switch
 c Lookup Pre Ret Held Capture Quiet Enter Exit SR SN SL Vector Range.
 destruct(V293_builder_quiet_execution intspec i ir si t lg pre(spec_done None)st P sd entry exit vector
 saved table high current counter sched_id int_switch c Lookup Pre Held Capture Quiet Enter Exit SR SN SL Vector Range)
 as[Trace[After[Read[Fixed Valid]]]].
 cbn zeta;split;[exact Trace| ];split;[ |exact Fixed].
 assert(LowerISR:forall j,j<i ->ir j=false).
 { unfold BuildintPre in Pre;rewrite Lookup in Pre;inversion Pre;subst pre;eapply V293_irq_builder_lower_clear;exact Held. }
 rewrite V293_irq_eoi_exact in After.
 unfold BuildintRet in Ret;rewrite Lookup in Ret;inversion Ret;subst ret.
 destruct Valid as[R[N L]].
 eapply V293_bound_quiet_partial_return with
 (run:=V293_control_running(V293_control_exit(V293_control_enter c)))
 (nest:=V293_control_nesting(V293_control_exit(V293_control_enter c)))
 (locked:=V293_control_lock(V293_control_exit(V293_control_enter c)));
 [exact R|exact N|exact L|exact LowerISR|exact After].
Qed.


(* Actual pint/body/exint; contexts restore exactly, while the computed byte may change. *)
Theorem V293_builder_quiet_global_return : forall pc po pi ip T les aus cst t
 ge caller M ir si O interrupted ike ks intspec i lg pre ret (sd:ossched)
 entry exit vector saved table high current counter sched_id int_switch c,
 get T t=Some(interrupted,(ike,ks)) ->get les t=Some caller ->get aus t=Some((true,si,nil):localst) ->
 goodks(pc,(po,pi,ip))(kint interrupted ike caller ks) ->higherint ir i ->i<INUM ->
 ip i=Some(V293_irq_source_wrapper entry exit vector) ->
 intspec i=Some(spec_done None) ->
 Some pre=BuildintPre i intspec ir si Inv0 li t lg ->Some ret=BuildintRet i intspec ir si Inv0 li t lg ->
 (ge,emp,M,isrupd ir i true,(false,i::si,nil),O,spec_done None)|=pre ->
 V293_control_capture brun bn bl(ge,emp,M,isrupd ir i true,(false,i::si,nil),O,spec_done None)=
 Some(O,c) ->V293_control_dispatch(V293_control_enter c)=false ->
 (pumerge po pi)entry=Some(V293_OSIntEnter_function running nesting) ->
 (pumerge po pi)exit=Some(V293_OSIntExit_abstract_function running nesting lock saved table high target current counter sched_id int_switch) ->
 saved<>running ->saved<>nesting ->saved<>lock ->
 i=Z.to_nat(Int.unsigned vector) ->(0<=Int.unsigned vector<Z.of_nat INUM)%Z ->
 let final:=V293_control_exit(V293_control_enter c)in
 let Mf:=V293_put_byte M(bn,0%Z)(V293_control_nesting final)in
 let entered:=(set T t(curs(V293_irq_source_wrapper entry exit vector),(kenil,kint interrupted ike caller ks)),
 (ge,set les t emp,M,isrupd ir i true,set aus t(false,i::si,nil)),t)in
 let returning:=(set T t(curs(sprim exint),(kenil,kint interrupted ike caller ks)),
 (ge,set les t emp,Mf,ir,set aus t(false,i::si,nil)),t)in
 (match entered with(Ti,Si,ti)=>lpstep(pc,(po,pi,ip))T cst(ge,les,M,ir,aus)t Ti cst Si ti end) /\
 V293_global_steps(pc,(po,pi,ip))cst entered returning /\
 (match returning with(Tr,Sr,tr)=>lpstep(pc,(po,pi,ip))Tr cst Sr tr T cst(ge,les,Mf,ir,aus)t end) /\
 (ge,emp,Mf,isrupd ir i false,(false,i::si,nil),O,spec_done None)|=ret /\
 V293_control_steps sd V293_fixed_control_handler(O,c)(V293_control_Core(spec_done None))(O,final).
Proof.
 intros pc po pi ip T les aus cst t ge caller M ir si O interrupted ike ks intspec i lg pre ret sd
 entry exit vector saved table high current counter sched_id int_switch c
 Code Env Aux Good Higher Inum Installed Lookup Pre Ret Held Capture Quiet Enter Exit SR SN SL Vector Range.
 destruct(V293_builder_quiet_return_ready intspec i ir si t lg pre ret
 (ge,emp,M,isrupd ir i true,(false,i::si,nil),O,spec_done None)(pumerge po pi)sd entry exit vector
 saved table high current counter sched_id int_switch c Lookup Pre Ret Held Capture Quiet Enter Exit SR SN SL Vector Range)
 as[Trace[Ready Fixed]].
 assert(Clear:ir i=false)by(apply Higher;lia).
 rewrite V293_interrupt_eoi_restores_ir in Trace by exact Clear.
 pose proof(V293_interrupt_local_steps_global pc po pi ip _ _ _ _ Trace
 interrupted ike caller ks T les aus t cst Good)as Lifted.
 cbn zeta;set(Mf:=V293_put_byte M(bn,0%Z)(V293_control_nesting(V293_control_exit(V293_control_enter c))));split;[eapply V293_interrupt_source_enter;eassumption| ];split;[exact Lifted| ];split;[ |split;[exact Ready|exact Fixed]].
 assert(TSame:set T t(interrupted,(ike,ks))=T)by(exact(TasksMod.get_set_same Code)).
 assert(ESame:set les t caller=les)by(exact(CltEnvMod.get_set_same Env)).
 assert(ASame:set aus t((true,si,nil):localst)=aus)by(exact(TaskLStMod.get_set_same Aux)).
 assert(Return:lpstep(pc,(po,pi,ip))
 (set T t(curs(sprim exint),(kenil,kint interrupted ike caller ks)))cst
 (ge,set les t emp,Mf,ir,set aus t(false,i::si,nil))t
 (set T t(interrupted,(ike,ks)))cst
 (ge,set les t caller,Mf,ir,set aus t((true,si,nil):localst))t).
 { eapply pt_step.
   - apply map_get_set.
   - symmetry;apply set_set_eq.
   - unfold projS,projD;rewrite !map_get_set;reflexivity.
   - unfold projS,projD;rewrite !map_get_set;reflexivity.
   - split;[unfold Dteq|unfold Piteq];intros other Ne;cbn;
     rewrite !map_get_set';reflexivity||congruence.
   - eapply inapi_step;[reflexivity| | ].
     + eapply exint_step;reflexivity.
     + exists(curs(sprim exint));exists kenil;exists(kint interrupted ike caller ks).
       split;[reflexivity|right;right;discriminate]. }
 rewrite TSame,ESame,ASame in Return;exact Return.
Qed.
End BuilderQuiet.
