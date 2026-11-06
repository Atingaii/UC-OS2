(* Nested branch only, under the explicit ADR-0005 normalization boundary.
   Fresh saved storage disappears from the entire resulting heap. *)
Require Import CertiOS.certiucos.v293.proofs.V293InterruptBuilderEnterResources.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitCallExecution.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitExecution.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptBuilderEnterCall.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptControlExecution.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptFixedControlSpec.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptControlRetention.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptBindings.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptQuietBuilder.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptQuietContinuous.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptSourceRoundtrip.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyDynamic.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293LocalGlobalTrace.
Require Import CertiOS.certiucos.v293.code.V293OSIntEnter.
Require Import CertiOS.certiucos.v293.code.V293OSIntExit.
Require Import CertiOS.certiucos.v293.code.V293OSSchedGuards.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Lemma V293_nested_saved_free : forall M Ms bs bn n,
 fresh M bs -> bs<>bn ->
 V293_bytes_writable Ms bs 0%Z 4 -> free Tint32 bs Ms=Some M ->
 free Tint32 bs(V293_put_byte Ms(bn,0%Z)n)=Some(V293_put_byte M(bn,0%Z)n).
Proof.
 intros M Ms bs bn n Fresh Different W Back.
 set(M1:=V293_put_byte Ms(bn,0%Z)n).
 assert(W1:V293_bytes_writable M1 bs 0%Z 4).
 { intros k K;unfold M1;rewrite V293_put_byte_other by congruence;apply W;exact K. }
 destruct(V293_freeb_construct 4 M1 bs 0%Z W1)as[Mf Free].
 assert(Same:Mf=V293_put_byte M(bn,0%Z)n).
 { apply HalfPermMap.extensionality;intros[b i].
   change(get Mf(b,i)=get(V293_put_byte M(bn,0%Z)n)(b,i)).
   destruct(Pos.eq_dec b bs)as[E|E].
   - subst b;rewrite V293_put_byte_other by congruence.
     destruct(Z_lt_ge_dec i 0), (Z_lt_ge_dec i 4).
     + rewrite(V293_freeb_outside _ _ _ _ _ _ _ Free)by(right;left;lia).
       unfold M1;rewrite V293_put_byte_other by congruence.
       symmetry;eapply V293_freeb_outside;[exact Back|right;left;lia].
     + lia.
     + change(get Mf(bs,i)=get M(bs,i)).
       rewrite(V293_success_fresh_none M bs Fresh i).
       replace i with(0+Z.of_nat(Z.to_nat i))%Z by(rewrite Z2Nat.id;lia).
       eapply V293_freeb_removed;[exact Free|lia].
     + rewrite(V293_freeb_outside _ _ _ _ _ _ _ Free)by(right;right;lia).
       unfold M1;rewrite V293_put_byte_other by congruence.
       symmetry;eapply V293_freeb_outside;[exact Back|right;right;cbn;lia].
   - rewrite(V293_freeb_outside _ _ _ _ _ _ _ Free)by(left;exact E).
     unfold M1,V293_put_byte.
     destruct(map_dec_a(bn,0%Z)(b,i))as[A|A].
     + inversion A;subst b i;repeat rewrite map_get_set;reflexivity.
     + repeat rewrite map_get_set' by exact A.
       symmetry;eapply V293_freeb_outside;[exact Back|left;exact E]. }
 subst Mf;exact Free.
Qed.

Lemma V293_nested_void_return_exact : forall P ks ge le caller M Mf f body next bs,
 callcont ks=Some(kcall f body caller next) ->getaddr le=[(bs,Tint32)] ->
 free Tint32 bs M=Some Mf ->
 cstepstar P(curs sret,(kenil,ks))(ge,le,M)
 (curs(sskip None),(kenil,next))(ge,caller,Mf).
Proof.
 intros P ks ge le caller M Mf f body next bs Call Addr Free.
 eapply c_stepstarn.
 { eapply stmt_step;[reflexivity|eapply sret_step;eassumption||reflexivity]. }
 eapply c_stepstarn.
 { eapply stmt_step;[reflexivity|eapply sfree_step;eassumption||reflexivity]. }
 eapply c_stepstarn.
 { eapply stmt_step;[reflexivity|eapply sfreeend_step;eassumption||reflexivity]. }
 apply c_stepstar0.
Qed.

Lemma V293_nested_body_exact : forall P ks ge le caller M M0 M1 Mf ir enabled si ci
 running nesting lock saved table high target current counter sched_id int_switch br bn bs n f body next,
 2<=n -> n<256 -> get le saved=Some(bs,Tint32) ->
 store Tint32 M(bs,0%Z)(Vint32 Int.zero)=Some M0 ->
 get le running=None -> get ge running=Some(br,Tint8) ->
 load Tint8 M0(br,0%Z)=Some(V293_byteval 1) ->
 get le nesting=None -> get ge nesting=Some(bn,Tint8) ->
 load Tint8 M0(bn,0%Z)=Some(V293_byteval n) ->
 store Tint8 M0(bn,0%Z)(V293_byteval(Nat.pred n))=Some M1 ->
 callcont ks=Some(kcall f body caller next) -> getaddr le=[(bs,Tint32)] ->
 free Tint32 bs M1=Some Mf ->
 V293_local_steps P
 (curs(V293_OSIntExit_abstract_body running nesting lock saved table high target current counter sched_id int_switch),(kenil,ks))
 ((ge,le,M),ir,(enabled,si,ci))
 (curs(sskip None),(kenil,next))((ge,caller,Mf),ir,(enabled,si,ci)).
Proof.
 intros P ks ge le caller M M0 M1 Mf ir enabled si ci running nesting lock saved table high target current counter
 sched_id int_switch br bn bs n f body next Lower Bound Saved Init NR GR Run NN GN Nest Dec Call Addr Free.
 pose proof(V293_nested_void_return_exact P ks ge le caller M1 Mf f body next bs Call Addr Free)as Return.
 unfold V293_OSIntExit_abstract_body.
 eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity | apply sseq_step ]  |  ].
 eapply V293_local_trans.
 { apply V293_csteps_local;eapply V293_success_assign_zero;eassumption. }
 eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity | apply sskip_step ]  |  ].
 eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity | apply sseq_step ]  |  ].
 eapply V293_local_trans.
 { apply V293_csteps_local;eapply V293_entry_if_select with(flag:=true).
   unfold V293_OSIntEnter_running;change Int.one with(Int.repr(Z.of_nat 1)).
   exact(V293_success_global_byte_eq ge le M0 running br 1 1 ltac:(lia)ltac:(lia) NR GR Run). }
 eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity | apply sseq_step ]  |  ].
 eapply V293_local_cons;[apply encrit_step;reflexivity | ].
 eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity | apply sskip_step ]  |  ].
 eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity | apply sseq_step ]  |  ].
 eapply V293_local_trans.
 { apply V293_csteps_local;eapply V293_OSIntExit_nested_middle_execution;eassumption. }
 eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity | apply sskip_step ]  |  ].
 eapply V293_local_cons;[apply excrit_step;reflexivity | ].
 eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity | apply sskip_step ]  |  ].
 apply V293_csteps_local;exact Return.
Qed.

(* Stable complete-call interface: no allocation/free or execution oracle. *)
Theorem V293_nested_call_exact : forall P ks ge caller M ir enabled si ci
 f running nesting lock saved table high target current counter sched_id int_switch br bn n,
 P f=Some(V293_OSIntExit_abstract_function running nesting lock saved table high target current counter sched_id int_switch) ->
 saved<>running -> saved<>nesting -> 2<=n -> n<256 ->
 get ge running=Some(br,Tint8) -> get ge nesting=Some(bn,Tint8) ->
 load Tint8 M(br,0%Z)=Some(V293_byteval 1) ->
 load Tint8 M(bn,0%Z)=Some(V293_byteval n) ->
 (exists old,get M(bn,0%Z)=Some(true,old)) ->
 V293_local_steps P(curs(scall f nil),(kenil,ks))((ge,caller,M),ir,(enabled,si,ci))
 (curs(sskip None),(kenil,ks))((ge,caller,V293_put_byte M(bn,0%Z)(Nat.pred n)),ir,(enabled,si,ci)).
Proof.
 intros P ks ge caller M ir enabled si ci f running nesting lock saved table high target current counter
 sched_id int_switch br bn n Program SR SN Lower Bound GR GN Run Nest[old Writable].
 destruct(memory_has_fresh_block M)as[bs Fresh].
 assert(BR:bs<>br)by(eapply V293_success_load_not_fresh;eassumption).
 assert(BN:bs<>bn)by(eapply V293_success_load_not_fresh;eassumption).
 destruct(V293_success_scheduler_storage M bs Fresh)as[Ms[Init[W[Free Frame]]]].
 set(le:=set(emp:env)saved(bs,Tint32)).
 set(body:=V293_OSIntExit_abstract_body running nesting lock saved table high target current counter sched_id int_switch).
 assert(Saved:get le saved=Some(bs,Tint32))by(unfold le;apply map_get_set).
 assert(NR:get le running=None).
 { unfold le;rewrite map_get_set' by exact SR;apply map_emp_get. }
 assert(NN:get le nesting=None).
 { unfold le;rewrite map_get_set' by exact SN;apply map_emp_get. }
 assert(R0:load Tint8 Ms(br,0%Z)=Some(V293_byteval 1)).
 { etransitivity;[apply V293_load_block_frame;intro i;apply Frame;congruence  |  exact Run]. }
 assert(N0:load Tint8 Ms(bn,0%Z)=Some(V293_byteval n)).
 { etransitivity;[apply V293_load_block_frame;intro i;apply Frame;congruence  |  exact Nest]. }
 assert(WN:get Ms(bn,0%Z)=Some(true,old))by(rewrite Frame by congruence;exact Writable).
 pose proof(V293_put_byte_store Ms(bn,0%Z)(Nat.pred n)old WN)as Dec.
 set(M1:=V293_put_byte Ms(bn,0%Z)(Nat.pred n)).
 assert(Addr:getaddr le=[(bs,Tint32)]).
 { unfold le;change(getaddr(EnvMod.set EnvMod.emp saved(bs,Tint32))=[(bs,Tint32)]);reflexivity. }
 assert(Free1:free Tint32 bs M1=Some(V293_put_byte M(bn,0%Z)(Nat.pred n))).
 { unfold M1;eapply V293_nested_saved_free;eassumption. }
 pose proof(V293_nested_body_exact P(kcall f body caller ks)ge le caller
 (allocb M bs 0%Z 4)Ms M1(V293_put_byte M(bn,0%Z)(Nat.pred n))ir enabled si ci
 running nesting lock saved table high target current counter sched_id int_switch br bn bs n f body ks
 Lower Bound Saved Init NR GR R0 NN GN N0 Dec eq_refl Addr Free1)as Exec.
 eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity  |  apply snpcall_step]  |  ].
   eapply V293_local_cons.
   { apply ostc_step;eapply stmt_step;[reflexivity  |  ];eapply sfexec_step with(d1:=dnil)(d2:=dcons saved Tint32 dnil).
     - reflexivity.
     - reflexivity.
     - exact Program.
     - exact I.
     - reflexivity. }
   eapply V293_local_cons.
   { apply ostc_step;eapply stmt_step;[reflexivity  |  ];eapply salloclv_step.
     - reflexivity.
     - reflexivity.
     - exists bs;split;[exact Fresh  |  ];split;[reflexivity  |  ];split.
       + intros[v V];rewrite map_emp_get in V;discriminate.
       + reflexivity. }
   eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity  |  apply sallocend_step]  |  ].
   exact Exec.
Qed.

Section BuilderNestedExit.
Variables target running nesting lock:var.
Variables bt bg br bh bp bc bk brun bn bl:block.
Variable rest:list(addr*type).
Let li:=V293_irq_bound_li running nesting lock brun bn bl.
Let Inv0:=V293_ready_dynamic_exit_inv target bt bg br bh bp bc bk brun bn bl rest.
Let snapshot:=V293_irq_bound_snapshot target running nesting lock
 bt bg br bh bp bc bk brun bn bl rest.

Lemma V293_builder_snapshot_nested_return : forall n locked aop enabled ir si ci t ge le M O,
 n<255 ->
 (ge,le,M,ir,(enabled,si,ci),O,aop)|=snapshot 1(S n)locked aop enabled ir si ci t ->
 (ge,le,V293_put_byte M(bn,0%Z)n,ir,(enabled,si,ci),O,aop)|=
 snapshot 1 n locked aop enabled ir si ci t.
Proof.
 intros n locked aop enabled ir si ci t ge le M O Bound Held.
 set(Frame:=<||aop||> ** OS[ir,enabled,si,ci] **
   (Amapsto(brun,0%Z)Tint8 true(V293_byteval 1) **
   (Amapsto(bl,0%Z)Tint8 true(V293_byteval locked) **
   (p_local li t nil ** Aemp **
    (V293_quiet_irq_kept target bt bg br bh bp bc bk rest ** A_dom_lenv nil))))).
 assert(Owned:(ge,le,M,ir,(enabled,si,ci),O,aop)|=
 Amapsto(bn,0%Z)Tint8 true(V293_byteval(S n)) ** Frame).
 { unfold Frame,li;clear -Held;unfold snapshot,V293_irq_bound_snapshot,V293_enter_bound_external in Held;sep auto. }
 destruct(V293_builder_byte_writable _ _ _ _ Owned)as[v Writable].
 destruct(V293_tick_raw_slot_update(bn,0%Z)Tint8(V293_byteval(S n))(V293_byteval n)
 Frame ge le M ir(enabled,si,ci)O aop(V293_byte_type n ltac:(lia))Owned)
 as[Mf[Store Updated]].
 assert(Same:Mf=V293_put_byte M(bn,0%Z)n).
 { pose proof(V293_put_byte_store M(bn,0%Z)n v Writable);congruence. }
 subst Mf;clear Held Owned.
 unfold V293_owned_record_cell in Updated;apply astar_mono with
 (P':=Amapsto(bn,0%Z)Tint8 true(V293_byteval n))(Q':=Frame)in Updated.
 2:{ intros s K;apply astar_l_apure_elim in K;tauto. }
 2:{ intros s K;exact K. }
 unfold snapshot,V293_irq_bound_snapshot,V293_enter_bound_external,Frame,li in *;sep auto.
Qed.

(* Stable builder interface: the two calls use the same P, exact memory,
   original abstract state and original operation. Ends before exint. *)
Theorem V293_builder_nested_prefix : forall intspec i ir si t lg pre aop st P (sd:ossched) entry exit vector
 saved table high current counter sched_id int_switch n locked,
 intspec i=Some aop ->
 Some pre=BuildintPre i intspec ir si Inv0 li t lg ->st|=pre ->
 V293_control_capture brun bn bl st=Some(getabst st,V293_control 1 n locked) ->
 1<=n ->n<255 ->
 P entry=Some(V293_OSIntEnter_function running nesting) ->
 P exit=Some(V293_OSIntExit_abstract_function running nesting lock saved table high target current counter sched_id int_switch) ->
 saved<>running ->saved<>nesting ->
 i=Z.to_nat(Int.unsigned vector) ->(0<=Int.unsigned vector<Z.of_nat INUM)%Z ->
 exists Mf,
 V293_local_steps P(curs(V293_irq_source_wrapper entry exit vector),(kenil,kstop))(gettaskst st)
 (curs(sprim exint),(kenil,kstop))
 ((getgenv st,emp,Mf),isrupd(isrupd ir i true)i false,(false,i::si,nil)) /\
 (getgenv st,emp,Mf,isrupd(isrupd ir i true)i false,(false,i::si,nil),getabst st,aop)|=
 snapshot 1 n locked aop false(isrupd(isrupd ir i true)i false)(i::si)nil t /\
 V293_control_capture brun bn bl
 (getgenv st,emp,Mf,isrupd(isrupd ir i true)i false,(false,i::si,nil),getabst st,aop)=
 Some(getabst st,V293_control 1 n locked) /\
 (forall a,a<>(bn,0%Z)->get Mf a=get(getmem st)a).
Proof.
 intros intspec i ir si t lg pre aop st P sd entry exit vector saved table high current counter sched_id int_switch
 n locked Lookup Pre Held Capture Lower Bound Enter Exit SR SN Vector Range.
 destruct(V293_builder_enter_prefix target running nesting lock bt bg br bh bp bc bk brun bn bl rest
 intspec i ir si t lg pre aop st P sd entry exit vector Lookup Pre Held Enter Vector Range)
 as[c[Me[Valid[Captured[Prefix[After[Read[Step Frame]]]]]]]].
 rewrite Capture in Captured;inversion Captured;subst c.
 assert(Nest:V293_interrupt_nest_after 1 n=S n).
 { unfold V293_interrupt_nest_after;change((if Nat.ltb n 255 then S n else n)=S n);assert(E:Nat.ltb n 255=true)by(apply Nat.ltb_lt;exact Bound);rewrite E;reflexivity. }
 change((getgenv st,emp,Me,isrupd(isrupd ir i true)i false,(false,i::si,nil),getabst st,aop)|=
 snapshot 1(V293_interrupt_nest_after 1 n)locked aop false(isrupd(isrupd ir i true)i false)(i::si)nil t)in After.
 rewrite Nest in After.
 destruct Valid as[_[_ LockBound]];change(locked<256)in LockBound.
 destruct(V293_builder_snapshot_memory target running nesting lock bt bg br bh bp bc bk brun bn bl rest
 1(S n)locked aop false(isrupd(isrupd ir i true)i false)(i::si)nil t
 (getgenv st,emp,Me,isrupd(isrupd ir i true)i false,(false,i::si,nil),getabst st,aop)
 ltac:(lia)ltac:(lia)LockBound After)as[GR[GN[GL[LR[LN[LL[W[BR BL]]]]]]]].
 pose proof(V293_nested_call_exact P(kseq(sprim exint)kstop)(getgenv st)emp Me
 (isrupd(isrupd ir i true)i false)false(i::si)nil exit running nesting lock saved table high target current counter
 sched_id int_switch brun bn(S n)Exit SR SN ltac:(lia)ltac:(lia)GR GN LR LN W)as ExitTrace.
 cbn[Nat.pred]in ExitTrace.
 pose proof(V293_builder_snapshot_nested_return n locked aop false(isrupd(isrupd ir i true)i false)
 (i::si)nil t(getgenv st)emp Me(getabst st)Bound After)as Returned.
 exists(V293_put_byte Me(bn,0%Z)n);split.
 - eapply V293_local_trans;[exact Prefix| ].
   eapply V293_local_trans;[exact ExitTrace| ].
   eapply V293_local_cons.
   { apply ostc_step;eapply stmt_step;[reflexivity|apply sskip_step]. }
   apply V293_local_refl.
 - split;[exact Returned| ];split.
   + eapply(V293_control_capture_owned brun bn bl 1 n locked
     (getgenv st,emp,V293_put_byte Me(bn,0%Z)n,isrupd(isrupd ir i true)i false,(false,i::si,nil),getabst st,aop));try lia.
     eapply V293_irq_bound_snapshot_controls;exact Returned.
   + intros a Away;rewrite V293_put_byte_other by exact Away;apply Frame;exact Away.
Qed.
End BuilderNestedExit.
