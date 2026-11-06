(* Actual pint/body/exint, with the very same builder heap at both ends.
   Explicit entry and return steps rule out a zero-step roundtrip witness. *)
Require Import CertiOS.certiucos.v293.proofs.V293InterruptBuilderNestedExit.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitCallExecution.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptBuilderEnterResources.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptBuilderEnterCall.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptControlRetention.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptQuietISRReturn.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptBindings.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptQuietBuilder.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptQuietContinuous.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyDynamic.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitInterruptGlobal.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptSourceRoundtrip.
Require Import CertiOS.certiucos.v293.proofs.V293LocalGlobalTrace.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyGlobalTrace.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.code.V293OSIntEnter.
Require Import CertiOS.certiucos.v293.code.V293OSIntExit.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.framework.proof.join_prop.
Require Import CertiOS.tactics.basetac.join_lib.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Coq.Relations.Relation_Operators Lia.
Import ListNotations.
Local Open Scope nat_scope.

Lemma V293_nested_owned_byte_get : forall b n R ge le M ir aux O op,
 (ge,le,M,ir,aux,O,op)|=Amapsto(b,0%Z)Tint8 true(V293_byteval n) **R ->
 get M(b,0%Z)=Some(true,Byte(Byte.repr(Int.unsigned(Int.repr(Z.of_nat n))))).
Proof.
 intros b n R ge le M ir aux O op Held.
 apply sat_split in Held;destruct Held as(m1&m2&o1&o2&JM&JO&[Points Empty]&Frame).
 destruct Points as(vl&Enc&Points);subst vl.
 cbn[encode_val V293_byteval inj_bytes encode_int List.map ptomvallist]in Points.
 destruct Points as(p&z&J&P&Z);unfold ptomval in P;subst p.
 eapply join_get_get_l_true;[reflexivity|exact JM| |reflexivity].
 eapply join_get_get_l_true;[reflexivity|exact J|apply map_get_sig|reflexivity].
Qed.

(* kstop is not a hidden saved interrupt continuation. *)
Lemma V293_exint_kstop_blocked : forall P ge le M ir aux C st,
 ~loststep P(curs(sprim exint),(kenil,kstop))((ge,le,M),ir,aux)C st.
Proof.
 intros P ge le M ir aux C st Step;inversion Step;subst;
 repeat match goal with Heq:(_,_) =(_,_) |- _=>injection Heq;clear Heq;intros;subst end;
 try discriminate.
 all:match goal with Hc:cstep _ _ _ _ _ |- _=>inversion Hc;subst end.
 all:repeat match goal with Heq:(_,_) =(_,_) |- _=>injection Heq;clear Heq;intros;subst end.
 all:first[match goal with He:estep _ _ _ _ _ _ |- _=>inversion He;subst;discriminate end
 |match goal with Hs:sstep _ _ _ _ _ _ _ |- _=>inversion Hs;subst;discriminate end].
Qed.

Section NestedReturn.
Variables target running nesting lock:var.
Variables bt bg br bh bp bc bk brun bn bl:block.
Variable rest:list(addr*type).
Let li:=V293_irq_bound_li running nesting lock brun bn bl.
Let Inv0:=V293_ready_dynamic_exit_inv target bt bg br bh bp bc bk brun bn bl rest.
Let snapshot:=V293_irq_bound_snapshot target running nesting lock bt bg br bh bp bc bk brun bn bl rest.

(* Both byte encodings, permissions and all off-cell bytes agree. *)
Theorem V293_builder_nested_identity : forall intspec i ir si t lg pre aop st P (sd:ossched)
 entry exit vector saved table high current counter sched_id int_switch n locked,
 intspec i=Some aop ->Some pre=BuildintPre i intspec ir si Inv0 li t lg ->st|=pre ->
 V293_control_capture brun bn bl st=Some(getabst st,V293_control 1 n locked) ->
 1<=n ->n<255 ->
 P entry=Some(V293_OSIntEnter_function running nesting) ->
 P exit=Some(V293_OSIntExit_abstract_function running nesting lock saved table high target current counter sched_id int_switch) ->
 saved<>running ->saved<>nesting ->
 i=Z.to_nat(Int.unsigned vector) ->(0<=Int.unsigned vector<Z.of_nat INUM)%Z ->
 V293_local_steps P(curs(V293_irq_source_wrapper entry exit vector),(kenil,kstop))(gettaskst st)
 (curs(sprim exint),(kenil,kstop))
 ((getgenv st,emp,getmem st),isrupd(isrupd ir i true)i false,(false,i::si,nil)) /\
 (getgenv st,emp,getmem st,isrupd(isrupd ir i true)i false,(false,i::si,nil),getabst st,aop)|=
 snapshot 1 n locked aop false(isrupd(isrupd ir i true)i false)(i::si)nil t.
Proof.
 intros intspec i ir si t lg pre aop st P sd entry exit vector saved table high current counter sched_id int_switch
 n locked Lookup Pre Held Capture Lower Bound Enter Exit SR SN Vector Range.
 pose proof Held as Open;unfold BuildintPre in Pre;rewrite Lookup in Pre;inversion Pre;subst pre.
 apply V293_irq_bound_builder_open in Open.
 destruct Open as[r[k[l Open]]];apply astar_l_apure_elim in Open;destruct Open as[[R[K L]]Original].
 assert(Cap:V293_control_capture brun bn bl st=Some(getabst st,V293_control r k l)).
 { eapply V293_control_capture_owned;try eassumption;eapply V293_irq_bound_snapshot_controls;exact Original. }
 rewrite Capture in Cap;inversion Cap;subst r k l.
 destruct(V293_builder_nested_prefix target running nesting lock bt bg br bh bp bc bk brun bn bl rest
 intspec i ir si t lg _ aop st P sd entry exit vector saved table high current counter sched_id int_switch
 n locked Lookup ltac:(unfold BuildintPre;rewrite Lookup;reflexivity) Held Capture Lower Bound Enter Exit SR SN Vector Range)
 as[Mf[Trace[After[Read Frame]]]].
 assert(Old:st|=Amapsto(bn,0%Z)Tint8 true(V293_byteval n) **Atrue).
 { clear -Original;unfold V293_irq_bound_snapshot,V293_enter_bound_external in Original;sep auto. }
 assert(New:(getgenv st,emp,Mf,isrupd(isrupd ir i true)i false,(false,i::si,nil),getabst st,aop)|=
 Amapsto(bn,0%Z)Tint8 true(V293_byteval n) **Atrue).
 { clear -After;unfold V293_irq_bound_snapshot,V293_enter_bound_external in After;sep auto. }
 assert(Same:Mf=getmem st).
 { apply HalfPermMap.extensionality;intro a;destruct(map_dec_a a(bn,0%Z))as[E|E].
   - subst a;destruct st as[[[[[[ge le]M]irq]aux]O]op];cbn[getgenv getmem getabst]in *.
     change(get Mf(bn,0%Z)=get M(bn,0%Z)).
     rewrite(V293_nested_owned_byte_get _ _ _ _ _ _ _ _ _ _ Old).
     apply V293_nested_owned_byte_get in New;exact New.
   - apply Frame;exact E. }
 subst Mf;split;assumption.
Qed.

(* BuildintRet is reconstructed at the endpoint of that actual same-heap trace. *)
Theorem V293_builder_nested_return_ready : forall intspec i ir si t lg pre ret st P (sd:ossched)
 entry exit vector saved table high current counter sched_id int_switch n locked,
 intspec i=Some(spec_done None) ->
 Some pre=BuildintPre i intspec ir si Inv0 li t lg ->Some ret=BuildintRet i intspec ir si Inv0 li t lg ->st|=pre ->
 V293_control_capture brun bn bl st=Some(getabst st,V293_control 1 n locked) ->
 1<=n ->n<255 ->
 P entry=Some(V293_OSIntEnter_function running nesting) ->
 P exit=Some(V293_OSIntExit_abstract_function running nesting lock saved table high target current counter sched_id int_switch) ->
 saved<>running ->saved<>nesting ->
 i=Z.to_nat(Int.unsigned vector) ->(0<=Int.unsigned vector<Z.of_nat INUM)%Z ->
 V293_local_steps P(curs(V293_irq_source_wrapper entry exit vector),(kenil,kstop))(gettaskst st)
 (curs(sprim exint),(kenil,kstop))
 ((getgenv st,emp,getmem st),isrupd(isrupd ir i true)i false,(false,i::si,nil)) /\
 (getgenv st,emp,getmem st,isrupd ir i false,(false,i::si,nil),getabst st,spec_done None)|=ret.
Proof.
 intros intspec i ir si t lg pre ret st P sd entry exit vector saved table high current counter sched_id int_switch
 n locked Lookup Pre Ret Held Capture Lower Bound Enter Exit SR SN Vector Range.
 destruct(V293_builder_nested_identity intspec i ir si t lg pre(spec_done None)st P sd entry exit vector
 saved table high current counter sched_id int_switch n locked Lookup Pre Held Capture Lower Bound Enter Exit SR SN Vector Range)
 as[Trace After];split;[exact Trace| ].
 destruct(V293_control_builder_capture target running nesting lock bt bg br bh bp bc bk brun bn bl rest
 intspec i ir si t lg pre(spec_done None)st Lookup Pre Held)as[c[Valid Captured]].
 rewrite Capture in Captured;inversion Captured;subst c;destruct Valid as[_[_ LockBound]].
 change(locked<256)in LockBound.
 assert(LowerISR:forall j,j<i ->ir j=false).
 { unfold BuildintPre in Pre;rewrite Lookup in Pre;inversion Pre;subst pre.
   eapply V293_irq_builder_lower_clear;exact Held. }
 rewrite V293_irq_eoi_exact in After.
 unfold BuildintRet in Ret;rewrite Lookup in Ret;inversion Ret;subst ret.
 eapply V293_bound_quiet_partial_return with(run:=1)(nest:=n)(locked:=locked);try lia;[exact LowerISR|exact After].
Qed.

(* Stable source-global interface. Mandatory concrete pint and exint steps
   surround the body; the final whole global state is literally the input. *)
Theorem V293_builder_nested_global_roundtrip : forall pc po pi ip T les aus cst t
 ge caller M ir si O interrupted ike ks intspec i lg pre ret (sd:ossched)
 entry exit vector saved table high current counter sched_id int_switch n locked,
 get T t=Some(interrupted,(ike,ks)) ->get les t=Some caller ->get aus t=Some((true,si,nil):localst) ->
 goodks(pc,(po,pi,ip))(kint interrupted ike caller ks) ->higherint ir i ->i<INUM ->
 ip i=Some(V293_irq_source_wrapper entry exit vector) ->
 intspec i=Some(spec_done None) ->
 Some pre=BuildintPre i intspec ir si Inv0 li t lg ->Some ret=BuildintRet i intspec ir si Inv0 li t lg ->
 (ge,emp,M,isrupd ir i true,(false,i::si,nil),O,spec_done None)|=pre ->
 V293_control_capture brun bn bl(ge,emp,M,isrupd ir i true,(false,i::si,nil),O,spec_done None)=
 Some(O,V293_control 1 n locked) ->1<=n ->n<255 ->
 (pumerge po pi)entry=Some(V293_OSIntEnter_function running nesting) ->
 (pumerge po pi)exit=Some(V293_OSIntExit_abstract_function running nesting lock saved table high target current counter sched_id int_switch) ->
 saved<>running ->saved<>nesting ->
 i=Z.to_nat(Int.unsigned vector) ->(0<=Int.unsigned vector<Z.of_nat INUM)%Z ->
 let entered:=(set T t(curs(V293_irq_source_wrapper entry exit vector),(kenil,kint interrupted ike caller ks)),
 (ge,set les t emp,M,isrupd ir i true,set aus t(false,i::si,nil)),t)in
 let returning:=(set T t(curs(sprim exint),(kenil,kint interrupted ike caller ks)),
 (ge,set les t emp,M,ir,set aus t(false,i::si,nil)),t)in
 (match entered with(Ti,Si,ti)=>lpstep(pc,(po,pi,ip))T cst(ge,les,M,ir,aus)t Ti cst Si ti end) /\
 V293_global_steps(pc,(po,pi,ip))cst entered returning /\
 (match returning with(Tr,Sr,tr)=>lpstep(pc,(po,pi,ip))Tr cst Sr tr T cst(ge,les,M,ir,aus)t end) /\
 (ge,emp,M,isrupd ir i false,(false,i::si,nil),O,spec_done None)|=ret.
Proof.
 intros pc po pi ip T les aus cst t ge caller M ir si O interrupted ike ks intspec i lg pre ret sd
 entry exit vector saved table high current counter sched_id int_switch n locked
 Code Env Aux Good Higher Inum Installed Lookup Pre Ret Held Capture Lower Bound Enter Exit SR SN Vector Range.
 destruct(V293_builder_nested_return_ready intspec i ir si t lg pre ret
 (ge,emp,M,isrupd ir i true,(false,i::si,nil),O,spec_done None)(pumerge po pi)sd entry exit vector
 saved table high current counter sched_id int_switch n locked Lookup Pre Ret Held Capture Lower Bound Enter Exit SR SN Vector Range)
 as[Trace Ready].
 assert(Clear:ir i=false)by(apply Higher;lia).
 rewrite V293_interrupt_eoi_restores_ir in Trace by exact Clear.
 pose proof(V293_interrupt_local_steps_global pc po pi ip _ _ _ _ Trace
 interrupted ike caller ks T les aus t cst Good)as Lifted.
 cbn zeta;split;[eapply V293_interrupt_source_enter;eassumption| ];split;[exact Lifted| ];split;[ |exact Ready].
 assert(TSame:set T t(interrupted,(ike,ks))=T)by(exact(TasksMod.get_set_same Code)).
 assert(ESame:set les t caller=les)by(exact(CltEnvMod.get_set_same Env)).
 assert(ASame:set aus t((true,si,nil):localst)=aus)by(exact(TaskLStMod.get_set_same Aux)).
 assert(Return:lpstep(pc,(po,pi,ip))
 (set T t(curs(sprim exint),(kenil,kint interrupted ike caller ks)))cst
 (ge,set les t emp,M,ir,set aus t(false,i::si,nil))t
 (set T t(interrupted,(ike,ks)))cst
 (ge,set les t caller,M,ir,set aus t((true,si,nil):localst))t).
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
End NestedReturn.
