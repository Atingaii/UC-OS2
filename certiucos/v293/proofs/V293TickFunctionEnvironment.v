(* The real tick and scheduler share one specification. The CPU hook has no
   synthesized implementation: its exact remaining body obligation is exposed. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeReadyAPI.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickSharedSnapshot.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.framework.proof.toptheorem.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLoop.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickWhileRecords.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickPostHookHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickBuilderLocals.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.certiucos.v293.proofs.V293TimeReadyShared.
Require Import CertiOS.certiucos.v293.proofs.V293TimeNamesGood.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.certiucos.v293.code.V293OSTimeTick.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope nat_scope.

Section Environment.
Variables (bindings:list(V293_tick_task*(taskstatus*val))) (idle:addrval) (message:val)
 (br bg bp bn bu bh bt bx:block) (R:asrt) (Good:GoodFunAsrt R)
 (tick sched hook:fid) (ptcb rows group saved now running head unmap high y:var)
 (li:LocalInv) (LGood:GoodLInvAsrt li) (sd:ossched).
Let inv:=V293_time_ready_inv br bg bp bn.
Let tpre:=V293_tick_shared_fpre bindings idle message br bg bp bn bu bh R Good.
Let tpost:=V293_tick_shared_fpost bindings idle br bg bp bn bu bh R Good.
Let hpre:=V293_tick_shared_hook_pre bindings idle message br bg bp bn bu bh R Good.
Let hpost:=V293_tick_shared_hook_post bindings idle message br bg bp bn bu bh R Good.
Let spre:=V293_sched_fpre unmap group rows high bt bg br bx li LGood.
Let spost:=V293_sched_fpost unmap group rows high bt bg br bx li LGood.

Definition V293_tick_scheduler_program (port:option function) : progunit :=
 fun f=>if Z.eq_dec f tick then
 Some(V293_tick_function ptcb rows group saved now running head hook)
 else if Z.eq_dec f sched then Some(V293_OSSchedNew_function unmap group rows high y)
 else if Z.eq_dec f hook then port else None.
Definition V293_tick_scheduler_spec : funspec :=
 fun f=>if Z.eq_dec f tick then Some(tpre,tpost,(Tvoid,[]))
 else if Z.eq_dec f sched then Some(spre,spost,(Tvoid,[]))
 else if Z.eq_dec f hook then Some(hpre,hpost,(Tvoid,[])) else None.

Hypotheses (TS:tick<>sched) (TH:tick<>hook) (SH:sched<>hook).

Lemma V293_tick_scheduler_entries : forall port,
 V293_tick_scheduler_program port tick=Some(V293_tick_function ptcb rows group saved now running head hook) /\
 V293_tick_scheduler_program port sched=Some(V293_OSSchedNew_function unmap group rows high y) /\
 V293_tick_scheduler_program port hook=port /\
 V293_tick_scheduler_spec hook=Some(hpre,hpost,(Tvoid,[])).
Proof.
 intros;unfold V293_tick_scheduler_program,V293_tick_scheduler_spec.
 repeat destruct Z.eq_dec;try congruence;repeat split;reflexivity.
Qed.

Theorem V293_tick_scheduler_domain : forall port,
 EqDom(V293_tick_scheduler_program port)V293_tick_scheduler_spec <->
 exists fd,port=Some fd.
Proof.
 intros port;split.
 - intros Domain. destruct(proj2(Domain hook)(ex_intro _ _ (proj2(proj2(proj2(V293_tick_scheduler_entries port))))))as[fd Code].
   rewrite(proj1(proj2(proj2(V293_tick_scheduler_entries port))))in Code.
   exists fd;exact Code.
 - intros[fd Port]f;unfold V293_tick_scheduler_program,V293_tick_scheduler_spec.
   repeat destruct Z.eq_dec;split;intros[x Code];try discriminate;try(eexists;reflexivity).
   exists fd;exact Port.
Qed.

Theorem V293_tick_scheduler_missing_hook :
 ~ EqDom(V293_tick_scheduler_program None)V293_tick_scheduler_spec /\
 ~ WFFunEnv(V293_tick_scheduler_program None)V293_tick_scheduler_spec sd li inv.
Proof.
 assert(Missing:~EqDom(V293_tick_scheduler_program None)V293_tick_scheduler_spec).
 { intro Domain;apply V293_tick_scheduler_domain in Domain;destruct Domain as[fd Bad];discriminate. }
 split;[exact Missing|intros[Domain _];contradiction].
Qed.

(* This control passes the domain check. Only the hook return type changes;
   real body checking is not claimed by a domain failure. *)
Theorem V293_tick_scheduler_wrong_hook_type : forall d1 d2 body,
 EqDom(V293_tick_scheduler_program(Some(Tint32,d1,d2,body)))V293_tick_scheduler_spec /\
 ~WFFunEnv(V293_tick_scheduler_program(Some(Tint32,d1,d2,body)))V293_tick_scheduler_spec sd li inv.
Proof.
 intros d1 d2 body;split.
 - apply V293_tick_scheduler_domain;eexists;reflexivity.
 - intros[_ Bodies].
   destruct(Bodies hook hpre hpost Tvoid []
    (proj2(proj2(proj2(V293_tick_scheduler_entries (Some(Tint32,d1,d2,body)))))))as(a&b&s&Code&_).
   rewrite(proj1(proj2(proj2(V293_tick_scheduler_entries (Some(Tint32,d1,d2,body))))))in Code;discriminate.
Qed.

Hypotheses (Different:ptcb<>saved) (NA:NoAbs li)
 (Limit:(Int.unsigned(snd idle)+50<=Int.max_unsigned)%Z)
 (Valid:Forall V293_tick_binding_valid bindings)
 (Unique:NoDup(V293_tick_record_keys bindings idle))
 (Env:forall bc st,st |= V293_tick_builder_caller ptcb saved bc ** R ->
  V293_tick_post_env ptcb rows group now running head bc br bg bn bu bh(getgenv st)(getlenv st))
 (Local:forall owner,(CurTid owner ** R) ==> CurLINV li owner)
 (Frame:GoodFrm R) (Change:can_change_aop R)
 (UY:unmap<>y) (GY:group<>y) (RY:rows<>y) (HY:high<>y).

(* A hook residual is evaluated in the SAME complete map and specification,
   including real builders and declaration checks. No body proof is hidden. *)
Definition V293_tick_hook_remaining (port:option function) : Prop :=
 exists d1 d2 body,
 port=Some(Tvoid,d1,d2,body) /\ tlmatch nil d1 /\
 good_decllist(revlcons d1 d2)=true /\
 forall vl pre post lg tid,
 Some pre=BuildPreI(V293_tick_scheduler_program port)hook vl lg hpre tid ->
 Some post=BuildRetI(V293_tick_scheduler_program port)hook vl lg hpost tid ->
 InfRules V293_tick_scheduler_spec sd li inv post Afalse pre body Afalse tid.

Theorem V293_tick_scheduler_known_bodies : forall port f pre post tp tl,
 V293_tick_scheduler_spec f=Some(pre,post,(tp,tl)) -> f<>hook ->
 exists d1 d2 body,
 V293_tick_scheduler_program port f=Some(tp,d1,d2,body) /\ tlmatch tl d1 /\
 good_decllist(revlcons d1 d2)=true /\
 forall vl p r lg tid,
 Some p=BuildPreI(V293_tick_scheduler_program port)f vl lg pre tid ->
 Some r=BuildRetI(V293_tick_scheduler_program port)f vl lg post tid ->
 InfRules V293_tick_scheduler_spec sd li inv r Afalse p body Afalse tid.
Proof.
 intros port f pre post tp tl Lookup NotHook.
 unfold V293_tick_scheduler_spec in Lookup.
 destruct(Z.eq_dec f tick)as[Tick|NotTick].
 - subst f;inversion Lookup;subst pre post tp tl.
   exists dnil. exists (dcons ptcb(Tptr V293_tcb_type)(dcons saved Tint32 dnil)). exists
    (sseq(V293_tick_body ptcb rows group saved now running head hook)sret).
   split;[exact(proj1(V293_tick_scheduler_entries port))| ].
   split;[constructor| ]. split.
   + cbn[revlcons good_decllist in_decllist].
     assert(E:Zeq_bool ptcb saved=false).
     { destruct(Zeq_bool ptcb saved)eqn:E;[apply Zeq_bool_eq in E;contradiction|reflexivity]. }
     rewrite E;reflexivity.
   + intros vl p r lg tid Pre Post.
     eapply V293_tick_shared_internal_contract with(Good:=Good);try eassumption.
     * exact(proj2(proj2(proj2(V293_tick_scheduler_entries port)))).
     * exact(proj1(V293_tick_scheduler_entries port)).
 - destruct(Z.eq_dec f sched)as[Sched|NotSched].
   + subst f;inversion Lookup;subst pre post tp tl.
     exists dnil. exists (dcons y Tint8 dnil). exists (V293_OSSchedNew_body unmap group rows high y).
     split;[exact(proj1(proj2(V293_tick_scheduler_entries port)))| ].
     split;[constructor| ]. split;[reflexivity| ].
     intros vl p r lg tid Pre Post.
     eapply V293_OSSchedNew_internal_contract;try eassumption.
     exact(proj1(proj2(V293_tick_scheduler_entries port))).
   + destruct(Z.eq_dec f hook);[contradiction|discriminate].
Qed.

(* Stable interface: adding tick discharges its actual body, while a genuine
   hook body proof is both necessary and sufficient for this partial map. *)
Theorem V293_tick_scheduler_environment : forall port,
 WFFunEnv(V293_tick_scheduler_program port)V293_tick_scheduler_spec sd li inv <->
 V293_tick_hook_remaining port.
Proof.
 intro port;split.
 - intros[Domain Bodies].
   destruct(Bodies hook hpre hpost Tvoid []
    (proj2(proj2(proj2(V293_tick_scheduler_entries port)))))as(d1&d2&body&Code&Types&Decls&Checked).
   exists d1. exists d2. exists body;rewrite(proj1(proj2(proj2(V293_tick_scheduler_entries port))))in Code.
   auto.
 - intros(d1&d2&body&Port&Types&Decls&Checked);split.
   + apply V293_tick_scheduler_domain;exists(Tvoid,d1,d2,body);exact Port.
   + intros f pre post tp tl Lookup.
     destruct(Z.eq_dec f hook)as[Hook|Other].
     * subst f;rewrite(proj2(proj2(proj2(V293_tick_scheduler_entries port))))in Lookup.
       inversion Lookup;subst pre post tp tl.
       exists d1. exists d2. exists body;repeat split;try assumption.
       rewrite(proj1(proj2(proj2(V293_tick_scheduler_entries port))));exact Port.
     * eapply V293_tick_scheduler_known_bodies;eassumption.
Qed.
End Environment.
