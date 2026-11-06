Require Import CertiOS.certiucos.v293.proofs.V293InterruptFunctionEnvironment.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBoundarySwitch.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.code.V293OSIntEnter.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.framework.proof.toptheorem.
Require Import Coq.Lists.List.

(* The body argument also permits a single-call-site negative control.
   The production instance below uses the accepted source-level normalization. *)
Definition V293_exit_env_unit exit enter sched running nesting unmap group rows high y saved body : progunit :=
 fun f =>if Z.eq_dec f exit then Some(Tvoid,dnil,dcons saved Tint32 dnil,body)
 else V293_irq_internal_unit enter sched running nesting unmap group rows high y f.
Definition V293_exit_env_spec exit enter sched running nesting unmap group rows high
 brun bn bt bg br bh li Hli (xp:fpre)(xq:fpost) : funspec :=
 fun f =>if Z.eq_dec f exit then Some(xp,xq,(Tvoid,nil))
 else V293_irq_internal_spec enter sched running nesting unmap group rows high brun bn bt bg br bh li Hli f.

Lemma V293_exit_env_domains : forall exit enter sched running nesting unmap group rows high y saved body
 brun bn bt bg br bh li Hli xp xq,
 EqDom(V293_exit_env_unit exit enter sched running nesting unmap group rows high y saved body)
 (V293_exit_env_spec exit enter sched running nesting unmap group rows high brun bn bt bg br bh li Hli xp xq).
Proof.
 intros. intro f. unfold V293_exit_env_unit,V293_exit_env_spec.
 destruct(Z.eq_dec f exit);[split;intros _;eexists;reflexivity|apply V293_irq_internal_domains].
Qed.

Lemma V293_exit_env_entries : forall exit enter sched running nesting unmap group rows high y saved body,
 exit<>enter ->exit<>sched ->enter<>sched ->
 let P:=V293_exit_env_unit exit enter sched running nesting unmap group rows high y saved body in
 P exit=Some(Tvoid,dnil,dcons saved Tint32 dnil,body) /\
 P enter=Some(V293_OSIntEnter_function running nesting) /\
 P sched=Some(V293_OSSchedNew_function unmap group rows high y).
Proof.
 intros exit enter sched running nesting unmap group rows high y saved body XE XS ES P.
 unfold P,V293_exit_env_unit. destruct(V293_irq_internal_entries enter sched running nesting unmap group rows high y ES).
 repeat destruct Z.eq_dec;try congruence;auto.
Qed.

(* Exact remaining obligation: this equivalence does NOT discharge the exit body.
   The other two bodies are rebuilt using the new P and the new Spec. *)
Theorem V293_exit_env_remaining_body : forall exit enter sched running nesting unmap group rows high y saved body
 brun bn bt bg br bh li Hli xp xq sd inv,
 exit<>enter ->exit<>sched ->enter<>sched ->unmap<>y ->group<>y ->rows<>y ->high<>y ->
 let P:=V293_exit_env_unit exit enter sched running nesting unmap group rows high y saved body in
 let Spec:=V293_exit_env_spec exit enter sched running nesting unmap group rows high brun bn bt bg br bh li Hli xp xq in
 WFFunEnv P Spec sd li inv <->
 (forall vl pre post lg tid, Some pre=BuildPreI P exit vl lg xp tid ->
 Some post=BuildRetI P exit vl lg xq tid ->
 InfRules Spec sd li inv post Afalse pre body Afalse tid).
Proof.
 intros exit enter sched running nesting unmap group rows high y saved body
 brun bn bt bg br bh li Hli xp xq sd inv XE XS ES UY GY RY HY P Spec.
 pose proof(V293_exit_env_entries exit enter sched running nesting unmap group rows high y saved body XE XS ES)
 as(CodeX&CodeE&CodeS).
 assert(SpecX:Spec exit=Some(xp,xq,(Tvoid,nil))).
 { unfold Spec,V293_exit_env_spec;destruct Z.eq_dec;congruence. }
 split.
 - intros[Dom Checked]. destruct(Checked exit xp xq Tvoid nil SpecX)as(d1&d2&s&Code&Types&Decls&Proof).
   change(P exit=Some(Tvoid,dnil,dcons saved Tint32 dnil,body))in CodeX.
   rewrite CodeX in Code;inversion Code;subst;exact Proof.
 - intro Remaining. split;[apply V293_exit_env_domains| ].
   intros f pre post t tl Lookup. unfold Spec,V293_exit_env_spec in Lookup.
   destruct(Z.eq_dec f exit)as[E|NE].
   + subst f;inversion Lookup;subst pre post t tl.
     exists dnil;exists(dcons saved Tint32 dnil);exists body.
     split;[exact CodeX| ]. split;[constructor| ]. split;[reflexivity|exact Remaining].
   + unfold V293_irq_internal_spec in Lookup.
     destruct(Z.eq_dec f enter)as[E|NEE].
     * subst f;inversion Lookup;subst pre post t tl.
       exists dnil;exists dnil;exists(V293_OSIntEnter_body running nesting).
       split;[exact CodeE| ]. split;[constructor| ]. split;[reflexivity| ].
       intros vl p r lg tid Pre Post. eapply V293_OSIntEnter_internal_contract;try eassumption.
     * unfold V293_OSSchedNew_internal_spec in Lookup.
       destruct(Z.eq_dec f sched)as[E|NES];[ |discriminate]. subst f;inversion Lookup;subst pre post t tl.
       exists dnil;exists(dcons y Tint8 dnil);exists(V293_OSSchedNew_body unmap group rows high y).
       split;[exact CodeS| ]. split;[constructor| ]. split;[reflexivity| ].
       intros vl p r lg tid Pre Post. eapply V293_OSSchedNew_internal_contract;try eassumption.
Qed.

(* Static direct calls only: this is not an execution or Hoare oracle. *)
Fixpoint V293_direct_calls(s:stmts):list fid :=
 match s with
 | scall f _ | scalle _ f _ =>cons f nil
 | sseq a b | sif _ a b =>app(V293_direct_calls a)(V293_direct_calls b)
 | sifthen _ a | swhile _ a =>V293_direct_calls a
 | _=>nil
 end.
Definition V293_direct_calls_defined(P:progunit):Prop :=
 forall f t d1 d2 s,P f=Some(t,d1,d2,s) ->
 forall callee,In callee(V293_direct_calls s) ->exists fd,P callee=Some fd.

Lemma V293_exit_boundary_calls : forall running nesting lock saved table high target current counter sched,
 V293_direct_calls(V293_exit_boundary_body running nesting lock saved table high target current counter sched
 (V293_interrupt_handoff high current target))=cons sched nil.
Proof. reflexivity. Qed.

Theorem V293_exit_env_calls_defined : forall exit enter sched running nesting unmap group rows high y
 lock saved table target current counter,
 exit<>enter ->exit<>sched ->enter<>sched ->
 V293_direct_calls_defined(V293_exit_env_unit exit enter sched running nesting unmap group rows high y saved
 (V293_exit_boundary_body running nesting lock saved table high target current counter sched
 (V293_interrupt_handoff high current target))).
Proof.
 intros exit enter sched running nesting unmap group rows high y lock saved table target current counter XE XS ES.
 pose proof(V293_exit_env_entries exit enter sched running nesting unmap group rows high y saved
 (V293_exit_boundary_body running nesting lock saved table high target current counter sched
 (V293_interrupt_handoff high current target)) XE XS ES)as(CX&CE&CS).
 intros f t d1 d2 s Code callee Call.
 unfold V293_exit_env_unit,V293_irq_internal_unit,pumerge,V293_OSIntEnter_unit,V293_OSSchedNew_internal_unit in Code.
 destruct(Z.eq_dec f exit), (Z.eq_dec f enter), (Z.eq_dec f sched);try discriminate;
 inversion Code;subst;cbn[V293_direct_calls] in Call;try contradiction;
 try(change(In callee(cons sched nil))in Call;destruct Call as[Eq|[]];subst callee;eexists;exact CS).
Qed.

Lemma V293_exit_env_syntax : forall exit enter sched running nesting unmap group rows high y
 lock saved table target current counter,
 good_os_pu(V293_exit_env_unit exit enter sched running nesting unmap group rows high y saved
 (V293_exit_boundary_body running nesting lock saved table high target current counter sched
 (V293_interrupt_handoff high current target))).
Proof.
 intros exit enter sched running nesting unmap group rows high y lock saved table target current counter f t d1 d2 s Code.
 unfold V293_exit_env_unit in Code. destruct(Z.eq_dec f exit).
 - inversion Code;subst;split;[reflexivity|repeat split].
 - eapply V293_irq_internal_syntax;exact Code.
Qed.
