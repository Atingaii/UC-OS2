(* Early boot has a null current pointer. Framework initst and CurLINV are
   running-task boundaries, not contracts for creating the first boot task.
   No new invariant, phase tag, port execution or kernel closure is claimed. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import Coq.Lists.List.

Theorem V293_null_current_no_CurTid : forall ge le M ir aux O op b tp t R,
 get ge OSTCBCur=Some(b,Tptr tp) ->
 load(Tptr tp)M(b,0%Z)=Some Vnull ->
 ~((ge,le,M,ir,aux,O,op) |= CurTid t ** R).
Proof.
 intros ge le M ir aux O op b tp t R Binding Null Owned.
 destruct(V293_shared_current_read _ _ _ _ _ _ _ _ _ Owned)
  as(b'&tp'&Binding'&Pointer).
 assert(b=b' /\ tp=tp')by(congruence).
 destruct H;subst. congruence.
Qed.

Theorem V293_null_current_no_CurLINV : forall ge le M ir aux O op b tp li t,
 get ge OSTCBCur=Some(b,Tptr tp) ->
 load(Tptr tp)M(b,0%Z)=Some Vnull ->
 ~((ge,le,M,ir,aux,O,op) |= CurLINV li t).
Proof.
 intros ge le M ir aux O op b tp li t Binding Null [lg Owned].
 eapply V293_null_current_no_CurTid;[exact Binding|exact Null|exact Owned].
Qed.

(* Recursion over additional ready tasks preserves the current task's load
   in the full concrete memory. The abstract current is the same task. *)
Theorem V293_initst_current_read : forall S O I li lg,
 initst S O I li lg ->
 exists ge envs M ir lst b tp t,
 S=((ge,envs,M),ir,lst) /\
 get ge OSTCBCur=Some(b,Tptr tp) /\
 load(Tptr tp)M(b,0%Z)=Some(Vptr t) /\
 get O curtid=Some(oscurt t).
Proof.
 intros S O I li lg Init.
 induction Init as
  [S O G envs M ir lst E aux I li t lg Shape Envs Lst Current Owned
  |S O G envs envs' M m M' ir lst lst' E aux I li t tc lg
   Shape Envs Lst Memory Current Different Ready Init IH].
 - assert(Local: (G,E,M,ir,aux,O,spec_done None) |= CurTid t ** Atrue).
   { pose proof(Owned(spec_done None))as H. change((G,E,M,ir,aux,O,spec_done None) |=
     INV I ** CurTid t ** init_rdy li t lg)in H. clear -H;sep auto. }
   destruct(V293_shared_current_read _ _ _ _ _ _ _ _ _ Local)
    as(b&tp&Binding&Read).
   exists G. exists envs. exists M. exists ir. exists lst. exists b. exists tp. exists t. repeat split;assumption.
 - destruct IH as(ge&es&mem&isr&ls&b&tp&ct&Equal&Binding&Read&Abstract).
   inversion Equal;subst ge es mem isr ls.
   exists G. exists envs. exists M. exists ir. exists lst. exists b. exists tp. exists ct. split;[exact Shape| ].
   split;[exact Binding| ]. split;[ | exact Abstract].
   erewrite load_mono;[exact Read|apply map_join_comm;exact Memory|exact Read].
Qed.

Theorem V293_null_current_no_initst : forall ge envs M ir lst O I li lg b tp,
 get ge OSTCBCur=Some(b,Tptr tp) ->
 load(Tptr tp)M(b,0%Z)=Some Vnull ->
 ~initst((ge,envs,M),ir,lst)O I li lg.
Proof.
 intros ge envs M ir lst O I li lg b tp Binding Null Init.
 destruct(V293_initst_current_read _ _ _ _ _ Init)
  as(ge'&envs'&M'&ir'&lst'&b'&tp'&t&Equal&Binding'&Read&Abstract).
 inversion Equal;subst ge' envs' M' ir' lst'.
 assert(b=b' /\ tp=tp')by(congruence).
 destruct H;subst. congruence.
Qed.

(* Full abstract ownership does not require a fabricated physical CurTid.
   This addresses only GoodI's no-abstract-extension obligation, not GoodI. *)
Theorem V293_fields_no_abstract_frame : forall current tasks events now R s Of OO,
 s |= V293_shared_fields current tasks events now ** R ->
 join(getabst s)Of OO -> Of=emp.
Proof.
 intros current tasks events now R s Of OO Owned Joined.
 assert(Keys:
  get(getabst s)curtid=Some(oscurt current) /\
  get(getabst s)abstcblsid=Some(abstcblist tasks) /\
  get(getabst s)absecblsid=Some(absecblist events) /\
  get(getabst s)ostmid=Some(ostm now)).
 { repeat split.
   - eapply V293_star_abst_get_l;[ |exact Owned].
     intros st H;exact(proj1(V293_shared_fields_get _ _ _ _ st H)).
   - eapply V293_star_abst_get_l;[ |exact Owned].
     intros st H;exact(proj1(proj2(V293_shared_fields_get _ _ _ _ st H))).
   - eapply V293_star_abst_get_l;[ |exact Owned].
     intros st H;exact(proj1(proj2(proj2(V293_shared_fields_get _ _ _ _ st H)))).
   - eapply V293_star_abst_get_l;[ |exact Owned].
     intros st H;exact(proj2(proj2(proj2(V293_shared_fields_get _ _ _ _ st H)))). }
 destruct Keys as[HC[HT[HE HN]]].
 apply OSAbstMod.extensionality. intro key. rewrite OSAbstMod.emp_sem.
 change(get Of key=None). destruct key;match goal with |- get Of ?key = _ => destruct(get Of key)eqn:Value end;try assumption.
 all:exfalso;eapply OSAbstMod.map_join_get_some;
  [reflexivity|exact Joined| |exact Value];eassumption.
Qed.
