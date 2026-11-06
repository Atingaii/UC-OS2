(* Small constructed heaps, not the old complete-call heap.
   Synthetic void dispatch discharges the continuation to test nonvacuity. *)
Require Import CertiOS.certiucos.v293.proofs.V293ExitCriticalPrefixTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293ExitChangedTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293InvariantPendingTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293ReturnClientTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293PendingReturnTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293ClientSkipTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293SchedCallProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCallGlobal.
Require Import CertiOS.certiucos.v293.proofs.V293HandoffProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293ExitNestingProgSim.
Require Import CertiOS.certiucos.v293.code.V293OSIntExit.
Require Import CertiOS.certiucos.v293.code.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.simulation.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.framework.proof.memory_prop.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition EPge:env:=set(set V293_witness_ge 130%Z(8%positive,Tint8))131%Z(9%positive,Tint8).
Definition EPbyte b n :=V293_encoded_memory b 0%Z true(encode_val Tint8(V293_byteval n)).
Definition EPmemory n :=merge(EPbyte 8%positive n)(merge(EPbyte 9%positive 0)V293_witness_current).
Definition EPrest :=CurTid(7%positive,Int.zero) **Atrue.
Definition EPpo:progunit:=fun _=>Some(Tvoid,dnil,dnil,sret).
Definition EPempty:progunit:=fun _=>None.
Definition EPks:=kcall 140%Z sret(emp:env)kstop.
Definition EPprefix:=sseq(sprim encrit)(V293_OSIntExit_nesting_dispatch 130%Z 131%Z sret).
Definition EPstate (M:mem) (ci:list bool):=
 (EPge,(emp:env),M,(fun _:hid=>false),(false,(nil:list hid),ci),(emp:osabst),spec_done None).

Lemma EPgood : GoodInvAsrt EPrest.
Proof.
 unfold EPrest;split;[unfold CurTid,Agvarmapsto,Aptrmapsto;cbn[GoodInvAsrt];intros;repeat split;exact I|exact I].
Qed.

Lemma EPentry : forall n,n<=1 ->EPstate(EPmemory n)nil |=V293_exit_guard_resource 8%positive 9%positive n EPrest.
Proof.
 intros n Bound;change(V293_wstate EPge(emp:env)(EPmemory n)|=V293_exit_guard_resource 8%positive 9%positive n EPrest).
 unfold V293_exit_guard_resource,EPmemory.
 eapply V293_wstate_star.
 - apply map_join_merge;apply map_disjoint;intros[b i].
   destruct(Pos.eq_dec b 8%positive)as[E|E].
   + subst b;right;left;rewrite map_merge_semp by reflexivity.
     unfold EPbyte,V293_witness_current;rewrite !V293_encoded_memory_outside by(intuition congruence);reflexivity.
   + left;unfold EPbyte;apply V293_encoded_memory_outside;left;congruence.
 - unfold V293_owned_record_cell;apply astar_l_apure_intro.
   + split;[apply V293_encoded_memory_mapsto|reflexivity].
   + apply V293_byte_type;lia.
 - eapply V293_wstate_star.
   + apply map_join_merge;apply map_disjoint;intros[b i].
     destruct(Pos.eq_dec b 9%positive)as[E|E].
     * subst b;right;left;unfold V293_witness_current;apply V293_encoded_memory_outside;left;discriminate.
     * left;unfold EPbyte;apply V293_encoded_memory_outside;left;congruence.
   + unfold V293_owned_record_cell;apply astar_l_apure_intro.
     * split;[apply V293_encoded_memory_mapsto|reflexivity].
     * apply V293_byte_type;lia.
   + assert(C:V293_wstate EPge(emp:env)V293_witness_current|=CurTid(7%positive,Int.zero)).
     { exists Tvoid;exists 6%positive.
       eapply V293_wstate_star with(m1:=emp)(m2:=V293_witness_current).
       - apply map_join_comm;apply map_join_emp.
       - exists 6%positive;split;[vm_compute;reflexivity| ];split;[reflexivity|split;reflexivity].
       - split;[apply V293_encoded_memory_mapsto|reflexivity]. }
     unfold EPrest;sep auto.
Qed.

Lemma EPinside : InOS(SKIP,(kenil,EPks))(pumerge EPpo EPempty).
Proof. unfold EPks;eapply V293_bound_call_inos;reflexivity. Qed.

Lemma EPdispatch : forall pc ip A M ci,
 EPstate M ci |=V293_exit_guard_resource 8%positive 9%positive 0 EPrest ->
 TaskSim(pc,(EPpo,EPempty,ip))(curs sret,(kenil,EPks))
 (EPge,(emp:env),M,(fun _=>false),(false,nil,ci))
 (pc,A)(SKIP,(kenil,kstop))(emp:osabst)V293_shared_li V293_shared_inv(fun _=>True)(7%positive,Int.zero).
Proof.
 intros pc ip A M ci Held.
 assert(Local:satp(EPge,(emp:env),M,(fun _=>false),(false,nil,ci))(emp:osabst)
  (CurLINV V293_shared_li(7%positive,Int.zero))).
 { eapply V293_exit_guards_local with(op:=spec_done None);[ |exact Held].
   intros s H;exact H. }
 eapply V293_changed_pure_TaskSim with(ks:=EPks)(C':=(curs(sfree nil None),(kenil,EPks)));
 [exact EPinside|reflexivity|reflexivity| | |exact Local| ].
 - intros[x E];discriminate E.
 - intros;eapply stmt_step;[reflexivity| ];eapply sret_step;[reflexivity|reflexivity|reflexivity].
 - eapply V293_changed_pure_TaskSim with(ks:=EPks)(C':=(SKIP,(kenil,kstop)));
   [exact EPinside|reflexivity|reflexivity| | |exact Local| ].
   + intros[x E];discriminate E.
   + intros;eapply stmt_step;[reflexivity| ];eapply sfreeend_step;reflexivity.
   + apply V293_return_client_coinduction;[right;right;reflexivity|exact Local|exact I].
Qed.

Theorem EPnonempty_prefix : forall pc ip A n,n<=1 ->
 EPstate(EPmemory n)nil |=V293_exit_guard_resource 8%positive 9%positive n EPrest /\
 TaskSim(pc,(EPpo,EPempty,ip))(curs EPprefix,(kenil,EPks))
 (EPge,(emp:env),EPmemory n,(fun _=>false),(false,nil,nil))
 (pc,A)(SKIP,(kenil,kstop))(emp:osabst)V293_shared_li V293_shared_inv(fun _=>True)(7%positive,Int.zero).
Proof.
 intros pc ip A n Bound;split;[apply EPentry;exact Bound| ].
 unfold EPprefix;eapply V293_exit_critical_prefix_TaskSim with(op:=spec_done None)(R:=EPrest);
 [reflexivity|exact EPinside|exact Bound|reflexivity|reflexivity|reflexivity|reflexivity|exact EPgood| |apply EPentry;exact Bound| ].
 - intros s H;exact H.
 - intros M' Held;apply EPdispatch;exact Held.
Qed.

Theorem EPencrit_frame : forall p ks ge le M ir ci,
 loststep p(curs(sprim encrit),(kenil,ks))((ge,le,M),ir,(false,nil,ci))
 (SKIP,(kenil,ks))((ge,le,M),ir,(false,nil,false::ci)).
Proof. intros;apply encrit_step;reflexivity. Qed.

(* Same initial heap and guards; only the decrement statement is removed.
   These executions stop at the dispatch cut, before synthetic sret. *)
Lemma EPif_select : forall p ks ge le M e yes no v take,
 evalval e(ge,le,M)=Some v ->istrue v=Some take ->
 cstepstar p(curs(sif e yes no),(kenil,ks))(ge,le,M)
 (curs(if take then yes else no),(kenil,ks))(ge,le,M).
Proof.
 intros p ks ge le M e yes no v take Eval Truth.
 eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply sif_step]| ].
 eapply V293_cstepstar_trans.
 { apply V293_expr_steps;apply evalval_imply_estepstar;exact Eval. }
 destruct take; eapply c_stepstarn;
 [eapply stmt_step;[reflexivity|apply svift_step;exact Truth]|apply c_stepstar0|
  eapply stmt_step;[reflexivity|apply sviff_step;exact Truth]|apply c_stepstar0].
Qed.

Lemma EPcontrol_guard : forall p ks M n,
 load Tint8 M(8%positive,0%Z)=Some(V293_byteval n) ->
 load Tint8 M(9%positive,0%Z)=Some(V293_byteval 0) ->n<=1 ->
 cstepstar p(curs(V293_OSIntExit_guards 130%Z 131%Z sret),(kenil,ks))(EPge,(emp:env),M)
 (curs(if Nat.eqb n 0 then sret else sskip None),(kenil,ks))(EPge,(emp:env),M).
Proof.
 intros p ks M n NR LR Bound;destruct n as [ | n ];[ |assert(n=0)by lia;subst n].
 - unfold V293_OSIntExit_guards;eapply V293_cstepstar_trans.
   + eapply EPif_select with(v:=Vint32 Int.one)(take:=true);
     [eapply V293_exit_zero_eval;[reflexivity|reflexivity|exact NR]|reflexivity].
   + eapply EPif_select with(v:=Vint32 Int.one)(take:=true);
     [eapply V293_exit_zero_eval;[reflexivity|reflexivity|exact LR]|reflexivity].
 - unfold V293_OSIntExit_guards;eapply EPif_select with(v:=Vint32 Int.zero)(take:=false);[ |reflexivity].
   exact(V293_success_global_byte_eq EPge(emp:env)M 130%Z 8%positive 1 0
    ltac:(lia)ltac:(lia)eq_refl eq_refl NR).
Qed.

Lemma EPreads : forall M ci n,
 EPstate M ci |=V293_exit_guard_resource 8%positive 9%positive n EPrest ->
 load Tint8 M(8%positive,0%Z)=Some(V293_byteval n) /\
 load Tint8 M(9%positive,0%Z)=Some(V293_byteval 0).
Proof.
 intros M ci n Held;split.
 - change(load Tint8(assertion.getmem(EPstate M ci))(8%positive,0%Z)=Some(V293_byteval n)).
   unfold V293_exit_guard_resource in Held;eapply V293_record_star_load_l;[ |exact Held];intros;eapply V293_owned_record_cell_load;eassumption.
 - change(load Tint8(assertion.getmem(EPstate M ci))(9%positive,0%Z)=Some(V293_byteval 0)).
   unfold V293_exit_guard_resource in Held;eapply V293_record_star_load_r;[ |exact Held];intros.
   eapply V293_record_star_load_l;[ |eassumption];intros;eapply V293_owned_record_cell_load;eassumption.
Qed.

Lemma EPdecrement_execution : forall p ks M ci n,n<=1 ->
 EPstate M ci |=V293_exit_guard_resource 8%positive 9%positive n EPrest ->
 exists Mf,
 (if Nat.eqb n 0 then Mf=M else store Tint8 M(8%positive,0%Z)(V293_byteval 0)=Some Mf) /\
 EPstate Mf ci |=V293_exit_guard_resource 8%positive 9%positive 0 EPrest /\
 cstepstar p(curs(V293_OSIntExit_decrement 130%Z),(kenil,ks))(EPge,(emp:env),M)
 (SKIP,(kenil,ks))(EPge,(emp:env),Mf).
Proof.
 intros p ks M ci n Bound Held;destruct(EPreads _ _ _ Held)as[NR LR].
 destruct(V293_exit_decrement_eval EPge(emp:env)M 130%Z 8%positive n
  ltac:(lia)eq_refl eq_refl NR)as[Positive Assignment].
 destruct n as [ | n ];[ |assert(n=0)by lia;subst n].
 - exists M;split;[reflexivity| ];split;[exact Held| ].
   unfold V293_OSIntExit_decrement;eapply V293_rekey_if_execution with(flag:=false);
   [exact Positive|discriminate|reflexivity].
 - destruct(V293_owned_record_cell_update _ _ _ (V293_byteval 0) _ _ _ _ _ _ _ _
   (V293_byte_type 0 ltac:(lia))Held)as(Mf&Store&Updated).
   exists Mf;split;[exact Store| ];split;[exact Updated| ].
   destruct(Assignment ltac:(lia))as(TL&Addr&TR&Value).
   unfold V293_OSIntExit_decrement;eapply V293_rekey_if_execution with(flag:=true);
   [exact Positive| |discriminate].
   intros _;eapply V293_assign_byte_execution;eassumption.
Qed.

Theorem EPsingle_decrement_control : forall p ks n,n<=1 ->
 exists Mf,
 (if Nat.eqb n 0 then Mf=EPmemory n else store Tint8(EPmemory n)(8%positive,0%Z)(V293_byteval 0)=Some Mf) /\
 load Tint8 Mf(8%positive,0%Z)=Some(V293_byteval 0) /\
 cstepstar p(curs(V293_OSIntExit_nesting_dispatch 130%Z 131%Z sret),(kenil,ks))(EPge,(emp:env),EPmemory n)
 (curs sret,(kenil,ks))(EPge,(emp:env),Mf) /\
 cstepstar p(curs(V293_OSIntExit_guards 130%Z 131%Z sret),(kenil,ks))(EPge,(emp:env),EPmemory n)
 (curs(if Nat.eqb n 0 then sret else sskip None),(kenil,ks))(EPge,(emp:env),EPmemory n).
Proof.
 intros p ks n Bound;pose proof(EPentry n Bound)as Held.
 destruct(EPdecrement_execution p(kseq(V293_OSIntExit_guards 130%Z 131%Z sret)ks)
  (EPmemory n)nil n Bound Held)as(Mf&Change&Updated&Decrement).
 destruct(EPreads _ _ _ Updated)as[NF LF].
 exists Mf;split;[exact Change| ];split;[exact NF| ];split.
 - unfold V293_OSIntExit_nesting_dispatch.
   eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply sseq_step]| ].
   eapply V293_cstepstar_trans;[exact Decrement| ].
   eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply sskip_step]| ].
   exact(EPcontrol_guard p ks Mf 0 NF LF ltac:(lia)).
 - destruct(EPreads _ _ _ Held)as[NR LR].
   eapply EPcontrol_guard;eassumption.
Qed.
