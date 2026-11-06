(* Physical controls of the new outer call; not a complete active-call witness. *)
Require Import CertiOS.certiucos.v293.proofs.V293ExitActiveCallProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitDispatchExecution.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitExecution.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293ExitNestingProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyFullCall.
Require Import CertiOS.certiucos.v293.code.V293OSIntExit.
Require Import CertiOS.audit.probes.V293CriticalReturnProgSimProbe.
Require Import CertiOS.audit.probes.V293ExitNestingProgSimProbe.
Require Import CertiOS.audit.probes.V293SchedCallEntryProgSimProbe.
Require Import CertiOS.audit.probes.V293ReadyCriticalGlobalProbe.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.audit.probes.V293TaskRecordInvariantProbe.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.framework.proof.join_prop.
Require Import CertiOS.framework.auxlibs.MapLib.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Local Open Scope nat_scope.

Lemma APfresh_storage : forall M bs target P ks ge saved,
 fresh M bs -> load Tint32 M(target,0%Z)=Some(Vint32 Int.zero) ->
 exists Ms,
 bs<>target /\
 store Tint32(allocb M bs 0%Z 4)(bs,0%Z)(Vint32 Int.zero)=Some Ms /\
 cstepstar P(curs(sassign(evar saved)(econst32 Int.zero)),(kenil,ks))
 (ge,V293_cpu_lenv saved bs,allocb M bs 0%Z 4)
 (SKIP,(kenil,ks))(ge,V293_cpu_lenv saved bs,Ms) /\
 load Tint32 Ms(target,0%Z)=Some(Vint32 Int.zero) /\
 free Tint32 bs Ms=Some M /\
 (forall c i,c<>bs ->get Ms(c,i)=get M(c,i)).
Proof.
 intros M bs target P ks ge saved Fresh Target.
 assert(Separate:bs<>target).
 { intro Same;subst target.
   pose proof(V293_success_fresh_none M bs Fresh 0%Z)as Empty.
   unfold load,loadm in Target;cbn[typelen loadbytes]in Target.
   change(@get addr(bool*memval)mem memMap M(bs,0%Z)=None)in Empty.
   rewrite Empty in Target;discriminate. }
 destruct(V293_success_scheduler_storage M bs Fresh)as(Ms&Init&Writable&Free&Frame).
 exists Ms;split;[exact Separate| ];split;[exact Init| ];split.
 - eapply V293_success_assign_zero;[unfold V293_cpu_lenv;apply map_get_set|exact Init].
 - split.
   + transitivity(load Tint32 M(target,0%Z));[apply V293_load_block_frame|exact Target].
     intros i;apply Frame;congruence.
   + split;assumption.
Qed.

(* The two inputs differ ONLY at the nesting byte. The active trace stops
   at dispatch; the nested trace skips dispatch and retains the rest. *)
Theorem APnesting_control : forall P ks dispatch,
 (forall b i,(b,i)<>(96%positive,0%Z) ->
  get(NPinitial 1)(b,i)=get(NPinitial 2)(b,i)) /\
 cstepstar P(curs(V293_OSIntExit_nesting_dispatch 110%Z 111%Z dispatch),(kenil,ks))
 (CGge,CGle,NPinitial 1)(curs dispatch,(kenil,ks))(CGge,CGle,CEM) /\
 cstepstar P(curs(V293_OSIntExit_nesting_dispatch 110%Z 111%Z dispatch),(kenil,ks))
 (CGge,CGle,NPinitial 2)(SKIP,(kenil,ks))(CGge,CGle,NPinitial 1).
Proof.
 intros P ks dispatch;split.
 - intros b i Ne;unfold NPinitial,V293_write_byte;repeat rewrite map_get_set' by congruence;reflexivity.
 - assert(Store:forall n,store Tint8(NPinitial n)(96%positive,0%Z)(V293_byteval(Nat.pred n))=
    Some(V293_write_byte(NPinitial n)96%positive(Nat.pred n))).
   { intro n;apply V293_write_byte_store with(old:=Byte(Byte.repr(Int.unsigned(Int.repr(Z.of_nat n))))).
     unfold NPinitial,V293_write_byte;apply map_get_set. }
   split.
   + unfold V293_OSIntExit_nesting_dispatch.
     eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply sseq_step]| ].
     eapply V293_cstepstar_trans.
     { eapply V293_exit_one_decrement_execution with(bn:=96%positive);try reflexivity.
       - unfold NPinitial;apply V293_write_byte_load;lia.
       - pose proof(Store 1)as S;change(store Tint8(NPinitial 1)(96%positive,0%Z)(V293_byteval 0)=
         Some(V293_exit_decrement_memory(NPinitial 1)96%positive 1))in S.
         rewrite NPdecrement_canonical in S;exact S. }
     eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply sskip_step]| ].
     eapply V293_exit_zero_guards_enter with(bn:=96%positive)(bl:=97%positive);try reflexivity.
     * exact(proj1(NPzero_cells 96%positive ltac:(auto))).
     * exact(proj1(NPzero_cells 97%positive ltac:(auto))).
   + eapply V293_OSIntExit_nested_middle_execution with(bn:=96%positive)(n:=2);try reflexivity;try lia.
     * unfold NPinitial;apply V293_write_byte_load;lia.
     * pose proof(Store 2)as S.
       replace(V293_write_byte(NPinitial 2)96%positive(Nat.pred 2))with(NPinitial 1)in S.
       -- exact S.
       -- unfold NPinitial,V293_write_byte;apply set_set_eq.
Qed.

Theorem APtyped_resource_family : forall n cs,n=1 \/ n=2 ->
 CGstate OwnershipWaiting(NPinitial n)cs |=
 V293_owned_record_cell((96%positive,0%Z),Tint8,V293_byteval n) ** CPother /\
 forall bs P ks ge saved,fresh(NPinitial n)bs ->exists Ms,
 bs<>98%positive /\
 store Tint32(allocb(NPinitial n)bs 0%Z 4)(bs,0%Z)(Vint32 Int.zero)=Some Ms /\
 cstepstar P(curs(sassign(evar saved)(econst32 Int.zero)),(kenil,ks))
 (ge,V293_cpu_lenv saved bs,allocb(NPinitial n)bs 0%Z 4)
 (SKIP,(kenil,ks))(ge,V293_cpu_lenv saved bs,Ms) /\
 load Tint32 Ms(98%positive,0%Z)=Some(Vint32 Int.zero) /\
 free Tint32 bs Ms=Some(NPinitial n) /\
 (forall c i,c<>bs ->get Ms(c,i)=get(NPinitial n)(c,i)).
Proof.
 intros n cs Which.
 pose proof(CPtyped_updated n cs ltac:(destruct Which;lia))as Typed.
 split;[exact Typed| ].
 intros bs P ks ge saved Fresh;apply APfresh_storage;[exact Fresh| ].
 eapply V293_record_star_load_l with(s:=CGstate OwnershipWaiting(NPinitial n)cs)
 (P:=V293_owned_record_cell((98%positive,0%Z),Tint32,Vint32 Int.zero))(Q:=Atrue).
 - intros st Held;apply V293_owned_record_cell_load;exact Held.
 - unfold CPother in Typed;sep auto.
Qed.
