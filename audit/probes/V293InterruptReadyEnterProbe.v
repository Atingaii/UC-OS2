Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.tactics.basetac.join_lib.
Require Import CertiOS.tactics.basetac.join_general.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyEnter.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyBoundary.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyStorageInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.code.V293OSIntEnter.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.audit.probes.V293InterruptReadyBoundaryProbe.
Require Import CertiOS.audit.probes.V293ReadyStorageInvariantProbe.
Require Import CertiOS.audit.probes.V293ReadyCriticalGlobalProbe.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.
Definition ENprefix:list(addr*type):=
 [((91%positive,0%Z),Tint8);((94%positive,0%Z),Tint8);((95%positive,0%Z),Tint32)].
Definition ENboundary:=V293_enter_ready_boundary 80%positive 81%positive 82%positive
 96%positive 97%positive 110%Z 111%Z 106%Z V293_tcb_type ENprefix nil
 (spec_done None)[0]nil OwnershipWaiting.
Definition ENkept:=V293_enter_ready_kept 80%positive 81%positive 82%positive
 96%positive 97%positive 110%Z 111%Z 106%Z V293_tcb_type ENprefix nil
 [0]nil OwnershipWaiting.
Definition ENopen:=V293_enter_ready_open 80%positive 81%positive 82%positive
 96%positive 97%positive 110%Z 111%Z 106%Z V293_tcb_type ENprefix nil
 (spec_done None)[0]nil OwnershipWaiting.
Definition ENpre:=V293_enter_ready_fpre 80%positive 81%positive 82%positive
 96%positive 97%positive 110%Z 111%Z 106%Z V293_tcb_type ENprefix nil.
Definition ENpost:=V293_enter_ready_fpost 80%positive 81%positive 82%positive
 96%positive 97%positive 110%Z 111%Z 106%Z V293_tcb_type ENprefix nil.
Definition ENstate M O:=IQstate M(fun _:hid=>false)0 O.
Lemma ENnonempty : exists M O,ENstate M O |= ENboundary ** A_dom_lenv nil.
Proof.
 destruct(IQreturn_nonempty 0)as(M&O&Held);exists M;exists O.
 assert(G:(CGge,emp,empmem,(fun _:hid=>false),(false,[0],nil),empabst,spec_done None)|=
 V293_interrupt_globals 110%Z 111%Z 96%positive 97%positive).
 { unfold V293_interrupt_globals;split;apply agvarenv_intro;
   [split;reflexivity|split;reflexivity|split;reflexivity|split;reflexivity]. }
 assert(Pack:ENstate M O |= V293_interrupt_globals 110%Z 111%Z 96%positive 97%positive **
 V293_irq_ready_closed 80%positive 81%positive 82%positive 106%Z V293_tcb_type PPcells
 0 nil(spec_done None)OwnershipWaiting nil).
 { unfold ENstate,IQstate;apply sat_split';exists empmem;exists M;exists empabst;exists O.
   split;[apply join_emp| ];split;[apply join_emp| ];split;assumption. }
 apply astar_comm in Pack;apply V293_irq_ready_enter_boundary with(prefix:=ENprefix)(suffix:=nil)in Pack;exact Pack.
Qed.
Lemma ENwrite_run : forall run nest n M O,
 run<256 ->n<256 ->ENstate M O |= ENopen run nest ->
 ENstate(V293_put_byte M(96%positive,0%Z)n)O |= ENopen n nest.
Proof.
 intros run nest n M O Br Bn H.
 unfold ENopen,V293_enter_ready_open,V293_interrupt_cells in H;
 cbn[V293_rdy_raw_cells]in H.
 assert(Pack:ENstate M O |=
 V293_owned_record_cell((96%positive,0%Z),Tint8,V293_byteval run) **
 (<||spec_done None||> ** (Amapsto(97%positive,0%Z)Tint8 true(V293_byteval nest) ** ENkept))).
 { assert(T:rule_type_val_match Tint8(V293_byteval run)=true)by(apply V293_byte_type;exact Br).
   unfold V293_owned_record_cell;sep auto. }
 unfold ENstate,IQstate in Pack.
 destruct(V293_owned_byte_update _ _ n _ _ _ _ _ _ _ _ Bn Pack)as[_ Updated].
 unfold ENstate,IQstate,ENopen,V293_enter_ready_open,V293_interrupt_cells;
 cbn[V293_rdy_raw_cells];unfold V293_owned_record_cell in Updated;sep auto.
Qed.
Lemma ENwrite_nest : forall run nest n M O,
 nest<256 ->n<256 ->ENstate M O |= ENopen run nest ->
 ENstate(V293_put_byte M(97%positive,0%Z)n)O |= ENopen run n.
Proof.
 intros run nest n M O Br Bn H.
 unfold ENopen,V293_enter_ready_open,V293_interrupt_cells in H;
 cbn[V293_rdy_raw_cells]in H.
 assert(Pack:ENstate M O |=
 V293_owned_record_cell((97%positive,0%Z),Tint8,V293_byteval nest) **
 (<||spec_done None||> ** (Amapsto(96%positive,0%Z)Tint8 true(V293_byteval run) ** ENkept))).
 { assert(T:rule_type_val_match Tint8(V293_byteval nest)=true)by(apply V293_byte_type;exact Br).
   unfold V293_owned_record_cell;sep auto. }
 unfold ENstate,IQstate in Pack.
 destruct(V293_owned_byte_update _ _ n _ _ _ _ _ _ _ _ Bn Pack)as[_ Updated].
 unfold ENstate,IQstate,ENopen,V293_enter_ready_open,V293_interrupt_cells;
 cbn[V293_rdy_raw_cells];unfold V293_owned_record_cell in Updated;sep auto.
Qed.
Theorem ENzero_nonempty : exists M O,ENstate M O |=ENopen 0 0.
Proof.
 destruct ENnonempty as(M&O&Held).
 apply V293_enter_ready_extract in Held;destruct Held as(run&nest&Held).
 apply astar_l_apure_elim in Held;destruct Held as[[Br Bn]Held].
 pose proof(ENwrite_run run nest 0 M O Br ltac:(lia) Held)as First.
 exists(V293_put_byte(V293_put_byte M(96%positive,0%Z)0)(97%positive,0%Z)0);exists O.
 apply ENwrite_nest with(nest:=nest);[exact Bn|lia|exact First].
Qed.
Theorem ENbuilders_nonempty : exists pre post M O,
 Some pre=BuildPreI(V293_OSIntEnter_unit 500%Z 110%Z 111%Z)500%Z nil
 (V293_enter_ready_call_lg(spec_done None)[0]nil)ENpre OwnershipWaiting /\
 Some post=BuildRetI(V293_OSIntEnter_unit 500%Z 110%Z 111%Z)500%Z nil
 (V293_enter_ready_call_lg(spec_done None)[0]nil)ENpost OwnershipWaiting /\
 ENstate M O |=pre.
Proof.
 destruct ENnonempty as(M&O&Held).
 eexists;eexists;exists M;exists O;split;[reflexivity| ];split;[reflexivity| ].
 change(ENstate M O |=Aemp ** (ENboundary ** A_dom_lenv nil));sep auto.
Qed.
Lemma ENrunning_eval : forall run nest M O,
 run<256 ->nest<256 ->ENstate M O |=ENopen run nest ->
 evalval(V293_OSIntEnter_running 110%Z)(getsmem(ENstate M O))=
 Some(Vint32(if Nat.eqb run 1 then Int.one else Int.zero)).
Proof.
 intros run nest M O Br Bn Held.
 unfold ENopen,V293_enter_ready_open in Held.
 apply astar_l_aop'_elim in Held;destruct Held as[_ Held].
 assert(Env:forall st,st |= ENkept ->V293_interrupt_env 110%Z 111%Z 96%positive 97%positive(getgenv st)(getlenv st)).
 { intros st H;eapply V293_enter_ready_env;exact H. }
 exact(proj1(proj1(V293_interrupt_owned_eval 110%Z 111%Z 96%positive 97%positive
 run nest ENkept(ENstate M O)Br Bn Env Held))).
Qed.
(* These are two admissible physical entries and real guard evaluations,
   not two complete executions or a boot-reachability argument. *)
Theorem ENsingle_running_control : exists M O,
 ENstate M O |=ENopen 0 0 /\
 ENstate(V293_put_byte M(96%positive,0%Z)1)O |=ENopen 1 0 /\
 ENstate M O |=ENboundary ** A_dom_lenv nil /\
 ENstate(V293_put_byte M(96%positive,0%Z)1)O |=ENboundary ** A_dom_lenv nil /\
 evalval(V293_OSIntEnter_running 110%Z)(getsmem(ENstate M O))=Some(Vint32 Int.zero) /\
 evalval(V293_OSIntEnter_running 110%Z)
 (getsmem(ENstate(V293_put_byte M(96%positive,0%Z)1)O))=Some(Vint32 Int.one) /\
 (forall a,a<>(96%positive,0%Z) ->get(V293_put_byte M(96%positive,0%Z)1)a=get M a) /\
 V293_interrupt_nest_after 0 0=0 /\ V293_interrupt_nest_after 1 0=1 /\
 V293_interrupt_nest_after 1 255=255.
Proof.
 destruct ENzero_nonempty as(M&O&Zero);exists M;exists O.
 pose proof(ENwrite_run 0 0 1 M O ltac:(lia)ltac:(lia)Zero)as One.
 split;[exact Zero| ];split;[exact One| ];split.
 - apply V293_enter_ready_close with(run:=0)(nest:=0);[lia|lia|exact Zero].
 - split.
   + apply V293_enter_ready_close with(run:=1)(nest:=0);[lia|lia|exact One].
   + split;[exact(ENrunning_eval 0 0 M O ltac:(lia)ltac:(lia)Zero)| ].
     split;[exact(ENrunning_eval 1 0 _ O ltac:(lia)ltac:(lia)One)| ].
     split;[intros[b i]Apart;apply V293_put_byte_other;exact Apart| ].
     repeat split;reflexivity.
Qed.
Theorem ENactual_call : forall Spec sd r ri,
 Spec 500%Z=Some(ENpre,ENpost,(Tvoid,nil)) ->
 InfRules Spec sd V293_shared_li PPinv r ri
 (ENboundary ** A_dom_lenv nil)(scall 500%Z nil)
 (ENboundary ** A_dom_lenv nil)OwnershipWaiting.
Proof. intros;unfold ENboundary,PPinv;apply V293_OSIntEnter_ready_call with(prefix:=ENprefix)(suffix:=nil);exact H. Qed.
