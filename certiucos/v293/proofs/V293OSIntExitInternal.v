(* Uniform function specifications for the ORIGINAL OSIntExit body.
   Callee implementations and production ISR invariants remain separate obligations. *)
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitSwitchCall.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitResourceCodec.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBuilders.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.code.V293OSIntExit.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCall.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitIndexedPort.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitResourceBridge.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition V293_exit_internal_encode run x :=
 logic_val(Vint32(Int.repr(Z.of_nat run)))::V293_exit_encode x.
Definition V293_exit_internal_index lg : option(nat*V293_exit_snapshot) :=
 match lg with
 | logic_val(Vint32 run)::rest =>
   match V293_exit_decode rest with
   | Some x => Some(Z.to_nat(Int.unsigned run),x)
   | None => None
   end
 | _ => None
 end.
Lemma V293_exit_internal_roundtrip : forall run x,
 run<256 -> V293_exit_snapshot_bounded x ->
 V293_exit_internal_index(V293_exit_internal_encode run x)=Some(run,x).
Proof.
 intros run x Bound Valid;unfold V293_exit_internal_index,V293_exit_internal_encode.
 rewrite V293_exit_codec_roundtrip by exact Valid.
 rewrite V293_sched_snapshot_roundtrip by exact Bound;reflexivity.
Qed.
Definition V293_exit_internal_valid run x : Prop :=
 run<256 /\ V293_exit_snapshot_bounded x /\
 (exists p,V293_bitmap_ready(V293_xlo x)(V293_xhi x)p) /\
 V293_bitmap_tasks(V293_xlo x)(V293_xhi x)(V293_xtasks x) /\
 V293_priority_table(V293_xentries x)(V293_xtasks x).

Section UniformInternal.
Variables unmap group rows high:var.
Variables bt bg br bh:block.
Variable li:LocalInv.
Variable tp:type.
Variables bp bo bcur bcounter bn bl:block.
Variable Out:V293_exit_snapshot -> tid -> asrt.
Variable Sw:V293_exit_snapshot -> tid -> addrval -> asrt.
Variable Hli:GoodLInvAsrt li.
Variable OG:forall x t,GoodFunAsrt(Out x t).
Variable SG:forall x t address,GoodFunAsrt(Sw x t address).
Let entryS:=V293_exit_snapshot_entry unmap group rows high bt bg br bh li tp bp bo bcur bcounter bn bl.
Let acquiredS:=V293_exit_snapshot_acquired unmap group rows high bt bg br bh li tp bp bo bcur bcounter bn bl.
Let leavingS:=V293_exit_snapshot_leaving unmap group rows high bt bg br bh li tp bp bo bcur bcounter bn bl Sw.
Let restoredS:=V293_exit_snapshot_restored Out.
Let entryF:=V293_exit_select entryS.
Let acquiredF:=V293_exit_select acquiredS.
Let leavingF:=V293_exit_select leavingS.
Let restoredF:=V293_exit_select restoredS.
Let FEG:forall lg t address,GoodFunAsrt(entryF lg t address).
Proof. apply V293_exit_select_good;apply V293_exit_snapshot_entry_good;exact Hli. Defined.
Let FAG:forall lg t address,GoodFunAsrt(acquiredF lg t address).
Proof. apply V293_exit_select_good;apply V293_exit_snapshot_acquired_good;exact Hli. Defined.
Let FLG:forall lg t address,GoodFunAsrt(leavingF lg t address).
Proof. apply V293_exit_select_good;apply V293_exit_snapshot_leaving_good;assumption. Defined.
Let FRG:forall lg t address,GoodFunAsrt(restoredF lg t address).
Proof. apply V293_exit_select_good;apply V293_exit_snapshot_restored_good;exact OG. Defined.
Let switchS:=V293_exit_snapshot_switch_pre unmap group rows high bt bg br bh li tp bp bo bcur bcounter bn bl.
Let switchF:=V293_exit_switch_select switchS.
Let switchedF:=V293_exit_switch_select Sw.
Let FSG:forall lg t,GoodFunAsrt(switchF lg t).
Proof. apply V293_exit_switch_select_good;apply V293_exit_snapshot_switch_pre_good;exact Hli. Defined.
Let FPG:forall lg t,GoodFunAsrt(switchedF lg t).
Proof. apply V293_exit_switch_select_good;exact SG. Defined.
Variables table target current counter nesting lock running:var.
Variable brun:block.
Variable extra:asrt.
Variable EG:GoodFunAsrt extra.
Let shared x t:=V293_exit_snapshot_pre unmap group rows high bt bg br bh li tp bp bo bcur bcounter bn bl x t.
Definition V293_exit_internal_external_pre run x t :=
 V293_exit_builder_external_pre table target current counter nesting lock running tp bp bo bcur bcounter bn bl brun
 (V293_xaop x)(shared x t)extra run.
Definition V293_exit_internal_external_post run x t result :=
 V293_exit_builder_external_post table target current counter nesting lock running tp bp bo bcur bcounter bn bl brun
 (V293_xaop x)(shared x t)(Out x t)extra run result.
Lemma V293_exit_internal_external_pre_good : forall run x t,
 GoodFunAsrt(V293_exit_internal_external_pre run x t).
Proof.
 intros;apply V293_exit_builder_pre_good;[unfold shared,V293_exit_snapshot_pre;
 apply V293_exit_physical_pre_good;exact Hli|exact EG].
Defined.
Lemma V293_exit_internal_external_post_good : forall run x t result,
 GoodFunAsrt(V293_exit_internal_external_post run x t result).
Proof.
 intros;apply V293_exit_builder_post_good;[unfold shared,V293_exit_snapshot_pre;
 apply V293_exit_physical_pre_good;exact Hli|apply OG|exact EG].
Defined.
Definition V293_exit_internal_pre_asrt lg t :=
 match V293_exit_internal_index lg with
 | Some(run,x) => [|V293_exit_internal_valid run x|] ** V293_exit_internal_external_pre run x t
 | None => Afalse
 end.
Definition V293_exit_internal_post_asrt lg t result :=
 match V293_exit_internal_index lg with
 | Some(run,x) => V293_exit_internal_external_post run x t result
 | None => Afalse
 end.
Definition V293_exit_internal_fpre : fpre.
Proof.
 intros vl lg t;refine(@mkfunasrt(V293_exit_internal_pre_asrt lg t)_).
 unfold V293_exit_internal_pre_asrt;destruct(V293_exit_internal_index lg)as[[run x]| ];[split;[exact I|apply V293_exit_internal_external_pre_good]|exact I].
Defined.
Definition V293_exit_internal_fpost : fpost.
Proof.
 intros vl result lg t;refine(@mkfunasrt(V293_exit_internal_post_asrt lg t result)_).
 unfold V293_exit_internal_post_asrt;destruct(V293_exit_internal_index lg)as[[run x]| ];[apply V293_exit_internal_external_post_good|exact I].
Defined.

Theorem V293_OSIntExit_internal_contract : forall P f Spec sd I saved
 sched_id enter exit int_switch vl lg tid pre post,
 table<>saved -> high<>saved -> target<>saved -> current<>saved ->
 counter<>saved -> nesting<>saved -> lock<>saved -> running<>saved ->
 GoodFrm extra ->
 (forall x t,Out x t ==> CurLINV li t) ->
 (forall x t address,Sw x t address ==> CurLINV li t) ->
 Spec sched_id=Some(V293_sched_fpre unmap group rows high bt bg br bh li Hli,
  V293_sched_fpost unmap group rows high bt bg br bh li Hli,(Tvoid,nil)) ->
 Spec enter=Some(V293_indexed_pointer_fpre entryF FEG,
  V293_indexed_pointer_fpost acquiredF FAG,(Tvoid,[Tptr Tint32])) ->
 Spec exit=Some(V293_indexed_pointer_fpre leavingF FLG,
  V293_indexed_pointer_fpost restoredF FRG,(Tvoid,[Tptr Tint32])) ->
 Spec int_switch=Some(V293_nullary_fpre switchF FSG,
  V293_nullary_fpost switchedF FPG,(Tvoid,nil)) ->
 P f=Some(V293_OSIntExit_function running nesting lock saved table high target current counter
  sched_id enter exit int_switch) ->
 Some pre=BuildPreI P f vl lg V293_exit_internal_fpre tid ->
 Some post=BuildRetI P f vl lg V293_exit_internal_fpost tid ->
 InfRules Spec sd li I post Afalse pre
 (V293_OSIntExit_body running nesting lock saved table high target current counter
  sched_id enter exit int_switch) Afalse tid.
Proof.
 intros P f Spec sd I saved sched_id enter exit int_switch vl lg tid pre post
 T H G C K N L R Frame OL SL Sched Enter Exit Switch Body Pre Post.
 unfold BuildPreI in Pre;rewrite Body in Pre.
 destruct vl as[ |v vl].
 2:{ assert(E:dl_vl_match dnil(rev(v::vl))=false).
     { destruct(rev(v::vl))eqn:Rev;[ |reflexivity].
       apply(f_equal(@rev val))in Rev;rewrite rev_involutive in Rev;discriminate. }
     unfold V293_OSIntExit_function in Pre;rewrite E in Pre;discriminate. }
 change(Some pre=Some(V293_exit_builder_cells saved ** V293_exit_internal_pre_asrt lg tid **
 V293_exit_builder_domain saved))in Pre;inversion Pre;subst pre.
 unfold BuildRetI in Post;rewrite Body in Post.
 change(Some post=Some(fun result=>V293_exit_builder_cells saved ** V293_exit_internal_post_asrt lg tid result **
 V293_exit_builder_domain saved))in Post;inversion Post;subst post.
 unfold V293_exit_internal_pre_asrt,V293_exit_internal_post_asrt.
 destruct(V293_exit_internal_index lg)as[[run x]| ]eqn:Index.
 - eapply conseq_rule with(p:=(V293_exit_builder_cells saved ** V293_exit_internal_external_pre run x tid ** V293_exit_builder_domain saved) **
   [|V293_exit_internal_valid run x|]).
   + intros s Held;clear -Held;sep auto.
   + intros s Held;exact Held.
   + apply pure_split_rule;intros[Run[Bound[Ready[Tasks Table]]]].
     destruct x as[lo hi nc nest locked c old token value entries tasks aop].
     destruct Bound as[Lo[Hi[Current[Nest Locked]]]].
     eapply V293_OSIntExit_port_lookup_builder_contract
      with(P:=P)(f:=f)(vl:=nil)(lg:=lg)(unmap:=unmap)(group:=group)(rows:=rows)
      (lo:=lo)(hi:=hi)(nc:=nc)(nest:=nest)(locked:=locked)(c:=c)(old:=old)(token:=token)(value:=value)
      (entries:=entries)(tasks:=tasks)(aop:=aop)(run:=run)(extra:=extra)(Out:=Out)(Sw:=Sw)
      (Hli:=Hli)(OG:=OG)(SG:=SG)
      (GP:=V293_exit_internal_external_pre_good run
        (V293_mk_exit_snapshot lo hi nc nest locked c old token value entries tasks aop)tid)
      (GQ:=V293_exit_internal_external_post_good run
        (V293_mk_exit_snapshot lo hi nc nest locked c old token value entries tasks aop)tid);
      try eassumption;try(intros;assumption).
     * apply OL.
     * intros bs;apply SL.
     * unfold BuildPreI;rewrite Body;reflexivity.
     * unfold BuildRetI;rewrite Body;reflexivity.
 - eapply conseq_rule with(p:=Afalse)(q:=Afalse).
   + intros s Held;apply astar_comm in Held;apply astar_assoc_elim in Held;
     apply astar_l_afalse_elim in Held;exact Held.
   + intros s Held;exact Held.
   + apply pfalse_rule.
Qed.
End UniformInternal.
