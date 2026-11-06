Require Import CertiOS.certiucos.v293.code.V293OSIntEnter.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickDelayHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitDispatch.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCall.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import Coq.Lists.List.
(* Actual single-local builders for the original OSIntExit. This connects
   allocated builder assertions, not an allocator/free execution trace. *)
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBody.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitResourceBridge.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitCriticalCalls.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.code.V293OSIntExit.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBuilders.

Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitIndexedPort.

Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitResourceCodec.

(* Nullary runtime calls; logical arguments do not alter the C signature. *)
Definition V293_nullary_fpre (resource:list logicvar -> tid -> asrt)
 (good:forall lg t,GoodFunAsrt(resource lg t)) : fpre :=
 fun vl lg t => match vl with
 | nil => @mkfunasrt(resource lg t)(good lg t)
 | _ => @mkfunasrt Afalse I
 end.
Definition V293_nullary_fpost (resource:list logicvar -> tid -> asrt)
 (good:forall lg t,GoodFunAsrt(resource lg t)) : fpost :=
 fun vl result lg t => match vl with
 | nil => @mkfunasrt([|result=None|] ** resource lg t)(conj I(good lg t))
 | _ => @mkfunasrt Afalse I
 end.
Theorem V293_nullary_call : forall Spec sd li I r ri t callee frame
 (before after:list logicvar -> tid -> asrt)
 (BG:forall lg t,GoodFunAsrt(before lg t))
 (AG:forall lg t,GoodFunAsrt(after lg t)) lg,
 GoodFrm frame -> (before lg t ==> CurLINV li t) ->
 (after lg t ==> CurLINV li t) ->
 Spec callee=Some(V293_nullary_fpre before BG,V293_nullary_fpost after AG,(Tvoid,nil)) ->
 InfRules Spec sd li I r ri (before lg t ** frame)(scall callee nil)(after lg t ** frame)t.
Proof.
 intros Spec sd li I r ri t callee frame before after BG AG lg F BL AL Lookup.
 eapply conseq_rule with(q:=EX result:option val,
  getasrt(V293_nullary_fpost after AG nil result lg t) ** frame).
 - intros s H;exact H.
 - intros s[result H];cbn[V293_nullary_fpost getasrt]in H;clear -H;sep auto.
 - eapply call_rule with(pre:=V293_nullary_fpre before BG)
   (post:=V293_nullary_fpost after AG)(vl:=nil)(logicl:=lg)(tp:=Tvoid)(tl:=nil)(p:=frame).
   + exact F.
   + exact Lookup.
   + intros s H;exact H.
   + intros s H;reflexivity.
   + reflexivity.
   + exact BL.
   + intros s[result H];cbn[V293_nullary_fpost getasrt]in H.
     eapply V293_star_CurLINV_r;[exact AL|exact H].
Qed.

(* The saved address is a logical witness, NOT a runtime argument to OSIntCtxSw. *)
Definition V293_exit_switch_encode x address := logic_val(Vptr address)::V293_exit_encode x.
Definition V293_exit_switch_select
 (resource:V293_exit_snapshot -> tid -> addrval -> asrt) lg t : asrt :=
 match lg with
 | logic_val(Vptr address)::rest => V293_exit_select resource rest t address
 | _ => Afalse
 end.
Lemma V293_exit_switch_select_good : forall resource,
 (forall x t address,GoodFunAsrt(resource x t address)) ->
 forall lg t,GoodFunAsrt(V293_exit_switch_select resource lg t).
Proof.
 intros resource G lg t;unfold V293_exit_switch_select.
 destruct lg as [ | a lg ];[exact I| ].
 destruct a;try exact I;destruct v;try exact I;apply V293_exit_select_good;exact G.
Qed.
Lemma V293_exit_switch_select_encoded : forall resource x t address,
 V293_exit_snapshot_bounded x ->
 V293_exit_switch_select resource(V293_exit_switch_encode x address)t=resource x t address.
Proof.
 intros;unfold V293_exit_switch_select,V293_exit_switch_encode,V293_exit_select.
 rewrite V293_exit_codec_roundtrip by assumption;reflexivity.
Qed.

Section SwitchResources.
Variables unmap group rows high:var.
Variables bt bg br bh:block.
Variable li:LocalInv.
Variable tp:type.
Variables bp bo bcur bcounter bn bl:block.
Definition V293_exit_snapshot_switch_pre x t address :=
 V293_exit_physical_tail unmap group rows high bt bg br bh(V293_xlo x)(V293_xhi x)li t(V293_xaop x)
 tp bp bo(V293_xentries x)(V293_xtasks x)bcur bcounter bn bl(V293_xcurrent x)
 (V293_exit_depth(V293_xnest x))(V293_xlocked x)(Int.add(V293_xcounter x)Int.one) **
 PV address@Tint32|->V293_xtoken x.
Lemma V293_exit_snapshot_switch_pre_good : GoodLInvAsrt li ->
 forall x t address,GoodFunAsrt(V293_exit_snapshot_switch_pre x t address).
Proof. intros;split;[apply V293_exit_physical_tail_good;assumption|exact I]. Qed.
Lemma V293_exit_snapshot_switch_pre_local : forall x t address,
 V293_exit_snapshot_switch_pre x t address ==> CurLINV li t.
Proof. intros x t address;unfold V293_exit_snapshot_switch_pre;apply V293_star_CurLINV_l;apply V293_exit_physical_tail_local. Qed.
End SwitchResources.

Section PortLookupBuilder.
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
Variable extra:asrt.
Variable run:nat.
Variable brun:block.
Variables lo hi nc nest locked:nat.
Variables old token value:val.
Variable c:int32.
Variable aop:spec_code.
Variable entries:list val.
Variable tasks:TcbMod.map.
Variable tid:Modules.tid.
Let snapshot:=V293_mk_exit_snapshot lo hi nc nest locked c old token value entries tasks aop.
Let shared:=V293_exit_snapshot_pre unmap group rows high bt bg br bh li tp bp bo bcur bcounter bn bl snapshot tid.
Let output:=Out snapshot tid.
Let switch_post:=Sw snapshot tid.
Let B_external_pre := V293_exit_builder_external_pre table target current counter nesting lock running tp bp bo bcur bcounter bn bl brun aop shared extra run.
Let B_external_post := V293_exit_builder_external_post table target current counter nesting lock running tp bp bo bcur bcounter bn bl brun aop shared output extra run.
Let B_fpre := V293_exit_builder_fpre table target current counter nesting lock running tp bp bo bcur bcounter bn bl brun aop shared extra run.
Let B_fpost := V293_exit_builder_fpost table target current counter nesting lock running tp bp bo bcur bcounter bn bl brun aop shared output extra run.
Let B_frame := V293_exit_builder_frame table high target current counter nesting lock running tp bp bo bcur bcounter bn bl brun extra run.
Let tail := V293_exit_physical_tail unmap group rows high bt bg br bh lo hi li tid aop
 tp bp bo entries tasks bcur bcounter bn bl nc.

(* All callee obligations are lookups here; this does NOT establish their
   bodies, a complete function environment, or an execution/refinement trace. *)
Theorem V293_OSIntExit_port_lookup_builder_contract : forall P f Spec sd I saved vl lg pre post
 sched_id enter exit int_switch
 (GP:GoodFunAsrt B_external_pre)
 (GQ:forall result,GoodFunAsrt(B_external_post result)),
 table<>saved -> high<>saved -> target<>saved -> current<>saved ->
 counter<>saved -> nesting<>saved -> lock<>saved -> running<>saved ->
 run<256 -> lo<256 -> hi<256 -> (exists p,V293_bitmap_ready lo hi p) ->
 nc<256 -> nest<256 -> locked<256 -> V293_bitmap_tasks lo hi tasks ->
 V293_priority_table entries tasks -> GoodFrm extra ->
 (output ==> CurLINV li tid) ->
 (forall bs,switch_post(bs,Int.zero) ==> CurLINV li tid) ->
 (run=1 -> Spec sched_id=Some(V293_sched_fpre unmap group rows high bt bg br bh li Hli,
  V293_sched_fpost unmap group rows high bt bg br bh li Hli,(Tvoid,nil))) ->
 (run=1 -> Spec enter=Some(V293_indexed_pointer_fpre entryF FEG,
  V293_indexed_pointer_fpost acquiredF FAG,(Tvoid,[Tptr Tint32]))) ->
 (run=1 -> Spec exit=Some(V293_indexed_pointer_fpre leavingF FLG,
  V293_indexed_pointer_fpost restoredF FRG,(Tvoid,[Tptr Tint32]))) ->
 (run=1 -> V293_exit_depth nest=0 -> locked=0 ->
  V293_ready_select lo hi(V293_ready_group lo hi)<>nc ->
  Spec int_switch=Some(V293_nullary_fpre switchF FSG,
   V293_nullary_fpost switchedF FPG,(Tvoid,nil))) ->
 P f=Some(V293_OSIntExit_function running nesting lock saved table high target current counter
  sched_id enter exit int_switch) ->
 Some pre=BuildPreI P f vl lg(B_fpre GP)tid ->
 Some post=BuildRetI P f vl lg(B_fpost GQ)tid ->
 InfRules Spec sd li I post Afalse pre
  (V293_OSIntExit_body running nesting lock saved table high target current counter
    sched_id enter exit int_switch) Afalse tid.
Proof.
 intros P f Spec sd I saved vl lg pre post sched_id enter exit int_switch GP GQ
 T H G C K N L R Hrun Hlo Hhi Hr Hnc Hn Hl Hb Htable F OL SL Lookup Enter Exit Switch Body Pre Post.
 assert(Bound:V293_exit_snapshot_bounded snapshot)by(repeat split;assumption).
 eapply V293_OSIntExit_encoded_builder_contract
 with(unmap:=unmap)(group:=group)(rows:=rows)(lo:=lo)(hi:=hi)(nc:=nc)
 (bt:=bt)(bg:=bg)(br:=br)(bh:=bh)(entries:=entries)(tasks:=tasks)
 (Out:=Out)(Sw:=Sw)(OG:=OG)(SG:=SG)(extra:=extra)(run:=run)
 (P:=P)(f:=f)(vl:=vl)(lg:=lg)(GP:=GP)(GQ:=GQ)(Hli:=Hli)
 (token:=token)(old:=old)(c:=c)(nest:=nest)(locked:=locked)(value:=value);try eassumption.
 intros bs Run Depth Locked Different.
 assert(Before:switchF(V293_exit_switch_encode snapshot(bs,Int.zero))tid=
  tail(V293_exit_depth nest)locked(Int.add c Int.one) ** PV(bs,Int.zero)@Tint32|->token).
 { unfold switchF;rewrite V293_exit_switch_select_encoded by exact Bound;reflexivity. }
 assert(After:switchedF(V293_exit_switch_encode snapshot(bs,Int.zero))tid=switch_post(bs,Int.zero)).
 { unfold switchedF;rewrite V293_exit_switch_select_encoded by exact Bound;reflexivity. }
 change(InfRules Spec sd li I
 (fun result => [|result=None|] ** V293_exit_body_post run aop shared
 (V293_saved_pointer_resource aop value output) saved bs (B_frame saved)) Afalse
 ((tail(V293_exit_depth nest)locked(Int.add c Int.one) ** PV(bs,Int.zero)@Tint32|->token) **
 (Alvarenv saved Tint32(bs,0%Z) ** B_frame saved)) (scall int_switch nil)
 (switch_post(bs,Int.zero) ** (Alvarenv saved Tint32(bs,0%Z) ** B_frame saved))tid).
 rewrite <- Before,<- After.
 apply V293_nullary_call with(BG:=FSG)(AG:=FPG).
 - cbn[GoodFrm]. split;[exact Logic.I| ].
   unfold B_frame,V293_exit_builder_frame;cbn[GoodFrm].
   split;[apply V293_exit_caller_bindings_good| ].
   unfold V293_guard_cell,V293_exit_builder_domain;cbn[GoodFrm];tauto.
 - rewrite Before;apply V293_star_CurLINV_l;apply V293_exit_physical_tail_local.
 - rewrite After;apply SL.
 - apply Switch;assumption.
Qed.
End PortLookupBuilder.
