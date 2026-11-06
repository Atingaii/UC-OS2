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

(* A single funspec is indexed by logical arguments and the calling task.
   This removes the fixed-owner/empty-lg restriction; it does not implement
   a port or choose a production encoding for the resource family. *)
Definition V293_indexed_pointer_fpre
 (resource:list logicvar -> tid -> addrval -> asrt)
 (good:forall lg t address,GoodFunAsrt(resource lg t address)) : fpre :=
 fun vl lg t => match vl with
 | [Vptr address] => @mkfunasrt (resource lg t address)(good lg t address)
 | _ => @mkfunasrt Afalse I
 end.
Definition V293_indexed_pointer_fpost
 (resource:list logicvar -> tid -> addrval -> asrt)
 (good:forall lg t address,GoodFunAsrt(resource lg t address)) : fpost :=
 fun vl result lg t => match vl with
 | [Vptr address] => @mkfunasrt
     ([|result=None|] ** resource lg t address)(conj I(good lg t address))
 | _ => @mkfunasrt Afalse I
 end.

Theorem V293_indexed_pointer_call : forall Spec sd li I r ri tid callee saved bs frame
 (before after:list logicvar -> Modules.tid -> addrval -> asrt)
 (BG:forall lg t address,GoodFunAsrt(before lg t address))
 (AG:forall lg t address,GoodFunAsrt(after lg t address)) lg,
 GoodFrm frame ->
 (before lg tid(bs,Int.zero) ==> CurLINV li tid) ->
 (after lg tid(bs,Int.zero) ==> CurLINV li tid) ->
 Spec callee=Some(V293_indexed_pointer_fpre before BG,
  V293_indexed_pointer_fpost after AG,(Tvoid,[Tptr Tint32])) ->
 InfRules Spec sd li I r ri
 (before lg tid(bs,Int.zero) ** (Alvarenv saved Tint32(bs,0%Z) ** frame))
 (scall callee [eaddrof(evar saved)])
 (after lg tid(bs,Int.zero) ** (Alvarenv saved Tint32(bs,0%Z) ** frame))tid.
Proof.
 intros Spec sd li I r ri tid callee saved bs frame before after BG AG lg Frame BL AL Lookup.
 eapply conseq_rule with(q:=EX result:option val,
   getasrt(V293_indexed_pointer_fpost after AG [Vptr(bs,Int.zero)]result lg tid) **
   (Alvarenv saved Tint32(bs,0%Z) ** frame)).
 - intros s H;exact H.
 - intros s[result H];cbn[V293_indexed_pointer_fpost getasrt]in H;clear -H;sep auto.
 - eapply call_rule with(pre:=V293_indexed_pointer_fpre before BG)
   (post:=V293_indexed_pointer_fpost after AG)(vl:=[Vptr(bs,Int.zero)])
   (logicl:=lg)(tp:=Tvoid)(tl:=[Tptr Tint32])
   (p:=Alvarenv saved Tint32(bs,0%Z) ** frame).
   + cbn[GoodFrm];tauto.
   + exact Lookup.
   + intros s H;exact H.
   + intros s H. eapply V293_saved_pointer_argument. clear -H;sep auto.
   + reflexivity.
   + exact BL.
   + intros s[result H];cbn[V293_indexed_pointer_fpost getasrt]in H.
     eapply V293_star_CurLINV_r;[exact AL|exact H].
Qed.

Section IndexedPort.
Variables entryF acquiredF leavingF restoredF : list logicvar -> tid -> addrval -> asrt.
Variables (FEG:forall lg t address,GoodFunAsrt(entryF lg t address))
 (FAG:forall lg t address,GoodFunAsrt(acquiredF lg t address))
 (FLG:forall lg t address,GoodFunAsrt(leavingF lg t address))
 (FRG:forall lg t address,GoodFunAsrt(restoredF lg t address)).
Variables enter_lg exit_lg : list logicvar.
Section OriginalBody.
Variables unmap group rows high : var.
Variables bt bg br bh : block.
Variables lo hi : nat.
Variable li : LocalInv.
Variable tid : Modules.tid.
Variable aop : spec_code.
Variables table target : var.
Variable tp : type.
Variables bp bo : block.
Variable entries : list val.
Variable tasks : TcbMod.map.
Variables current counter nesting lock : var.
Variables bcur bcounter bn bl : block.
Variable nc : nat.
Let bindings := V293_exit_caller_bindings high table target tp bp bo
 current counter nesting lock bcur bcounter bn bl.
Let acquired := V293_exit_acquired unmap group rows high bt bg br bh lo hi li tid aop
 tp bp bo entries tasks bcur bcounter bn bl nc.
Let leaving := V293_exit_leaving unmap group rows high bt bg br bh lo hi li tid aop
 tp bp bo entries tasks bcur bcounter bn bl nc.
Let tail := V293_exit_physical_tail unmap group rows high bt bg br bh lo hi li tid aop
 tp bp bo entries tasks bcur bcounter bn bl nc.

Theorem V293_OSIntExit_indexed_bridge : forall Spec sd I r ri sched_id int_switch enter exit saved bs extra
 token old c nest locked switch_post entry restored (Hli:GoodLInvAsrt li),
 lo<256 -> hi<256 -> (exists p,V293_bitmap_ready lo hi p) -> nc<256 -> nest<256 -> locked<256 ->
 V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks -> GoodFrm extra ->
 (entry(bs,Int.zero) ==> CurLINV li tid) ->
 (restored(bs,Int.zero) ==> CurLINV li tid) ->
 (switch_post(bs,Int.zero) ==> CurLINV li tid) ->
 Spec sched_id=Some(V293_sched_fpre unmap group rows high bt bg br bh li Hli,
  V293_sched_fpost unmap group rows high bt bg br bh li Hli,(Tvoid,nil)) ->
 Spec enter=Some(V293_indexed_pointer_fpre entryF FEG,
  V293_indexed_pointer_fpost acquiredF FAG,(Tvoid,[Tptr Tint32])) ->
 Spec exit=Some(V293_indexed_pointer_fpre leavingF FLG,
  V293_indexed_pointer_fpost restoredF FRG,(Tvoid,[Tptr Tint32])) ->
 entryF enter_lg tid=entry ->
 acquiredF enter_lg tid=acquired nest locked old c token ->
 leavingF exit_lg tid=leaving nest locked old c token switch_post ->
 restoredF exit_lg tid=restored ->
 (V293_exit_depth nest=0 -> locked=0 -> V293_ready_select lo hi(V293_ready_group lo hi)<>nc ->
  InfRules Spec sd li I r ri
   ((tail(V293_exit_depth nest)locked(Int.add c Int.one) **
     PV(bs,Int.zero)@Tint32|->token) **
    (Alvarenv saved Tint32(bs,0%Z) ** (bindings ** extra)))
   (scall int_switch nil)
   (switch_post(bs,Int.zero) ** (Alvarenv saved Tint32(bs,0%Z) ** (bindings ** extra)))tid) ->
 InfRules Spec sd li I r ri
 (entry(bs,Int.zero) ** (Alvarenv saved Tint32(bs,0%Z) ** (bindings ** extra)))
 (sseq(scall enter ((eaddrof(evar saved))::nil))
   (sseq(V293_OSIntExit_nesting_dispatch nesting lock
     (V293_OSIntExit_dispatch table high target current counter sched_id int_switch))
     (scall exit ((eaddrof(evar saved))::nil))))
 (restored(bs,Int.zero) ** (Alvarenv saved Tint32(bs,0%Z) ** (bindings ** extra)))tid.
Proof.
 intros Spec sd I r ri sched_id int_switch enter exit saved bs extra token old c nest locked
 switch_post entry restored Hli Hlo Hhi Hr Hnc Hn Hl Hb Htable F EL RL SL Lookup Enter Exit MatchEntry MatchAcquired MatchLeaving MatchRestored Call.
 eapply seq_rule with(p':=acquired nest locked old c token(bs,Int.zero) **
  (Alvarenv saved Tint32(bs,0%Z) ** (bindings ** extra))).
 - rewrite <- MatchEntry, <- MatchAcquired. eapply V293_indexed_pointer_call with(BG:=FEG)(AG:=FAG)(lg:=enter_lg).
   + cbn[GoodFrm];split;[apply V293_exit_caller_bindings_good|exact F].
   + rewrite MatchEntry;exact EL.
   + rewrite MatchAcquired;apply V293_exit_acquired_local.
   + exact Enter.
 - eapply seq_rule with(p':=leaving nest locked old c token switch_post(bs,Int.zero) **
    (Alvarenv saved Tint32(bs,0%Z) ** (bindings ** extra))).
   + unfold acquired,leaving,bindings.
     apply V293_OSIntExit_middle_bridge with(Hli:=Hli);assumption.
   + rewrite <- MatchLeaving, <- MatchRestored. eapply V293_indexed_pointer_call with(BG:=FLG)(AG:=FRG)(lg:=exit_lg).
     * cbn[GoodFrm];split;[apply V293_exit_caller_bindings_good|exact F].
     * rewrite MatchLeaving;apply V293_exit_leaving_local;exact SL.
     * rewrite MatchRestored;exact RL.
     * exact Exit.
Qed.

Theorem V293_OSIntExit_indexed_body : forall Spec sd I saved bs oldsave running brun run extra
 sched_id enter exit int_switch token old c nest locked shared switch_post restored
 (Hli:GoodLInvAsrt li),
 run<256 -> lo<256 -> hi<256 -> (exists p,V293_bitmap_ready lo hi p) ->
 nc<256 -> nest<256 -> locked<256 -> V293_bitmap_tasks lo hi tasks ->
 V293_priority_table entries tasks -> GoodFrm extra ->
 (shared ==> CurLINV li tid) ->
 (restored(bs,Int.zero) ==> CurLINV li tid) ->
 (switch_post(bs,Int.zero) ==> CurLINV li tid) ->
 (run=1 -> Spec sched_id=Some(V293_sched_fpre unmap group rows high bt bg br bh li Hli,
  V293_sched_fpost unmap group rows high bt bg br bh li Hli,(Tvoid,nil))) ->
 (run=1 -> Spec enter=Some(V293_indexed_pointer_fpre entryF FEG,
  V293_indexed_pointer_fpost acquiredF FAG,(Tvoid,[Tptr Tint32]))) ->
 (run=1 -> Spec exit=Some(V293_indexed_pointer_fpre leavingF FLG,
  V293_indexed_pointer_fpost restoredF FRG,(Tvoid,[Tptr Tint32]))) ->
 (run=1 -> entryF enter_lg tid=V293_saved_pointer_resource aop(Vint32 Int.zero)shared) ->
 (run=1 -> acquiredF enter_lg tid=acquired nest locked old c token) ->
 (run=1 -> leavingF exit_lg tid=leaving nest locked old c token switch_post) ->
 (run=1 -> restoredF exit_lg tid=restored) ->
 (run=1 -> V293_exit_depth nest=0 -> locked=0 ->
  V293_ready_select lo hi(V293_ready_group lo hi)<>nc ->
  InfRules Spec sd li I
   (fun result => [|result=None|] ** V293_exit_body_post run aop shared restored saved bs
     (bindings ** (V293_guard_cell running brun run ** extra))) Afalse
   ((tail(V293_exit_depth nest)locked(Int.add c Int.one) ** PV(bs,Int.zero)@Tint32|->token) **
    (Alvarenv saved Tint32(bs,0%Z) ** (bindings ** (V293_guard_cell running brun run ** extra))))
   (scall int_switch nil)
   (switch_post(bs,Int.zero) **
    (Alvarenv saved Tint32(bs,0%Z) ** (bindings ** (V293_guard_cell running brun run ** extra))))tid) ->
 InfRules Spec sd li I
  (fun result => [|result=None|] ** V293_exit_body_post run aop shared restored saved bs
    (bindings ** (V293_guard_cell running brun run ** extra))) Afalse
  (V293_exit_body_pre aop shared saved bs oldsave
    (bindings ** (V293_guard_cell running brun run ** extra)))
  (V293_OSIntExit_body running nesting lock saved table high target current counter
    sched_id enter exit int_switch) Afalse tid.
Proof.
 intros Spec sd I saved bs oldsave running brun run extra sched_id enter exit int_switch
 token old c nest locked shared switch_post restored Hli
 Hrun Hlo Hhi Hr Hnc Hn Hl Hb Htable F Local RL SL Lookup Enter Exit MatchEntry MatchAcquired MatchLeaving MatchRestored Call.
 unfold V293_OSIntExit_body. eapply seq_rule with
 (p':=V293_exit_body_at aop shared saved bs(bindings ** (V293_guard_cell running brun run ** extra))).
 - unfold V293_exit_body_pre,V293_exit_body_at.
   apply V293_OSIntExit_saved_initialize;exact Local.
 - eapply seq_rule with
   (p':=V293_exit_body_post run aop shared restored saved bs
     (bindings ** (V293_guard_cell running brun run ** extra))).
   + eapply V293_tick_known_ift_hoare with(flag:=Nat.eqb run 1).
     * intros s H. assert(G:s |= V293_guard_cell running brun run ** Atrue).
       { unfold V293_exit_body_at in H;clear -H;sep auto. }
       destruct(V293_exit_running_eval running brun run Atrue s Hrun G)as[V T].
       split;[exact V|split;[exact T|discriminate]].
     * unfold V293_exit_body_post. destruct(Nat.eqb run 1)eqn:On.
       -- unfold V293_exit_body_post in Call. rewrite On in Call.
          apply Nat.eqb_eq in On. unfold V293_exit_body_at,bindings.
          eapply V293_OSIntExit_indexed_bridge
           with(Hli:=Hli)(token:=token)(old:=old)(c:=c)(nest:=nest)(locked:=locked)
           (switch_post:=switch_post);
           try eassumption.
          ++ split;[apply V293_guard_cell_good|exact F].
          ++ apply V293_saved_pointer_resource_local;exact Local.
          ++ apply Lookup;exact On.
          ++ apply Enter;exact On.
          ++ apply Exit;exact On.
          ++ apply MatchEntry;exact On.
          ++ apply MatchAcquired;exact On.
          ++ apply MatchLeaving;exact On.
          ++ apply MatchRestored;exact On.
          ++ intros Depth Lock Different. apply Call;assumption.
       -- unfold V293_exit_body_at. intros s H;exact H.
   + apply ret_rule. intros s H. apply astar_l_apure_intro;[exact H|reflexivity].
Qed.
End OriginalBody.

Section CallerGlobals.
Variables table high target current counter nesting lock running : var.
Variable tp : type.
Variables bp bo bcur bcounter bn bl brun : block.
Variables (aop:spec_code)(shared output extra:asrt)(run:nat).
Let B_external_pre := V293_exit_builder_external_pre table target current counter nesting lock running tp bp bo bcur bcounter bn bl brun aop shared extra run.
Let B_external_post := V293_exit_builder_external_post table target current counter nesting lock running tp bp bo bcur bcounter bn bl brun aop shared output extra run.
Let B_fpre := V293_exit_builder_fpre table target current counter nesting lock running tp bp bo bcur bcounter bn bl brun aop shared extra run.
Let B_fpost := V293_exit_builder_fpost table target current counter nesting lock running tp bp bo bcur bcounter bn bl brun aop shared output extra run.
Let B_pre := V293_exit_builder_pre table target current counter nesting lock running tp bp bo bcur bcounter bn bl brun aop shared extra run.
Let B_post := V293_exit_builder_post table target current counter nesting lock running tp bp bo bcur bcounter bn bl brun aop shared output extra run.
Let B_frame := V293_exit_builder_frame table high target current counter nesting lock running tp bp bo bcur bcounter bn bl brun extra run.
Variables unmap group rows : var.
Variables bt bg br bh : block.
Variables lo hi : nat.
Variable li : LocalInv.
Variable tid : Modules.tid.
Variable entries : list val.
Variable tasks : TcbMod.map.
Variable nc : nat.
Let acquired := V293_exit_acquired unmap group rows high bt bg br bh lo hi li tid aop
 tp bp bo entries tasks bcur bcounter bn bl nc.
Let leaving := V293_exit_leaving unmap group rows high bt bg br bh lo hi li tid aop
 tp bp bo entries tasks bcur bcounter bn bl nc.
Let tail := V293_exit_physical_tail unmap group rows high bt bg br bh lo hi li tid aop
 tp bp bo entries tasks bcur bcounter bn bl nc.


Theorem V293_OSIntExit_indexed_builder_resources : forall Spec sd I saved
 sched_id enter exit int_switch token old c nest locked switch_post value
 (Hli:GoodLInvAsrt li),
 table<>saved -> high<>saved -> target<>saved -> current<>saved ->
 counter<>saved -> nesting<>saved -> lock<>saved -> running<>saved ->
 run<256 -> lo<256 -> hi<256 -> (exists p,V293_bitmap_ready lo hi p) ->
 nc<256 -> nest<256 -> locked<256 -> V293_bitmap_tasks lo hi tasks ->
 V293_priority_table entries tasks -> GoodFrm extra ->
 (shared ==> CurLINV li tid) ->
 (output ==> CurLINV li tid) ->
 (forall bs,switch_post(bs,Int.zero) ==> CurLINV li tid) ->
 (run=1 -> Spec sched_id=Some(V293_sched_fpre unmap group rows high bt bg br bh li Hli,
  V293_sched_fpost unmap group rows high bt bg br bh li Hli,(Tvoid,nil))) ->
 (run=1 -> Spec enter=Some(V293_indexed_pointer_fpre entryF FEG,
  V293_indexed_pointer_fpost acquiredF FAG,(Tvoid,[Tptr Tint32]))) ->
 (run=1 -> Spec exit=Some(V293_indexed_pointer_fpre leavingF FLG,
  V293_indexed_pointer_fpost restoredF FRG,(Tvoid,[Tptr Tint32]))) ->
 (run=1 -> entryF enter_lg tid=V293_saved_pointer_resource aop(Vint32 Int.zero)shared) ->
 (run=1 -> acquiredF enter_lg tid=acquired nest locked old c token) ->
 (run=1 -> leavingF exit_lg tid=leaving nest locked old c token switch_post) ->
 (run=1 -> restoredF exit_lg tid=V293_saved_pointer_resource aop value output) ->
 (forall bs,run=1 -> V293_exit_depth nest=0 -> locked=0 ->
  V293_ready_select lo hi(V293_ready_group lo hi)<>nc ->
  InfRules Spec sd li I
   (fun result => [|result=None|] ** V293_exit_body_post run aop shared (V293_saved_pointer_resource aop value output) saved bs
     (B_frame saved)) Afalse
   ((tail(V293_exit_depth nest)locked(Int.add c Int.one) ** PV(bs,Int.zero)@Tint32|->token) **
    (Alvarenv saved Tint32(bs,0%Z) ** (B_frame saved)))
   (scall int_switch nil)
   (switch_post(bs,Int.zero) **
    (Alvarenv saved Tint32(bs,0%Z) ** (B_frame saved)))tid) ->
 InfRules Spec sd li I (B_post saved) Afalse (B_pre saved)
  (V293_OSIntExit_body running nesting lock saved table high target current counter
    sched_id enter exit int_switch) Afalse tid.
Proof.
 intros Spec sd I saved sched_id enter exit int_switch token old c nest locked switch_post value
 Hli T H G C K N L R Hrun Hlo Hhi Hr Hnc Hn Hl Hb Htable F Local OL SL Lookup Enter Exit MatchEntry MatchAcquired MatchLeaving MatchRestored Call.
 eapply conseq_rule;[apply (V293_exit_builder_unpack table high target current counter nesting lock running tp bp bo bcur bcounter bn bl brun);assumption|intros s Hs;exact Hs| ].
 apply ex_intro_rule;intro oldsave;apply ex_intro_rule;intro bs.
 eapply r_conseq_rule with(r:=fun result => [|result=None|] **
 V293_exit_body_post run aop shared(V293_saved_pointer_resource aop value output)
 saved bs(B_frame saved)).
 - intro result;apply (V293_exit_builder_pack table high target current counter nesting lock running tp bp bo bcur bcounter bn bl brun).
 - intros s Hs;exact Hs.
 - unfold B_frame,V293_exit_builder_frame.
   eapply (V293_OSIntExit_indexed_body unmap group rows high bt bg br bh lo hi li tid aop
    table target tp bp bo entries tasks current counter nesting lock bcur bcounter bn bl nc)
    with(Hli:=Hli)
    (token:=token)(old:=old)(c:=c)(nest:=nest)(locked:=locked);try eassumption.
   + split;[exact F|exact Logic.I].
   + apply V293_saved_pointer_resource_local;exact OL.
   + apply SL.
   + apply Call.
Qed.

Theorem V293_OSIntExit_indexed_builder_contract : forall P f Spec sd I saved vl lg pre post
 sched_id enter exit int_switch token old c nest locked switch_post value
 (Hli:GoodLInvAsrt li)
 (GP:GoodFunAsrt B_external_pre)
 (GQ:forall result,GoodFunAsrt(B_external_post result)),
 table<>saved -> high<>saved -> target<>saved -> current<>saved ->
 counter<>saved -> nesting<>saved -> lock<>saved -> running<>saved ->
 run<256 -> lo<256 -> hi<256 -> (exists p,V293_bitmap_ready lo hi p) ->
 nc<256 -> nest<256 -> locked<256 -> V293_bitmap_tasks lo hi tasks ->
 V293_priority_table entries tasks -> GoodFrm extra ->
 (shared ==> CurLINV li tid) ->
 (output ==> CurLINV li tid) ->
 (forall bs,switch_post(bs,Int.zero) ==> CurLINV li tid) ->
 (run=1 -> Spec sched_id=Some(V293_sched_fpre unmap group rows high bt bg br bh li Hli,
  V293_sched_fpost unmap group rows high bt bg br bh li Hli,(Tvoid,nil))) ->
 (run=1 -> Spec enter=Some(V293_indexed_pointer_fpre entryF FEG,
  V293_indexed_pointer_fpost acquiredF FAG,(Tvoid,[Tptr Tint32]))) ->
 (run=1 -> Spec exit=Some(V293_indexed_pointer_fpre leavingF FLG,
  V293_indexed_pointer_fpost restoredF FRG,(Tvoid,[Tptr Tint32]))) ->
 (run=1 -> entryF enter_lg tid=V293_saved_pointer_resource aop(Vint32 Int.zero)shared) ->
 (run=1 -> acquiredF enter_lg tid=acquired nest locked old c token) ->
 (run=1 -> leavingF exit_lg tid=leaving nest locked old c token switch_post) ->
 (run=1 -> restoredF exit_lg tid=V293_saved_pointer_resource aop value output) ->
 (forall bs,run=1 -> V293_exit_depth nest=0 -> locked=0 ->
  V293_ready_select lo hi(V293_ready_group lo hi)<>nc ->
  InfRules Spec sd li I
   (fun result => [|result=None|] ** V293_exit_body_post run aop shared (V293_saved_pointer_resource aop value output) saved bs
     (B_frame saved)) Afalse
   ((tail(V293_exit_depth nest)locked(Int.add c Int.one) ** PV(bs,Int.zero)@Tint32|->token) **
    (Alvarenv saved Tint32(bs,0%Z) ** (B_frame saved)))
   (scall int_switch nil)
   (switch_post(bs,Int.zero) **
    (Alvarenv saved Tint32(bs,0%Z) ** (B_frame saved)))tid) ->
 P f=Some(V293_OSIntExit_function running nesting lock saved table high target current counter
  sched_id enter exit int_switch) ->
 Some pre=BuildPreI P f vl lg(B_fpre GP)tid ->
 Some post=BuildRetI P f vl lg(B_fpost GQ)tid ->
 InfRules Spec sd li I post Afalse pre
  (V293_OSIntExit_body running nesting lock saved table high target current counter
    sched_id enter exit int_switch) Afalse tid.
Proof.
 intros P f Spec sd I saved vl lg pre post sched_id enter exit int_switch token old c nest locked
 switch_post value Hli GP GQ T H G C K N L R Hrun Hlo Hhi Hr Hnc Hn Hl Hb Htable F
 Local OL SL Lookup Enter Exit MatchEntry MatchAcquired MatchLeaving MatchRestored Call Body Pre Post.
 destruct(V293_exit_builder_identify table high target current counter nesting lock running tp bp bo bcur bcounter bn bl brun aop shared output extra run P f saved sched_id enter exit int_switch vl lg tid pre post
 GP GQ Body Pre Post)as[EP EQ];subst pre post.
 apply V293_OSIntExit_indexed_builder_resources with(Hli:=Hli)(token:=token)(old:=old)(c:=c)(nest:=nest)(locked:=locked)
 (switch_post:=switch_post)(value:=value);assumption.
Qed.
End CallerGlobals.
End IndexedPort.
