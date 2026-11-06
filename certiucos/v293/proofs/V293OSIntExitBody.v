(* Full original OSIntExit body, with actual call obligations left explicit.
   This does not supply a production port, local allocation or function builder. *)
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitResourceBridge.
Require Import CertiOS.certiucos.v293.code.V293OSIntEnter.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickDelayHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterInternal.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitDispatch.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitCriticalCalls.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCall.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.code.V293OSIntExit.
Require Import Coq.Lists.List.
Local Open Scope nat_scope.

Definition V293_exit_body_pre aop shared saved bs old frame : asrt :=
 <||aop||> ** (V293_time_cell true saved bs old ** (shared ** frame)).
Definition V293_exit_body_at aop shared saved bs frame : asrt :=
 V293_saved_pointer_resource aop(Vint32 Int.zero)shared(bs,Int.zero) **
 (Alvarenv saved Tint32(bs,0%Z) ** frame).
Definition V293_exit_body_post run aop shared (restored:addrval->asrt) saved bs frame : asrt :=
 (if Nat.eqb run 1 then restored(bs,Int.zero)
  else V293_saved_pointer_resource aop(Vint32 Int.zero)shared(bs,Int.zero)) **
 (Alvarenv saved Tint32(bs,0%Z) ** frame).

Lemma V293_exit_running_eval : forall x b n rest s,
  n < 256 -> s |= V293_guard_cell x b n ** rest ->
  evalval (V293_OSIntEnter_running x) (getsmem s) =
    Some (Vint32 (if Nat.eqb n 1 then Int.one else Int.zero)) /\
  evaltype (V293_OSIntEnter_running x) (getsmem s) = Some Tint32.
Proof.
  intros x b n rest s Hn Hs.
  assert (E : get (getgenv s) x = Some (b, Tint8) /\ get (getlenv s) x = None).
  { eapply V293_star_env_l; [ | exact Hs]. intros s0 H0.
    eapply V293_star_env_l; [ | exact H0]. intros s1 [G N].
    destruct G as [b' [G [Eb _]]]. inversion Eb; subst b'.
    split; [exact G | ]. cbn [sat] in N.
    destruct (get (getlenv s1) x) as [v  |  ] eqn:Ev; [exfalso; apply N; exists v; exact Ev | reflexivity]. }
  assert (L : load Tint8 (getmem s) (b, 0%Z) = Some (V293_byteval n)).
  { eapply V293_star_load_l; [ | exact Hs]. intros s0 H0.
    eapply V293_star_load_r; [ | exact H0]. intros; eapply V293_mapsto_load; eauto. }
  destruct E as [G N]. destruct s as [[[[[[ge le] M] ir] aux] O] op].
  cbn [getgenv getlenv getmem get_smem get_genv get_lenv get_mem] in G, N, L.
  unfold V293_OSIntEnter_running. cbn [getsmem get_smem evalval evaltype get_lenv get_genv].
  rewrite N, G.
  cbn -[load].
  rewrite L. unfold V293_byteval.
  cbn [cast_eval bop_eval val_eq bop_type]. rewrite V293_interrupt_eq_one by exact Hn.
  destruct (Nat.eqb n 1); split; reflexivity.
Qed.

(* This real source path still initializes saved and returns None. It needs
   neither a callee lookup nor any proof of the unreachable enabled body. *)
Theorem V293_OSIntExit_not_running_body : forall Spec sd li I tid aop shared
 saved bs old running brun run extra nesting lock table high target current counter
 sched_id enter exit int_switch,
 run<256 -> run<>1 -> (shared ==> CurLINV li tid) ->
 InfRules Spec sd li I
  (fun result => [|result=None|] ** V293_exit_body_at aop shared saved bs
    (V293_guard_cell running brun run ** extra)) Afalse
  (V293_exit_body_pre aop shared saved bs old(V293_guard_cell running brun run ** extra))
  (V293_OSIntExit_body running nesting lock saved table high target current counter
    sched_id enter exit int_switch) Afalse tid.
Proof.
 intros Spec sd li I tid aop shared saved bs old running brun run extra nesting lock
 table high target current counter sched_id enter exit int_switch Bound Off Local.
 unfold V293_OSIntExit_body. eapply seq_rule with
 (p':=V293_exit_body_at aop shared saved bs(V293_guard_cell running brun run ** extra)).
 - unfold V293_exit_body_pre,V293_exit_body_at.
   apply V293_OSIntExit_saved_initialize;exact Local.
 - eapply seq_rule with
   (p':=V293_exit_body_at aop shared saved bs(V293_guard_cell running brun run ** extra)).
   + eapply V293_tick_known_ift_hoare with(flag:=Nat.eqb run 1).
     * intros s H. assert(G:s |= V293_guard_cell running brun run ** Atrue).
       { unfold V293_exit_body_at in H;clear -H;sep auto. }
       destruct(V293_exit_running_eval running brun run Atrue s Bound G)as[V T].
       split;[exact V|split;[exact T|discriminate]].
     * assert(E:Nat.eqb run 1=false)by(apply Nat.eqb_neq;exact Off).
       rewrite E. intros s H;exact H.
   + apply ret_rule. intros s H. apply astar_l_apure_intro;[exact H|reflexivity].
Qed.

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

(* No whole enabled-branch or middle proof is supplied by the caller. Only
   the actual changed-priority interrupt-switch statement remains open. *)
Theorem V293_OSIntExit_body_hoare : forall Spec sd I saved bs oldsave running brun run extra
 sched_id enter exit int_switch token old c nest locked shared switch_post restored
 (Hli:GoodLInvAsrt li)(SharedGood:GoodFunAsrt shared)
 (SG:forall address,GoodFunAsrt(switch_post address))
 (RG:forall address,GoodFunAsrt(restored address)),
 run<256 -> lo<256 -> hi<256 -> (exists p,V293_bitmap_ready lo hi p) ->
 nc<256 -> nest<256 -> locked<256 -> V293_bitmap_tasks lo hi tasks ->
 V293_priority_table entries tasks -> GoodFrm extra ->
 (shared ==> CurLINV li tid) ->
 (restored(bs,Int.zero) ==> CurLINV li tid) ->
 (switch_post(bs,Int.zero) ==> CurLINV li tid) ->
 (run=1 -> Spec sched_id=Some(V293_sched_fpre unmap group rows high bt bg br bh li Hli,
  V293_sched_fpost unmap group rows high bt bg br bh li Hli,(Tvoid,nil))) ->
 (run=1 -> Spec enter=Some(V293_saved_pointer_fpre tid
   (V293_saved_pointer_resource aop(Vint32 Int.zero)shared)
   (V293_saved_pointer_resource_good aop(Vint32 Int.zero)shared SharedGood),
  V293_saved_pointer_fpost tid(acquired nest locked old c token)
   (V293_exit_acquired_good unmap group rows high bt bg br bh lo hi li tid aop
    tp bp bo entries tasks bcur bcounter bn bl nc nest locked old c token Hli),
  (Tvoid,(Tptr Tint32)::nil))) ->
 (run=1 -> Spec exit=Some(V293_saved_pointer_fpre tid
   (leaving nest locked old c token switch_post)
   (V293_exit_leaving_good unmap group rows high bt bg br bh lo hi li tid aop
    tp bp bo entries tasks bcur bcounter bn bl nc nest locked old c token switch_post Hli SG),
  V293_saved_pointer_fpost tid restored RG,(Tvoid,(Tptr Tint32)::nil))) ->
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
 token old c nest locked shared switch_post restored Hli SharedGood SG RG
 Hrun Hlo Hhi Hr Hnc Hn Hl Hb Htable F Local RL SL Lookup Enter Exit Call.
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
          eapply (V293_OSIntExit_resource_bridge unmap group rows high bt bg br bh lo hi li tid aop
           table target tp bp bo entries tasks current counter nesting lock bcur bcounter bn bl nc)
           with(Hli:=Hli)(token:=token)(old:=old)(c:=c)(nest:=nest)(locked:=locked)
           (switch_post:=switch_post)
           (SG:=SG)(RG:=RG)
           (EG:=V293_saved_pointer_resource_good aop(Vint32 Int.zero)shared SharedGood);
           try eassumption.
          ++ split;[apply V293_guard_cell_good|exact F].
          ++ apply V293_saved_pointer_resource_local;exact Local.
          ++ apply Lookup;exact On.
          ++ apply Enter;exact On.
          ++ apply Exit;exact On.
          ++ intros Depth Lock Different. apply Call;assumption.
       -- unfold V293_exit_body_at. intros s H;exact H.
   + apply ret_rule. intros s H. apply astar_l_apure_intro;[exact H|reflexivity].
Qed.
End OriginalBody.
