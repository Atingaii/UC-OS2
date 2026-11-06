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

Definition V293_exit_builder_domain saved := A_dom_lenv (cons (saved,Tint32) nil).
Definition V293_exit_builder_cells saved := (EX old:val,LV saved @Tint32|->old) ** Aemp.
Lemma V293_exit_builder_buildpq : forall saved,
 buildp(dcons saved Tint32 dnil)nil=Some(V293_exit_builder_cells saved) /\
 buildq(dcons saved Tint32 dnil)=Some(V293_exit_builder_cells saved).
Proof. intros;split;reflexivity. Qed.
Lemma V293_exit_builder_not_shadow : forall le saved x,
 x<>saved -> eq_dom_env le (cons (saved,Tint32) nil) -> get le x=None.
Proof.
 intros le saved x Ne D. destruct(get le x)as[[b t]| ]eqn:E;[ |reflexivity].
 exfalso. pose proof(proj2(D x t)(ex_intro _ b E))as H.
 simpl in H;destruct H as[H|H];[inversion H;congruence|contradiction].
Qed.

Lemma V293_exit_empty_star : forall p q s,
 s |= Aemp -> s |= p -> s |= q -> s |= p ** q.
Proof. intros p q s E P Q;destruct_s s;simpl in *;join auto. Qed.

Section CallerGlobals.
Variables table high target current counter nesting lock running : var.
Variable tp : type.
Variables bp bo bcur bcounter bn bl brun : block.
Definition V293_exit_builder_globals : asrt :=
 Agvarenv table(Tarray(Tptr tp)13)(bp,0%Z) //\\
 Agvarenv target(Tptr tp)(bo,0%Z) //\\
 Agvarenv current Tint8(bcur,0%Z) //\\
 Agvarenv counter Tint32(bcounter,0%Z) //\\
 Agvarenv nesting Tint8(bn,0%Z) //\\
 Agvarenv lock Tint8(bl,0%Z) //\\ Agvarenv running Tint8(brun,0%Z).
Lemma V293_exit_builder_globals_good : GoodFunAsrt V293_exit_builder_globals.
Proof. unfold V293_exit_builder_globals;cbn[GoodFunAsrt];repeat split;exact I. Qed.
Lemma V293_exit_builder_names : forall saved,
 table<>saved -> high<>saved -> target<>saved -> current<>saved ->
 counter<>saved -> nesting<>saved -> lock<>saved -> running<>saved ->
 V293_exit_builder_globals ** V293_exit_builder_domain saved ==>
 V293_exit_caller_bindings high table target tp bp bo current counter nesting lock
  bcur bcounter bn bl **
 ((Agvarenv running Tint8(brun,0%Z) //\\ A_notin_lenv running) ** V293_exit_builder_domain saved).
Proof.
 intros saved T H G C K N L R s Held.
 unfold V293_exit_builder_domain in *.
 apply astar_comm in Held;apply astar_l_adomlenv_elim in Held;destruct Held as[D Held].
 assert(Absent:forall x,x<>saved -> ~ indom(getlenv s)x).
 { intros x Ne[v E]. rewrite(V293_exit_builder_not_shadow _ _ _ Ne D)in E;discriminate. }
 assert(NT:~indom(getlenv s)table)by(apply Absent;exact T).
 assert(NH:~indom(getlenv s)high)by(apply Absent;exact H).
 assert(NG:~indom(getlenv s)target)by(apply Absent;exact G).
 assert(NC:~indom(getlenv s)current)by(apply Absent;exact C).
 assert(NK:~indom(getlenv s)counter)by(apply Absent;exact K).
 assert(NN:~indom(getlenv s)nesting)by(apply Absent;exact N).
 assert(NL:~indom(getlenv s)lock)by(apply Absent;exact L).
 assert(NR:~indom(getlenv s)running)by(apply Absent;exact R).
 assert(B:s |= (V293_exit_caller_bindings high table target tp bp bo current counter nesting lock
  bcur bcounter bn bl ** (Agvarenv running Tint8(brun,0%Z) //\\ A_notin_lenv running)) **
  A_dom_lenv (cons (saved,Tint32) nil)).
 { apply astar_comm;apply astar_l_adomlenv_intro;[ |exact D].
 unfold V293_exit_builder_globals,V293_exit_caller_bindings,V293_prefix_bindings,
  V293_counter_bindings,V293_exit_guard_bindings in *.
 destruct Held as[GT [GG [GC [GK [GN [GL GR]]]]]].
 assert(E:s |= Aemp)by(pose proof GR as E;apply agvarenv_elim in E;exact(proj2 E)).
 assert(NT0:s |= A_notin_lenv table)by(apply anotinlenv_intro;assumption).
 assert(NH0:s |= A_notin_lenv high)by(apply anotinlenv_intro;assumption).
 assert(NG0:s |= A_notin_lenv target)by(apply anotinlenv_intro;assumption).
 assert(NC0:s |= A_notin_lenv current)by(apply anotinlenv_intro;assumption).
 assert(NK0:s |= A_notin_lenv counter)by(apply anotinlenv_intro;assumption).
 assert(NN0:s |= A_notin_lenv nesting)by(apply anotinlenv_intro;assumption).
 assert(NL0:s |= A_notin_lenv lock)by(apply anotinlenv_intro;assumption).
 assert(NR0:s |= A_notin_lenv running)by(apply anotinlenv_intro;assumption).
 repeat apply V293_exit_empty_star;try exact E;repeat split;assumption.
 }
 clear -B;sep auto.
Qed.


Lemma V293_exit_builder_forget_names :
 V293_exit_caller_bindings high table target tp bp bo current counter nesting lock bcur bcounter bn bl **
 (Agvarenv running Tint8(brun,0%Z) //\\ A_notin_lenv running) ==>
 V293_exit_builder_globals.
Proof.
 intros s Held;unfold V293_exit_caller_bindings,V293_prefix_bindings,
 V293_counter_bindings,V293_exit_guard_bindings in Held.
 assert(U:s |=
 ((Agvarenv table(Tarray(Tptr tp)13)(bp,0%Z) ** Agvarenv target(Tptr tp)(bo,0%Z)) **
 (Agvarenv current Tint8(bcur,0%Z) **
 (Agvarenv counter Tint32(bcounter,0%Z) **
 (Agvarenv nesting Tint8(bn,0%Z) ** Agvarenv lock Tint8(bl,0%Z))))) **
 Agvarenv running Tint8(brun,0%Z)).
 { eapply astar_mono;[ | |exact Held].
   - eapply astar_mono.
     + intros s0 [T [G Rest]].
       apply V293_exit_empty_star;try assumption.
       apply agvarenv_elim in T;exact(proj2 T).
     + repeat apply astar_mono;intros s0 [G N];exact G.
   - intros s0 [G N];exact G. }
 sep normal in U.
 apply astar_l_agvarenv_elim in U;destruct U as[GT U].
 apply astar_l_agvarenv_elim in U;destruct U as[GG U].
 apply astar_l_agvarenv_elim in U;destruct U as[GC U].
 apply astar_l_agvarenv_elim in U;destruct U as[GK U].
 apply astar_l_agvarenv_elim in U;destruct U as[GN U].
 apply astar_l_agvarenv_elim in U;destruct U as[GL U].
 apply agvarenv_elim in U;destruct U as[GR E].
 unfold V293_exit_builder_globals;repeat split;apply agvarenv_intro;assumption.
Qed.

Variables (aop:spec_code)(shared output extra:asrt)(run:nat).
Definition V293_exit_builder_external_pre :=
 <||aop||> ** (shared ** (V293_exit_builder_globals **
 (Amapsto(brun,0%Z)Tint8 false(V293_byteval run) ** extra))).
Definition V293_exit_builder_external_post (result:option val) :=
 [|result=None|] ** (<||aop||> ** ((if Nat.eqb run 1 then output else shared) **
 (V293_exit_builder_globals ** (Amapsto(brun,0%Z)Tint8 false(V293_byteval run) ** extra)))).
Definition V293_exit_builder_pre saved :=
 V293_exit_builder_cells saved ** V293_exit_builder_external_pre ** V293_exit_builder_domain saved.
Definition V293_exit_builder_post saved result :=
 V293_exit_builder_cells saved ** V293_exit_builder_external_post result ** V293_exit_builder_domain saved.
Definition V293_exit_builder_frame saved :=
 V293_exit_caller_bindings high table target tp bp bo current counter nesting lock bcur bcounter bn bl **
 (V293_guard_cell running brun run ** (extra ** V293_exit_builder_domain saved)).
Lemma V293_exit_builder_pre_good : GoodFunAsrt shared -> GoodFunAsrt extra ->
 GoodFunAsrt V293_exit_builder_external_pre.
Proof.
 intros S E;unfold V293_exit_builder_external_pre;repeat split;try exact I;try assumption;
 apply V293_exit_builder_globals_good.
Qed.
Lemma V293_exit_builder_post_good : forall result,
 GoodFunAsrt shared -> GoodFunAsrt output -> GoodFunAsrt extra ->
 GoodFunAsrt(V293_exit_builder_external_post result).
Proof.
 intros result S O E;unfold V293_exit_builder_external_post;repeat split;try exact I;try assumption;
 try apply V293_exit_builder_globals_good;destruct(Nat.eqb run 1);assumption.
Qed.
Lemma V293_exit_builder_unpack : forall saved,
 table<>saved -> high<>saved -> target<>saved -> current<>saved ->
 counter<>saved -> nesting<>saved -> lock<>saved -> running<>saved ->
 V293_exit_builder_pre saved ==>
 EX old:val,EX bs:block,V293_exit_body_pre aop shared saved bs old(V293_exit_builder_frame saved).
Proof.
 intros saved T H G C K N L R s Held.
 assert(U:s |= (V293_exit_builder_globals ** V293_exit_builder_domain saved) **
  (V293_exit_builder_cells saved ** (<||aop||> ** (shared **
   (Amapsto(brun,0%Z)Tint8 false(V293_byteval run) ** extra))))).
 { unfold V293_exit_builder_pre,V293_exit_builder_external_pre in Held;clear -Held;sep auto. }
 eapply astar_mono in U.
 2:{ apply V293_exit_builder_names;assumption. }
 2:{ intros s0 H0;exact H0. }
 unfold V293_exit_builder_cells,Alvarmapsto,Alvarenv',Aptrmapsto,
 V293_exit_body_pre,V293_time_cell,V293_time_binding,V293_exit_builder_frame,V293_guard_cell in *.
 clear -U;sep auto.
Qed.
Lemma V293_exit_builder_pack : forall saved bs value result,
 [|result=None|] **
 V293_exit_body_post run aop shared (V293_saved_pointer_resource aop value output)
 saved bs(V293_exit_builder_frame saved) ==>
 V293_exit_builder_post saved result.
Proof.
 intros saved bs value result s Held.
 unfold V293_exit_body_post,V293_exit_builder_frame,V293_guard_cell in Held.
 assert(U:s |=
 (V293_exit_caller_bindings high table target tp bp bo current counter nesting lock bcur bcounter bn bl **
 (Agvarenv running Tint8(brun,0%Z) //\\ A_notin_lenv running)) **
 ([|result=None|] ** ((if Nat.eqb run 1 then V293_saved_pointer_resource aop value output(bs,Int.zero)
 else V293_saved_pointer_resource aop(Vint32 Int.zero)shared(bs,Int.zero)) **
 (Alvarenv saved Tint32(bs,0%Z) ** (Amapsto(brun,0%Z)Tint8 false(V293_byteval run) **
 (extra ** V293_exit_builder_domain saved)))))).
 { clear -Held;sep auto. }
 eapply astar_mono in U.
 2:{ apply V293_exit_builder_forget_names. }
 2:{ intros s0 H0;exact H0. }
 unfold V293_exit_builder_post,V293_exit_builder_external_post,V293_exit_builder_cells,
 Alvarmapsto,Alvarenv',Aptrmapsto.
 destruct(Nat.eqb run 1);unfold V293_saved_pointer_resource in U;clear -U;sep auto.
Qed.


Definition V293_exit_builder_fpre (Good:GoodFunAsrt V293_exit_builder_external_pre) : fpre :=
 fun vl lg tid => @mkfunasrt V293_exit_builder_external_pre Good.
Definition V293_exit_builder_fpost (Good:forall result,GoodFunAsrt(V293_exit_builder_external_post result)) : fpost :=
 fun vl result lg tid => @mkfunasrt(V293_exit_builder_external_post result)(Good result).

Lemma V293_exit_builder_identify : forall P f saved sched_id enter exit int_switch vl lg tid pre post
 (GP:GoodFunAsrt V293_exit_builder_external_pre)
 (GQ:forall result,GoodFunAsrt(V293_exit_builder_external_post result)),
 P f=Some(V293_OSIntExit_function running nesting lock saved table high target current counter
 sched_id enter exit int_switch) ->
 Some pre=BuildPreI P f vl lg(V293_exit_builder_fpre GP)tid ->
 Some post=BuildRetI P f vl lg(V293_exit_builder_fpost GQ)tid ->
 pre=V293_exit_builder_pre saved /\ post=V293_exit_builder_post saved.
Proof.
 intros P f saved sched_id enter exit int_switch vl lg tid pre post GP GQ Body Pre Post.
 unfold BuildPreI in Pre;rewrite Body in Pre.
 destruct vl as[ |v vl].
 2:{ assert(E:dl_vl_match dnil(rev(v::vl))=false).
     { destruct(rev(v::vl))eqn:Rev;[ |reflexivity].
       apply(f_equal(@rev val))in Rev;rewrite rev_involutive in Rev;discriminate. }
     unfold V293_OSIntExit_function in Pre;rewrite E in Pre;discriminate. }
 change(Some pre=Some(V293_exit_builder_pre saved))in Pre;inversion Pre;subst pre.
 unfold BuildRetI in Post;rewrite Body in Post.
 change(Some post=Some(V293_exit_builder_post saved))in Post;inversion Post;subst post.
 split;reflexivity.
Qed.

Theorem V293_OSIntExit_not_running_builder_resources : forall Spec sd li I tid saved
 sched_id enter exit int_switch,
 table<>saved -> high<>saved -> target<>saved -> current<>saved ->
 counter<>saved -> nesting<>saved -> lock<>saved -> running<>saved ->
 run<256 -> run<>1 -> (shared ==> CurLINV li tid) ->
 InfRules Spec sd li I (V293_exit_builder_post saved) Afalse (V293_exit_builder_pre saved)
 (V293_OSIntExit_body running nesting lock saved table high target current counter
 sched_id enter exit int_switch) Afalse tid.
Proof.
 intros Spec sd li I tid saved sched_id enter exit int_switch T H G C K N L R Bound Off Local.
 eapply conseq_rule;[apply V293_exit_builder_unpack;assumption|intros s Hs;exact Hs| ].
 apply ex_intro_rule;intro old;apply ex_intro_rule;intro bs.
 eapply r_conseq_rule with(r:=fun result => [|result=None|] **
  V293_exit_body_at aop shared saved bs(V293_exit_builder_frame saved)).
 - intro result;assert(E:Nat.eqb run 1=false)by(apply Nat.eqb_neq;exact Off).
   pose proof(V293_exit_builder_pack saved bs(Vint32 Int.zero)result)as Pack.
   unfold V293_exit_body_post in Pack;rewrite E in Pack;exact Pack.
 - intros s Hs;exact Hs.
 - let F := constr:(V293_exit_caller_bindings high table target tp bp bo current counter nesting lock
   bcur bcounter bn bl ** (extra ** V293_exit_builder_domain saved))in
   eapply r_conseq_rule with(r:=fun result => [|result=None|] **
    V293_exit_body_at aop shared saved bs(V293_guard_cell running brun run ** F)).
   + intro result;unfold V293_exit_body_at,V293_exit_builder_frame;intros s Hs;clear -Hs;sep auto.
   + intros s Hs;exact Hs.
   + eapply conseq_rule with(p:=V293_exit_body_pre aop shared saved bs old
     (V293_guard_cell running brun run **
     (V293_exit_caller_bindings high table target tp bp bo current counter nesting lock bcur bcounter bn bl **
     (extra ** V293_exit_builder_domain saved)))).
     * unfold V293_exit_body_pre,V293_exit_builder_frame;intros s Hs;clear -Hs;sep auto.
     * intros s Hs;exact Hs.
     * apply V293_OSIntExit_not_running_body;assumption.
Qed.

Theorem V293_OSIntExit_not_running_builder_contract : forall P f Spec sd li I tid saved
 sched_id enter exit int_switch vl lg pre post
 (GP:GoodFunAsrt V293_exit_builder_external_pre)
 (GQ:forall result,GoodFunAsrt(V293_exit_builder_external_post result)),
 table<>saved -> high<>saved -> target<>saved -> current<>saved ->
 counter<>saved -> nesting<>saved -> lock<>saved -> running<>saved ->
 run<256 -> run<>1 -> (shared ==> CurLINV li tid) ->
 P f=Some(V293_OSIntExit_function running nesting lock saved table high target current counter
 sched_id enter exit int_switch) ->
 Some pre=BuildPreI P f vl lg(V293_exit_builder_fpre GP)tid ->
 Some post=BuildRetI P f vl lg(V293_exit_builder_fpost GQ)tid ->
 InfRules Spec sd li I post Afalse pre
 (V293_OSIntExit_body running nesting lock saved table high target current counter
 sched_id enter exit int_switch) Afalse tid.
Proof.
 intros P f Spec sd li I tid saved sched_id enter exit int_switch vl lg pre post GP GQ
 T H G C K N L R Bound Off Local Body Pre Post.
 destruct(V293_exit_builder_identify P f saved sched_id enter exit int_switch vl lg tid pre post
 GP GQ Body Pre Post)as[EP EQ];subst pre post.
 apply V293_OSIntExit_not_running_builder_resources;assumption.
Qed.


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

Theorem V293_OSIntExit_builder_resources : forall Spec sd I saved
 sched_id enter exit int_switch token old c nest locked switch_post value
 (Hli:GoodLInvAsrt li)(SharedGood:GoodFunAsrt shared)
 (SG:forall address,GoodFunAsrt(switch_post address))
 (OutGood:GoodFunAsrt output),
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
  V293_saved_pointer_fpost tid(V293_saved_pointer_resource aop value output)
   (V293_saved_pointer_resource_good aop value output OutGood),(Tvoid,(Tptr Tint32)::nil))) ->
 (forall bs,run=1 -> V293_exit_depth nest=0 -> locked=0 ->
  V293_ready_select lo hi(V293_ready_group lo hi)<>nc ->
  InfRules Spec sd li I
   (fun result => [|result=None|] ** V293_exit_body_post run aop shared (V293_saved_pointer_resource aop value output) saved bs
     (V293_exit_builder_frame saved)) Afalse
   ((tail(V293_exit_depth nest)locked(Int.add c Int.one) ** PV(bs,Int.zero)@Tint32|->token) **
    (Alvarenv saved Tint32(bs,0%Z) ** (V293_exit_builder_frame saved)))
   (scall int_switch nil)
   (switch_post(bs,Int.zero) **
    (Alvarenv saved Tint32(bs,0%Z) ** (V293_exit_builder_frame saved)))tid) ->
 InfRules Spec sd li I (V293_exit_builder_post saved) Afalse (V293_exit_builder_pre saved)
  (V293_OSIntExit_body running nesting lock saved table high target current counter
    sched_id enter exit int_switch) Afalse tid.
Proof.
 intros Spec sd I saved sched_id enter exit int_switch token old c nest locked switch_post value
 Hli SharedGood SG OutGood T H G C K N L R Hrun Hlo Hhi Hr Hnc Hn Hl Hb Htable F Local OL SL Lookup Enter Exit Call.
 eapply conseq_rule;[apply V293_exit_builder_unpack;assumption|intros s Hs;exact Hs| ].
 apply ex_intro_rule;intro oldsave;apply ex_intro_rule;intro bs.
 eapply r_conseq_rule with(r:=fun result => [|result=None|] **
 V293_exit_body_post run aop shared(V293_saved_pointer_resource aop value output)
 saved bs(V293_exit_builder_frame saved)).
 - intro result;apply V293_exit_builder_pack.
 - intros s Hs;exact Hs.
 - unfold V293_exit_builder_frame.
   eapply (V293_OSIntExit_body_hoare unmap group rows high bt bg br bh lo hi li tid aop
    table target tp bp bo entries tasks current counter nesting lock bcur bcounter bn bl nc)
    with(Hli:=Hli)(SharedGood:=SharedGood)(SG:=SG)
    (RG:=V293_saved_pointer_resource_good aop value output OutGood)
    (token:=token)(old:=old)(c:=c)(nest:=nest)(locked:=locked);try eassumption.
   + split;[exact F|exact Logic.I].
   + apply V293_saved_pointer_resource_local;exact OL.
   + apply SL.
   + apply Call.
Qed.
Theorem V293_OSIntExit_builder_contract : forall P f Spec sd I saved vl lg pre post
 sched_id enter exit int_switch token old c nest locked switch_post value
 (Hli:GoodLInvAsrt li)(SharedGood:GoodFunAsrt shared)
 (SG:forall address,GoodFunAsrt(switch_post address))
 (OutGood:GoodFunAsrt output)
 (GP:GoodFunAsrt V293_exit_builder_external_pre)
 (GQ:forall result,GoodFunAsrt(V293_exit_builder_external_post result)),
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
  V293_saved_pointer_fpost tid(V293_saved_pointer_resource aop value output)
   (V293_saved_pointer_resource_good aop value output OutGood),(Tvoid,(Tptr Tint32)::nil))) ->
 (forall bs,run=1 -> V293_exit_depth nest=0 -> locked=0 ->
  V293_ready_select lo hi(V293_ready_group lo hi)<>nc ->
  InfRules Spec sd li I
   (fun result => [|result=None|] ** V293_exit_body_post run aop shared (V293_saved_pointer_resource aop value output) saved bs
     (V293_exit_builder_frame saved)) Afalse
   ((tail(V293_exit_depth nest)locked(Int.add c Int.one) ** PV(bs,Int.zero)@Tint32|->token) **
    (Alvarenv saved Tint32(bs,0%Z) ** (V293_exit_builder_frame saved)))
   (scall int_switch nil)
   (switch_post(bs,Int.zero) **
    (Alvarenv saved Tint32(bs,0%Z) ** (V293_exit_builder_frame saved)))tid) ->
 P f=Some(V293_OSIntExit_function running nesting lock saved table high target current counter
  sched_id enter exit int_switch) ->
 Some pre=BuildPreI P f vl lg(V293_exit_builder_fpre GP)tid ->
 Some post=BuildRetI P f vl lg(V293_exit_builder_fpost GQ)tid ->
 InfRules Spec sd li I post Afalse pre
  (V293_OSIntExit_body running nesting lock saved table high target current counter
    sched_id enter exit int_switch) Afalse tid.
Proof.
 intros P f Spec sd I saved vl lg pre post sched_id enter exit int_switch token old c nest locked
 switch_post value Hli SharedGood SG OutGood GP GQ T H G C K N L R Hrun Hlo Hhi Hr Hnc Hn Hl Hb Htable F
 Local OL SL Lookup Enter Exit Call Body Pre Post.
 destruct(V293_exit_builder_identify P f saved sched_id enter exit int_switch vl lg tid pre post
 GP GQ Body Pre Post)as[EP EQ];subst pre post.
 apply V293_OSIntExit_builder_resources with(Hli:=Hli)(SharedGood:=SharedGood)(SG:=SG)
 (OutGood:=OutGood)(token:=token)(old:=old)(c:=c)(nest:=nest)(locked:=locked)
 (switch_post:=switch_post)(value:=value);assumption.
Qed.
End CallerGlobals.
