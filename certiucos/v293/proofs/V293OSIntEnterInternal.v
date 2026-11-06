Require Import CertiOS.certiucos.v293.code.V293OSIntEnter.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFieldsHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickDelayHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedGuards.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.
Definition V293_interrupt_nest_after run nest :=
 if Nat.eqb run 1 && Nat.ltb nest 255 then S nest else nest.
Definition V293_interrupt_cells (br bn : block) run nest :=
 [((br,0%Z),Tint8,V293_byteval run);((bn,0%Z),Tint8,V293_byteval nest)].
Definition V293_interrupt_env (running nesting : var) br bn (ge le : env) :=
 @get var (block*type) env EnvMap le running=None /\ get ge running=Some(br,Tint8) /\
 get le nesting=None /\ get ge nesting=Some(bn,Tint8).

Lemma V293_interrupt_eq_one : forall n, n<256 ->
 Int.eq (Int.repr (Z.of_nat n)) Int.one=Nat.eqb n 1.
Proof.
 intros n Hn. destruct (Nat.eqb n 1) eqn:E.
 - apply Nat.eqb_eq in E;subst;reflexivity.
 - apply Int.eq_false. intro X. apply (f_equal Int.unsigned) in X.
   rewrite Int.unsigned_repr in X by (unfold Int.max_unsigned,Int.modulus,Int.wordsize;simpl;lia).
   change (Z.of_nat n=1)%Z in X. apply Nat.eqb_neq in E;lia.
Qed.
Lemma V293_interrupt_lt_255 : forall n, n<256 ->
 Int.ltu (Int.repr (Z.of_nat n)) (Int.repr 255)=Nat.ltb n 255.
Proof.
 intros n Hn. unfold Int.ltu.
 rewrite !Int.unsigned_repr by (unfold Int.max_unsigned,Int.modulus,Int.wordsize;simpl;lia).
 destruct (zlt (Z.of_nat n) 255); destruct (Nat.ltb n 255) eqn:E;auto;
 apply Nat.ltb_lt in E || apply Nat.ltb_ge in E;lia.
Qed.
Lemma V293_interrupt_byte_add : forall n, n<255 ->
 Int.modu (Int.add (Int.repr (Z.of_nat n)) Int.one) (Int.repr Byte.modulus)=
 Int.repr (Z.of_nat (S n)).
Proof.
 intros n Hn.
 assert (U:Int.unsigned(Int.repr(Z.of_nat n))=Z.of_nat n).
 { apply Int.unsigned_repr. unfold Int.max_unsigned,Int.modulus,Int.wordsize;simpl;lia. }
 unfold Int.add. rewrite U. change (Int.modu (Int.repr (Z.of_nat n+1)) (Int.repr 256)=Int.repr (Z.of_nat (S n))).
 unfold Int.modu. rewrite !Int.unsigned_repr by (unfold Int.max_unsigned,Int.modulus,Int.wordsize;simpl;lia).
 change (Int.repr ((Z.of_nat n+1) mod 256)=Int.repr (Z.of_nat(S n))).
 rewrite Z.mod_small by lia. f_equal;lia.
Qed.

Lemma V293_interrupt_owned_eval : forall running nesting br bn run nest R s,
 run<256 -> nest<256 ->
 (forall st,st |= R -> V293_interrupt_env running nesting br bn (getgenv st) (getlenv st)) ->
 s |= V293_rdy_raw_cells (V293_interrupt_cells br bn run nest) R ->
 (evalval (V293_OSIntEnter_running running) (getsmem s)=
   Some(Vint32(if Nat.eqb run 1 then Int.one else Int.zero)) /\
  evaltype (V293_OSIntEnter_running running) (getsmem s)=Some Tint32) /\
 (evalval (V293_OSIntEnter_room nesting) (getsmem s)=
   Some(Vint32(if Nat.ltb nest 255 then Int.one else Int.zero)) /\
  evaltype (V293_OSIntEnter_room nesting) (getsmem s)=Some Tint32) /\
 (evaladdr (evar nesting) (getsmem s)=Some(Vptr(bn,Int.zero)) /\
  evaltype (evar nesting) (getsmem s)=Some Tint8) /\
 (nest<255 -> evalval (V293_OSIntEnter_next nesting) (getsmem s)=Some(V293_byteval(S nest)) /\
  evaltype (V293_OSIntEnter_next nesting) (getsmem s)=Some Tint8).
Proof.
 intros running nesting br bn run nest R s Hr Hn Env Owned.
 pose proof (V293_raw_cells_frame_env _ _ _ Env _ Owned) as (Nr&Gr&Nn&Gn).
 assert (Lr:load Tint8 (getmem s)(br,0%Z)=Some(V293_byteval run)).
 { eapply (V293_rdy_raw_load (V293_interrupt_cells br bn run nest) R _ _ _ s);[cbn [V293_interrupt_cells In];tauto|apply V293_byte_type;exact Hr|exact Owned]. }
 assert (Ln:load Tint8 (getmem s)(bn,0%Z)=Some(V293_byteval nest)).
 { eapply (V293_rdy_raw_load (V293_interrupt_cells br bn run nest) R _ _ _ s);[cbn [V293_interrupt_cells In];tauto|apply V293_byte_type;exact Hn|exact Owned]. }
 destruct s as [[[[[[ge le] M] ir] aux] O] op].
 cbn [getgenv getlenv getmem get_smem get_genv get_lenv get_mem] in Nr,Gr,Nn,Gn,Lr,Ln.
 unfold V293_OSIntEnter_running,V293_OSIntEnter_room,V293_OSIntEnter_next.
 cbn [getsmem get_smem evalval evaltype evaladdr get_lenv get_genv].
 rewrite Nr,Nn,Gr,Gn. cbn -[load]. rewrite Lr,Ln.
 unfold V293_byteval. cbn [cast_eval bop_eval val_eq bop_type cmp_val cmpu].
 rewrite V293_interrupt_eq_one by exact Hr. rewrite V293_interrupt_lt_255 by exact Hn.
 change (Nat.ltb nest 255) with (Nat.leb nest 254).
 repeat split;try (destruct (Nat.eqb run 1);reflexivity);try (destruct(Nat.leb nest 254);reflexivity).
 change (Some(Vint32(Int.modu(Int.add(Int.repr(Z.of_nat nest))Int.one)(Int.repr Byte.modulus)))=Some(Vint32(Int.repr(Z.of_nat(S nest))))).
 rewrite V293_interrupt_byte_add by assumption. reflexivity.
Qed.

Theorem V293_OSIntEnter_updates_hoare : forall Spec sd li I r ri tid aop
 running nesting br bn run nest R,
 run<256 -> nest<256 ->
 (forall st,st |= R -> V293_interrupt_env running nesting br bn (getgenv st) (getlenv st)) ->
 (R ==> CurLINV li tid) ->
 InfRules Spec sd li I r ri
 (<||aop||> ** V293_rdy_raw_cells (V293_interrupt_cells br bn run nest) R)
 (V293_OSIntEnter_updates running nesting)
 (<||aop||> ** V293_rdy_raw_cells (V293_interrupt_cells br bn run (V293_interrupt_nest_after run nest)) R) tid.
Proof.
 intros Spec sd li I r ri tid aop running nesting br bn run nest R Hr Hn Env Linv.
 assert (E:forall s,s |= V293_rdy_raw_cells(V293_interrupt_cells br bn run nest)R ->
   (s |= Rv (V293_OSIntEnter_running running) @ Tint32 == Vint32(if Nat.eqb run 1 then Int.one else Int.zero)) /\
   (s |= Rv (V293_OSIntEnter_room nesting) @ Tint32 == Vint32(if Nat.ltb nest 255 then Int.one else Int.zero))).
 { intros s HS. destruct(V293_interrupt_owned_eval _ _ _ _ _ _ _ s Hr Hn Env HS) as [[Er Tr] [[En Tn] Rest]].
   split;split; [exact Er|split; [exact Tr|discriminate]|exact En|split; [exact Tn|discriminate]]. }
 unfold V293_OSIntEnter_updates,V293_interrupt_nest_after.
 eapply V293_tick_known_ift_hoare with(flag:=Nat.eqb run 1).
 - intros s HS. apply astar_l_aop'_elim in HS as [_ Owned]. exact(proj1(E s Owned)).
 - destruct(Nat.eqb run 1) eqn:Erun; [ | intros s HS;exact HS].
   eapply seq_rule with(p':=<||aop||> ** V293_rdy_raw_cells(V293_interrupt_cells br bn run (if Nat.ltb nest 255 then S nest else nest))R).
   + eapply V293_tick_known_ift_hoare with(flag:=Nat.ltb nest 255).
     * intros s HS. apply astar_l_aop'_elim in HS as [_ Owned]. exact(proj2(E s Owned)).
     * destruct(Nat.ltb nest 255)eqn:Eroom; [ | intros s HS;exact HS].
       apply Nat.ltb_lt in Eroom.
       change (InfRules Spec sd li I r ri
        (<||aop||> ** V293_rdy_raw_cells ([((br,0%Z),Tint8,V293_byteval run)]++((bn,0%Z),Tint8,V293_byteval nest)::[])R)
        (sassign (evar nesting)(V293_OSIntEnter_next nesting))
        (<||aop||> ** V293_rdy_raw_cells ([((br,0%Z),Tint8,V293_byteval run)]++((bn,0%Z),Tint8,V293_byteval(S nest))::[])R)tid).
       eapply V293_raw_assign_hoare with(rt:=Tint8).
       -- reflexivity.
       -- apply eq_int;auto.
       -- intros s HS. destruct(V293_interrupt_owned_eval _ _ _ _ _ _ _ s Hr Hn Env HS) as [_ [_ [[A T] Next]]].
          destruct(Next Eroom)as[V TV]. split;[split;assumption|split; [exact V|split; [exact TV|discriminate]]].
       -- exact Linv.
   + apply skip_rule.
Qed.

Definition V293_interrupt_globals (running nesting : var) br bn : asrt :=
 Agvarenv running Tint8 (br,0%Z) //\\ Agvarenv nesting Tint8 (bn,0%Z).
Definition V293_interrupt_resource running nesting br bn run nest li tid :=
 V293_rdy_raw_cells (V293_interrupt_cells br bn run nest)
   (V293_interrupt_globals running nesting br bn ** (CurLINV li tid ** Aie false)).
Definition V293_interrupt_pre running nesting br bn run nest li tid aop :=
 [|run<256 /\ nest<256|] ** (<||aop||> ** V293_interrupt_resource running nesting br bn run nest li tid).
Definition V293_interrupt_post running nesting br bn run nest li tid aop (result:option val) :=
 [|result=None|] ** (<||aop||> ** V293_interrupt_resource running nesting br bn run (V293_interrupt_nest_after run nest) li tid).

Lemma V293_interrupt_resource_good : forall running nesting br bn run nest li tid,
 GoodLInvAsrt li -> GoodFunAsrt(V293_interrupt_resource running nesting br bn run nest li tid).
Proof.
 intros. unfold V293_interrupt_resource,V293_interrupt_cells,V293_interrupt_globals;cbn [V293_rdy_raw_cells].
 repeat split;try exact I. apply V293_CurLINV_function_assertion;exact H.
Qed.
Definition V293_interrupt_pre_asrt running nesting br bn li tid (lg:list logicvar) :=
 match lg with
 | cons (logic_lv (cons (Vint32 run) (cons (Vint32 nest) nil))) (cons (logic_code aop) nil) =>
   V293_interrupt_pre running nesting br bn (Z.to_nat(Int.unsigned run)) (Z.to_nat(Int.unsigned nest)) li tid aop
 | _ => Afalse end.
Definition V293_interrupt_post_asrt running nesting br bn li tid (lg:list logicvar) result :=
 match lg with
 | cons (logic_lv (cons (Vint32 run) (cons (Vint32 nest) nil))) (cons (logic_code aop) nil) =>
   V293_interrupt_post running nesting br bn (Z.to_nat(Int.unsigned run)) (Z.to_nat(Int.unsigned nest)) li tid aop result
 | _ => Afalse end.

Local Ltac interrupt_logic_cases :=
 repeat match goal with
 | |- context[match ?x with _ => _ end] => destruct x
 end;try exact I;
 unfold V293_interrupt_pre,V293_interrupt_post;
 split; [exact I|split; [exact I|apply V293_interrupt_resource_good;assumption]].
Definition V293_interrupt_fpre (running nesting:var)(br bn:block)(li:LocalInv)(Hli:GoodLInvAsrt li):fpre.
Proof.
 intros vl lg tid. refine(@mkfunasrt(V293_interrupt_pre_asrt running nesting br bn li tid lg)_).
 unfold V293_interrupt_pre_asrt. interrupt_logic_cases.
Defined.
Definition V293_interrupt_fpost (running nesting:var)(br bn:block)(li:LocalInv)(Hli:GoodLInvAsrt li):fpost.
Proof.
 intros vl result lg tid. refine(@mkfunasrt(V293_interrupt_post_asrt running nesting br bn li tid lg result)_).
 unfold V293_interrupt_post_asrt. interrupt_logic_cases.
Defined.

Lemma V293_interrupt_empty_local : forall le x,
 eq_dom_env le [] -> @get var (block*type) env EnvMap le x=None.
Proof.
 intros le x D. destruct(get le x)as [[b t] | ]eqn:E; [ | reflexivity].
 exfalso. exact(proj2(D x t)(ex_intro _ b E)).
Qed.
Lemma V293_interrupt_builder_env : forall running nesting br bn li tid st,
 st |= (V293_interrupt_globals running nesting br bn ** (CurLINV li tid ** Aie false)) ** A_dom_lenv nil ->
 V293_interrupt_env running nesting br bn (getgenv st)(getlenv st).
Proof.
 intros running nesting br bn li tid st HS.
 apply astar_comm in HS. apply astar_l_adomlenv_elim in HS. destruct HS as[D HS].
 assert(G:@get var (block*type) env EnvMap (getgenv st) running=Some(br,Tint8) /\
          @get var (block*type) env EnvMap (getgenv st) nesting=Some(bn,Tint8)).
 { eapply V293_star_env_l with (E:=fun ge le => @get var (block*type) env EnvMap ge running=Some(br,Tint8) /\ get ge nesting=Some(bn,Tint8));[ |exact HS]. intros s [G1 G2].
   apply agvarenv_elim in G1;apply agvarenv_elim in G2. change (EnvMod.get(getgenv s)running=Some(br,Tint8) /\ EnvMod.get(getgenv s)nesting=Some(bn,Tint8));tauto. }
 unfold V293_interrupt_env. repeat split;try apply V293_interrupt_empty_local;try exact D;tauto.
Qed.

Lemma V293_interrupt_entry_rearrange : forall running nesting br bn run nest li tid aop,
 Aemp ** (V293_interrupt_pre running nesting br bn run nest li tid aop ** A_dom_lenv nil) ==>
 (<||aop||> ** V293_rdy_raw_cells(V293_interrupt_cells br bn run nest)
   ((V293_interrupt_globals running nesting br bn ** (CurLINV li tid ** Aie false)) ** A_dom_lenv nil)) ** [|run<256 /\ nest<256|].
Proof.
 intros running nesting br bn run nest li tid aop s HS. unfold V293_interrupt_pre,V293_interrupt_resource,V293_interrupt_cells in *;cbn [V293_rdy_raw_cells] in *;sep auto.
Qed.
Lemma V293_interrupt_return_rearrange : forall running nesting br bn run nest li tid aop,
 <||aop||> ** V293_rdy_raw_cells(V293_interrupt_cells br bn run (V293_interrupt_nest_after run nest))
   ((V293_interrupt_globals running nesting br bn ** (CurLINV li tid ** Aie false)) ** A_dom_lenv nil) ==>
 Aemp ** (V293_interrupt_post running nesting br bn run nest li tid aop None ** A_dom_lenv nil).
Proof.
 intros running nesting br bn run nest li tid aop s HS. unfold V293_interrupt_post,V293_interrupt_resource,V293_interrupt_cells in *;cbn [V293_rdy_raw_cells] in *;sep auto.
Qed.
Theorem V293_OSIntEnter_internal_resources : forall Spec sd li I tid aop running nesting br bn run nest,
 InfRules Spec sd li I
 (fun result => Aemp ** (V293_interrupt_post running nesting br bn run nest li tid aop result ** A_dom_lenv nil)) Afalse
 (Aemp ** (V293_interrupt_pre running nesting br bn run nest li tid aop ** A_dom_lenv nil))
 (V293_OSIntEnter_body running nesting) Afalse tid.
Proof.
 intros. eapply conseq_rule.
 - apply V293_interrupt_entry_rearrange.
 - intros s H;exact H.
 - apply pure_split_rule. intros [Hr Hn]. unfold V293_OSIntEnter_body.
   eapply seq_rule.
   + eapply V293_OSIntEnter_updates_hoare;[exact Hr|exact Hn|apply V293_interrupt_builder_env| ].
     eapply V293_star_CurLINV_l. eapply V293_star_CurLINV_r. apply V293_CurLINV_extend.
   + apply ret_rule. apply V293_interrupt_return_rearrange.
Qed.

Lemma V293_interrupt_false_entry : forall Spec sd li I r tid body,
 InfRules Spec sd li I r Afalse (Aemp ** (Afalse ** A_dom_lenv nil)) body Afalse tid.
Proof.
 intros. eapply conseq_rule with(p:=Afalse)(q:=Afalse).
 - intros s HS. apply astar_comm in HS. apply astar_assoc_elim in HS. apply astar_l_afalse_elim in HS;exact HS.
 - intros s HS;exact HS.
 - apply pfalse_rule.
Qed.
Theorem V293_OSIntEnter_internal_contract : forall P f Spec sd li I running nesting br bn
 (Hli:GoodLInvAsrt li) lg tid vl pre post,
 P f=Some(V293_OSIntEnter_function running nesting) ->
 Some pre=BuildPreI P f vl lg (V293_interrupt_fpre running nesting br bn li Hli) tid ->
 Some post=BuildRetI P f vl lg (V293_interrupt_fpost running nesting br bn li Hli) tid ->
 InfRules Spec sd li I post Afalse pre (V293_OSIntEnter_body running nesting) Afalse tid.
Proof.
 intros P f Spec sd li I running nesting br bn Hli lg tid vl pre post Code Pre Post.
 unfold BuildPreI in Pre. rewrite Code in Pre.
 destruct vl as [ |v vl].
 2: { assert(E:dl_vl_match dnil(rev(v::vl))=false).
      { destruct(rev(v::vl))eqn:E;[ |reflexivity]. apply(f_equal(@rev val))in E;rewrite rev_involutive in E;discriminate. }
      unfold V293_OSIntEnter_function in Pre;rewrite E in Pre;discriminate. }
 cbv beta iota zeta delta [V293_OSIntEnter_function rev revlcons dl_vl_match buildp good_decllist getlenvdom V293_interrupt_fpre getasrt] in Pre.
 change (Some pre=Some(Aemp ** (V293_interrupt_pre_asrt running nesting br bn li tid lg ** A_dom_lenv nil)))in Pre.
 inversion Pre;subst pre. unfold BuildRetI in Post;rewrite Code in Post.
 cbv beta iota zeta delta [V293_OSIntEnter_function rev revlcons buildq good_decllist getlenvdom V293_interrupt_fpost getasrt] in Post.
 change (Some post=Some(fun result => Aemp ** (V293_interrupt_post_asrt running nesting br bn li tid lg result ** A_dom_lenv nil)))in Post.
 inversion Post;subst post.
 unfold V293_interrupt_pre_asrt,V293_interrupt_post_asrt.
 repeat match goal with |- context[match ?x with _ => _ end] => destruct x end;
 try apply V293_interrupt_false_entry.
 apply V293_OSIntEnter_internal_resources.
Qed.
Definition V293_OSIntEnter_unit (enter:fid)(running nesting:var):progunit :=
 fun f => if Z.eq_dec f enter then Some(V293_OSIntEnter_function running nesting) else None.
Definition V293_OSIntEnter_spec enter running nesting br bn li (Hli:GoodLInvAsrt li):funspec :=
 fun f => if Z.eq_dec f enter then Some(V293_interrupt_fpre running nesting br bn li Hli,
 V293_interrupt_fpost running nesting br bn li Hli,(Tvoid,nil))else None.
Theorem V293_OSIntEnter_WFFunEnv : forall enter running nesting br bn li Hli sd I,
 WFFunEnv(V293_OSIntEnter_unit enter running nesting)(V293_OSIntEnter_spec enter running nesting br bn li Hli)sd li I.
Proof.
 intros. split.
 - intros f. unfold V293_OSIntEnter_unit,V293_OSIntEnter_spec.
   destruct(Z.eq_dec f enter);split;intros [a H];try discriminate;eexists;reflexivity.
 - intros f pre post t tl HS. unfold V293_OSIntEnter_spec in HS.
   destruct(Z.eq_dec f enter);try discriminate. inversion HS;subst pre post t tl.
   exists dnil. exists dnil. exists (V293_OSIntEnter_body running nesting). split.
   + unfold V293_OSIntEnter_unit;destruct(Z.eq_dec f enter);[reflexivity|contradiction].
   + split;[constructor | ]. split;[reflexivity | ].
     intros vl pre post lg tid Pre Post. eapply V293_OSIntEnter_internal_contract;try eassumption.
     unfold V293_OSIntEnter_unit;destruct(Z.eq_dec f enter);[reflexivity|contradiction].
Qed.
Theorem V293_OSIntEnter_builders : forall enter running nesting br bn li Hli lg tid,
 exists pre post,
 Some pre=BuildPreI(V293_OSIntEnter_unit enter running nesting)enter nil lg (V293_interrupt_fpre running nesting br bn li Hli)tid /\
 Some post=BuildRetI(V293_OSIntEnter_unit enter running nesting)enter nil lg (V293_interrupt_fpost running nesting br bn li Hli)tid.
Proof.
 intros. unfold BuildPreI,BuildRetI,V293_OSIntEnter_unit.
 destruct(Z.eq_dec enter enter);[ |contradiction]. eexists;eexists;split;reflexivity.
Qed.
