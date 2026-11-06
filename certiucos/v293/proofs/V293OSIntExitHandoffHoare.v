(* Actual normalized changed-task suffix. Shared writable cells return to the
   invariant before switch; the post describes THIS thread's resumption. *)
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBoundarySwitch.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStorageTail.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStoragePrefix.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitch.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrent.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition V293_handoff_binding x b :=
 Agvarenv x Tint8(b,0%Z) //\\ A_notin_lenv x.
Definition V293_handoff_byte x b n :=
 V293_handoff_binding x b ** Amapsto(b,0%Z)Tint8 true(V293_byteval n).
Lemma V293_handoff_binding_env : forall x b s,
 s |= V293_handoff_binding x b ->
 get(getgenv s)x=Some(b,Tint8) /\ get(getlenv s)x=None.
Proof.
 intros x b s[G[N E]]. destruct G as[b'[G[B _]]];inversion B;subst b'.
 split;[exact G| ]. destruct(get(getlenv s)x)as[v| ]eqn:L;[ |reflexivity].
 exfalso;apply N;exists v;exact L.
Qed.
Lemma V293_handoff_byte_read : forall x b n rest s,
 n<256 ->s |= V293_handoff_byte x b n ** rest ->
 evalval(evar x)(getsmem s)=Some(V293_byteval n) /\
 evaltype(evar x)(getsmem s)=Some Tint8.
Proof.
 intros x b n rest s Bound Held.
 assert(Env:get(getgenv s)x=Some(b,Tint8) /\ get(getlenv s)x=None).
 { eapply V293_star_env_l;[ |exact Held].
   intros st H;eapply V293_star_env_l;[apply V293_handoff_binding_env|exact H]. }
 assert(Load:load Tint8(getmem s)(b,0%Z)=Some(V293_byteval n)).
 { eapply V293_star_load_l;[ |exact Held]. intros st H;eapply V293_star_load_r;[ |exact H].
   intros st'[Map _];eapply mapstoval_load;[apply V293_byte_type;exact Bound|exact Map]. }
 destruct Env as[G N]. destruct s as[[[[[[ge le]M]ir]aux]O]op].
 cbn[getgenv getlenv getmem get_smem get_genv get_lenv get_mem]in G,N,Load.
 cbn[getsmem get_smem evalval evaltype get_lenv get_genv];rewrite N,G.
 cbn -[load];rewrite Load;split;reflexivity.
Qed.
Theorem V293_handoff_byte_copy : forall Spec sd li I r ri tid aop frame high current bh bc nh nc,
 nh<256 ->(frame ==> CurLINV li tid) ->
 InfRules Spec sd li I r ri
 (<||aop||> ** (V293_handoff_byte current bc nc ** (V293_handoff_byte high bh nh ** frame)))
 (sassign(evar current)(evar high))
 (<||aop||> ** (V293_handoff_byte current bc nh ** (V293_handoff_byte high bh nh ** frame))) tid.
Proof.
 intros Spec sd li I r ri tid aop frame high current bh bc nh nc Bound Local.
 eapply conseq_rule with
 (p:=<||aop||> ** ((V293_handoff_binding current bc ** (V293_handoff_byte high bh nh ** frame)) **
 Amapsto(bc,0%Z)Tint8 true(V293_byteval nc)))
 (q:=<||aop||> ** ((V293_handoff_binding current bc ** (V293_handoff_byte high bh nh ** frame)) **
 Amapsto(bc,0%Z)Tint8 true(V293_byteval nh))).
 - unfold V293_handoff_byte;intros st H;sep auto.
 - unfold V293_handoff_byte;intros st H;sep auto.
 - eapply assign_rule with(l:=(bc,Int.zero))(tp1:=Tint8)(tp2:=Tint8).
   + apply eq_int;auto.
   + intros st H.
     assert(G:get(getgenv st)current=Some(bc,Tint8) /\ get(getlenv st)current=None).
     { eapply V293_star_env_l;[ |exact H]. intros s HS;
       eapply V293_star_env_l;[apply V293_handoff_binding_env|exact HS]. }
     assert(B:st |= V293_handoff_byte high bh nh ** Atrue)by(clear -H;sep auto).
     destruct(V293_handoff_byte_read high bh nh Atrue st Bound B)as[Value Ty].
     split.
     * destruct G as[G N];destruct st as[[[[[[ge le]M]ir]aux]O]op].
       cbn[getgenv getlenv get_smem get_genv get_lenv]in G,N.
       cbn[sat evaladdr evaltype getsmem get_smem get_lenv get_genv];rewrite N,G;auto.
     * split;[exact Value|split;[exact Ty|discriminate]].
   + intros st H;apply V293_CurLINV_extend with(extra:=Atrue).
     eapply astar_mono;[exact Local|intros s HS;exact HS| ]. clear -H;sep auto.
Qed.

Section ChangedTail.
Variables high current counter target:var.
Variables bh bc bk:block.
Variable tp:type.
Variable rest:list(addr*type).
Variable tid:Modules.tid.
Variable tasks:TcbMod.map.
Variable events:EcbMod.map.
Variable now:int32.
Variable next:Modules.tid.
Variable aop:spec_code.
Variable stack:list hid.
Variable critical:list bool.
Variable px:asrt.
Let bytecells := ((bh,0%Z),Tint8)::((bc,0%Z),Tint8)::rest.
Let cells := ((bk,0%Z),Tint32)::bytecells.
Let inv := V293_storage_inv cells target tp.
Let private := (V293_handoff_binding high bh ** V293_handoff_binding current bc) ** px.
Definition V293_exit_handoff_tail nh nc c :=
 <||sched;;aop||> **
 ((V293_storage_open target tp tid tasks events now next ** CurTid tid) **
 ((Ais stack ** Acs critical) **
 (V293_handoff_byte high bh nh ** (V293_handoff_byte current bc nc **
 (V293_counter_cell counter bk c ** (V293_storage rest ** px)))))).
Definition V293_exit_handoff_resumed :=
 V293_storage_resumed target counter tp bk bytecells tid aop stack critical private.
Lemma V293_exit_handoff_local :
 (px ==> LINV V293_shared_li tid nil ** Atrue) ->
 CurTid tid ** px ==> CurLINV V293_shared_li tid.
Proof.
 intros Local st H;unfold CurLINV;exists(nil:list logicvar).
 eapply astar_mono in H;[ |intros s HS;exact HS|exact Local];clear -H;sep auto.
Qed.
Lemma V293_exit_handoff_close : forall nh nc c,
 nh<256 ->nc<256 ->
 V293_exit_handoff_tail nh nc c ==>
 V293_storage_tail target counter tp bk bytecells tid tasks events now next aop stack critical private c.
Proof.
 intros nh nc c Hnh Hnc st H.
 assert(Bytes:Amapsto(bh,0%Z)Tint8 true(V293_byteval nh) **
 (Amapsto(bc,0%Z)Tint8 true(V293_byteval nc) ** V293_storage rest) ==>
 V293_storage bytecells).
 { intros s HS;cbn[bytecells V293_storage].
   eapply astar_mono;[ |apply astar_mono;[ |intros s0 HS0;exact HS0]|exact HS];
   unfold V293_storage_cell;[exists(V293_byteval nh)|exists(V293_byteval nc)];
   sep auto;apply V293_byte_type;assumption. }
 assert(Reordered:st |= (Amapsto(bh,0%Z)Tint8 true(V293_byteval nh) **
 (Amapsto(bc,0%Z)Tint8 true(V293_byteval nc) ** V293_storage rest)) **
 (<||sched;;aop||> ** ((V293_storage_open target tp tid tasks events now next ** CurTid tid) **
 ((Ais stack ** Acs critical) **
 (PV(bk,Int.zero)@Tint32|->Vint32 c ** (V293_counter_bindings counter bk ** private)))))).
 { unfold V293_exit_handoff_tail,V293_handoff_byte,V293_counter_cell,private in *;clear -H;sep auto. }
 eapply astar_mono in Reordered;[ |exact Bytes|intros s HS;exact HS].
 unfold V293_storage_tail,V293_storage_switch_payload;clear -Reordered;sep auto.
Qed.
Theorem V293_exit_handoff_increment : forall Spec r ri nh nc c,
 (px ==> LINV V293_shared_li tid nil ** Atrue) ->
 InfRules Spec V293_scheduler V293_shared_li inv r ri
 (V293_exit_handoff_tail nh nc c)(V293_OSSched_increment counter)
 (V293_exit_handoff_tail nh nc(Int.add c Int.one))tid.
Proof.
 intros Spec r ri nh nc c Local.
 eapply conseq_rule with
 (p:=<||sched;;aop||> **
 (((V293_storage_open target tp tid tasks events now next ** CurTid tid) **
 ((Ais stack ** Acs critical) **
 (V293_handoff_byte high bh nh ** (V293_handoff_byte current bc nc **
 (V293_storage rest ** px))))) ** V293_counter_cell counter bk c))
 (q:=<||sched;;aop||> **
 (((V293_storage_open target tp tid tasks events now next ** CurTid tid) **
 ((Ais stack ** Acs critical) **
 (V293_handoff_byte high bh nh ** (V293_handoff_byte current bc nc **
 (V293_storage rest ** px))))) ** V293_counter_cell counter bk(Int.add c Int.one))).
 - unfold V293_exit_handoff_tail;intros st H;sep auto.
 - unfold V293_exit_handoff_tail;intros st H;sep auto.
 - apply V293_OSSched_counter_increment;intros st H;apply V293_CurLINV_extend with(extra:=Atrue).
   eapply astar_mono;[apply V293_exit_handoff_local;exact Local|intros s HS;exact HS| ]. clear -H;sep auto.
Qed.
Theorem V293_exit_handoff_copy : forall Spec r ri nh nc c,
 nh<256 ->(px ==> LINV V293_shared_li tid nil ** Atrue) ->
 InfRules Spec V293_scheduler V293_shared_li inv r ri
 (V293_exit_handoff_tail nh nc c)(sassign(evar current)(evar high))
 (V293_exit_handoff_tail nh nh c)tid.
Proof.
 intros Spec r ri nh nc c Bound Local.
 eapply conseq_rule with
 (p:=<||sched;;aop||> ** (V293_handoff_byte current bc nc **
 (V293_handoff_byte high bh nh **
 ((V293_storage_open target tp tid tasks events now next ** CurTid tid) **
 ((Ais stack ** Acs critical) ** (V293_counter_cell counter bk c ** (V293_storage rest ** px)))))))
 (q:=<||sched;;aop||> ** (V293_handoff_byte current bc nh **
 (V293_handoff_byte high bh nh **
 ((V293_storage_open target tp tid tasks events now next ** CurTid tid) **
 ((Ais stack ** Acs critical) ** (V293_counter_cell counter bk c ** (V293_storage rest ** px))))))).
 - unfold V293_exit_handoff_tail;intros st H;sep auto.
 - unfold V293_exit_handoff_tail;intros st H;sep auto.
 - apply V293_handoff_byte_copy;[exact Bound| ].
   intros st H;apply V293_CurLINV_extend with(extra:=Atrue).
   eapply astar_mono;[apply V293_exit_handoff_local;exact Local|intros s HS;exact HS| ]. clear -H;sep auto.
Qed.
Theorem V293_OSIntExit_owned_handoff : forall Spec r ri nh nc c,
 nh<256 ->indom tasks tid ->V293_highest_ready tasks next ->GoodFrm px ->
 (px ==> LINV V293_shared_li tid nil ** Atrue) ->
 InfRules Spec V293_scheduler V293_shared_li inv r ri
 (V293_exit_handoff_tail nh nc c)(V293_interrupt_handoff high current target)
 V293_exit_handoff_resumed tid.
Proof.
 intros Spec r ri nh nc c Bound Member Highest Good Local.
 unfold V293_interrupt_handoff;eapply seq_rule with(p':=V293_exit_handoff_tail nh nh c).
 - apply V293_exit_handoff_copy;assumption.
 - eapply conseq_rule with
   (p:=V293_storage_tail target counter tp bk bytecells tid tasks events now next aop stack critical private c)
   (q:=V293_exit_handoff_resumed).
   + apply V293_exit_handoff_close;assumption.
   + intros st H;exact H.
   + unfold V293_storage_tail,V293_exit_handoff_resumed,V293_storage_resumed.
     eapply switch_rule with(P':=V293_storage_switch_payload target tp bk bytecells tid tasks events now next aop stack critical c)
     (Px:=V293_counter_bindings counter bk ** private)(lg:=nil).
     * unfold private,V293_handoff_binding,V293_counter_bindings;cbn[GoodFrm];tauto.
     * intros st H;exact H.
     * apply V293_storage_tail_return.
     * apply V293_storage_tail_switch_pre;assumption.
     * unfold private;intros st H.
       assert(P:st |= px ** Atrue)by(clear -H;sep auto).
       eapply astar_mono in P;[ |exact Local|intros s HS;exact HS];clear -P;sep auto.
Qed.
Theorem V293_OSIntExit_changed_tail : forall Spec r ri nh nc c,
 nh<256 ->indom tasks tid ->V293_highest_ready tasks next ->GoodFrm px ->
 (px ==> LINV V293_shared_li tid nil ** Atrue) ->
 InfRules Spec V293_scheduler V293_shared_li inv r ri
 (V293_exit_handoff_tail nh nc c)
 (sseq(V293_OSSched_increment counter)
 (sseq(sskip None)(V293_interrupt_handoff high current target)))
 V293_exit_handoff_resumed tid.
Proof.
 intros Spec r ri nh nc c Bound Member Highest Good Local.
 eapply seq_rule with(p':=V293_exit_handoff_tail nh nc(Int.add c Int.one)).
 - apply V293_exit_handoff_increment;exact Local.
 - eapply seq_rule with(p':=V293_exit_handoff_tail nh nc(Int.add c Int.one)).
   + apply skip_rule.
   + apply V293_OSIntExit_owned_handoff;assumption.
Qed.
End ChangedTail.
