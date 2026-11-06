(* A separate candidate; old function proofs continue to use their original invariant. *)
Require Import CertiOS.certiucos.v293.proofs.V293DispatchState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitchPre.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293ReadySwitchStep.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia Coq.Logic.Classical_Prop.
Import ListNotations.
Local Open Scope nat_scope.

Require Import CertiOS.certiucos.v293.proofs.V293ReadyStorageInvariant.

Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrent.
Require Import CertiOS.certiucos.v293.proofs.V293TCBJointShared.

Section CurrentInvariant.
Variables br bg bp : block.
Variable target : var.
Variable tp : type.
Variable cells : list(addr*type).
Variable bc : block.
Let basecore:=V293_ready_storage_core br bg bp target tp cells.
Let baseinv:=V293_ready_storage_inv br bg bp target tp cells.
Let payload t tasks events now :=
 V293_shared_ready_records br bg bp t tasks events now **
 V293_ready_storage_extra target tp cells.
Definition V293_current_guard t tasks :=
 (EX nc:nat,[|V293_current_task tasks t nc|] **
   (Amapsto(bc,0%Z)Tint8 true(V293_byteval nc) ** Atrue)) \\//
 ([|V293_highest_ready tasks t|] ** Atrue).
Definition V293_ready_current_core := EX t:tid,EX tasks:TcbMod.map,
 EX events:EcbMod.map,EX now:int32,
 payload t tasks events now //\\ V293_current_guard t tasks.
Lemma V293_current_guard_good : forall t tasks,GoodInvAsrt(V293_current_guard t tasks).
Proof. intros;unfold V293_current_guard;cbn[GoodInvAsrt];auto. Qed.
Lemma V293_current_core_forget : V293_ready_current_core ==> basecore.
Proof.
 intros st[t[tasks[events[now[H G]]]]].
 unfold basecore,V293_ready_storage_core,V293_ready_core.
 unfold payload in H.
 eapply astar_mono;[ |intros s K;exact K|exact H].
 intros s K;exists t;exists tasks;exists events;exists now;exact K.
Qed.
Lemma V293_current_guard_frame : forall t tasks R,
 V293_current_guard t tasks ** R ==> V293_current_guard t tasks.
Proof.
 intros t tasks R st H;destruct st as[[[[[[ge le] M]ir]aux]O]op];apply sat_split in H.
 destruct H as(m1&m2&o1&o2&JM&JO&Guard&Frame).
 unfold V293_current_guard in *;destruct Guard as[[n G]|G].
 - left;exists n;apply astar_l_apure_elim in G;destruct G as[C G].
   apply astar_l_apure_intro;[ |exact C].
   assert(P:(ge,le,M,ir,aux,O,op)|=(Amapsto(bc,0%Z)Tint8 true(V293_byteval n) ** Atrue) ** R).
   { apply sat_split';exists m1;exists m2;exists o1;exists o2;split;[exact JM| ];split;[exact JO| ];split;[exact G|exact Frame]. }
   clear Frame;sep auto.
 - right;apply astar_l_apure_elim in G;destruct G as[Highest _].
   apply astar_l_apure_intro;[exact I|exact Highest].
Qed.
Lemma V293_current_guard_same : forall t tasks nc st,
 nc<256 ->load Tint8(getmem st)(bc,0%Z)=Some(V293_byteval nc) ->
 st|=V293_current_guard t tasks ->
 V293_current_task tasks t nc \/ V293_highest_ready tasks t.
Proof.
 intros t tasks nc st Bound Load Guard;destruct Guard as[[n G]|G].
 - apply astar_l_apure_elim in G;destruct G as[C G].
   assert(L:load Tint8(getmem st)(bc,0%Z)=Some(V293_byteval n)).
   { eapply V293_star_load_l;[ |exact G].
     intros s[Map _];eapply mapstoval_load;[apply V293_byte_type;destruct C;lia|exact Map]. }
   assert(n=nc)by(eapply V293_byteval_injective_bounded;[destruct C;lia|exact Bound|congruence]).
   subst n;left;exact C.
 - apply astar_l_apure_elim in G;right;exact(proj1 G).
Qed.
Lemma V293_current_core_good : GoodInvAsrt V293_ready_current_core.
Proof.
 unfold V293_ready_current_core;intros t tasks events now;split.
 - unfold payload;split;[ |apply V293_ready_storage_extra_good].
   unfold V293_shared_ready_records;split;[ |apply V293_ready_payload_good].
   unfold V293_shared_fields,CurTid,Agvarmapsto,Aptrmapsto;cbn[GoodInvAsrt];repeat split;exact I.
 - apply V293_current_guard_good.
Qed.
Lemma V293_current_core_precise : precise V293_ready_current_core.
Proof.
 intros s M1 M2 O1 O2 H1 H2 M O HM1 HM2 HO1 HO2.
 apply V293_current_core_forget in H1,H2.
 eapply V293_ready_storage_core_precise;eassumption.
Qed.
Lemma V293_current_guard_context : forall t tasks ge le M ir aux O op ge' le' ir' aux' O' op',
 (ge,le,M,ir,aux,O,op)|=V293_current_guard t tasks ->
 (ge',le',M,ir',aux',O',op')|=V293_current_guard t tasks.
Proof.
 intros t tasks ge le M ir aux O op ge' le' ir' aux' O' op' H.
 unfold V293_current_guard in *;destruct H as[[nc H]|H].
 - left;exists nc;apply astar_l_apure_elim in H;destruct H as[C H].
   apply astar_l_apure_intro;[ |exact C].
   apply sat_split in H;destruct H as(m1&m2&o1&o2&JM&JO&Cell&Rest).
   destruct Cell as[Map Empty].
   apply sat_split';exists m1;exists m2;exists (emp:osabst);exists O'.
   split;[exact JM| ];split;[apply map_join_comm;apply map_join_emp| ];split;[split;[exact Map|reflexivity]|exact I].
 - right;apply astar_l_apure_elim in H;destruct H as[C _].
   apply astar_l_apure_intro;[exact I|exact C].
Qed.
Lemma V293_current_core_aux : forall ge le M ir aux O op ir' aux',
 (ge,le,M,ir,aux,O,op)|=V293_ready_current_core ->
 (ge,le,M,ir',aux',O,op)|=V293_ready_current_core.
Proof.
 intros ge le M ir aux O op ir' aux' [t[tasks[events[now[Held Guard]]]]].
 exists t;exists tasks;exists events;exists now;split.
 - unfold payload in *;apply sat_split in Held;destruct Held as(m1&m2&o1&o2&JM&JO&Ready&Extra).
   apply sat_split';exists m1;exists m2;exists o1;exists o2.
   split;[exact JM| ];split;[exact JO| ];split.
   + unfold V293_shared_ready_records in *;apply sat_split in Ready;destruct Ready as(m3&m4&o3&o4&JM2&JO2&Shared&Records).
     apply sat_split';exists m3;exists m4;exists o3;exists o4.
     split;[exact JM2| ];split;[exact JO2| ];split;[exact Shared|eapply V293_ready_payload_context;exact Records].
   + unfold V293_ready_storage_extra in *;apply sat_split in Extra;destruct Extra as(m3&m4&o3&o4&JM2&JO2&Dispatch&Storage).
     apply sat_split';exists m3;exists m4;exists o3;exists o4.
     split;[exact JM2| ];split;[exact JO2| ];split;[exact Dispatch|eapply V293_storage_aux_stable;exact Storage].
 - eapply V293_current_guard_context;exact Guard.
Qed.
Definition V293_ready_current_inv : Inv.
Proof.
 intro k;destruct k.
 - refine(@mkinvasrt V293_ready_current_core V293_current_core_good _).
   split;[exact V293_current_core_precise| ].
   unfold assertion.inv_isr_prop;repeat split;intros;
     destruct s as [[[[[[ge le] M] ir] [[ie si] cs]] O] op];
     eapply V293_current_core_aux;exact H.
 - exact(V293_shared_inv(S k)).
Defined.
Lemma V293_current_noisr_tail : forall n k,
  starinv_noisr (V293_ready_current_inv) (S k) n <==> Aemp.
Proof.
  intros n. induction n; intros k s; simpl starinv_noisr; [reflexivity | ].
  split; intro Hs.
  - apply astar_l_aemp_elim in Hs. apply IHn in Hs. exact Hs.
  - apply astar_l_aemp_intro. apply IHn. exact Hs.
Qed.
Lemma V293_current_noisr_core : forall n,
  starinv_noisr (V293_ready_current_inv) 0 n <==> V293_ready_current_core.
Proof.
  intros [ | n] s; [reflexivity | ].
  split; intro Hs.
  - apply astar_r_aemp_elim. eapply astar_mono; [intros st H; exact H | intros st H; apply V293_current_noisr_tail in H; exact H | exact Hs].
  - eapply astar_mono; [intros st H; exact H | intros st H; apply V293_current_noisr_tail; exact H | ].
    apply astar_r_aemp_intro. exact Hs.
Qed.
Lemma V293_current_switch_open :
  SWINV (V293_ready_current_inv) ==>
  V293_shared_flags ** V293_ready_current_core.
Proof.
  intros s Hs. destruct s as [[[[[[ge le] M] ir] aux] O] op].
  assert (HC : forall i, ir i = false).
  { eapply (V293_shared_clear_state ge le M ir aux O op). unfold SWINV in Hs. sep auto. }
  unfold SWINV in Hs. apply sat_split in Hs.
  destruct Hs as (m1 & m2 & o1 & o2 & JM & JO & HF & k & HK).
  apply sat_split in HK. destruct HK as (m3 & m4 & o3 & o4 & JM2 & JO2 & HT & HI).
  unfold invlth_isr in HI. rewrite Nat.sub_0_r in HI.
  apply invisr_imply_noisr' in HI; [ | intros; apply HC]. apply V293_current_noisr_core in HI.
  assert (HP : (ge, le, M, ir, aux, O, op) |= (isrclr ** Aie false) ** (ATopis k ** V293_ready_current_core)).
  { apply sat_split'. exists m1. exists m2. exists o1. exists o2.  repeat first [assumption | split].
    apply sat_split'. exists m3. exists m4. exists o3. exists o4.  repeat first [assumption | split]. }
  unfold V293_shared_flags. sep auto.
Qed.
Lemma V293_current_switch_close :
  V293_shared_flags ** V293_ready_current_core ==> SWINV (V293_ready_current_inv).
Proof.
  intros s Hs. destruct s as [[[[[[ge le] M] ir] aux] O] op].
  assert (HC : forall i, ir i = false).
  { eapply (V293_shared_clear_state ge le M ir aux O op). unfold V293_shared_flags in Hs. sep auto. }
  unfold V293_shared_flags in Hs. sep normal in Hs. sep destruct Hs.
  assert (HP : (ge, le, M, ir, aux, O, op) |= (isrclr ** Aie false) ** (ATopis x ** V293_ready_current_core)) by (sep auto).
  apply sat_split in HP. destruct HP as (m1 & m2 & o1 & o2 & JM & JO & HF & HK).
  apply sat_split in HK. destruct HK as (m3 & m4 & o3 & o4 & JM2 & JO2 & HT & HI).
  apply (proj2 (V293_current_noisr_core x _)) in HI.
  apply V293_shared_clear_noisr_close in HI; [ | exact HC].
  unfold SWINV.
  apply sat_split'. exists m1. exists m2. exists o1. exists o2.  repeat first [assumption | split].
  exists x. unfold invlth_isr. rewrite Nat.sub_0_r. apply sat_split'. exists m3. exists m4. exists o3. exists o4.  repeat first [assumption | split].
Qed.


Lemma V293_current_switch_forget : forall t,
 SWINVt V293_ready_current_inv t ==> SWINVt baseinv t.
Proof.
 intros t st H;unfold SWINVt in *;fold(CurTid t)in *.
 eapply astar_mono in H;[ |apply V293_current_switch_open|intros s K;exact K].
 assert(P:st|=(V293_shared_flags ** basecore) ** CurTid t).
 { eapply astar_mono;[ |intros s K;exact K|exact H].
   eapply astar_mono;[intros s K;exact K|apply V293_current_core_forget]. }
 eapply astar_mono;[apply V293_ready_storage_switch_close|intros s K;exact K|exact P].
Qed.
Lemma V293_current_core_highest_frame : forall R ge le M ir aux O op,
 (ge,le,M,ir,aux,O,op)|=basecore ** R ->sched_self V293_scheduler O ->
 (ge,le,M,ir,aux,O,op)|=V293_ready_current_core ** R.
Proof.
 intros R ge le M ir aux O op H[ct[CT[ts[TS Highest]]]].
 apply sat_split in H;destruct H as(m1&m2&o1&o2&JM&JO&Core&Frame).
 unfold basecore,V293_ready_storage_core,V293_ready_core in Core.
 sep normal in Core;sep destruct Core.
 change((ge,le,m1,ir,aux,o1,op)|=payload x x0 x1 x2)in Core.
 assert(Fields:(ge,le,m1,ir,aux,o1,op)|=
  (CurTid x ** V293_shared_fields x x0 x1 x2) ** Atrue).
 { unfold payload,V293_shared_ready_records in Core;sep auto. }
 destruct(V293_shared_fields_core_get _ _ _ _ _ _ Fields)as[C[T _]].
 change(get o1 curtid=Some(oscurt x))in C.
 change(get o1 abstcblsid=Some(abstcblist x0))in T.
 assert(Cfull:get O curtid=Some(oscurt x))by(eapply OSAbstMod.join_get_l;[exact JO|exact C]).
 assert(Tfull:get O abstcblsid=Some(abstcblist x0))by(eapply OSAbstMod.join_get_l;[exact JO|exact T]).
 assert(x=ct)by congruence;assert(x0=ts)by congruence;subst x x0.
 apply sat_split';exists m1;exists m2;exists o1;exists o2.
 split;[exact JM| ];split;[exact JO| ];split;[ |exact Frame].
 exists ct;exists ts;exists x1;exists x2;split;[exact Core| ].
 right;apply astar_l_apure_intro;[exact I|exact Highest].
Qed.
Lemma V293_current_core_guard_frame : forall R ge le M ir aux O op,
 (ge,le,M,ir,aux,O,op)|=V293_ready_current_core ** R ->
 exists t tasks,get O curtid=Some(oscurt t) /\
 get O abstcblsid=Some(abstcblist tasks) /\
 (ge,le,M,ir,aux,O,op)|=V293_current_guard t tasks.
Proof.
 intros R ge le M ir aux O op H.
 apply sat_split in H;destruct H as(m1&m2&o1&o2&JM&JO&[t[tasks[events[now[Held Guard]]]]]&Frame).
 assert(Fields:(ge,le,m1,ir,aux,o1,op)|=
  (CurTid t ** V293_shared_fields t tasks events now) ** Atrue).
 { unfold payload,V293_shared_ready_records in Held;clear Guard Frame;sep auto. }
 destruct(V293_shared_fields_core_get _ _ _ _ _ _ Fields)as[C[T _]].
 exists t;exists tasks;split.
 - eapply OSAbstMod.join_get_l;[exact JO|exact C].
 - split;[eapply OSAbstMod.join_get_l;[exact JO|exact T]| ].
   apply V293_current_guard_frame with(R:=R).
   apply sat_split';exists m1;exists m2;exists o1;exists o2;split;[exact JM| ];split;[exact JO| ];split;[exact Guard|exact Frame].
Qed.
Theorem V293_current_core_same_sched : forall R ge le M ir aux O op t tasks lo hi entries nc,
 (ge,le,M,ir,aux,O,op)|=V293_ready_current_core ** R ->
 get O curtid=Some(oscurt t) ->get O abstcblsid=Some(abstcblist tasks) ->
 V293_ready_rel lo hi entries tasks ->nc<256 ->
 load Tint8 M(bc,0%Z)=Some(V293_byteval nc) ->
 V293_ready_select lo hi(V293_ready_group lo hi)=nc ->
 sched_self V293_scheduler O.
Proof.
 intros R ge le M ir aux O op t tasks lo hi entries nc H CT TS Rel Bound Load Equal.
 destruct(V293_current_core_guard_frame R ge le M ir aux O op H)as[u[ts[C[T G]]]].
 assert(u=t)by congruence;assert(ts=tasks)by congruence;subst u ts.
 destruct(V293_current_guard_same t tasks nc (ge,le,M,ir,aux,O,op) Bound Load G)as[Current|Highest].
 - exists t;split;[exact CT| ];exists tasks;split;[exact TS| ].
   destruct Rel as[Lo[Hi[Rep[B P]]]].
   destruct(V293_ready_selection_task lo hi entries tasks Lo Hi Rep B P)
     as[next[m[Task[Entry Highest]]]].
   assert(next=t).
   { apply(proj2(V293_OSSched_current_target lo hi entries tasks t nc next
       Lo Hi Rep B P Current Highest));exact Equal. }
   subst next;exact Highest.
 - exists t;split;[exact CT| ];exists tasks;split;assumption.
Qed.
Lemma V293_current_switch_highest : forall t ge le M ir aux O op,
 (ge,le,M,ir,aux,O,op)|=SWINVt baseinv t ->sched_self V293_scheduler O ->
 (ge,le,M,ir,aux,O,op)|=SWINVt V293_ready_current_inv t.
Proof.
 intros t ge le M ir aux O op H High;unfold SWINVt in *;fold(CurTid t)in *.
 eapply astar_mono in H;[ |apply V293_ready_storage_switch_open|intros s K;exact K].
 assert(P:(ge,le,M,ir,aux,O,op)|=basecore ** (V293_shared_flags ** CurTid t))by(sep auto).
 apply V293_current_core_highest_frame in P;[ |exact High].
 eapply astar_mono with(P:=V293_shared_flags ** V293_ready_current_core)(Q:=CurTid t).
 - apply V293_current_switch_close.
 - intros st K;exact K.
 - clear H;sep auto.
Qed.
Theorem V293_ready_current_good : GoodI V293_ready_current_inv V293_scheduler V293_shared_li.
Proof.
 pose proof(V293_ready_storage_good br bg bp target tp cells)as[NoFrame[Current[Switch Scheduler]]].
 split.
 - intros o O Of op OO Held Join;apply V293_current_noisr_core in Held.
   apply V293_current_core_forget in Held.
   eapply NoFrame;[ |exact Join].
   apply V293_ready_storage_noisr_core;exact Held.
 - split.
   + intros o O op t Held;eapply Current;apply V293_current_switch_forget;exact Held.
   + split;[ |exact Scheduler].
     intros o O op t b tq M' ct Held Highest Env Store.
     pose proof(V293_current_switch_forget ct _ Held)as Base.
     destruct(Switch o O op t b tq M' ct Base Highest Env Store)as[ts[Tasks Cases]].
     assert(Ht:V293_scheduler O t).
     { destruct o as[[[[ge le] M] ir]aux].
       apply sat_split in Highest;destruct Highest as(m1&m2&o1&o2&JM&JO&Ht&Rest).
       destruct Ht as[Sched Empty].
       exact(proj1 V293_scheduler_good o1 o2 O t JO Sched). }
     assert(Self:sched_self V293_scheduler(set O curtid(oscurt t))).
     { exists t;split;[apply map_get_set| ].
       destruct Ht as[ts'[T H]];exists ts';split;[rewrite map_get_set' by discriminate;exact T|exact H]. }
     exists ts;split;[exact Tasks| ].
     destruct Cases as[[Live After]|[Dead Release]].
     * left;split;[exact Live| ].
       destruct o as[[[[ge le] M] ir]aux];eapply V293_current_switch_highest;[exact After|exact Self].
     * right;split;[exact Dead| ];intros Mx Ox MM OO Local JM JO.
       pose proof(Release Mx Ox MM OO Local JM JO)as After.
       assert(Hfull:V293_scheduler OO t)by(exact(proj1 V293_scheduler_good O Ox OO t JO Ht)).
       assert(SelfFull:sched_self V293_scheduler(set OO curtid(oscurt t))).
       { exists t;split;[apply map_get_set| ].
         destruct Hfull as[ts'[T H]];exists ts';split;[rewrite map_get_set' by discriminate;exact T|exact H]. }
       destruct o as[[[[ge le] M] ir]aux];eapply V293_current_switch_highest;[exact After|exact SelfFull].
Qed.
End CurrentInvariant.
