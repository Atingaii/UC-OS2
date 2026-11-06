(* Ready/TCB ownership and dispatch storage in one invariant. No value-level
   cache relation or ISR/API preservation is asserted here. *)
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

Section ReadyStorage.
Variables br bg bp : block.
Variable target : var.
Variable tp : type.
Variable cells : list (addr * type).
Definition V293_ready_storage_extra := V293_dispatch_cell target tp ** V293_storage cells.
Definition V293_ready_storage_core := V293_ready_core br bg bp ** V293_ready_storage_extra.
Lemma V293_ready_storage_extra_good : GoodInvAsrt V293_ready_storage_extra.
Proof.
 unfold V293_ready_storage_extra,V293_dispatch_cell,Agvarmapsto,Aptrmapsto.
 split;[cbn;intros;repeat split;exact I|apply V293_storage_good].
Qed.
Lemma V293_ready_storage_core_good : GoodInvAsrt V293_ready_storage_core.
Proof. split;[apply V293_ready_core_good|apply V293_ready_storage_extra_good]. Qed.
Lemma V293_ready_storage_core_precise : precise V293_ready_storage_core.
Proof.
 apply precise_star;[apply V293_ready_core_precise| ].
 apply precise_star;[apply V293_dispatch_cell_precise|apply V293_storage_precise].
Qed.
Lemma V293_ready_storage_core_aux : forall ge le M ir aux O op ir' aux',
 (ge,le,M,ir,aux,O,op) |= V293_ready_storage_core ->
 (ge,le,M,ir',aux',O,op) |= V293_ready_storage_core.
Proof.
 intros ge le M ir aux O op ir' aux' Held.
 apply sat_split in Held;destruct Held as(m1&m2&o1&o2&JM&JO&Ready&Extra).
 apply sat_split';exists m1;exists m2;exists o1;exists o2.
 split;[exact JM| ];split;[exact JO| ];split.
 - eapply V293_ready_core_aux;exact Ready.
 - apply sat_split in Extra;destruct Extra as(m3&m4&o3&o4&JM2&JO2&Dispatch&Storage).
   apply sat_split';exists m3;exists m4;exists o3;exists o4.
   split;[exact JM2| ];split;[exact JO2| ];split;[exact Dispatch| ].
   eapply V293_storage_aux_stable;exact Storage.
Qed.
Definition V293_ready_storage_inv : Inv.
Proof.
 intro k;destruct k.
 - refine(@mkinvasrt V293_ready_storage_core V293_ready_storage_core_good _).
   split;[exact V293_ready_storage_core_precise| ].
   unfold assertion.inv_isr_prop;repeat split;intros;
     destruct s as [[[[[[ge le] M] ir] [[ie si] cs]] O] op];
     eapply V293_ready_storage_core_aux;exact H.
 - exact(V293_shared_inv(S k)).
Defined.
Lemma V293_ready_storage_noisr_tail : forall n k,
  starinv_noisr (V293_ready_storage_inv) (S k) n <==> Aemp.
Proof.
  intros n. induction n; intros k s; simpl starinv_noisr; [reflexivity | ].
  split; intro Hs.
  - apply astar_l_aemp_elim in Hs. apply IHn in Hs. exact Hs.
  - apply astar_l_aemp_intro. apply IHn. exact Hs.
Qed.
Lemma V293_ready_storage_noisr_core : forall n,
  starinv_noisr (V293_ready_storage_inv) 0 n <==> V293_ready_storage_core.
Proof.
  intros [ | n] s; [reflexivity | ].
  split; intro Hs.
  - apply astar_r_aemp_elim. eapply astar_mono; [intros st H; exact H | intros st H; apply V293_ready_storage_noisr_tail in H; exact H | exact Hs].
  - eapply astar_mono; [intros st H; exact H | intros st H; apply V293_ready_storage_noisr_tail; exact H | ].
    apply astar_r_aemp_intro. exact Hs.
Qed.
Lemma V293_ready_storage_switch_open :
  SWINV (V293_ready_storage_inv) ==>
  V293_shared_flags ** V293_ready_storage_core.
Proof.
  intros s Hs. destruct s as [[[[[[ge le] M] ir] aux] O] op].
  assert (HC : forall i, ir i = false).
  { eapply (V293_shared_clear_state ge le M ir aux O op). unfold SWINV in Hs. sep auto. }
  unfold SWINV in Hs. apply sat_split in Hs.
  destruct Hs as (m1 & m2 & o1 & o2 & JM & JO & HF & k & HK).
  apply sat_split in HK. destruct HK as (m3 & m4 & o3 & o4 & JM2 & JO2 & HT & HI).
  unfold invlth_isr in HI. rewrite Nat.sub_0_r in HI.
  apply invisr_imply_noisr' in HI; [ | intros; apply HC]. apply V293_ready_storage_noisr_core in HI.
  assert (HP : (ge, le, M, ir, aux, O, op) |= (isrclr ** Aie false) ** (ATopis k ** V293_ready_storage_core)).
  { apply sat_split'. exists m1. exists m2. exists o1. exists o2.  repeat first [assumption | split].
    apply sat_split'. exists m3. exists m4. exists o3. exists o4.  repeat first [assumption | split]. }
  unfold V293_shared_flags. sep auto.
Qed.
Lemma V293_ready_storage_switch_close :
  V293_shared_flags ** V293_ready_storage_core ==> SWINV (V293_ready_storage_inv).
Proof.
  intros s Hs. destruct s as [[[[[[ge le] M] ir] aux] O] op].
  assert (HC : forall i, ir i = false).
  { eapply (V293_shared_clear_state ge le M ir aux O op). unfold V293_shared_flags in Hs. sep auto. }
  unfold V293_shared_flags in Hs. sep normal in Hs. sep destruct Hs.
  assert (HP : (ge, le, M, ir, aux, O, op) |= (isrclr ** Aie false) ** (ATopis x ** V293_ready_storage_core)) by (sep auto).
  apply sat_split in HP. destruct HP as (m1 & m2 & o1 & o2 & JM & JO & HF & HK).
  apply sat_split in HK. destruct HK as (m3 & m4 & o3 & o4 & JM2 & JO2 & HT & HI).
  apply (proj2 (V293_ready_storage_noisr_core x _)) in HI.
  apply V293_shared_clear_noisr_close in HI; [ | exact HC].
  unfold SWINV.
  apply sat_split'. exists m1. exists m2. exists o1. exists o2.  repeat first [assumption | split].
  exists x. unfold invlth_isr. rewrite Nat.sub_0_r. apply sat_split'. exists m3. exists m4. exists o3. exists o4.  repeat first [assumption | split].
Qed.

(* These are exact resource equivalences, not a transport theorem for InfRules. *)
Theorem V293_ready_storage_switch_resources : forall t,
 SWINVt V293_ready_storage_inv t <==>
 (SWINVt (V293_ready_inv br bg bp) t ** V293_ready_storage_extra).
Proof.
 intros t s;split;intro Held.
 - unfold SWINVt in *;fold(CurTid t)in *.
   eapply astar_mono in Held;[ |apply V293_ready_storage_switch_open|intros st H;exact H].
   assert(Open:s |= (V293_shared_flags ** V293_ready_core br bg bp) **
     (CurTid t ** V293_ready_storage_extra)).
   { unfold V293_ready_storage_core in Held;sep auto. }
   eapply astar_mono in Open;[ |apply V293_ready_switch_close|intros st H;exact H].
   clear Held;sep auto.
 - unfold SWINVt in *;fold(CurTid t)in *.
   assert(Open:s |= (SWINV (V293_ready_inv br bg bp)) **
     (CurTid t ** V293_ready_storage_extra)) by(sep auto).
   eapply astar_mono in Open;[ |apply V293_ready_switch_open|intros st H;exact H].
   eapply astar_mono with(P:=V293_shared_flags ** V293_ready_storage_core)(Q:=CurTid t).
   + apply V293_ready_storage_switch_close.
   + intros st H;exact H.
   + unfold V293_ready_storage_core;clear Held;sep auto.
Qed.
Lemma V293_ready_storage_store_frame : forall ct t R ge le M M' ir aux O op b tq,
 (ge,le,M,ir,aux,O,op) |= SWINVt V293_ready_storage_inv ct ** R ->
 get ge OSTCBCur=Some(b,Tptr tq) ->
 store(Tptr tq)M(b,0%Z)(Vptr t)=Some M' ->
 (ge,le,M',ir,aux,set O curtid(oscurt t),op) |= SWINVt V293_ready_storage_inv t ** R.
Proof.
 intros ct t R ge le M M' ir aux O op b tq Held Env Store.
 eapply astar_mono in Held;[ |intros st H;apply V293_ready_storage_switch_resources in H;exact H|intros st H;exact H].
 apply astar_assoc_elim in Held.
 pose proof(V293_ready_store_frame br bg bp ct t
   (V293_ready_storage_extra ** R) ge le M M' ir aux O op b tq Held Env Store)as After.
 apply astar_assoc_intro in After.
 eapply astar_mono;[ |intros st H;exact H|exact After].
 intros st H;apply V293_ready_storage_switch_resources;exact H.
Qed.
Theorem V293_ready_storage_good : GoodI V293_ready_storage_inv V293_scheduler V293_shared_li.
Proof.
 split.
 - intros o O Of op OO Held Join;apply V293_ready_storage_noisr_core in Held.
   eapply(V293_shared_no_abstract_frame(o,O,op)Of OO);[ |exact Join].
   unfold V293_ready_storage_core,V293_ready_core,V293_shared_ready_records,V293_shared_core in *;sep auto.
 - split.
   + intros o O op t Held;destruct o as [[[[ge le] M] ir] aux].
     assert(Current:(ge,le,M,ir,aux,O,op) |= CurTid t ** Atrue).
     { unfold SWINVt in Held;fold(CurTid t)in Held;sep auto. }
     destruct(V293_shared_current_read _ _ _ _ _ _ _ _ _ Current)as(b&tq&Env&Load).
     exists b;exists tq;split;[exact Env| ];split;[exact Load| ].
     apply V293_ready_storage_switch_resources in Held.
     eapply astar_mono in Held;[ |apply V293_ready_switch_full|intros st H;exact H].
     unfold V293_ready_full in Held;sep normal in Held;sep destruct Held.
     change(get(getabst(ge,le,M,ir,aux,O,op))curtid=Some(oscurt t)).
     eapply V293_star_abst_get_l with(p:=Aabsdata curtid(oscurt t))(q:=Atrue).
     * apply V293_shared_abs_get.
     * unfold V293_shared_fields in Held;clear Current;sep auto.
   + split.
     * intros o O op t b tq M' ct Held Highest Env Store;destruct o as [[[[ge le] M] ir] aux].
       assert(Map:exists ts,get O abstcblsid=Some(abstcblist ts)).
       { pose proof Held as Open;apply V293_ready_storage_switch_resources in Open.
         eapply astar_mono in Open;[ |apply V293_ready_switch_full|intros st H;exact H].
         unfold V293_ready_full in Open;sep normal in Open;sep destruct Open;exists x.
         change(get(getabst(ge,le,M,ir,aux,O,op))abstcblsid=Some(abstcblist x)).
         eapply V293_star_abst_get_l with(p:=Aabsdata abstcblsid(abstcblist x))(q:=Atrue).
         - apply V293_shared_abs_get.
         - unfold V293_shared_fields in Open;clear Held;sep auto. }
       destruct Map as[ts Map];exists ts;split;[exact Map| ].
       apply astar_r_aemp_intro in Held.
       pose proof(V293_ready_storage_store_frame ct t Aemp ge le M M' ir aux O op b tq Held Env Store)as After.
       apply astar_r_aemp_elim in After.
       destruct(classic(indom ts ct))as[Live|Dead].
       -- left;split;assumption.
       -- right;split;[exact Dead| ];intros Mx Ox MM OO Local JM JO.
          specialize(Local op);destruct Local as[lg Local].
          change(Mx=emp /\ Ox=emp)in Local;destruct Local as[EM EO];subst Mx Ox.
          apply map_join_emp' in JM;apply map_join_emp' in JO;subst MM OO;exact After.
     * apply V293_scheduler_good.
Qed.

Theorem V293_ready_storage_switch_step :
 forall pc po pi ip T cst ks (current next:tid) bt bc ge le les M ir aux au O op R,
 get les current=Some le ->get au current=Some aux ->
 get T current=Some(curs(sprim(switch target)),(kenil,ks)) ->
 get ge target=Some(bt,Tptr tp) ->load(Tptr tp)M(bt,0%Z)=Some(Vptr next) ->
 get ge OSTCBCur=Some(bc,Tptr tp) ->
 (ge,le,M,ir,aux,O,op) |= SWINVt V293_ready_storage_inv current ** R ->
 exists Mf,
 lpstep(pc,(po,pi,ip))T cst(ge,les,M,ir,au)current
   (set T current(SKIP,(kenil,ks)))cst(ge,les,Mf,ir,au)next /\
 store(Tptr tp)M(bc,0%Z)(Vptr next)=Some Mf /\
 (ge,le,Mf,ir,aux,set O curtid(oscurt next),op) |= SWINVt V293_ready_storage_inv next ** R /\
 load(Tptr tp)Mf(bc,0%Z)=Some(Vptr next) /\
 (forall c i,c<>bc \/ (i<0)%Z \/ (4<=i)%Z ->get Mf(c,i)=get M(c,i)).
Proof.
 intros pc po pi ip T cst ks current next bt bc ge le les M ir aux au O op R
   Local Aux Code Target Read Current Held.
 eapply astar_mono in Held;[ |intros st H;apply V293_ready_storage_switch_resources in H;exact H|intros st H;exact H].
 apply astar_assoc_elim in Held.
 destruct(V293_ready_switch_step br bg bp pc po pi ip T cst ks current next target bt bc
   ge le les M ir aux au O op(V293_ready_storage_extra ** R)tp
   Local Aux Code Target Read Current Held)as(Mf&Step&Store&After&Load&Skipped&Other&Outside).
 exists Mf;split;[exact Step| ];split;[exact Store| ];split.
 - apply astar_assoc_intro in After.
   eapply astar_mono;[ |intros st H;exact H|exact After].
   intros st H;apply V293_ready_storage_switch_resources;exact H.
 - split;assumption.
Qed.
Theorem V293_ready_storage_selected : forall current R s,
 s |= SWINVt V293_ready_storage_inv current ** R ->
 exists tasks lo hi entries t message,
 get(getabst s)abstcblsid=Some(abstcblist tasks) /\
 V293_ready_rel lo hi entries tasks /\
 V293_ready_loads(getmem s)br bg bp lo hi entries /\
 get tasks t=Some(Int.repr(Z.of_nat(V293_ready_select lo hi(V293_ready_group lo hi))),rdy,message) /\
 load(Tptr V293_tcb_type)(getmem s)(bp,4*Z.of_nat(V293_ready_select lo hi(V293_ready_group lo hi)))%Z=Some(Vptr t) /\
 V293_scheduler(getabst s)t.
Proof.
 intros current R s Held.
 eapply astar_mono in Held;[ |intros st H;apply V293_ready_storage_switch_resources in H;exact H|intros st H;exact H].
 apply astar_assoc_elim in Held;eapply V293_ready_switch_selected;exact Held.
Qed.
End ReadyStorage.
