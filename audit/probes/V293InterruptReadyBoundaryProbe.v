Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyBoundary.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyStorageInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitch.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.audit.probes.V293ReadyStorageInvariantProbe.
Require Import CertiOS.audit.probes.V293ReadyCriticalGlobalProbe.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.auxlibs.MapLib.
Require Import CertiOS.tactics.basetac.join_lib.
Require Import CertiOS.tactics.basetac.join_general.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.
Definition IQcore:=V293_ready_storage_core 80%positive 81%positive 82%positive
 106%Z V293_tcb_type PPcells.
Definition IQstate M ir i O:RstateOP:=
 (CGge,emp,M,ir,(false,[i],nil),O,spec_done None).
Definition IQspec:hid->option absop:=fun _=>Some(spec_done None).
Lemma IQheap : forall ir aux,exists M O,
 (CGge,emp,M,ir,aux,O,spec_done None)|=IQcore ** CurTid OwnershipWaiting.
Proof.
 intros ir aux;destruct(PPnonempty true nil)as(M&Trace&Held&Target&Cache).
 unfold CGstate in Held;apply sat_split in Held.
 destruct Held as(m1&m2&o1&o2&JM&JO&Held&Private).
 unfold SWINVt in Held.
 eapply astar_mono in Held;[ |apply V293_ready_storage_switch_open|intros s H;exact H].
 unfold V293_shared_flags,isrclr in Held;sep normal in Held;sep destruct Held.
 assert(Raw:(CGge,CGle,m1,(fun _=>false),(false,nil,[true]),o1,spec_done None)|=
 (Aisr x //\\ [|forall j,x j=false|]) ** (IQcore ** CurTid OwnershipWaiting))by(unfold IQcore,CurTid;sep auto).
 apply astar_l_aconj_elim in Raw;destruct Raw as[Raw _].
 assert(Core:(CGge,CGle,m1,(fun _=>false),(false,nil,[true]),o1,spec_done None)|=
 IQcore ** CurTid OwnershipWaiting)by(sep auto).
 assert(Good:GoodInvAsrt(IQcore ** CurTid OwnershipWaiting)).
 { split;[apply V293_ready_storage_core_good| ].
   unfold CurTid;intro tp;unfold Agvarmapsto,Agvarenv',Aptrmapsto;cbn[GoodInvAsrt];auto. }
 assert(Empty:(CGge,emp,m1,(fun _=>false),(false,nil,[true]),o1,spec_done None)|=
 IQcore ** CurTid OwnershipWaiting)by(eapply good_inv_prop;[exact Good|exact Core]).
 apply sat_split in Empty;destruct Empty as(m3&m4&o3&o4&JM2&JO2&Shared&Current).
 exists m1;exists o1;apply sat_split';exists m3;exists m4;exists o3;exists o4.
 split;[exact JM2| ];split;[exact JO2| ];split.
 - eapply V293_ready_storage_core_aux;exact Shared.
 - exact Current.
Qed.
Lemma IQactive_lower : forall i j,0<=j<i ->isrupd(fun _:hid=>false)i true j=false.
Proof.
 intros i j B;unfold isrupd;assert(E:Nat.eqb i j=false)by(apply Nat.eqb_neq;lia);rewrite E;reflexivity.
Qed.
Lemma IQentry : forall i,exists M O,
 IQstate M(isrupd(fun _:hid=>false)i true)i O |=
 ipreasrt' i(fun _:hid=>false)nil(spec_done None)PPinv **
 p_local V293_shared_li OwnershipWaiting nil.
Proof.
 intro i;destruct(IQheap (isrupd(fun _:hid=>false)i true)(false,[i],nil))as(M&O&Core).
 exists M;exists O.
 assert(ISR:(CGge,emp,empmem,isrupd(fun _:hid=>false)i true,(false,[i],nil),empabst,spec_done None)|=isr_inv).
 { exists(isrupd(fun _:hid=>false)i true);split.
   - apply aisr_intro;[split;reflexivity|reflexivity].
   - exists i;split.
     + apply atopis_intro;[split;reflexivity|reflexivity].
     + apply apure_intro;[split;reflexivity|apply IQactive_lower]. }
 assert(Pack:IQstate M(isrupd(fun _:hid=>false)i true)i O |=
 isr_inv ** (IQcore ** CurTid OwnershipWaiting)).
 { unfold IQstate;apply sat_split';exists empmem;exists M;exists empabst;exists O.
   split;[apply join_emp| ];split;[apply join_emp| ];split;assumption. }
 apply astar_l_aisr_intro with(i:=isrupd(fun _:hid=>false)i true)in Pack;[ |reflexivity].
 apply astar_l_aie_intro with(i:=false)in Pack;[ |reflexivity].
 apply astar_l_ais_intro with(i:=[i])in Pack;[ |reflexivity].
 apply astar_l_acs_intro with(i:=nil)in Pack;[ |reflexivity].
 apply astar_l_adomlenv_intro with(d:=nil)in Pack;[ |intros x tp;split;[contradiction|intros[l H];discriminate]].
 apply astar_l_aop'_intro with(aop:=spec_done None)in Pack;[ |reflexivity].
 assert(Extra:GoodLInvAsrt V293_shared_li)by apply V293_switch_li_good.
 unfold ipreasrt',invlth_noisr;rewrite Nat.sub_0_r.
 assert(Back:IQcore ==> starinv_noisr PPinv 0 i).
 { intros s H;apply V293_ready_storage_noisr_core;exact H. }
 assert(Pack2:IQstate M(isrupd(fun _:hid=>false)i true)i O |= IQcore **
 (isr_inv ** <||spec_done None||> ** Aisr(isrupd(fun _:hid=>false)i true) **
 Aie false ** Ais(i::nil) ** Acs nil ** A_dom_lenv nil ** CurTid OwnershipWaiting))by(sep auto).
 eapply astar_mono in Pack2;[ |exact Back|intros s H;exact H].
 unfold p_local,LINV,V293_shared_li;clear Pack Core;sep auto.
Qed.
Theorem IQbuilders_nonempty : forall i,
 exists pre M O,Some pre=BuildintPre i IQspec(fun _:hid=>false)nil PPinv
 V293_shared_li OwnershipWaiting nil /\
 IQstate M(isrupd(fun _:hid=>false)i true)i O |= pre.
Proof.
 intro i;destruct(IQentry i)as(M&O&Held).
 eexists;exists M;exists O;split;[reflexivity|exact Held].
Qed.
Theorem IQreturn_nonempty : forall i,exists M O,
 IQstate M(fun _:hid=>false)i O |=
 V293_irq_ready_closed 80%positive 81%positive 82%positive 106%Z V293_tcb_type PPcells
 i nil(spec_done None)OwnershipWaiting nil.
Proof.
 intro i;destruct(IQheap (fun _:hid=>false)(false,[i],nil))as(M&O&Core).
 exists M;exists O;apply V293_irq_ready_open_close.
 unfold V293_irq_ready_open,V293_irq_ready_frame.
 apply astar_l_aisr_intro with(i:=fun _:hid=>false)in Core;[ |reflexivity].
 apply astar_l_aie_intro with(i:=false)in Core;[ |reflexivity].
 apply astar_l_ais_intro with(i:=[i])in Core;[ |reflexivity].
 apply astar_l_acs_intro with(i:=nil)in Core;[ |reflexivity].
 apply astar_l_adomlenv_intro with(d:=nil)in Core;[ |intros x tp;split;[contradiction|intros[l H];discriminate]].
 apply astar_l_aop'_intro with(aop:=spec_done None)in Core;[ |reflexivity].
 assert(Extra:GoodLInvAsrt V293_shared_li)by apply V293_switch_li_good.
 unfold p_local,LINV,V293_shared_li;sep auto.
Qed.
Theorem IQreturn_builder : forall i,exists ret M O,
 Some ret=BuildintRet i IQspec(fun _:hid=>false)nil PPinv V293_shared_li OwnershipWaiting nil /\
 IQstate M(fun _:hid=>false)i O |=ret.
Proof.
 intro i;destruct(IQreturn_nonempty i)as(M&O&Held).
 eexists;exists M;exists O;split;[reflexivity| ].
 apply V293_irq_ready_return_resources;[reflexivity|exact Held].
Qed.
Definition IQother: isr:=fun j=>Nat.eqb 1 j.
Theorem IQsingle_bit_control :
 0<INUM /\ 1<INUM /\
 isrupd(isrupd(fun _:hid=>false)0 true)0 false=(fun _:hid=>false) /\
 isrupd(isrupd IQother 0 true)0 false 1=true /\
 isrupd(isrupd IQother 0 true)0 false<>(fun _:hid=>false) /\
 (forall j,j<>1 ->IQother j=(fun _:hid=>false)j).
Proof.
 split;[unfold INUM;lia| ];split;[unfold INUM;lia| ].
 split;[apply V293_irq_clear_update;reflexivity| ].
 split;[apply V293_irq_other_bit_survives;[lia|reflexivity]| ].
 split.
 - intro E;pose proof(f_equal(fun f=>f 1)E)as Bad;discriminate.
 - intros j Apart;unfold IQother;apply Nat.eqb_neq;lia.
Qed.
Theorem IQactual_endpoints : forall Spec sd pre ret,
 Some pre=BuildintPre 0 IQspec(fun _:hid=>false)nil PPinv V293_shared_li OwnershipWaiting nil ->
 Some ret=BuildintRet 0 IQspec(fun _:hid=>false)nil PPinv V293_shared_li OwnershipWaiting nil ->
 InfRules Spec sd V293_shared_li PPinv arfalse ret pre(sprim(eoi Int.zero))
 (V293_irq_ready_closed 80%positive 81%positive 82%positive 106%Z V293_tcb_type PPcells
 0 nil(spec_done None)OwnershipWaiting nil)OwnershipWaiting /\
 InfRules Spec sd V293_shared_li PPinv arfalse ret
 (V293_irq_ready_closed 80%positive 81%positive 82%positive 106%Z V293_tcb_type PPcells
 0 nil(spec_done None)OwnershipWaiting nil)(sprim exint)Afalse OwnershipWaiting.
Proof.
 intros Spec sd pre ret Pre Ret;split.
 - eapply V293_irq_ready_eoi_closed with(intspec:=IQspec)(ir:=fun _:hid=>false).
   + discriminate.
   + exact Pre.
   + reflexivity.
   + change(0<=0<2)%Z;lia.
   + reflexivity.
 - eapply V293_irq_ready_exint with(intspec:=IQspec)(ir:=fun _:hid=>false).
   + exact Ret.
   + reflexivity.
Qed.
