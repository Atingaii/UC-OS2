(* Existing interrupt continuation, original global semantics, exact call prefix.
   No interrupt handler installation or fabricated CPU-port implementation. *)
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitSwitchEntry.
Require Import CertiOS.certiucos.v293.proofs.V293LocalGlobalTrace.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyGlobalTrace.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCallGlobal.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyFullCall.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitCallExecution.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitExecution.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrent.
Require Import CertiOS.certiucos.v293.code.V293OSIntExit.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.step_prop.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.framework.proof.join_prop.
Require Import CertiOS.tactics.basetac.join_lib.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Lemma V293_interrupt_enclosing_not_no_os : forall pc po pi ip c ke le tail inner,
 ~no_os(pc,(po,pi,ip))(inner ## kint c ke le tail).
Proof.
 intros pc po pi ip c ke le tail inner;induction inner;cbn;try tauto.
 destruct(pumerge po pi f);tauto.
Qed.

(* intcont stops at a call. Its actual lookup and goodks are needed; simply
   having an interrupt somewhere underneath a missing call is NOT sufficient. *)
Lemma V293_interrupt_enclosing_inos : forall pc po pi ip c ke le tail C,
 goodks(pc,(po,pi,ip))(snd(snd(V293_enclose C(kint c ke le tail)))) ->
 InOS(V293_enclose C(kint c ke le tail))(pumerge po pi).
Proof.
 intros pc po pi ip c ke le tail [v [ve inner]] Good.
 exists v;exists ve;exists(inner ## kint c ke le tail);split;[reflexivity| ].
 right;revert Good;induction inner;cbn;intro Good;try solve[apply IHinner;exact Good].
 - right;discriminate.
 - destruct(pumerge po pi f)as[[[[ty d1]d2]body]| ]eqn:Lookup.
   + left;exists f;exists e;exists(inner ## kint c ke le tail).
     exists ty;exists d1;exists d2;exists s;exists body;auto.
   + exfalso;eapply V293_interrupt_enclosing_not_no_os;exact Good.
 - right;discriminate.
 - contradiction.
Qed.

Lemma V293_interrupt_loststep_global : forall pc po pi ip c ke saved tail
 T les aus t cst C st C' st',
 goodks(pc,(po,pi,ip))(snd(snd(V293_enclose C(kint c ke saved tail)))) ->
 loststep(pumerge po pi)C st C' st' ->
 (match V293_local_global_at T les aus t(V293_enclose C(kint c ke saved tail))st,
        V293_local_global_at T les aus t(V293_enclose C'(kint c ke saved tail))st' with
 |(Ti,Si,ti),(Tf,Sf,tf)=>lpstep(pc,(po,pi,ip))Ti cst Si ti Tf cst Sf tf end) /\
 goodks(pc,(po,pi,ip))(snd(snd(V293_enclose C'(kint c ke saved tail)))).
Proof.
 intros pc po pi ip c ke saved tail T les aus t cst
 [v [ve inner]] [[[[ge le]M]ir]aux] [v' [ve' inner']] [[[[ge' le']M']ir']aux'] Good Step.
 pose proof(loststep_cont_locality _ _ _ _ _ _ _ _ po pi(kint c ke saved tail)Step)as Framed.
 assert(Local:ltstep(pc,(po,pi,ip))t
 (v,(ve,inner ## kint c ke saved tail))cst((ge,le,M),ir,aux)
 (v',(ve',inner' ## kint c ke saved tail))cst((ge',le',M'),ir',aux')).
 { eapply inapi_step;[reflexivity|exact Framed| ].
   exact(V293_interrupt_enclosing_inos pc po pi ip c ke saved tail(v,(ve,inner))Good). }
 split.
 - cbn[V293_local_global_at V293_global_at V293_enclose];eapply pt_step.
   + apply map_get_set.
   + symmetry;apply set_set_eq.
   + unfold projS,projD;rewrite !map_get_set;reflexivity.
   + unfold projS,projD;rewrite !map_get_set;reflexivity.
   + split;[unfold Dteq|unfold Piteq];intros other Apart;cbn;
      rewrite !map_get_set';reflexivity||congruence.
   + exact Local.
 - eapply ltstep_goodks;eauto.
Qed.

Theorem V293_interrupt_local_steps_global : forall pc po pi ip C st Cf stf,
 V293_local_steps(pumerge po pi)C st Cf stf ->
 forall c ke saved tail T les aus t cst,
 goodks(pc,(po,pi,ip))(snd(snd(V293_enclose C(kint c ke saved tail)))) ->
 V293_global_steps(pc,(po,pi,ip))cst
 (V293_local_global_at T les aus t(V293_enclose C(kint c ke saved tail))st)
 (V293_local_global_at T les aus t(V293_enclose Cf(kint c ke saved tail))stf).
Proof.
 intros pc po pi ip C st Cf stf Trace;unfold V293_local_steps in Trace.
 remember(C,st)as first eqn:First in Trace;remember(Cf,stf)as last eqn:Last in Trace.
 revert C st Cf stf First Last;induction Trace as[x|x y z Step Rest IH];
 intros C st Cf stf First Last;subst x.
 - inversion Last;subst;intros;apply rt1n_refl.
 - destruct y as[Mid smid];destruct z as[End send];inversion Last;subst End send.
   intros c ke saved tail T les aus t cst Good.
   destruct(V293_interrupt_loststep_global pc po pi ip c ke saved tail T les aus t cst
   C st Mid smid Good Step)as[Global Next].
   eapply rt1n_trans;[exact Global| ];eapply IH;eauto.
Qed.

(* Updating the current task leaves every other task map entry unchanged. *)
Lemma V293_global_endpoint_other_tasks : forall (T:tasks)(les:cltenvs)(aus:ltaskstset)t (C:code)(le:env)(aux:localst)other,
 other<>t ->
 get(set T t C)other=get T other /\
 get(set les t le)other=get les other /\
 get(set aus t aux)other=get aus other.
Proof. intros;repeat split;apply map_get_set';congruence. Qed.

Theorem V293_OSIntExit_interrupt_switch_entry :
 forall br bg bp P ks pc po pi ip T les aus cst interrupted ike interrupted_le ge caller M ir enabled si ci O op ct R tasks nc
 f sched_id unmap group rows high y table target nesting lock running saved current counter int_switch
 bt bh bo bn bl brun bc bcount c oldhigh oldtarget,
 P=pumerge po pi ->
 get T ct=Some(curs(scall f nil),(kenil,kint interrupted ike interrupted_le ks)) ->
 get les ct=Some caller ->get aus ct=Some(enabled,si,ci) ->
 goodks(pc,(po,pi,ip))ks ->
 P f=Some(V293_OSIntExit_abstract_function running nesting lock saved table high target current counter sched_id int_switch) ->
 P sched_id=Some(V293_OSSchedNew_function unmap group rows high y) ->
 ~In saved [unmap;group;rows;high;table;target;nesting;lock;running;current;counter] ->
 y<>unmap ->y<>group ->y<>rows ->y<>high ->y<>table ->bh<>bp ->bn<>bt ->
 get ge unmap=Some(bt,Tarray Tint8 256) ->get ge group=Some(bg,Tint8) ->
 get ge rows=Some(br,Tarray Tint8 2) ->get ge high=Some(bh,Tint8) ->
 get ge table=Some(bp,Tarray(Tptr V293_tcb_type)13) ->get ge target=Some(bo,Tptr V293_tcb_type) ->
 get ge nesting=Some(bn,Tint8) ->get ge lock=Some(bl,Tint8) ->
 get ge running=Some(brun,Tint8) ->get ge current=Some(bc,Tint8) ->get ge counter=Some(bcount,Tint32) ->
 get O abstcblsid=Some(abstcblist tasks) ->V293_current_task tasks ct nc ->
 ~V293_highest_ready tasks ct ->GoodInvAsrt R ->
 (forall n,n<256 ->load Tint8 M(bt,Z.of_nat n)=Some(V293_byteval(V293_ready_lookup n))) ->
 (ge,caller,M,ir,(false,si,ci),O,op)|=SWINVt(V293_ready_inv br bg bp)ct **
 (V293_owned_record_cell((bh,0%Z),Tint8,oldhigh) **
 (V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,oldtarget) **
 (V293_owned_record_cell((bn,0%Z),Tint8,V293_byteval 1) **
 (V293_owned_record_cell((bl,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval nc) **
 (V293_owned_record_cell((brun,0%Z),Tint8,V293_byteval 1) **
 (V293_owned_record_cell((bcount,0%Z),Tint32,Vint32 c) **R))))))) ->
 exists bs next nh Mf,fresh M bs /\ next<>ct /\ nh<>nc /\
 V293_highest_ready tasks next /\V293_current_task tasks next nh /\
 V293_global_steps(pc,(po,pi,ip))cst
 (T,(ge,les,M,ir,aus),ct)
 (set T ct(curs(sfexec int_switch nil nil),(kenil,
   kseq(sprim excrit)(kseq sret(kcall f
     (V293_OSIntExit_abstract_body running nesting lock saved table high target current counter sched_id int_switch)
       caller(kint interrupted ike interrupted_le ks))))),
  (ge,set les ct(V293_cpu_lenv saved bs),Mf,ir,set aus ct(false,si,enabled::ci)),ct) /\
 (ge,V293_cpu_lenv saved bs,Mf,ir,(false,si,enabled::ci),O,op)|=
 SWINVt(V293_ready_inv br bg bp)ct **
 (V293_owned_record_cell((bh,0%Z),Tint8,V293_byteval nh) **
 (V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,Vptr next) **
 (V293_owned_record_cell((bn,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((bl,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval nc) **
 (V293_owned_record_cell((brun,0%Z),Tint8,V293_byteval 1) **
 (V293_owned_record_cell((bcount,0%Z),Tint32,Vint32(Int.add c Int.one)) **
 (Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **R)))))))) /\
 load(Tptr V293_tcb_type)Mf(bo,0%Z)=Some(Vptr next) /\
 load Tint32 Mf(bcount,0%Z)=Some(Vint32(Int.add c Int.one)) /\
 load Tint8 Mf(bc,0%Z)=Some(V293_byteval nc) /\
 (forall k,k<4 ->exists v,get Mf(bs,Z.of_nat k)=Some(true,v)) /\
 (forall block i,block<>bs ->block<>bo ->(block,i)<>(bh,0%Z) ->(block,i)<>(bn,0%Z) ->
   (block<>bcount \/(i<0)%Z \/(4<=i)%Z) ->get Mf(block,i)=get M(block,i)).
Proof.
 intros br bg bp P ks pc po pi ip T les aus cst interrupted ike interrupted_le ge caller M ir enabled si ci O op ct R tasks nc
 f sched_id unmap group rows high y table target nesting lock running saved current counter int_switch
 bt bh bo bn bl brun bc bcount c oldhigh oldtarget
 Merge Code Env Aux GoodKs Program Scheduler Names YU YG YR YH YT HP NT
 GU GG GR GH GT GO GN GL GRun GC GCount Map Current NotHighest Good Lookup Held.
 subst P.
 destruct(V293_OSIntExit_switch_entry_execution br bg bp(pumerge po pi)kstop
 ge caller M ir enabled si ci O op ct R tasks nc
 f sched_id unmap group rows high y table target nesting lock running saved current counter int_switch
 bt bh bo bn bl brun bc bcount c oldhigh oldtarget
 Program Scheduler Names YU YG YR YH YT HP NT
 GU GG GR GH GT GO GN GL GRun GC GCount Map Current NotHighest Good Lookup Held)
 as(bs&next&nh&Mf&Fresh&Different&PrioDifferent&Highest&Next&Trace&Post&Target&Count&Cache&Alive&Frame).
 pose proof(V293_interrupt_local_steps_global pc po pi ip _ _ _ _ Trace
 interrupted ike interrupted_le ks T les aus ct cst GoodKs)as Global.
 cbn[V293_enclose AddKsToTail]in Global.
 cbn[V293_local_global_at V293_global_at]in Global.
 assert(TStart:set T ct(curs(scall f nil),(kenil,kint interrupted ike interrupted_le ks))=T)
 by(apply get_set_same;exact Code).
 assert(EStart:set les ct caller=les)by(apply get_set_same;exact Env).
 assert(AStart:set aus ct(enabled,si,ci)=aus)by(apply get_set_same;exact Aux).
 assert(Start:(set T ct(curs(scall f nil),(kenil,kint interrupted ike interrupted_le ks)),
 (ge,set les ct caller,M,ir,set aus ct(enabled,si,ci)),ct)=(T,(ge,les,M,ir,aus),ct)).
 { rewrite TStart,EStart,AStart;reflexivity. }
 replace (T,(ge,les,M,ir,aus),ct) with
 (set T ct(curs(scall f nil),(kenil,kint interrupted ike interrupted_le ks)),
 (ge,set les ct caller,M,ir,set aus ct(enabled,si,ci)),ct) by exact Start.

 exists bs;exists next;exists nh;exists Mf;repeat first[assumption|split].
Qed.

(* Global rather than merely local dead end. A ready second task cannot run
   spontaneously, and disabled IE excludes lintstep. No claim for enabled IE. *)
Theorem V293_missing_port_disabled_no_global_step :
 forall pc po pi ip T cst ge les M ir aus t le si ci port args types ks,
 get T t=Some(curs(sfexec port args types),(kenil,ks)) ->
 get les t=Some le ->get aus t=Some(false,si,ci) ->
 InOS(curs(sfexec port args types),(kenil,ks))(pumerge po pi) ->
 pumerge po pi port=None ->
 ~exists T' cst' S' t',lpstep(pc,(po,pi,ip))T cst(ge,les,M,ir,aus)t T' cst' S' t'.
Proof.
 intros pc po pi ip T cst ge les M ir aus t le si ci port args types ks Code Env Aux Class Missing
 (T'&cst'&S'&t'&Step).
 change (@get tid code tasks TasksMap T t=Some(curs(sfexec port args types),(kenil,ks))) in Code.
 change (@get tid localst ltaskstset TaskLStMap aus t=Some(false,si,ci)) in Aux.
 assert(Project:projS(ge,les,M,ir,aus)t=Some((ge,le,M),ir,(false,si,ci))).
 { unfold projS,projD;rewrite Env,Aux;reflexivity. }
 inversion Step;subst;unfold code,taskst,localst,get,TasksMap in *;cbn in *;try congruence.
 all: match goal with H: _=Some ?C |- _=>
   is_var C;let ty:=type of C in unify ty code;assert(E:C=(curs(sfexec port args types),(kenil,ks)))by congruence;subst C
 end.
 all: match goal with H: _=Some ?st |- _=>
   is_var st;let ty:=type of st in unify ty taskst;
   assert(E:st=((ge,le,M),ir,(false,si,ci)))by congruence;subst st
 end.
 - match goal with H:lintstep _ _ _ _ _ |- _=>inversion H;discriminate end.
 - match goal with H:ltstep _ _ _ _ _ _ _ _ |- _=>inversion H;subst end;
   repeat match goal with H:(_,_) =(_,_) |- _=>inversion H;subst;clear H end.
   + match goal with H:~InOS _ _ |- _=>apply H;exact Class end.
   + eapply V293_missing_port_has_no_step;[exact Missing| ].
     eexists;eexists;eassumption.
Qed.
