(* Shared-resource reclosure AFTER the real source-boundary switch.
   The copy/switch transient is unchanged. Cache correctness is reported
   separately because the current invariant permits its highest arm. *)
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBoundarySwitch.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCurrentInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyStorageInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchState.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCacheContract.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyFullCall.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrent.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyGlobalTrace.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition V293_exit_shared_cells bh bn bl bc brun bk rest : list(addr*type) :=
 [((bh,0%Z),Tint8);((bn,0%Z),Tint8);((bl,0%Z),Tint8);
  ((bc,0%Z),Tint8);((brun,0%Z),Tint8);((bk,0%Z),Tint32)]++rest.

Lemma V293_exit_cell_to_storage : forall a tau v,
 V293_owned_record_cell(a,tau,v) ==> V293_storage_cell a tau.
Proof.
 intros a tau v st Held;exists v;exact Held.
Qed.

Lemma V293_exit_shared_reclose :
 forall br bg bp target bh bo bn bl bc brun bk rest
 ge le M ir aux O op t tasks nh cache c R,
 get ge target=Some(bo,Tptr V293_tcb_type) ->
 get O abstcblsid=Some(abstcblist tasks) ->V293_highest_ready tasks t ->
 (ge,le,M,ir,aux,O,op)|=SWINVt(V293_ready_inv br bg bp)t **
 (V293_owned_record_cell((bh,0%Z),Tint8,V293_byteval nh) **
 (V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,Vptr t) **
 (V293_owned_record_cell((bn,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((bl,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval cache) **
 (V293_owned_record_cell((brun,0%Z),Tint8,V293_byteval 1) **
 (V293_owned_record_cell((bk,0%Z),Tint32,Vint32 c) **
 (V293_storage rest **R)))))))) ->
 (ge,le,M,ir,aux,O,op)|=
 SWINVt(V293_ready_current_inv br bg bp target V293_tcb_type
 (V293_exit_shared_cells bh bn bl bc brun bk rest)bc)t **R.
Proof.
 intros br bg bp target bh bo bn bl bc brun bk rest
 ge le M ir aux O op t tasks nh cache c R Target Map Highest Held.
 assert(Storage: V293_owned_record_cell((bh,0%Z),Tint8,V293_byteval nh) **
 (V293_owned_record_cell((bn,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((bl,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval cache) **
 (V293_owned_record_cell((brun,0%Z),Tint8,V293_byteval 1) **
 (V293_owned_record_cell((bk,0%Z),Tint32,Vint32 c) **V293_storage rest))))) ==>
 V293_storage(V293_exit_shared_cells bh bn bl bc brun bk rest)).
 { unfold V293_exit_shared_cells;cbn[V293_storage].
   repeat apply astar_mono;try(intros st H;exact H);
   apply V293_exit_cell_to_storage. }
 assert(Global:forall m o,
 (ge,le,m,ir,aux,o,op)|=V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,Vptr t) ->
 (ge,le,m,ir,aux,o,op)|=V293_dispatch_cell target V293_tcb_type).
 { intros m o H;unfold V293_dispatch_cell.
   apply astar_l_apure_elim in H;destruct H as[_ H].
   exists(Vptr t);apply astar_l_apure_intro;[ |reflexivity].
   exists bo;unfold Agvarenv',Aptrmapsto;cbn[addrval_to_addr].
   apply astar_l_agvarenv_intro;[exact H|split;[reflexivity|exact Target]]. }
 assert(Closed:(ge,le,M,ir,aux,O,op)|=
 SWINVt(V293_ready_storage_inv br bg bp target V293_tcb_type
 (V293_exit_shared_cells bh bn bl bc brun bk rest))t **R).
 { eapply astar_mono;[intros st H;apply V293_ready_storage_switch_resources;exact H|intros st H;exact H| ].
   assert(Parts:(ge,le,M,ir,aux,O,op)|=
 (V293_owned_record_cell((bh,0%Z),Tint8,V293_byteval nh) **
 (V293_owned_record_cell((bn,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((bl,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval cache) **
 (V293_owned_record_cell((brun,0%Z),Tint8,V293_byteval 1) **
 (V293_owned_record_cell((bk,0%Z),Tint32,Vint32 c) **V293_storage rest)))))) **
 (V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,Vptr t) **
 (SWINVt(V293_ready_inv br bg bp)t **R)))by(sep auto).
   eapply astar_mono in Parts;[ |exact Storage|intros st H;exact H].
   apply sat_split in Parts;destruct Parts as(ma&mb&oa&ob&JMa&JOa&Store&Parts).
   apply sat_split in Parts;destruct Parts as(mt&mr&ot&orr&JMb&JOb&Cell&Rest).
   apply Global in Cell.
   assert(Parts:(ge,le,M,ir,aux,O,op)|=
   V293_storage(V293_exit_shared_cells bh bn bl bc brun bk rest) **
   (V293_dispatch_cell target V293_tcb_type ** (SWINVt(V293_ready_inv br bg bp)t **R))).
   { apply sat_split';exists ma;exists mb;exists oa;exists ob.
     split;[exact JMa| ];split;[exact JOa| ];split;[exact Store| ].
     apply sat_split';exists mt;exists mr;exists ot;exists orr.
     split;[exact JMb| ];split;[exact JOb| ];split;assumption. }
   unfold V293_ready_storage_extra;clear Held;sep auto. }
 apply sat_split in Closed;destruct Closed as(m1&m2&o1&o2&JM&JO&Shared&Private).
 assert(Current:get o1 curtid=Some(oscurt t)).
 { destruct(V293_ready_storage_good br bg bp target V293_tcb_type
   (V293_exit_shared_cells bh bn bl bc brun bk rest))as[_[Read _]].
   destruct(Read _ _ _ _ Shared)as(b&tq&envBound&loaded&currentBound);exact currentBound. }
 assert(Fields:(ge,le,m1,ir,aux,o1,op)|=V293_shared_core ** Atrue).
 { unfold SWINVt in Shared;eapply astar_mono in Shared;
   [ |apply V293_ready_storage_switch_open|intros st H;exact H].
   unfold V293_ready_storage_core,V293_ready_core,V293_shared_ready_records,V293_shared_core in *;
   sep normal in Shared;sep destruct Shared;sep auto. }
 assert(Empty:o2=emp)by(eapply V293_shared_no_abstract_frame;[exact Fields|exact JO]).
 subst o2;apply map_join_emp' in JO;subst o1.
 apply sat_split';exists m1;exists m2;exists O;exists(emp:osabst).
 split;[exact JM| ];split;[apply map_join_emp| ];split;[ |exact Private].
 eapply V293_current_switch_highest;[exact Shared| ].
 exists t;split;[exact Current| ];exists tasks;split;assumption.
Qed.

Theorem V293_exit_boundary_shared_reclose :
 forall (sync:bool) br bg bp P ks pc po pi ip T les aus cst interrupted ike interrupted_le ge caller M ir enabled si ci O op ct rest R tasks nc
 f sched_id unmap group rows high y table target nesting lock running saved current counter
 bt bh bo bn bl brun bc bcount c oldhigh oldtarget bcur,
 P=pumerge po pi ->
 get T ct=Some(curs(scall f nil),(kenil,kint interrupted ike interrupted_le ks)) ->
 get les ct=Some caller ->get aus ct=Some(enabled,si,ci) ->
 goodks(pc,(po,pi,ip))ks ->
 P f=Some(V293_exit_boundary_function running nesting lock saved table high target current counter sched_id (if sync then V293_interrupt_handoff high current target else sprim(switch target))) ->
 P sched_id=Some(V293_OSSchedNew_function unmap group rows high y) ->
 ~In saved [unmap;group;rows;high;table;target;nesting;lock;running;current;counter] ->
 y<>unmap ->y<>group ->y<>rows ->y<>high ->y<>table ->bh<>bp ->bn<>bt ->
 get ge unmap=Some(bt,Tarray Tint8 256) ->get ge group=Some(bg,Tint8) ->
 get ge rows=Some(br,Tarray Tint8 2) ->get ge high=Some(bh,Tint8) ->
 get ge table=Some(bp,Tarray(Tptr V293_tcb_type)13) ->get ge target=Some(bo,Tptr V293_tcb_type) ->
 get ge nesting=Some(bn,Tint8) ->get ge lock=Some(bl,Tint8) ->
 get ge running=Some(brun,Tint8) ->get ge current=Some(bc,Tint8) ->get ge counter=Some(bcount,Tint32) ->
 get ge OSTCBCur=Some(bcur,Tptr V293_tcb_type) ->
 (forall t pr st msg,get tasks t=Some(pr,st,msg) ->
   exists C le aux,get T t=Some C /\ get les t=Some le /\ get aus t=Some aux) ->
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
 (V293_owned_record_cell((bcount,0%Z),Tint32,Vint32 c) **(V293_storage rest **R)))))))) ->
 exists bs next nh Me Ms Mf,fresh M bs /\ next<>ct /\ nh<>nc /\
 V293_highest_ready tasks next /\V293_current_task tasks next nh /\
 V293_global_steps(pc,(po,pi,ip))cst
 (T,(ge,les,M,ir,aus),ct)
 (set T ct(SKIP,(kenil,
   kseq(sprim excrit)(kseq sret(kcall f
     (V293_exit_boundary_body running nesting lock saved table high target current counter sched_id
       (if sync then V293_interrupt_handoff high current target else sprim(switch target)))
       caller(kint interrupted ike interrupted_le ks))))),
  (ge,set les ct(V293_cpu_lenv saved bs),Mf,ir,set aus ct(false,si,enabled::ci)),next) /\
 (ge,V293_cpu_lenv saved bs,Mf,ir,(false,si,enabled::ci),set O curtid(oscurt next),op)|=
 SWINVt(V293_ready_current_inv br bg bp target V293_tcb_type
   (V293_exit_shared_cells bh bn bl bc brun bcount rest)bc)next **
 (Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **R) /\
 load(Tptr V293_tcb_type)Mf(bcur,0%Z)=Some(Vptr next) /\
 load Tint8 Mf(bc,0%Z)=Some(V293_byteval(if sync then nh else nc)) /\
 load Tint32 Mf(bcount,0%Z)=Some(Vint32(Int.add c Int.one)) /\
 (forall k,k<4 ->exists v,get Mf(bs,Z.of_nat k)=Some(true,v)) /\
 (V293_cache_current tasks next Mf bc <-> sync=true) /\
 (sync=true ->store Tint8 Me(bc,0%Z)(V293_byteval nh)=Some Ms) /\
 store(Tptr V293_tcb_type)Ms(bcur,0%Z)(Vptr next)=Some Mf /\
 (exists C le aux,get T next=Some C /\get les next=Some le /\get aus next=Some aux /\
   get(set T ct(SKIP,(kenil,kseq(sprim excrit)(kseq sret(kcall f
     (V293_exit_boundary_body running nesting lock saved table high target current counter sched_id
       (if sync then V293_interrupt_handoff high current target else sprim(switch target)))
       caller(kint interrupted ike interrupted_le ks))))))next=Some C /\
   get(set les ct(V293_cpu_lenv saved bs))next=Some le /\
   get(set aus ct(false,si,enabled::ci))next=Some aux).

Proof.
 intros sync br bg bp P ks pc po pi ip T les aus cst interrupted ike interrupted_le ge caller M ir enabled si ci O op ct rest R tasks nc
 f sched_id unmap group rows high y table target nesting lock running saved current counter
 bt bh bo bn bl brun bc bcount c oldhigh oldtarget bcur
 Merge Code Env Aux GoodKs Program Scheduler Names YU YG YR YH YT HP NT
 GU GG GR GH GT GO GN GL GRun GC GCount GCur Domain Map Current NotHighest Good Lookup Held.
 destruct(V293_OSIntExit_boundary_switch sync br bg bp P ks pc po pi ip T les aus cst
 interrupted ike interrupted_le ge caller M ir enabled si ci O op ct (V293_storage rest **R) tasks nc
 f sched_id unmap group rows high y table target nesting lock running saved current counter
 bt bh bo bn bl brun bc bcount c oldhigh oldtarget bcur
 Merge Code Env Aux GoodKs Program Scheduler Names YU YG YR YH YT HP NT
 GU GG GR GH GT GO GN GL GRun GC GCount GCur Domain Map Current NotHighest
 (conj(V293_storage_good rest)Good)Lookup Held)
 as(bs&next&nh&Me&Ms&Mf&Fresh&Different&PrioDifferent&Highest&Next&Steps&Post&Pointer&Cache&Count&Alive&Coherence&Copy&Switch&Target).
 assert(Reclosed:(ge,V293_cpu_lenv saved bs,Mf,ir,(false,si,enabled::ci),
 set O curtid(oscurt next),op)|=
 SWINVt(V293_ready_current_inv br bg bp target V293_tcb_type
   (V293_exit_shared_cells bh bn bl bc brun bcount rest)bc)next **
 (Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **R)).
 { eapply V293_exit_shared_reclose with(bo:=bo)(tasks:=tasks)
   (nh:=nh)(cache:=if sync then nh else nc)(c:=Int.add c Int.one).
 - exact GO.
 - rewrite map_get_set' by discriminate;exact Map.
 - exact Highest.
 - clear Held;sep auto. }
 exists bs;exists next;exists nh;exists Me;exists Ms;exists Mf.
 repeat first[assumption|split].
Qed.
