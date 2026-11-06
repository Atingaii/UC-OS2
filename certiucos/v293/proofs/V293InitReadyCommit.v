(* Shared-ready ownership after genuine high-level task creation.
   This bridge does not establish whole caller simulation or startup reachability. *)
Require Import CertiOS.certiucos.v293.proofs.V293InitReadyPayload.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.certiucos.v293.proofs.V293NullBytes.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBClear.
Require Import CertiOS.certiucos.v293.proofs.V293CanonicalInitReturn.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.sep_combine_lemmas.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import Coq.Lists.List Coq.Sorting.Permutation.
Require Import CertiOS.certiucos.v293.proofs.V293InitPriorityTable.
Require Import CertiOS.certiucos.v293.proofs.V293InitPublishRecords.
Require Import CertiOS.certiucos.v293.proofs.V293PublishRecords.
Require Import CertiOS.certiucos.v293.proofs.V293InitAllRecords.
Require Import CertiOS.certiucos.v293.proofs.V293StartRecord.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFunction.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitEntry.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPriorityHook.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPublish.
Require Import CertiOS.certiucos.v293.proofs.V293TCBCallSuccess.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitPrefix.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitFunction.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Import ListNotations.
Local Open Scope nat_scope.

Lemma V293_init_shared_fields_from_slots : forall current tasks events now ge le ir aux O op,
 get O curtid=Some(oscurt current) -> get O abstcblsid=Some(abstcblist tasks) ->
 get O absecblsid=Some(absecblist events) -> get O ostmid=Some(ostm now) ->
 (ge,le,emp,ir,aux,O,op) |= V293_shared_fields current tasks events now.
Proof.
 intros current tasks events now ge le ir aux O op C T E N.
 assert(Exact:O=merge(sig curtid(oscurt current))
  (merge(sig abstcblsid(abstcblist tasks))
   (merge(sig absecblsid(absecblist events))(sig ostmid(ostm now))))).
 { apply OSAbstMod.extensionality. intro key. destruct key; simpl; assumption. }
 rewrite Exact. unfold V293_shared_fields.
 apply sat_split'. exists(emp:mem). exists(emp:mem). exists(sig curtid(oscurt current)). exists(merge(sig abstcblsid(abstcblist tasks))(merge(sig absecblsid(absecblist events))(sig ostmid(ostm now)))).
 split;[apply map_join_emp | ].
 split;[apply map_join_merge;apply map_disjoint;intros key;destruct key;simpl;auto | ].
 split;[split;reflexivity | ].
 apply sat_split'. exists(emp:mem). exists(emp:mem). exists(sig abstcblsid(abstcblist tasks)). exists(merge(sig absecblsid(absecblist events))(sig ostmid(ostm now))).
 split;[apply map_join_emp | ].
 split;[apply map_join_merge;apply map_disjoint;intros key;destruct key;simpl;auto | ].
 split;[split;reflexivity | ].
 apply sat_split'. exists(emp:mem). exists(emp:mem). exists(sig absecblsid(absecblist events)). exists(sig ostmid(ostm now)).
 split;[apply map_join_emp | ].
 split;[apply map_join_merge;apply map_disjoint;intros key;destruct key;simpl;auto | ].
 split;[split;reflexivity | ].
 split;reflexivity.
Qed.

Lemma V293_init_ready_physical_empty : forall br bg bp tasks current ge le M ir aux O op,
 (ge,le,M,ir,aux,O,op) |= V293_ready_payload br bg bp tasks ** CurTid current -> O=emp.
Proof.
 intros br bg bp tasks current ge le M ir aux O op Held.
 apply sat_split in Held. destruct Held as(mr&mc&orr&oc&JM&JO&Ready&Current).
 destruct(V293_current_fragment_local _ _ _ _ _ _ _ _ Current)as(b&tp&GE&EC&_).
 apply sat_split in Ready. destruct Ready as(mt&mb&ot&ob&JMR&JOR&Tasks&lo&hi&entries&Bytes).
 apply astar_l_apure_elim in Bytes. destruct Bytes as[_ Bytes].
 pose proof(V293_owned_cells_abstract_empty _ _ _ _ _ _ _ _ Bytes)as EB.
 destruct(V293_owned_task_list_local _ _ _ _ _ _ _ _ Tasks)as[ET _].
 subst ot ob oc. apply map_join_emp' in JOR. subst orr.
 apply map_join_emp' in JO. symmetry;exact JO.
Qed.

Lemma V293_init_raw_frame_drop : forall cells P,
 V293_rdy_raw_cells cells(P ** Atrue) ==> P ** Atrue.
Proof.
 induction cells as[ | [[a tp] v] cells IH];intros P s Held;cbn[V293_rdy_raw_cells]in Held.
 - exact Held.
 - eapply astar_mono in Held;[ |intros st H;exact H |apply IH]. clear -Held. sep auto.
Qed.

Lemma V293_init_ready_current_from_frame : forall br bg bp tasks current bc tp prefix suffix ge le M ir aux O op,
 get ge OSTCBCur=Some(bc,Tptr tp) ->
 (ge,le,M,ir,aux,O,op) |= V293_ready_payload br bg bp tasks **
 V293_rdy_raw_cells(prefix++((bc,0%Z),Tptr tp,Vptr current)::suffix) Atrue ->
 (ge,le,M,ir,aux,O,op) |= (V293_ready_payload br bg bp tasks ** CurTid current) ** Atrue.
Proof.
 intros br bg bp tasks current bc tp prefix suffix ge le M ir aux O op GE Held.
 apply V293_raw_cells_frame_in in Held.
 assert(Ordered:(ge,le,M,ir,aux,O,op) |=
  Amapsto(bc,0%Z)(Tptr tp)true(Vptr current) **
  V293_rdy_raw_cells(prefix++suffix)(V293_ready_payload br bg bp tasks ** Atrue)).
 { change((ge,le,M,ir,aux,O,op) |= V293_rdy_raw_cells
    (((bc,0%Z),Tptr tp,Vptr current)::(prefix++suffix))
    (V293_ready_payload br bg bp tasks ** Atrue)).
   eapply V293_raw_cells_permutation;[apply Permutation_sym,Permutation_middle |exact Held]. }
 assert(Named:(ge,le,emp,ir,aux,emp,op) |= (G&OSTCBCur@(Tptr tp)==(bc,Int.zero))).
 { exists bc. repeat split;assumption || reflexivity. }
 assert(Pack:(ge,le,M,ir,aux,O,op) |=
  (G&OSTCBCur@(Tptr tp)==(bc,Int.zero)) **
  (Amapsto(bc,0%Z)(Tptr tp)true(Vptr current) **
   V293_rdy_raw_cells(prefix++suffix)(V293_ready_payload br bg bp tasks ** Atrue))).
 { apply sat_split'. exists(emp:mem). exists M. exists(emp:osabst). exists O.
   split;[apply map_join_comm;apply map_join_emp | ].
   split;[apply map_join_comm;apply map_join_emp | ]. split;assumption. }
 assert(Full:(ge,le,M,ir,aux,O,op) |= (GV OSTCBCur@(Tptr tp)|->Vptr current) **
  V293_rdy_raw_cells(prefix++suffix)(V293_ready_payload br bg bp tasks ** Atrue)).
 { assert(Pair:(ge,le,M,ir,aux,O,op) |=
    ((G&OSTCBCur@(Tptr tp)==(bc,Int.zero)) **
     Amapsto(bc,0%Z)(Tptr tp)true(Vptr current)) **
    V293_rdy_raw_cells(prefix++suffix)(V293_ready_payload br bg bp tasks ** Atrue))
    by(clear -Pack;sep auto).
   eapply astar_mono;[ |intros st H;exact H |exact Pair].
   intros st H. unfold Agvarmapsto. exists bc. exact H. }
 eapply astar_mono in Full;[ |apply GV_separate_rw |intros st H;exact H].
 assert(Current:(ge,le,M,ir,aux,O,op) |= CurTid current **
  (V293_rdy_raw_cells(prefix++suffix)(V293_ready_payload br bg bp tasks ** Atrue) ** Atrue)).
 { unfold CurTid. clear -Full. sep auto. }

 assert(Framed:(ge,le,M,ir,aux,O,op) |= CurTid current ** (V293_ready_payload br bg bp tasks ** Atrue)).
 { eapply astar_mono;[intros st H;exact H | |exact Current].
   intros st H. eapply astar_mono in H;[ |apply V293_init_raw_frame_drop |intros st2 K;exact K].
   clear -H. sep auto. }
 clear -Framed. sep auto.
Qed.

Lemma V293_init_ready_shared_pack : forall br bg bp tasks current events now ge le M ir aux O O' op,
 get O' curtid=Some(oscurt current) -> get O' abstcblsid=Some(abstcblist tasks) ->
 get O' absecblsid=Some(absecblist events) -> get O' ostmid=Some(ostm now) ->
 (ge,le,M,ir,aux,O,op) |= (V293_ready_payload br bg bp tasks ** CurTid current) ** Atrue ->
 (ge,le,M,ir,aux,O',op) |= V293_shared_ready_records br bg bp current tasks events now ** Atrue.
Proof.
 intros br bg bp tasks current events now ge le M ir aux O O' op C T E N Held.
 apply sat_split in Held. destruct Held as(mp&mr&opart&orest&JM&JO&Physical&_).
 pose proof(V293_init_ready_physical_empty _ _ _ _ _ _ _ _ _ _ _ _ Physical)as Empty.
 subst opart.
 pose proof(V293_init_shared_fields_from_slots _ _ _ _ ge le ir aux O' op C T E N)as Fields.
 assert(Joint:(ge,le,M,ir,aux,O',op) |=
  ((V293_ready_payload br bg bp tasks ** CurTid current) **
   V293_shared_fields current tasks events now) ** Atrue).
 { apply sat_split'. exists mp. exists mr. exists O'. exists(emp:osabst).
   split;[exact JM | ]. split;[apply map_join_emp | ]. split;[ |exact I].
   apply sat_split'. exists mp. exists(emp:mem). exists(emp:osabst). exists O'.
   split;[apply map_join_emp | ]. split;[apply map_join_comm;apply map_join_emp | ]. split;assumption. }
 unfold V293_shared_ready_records. clear -Joint. sep auto.
Qed.

(* A real client function: one pointer argument, no local variables, arbitrary
   body. Its allocation and argument store are constructed, not presumed. *)
Lemma V293_init_client_allocate : forall pc f tau arg body ge M b v,
 pc f=Some(tau,dcons arg(Tptr Tvoid)dnil,dnil,body) -> fresh M b ->
 type_val_match(Tptr Tvoid)v=true ->
 exists M', store(Tptr Tvoid)(allocb M b 0%Z(typelen(Tptr Tvoid)))(b,0%Z)v=Some M' /\
 load(Tptr Tvoid)M'(b,0%Z)=Some v /\
 cstepstar pc (curs(sfexec f [v] [Tptr Tvoid]),(kenil,kstop)) (ge,emp,M)
 (curs body,(kenil,kcall f body emp kstop)) (ge,set emp arg(b,Tptr Tvoid),M').
Proof.
 intros pc f tau arg body ge M b v Program Fresh Valid.
 pose proof(V293_tick_allocate_frame ge (emp:env) M (fun _=>false) (false,[],[])
  (emp:osabst)(spec_done None)b(Tptr Tvoid)Atrue Fresh I)as Owned.
 apply sat_split in Owned. destruct Owned as(part&rest&o1&o2&JM&JO&[Bytes Empty]&Frame).
 destruct(store_exist_join' _ _ _ v _ _ _ Bytes JM)as(M'&Store).
 exists M'. split;[exact Store | ]. split.
 - destruct(store_mapstoval_frame1 _ _ _ _ _ _ _ _ Bytes JM Store)as(part'&Bytes'&Local&Joined).
   eapply load_mem_mono;[ |exists rest;exact Joined].
   eapply mapstoval_load;[ |exact Bytes'].
   destruct v;simpl in Valid |- *;try discriminate;reflexivity.
 - eapply c_stepstarn.
 { eapply stmt_step;[reflexivity | ].
   eapply sfexec_step with(d1:=dcons arg(Tptr Tvoid)dnil)(d2:=dnil);
    [reflexivity |reflexivity |exact Program |split;[exact I |reflexivity] | ].
   cbn[tl_vl_match]. rewrite Valid. reflexivity. }
 eapply c_stepstarn.
 { eapply stmt_step;[reflexivity | ]. eapply sallocp_step with(b:=b);
    [reflexivity |reflexivity | |apply map_get_set |exact Store].
   exists b. repeat split;try reflexivity;try assumption.
   intros[x Lookup]. rewrite map_emp_get in Lookup. discriminate. }
 eapply c_stepstarn;[eapply stmt_step;[reflexivity |apply sallocend_step] |apply c_stepstar0].
Qed.

Theorem V293_init_ready_create_commit :
 forall br bg bp tasks current new events now ge le M ir aux O op
 pc A T cenvs clientM b f tau arg body entry argument priority ke ks rest bc tp prefix suffix,
 get O curtid=Some(oscurt current) -> get O abstcblsid=Some(abstcblist tasks) ->
 get O absecblsid=Some(absecblist events) -> get O ostmid=Some(ostm now) ->
 get tasks new=None -> new<>current -> get T new=None -> get cenvs new=None ->
 get T current=Some(curs(hapi_code(spec_seq(spec_crt entry argument(Vint32 priority))rest)),(ke,ks)) ->
 vtoZ entry=Some f -> pc f=Some(tau,dcons arg(Tptr Tvoid)dnil,dnil,body) ->
 fresh clientM b -> type_val_match(Tptr Tvoid)argument=true ->
 get ge OSTCBCur=Some(bc,Tptr tp) ->
 (ge,le,M,ir,aux,O,op) |= V293_ready_payload br bg bp(set tasks new(priority,rdy,Vnull)) **
  V293_rdy_raw_cells(prefix++((bc,0%Z),Tptr tp,Vptr current)::suffix)Atrue ->
 exists clientM',
 let O':=set O abstcblsid(abstcblist(set tasks new(priority,rdy,Vnull))) in
 let T':=set(set T current(curs(hapi_code rest),(ke,ks)))new(nilcont body) in
 let cenvs':=set cenvs new(set emp arg(b,Tptr Tvoid)) in
 hpstep(pc,A)T(ge,cenvs,clientM)O T'(ge,cenvs',clientM')O' /\
 get T' new=Some(nilcont body) /\ get T' current=Some(curs(hapi_code rest),(ke,ks)) /\
 get cenvs' new=Some(set emp arg(b,Tptr Tvoid)) /\
 load(Tptr Tvoid)clientM'(b,0%Z)=Some argument /\
 (ge,le,M,ir,aux,O',op) |=
  V293_shared_ready_records br bg bp current(set tasks new(priority,rdy,Vnull))events now ** Atrue /\
 (ge,le,M,ir,aux,O',op) |= V293_ready_core br bg bp ** Atrue.
Proof.
 intros br bg bp tasks current new events now ge le M ir aux O op pc A T cenvs clientM b f tau arg
 body entry argument priority ke ks rest bc tp prefix suffix C Tasks Events Clock Fresh NewCurrent
 NewCode NewEnv Caller Entry Program FreshBlock Valid GE Physical.
 destruct(V293_init_client_allocate pc f tau arg body ge clientM b argument Program FreshBlock Valid)
  as(clientM'&Store&Read&Allocation).
 exists clientM'. cbn zeta.
 assert(Join:TcbMod.join tasks(sig new(priority,rdy,Vnull))(set tasks new(priority,rdy,Vnull))).
 { apply TcbMod.join_sig_set. intros[v Lookup]. change(TcbMod.get tasks new=Some v)in Lookup. change(TcbMod.get tasks new=None)in Fresh. congruence. }
 split.
 - eapply hpcrt_step with(t:=current)(t':=new)(f:=f)(tls:=tasks)
    (tls':=set tasks new(priority,rdy,Vnull))(tau:=tau)
    (d1:=dcons arg(Tptr Tvoid)dnil)(d2:=dnil)(s:=body)(le:=set emp arg(b,Tptr Tvoid));
    try reflexivity;try eassumption.
 - split;[apply map_get_set | ]. split.
   + rewrite map_get_set' by congruence. apply map_get_set.
   + split;[apply map_get_set | ]. split.
     * exact Read.
     * assert(Shared:(ge,le,M,ir,aux,set O abstcblsid
        (abstcblist(set tasks new(priority,rdy,Vnull))),op) |=
        V293_shared_ready_records br bg bp current(set tasks new(priority,rdy,Vnull))events now ** Atrue).
       { eapply V293_init_ready_shared_pack with(O:=O).
         - rewrite map_get_set' by discriminate. exact C.
         - apply map_get_set.
         - rewrite map_get_set' by discriminate. exact Events.
         - rewrite map_get_set' by discriminate. exact Clock.
         - eapply V293_init_ready_current_from_frame;[exact GE |exact Physical]. }
       split;[exact Shared | ].
       eapply astar_mono;[ |intros st H;exact H |exact Shared].
       intros st H. exists current. exists(set tasks new(priority,rdy,Vnull)). exists events. exists now. exact H.
Qed.

(* Same physical heap and witnesses; only abstract task insertion is removed. *)
Theorem V293_init_ready_stale_commit_rejected : forall br bg bp tasks current new priority events now s,
 get tasks new=None -> get(getabst s)abstcblsid=Some(abstcblist tasks) ->
 ~s |= V293_shared_ready_records br bg bp current(set tasks new(priority,rdy,Vnull))events now ** Atrue.
Proof.
 intros br bg bp tasks current new priority events now s Fresh Old Shared.
 assert(Updated:get(getabst s)abstcblsid=Some(abstcblist(set tasks new(priority,rdy,Vnull)))).
 { eapply V293_star_abst_get_l;[ |exact Shared].
   intros st Held. exact(proj1(proj2(V293_shared_fields_core_get _ _ _ _ _ _ Held))). }
 rewrite Old in Updated. injection Updated as Equal.
 assert(Lookup:get tasks new=Some(priority,rdy,Vnull)).
 { rewrite Equal. apply map_get_set. }
 change(TcbMod.get tasks new=None)in Fresh.
 change(TcbMod.get tasks new=Some(priority,rdy,Vnull))in Lookup. congruence.
Qed.

Theorem V293_init_insert_not_ordinary_primitive : forall O tasks new priority,
 get O abstcblsid=Some(abstcblist tasks) -> get tasks new=None ->
 ~eqdomO O(set O abstcblsid(abstcblist(set tasks new(priority,rdy,Vnull)))).
Proof.
 intros O tasks new priority Old Fresh [_ Domains].
 destruct(Domains tasks Old)as(tasks'&Updated&Same).
 rewrite map_get_set in Updated. injection Updated as Equal. subst tasks'.
 assert(New:indom(set tasks new(priority,rdy,Vnull))new).
 { exists(priority,rdy,Vnull). apply map_get_set. }
 apply(proj2(Same new))in New. destruct New as[v Lookup].
 change(TcbMod.get tasks new=None)in Fresh.
 change(TcbMod.get tasks new=Some v)in Lookup. congruence.
Qed.

(* Conditional source return and allocating abstract creation share the exact Mf. *)
Theorem V293_OS_TCBInit_shared_return_under_hooks :
 forall entries tasks lo0 hi0 P f hi hc caller ks ge M ir aux O op enabled si ci
 b1 b2 b3 b4 b5 b6 b7 b8 b9 bf table bt base bh bg br bn bo obase present p n
 top bottom identity size ext options pc next old prev back restframe current events now bc tp hpc A T cenvs clientM freshb
 clientf tau arg body entry argument ke hks rest,
 let frame:=((bc,0%Z),Tptr tp,Vptr current)::restframe in
 let g:=V293_ready_group lo0 hi0 in
 let r:=V293_ready_row lo0 hi0 (V293_prio_row p) in
 let le:=V293_tcb_function_env b1 b2 b3 b4 b5 b6 b7 b8 b9 in
 let blocks:=V293_tcb_function_blocks b1 b2 b3 b4 b5 b6 b7 b8 b9 in
 let tasks':=set tasks (bt,Int.repr base) (Int.repr(Z.of_nat p),rdy,Vnull) in
 let extra:=V293_priority_hole entries table 0%Z p++V293_init_other_row br lo0 hi0 p::frame in
 let tail:=V293_tcb_creation_tail bt base bh bg br bn bo obase present p prev g r n back++extra in
 let survivors:=V293_tcb_init_record_remainder bt base top bottom identity size ext options++
  [((bf,0%Z),Tptr V293_tcb_type,next);((table,(4*Z.of_nat p)%Z),Tptr V293_tcb_type,Vptr(bt,Int.repr base))]++extra in
 let after:=V293_pub_link_cells b8 bt base bh bg br bn bo obase present p
  (V293_pub_old_head present bo obase) Vnull (Vptr(bt,Int.repr base))
  (Nat.setbit g (V293_prio_row p)) (Nat.setbit r (V293_prio_bit p)) (S n) (Vptr(bt,Int.repr base)) in
 get O curtid=Some(oscurt current) -> get O abstcblsid=Some(abstcblist tasks) ->
 get O absecblsid=Some(absecblist events) -> get O ostmid=Some(ostm now) ->
 (bt,Int.repr base)<>current -> get T (bt,Int.repr base)=None ->
 get cenvs (bt,Int.repr base)=None ->
 get T current=Some(curs(hapi_code(spec_seq(spec_crt entry argument(Vint32(Int.repr(Z.of_nat p))))rest)),(ke,hks)) ->
 vtoZ entry=Some clientf -> hpc clientf=Some(tau,dcons arg(Tptr Tvoid)dnil,dnil,body) ->
 fresh clientM freshb -> type_val_match(Tptr Tvoid)argument=true ->
 get ge OSTCBCur=Some(bc,Tptr tp) ->
 lo0<256 -> hi0<256 -> V293_bitmap_tasks lo0 hi0 tasks ->
 V293_init_priority_table entries tasks -> nth p entries Vnull=Vnull ->
 get ge 91%Z=Some(bf,Tptr V293_tcb_type) -> get ge 92%Z=Some(table,Tarray(Tptr V293_tcb_type) 13) ->
 V293_pub_env ge le 108%Z 93%Z 94%Z 95%Z 96%Z b8 bh bg br bn ->
 get tasks (bt,Int.repr base)=None -> p<13 -> NoDup blocks ->
 (0<=base)%Z -> (base+55<=Int.max_unsigned)%Z ->
 (0<=obase)%Z -> (obase+24<=Int.max_unsigned)%Z -> n<255 ->
 V293_tcb_init_values_valid top bottom identity size ext options ->
 rule_type_val_match (Tptr V293_tcb_type) next=true ->
 (forall t value, In (t,value) (TcbMod.lst tasks') -> ~In (fst t) blocks) ->
 (forall a tp v, In (a,tp,v) (tl after++survivors) -> ~In (fst a) blocks) ->
 V293_records_hook_return tasks' P hi bt base (V293_tcb_first_hook_cont f hi hc caller ks)
  ge le ir aux O op enabled si ci
  (V293_record_hook_cells b1 b2 b3 b4 b5 b6 b7 b8 b9 bf table bt base p
   top bottom identity size ext options next Vnull tail) ->
 V293_records_hook_return tasks' P hc bt base (V293_tcb_second_hook_cont f hi hc caller ks)
  ge le ir aux O op enabled si ci
  (V293_record_hook_cells b1 b2 b3 b4 b5 b6 b7 b8 b9 bf table bt base p
   top bottom identity size ext options next (Vptr(bt,Int.repr base)) tail) ->
 (ge,le,M,ir,aux,O,op)  |= V293_rdy_raw_cells
  (V293_tcb_init_old_fields bt base old ++
   V293_tcb_prefix_inputs b8 b1 b2 b3 b4 b5 b6 b7 pc p top bottom identity size ext options ++
   V293_tcb_prefix_links bf bt base (Vptr(bt,Int.repr base)) next ++
   ((b9,0%Z),Tint32,Vint32 Int.zero)::((table,(4*Z.of_nat p)%Z),Tptr V293_tcb_type,Vnull)::tail)
  (V293_owned_task_records tasks ** Atrue) ->
 exists Mf clientM',

 V293_local_steps P
  (curs(V293_TCBInit_prefix 91%Z 108%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z
   (V293_TCBInit_success_suffix hi hc)),(kenil,kcall f (V293_TCBInit_function_body hi hc) caller ks))
  ((ge,le,M),ir,(enabled,si,ci))
  (curs(sskip(Some(Vint32 Int.zero))),(kenil,ks)) ((ge,caller,Mf),ir,(enabled,si,ci)) /\
 hpstep(hpc,A) T(ge,cenvs,clientM)O
  (set(set T current(curs(hapi_code rest),(ke,hks)))(bt,Int.repr base)(nilcont body))
  (ge,set cenvs(bt,Int.repr base)(set emp arg(freshb,Tptr Tvoid)),clientM')
  (set O abstcblsid(abstcblist tasks')) /\
 load(Tptr Tvoid)clientM'(freshb,0%Z)=Some argument /\
 (ge,caller,Mf,ir,aux,set O abstcblsid(abstcblist tasks'),op) |=
  V293_shared_ready_records br bg table current tasks' events now ** Atrue /\
 (ge,caller,Mf,ir,aux,set O abstcblsid(abstcblist tasks'),op) |= V293_ready_core br bg table ** Atrue /\
 ~(ge,caller,Mf,ir,aux,O,op) |=
  V293_shared_ready_records br bg table current tasks' events now ** Atrue.
Proof.
 intros entries tasks lo0 hi0 P f hi hc caller ks ge M ir aux O op enabled si ci
 b1 b2 b3 b4 b5 b6 b7 b8 b9 bf table bt base bh bg br bn bo obase present p n
 top bottom identity size ext options pc next old prev back restframe current events now bc tp hpc A T cenvs clientM freshb
 clientf tau arg body entry argument ke hks rest frame
 g r le blocks tasks' extra tail survivors after C Tasks Events Clock NewCurrent NewCode NewEnv
 Caller EntryPoint Program FreshBlock Argument CurrentGlobal
 Low High Bitmap Canonical Null FreeGlobal TableGlobal PubEnv Fresh Range ND Base Bound
 OldBase OldBound Count Valid Next TasksAway CellsAway Hook1 Hook2 Entry.
 destruct(V293_OS_TCBInit_ready_return_under_hooks entries tasks lo0 hi0 P f hi hc caller ks ge M ir aux O op
 enabled si ci b1 b2 b3 b4 b5 b6 b7 b8 b9 bf table bt base bh bg br bn bo obase present p n
 top bottom identity size ext options pc next old prev back frame
 Low High Bitmap Canonical Null FreeGlobal TableGlobal PubEnv Fresh Range ND Base Bound OldBase OldBound Count Valid Next
 TasksAway CellsAway Hook1 Hook2 Entry)as(Mf&Exec&Final&Freed&NewCanonical&Payload).
 set(prefix:=[((bt,(base+20)%Z),Tcom_ptr 410%Z,V293_pub_old_head present bo obase);
  ((bt,(base+24)%Z),Tcom_ptr 410%Z,Vnull);
  ((bh,0%Z),Tptr V293_tcb_type,Vptr(bt,Int.repr base))]++
  [((bn,0%Z),Tint8,V293_byteval(S n))]++
  (if present then [((bo,(obase+24)%Z),Tcom_ptr 410%Z,Vptr(bt,Int.repr base))] else [])++
  V293_tcb_init_record_remainder bt base top bottom identity size ext options++
  [((bf,0%Z),Tptr V293_tcb_type,next)]).
 assert(Physical:(ge,caller,Mf,ir,aux,O,op) |= V293_ready_payload br bg table tasks' **
   V293_rdy_raw_cells(prefix++((bc,0%Z),Tptr tp,Vptr current)::restframe) Atrue).
 { unfold prefix,frame. repeat rewrite <-app_assoc. exact Payload. }
 destruct(V293_init_ready_create_commit br bg table tasks current(bt,Int.repr base)events now
 ge caller Mf ir aux O op hpc A T cenvs clientM freshb clientf tau arg body entry argument
 (Int.repr(Z.of_nat p)) ke hks rest bc tp prefix restframe C Tasks Events Clock Fresh
 NewCurrent NewCode NewEnv Caller EntryPoint Program FreshBlock Argument CurrentGlobal Physical)
 as(clientM'&Commit&NewControl&CurrentControl&NewEnvironment&Read&Shared&Core).
 exists Mf. exists clientM'. split;[exact Exec | ]. split;[exact Commit | ].
 split;[exact Read | ]. split;[exact Shared | ]. split;[exact Core | ].
 eapply V293_init_ready_stale_commit_rejected;[exact Fresh |exact Tasks].
Qed.

Print Assumptions V293_init_shared_fields_from_slots.
Print Assumptions V293_init_ready_physical_empty.
Print Assumptions V293_init_raw_frame_drop.
Print Assumptions V293_init_ready_current_from_frame.
Print Assumptions V293_init_ready_shared_pack.
Print Assumptions V293_init_client_allocate.
Print Assumptions V293_init_ready_create_commit.
Print Assumptions V293_init_ready_stale_commit_rejected.
Print Assumptions V293_init_insert_not_ordinary_primitive.
Print Assumptions V293_OS_TCBInit_shared_return_under_hooks.
