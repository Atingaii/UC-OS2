(* Real function entry composed with the original shared-ready creation bridge.
   The two CPU hooks remain explicit implementation obligations. *)
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
Require Import CertiOS.certiucos.v293.proofs.V293InitReadyCommit.
Require Import CertiOS.certiucos.v293.proofs.V293CallRecords.
Require Import Lia.
Import ListNotations.
Local Open Scope nat_scope.

Theorem V293_OS_TCBInit_call_shared_return_under_hooks :
 forall entries tasks lo0 hi0 P f hi hc caller ks ge M ir aux O op enabled si ci
 b1 b2 b3 b4 b5 b6 b7 b8 b9 bf table bt base bh bg br bn bo obase present p n
 top bottom identity size ext options next old prev back restframe current events now bc tp hpc A T cenvs clientM freshb
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
 P f=Some(V293_TCBInit_function hi hc) ->
 (forall b, In b blocks -> fresh M b) ->
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
 (ge,caller,M,ir,aux,O,op) |= V293_rdy_raw_cells
  (V293_tcb_init_old_fields bt base old ++
   V293_tcb_prefix_links bf bt base (Vptr(bt,Int.repr base)) next ++
   ((table,(4*Z.of_nat p)%Z),Tptr V293_tcb_type,Vnull)::tail)
  (V293_owned_task_records tasks ** Atrue) ->
 exists Mf clientM',

 V293_local_steps P
  (curs(sfexec f [options;ext;size;identity;bottom;top;V293_byteval p]
   V293_TCBInit_argument_types),(kenil,ks)) ((ge,caller,M),ir,(enabled,si,ci))
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
 top bottom identity size ext options next old prev back restframe current events now bc tp hpc A T cenvs clientM freshb
 clientf tau arg body entry argument ke hks rest frame
 g r le blocks tasks' extra tail survivors after Function LocalsFresh C Tasks Events Clock NewCurrent NewCode NewEnv
 Caller EntryPoint Program FreshBlock Argument CurrentGlobal
 Low High Bitmap Canonical Null FreeGlobal TableGlobal PubEnv Fresh Range ND Base Bound
 OldBase OldBound Count Valid Next TasksAway CellsAway Hook1 Hook2 Entry.
 assert (Values : V293_tcb_function_values_valid (V293_byteval p) top bottom identity size ext options).
 { unfold V293_tcb_function_values_valid. unfold V293_tcb_init_values_valid in Valid.
   split;[apply V293_byte_type;lia |exact Valid]. }
 apply V293_raw_cells_move_frame in Entry.
 destruct (V293_tcb_call_prologue_records tasks P ks ge caller M ir aux O op enabled si ci f hi hc
  b1 b2 b3 b4 b5 b6 b7 b8 b9 (V293_byteval p) top bottom identity size ext options _
  Function ND LocalsFresh Values Entry) as (Mi&Prologue&Allocated).
 assert (PrefixEntry : (ge,le,Mi,ir,aux,O,op) |= V293_rdy_raw_cells
  (V293_tcb_init_old_fields bt base old ++
   V293_tcb_prefix_inputs b8 b1 b2 b3 b4 b5 b6 b7 Vundef p top bottom identity size ext options ++
   V293_tcb_prefix_links bf bt base (Vptr(bt,Int.repr base)) next ++
   ((b9,0%Z),Tint32,Vint32 Int.zero)::((table,(4*Z.of_nat p)%Z),Tptr V293_tcb_type,Vnull)::tail)
  (V293_owned_task_records tasks ** Atrue)).
 { unfold le,V293_tcb_function_cells,V293_tcb_prefix_inputs,V293_tcb_init_input_cells,
   V293_tcb_init_old_fields,V293_tcb_prefix_links in Allocated |- *.
   cbn [V293_rdy_raw_cells app tl] in Allocated |- *. clear -Allocated.
   sep auto. apply V293_raw_cells_collect_frame. exact Allocated. }
 destruct (V293_OS_TCBInit_shared_return_under_hooks entries tasks lo0 hi0 P f hi hc caller ks ge Mi ir aux O op
  enabled si ci b1 b2 b3 b4 b5 b6 b7 b8 b9 bf table bt base bh bg br bn bo obase present p n
  top bottom identity size ext options Vundef next old prev back restframe current events now bc tp hpc A T cenvs clientM freshb
  clientf tau arg body entry argument ke hks rest
  C Tasks Events Clock NewCurrent NewCode NewEnv Caller EntryPoint Program FreshBlock Argument CurrentGlobal
  Low High Bitmap Canonical Null FreeGlobal TableGlobal PubEnv Fresh Range ND Base Bound OldBase OldBound Count Valid Next
  TasksAway CellsAway Hook1 Hook2 PrefixEntry) as (Mf&clientM'&Body&Commit&Read&Shared&Core&Stale).
 exists Mf. exists clientM'. split;[eapply V293_local_trans;[exact Prologue |exact Body] | ].
 split;[exact Commit | ]. split;[exact Read | ]. split;[exact Shared | ]. split;assumption.
Qed.

(* This checks only missing function entry, not any later hook or commit. *)
Theorem V293_tcb_missing_call_cannot_return : forall P f args types ks m ir au ret ks' state',
 P f=None ->
 ~V293_local_steps P (curs(sfexec f args types),(kenil,ks)) (m,ir,au)
  (curs(sskip ret),(kenil,ks')) state'.
Proof.
 intros P f args types ks m ir au ret ks' state' Missing Run.
 unfold V293_local_steps in Run.
 inversion Run as [ | y z Step Rest];subst.
 destruct y as [C1 state1]. cbn in Step.
 apply (V293_missing_port_has_no_step P f args types ks m ir au Missing).
 exists C1. exists state1. exact Step.
Qed.
Print Assumptions V293_OS_TCBInit_call_shared_return_under_hooks.
Print Assumptions V293_tcb_missing_call_cannot_return.
