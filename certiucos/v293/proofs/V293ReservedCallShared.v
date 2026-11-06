(* The selected physical slot contains a reserved pointer, not null.
   Logical entries describe only the retained table hole at entry.
   Both CPU hook implementations and global concurrent ownership remain open. *)
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

Require Import CertiOS.certiucos.v293.proofs.V293InitReadyCommit.
Require Import CertiOS.certiucos.v293.proofs.V293CallRecords.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateTCBEntry.
Require Import Lia.
Require Import CertiOS.certiucos.v293.proofs.V293CallResultShared.

Lemma V293_priority_reassemble_frame : forall entries tasks b p replacement prefix suffix,
 V293_init_priority_table(update_nth_val p entries replacement)tasks ->
 p<length entries ->
 V293_owned_task_records tasks ** V293_rdy_raw_cells
  (prefix++(((b,(4*Z.of_nat p)%Z),Tptr V293_tcb_type,replacement)::
   V293_priority_hole entries b 0%Z p)++suffix)Atrue ==>
 V293_owned_priority_table b(update_nth_val p entries replacement) **
 (V293_owned_task_records tasks ** V293_rdy_raw_cells(prefix++suffix)Atrue).
Proof.
 intros entries tasks b p replacement prefix suffix Canonical Range s Held.
 set(cells:=((b,(4*Z.of_nat p)%Z),Tptr V293_tcb_type,replacement)::
  V293_priority_hole entries b 0%Z p).
 assert(Shuffled:s |= V293_owned_task_records tasks **
  V293_rdy_raw_cells cells(V293_rdy_raw_cells(prefix++suffix)Atrue)).
 { eapply astar_mono;[intros st H;exact H | |exact Held]. intros st H.
   apply(V293_raw_cells_permutation _ _ (Permutation_app_swap_app prefix cells suffix) Atrue)in H.
   rewrite V293_raw_cells_append in H. exact H. }
 apply V293_raw_cells_frame_in in Shuffled.
 eapply V293_priority_reassemble;[exact Canonical |exact Range |exact Shuffled].
Qed.

Theorem V293_OS_TCBInit_slot_ready_return_under_hooks :
 forall entries tasks lo0 hi0 P f hi hc caller ks ge M ir aux O op enabled si ci
 b1 b2 b3 b4 b5 b6 b7 b8 b9 bf table bt base bh bg br bn bo obase present p n
 top bottom identity size ext options pc next old slot prev back frame,
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
   top bottom identity size ext options next slot tail) ->
 V293_records_hook_return tasks' P hc bt base (V293_tcb_second_hook_cont f hi hc caller ks)
  ge le ir aux O op enabled si ci
  (V293_record_hook_cells b1 b2 b3 b4 b5 b6 b7 b8 b9 bf table bt base p
   top bottom identity size ext options next (Vptr(bt,Int.repr base)) tail) ->
 (ge,le,M,ir,aux,O,op)  |= V293_rdy_raw_cells
  (V293_tcb_init_old_fields bt base old ++
   V293_tcb_prefix_inputs b8 b1 b2 b3 b4 b5 b6 b7 pc p top bottom identity size ext options ++
   V293_tcb_prefix_links bf bt base (Vptr(bt,Int.repr base)) next ++
   ((b9,0%Z),Tint32,Vint32 Int.zero)::((table,(4*Z.of_nat p)%Z),Tptr V293_tcb_type,slot)::tail)
  (V293_owned_task_records tasks ** Atrue) ->
 exists Mf,
 V293_local_steps P
  (curs(V293_TCBInit_prefix 91%Z 108%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z
   (V293_TCBInit_success_suffix hi hc)),(kenil,kcall f (V293_TCBInit_function_body hi hc) caller ks))
  ((ge,le,M),ir,(enabled,si,ci))
  (curs(sskip(Some(Vint32 Int.zero))),(kenil,ks)) ((ge,caller,Mf),ir,(enabled,si,ci)) /\
 (ge,caller,Mf,ir,aux,O,op)  |= V293_owned_task_records tasks' **
  V293_rdy_raw_cells (tl after++survivors) Atrue /\
 (forall b tp k, In (b,tp) (V293_tcb_function_addresses b1 b2 b3 b4 b5 b6 b7 b8 b9) ->
  k<typelen tp -> get Mf (b,Z.of_nat k)=None) /\
 V293_init_priority_table(update_nth_val p entries(Vptr(bt,Int.repr base)))tasks' /\
 (ge,caller,Mf,ir,aux,O,op)  |=
 V293_ready_payload br bg table tasks' ** V293_rdy_raw_cells
  ([((bt,(base+20)%Z),Tcom_ptr 410%Z,V293_pub_old_head present bo obase);
    ((bt,(base+24)%Z),Tcom_ptr 410%Z,Vnull);
    ((bh,0%Z),Tptr V293_tcb_type,Vptr(bt,Int.repr base))]++
   [((bn,0%Z),Tint8,V293_byteval(S n))]++
   (if present then [((bo,(obase+24)%Z),Tcom_ptr 410%Z,Vptr(bt,Int.repr base))] else [])++
   V293_tcb_init_record_remainder bt base top bottom identity size ext options++
   ((bf,0%Z),Tptr V293_tcb_type,next)::frame) Atrue.
Proof.
 intros entries tasks lo0 hi0 P f hi hc caller ks ge M ir aux O op enabled si ci
 b1 b2 b3 b4 b5 b6 b7 b8 b9 bf table bt base bh bg br bn bo obase present p n
 top bottom identity size ext options pc next old slot prev back frame
 g r le blocks tasks' extra tail survivors after Low High Bitmap Canonical Null
 FreeGlobal TableGlobal PubEnv Fresh Range ND Base Bound OldBase OldBound Count Valid Next
 TasksAway CellsAway Hook1 Hook2 Entry.
 assert(G:g<256).
 { unfold g,V293_ready_group. destruct(lo0 =? 0);destruct(hi0 =? 0);lia. }
 assert(Row:r<256).
 { unfold r,V293_ready_row. destruct(V293_prio_row p =? 0);assumption. }
 destruct(V293_OS_TCBInit_prefix_return_records_under_hooks tasks P f hi hc caller ks ge M ir aux O op
 enabled si ci b1 b2 b3 b4 b5 b6 b7 b8 b9 bf table bt base bh bg br bn bo obase present p g r n
 top bottom identity size ext options pc next old slot prev back extra
 FreeGlobal TableGlobal PubEnv Fresh Range ND Base Bound OldBase OldBound G Row Count Valid Next
 TasksAway CellsAway Hook1 Hook2 Entry)as(Mf&Exec&Final&Freed).
 assert(NewCanonical:V293_init_priority_table(update_nth_val p entries(Vptr(bt,Int.repr base)))tasks').
 { apply V293_init_priority_insert;assumption. }
 assert(Joint:(ge,caller,Mf,ir,aux,O,op) |=
  V293_owned_priority_table table(update_nth_val p entries(Vptr(bt,Int.repr base))) **
  (V293_owned_task_records tasks' ** V293_rdy_raw_cells
   (tl after++V293_tcb_init_record_remainder bt base top bottom identity size ext options++
    ((bf,0%Z),Tptr V293_tcb_type,next)::V293_init_other_row br lo0 hi0 p::frame)Atrue)).
 { set(prefix:=tl after++V293_tcb_init_record_remainder bt base top bottom identity size ext options++
    [((bf,0%Z),Tptr V293_tcb_type,next)]).
   pose proof(V293_priority_reassemble_frame entries tasks' table p(Vptr(bt,Int.repr base))
    prefix(V293_init_other_row br lo0 hi0 p::frame)NewCanonical
    ltac:(pose proof(proj1(proj1 Canonical));lia))as PackTable.
   specialize(PackTable(ge,caller,Mf,ir,aux,O,op)).
   unfold prefix,survivors,extra in PackTable,Final.
   cbn[app]in PackTable,Final |- *.
   repeat rewrite <-app_assoc in PackTable.
   repeat rewrite <-app_assoc in Final.
   repeat rewrite <-app_assoc.
   cbn[app]in PackTable,Final |- *. exact(PackTable Final). }
 exists Mf. split;[exact Exec | ]. split;[exact Final | ]. split;[exact Freed | ].
 split;[exact NewCanonical | ].
 pose proof(V293_init_ready_insert lo0 hi0 entries tasks (bt,Int.repr base) p
 Low High Range Fresh Bitmap Canonical Null)as Rel.
 pose proof (V293_init_ready_pack br bg table lo0 hi0 p
 (update_nth_val p entries(Vptr(bt,Int.repr base))) tasks'
 [((bt,(base+20)%Z),Tcom_ptr 410%Z,V293_pub_old_head present bo obase);
  ((bt,(base+24)%Z),Tcom_ptr 410%Z,Vnull);
  ((bh,0%Z),Tptr V293_tcb_type,Vptr(bt,Int.repr base))]
 ([((bn,0%Z),Tint8,V293_byteval(S n))]++
  (if present then [((bo,(obase+24)%Z),Tcom_ptr 410%Z,Vptr(bt,Int.repr base))] else [])++
  V293_tcb_init_record_remainder bt base top bottom identity size ext options++
  [((bf,0%Z),Tptr V293_tcb_type,next)]) frame Rel)as Pack.
 specialize(Pack (ge,caller,Mf,ir,aux,O,op)).
 unfold after,V293_pub_link_cells in Joint. cbn[tl]in Joint.
 cbn[app]in Pack,Joint |- *.
 repeat rewrite <-app_assoc in Pack,Joint |- *.
 destruct present;exact(Pack Joint).
Qed.

Theorem V293_OS_TCBInit_reserved_call_assign_shared_under_hooks :
 forall entries tasks lo0 hi0 P f hi hc caller ks ge M ir aux O op enabled si ci
 b1 b2 b3 b4 b5 b6 b7 b8 b9 bf table bt base bh bg br bn bo obase present p n
 top bottom identity size ext options next old prev back reserve current events now bc tp hpc A T cenvs clientM freshb
 clientf tau arg body entry argument ke hks rest err berr olderr before afterframe,
 let retks:=kassignr(evar err)Tint8 ks in
 let restframe:=before++((berr,0%Z),Tint8,olderr)::afterframe in
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
 let returned:=V293_TCBInit_return_frame bt base bh bn bo obase present n top bottom identity size ext options bf next in
 (bt,Int.repr base)<>(reserve,Int.zero) ->
 get caller err=Some(berr,Tint8) ->
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
 V293_records_hook_return tasks' P hi bt base (V293_tcb_first_hook_cont f hi hc caller retks)
  ge le ir aux O op enabled si ci
  (V293_record_hook_cells b1 b2 b3 b4 b5 b6 b7 b8 b9 bf table bt base p
   top bottom identity size ext options next (Vptr(reserve,Int.zero)) tail) ->
 V293_records_hook_return tasks' P hc bt base (V293_tcb_second_hook_cont f hi hc caller retks)
  ge le ir aux O op enabled si ci
  (V293_record_hook_cells b1 b2 b3 b4 b5 b6 b7 b8 b9 bf table bt base p
   top bottom identity size ext options next (Vptr(bt,Int.repr base)) tail) ->
 (ge,caller,M,ir,aux,O,op) |= V293_rdy_raw_cells
  (V293_tcb_init_old_fields bt base old ++
   V293_tcb_prefix_links bf bt base (Vptr(bt,Int.repr base)) next ++
   ((table,(4*Z.of_nat p)%Z),Tptr V293_tcb_type,Vptr(reserve,Int.zero))::tail)
  (V293_owned_task_records tasks ** Atrue) ->
 exists Mf clientM',
 V293_local_steps P
  (curs(sfexec f [options;ext;size;identity;bottom;top;V293_byteval p]
   V293_TCBInit_argument_types),(kenil,retks)) ((ge,caller,M),ir,(enabled,si,ci))
  (curs(sskip None),(kenil,ks)) ((ge,caller,Mf),ir,(enabled,si,ci)) /\
 hpstep(hpc,A) T(ge,cenvs,clientM)O
  (set(set T current(curs(hapi_code rest),(ke,hks)))(bt,Int.repr base)(nilcont body))
  (ge,set cenvs(bt,Int.repr base)(set emp arg(freshb,Tptr Tvoid)),clientM')
  (set O abstcblsid(abstcblist tasks')) /\
 load(Tptr Tvoid)clientM'(freshb,0%Z)=Some argument /\
 (ge,caller,Mf,ir,aux,set O abstcblsid(abstcblist tasks'),op) |=
  V293_shared_ready_records br bg table current tasks' events now **
  V293_rdy_raw_cells(returned++before++((berr,0%Z),Tint8,Vint32 Int.zero)::afterframe)Atrue.
Proof.
 intros entries tasks lo0 hi0 P f hi hc caller ks ge M ir aux O op enabled si ci
 b1 b2 b3 b4 b5 b6 b7 b8 b9 bf table bt base bh bg br bn bo obase present p n
 top bottom identity size ext options next old prev back reserve current events now bc tp hpc A T cenvs clientM freshb
 clientf tau arg body entry argument ke hks rest err berr olderr before afterframe retks restframe frame
 g r le blocks tasks' extra tail survivors after returned TokenDistinct ErrEnv Function LocalsFresh C Tasks Events Clock NewCurrent NewCode NewEnv
 Caller EntryPoint Program FreshBlock Argument CurrentGlobal
 Low High Bitmap Canonical Null FreeGlobal TableGlobal PubEnv Fresh Range ND Base Bound
 OldBase OldBound Count Valid Next TasksAway CellsAway Hook1 Hook2 Entry.
 assert (Values : V293_tcb_function_values_valid (V293_byteval p) top bottom identity size ext options).
 { unfold V293_tcb_function_values_valid. unfold V293_tcb_init_values_valid in Valid.
   split;[apply V293_byte_type;lia |exact Valid]. }
 apply V293_raw_cells_move_frame in Entry.
 destruct (V293_tcb_call_prologue_records tasks P retks ge caller M ir aux O op enabled si ci f hi hc
  b1 b2 b3 b4 b5 b6 b7 b8 b9 (V293_byteval p) top bottom identity size ext options _
  Function ND LocalsFresh Values Entry) as (Mi&Prologue&Allocated).
 assert (PrefixEntry : (ge,le,Mi,ir,aux,O,op) |= V293_rdy_raw_cells
  (V293_tcb_init_old_fields bt base old ++
   V293_tcb_prefix_inputs b8 b1 b2 b3 b4 b5 b6 b7 Vundef p top bottom identity size ext options ++
   V293_tcb_prefix_links bf bt base (Vptr(bt,Int.repr base)) next ++
   ((b9,0%Z),Tint32,Vint32 Int.zero)::((table,(4*Z.of_nat p)%Z),Tptr V293_tcb_type,Vptr(reserve,Int.zero))::tail)
  (V293_owned_task_records tasks ** Atrue)).
 { unfold le,V293_tcb_function_cells,V293_tcb_prefix_inputs,V293_tcb_init_input_cells,
   V293_tcb_init_old_fields,V293_tcb_prefix_links in Allocated |- *.
   cbn [V293_rdy_raw_cells app tl] in Allocated |- *. clear -Allocated.
   sep auto. apply V293_raw_cells_collect_frame. exact Allocated. }
 destruct(V293_OS_TCBInit_slot_ready_return_under_hooks entries tasks lo0 hi0 P f hi hc caller retks ge Mi ir aux O op
 enabled si ci b1 b2 b3 b4 b5 b6 b7 b8 b9 bf table bt base bh bg br bn bo obase present p n
 top bottom identity size ext options Vundef next old (Vptr(reserve,Int.zero)) prev back frame
 Low High Bitmap Canonical Null FreeGlobal TableGlobal PubEnv Fresh Range ND Base Bound OldBase OldBound Count Valid Next
 TasksAway CellsAway Hook1 Hook2 PrefixEntry)as(Mr&Body&Final&Freed&NewCanonical&Payload).
 assert(Physical:(ge,caller,Mr,ir,aux,O,op) |= V293_ready_payload br bg table tasks' **
   V293_rdy_raw_cells(returned++((bc,0%Z),Tptr tp,Vptr current)::restframe)Atrue).
 { unfold returned,V293_TCBInit_return_frame,frame. repeat rewrite <-app_assoc. exact Payload. }
 destruct(V293_init_ready_create_commit br bg table tasks current(bt,Int.repr base)events now
 ge caller Mr ir aux O op hpc A T cenvs clientM freshb clientf tau arg body entry argument
 (Int.repr(Z.of_nat p)) ke hks rest bc tp returned restframe C Tasks Events Clock Fresh
 NewCurrent NewCode NewEnv Caller EntryPoint Program FreshBlock Argument CurrentGlobal Physical)
 as(clientM'&Commit&NewControl&CurrentControl&NewEnvironment&Read&WeakShared&Core).
 assert(Shared:(ge,caller,Mr,ir,aux,set O abstcblsid(abstcblist tasks'),op) |=
  V293_shared_ready_records br bg table current tasks' events now **
  V293_rdy_raw_cells(returned++restframe)Atrue).
 { eapply V293_return_ready_shared_keep with(O:=O).
   - rewrite map_get_set' by discriminate. exact C.
   - apply map_get_set.
   - rewrite map_get_set' by discriminate. exact Events.
   - rewrite map_get_set' by discriminate. exact Clock.
   - eapply V293_return_ready_current_keep;[exact CurrentGlobal |exact Physical]. }
 unfold restframe in Shared. rewrite app_assoc in Shared.
 destruct(V293_return_assign_shared br bg table tasks' current events now(returned++before)afterframe
 err berr olderr P ks ge caller Mr ir aux(set O abstcblsid(abstcblist tasks'))op ErrEnv Shared)
 as(Mf&Assign&Assigned).
 exists Mf. exists clientM'. split.
 - eapply V293_local_trans;[exact Prologue | ]. eapply V293_local_trans;[exact Body | ].
   apply V293_csteps_local. exact Assign.
 - split;[exact Commit | ]. split;[exact Read | ]. rewrite app_assoc. exact Assigned.
Qed.
