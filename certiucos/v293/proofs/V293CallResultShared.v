(* Retain physical caller resources through shared-ready packing and return assignment. *)
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
Lemma V293_return_ready_current_keep : forall br bg bp tasks current bc tp prefix suffix ge le M ir aux O op,
 get ge OSTCBCur=Some(bc,Tptr tp) ->
 (ge,le,M,ir,aux,O,op) |= V293_ready_payload br bg bp tasks **
 V293_rdy_raw_cells(prefix++((bc,0%Z),Tptr tp,Vptr current)::suffix) Atrue ->
 (ge,le,M,ir,aux,O,op) |= (V293_ready_payload br bg bp tasks ** CurTid current) **
 V293_rdy_raw_cells(prefix++suffix)Atrue.
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

 assert(Moved:(ge,le,M,ir,aux,O,op) |= CurTid current **
  ((V293_ready_payload br bg bp tasks ** V293_rdy_raw_cells(prefix++suffix)Atrue) ** Atrue)).
 { eapply astar_mono;[intros st H;exact H | |exact Current].
   apply astar_mono;[apply V293_raw_cells_move_frame |intros st H;exact H]. }
 assert(OrderedFrame:(ge,le,M,ir,aux,O,op) |=
  (V293_ready_payload br bg bp tasks ** CurTid current) **
  (V293_rdy_raw_cells(prefix++suffix)Atrue ** Atrue))by(clear -Moved;sep auto).
 eapply astar_mono;[intros st H;exact H | |exact OrderedFrame].
 intros st H. apply astar_comm in H. apply V293_raw_cells_frame_in in H.
 apply V293_raw_cells_mono with(P:=Atrue ** Atrue);[ |exact H].
 intros st2 K. exact I.
Qed.

Lemma V293_return_raw_abstract_reset : forall cells ge le M ir aux O op,
 (ge,le,M,ir,aux,O,op) |= V293_rdy_raw_cells cells Atrue ->
 (ge,le,M,ir,aux,emp,op) |= V293_rdy_raw_cells cells Atrue.
Proof.
 induction cells as[ | [[a tp] v] cells IH];intros ge le M ir aux O op Held;
 cbn[V293_rdy_raw_cells]in *;[exact I | ].
 apply sat_split in Held. destruct Held as(mc&mr&oc&orr&JM&JO&Cell&Rest).
 destruct Cell as[Bytes Empty].
 apply sat_split'. exists mc. exists mr. exists(emp:osabst). exists(emp:osabst).
 split;[exact JM | ]. split;[apply map_join_emp | ].
 split;[split;[exact Bytes |reflexivity] |eapply IH;exact Rest].
Qed.

Lemma V293_return_ready_shared_keep : forall br bg bp tasks current events now cells ge le M ir aux O O' op,
 get O' curtid=Some(oscurt current) -> get O' abstcblsid=Some(abstcblist tasks) ->
 get O' absecblsid=Some(absecblist events) -> get O' ostmid=Some(ostm now) ->
 (ge,le,M,ir,aux,O,op) |= (V293_ready_payload br bg bp tasks ** CurTid current) **
  V293_rdy_raw_cells cells Atrue ->
 (ge,le,M,ir,aux,O',op) |= V293_shared_ready_records br bg bp current tasks events now **
  V293_rdy_raw_cells cells Atrue.
Proof.
 intros br bg bp tasks current events now cells ge le M ir aux O O' op C T E N Held.
 apply sat_split in Held. destruct Held as(mp&mr&opart&orest&JM&JO&Physical&Frame).
 pose proof(V293_init_ready_physical_empty _ _ _ _ _ _ _ _ _ _ _ _ Physical)as Empty.
 subst opart. apply V293_return_raw_abstract_reset in Frame.
 pose proof(V293_init_shared_fields_from_slots _ _ _ _ ge le ir aux O' op C T E N)as Fields.
 assert(Joint:(ge,le,M,ir,aux,O',op) |=
  ((V293_ready_payload br bg bp tasks ** CurTid current) **
   V293_shared_fields current tasks events now) ** V293_rdy_raw_cells cells Atrue).
 { apply sat_split'. exists mp. exists mr. exists O'. exists(emp:osabst).
   split;[exact JM | ]. split;[apply map_join_emp | ]. split;[ |exact Frame].
   apply sat_split'. exists mp. exists(emp:mem). exists(emp:osabst). exists O'.
   split;[apply map_join_emp | ]. split;[apply map_join_comm;apply map_join_emp | ]. split;assumption. }
 unfold V293_shared_ready_records. clear -Joint. sep auto.
Qed.

Lemma V293_return_assign_shared : forall br bg bp tasks current events now before after
 err b old P ks ge le M ir aux O op,
 get le err=Some(b,Tint8) ->
 (ge,le,M,ir,aux,O,op) |= V293_shared_ready_records br bg bp current tasks events now **
  V293_rdy_raw_cells(before++((b,0%Z),Tint8,old)::after)Atrue ->
 exists Mf,
 cstepstar P(curs(sskip(Some(Vint32 Int.zero))),(kenil,kassignr(evar err)Tint8 ks))(ge,le,M)
  (curs(sskip None),(kenil,ks))(ge,le,Mf) /\
 (ge,le,Mf,ir,aux,O,op) |= V293_shared_ready_records br bg bp current tasks events now **
  V293_rdy_raw_cells(before++((b,0%Z),Tint8,Vint32 Int.zero)::after)Atrue.
Proof.
 intros br bg bp tasks current events now before after err b old P ks ge le M ir aux O op Env Held.
 apply V293_raw_cells_frame_in in Held.
 destruct(V293_return_value_assign before (b,0%Z) Tint8 old after(Vint32 Int.zero)(evar err)
  (V293_shared_ready_records br bg bp current tasks events now ** Atrue)P ks ge le M ir aux O op)
 as(Mf&Exec&Final).
 - V293_rdy_eval.
 - V293_rdy_eval.
 - reflexivity.
 - reflexivity.
 - exact Held.
 - exists Mf. split;[exact Exec |apply V293_raw_cells_move_frame;exact Final].
Qed.

Definition V293_TCBInit_return_frame bt base bh bn bo obase present n top bottom identity size ext options bf next :=
 [((bt,(base+20)%Z),Tcom_ptr 410%Z,V293_pub_old_head present bo obase);
  ((bt,(base+24)%Z),Tcom_ptr 410%Z,Vnull);
  ((bh,0%Z),Tptr V293_tcb_type,Vptr(bt,Int.repr base))]++
 [((bn,0%Z),Tint8,V293_byteval(S n))]++
 (if present then [((bo,(obase+24)%Z),Tcom_ptr 410%Z,Vptr(bt,Int.repr base))] else [])++
 V293_tcb_init_record_remainder bt base top bottom identity size ext options++
 [((bf,0%Z),Tptr V293_tcb_type,next)].

Theorem V293_OS_TCBInit_call_assign_shared_under_hooks :
 forall entries tasks lo0 hi0 P f hi hc caller ks ge M ir aux O op enabled si ci
 b1 b2 b3 b4 b5 b6 b7 b8 b9 bf table bt base bh bg br bn bo obase present p n
 top bottom identity size ext options next old prev back current events now bc tp hpc A T cenvs clientM freshb
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
   top bottom identity size ext options next Vnull tail) ->
 V293_records_hook_return tasks' P hc bt base (V293_tcb_second_hook_cont f hi hc caller retks)
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
 top bottom identity size ext options next old prev back current events now bc tp hpc A T cenvs clientM freshb
 clientf tau arg body entry argument ke hks rest err berr olderr before afterframe retks restframe frame
 g r le blocks tasks' extra tail survivors after returned ErrEnv Function LocalsFresh C Tasks Events Clock NewCurrent NewCode NewEnv
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
   ((b9,0%Z),Tint32,Vint32 Int.zero)::((table,(4*Z.of_nat p)%Z),Tptr V293_tcb_type,Vnull)::tail)
  (V293_owned_task_records tasks ** Atrue)).
 { unfold le,V293_tcb_function_cells,V293_tcb_prefix_inputs,V293_tcb_init_input_cells,
   V293_tcb_init_old_fields,V293_tcb_prefix_links in Allocated |- *.
   cbn [V293_rdy_raw_cells app tl] in Allocated |- *. clear -Allocated.
   sep auto. apply V293_raw_cells_collect_frame. exact Allocated. }
 destruct(V293_OS_TCBInit_ready_return_under_hooks entries tasks lo0 hi0 P f hi hc caller retks ge Mi ir aux O op
 enabled si ci b1 b2 b3 b4 b5 b6 b7 b8 b9 bf table bt base bh bg br bn bo obase present p n
 top bottom identity size ext options Vundef next old prev back frame
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
