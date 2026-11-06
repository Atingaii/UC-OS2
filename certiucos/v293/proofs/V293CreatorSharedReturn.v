Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateExtPrefix.
Require Import CertiOS.framework.proof.cstepLib.
Require Import Coq.Lists.List Lia.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtCalls.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateStackEntry.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBCall.
Require Import CertiOS.certiucos.v293.proofs.V293TCBSuccessReturn.
(* Real caller prefix and stack-value assignment compose with the original
   strong shared return. Task identity and argument are the actual stack-call
   arguments, not independent witnesses. One stack return and two CPU returns
   remain conditions; concurrent reservation ownership is not supplied. *)
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

Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateTCBSuccess.
Require Import CertiOS.certiucos.v293.proofs.V293ReservedCallShared.

(* Reorder only whole owned segments; their bytes and residual assertion stay fixed. *)
Local Ltac creator_permute :=
 lazymatch goal with
 | |- Permutation (@nil _) (@nil _) => constructor
 | |- Permutation ?xs (?x::?ys) =>
   let rec extract before remaining :=
    lazymatch remaining with
    | x::?zs => eapply Permutation_trans with(l':=x::(before++zs));
      [apply Permutation_sym,Permutation_middle |apply perm_skip;cbn[app];creator_permute]
    | ?z::?zs => extract(before++[z])zs
    end
   in extract(@nil(list V293_record_cell))xs
 end.

Lemma V293_creator_reorder : forall A B C D E F G H slot R,
 V293_rdy_raw_cells(A++slot::B)(V293_rdy_raw_cells(C++D++E++F++G++H)R) ==>
 V293_rdy_raw_cells(C++D++slot::E++F++G++A++B++H)R.
Proof.
 intros A B C D E F G H slot R st Held.
 rewrite <-V293_raw_cells_append in Held.
 assert(Order:Permutation((A++slot::B)++C++D++E++F++G++H)
  (C++D++slot::E++F++G++A++B++H)).
 { assert(Flat:Permutation(flat_map(fun x:list V293_record_cell => x)[A;[slot];B;C;D;E;F;G;H])
   (flat_map(fun x:list V293_record_cell => x)[C;D;[slot];E;F;G;A;B;H])).
   { apply Permutation_flat_map. creator_permute. }
   cbn[flat_map]in Flat. repeat rewrite app_nil_r in Flat.
   repeat rewrite <-app_assoc in Flat. repeat rewrite <-app_assoc. cbn[app]in Flat |- *. exact Flat. }
 eapply V293_raw_cells_permutation;[exact Order |exact Held].
Qed.

(* Select actual local blocks at the reached bridge heap; finite task records
   and future survivor cells are excluded without a freshness oracle. *)
Lemma V293_creator_fresh_records : forall M (tasks:TcbMod.map) (cells:list V293_record_cell),
 exists b1 b2 b3 b4 b5 b6 b7 b8 b9,
 NoDup(V293_tcb_function_blocks b1 b2 b3 b4 b5 b6 b7 b8 b9) /\
 (forall b, In b(V293_tcb_function_blocks b1 b2 b3 b4 b5 b6 b7 b8 b9) -> fresh M b) /\
 (forall t value, In(t,value)(TcbMod.lst tasks) ->
  ~In(fst t)(V293_tcb_function_blocks b1 b2 b3 b4 b5 b6 b7 b8 b9)) /\
 (forall a tp v, In(a,tp,v)cells ->
  ~In(fst a)(V293_tcb_function_blocks b1 b2 b3 b4 b5 b6 b7 b8 b9)).
Proof.
 intros M tasks cells.
 set(extra:=map(fun '(t,_) => ((fst t,0%Z),Tint8,Vundef))(TcbMod.lst tasks)).
 destruct(V293_tcb_fresh_nine_avoiding M(extra++cells))
 as(b1&b2&b3&b4&b5&b6&b7&b8&b9&ND&Fresh&Away).
 exists b1. exists b2. exists b3. exists b4. exists b5. exists b6. exists b7. exists b8. exists b9.  split;[exact ND | ]. split;[exact Fresh | ]. split.
 - intros t value Member. apply(Away(fst t,0%Z)Tint8 Vundef).
   apply in_or_app;left. unfold extra. apply in_map_iff. exists(t,value);split;[reflexivity |exact Member].
 - intros a tp v Member. apply(Away a tp v). apply in_or_app;right;exact Member.
Qed.

Definition V293_creator_before bp bn cpu p btask barg btop bopt target argv topv optv
 bs bb bi bz be value bottom identity size ext : list V293_record_cell :=
 [((bp,0%Z),Tint8,V293_byteval p);((bn,0%Z),Tint8,V293_byteval 0);
  ((cpu,0%Z),Tint32,Vint32 Int.zero)] ++
 V293_stack_argument_cells btask barg btop bopt target argv topv optv ++
 [((bs,0%Z),Tptr Tint32,value);((bb,0%Z),Tptr Tint32,bottom);
  ((bi,0%Z),Tint16,identity);((bz,0%Z),Tint32,size);((be,0%Z),Tptr Tvoid,ext)].

Theorem V293_OSTaskCreateExt_shared_return_under_hooks :
 forall entries tasks lo0 hi0 P f hi hc caller ks ge M ir aux O op enabled si ci
 bf table bt base bh bg br bn bo obase present p n
 top bottom identity size ext options next old prev back reserve current events now bc tp hpc A T cenvs clientM freshb
 clientf tau arg body ke hks rest err berr olderr afterframe
 tableid prioid nestingid cpuid reserveid bp bnest bcpu oldcpu
 psp stack task taskarg stacktop opt btask barg btop bopt target argv topv
 bottomid identityid sizeid extid bs bb bi bz be oldpsp callerrest,
 let resume:=kseq callerrest(kseq V293_TaskCreateExt_occupied ks) in
 let retks:=V293_create_TCB_cont err callerrest ks in
 let before:=V293_creator_before bp bnest bcpu p btask barg btop bopt target argv topv options
  bs bb bi bz be top bottom identity size ext in
 let restframe:=before++((berr,0%Z),Tint8,olderr)::afterframe in
 let frame:=((bc,0%Z),Tptr tp,Vptr current)::restframe in
 let g:=V293_ready_group lo0 hi0 in
 let r:=V293_ready_row lo0 hi0 (V293_prio_row p) in
 let tasks':=set tasks (bt,Int.repr base) (Int.repr(Z.of_nat p),rdy,Vnull) in
 let extra:=V293_priority_hole entries table 0%Z p++V293_init_other_row br lo0 hi0 p::frame in
 let tail:=V293_tcb_creation_tail bt base bh bg br bn bo obase present p prev g r n back++extra in
 let survivors:=V293_tcb_init_record_remainder bt base top bottom identity size ext options++
  [((bf,0%Z),Tptr V293_tcb_type,next);((table,(4*Z.of_nat p)%Z),Tptr V293_tcb_type,Vptr(bt,Int.repr base))]++extra in
 let after:=V293_pub_link_cells bf bt base bh bg br bn bo obase present p
  (V293_pub_old_head present bo obase) Vnull (Vptr(bt,Int.repr base))
  (Nat.setbit g (V293_prio_row p)) (Nat.setbit r (V293_prio_bit p)) (S n) (Vptr(bt,Int.repr base)) in
 let returned:=V293_TCBInit_return_frame bt base bh bn bo obase present n top bottom identity size ext options bf next in
 (bt,Int.repr base)<>(reserve,Int.zero) ->
 get caller err=Some(berr,Tint8) ->
 P f=Some(V293_TCBInit_function hi hc) ->
 get O curtid=Some(oscurt current) -> get O abstcblsid=Some(abstcblist tasks) ->
 get O absecblsid=Some(absecblist events) -> get O ostmid=Some(ostm now) ->
 (bt,Int.repr base)<>current -> get T (bt,Int.repr base)=None ->
 get cenvs (bt,Int.repr base)=None ->
 get T current=Some(curs(hapi_code(spec_seq(spec_crt (V293_task_selector target) argv(Vint32(Int.repr(Z.of_nat p))))rest)),(ke,hks)) ->
 vtoZ (V293_task_selector target)=Some clientf -> hpc clientf=Some(tau,dcons arg(Tptr Tvoid)dnil,dnil,body) ->
 fresh clientM freshb -> type_val_match(Tptr Tvoid)argv=true ->
 get ge OSTCBCur=Some(bc,Tptr tp) ->
 lo0<256 -> hi0<256 -> V293_bitmap_tasks lo0 hi0 tasks ->
 V293_init_priority_table entries tasks -> nth p entries Vnull=Vnull ->
 get ge 91%Z=Some(bf,Tptr V293_tcb_type) -> get ge 92%Z=Some(table,Tarray(Tptr V293_tcb_type) 13) ->
 get ge 93%Z=Some(bh,Tptr V293_tcb_type) -> get ge 94%Z=Some(bg,Tint8) ->
 get ge 95%Z=Some(br,Tarray Tint8 2) -> get ge 96%Z=Some(bn,Tint8) ->
 get tasks (bt,Int.repr base)=None -> p<13 ->
 (0<=base)%Z -> (base+55<=Int.max_unsigned)%Z ->
 (0<=obase)%Z -> (obase+24<=Int.max_unsigned)%Z -> n<255 ->
 V293_tcb_init_values_valid top bottom identity size ext options ->
 rule_type_val_match (Tptr V293_tcb_type) next=true ->
 (forall b1 b2 b3 b4 b5 b6 b7 b8 b9,
  NoDup(V293_tcb_function_blocks b1 b2 b3 b4 b5 b6 b7 b8 b9) ->
 V293_records_hook_return tasks' P hi bt base (V293_tcb_first_hook_cont f hi hc caller retks)
  ge (V293_tcb_function_env b1 b2 b3 b4 b5 b6 b7 b8 b9) ir aux O op enabled si ci
  (V293_record_hook_cells b1 b2 b3 b4 b5 b6 b7 b8 b9 bf table bt base p
   top bottom identity size ext options next (Vptr(reserve,Int.zero)) tail)) ->
 (forall b1 b2 b3 b4 b5 b6 b7 b8 b9,
  NoDup(V293_tcb_function_blocks b1 b2 b3 b4 b5 b6 b7 b8 b9) ->
 V293_records_hook_return tasks' P hc bt base (V293_tcb_second_hook_cont f hi hc caller retks)
  ge (V293_tcb_function_env b1 b2 b3 b4 b5 b6 b7 b8 b9) ir aux O op enabled si ci
  (V293_record_hook_cells b1 b2 b3 b4 b5 b6 b7 b8 b9 bf table bt base p
   top bottom identity size ext options next (Vptr(bt,Int.repr base)) tail)) ->
 get caller prioid=Some(bp,Tint8) -> get caller cpuid=Some(bcpu,Tint32) ->
 get caller nestingid=None -> get ge nestingid=Some(bnest,Tint8) ->
 get caller tableid=None -> get ge tableid=Some(table,Tarray(Tptr V293_tcb_type)13) ->
 get caller reserveid=None -> get ge reserveid=Some(reserve,Tint8) ->
 (0<=target<=Int.max_unsigned)%Z ->
 V293_stack_argument_env caller task taskarg stacktop opt btask barg btop bopt ->
 V293_stack_argument_valid argv topv options ->
 V293_create_TCB_env caller psp bottomid identityid sizeid extid err bs bb bi bz be berr ->
 V293_create_stack_return P stack [options;topv;argv;V293_task_selector target]
  (V293_create_stack_cont psp err f prioid bottomid identityid sizeid extid opt callerrest ks)
  ge caller ir aux O op
  (V293_rdy_raw_cells
   (V293_create_TCB_support bf bt base bh bg br bn bo obase present p next old prev g r n back
    (V293_priority_hole entries table 0%Z p++V293_init_other_row br lo0 hi0 p::
     ((bc,0%Z),Tptr tp,Vptr current)::afterframe))(V293_owned_task_records tasks ** Atrue))
  enabled si ci
  (V293_create_bridge_cells bp bnest bcpu table p(Vint32 Int.zero)(Vptr(reserve,Int.zero))
   btask barg btop bopt target argv topv options bs bb bi bz be berr oldpsp bottom identity size ext olderr) top ->
 (ge,caller,M,ir,aux,O,op) |= V293_rdy_raw_cells
  (V293_create_bridge_cells bp bnest bcpu table p oldcpu Vnull
   btask barg btop bopt target argv topv options bs bb bi bz be berr oldpsp bottom identity size ext olderr)
  (V293_rdy_raw_cells
   (V293_create_TCB_support bf bt base bh bg br bn bo obase present p next old prev g r n back
    (V293_priority_hole entries table 0%Z p++V293_init_other_row br lo0 hi0 p::
     ((bc,0%Z),Tptr tp,Vptr current)::afterframe))(V293_owned_task_records tasks ** Atrue)) ->
 exists Mf clientM',
 V293_local_steps P
  (curs(V293_TaskCreateExt_prefix tableid prioid nestingid cpuid reserveid
    (V293_TaskCreateExt_calls psp stack task taskarg stacktop opt err f prioid bottomid identityid sizeid extid callerrest)),
   (kenil,ks)) ((ge,caller,M),ir,(enabled,si,ci))
  (curs(sskip None),(kenil,resume)) ((ge,caller,Mf),ir,(enabled,si,ci)) /\
 hpstep(hpc,A) T(ge,cenvs,clientM)O
  (set(set T current(curs(hapi_code rest),(ke,hks)))(bt,Int.repr base)(nilcont body))
  (ge,set cenvs(bt,Int.repr base)(set emp arg(freshb,Tptr Tvoid)),clientM')
  (set O abstcblsid(abstcblist tasks')) /\
 load(Tptr Tvoid)clientM'(freshb,0%Z)=Some argv /\
 (ge,caller,Mf,ir,aux,set O abstcblsid(abstcblist tasks'),op) |=
  V293_shared_ready_records br bg table current tasks' events now **
  V293_rdy_raw_cells(returned++before++((berr,0%Z),Tint8,Vint32 Int.zero)::afterframe)Atrue.
Proof.
 intros entries tasks lo0 hi0 P f hi hc caller ks ge M ir aux O op enabled si ci
 bf table bt base bh bg br bn bo obase present p n
 top bottom identity size ext options next old prev back reserve current events now bc tp hpc A T cenvs clientM freshb
 clientf tau arg body ke hks rest err berr olderr afterframe
 tableid prioid nestingid cpuid reserveid bp bnest bcpu oldcpu
 psp stack task taskarg stacktop opt btask barg btop bopt target argv topv
 bottomid identityid sizeid extid bs bb bi bz be oldpsp callerrest
 resume retks before restframe frame g r tasks' extra tail survivors after returned
 TokenDistinct ErrEnv Function C Tasks Events Clock NewCurrent NewCode NewEnv
 Caller EntryPoint Program FreshBlock Argument CurrentGlobal Low High Bitmap Canonical Null
 FreeGlobal TableGlobal HeadGlobal GroupGlobal RowsGlobal CountGlobal Fresh Range
 Base Bound OldBase OldBound Count Valid Next Hook1 Hook2
 Bp Bcpu Nn Gn Nt Gt Nr Gr Target ArgEnv ArgValid Env HookReturn Owned.
 destruct(V293_OSTaskCreateExt_to_TCB_under_stack_return P ks ge caller M ir aux O op
  (V293_rdy_raw_cells
   (V293_create_TCB_support bf bt base bh bg br bn bo obase present p next old prev g r n back
    (V293_priority_hole entries table 0%Z p++V293_init_other_row br lo0 hi0 p::
     ((bc,0%Z),Tptr tp,Vptr current)::afterframe))(V293_owned_task_records tasks ** Atrue))
  enabled si ci tableid prioid nestingid cpuid reserveid bp bnest bcpu table reserve p oldcpu
  psp stack task taskarg stacktop opt btask barg btop bopt target argv topv options
  err f bottomid identityid sizeid extid bs bb bi bz be berr oldpsp bottom identity size ext olderr top callerrest
  Bp Bcpu Nn Gn Nt Gt Nr Gr Range Target ArgEnv ArgValid Env Valid HookReturn Owned)
 as(Mbridge&Prefix&AtTCB).
 assert(CalleeOwned:(ge,caller,Mbridge,ir,aux,O,op) |= V293_rdy_raw_cells
  (V293_tcb_init_old_fields bt base old ++
   V293_tcb_prefix_links bf bt base(Vptr(bt,Int.repr base))next ++
   ((table,(4*Z.of_nat p)%Z),Tptr V293_tcb_type,Vptr(reserve,Int.zero))::tail)
  (V293_owned_task_records tasks ** Atrue)).
 { unfold V293_create_bridge_cells,V293_create_prefix_cells,V293_create_TCB_support in AtTCB.
   pose proof(V293_creator_reorder
    ([((bp,0%Z),Tint8,V293_byteval p);((bnest,0%Z),Tint8,V293_byteval 0);
     ((bcpu,0%Z),Tint32,Vint32 Int.zero)])
    (V293_stack_argument_cells btask barg btop bopt target argv topv options++
     V293_create_bridge_extra bs bb bi bz be berr top bottom identity size ext olderr)
    (V293_tcb_init_old_fields bt base old)
    (V293_tcb_prefix_links bf bt base(Vptr(bt,Int.repr base))next)
    (V293_tcb_creation_tail bt base bh bg br bn bo obase present p prev g r n back)
    (V293_priority_hole entries table 0%Z p)
    ([V293_init_other_row br lo0 hi0 p;((bc,0%Z),Tptr tp,Vptr current)])
    afterframe ((table,(4*Z.of_nat p)%Z),Tptr V293_tcb_type,Vptr(reserve,Int.zero))
    (V293_owned_task_records tasks ** Atrue))as Reorder.
   specialize(Reorder(ge,caller,Mbridge,ir,aux,O,op)).
   repeat rewrite V293_raw_cells_append in AtTCB,Reorder |- *.
   cbn[V293_rdy_raw_cells app]in AtTCB,Reorder |- *.
   specialize(Reorder AtTCB).
   unfold tail,extra,frame,restframe,before,V293_creator_before,V293_create_bridge_extra in Reorder |- *.
   unfold V293_stack_argument_cells in Reorder |- *.
   repeat rewrite <-app_assoc in Reorder. repeat rewrite <-app_assoc.
   cbn[app]in Reorder |- *.
   repeat rewrite V293_raw_cells_append in Reorder. repeat rewrite V293_raw_cells_append.
   cbn[V293_rdy_raw_cells app]in Reorder |- *.
   rewrite(V293_raw_cells_append (V293_tcb_creation_tail bt base bh bg br bn bo obase present p prev g r n back) _ _)in Reorder.
   rewrite(V293_raw_cells_append (V293_priority_hole entries table 0%Z p) _ _)in Reorder.
   cbn[V293_rdy_raw_cells]in Reorder. exact Reorder. }

 destruct(V293_creator_fresh_records Mbridge tasks'(tl after++survivors))
 as(b1&b2&b3&b4&b5&b6&b7&b8&b9&ND&LocalsFresh&TasksAway&CellsAway).
 assert(PubEnv:V293_pub_env ge(V293_tcb_function_env b1 b2 b3 b4 b5 b6 b7 b8 b9)
  108%Z 93%Z 94%Z 95%Z 96%Z b8 bh bg br bn).
 { unfold V293_pub_env. repeat split;try assumption;
   unfold V293_tcb_function_env;repeat rewrite map_get_set' by discriminate;
   first[apply map_get_set |apply map_emp_get]. }
 specialize(Hook1 b1 b2 b3 b4 b5 b6 b7 b8 b9 ND).
 specialize(Hook2 b1 b2 b3 b4 b5 b6 b7 b8 b9 ND).
 destruct(V293_OS_TCBInit_reserved_call_assign_shared_under_hooks entries tasks lo0 hi0
 P f hi hc caller resume ge Mbridge ir aux O op enabled si ci
 b1 b2 b3 b4 b5 b6 b7 b8 b9 bf table bt base bh bg br bn bo obase present p n
 top bottom identity size ext options next old prev back reserve current events now bc tp hpc A T cenvs clientM freshb
 clientf tau arg body (V293_task_selector target) argv ke hks rest err berr olderr before afterframe
 TokenDistinct ErrEnv Function LocalsFresh C Tasks Events Clock NewCurrent NewCode NewEnv
 Caller EntryPoint Program FreshBlock Argument CurrentGlobal Low High Bitmap Canonical Null
 FreeGlobal TableGlobal PubEnv Fresh Range ND Base Bound OldBase OldBound Count Valid Next
 TasksAway CellsAway Hook1 Hook2 CalleeOwned)as(Mf&clientM'&TCB&Commit&Read&Shared).
 exists Mf. exists clientM'. split.
 - eapply V293_local_trans;[exact Prefix |exact TCB].
 - split;[exact Commit | ]. split;[exact Read |exact Shared].
Qed.
