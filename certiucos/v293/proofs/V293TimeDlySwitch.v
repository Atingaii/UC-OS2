(* Scheduler call after blocking, through the real comparison/counter and
   the accepted framework switch. No supplied execution or final store.
   The primitive changes the TCB pointer, not the priority cache. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeDlySchedCall.
Require Import CertiOS.certiucos.v293.proofs.V293ReadySourceTail.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickCountdown.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPointerCompare.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyFullCall.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Lemma V293_sched_change_raw : forall P ks ge le M high current counter suffix bh bc bk nh nc c,
 nh<256 ->nc<256 ->nh<>nc ->
 get le high=None ->get le current=None ->get le counter=None ->
 get ge high=Some(bh,Tint8) ->get ge current=Some(bc,Tint8) ->get ge counter=Some(bk,Tint32) ->
 load Tint8 M(bh,0%Z)=Some(V293_byteval nh) ->
 load Tint8 M(bc,0%Z)=Some(V293_byteval nc) ->
 load Tint32 M(bk,0%Z)=Some(Vint32 c) ->V293_bytes_writable M bk 0%Z 4 ->
 exists Mf,
 cstepstar P(curs(V293_OSSched_change high current counter suffix),(kenil,ks))(ge,le,M)
 (curs suffix,(kenil,ks))(ge,le,Mf) /\
 store Tint32 M(bk,0%Z)(Vint32(Int.add c Int.one))=Some Mf /\
 load Tint32 Mf(bk,0%Z)=Some(Vint32(Int.add c Int.one)) /\
 (forall b i,b<>bk \/(i<0)%Z \/(4<=i)%Z ->get Mf(b,i)=get M(b,i)).
Proof.
 intros P ks ge le M high current counter suffix bh bc bk nh nc c
 Nh Nc Different HN CN NN HG CG NG High Cache Count Writable.
 destruct(V293_OSSched_byte_comparison_eval ge le M high current bh bc nh nc
 Nh Nc HN CN HG CG High Cache)as[Guard GuardType].
 assert(E:Nat.eqb nh nc=false)by(apply Nat.eqb_neq;exact Different).
 rewrite E in Guard.
 destruct(V293_storebytes_exists(encode_val Tint32(Vint32(Int.add c Int.one)))M bk 0%Z)
 as(Mf&Store);[rewrite encode_val_length;exact Writable| ].
 destruct(V293_ready_counter_eval ge le M counter bk c NN NG Count)as(TL&TR&Addr&Value).
 exists Mf;split.
 - unfold V293_OSSched_change.
   eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply sifthen_step]| ].
   eapply V293_cstepstar_trans;[apply V293_expr_steps;apply evalval_imply_estepstar;exact Guard| ].
   eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply svift_step;reflexivity]| ].
   eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply sseq_step]| ].
   eapply V293_cstepstar_trans.
   { unfold V293_OSSched_increment;eapply V293_tick_assign32_execution with(off:=0%Z);
     try eassumption;try reflexivity;change(0<=0<=4294967295)%Z;lia. }
   eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply sskip_step]|apply c_stepstar0].
 - split;[exact Store| ];split.
   + unfold load,loadm;rewrite <-(encode_val_length Tint32(Vint32(Int.add c Int.one))).
     rewrite V293_loadbytes_get.
     * rewrite type_val_mach_encode_val_decode_val by reflexivity;reflexivity.
     * intros k Range;exists true;eapply V293_storebytes_nth;eassumption.
   + intros b i Outside;eapply V293_storebytes_outside;
     [exact Store|cbn[encode_val inj_bytes length];exact Outside].
Qed.

(* Stable call interface. Current may be blocked; only the actual priority
   bytes decide the branch. The original caller is saved below excrit/sret. *)
Theorem V293_sched_call_to_switch : forall P ks ge caller M ir enabled si ci forbidden
 f saved interrupt lock helper table high target current counter unmap group rows y
 bt bg br bh bi bl bp bd bc bk lo hi oldhigh nc c next,
 P f=Some(V293_OSSched_success_function saved interrupt lock helper table high target current counter) ->
 P helper=Some(V293_OSSchedNew_function unmap group rows high y) ->
 ~In saved[interrupt;lock;table;high;target;current;counter] ->
 ~In y[unmap;group;rows;high] ->
 get ge interrupt=Some(bi,Tint8) ->get ge lock=Some(bl,Tint8) ->
 get ge unmap=Some(bt,Tarray Tint8 256) ->get ge group=Some(bg,Tint8) ->
 get ge rows=Some(br,Tarray Tint8 2) ->get ge high=Some(bh,Tint8) ->
 get ge table=Some(bp,Tarray(Tptr V293_tcb_type)13) ->get ge target=Some(bd,Tptr V293_tcb_type) ->
 get ge current=Some(bc,Tint8) ->get ge counter=Some(bk,Tint32) ->
 load Tint8 M(bi,0%Z)=Some(V293_byteval 0) ->load Tint8 M(bl,0%Z)=Some(V293_byteval 0) ->
 V293_sched_read_memory M bt bg br lo hi(V293_ready_group lo hi) ->
 get M(bh,0%Z)=Some(true,oldhigh) ->V293_bytes_writable M bd 0%Z 4 ->
 load(Tptr V293_tcb_type)M(bp,(4*Z.of_nat(V293_ready_select lo hi(V293_ready_group lo hi)))%Z)=Some(Vptr next) ->
 load Tint8 M(bc,0%Z)=Some(V293_byteval nc) ->
 load Tint32 M(bk,0%Z)=Some(Vint32 c) ->V293_bytes_writable M bk 0%Z 4 ->
 lo<256 ->hi<256 ->(exists p,V293_bitmap_ready lo hi p) ->nc<256 ->
 V293_ready_select lo hi(V293_ready_group lo hi)<>nc ->
 bh<>bp ->bd<>bh ->bc<>bh ->bc<>bd ->bk<>bh ->bk<>bd ->
 exists bs byblock Mf,
 fresh M bs /\~In bs forbidden /\
 V293_local_steps P(curs(scall f nil),(kenil,ks))((ge,caller,M),ir,(enabled,si,ci))
 (curs(sprim(switch target)),
 (kenil,kseq(sseq(sprim excrit)sret)
 (kcall f(V293_OSSched_success_body saved interrupt lock helper table high target current counter)caller ks)))
 ((ge,V293_cpu_lenv saved bs,Mf),ir,(false,si,enabled::ci)) /\
 load Tint8 Mf(bh,0%Z)=Some(V293_byteval(V293_ready_select lo hi(V293_ready_group lo hi))) /\
 load(Tptr V293_tcb_type)Mf(bd,0%Z)=Some(Vptr next) /\
 load Tint32 Mf(bk,0%Z)=Some(Vint32(Int.add c Int.one)) /\
 V293_bytes_writable Mf bs 0%Z 4 /\get Mf(byblock,0%Z)=None /\
 (forall b i,b<>bs ->b<>bh ->b<>bd ->b<>bk ->get Mf(b,i)=get M(b,i)).
Proof.
 intros P ks ge caller M ir enabled si ci forbidden f saved interrupt lock helper table high target current counter
 unmap group rows y bt bg br bh bi bl bp bd bc bk lo hi oldhigh nc c next
 Program Helper SavedNames HelperNames GI GL GT GG GR GH GP GD GC GK LI LL Reads WH WD Pointer
 Cache Count WK Lo Hi Nonempty NC Different HP DH CH CD KH KD.
 destruct(V293_sched_call_to_change P ks ge caller M ir enabled si ci(forbidden++[bc;bk])
 f saved interrupt lock helper table high target current counter unmap group rows y
 bt bg br bh bi bl bp bd lo hi oldhigh next Program Helper
 ltac:(intro E;apply SavedNames;cbn in *;tauto)HelperNames GI GL GT GG GR GH GP GD
 LI LL Reads WH WD Pointer Lo Hi Nonempty HP DH)
 as(bs&byblock&Mi&Mr&Fresh&Away&FreshY&Prefix&High&Target&CPU&Dead&Frame).
 assert(BC:bs<>bc)by(intro E;apply Away;rewrite E;apply in_or_app;right;cbn;tauto).
 assert(BK:bs<>bk)by(intro E;apply Away;rewrite E;apply in_or_app;right;cbn;tauto).
 assert(ReadC:load Tint8 Mr(bc,0%Z)=Some(V293_byteval nc)).
 { etransitivity;[apply V293_load_block_frame;intro i;apply Frame;congruence|exact Cache]. }
 assert(ReadK:load Tint32 Mr(bk,0%Z)=Some(Vint32 c)).
 { etransitivity;[apply V293_load_block_frame;intro i;apply Frame;congruence|exact Count]. }
 assert(WKR:V293_bytes_writable Mr bk 0%Z 4).
 { intros k Range;destruct(WK k Range)as(v&Cell);exists v;rewrite Frame by congruence;exact Cell. }
 assert(Local:forall x,In x[high;current;counter]->get(V293_cpu_lenv saved bs)x=None).
 { intros x Member;unfold V293_cpu_lenv;rewrite map_get_set'.
   - apply map_emp_get.
   - intro E;apply SavedNames;subst;cbn in Member|-*;tauto. }
 destruct(V293_sched_change_raw P
 (kseq(sseq(sprim excrit)sret)(kcall f(V293_OSSched_success_body saved interrupt lock helper table high target current counter)caller ks)) ge(V293_cpu_lenv saved bs)Mr high current counter(sprim(switch target))
 bh bc bk(V293_ready_select lo hi(V293_ready_group lo hi))nc c
 ltac:(pose proof(V293_ready_selection_range lo hi(V293_ready_group lo hi)Lo Hi eq_refl Nonempty);lia)
 NC Different(Local high ltac:(cbn;tauto))(Local current ltac:(cbn;tauto))(Local counter ltac:(cbn;tauto))
 GH GC GK High ReadC ReadK WKR)as(Mf&Tail&Store&Counter&KFrame).
 assert(YK:byblock<>bk).
 { intro E;destruct(WKR 0 ltac:(lia))as(v&Cell);cbn in Cell;rewrite <-E,Dead in Cell;discriminate. }
 exists bs;exists byblock;exists Mf;split;[exact Fresh| ];split.
 - intro E;apply Away;apply in_or_app;left;exact E.
 - split;[eapply V293_local_trans;[exact Prefix|apply V293_csteps_local;exact Tail]| ];split.
   + etransitivity;[apply V293_load_block_frame;intro i;apply KFrame;left;congruence|exact High].
   + split.
     * etransitivity;[apply V293_load_block_frame;intro i;apply KFrame;left;congruence|exact Target].
     * split;[exact Counter| ];split.
       -- intros k Range;destruct(CPU k Range)as(v&Cell);exists v;rewrite KFrame by(left;congruence);exact Cell.
       -- split;[rewrite KFrame by(left;exact YK);exact Dead| ].
          intros b i NB NH ND NK;rewrite KFrame by(left;exact NK);apply Frame;assumption.
Qed.

(* Accepted port boundary: construct the store from raw write permission,
   then use the original pswitch_step. No pre-chosen final heap is assumed. *)
Theorem V293_sched_switch_commit : forall pc po pi ip T cst ks old next target bt bc tp
 ge le les M ir aux aus,
 get les old=Some le ->get aus old=Some aux ->
 get T old=Some(curs(sprim(switch target)),(kenil,ks)) ->
 get ge target=Some(bt,Tptr tp) ->load(Tptr tp)M(bt,0%Z)=Some(Vptr next) ->
 get ge OSTCBCur=Some(bc,Tptr tp) ->V293_bytes_writable M bc 0%Z 4 ->
 exists Mf,
 lpstep(pc,(po,pi,ip))T cst(ge,les,M,ir,aus)old
 (set T old(SKIP,(kenil,ks)))cst(ge,les,Mf,ir,aus)next /\
 store(Tptr tp)M(bc,0%Z)(Vptr next)=Some Mf /\
 load(Tptr tp)Mf(bc,0%Z)=Some(Vptr next) /\
 (forall b i,b<>bc \/(i<0)%Z \/(4<=i)%Z ->get Mf(b,i)=get M(b,i)).
Proof.
 intros pc po pi ip T cst ks old next target bt bc tp ge le les M ir aux aus
 Local Aux Code Target Read Current Writable.
 destruct(V293_storebytes_exists(encode_val(Tptr tp)(Vptr next))M bc 0%Z)
 as(Mf&Store);[rewrite encode_val_length;exact Writable| ].
 exists Mf;split.
 - eapply pswitch_step with(tst:=((ge,le,M),ir,aux))(l:=bt)(tp:=tp)(b:=bc);
   try reflexivity;try eassumption.
   unfold projS,projD;cbn;rewrite Local,Aux;reflexivity.
 - split;[exact Store| ];split;[eapply V293_store_readback;[reflexivity|exact Store]| ].
   intros b i Outside;eapply V293_storebytes_outside;
   [exact Store|destruct next;cbn[encode_val inj_pointer length];exact Outside].
Qed.
