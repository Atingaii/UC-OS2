(* Actual normalized scheduler call prefix after blocking. No current-task
   readiness or supplied callee execution is required. Stop before switch. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeDlyEntry.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyFullCall.
Require Import CertiOS.certiucos.v293.proofs.V293ReadySchedCall.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCriticalGlobal.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Require Import CertiOS.certiucos.v293.code.V293OSSchedDispatch.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Lemma V293_sched_byte_release_exact : forall M byblock bh row selected,
 fresh M byblock ->byblock<>bh ->
 free Tint8 byblock
 (V293_write_byte(V293_write_byte(allocb M byblock 0%Z 1)byblock row)bh selected)=
 Some(V293_write_byte M bh selected).
Proof.
 intros M byblock bh row selected Fresh Away.
 unfold free;cbn[typelen freeb].
 unfold V293_write_byte;rewrite map_get_set' by congruence.
 rewrite map_get_set. f_equal.
 apply HalfPermMap.extensionality;intros[c i].
 change(get(del(V293_write_byte(V293_write_byte(allocb M byblock 0%Z 1)byblock row)bh selected)(byblock,0%Z))(c,i)=get(V293_write_byte M bh selected)(c,i)).
 unfold V293_write_byte.
 destruct(addr_eq_dec(c,i)(byblock,0%Z))as[Same|Other].
 - inversion Same;subst c i. rewrite map_del_sem.
   repeat match goal with |- context[if ?d then _ else _]=>destruct d;try congruence end.
   rewrite map_get_set' by congruence. symmetry.
   apply V293_success_fresh_none;exact Fresh.
 - rewrite map_del_sem.
   repeat match goal with |- context[if ?d then _ else _]=>destruct d;try congruence end.
   destruct(addr_eq_dec(c,i)(bh,0%Z))as[Same|OtherH].
   + inversion Same;subst c i;rewrite !map_get_set;reflexivity.
   + rewrite !map_get_set' by congruence.
     apply V293_success_allocb_outside.
     destruct(Pos.eq_dec c byblock)as[Same|N].
     * subst c. assert(NZ : (i<>0)%Z).
       { intro E;apply Other;rewrite E;reflexivity. }
       right;cbn;lia.
     * left;exact N.
Qed.

(* Exact helper call: its fresh byte is not supplied by the caller, and the
   only net memory change is the original OSPrioHighRdy byte assignment. *)
Theorem V293_schednew_raw_call : forall P ks ge caller M f unmap group rows high y
 bt bg br bh lo hi oldhigh,
 P f=Some(V293_OSSchedNew_function unmap group rows high y) ->
 ~In y [unmap;group;rows;high] ->
 get ge unmap=Some(bt,Tarray Tint8 256) ->
 get ge group=Some(bg,Tint8) ->get ge rows=Some(br,Tarray Tint8 2) ->
 get ge high=Some(bh,Tint8) ->
 V293_sched_read_memory M bt bg br lo hi(V293_ready_group lo hi) ->
 get M(bh,0%Z)=Some(true,oldhigh) ->
 lo<256 ->hi<256 ->(exists p,V293_bitmap_ready lo hi p) ->
 exists byblock Ms,
 fresh M byblock /\
 cstepstar P(curs(scall f nil),(kenil,ks))(ge,caller,M)
 (SKIP,(kenil,ks))(ge,caller,V293_write_byte M bh(V293_ready_select lo hi(V293_ready_group lo hi))) /\
 free Tint8 byblock Ms=Some(V293_write_byte M bh(V293_ready_select lo hi(V293_ready_group lo hi))) /\
 get(V293_write_byte M bh(V293_ready_select lo hi(V293_ready_group lo hi)))(byblock,0%Z)=None /\
 byblock<>bh.
Proof.
 intros P ks ge caller M f unmap group rows high y bt bg br bh lo hi oldhigh
 Program Names GT GG GR GH Reads Write Lo Hi Nonempty.
 destruct(V293_ready_fresh_avoiding M[bt;bg;br;bh])as(byblock&Fresh&Away).
 assert(BT:byblock<>bt)by(intro E;apply Away;subst;cbn;tauto).
 assert(BG:byblock<>bg)by(intro E;apply Away;subst;cbn;tauto).
 assert(BR:byblock<>br)by(intro E;apply Away;subst;cbn;tauto).
 assert(BH:byblock<>bh)by(intro E;apply Away;subst;cbn;tauto).
 set(le:=(set emp y(byblock,Tint8):env)).
 set(Ma:=allocb M byblock 0%Z 1).
 set(g:=V293_ready_group lo hi).
 set(selected:=V293_ready_select lo hi g).
 set(body:=V293_OSSchedNew_body unmap group rows high y).
 set(Ms:=V293_write_byte(V293_write_byte Ma byblock(V293_ready_lookup g))bh selected).
 assert(Local:forall x,In x[unmap;group;rows;high]->get le x=None).
 { intros x Member;unfold le;rewrite map_get_set'.
   - apply map_emp_get.
   - intro E;apply Names;subst;exact Member. }
 assert(Env:V293_sched_read_env ge le unmap group rows bt bg br).
 { repeat split;first[apply Local;cbn;tauto|assumption]. }
 assert(ReadA:V293_sched_read_memory Ma bt bg br lo hi g).
 { destruct Reads as[G[T[L H]]];unfold V293_sched_read_memory.
   assert(Frame:forall b i,byblock<>b ->load Tint8 Ma(b,i)=load Tint8 M(b,i)).
   { intros b i N;unfold Ma,load,loadm;cbn[typelen loadbytes].
     rewrite V293_success_allocb_outside by(left;congruence);reflexivity. }
   split;[rewrite Frame by exact BG;exact G| ].
   split;[intros;rewrite Frame by exact BT;apply T;assumption| ].
   split;rewrite Frame by exact BR;assumption. }
 assert(WY:get Ma(byblock,0%Z)=Some(true,Undef))by(unfold Ma;cbn[allocb];apply map_get_set).
 assert(WH:get Ma(bh,0%Z)=Some(true,oldhigh)).
 { unfold Ma;rewrite V293_success_allocb_outside by(left;congruence);exact Write. }
 pose proof(V293_OSSchedNew_updates_execution P(kseq sret(kcall f body caller ks))ge le Ma
 unmap group rows high y bt bg br bh byblock lo hi g Undef oldhigh Env ReadA
 ltac:(unfold le;apply map_get_set)(Local high ltac:(cbn;tauto))GH WY WH BT BG BR BH
 Lo Hi eq_refl Nonempty)as Updates.
 assert(Free:free Tint8 byblock Ms=Some(V293_write_byte M bh selected)).
 { unfold Ms,Ma;apply V293_sched_byte_release_exact;assumption. }
 assert(Layout:getaddr le=[(byblock,Tint8)]).
 { unfold le;change(getaddr(EnvMod.set EnvMod.emp y(byblock,Tint8))=[(byblock,Tint8)]);reflexivity. }
 exists byblock;exists Ms;split;[exact Fresh| ];split.
 - eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply snpcall_step]| ].
   eapply c_stepstarn.
   { eapply stmt_step;[reflexivity| ];eapply sfexec_step with(d1:=dnil)(d2:=dcons y Tint8 dnil);
     [reflexivity|reflexivity|exact Program|exact I|reflexivity]. }
   eapply c_stepstarn.
   { eapply stmt_step;[reflexivity| ];eapply salloclv_step;[reflexivity|reflexivity| ].
     exists byblock;split;[exact Fresh| ];split;[reflexivity| ];split;
     [intros[v E];rewrite map_emp_get in E;discriminate|reflexivity]. }
   eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply sallocend_step]| ].
   unfold body,V293_OSSchedNew_body.
   eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply sseq_step]| ].
   eapply V293_cstepstar_trans;[exact Updates| ].
   eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply sskip_step]| ].
   eapply c_stepstarn;[eapply stmt_step;[reflexivity|eapply sret_step;eassumption||reflexivity]| ].
   eapply c_stepstarn;[eapply stmt_step;[reflexivity|eapply sfree_step;eassumption||reflexivity]| ].
   eapply c_stepstarn;[eapply stmt_step;[reflexivity|eapply sfreeend_step;reflexivity]|apply c_stepstar0].
 - split;[exact Free| ];split;[ |exact BH].
   unfold V293_write_byte;rewrite map_get_set' by congruence.
   apply V293_success_fresh_none;exact Fresh.
Qed.

(* Works when the current task has just blocked: no current-ready premise.
   The continuation is the original comparison/counter/switch, not a return. *)
Theorem V293_sched_call_to_change : forall P ks ge caller M ir enabled si ci forbidden
 f saved interrupt lock helper table high target current counter unmap group rows y
 bt bg br bh bi bl bp bd lo hi oldhigh next,
 P f=Some(V293_OSSched_success_function saved interrupt lock helper table high target current counter) ->
 P helper=Some(V293_OSSchedNew_function unmap group rows high y) ->
 ~In saved[interrupt;lock;table;high;target] ->
 ~In y[unmap;group;rows;high] ->
 get ge interrupt=Some(bi,Tint8) ->get ge lock=Some(bl,Tint8) ->
 get ge unmap=Some(bt,Tarray Tint8 256) ->get ge group=Some(bg,Tint8) ->
 get ge rows=Some(br,Tarray Tint8 2) ->get ge high=Some(bh,Tint8) ->
 get ge table=Some(bp,Tarray(Tptr V293_tcb_type)13) ->
 get ge target=Some(bd,Tptr V293_tcb_type) ->
 load Tint8 M(bi,0%Z)=Some(V293_byteval 0) ->
 load Tint8 M(bl,0%Z)=Some(V293_byteval 0) ->
 V293_sched_read_memory M bt bg br lo hi(V293_ready_group lo hi) ->
 get M(bh,0%Z)=Some(true,oldhigh) ->
 V293_bytes_writable M bd 0%Z 4 ->
 load(Tptr V293_tcb_type)M(bp,(4*Z.of_nat(V293_ready_select lo hi(V293_ready_group lo hi)))%Z)=Some(Vptr next) ->
 lo<256 ->hi<256 ->(exists p,V293_bitmap_ready lo hi p) ->
 bh<>bp ->bd<>bh ->
 exists bs byblock Mi Mf,
 fresh M bs /\ ~In bs forbidden /\ fresh Mi byblock /\
 V293_local_steps P(curs(scall f nil),(kenil,ks))((ge,caller,M),ir,(enabled,si,ci))
 (curs(V293_OSSched_change high current counter(sprim(switch target))),
 (kenil,kseq(sseq(sprim excrit)sret)
 (kcall f(V293_OSSched_success_body saved interrupt lock helper table high target current counter)caller ks)))
 ((ge,V293_cpu_lenv saved bs,Mf),ir,(false,si,enabled::ci)) /\
 load Tint8 Mf(bh,0%Z)=Some(V293_byteval(V293_ready_select lo hi(V293_ready_group lo hi))) /\
 load(Tptr V293_tcb_type)Mf(bd,0%Z)=Some(Vptr next) /\
 V293_bytes_writable Mf bs 0%Z 4 /\
 get Mf(byblock,0%Z)=None /\
 (forall c i,c<>bs ->c<>bh ->c<>bd ->get Mf(c,i)=get M(c,i)).
Proof.
 intros P ks ge caller M ir enabled si ci forbidden f saved interrupt lock helper table high target current counter
 unmap group rows y bt bg br bh bi bl bp bd lo hi oldhigh next
 Program Helper SavedNames HelperNames GI GL GT GG GR GH GP GD LI LL Reads WH WD Pointer Lo Hi Nonempty HP DH.
 destruct(V293_ready_fresh_avoiding M(forbidden++[bt;bg;br;bh;bi;bl;bp;bd]))as(bs&Fresh&Away).
 assert(Bound:forall b,In b[bt;bg;br;bh;bi;bl;bp;bd]->bs<>b).
 { intros b Member E;apply Away;rewrite E;apply in_or_app;right;exact Member. }
 assert(BH:bs<>bh)by(apply Bound;cbn;tauto).
 assert(BD:bs<>bd)by(apply Bound;cbn;tauto).
 set(le:=V293_cpu_lenv saved bs).
 assert(Names:forall x,In x[interrupt;lock;table;high;target]->get le x=None).
 { intros x Member;unfold le,V293_cpu_lenv;rewrite map_get_set'.
   - apply map_emp_get.
   - intro E;apply SavedNames;subst;exact Member. }
 destruct(V293_sched_call_enter P ks ge caller M ir(enabled,si,ci) f saved interrupt lock helper table high target current counter bs Program Fresh)
 as(Mi&Init&Writable&InitialFree&InitFrame&Entered).
 assert(Loads:forall tp b i,bs<>b ->load tp Mi(b,i)=load tp M(b,i)).
 { intros tp b i N;apply V293_load_block_frame;intro j;apply InitFrame;congruence. }
 assert(ReadI:V293_sched_read_memory Mi bt bg br lo hi(V293_ready_group lo hi)).
 { destruct Reads as[G[T[L H]]];repeat split.
   - rewrite Loads by(apply Bound;cbn;tauto);exact G.
   - intros;rewrite Loads by(apply Bound;cbn;tauto);auto.
   - rewrite Loads by(apply Bound;cbn;tauto);exact L.
   - rewrite Loads by(apply Bound;cbn;tauto);exact H. }
 assert(WHI:get Mi(bh,0%Z)=Some(true,oldhigh))by(rewrite InitFrame by congruence;exact WH).
 set(body:=V293_OSSched_success_body saved interrupt lock helper table high target current counter).
 set(change:=V293_OSSched_change high current counter(sprim(switch target))).
 set(K:=kseq(sseq(sprim excrit)sret)(kcall f body caller ks)).
 destruct(V293_schednew_raw_call P(kseq(V293_OSSched_target_update table high target)(kseq change K))
 ge le Mi helper unmap group rows high y bt bg br bh lo hi oldhigh
 Helper HelperNames GT GG GR GH ReadI WHI Lo Hi Nonempty)as(byblock&My&FreshY&NewCall&FreeY&DeadY&YH).
 set(selected:=V293_ready_select lo hi(V293_ready_group lo hi)).
 set(Mh:=V293_write_byte Mi bh selected).
 assert(FrameH:forall c i,c<>bh ->get Mh(c,i)=get Mi(c,i)).
 { intros;unfold Mh;apply V293_write_byte_other;congruence. }
 assert(WDH:V293_bytes_writable Mh bd 0%Z 4).
 { intros k Range;destruct(WD k Range)as(v&E);exists v;rewrite FrameH by congruence;rewrite InitFrame by congruence;exact E. }
 assert(YD:byblock<>bd).
 { intro E;destruct(WD 0 ltac:(lia))as(v&Cell);cbn in Cell.
   rewrite <- InitFrame in Cell by congruence.
   rewrite <- E in Cell;rewrite(V293_success_fresh_none Mi byblock FreshY 0%Z)in Cell;discriminate. }
 destruct(V293_storebytes_exists(encode_val(Tptr V293_tcb_type)(Vptr next))Mh bd 0%Z)
 as(Mf&Store);[rewrite encode_val_length;exact WDH| ].
 assert(FrameD:forall c i,c<>bd ->get Mf(c,i)=get Mh(c,i)).
 { intros c i N;eapply V293_storebytes_outside;[exact Store|left;exact N]. }
 assert(SelectedBound:selected<13)by(apply V293_ready_selection_range;assumption||reflexivity).
 assert(High:load Tint8 Mh(bh,0%Z)=Some(V293_byteval selected)).
 { unfold Mh;apply V293_write_byte_load;lia. }
 assert(Table:load(Tptr V293_tcb_type)Mh(bp,(4*Z.of_nat selected)%Z)=Some(Vptr next)).
 { etransitivity;[apply V293_load_block_frame;intro j;apply FrameH;congruence| ].
   rewrite Loads by(apply Bound;cbn;tauto);exact Pointer. }
 destruct(V293_eval_pointer_array ge le Mh table high V293_tcb_type bp bh selected(Vptr next)
 (Names table ltac:(cbn;tauto))(Names high ltac:(cbn;tauto))GP GH High SelectedBound Table)as[EV ET].
 assert(Assigned:cstepstar P(curs(V293_OSSched_target_update table high target),(kenil,kseq change K))
 (ge,le,Mh)(SKIP,(kenil,kseq change K))(ge,le,Mf)).
 { unfold V293_OSSched_target_update;eapply V293_assign_pointer_execution with(off:=0%Z)(tr:=Tptr V293_tcb_type);
   try exact ET;try exact EV;try exact Store;try reflexivity.
   - cbn[evaltype];rewrite(Names target ltac:(cbn;tauto)),GD;reflexivity.
   - apply eq_vptr;eauto.
   - cbn[evaladdr get_lenv get_genv];rewrite(Names target ltac:(cbn;tauto)),GD;reflexivity.
   - change(0<=0<=4294967295)%Z;lia. }
 exists bs;exists byblock;exists Mi;exists Mf;split;[exact Fresh| ];split.
 - intro E;apply Away;apply in_or_app;left;exact E.
 - split;[exact FreshY| ];split.
   + eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply snpcall_step]| ].
     eapply V293_local_trans;[exact Entered| ].
     eapply V293_local_trans.
     { eapply V293_sched_control_enter with(ni:=0)(nl:=0);try eassumption;try lia.
       - apply Names;cbn;tauto.
       - apply Names;cbn;tauto.
       - rewrite Loads by(apply Bound;cbn;tauto);exact LI.
       - rewrite Loads by(apply Bound;cbn;tauto);exact LL. }
     cbn[Nat.eqb andb].
     eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sseq_step]| ].
     unfold V293_OSSched_unlocked_prefix.
     eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sseq_step]| ].
     eapply V293_local_trans;[apply V293_csteps_local;exact NewCall| ].
     eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sskip_step]| ].
     eapply V293_local_trans;[apply V293_csteps_local;exact Assigned| ].
     eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sskip_step]| ].
     apply V293_local_refl.
   + split.
     * etransitivity;[apply V293_load_block_frame;intro j;apply FrameD;congruence|exact High].
     * split;[eapply V293_store_readback;[reflexivity|exact Store]| ];split.
       -- intros k Range;destruct(Writable k Range)as(v&E);exists v;rewrite FrameD by congruence;rewrite FrameH by congruence;exact E.
       -- split;[rewrite FrameD by exact YD;exact DeadY| ].
          intros c i NB NH ND;rewrite FrameD by exact ND;rewrite FrameH by exact NH;apply InitFrame;exact NB.
Qed.
