(* Complete source call, including every fresh allocation and the real return.
   The only simulation postcondition is at the restored caller continuation. *)
Require Import Coq.Arith.Arith Lia.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.simulation.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.framework.proof.step_prop.
Require Import CertiOS.framework.proof.join_prop.
Require Import CertiOS.framework.auxlibs.MapLib.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293ExitDispatchProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293HandoffProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293SchedCallEntryProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCallGlobal.
Local Open Scope nat_scope.

Lemma V293_assign_byte_progsim :
 forall pc po pi ip T cst t ks ge le les M M' ir aus si cs e1 e2 b v ph Th O,
 get les t=Some le ->get aus t=Some((false,si,cs):localst) ->
 InOS(SKIP,(kenil,ks))(pumerge po pi) ->get O curtid=Some(oscurt t) ->
 evaltype e1(ge,le,M)=Some Tint8 ->
 evaladdr e1(ge,le,M)=Some(Vptr(b,Int.zero)) ->
 evaltype e2(ge,le,M)=Some Tint8 ->evalval e2(ge,le,M)=Some v ->
 store Tint8 M(b,0%Z)v=Some M' ->
 ProgSim(pc,(po,pi,ip))(set T t(SKIP,(kenil,ks)))(ge,les,M',ir,aus)ph Th O cst t ->
 ProgSim(pc,(po,pi,ip))(set T t(curs(sassign e1 e2),(kenil,ks)))(ge,les,M,ir,aus)ph Th O cst t.
Proof.
 intros pc po pi ip T cst t ks ge le les M M' ir aus si cs e1 e2 b v ph Th O
 Local Aux Inside Cur Left Address Right Value Store Post.
 eapply V293_exit_pure_progsim with(ks:=ks)
 (C':=(cure e2,(kenil,kassignr e1 Tint8 ks)))(le:=le);try eassumption;try reflexivity.
 - eapply stmt_step;[reflexivity| ];eapply sassign_step;try eassumption;apply eq_int;auto.
 - eapply V293_exit_expr_progsim with(m:=(ge,le,M))(m':=(ge,le,M))
   (c':=curs(sskip(Some v)))(ke':=kenil)(le:=le);try eassumption;try reflexivity.
   + apply evalval_imply_estepstar;exact Value.
   + eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
   + eapply V293_exit_pure_progsim with(ks:=ks)
     (C':=(cure(eaddrof e1),(kenil,kassignl v Tint8 ks)))(le:=le);try eassumption;try reflexivity.
     * eapply stmt_step;[reflexivity|apply sassignrv_step].
     * eapply V293_exit_expr_progsim with(m:=(ge,le,M))(m':=(ge,le,M))
       (c':=curs(sskip(Some(Vptr(b,Int.zero)))))(ke':=kenil)(le:=le);try eassumption;try reflexivity.
       -- apply evaladdr_imply_estepstar;exact Address.
       -- eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
       -- eapply V293_os_silent_progsim with
          (C:=(curs(sskip(Some(Vptr(b,Int.zero)))),(kenil,kassignl v Tint8 ks)))
          (C':=(SKIP,(kenil,ks)))(le:=le)(M':=M');try eassumption.
          ++ apply map_get_set.
          ++ eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
          ++ eapply stmt_step;[reflexivity| ];eapply sassignend_step;try reflexivity;exact Store.
          ++ intros Cf mf Other;eapply V293_store_cstep_unique;[exact Store|exact Other].
          ++ rewrite tasks_set_a_set_a;exact Post.
Qed.

Theorem V293_sched_updates_progsim :
 forall pc po pi ip T cst t ks ge le les M ir aus si cs unmap group rows high y
 bt bg br bh byblock lo hi g oldy oldhigh ph Th O,
 get les t=Some le ->get aus t=Some((false,si,cs):localst) ->
 InOS(SKIP,(kenil,ks))(pumerge po pi) ->get O curtid=Some(oscurt t) ->
 V293_sched_read_env ge le unmap group rows bt bg br ->
 V293_sched_read_memory M bt bg br lo hi g ->
 get le y=Some(byblock,Tint8) ->get le high=None ->get ge high=Some(bh,Tint8) ->
 get M(byblock,0%Z)=Some(true,oldy) ->get M(bh,0%Z)=Some(true,oldhigh) ->
 byblock<>bt ->byblock<>bg ->byblock<>br ->byblock<>bh ->
 lo<256 ->hi<256 ->g=V293_ready_group lo hi ->(exists p,V293_bitmap_ready lo hi p) ->
 ProgSim(pc,(po,pi,ip))(set T t(SKIP,(kenil,ks)))
 (ge,les,V293_write_byte(V293_write_byte M byblock(V293_ready_lookup g))bh(V293_ready_select lo hi g),ir,aus)ph Th O cst t ->
 ProgSim(pc,(po,pi,ip))(set T t(curs(V293_OSSchedNew_updates unmap group rows high y),(kenil,ks)))
 (ge,les,M,ir,aus)ph Th O cst t.
Proof.
 intros pc po pi ip T cst t ks ge le les M ir aus si cs unmap group rows high y
 bt bg br bh byblock lo hi g oldy oldhigh ph Th O Local Aux Inside Cur
 He Hm Ey Eh Gh Wy Wh Byt Byg Byr Byh Hlo Hhi Hg Nonempty Post.
 assert(Gbound:g<256).
 { subst g;unfold V293_ready_group;destruct(lo=?0);destruct(hi=?0);lia. }
 destruct(V293_OSSchedNew_row_eval ge le M unmap group rows bt bg br lo hi g He Hm Gbound)as[Val1 Type1].
 pose proof(V293_write_byte_reads M bt bg br lo hi g byblock(V293_ready_lookup g)Byt Byg Byr Hm)as Reads1.
 pose proof(V293_write_byte_load M byblock(V293_ready_lookup g)
  ltac:(pose proof(proj1(V293_ready_row_spec g Gbound));lia))as Yload.
 destruct(V293_OSSchedNew_priority_eval ge le _ unmap group rows y bt bg br byblock lo hi g
  He Reads1 Ey Yload Hlo Hhi Hg Nonempty)as[Val2 Type2].
 unfold V293_OSSchedNew_updates.
 eapply V293_exit_pure_progsim with(ks:=ks)
 (C':=(curs(sassign(evar y)(V293_OSSchedNew_row_expr unmap group)),
 (kenil,kseq(sassign(evar high)(V293_OSSchedNew_priority_expr unmap rows y))ks)))(le:=le);
 try eassumption;try reflexivity.
 - eapply stmt_step;[reflexivity|apply sseq_step].
 - eapply V293_assign_byte_progsim with(M':=V293_write_byte M byblock(V293_ready_lookup g))(b:=byblock);
   try eassumption.
   + eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
   + cbn[evaltype];rewrite Ey;reflexivity.
   + cbn[evaladdr get_lenv];rewrite Ey;reflexivity.
   + eapply V293_write_byte_store;exact Wy.
   + eapply V293_exit_pure_progsim with(ks:=ks)
     (C':=(curs(sassign(evar high)(V293_OSSchedNew_priority_expr unmap rows y)),(kenil,ks)))(le:=le);
     try eassumption;try reflexivity.
     * eapply stmt_step;[reflexivity|apply sskip_step].
     * eapply V293_assign_byte_progsim with(b:=bh);try eassumption.
       -- cbn[evaltype];rewrite Eh,Gh;reflexivity.
       -- cbn[evaladdr get_lenv get_genv];rewrite Eh,Gh;reflexivity.
       -- eapply V293_write_byte_store;rewrite V293_write_byte_other by exact Byh;exact Wh.
Qed.

(* Allocation choices disappear after freeing the actual one-byte local.
   Equality is of the complete physical heap, not only of the priority load. *)
Lemma V293_sched_storage : forall M b bh yval priority old,
 fresh M b ->get M(bh,0%Z)=Some(true,old) ->
 free Tint8 b(V293_write_byte(V293_write_byte(allocb M b 0%Z 1)b yval)bh priority)
 =Some(V293_write_byte M bh priority).
Proof.
 intros M b bh yval priority old Fresh High.
 assert(Different:b<>bh).
 { intro E;subst bh;assert(Empty:get M(b,0%Z)=None)by(apply V293_success_fresh_none;exact Fresh);congruence. }
 set(Ms:=V293_write_byte(V293_write_byte(allocb M b 0%Z 1)b yval)bh priority).
 assert(W:V293_bytes_writable Ms b 0%Z 1).
 { intros k K;assert(k=0)by lia;subst k.
   exists(Byte(Byte.repr(Int.unsigned(Int.repr(Z.of_nat yval))))).
   replace(0+Z.of_nat 0)%Z with 0%Z by reflexivity.
   unfold Ms;rewrite V293_write_byte_other by congruence;unfold V293_write_byte;apply map_get_set. }
 destruct(V293_freeb_construct 1 Ms b 0%Z W)as[Mf Free].
 assert(Back:Mf=V293_write_byte M bh priority).
 { apply HalfPermMap.extensionality;intros[c i];change(get Mf(c,i)=get(V293_write_byte M bh priority)(c,i)).
   destruct(Pos.eq_dec c b)as[E|E].
   - subst c;rewrite V293_write_byte_other by congruence.
     destruct(Z.eq_dec i 0)as[Z0|Z0].
     + subst i;assert(Empty:get M(b,0%Z)=None)by(apply V293_success_fresh_none;exact Fresh);change(get Mf(b,0%Z)=get M(b,0%Z));rewrite Empty.
       change(get Mf(b,(0+Z.of_nat 0)%Z)=None);eapply V293_freeb_removed;[exact Free|lia].
     + rewrite(V293_freeb_outside _ _ _ _ _ _ _ Free)by(right;lia).
       unfold Ms;rewrite V293_write_byte_other by congruence.
       unfold V293_write_byte;rewrite map_get_set' by congruence.
       apply V293_success_allocb_outside;right;lia.
   - rewrite(V293_freeb_outside _ _ _ _ _ _ _ Free)by(left;exact E).
     unfold Ms,V293_write_byte.
     destruct(Pos.eq_dec c bh)as[F|F].
     + subst c;destruct(Z.eq_dec i 0)as[Z0|Z0].
       * subst i;repeat rewrite map_get_set;reflexivity.
       * repeat rewrite map_get_set' by congruence.
         apply V293_success_allocb_outside;left;exact E.
     + repeat rewrite map_get_set' by congruence.
       apply V293_success_allocb_outside;left;exact E. }
 subst Mf;exact Free.
Qed.

Lemma V293_free_one_successor : forall p ge le M Mf b ks C' m',
 free Tint8 b M=Some Mf ->
 cstep p(curs(sfree((b,Tint8)::nil)None),(kenil,ks))(ge,le,M)C' m' ->
 C'=(curs(sfree nil None),(kenil,ks)) /\ m'=(ge,le,Mf).
Proof.
 intros p ge le M Mf b ks C' m' Free H;inversion H;subst.
 - match goal with H:estep _ _ _ _ _ _ |- _ =>inversion H;subst;try discriminate end.
 - match goal with H:sstep _ _ _ _ _ _ _ |- _ =>inversion H;subst;try discriminate end.
   inversion H0;subst.
   repeat match goal with E:(_,_,_)=(_,_,_) |- _ =>inversion E;subst;clear E end.
   split;[reflexivity|congruence].
Qed.

Lemma V293_free_end_successor : forall p ge le M f body caller ks C' m',
 cstep p(curs(sfree nil None),(kenil,kcall f body caller ks))(ge,le,M)C' m' ->
 C'=(SKIP,(kenil,ks)) /\ m'=(ge,caller,M).
Proof.
 intros p ge le M f body caller ks C' m' H;inversion H;subst.
 - match goal with H:estep _ _ _ _ _ _ |- _ =>inversion H;subst;try discriminate end.
 - match goal with H:sstep _ _ _ _ _ _ _ |- _ =>inversion H;subst;try discriminate end.
   inversion H0;subst.
   repeat match goal with E:(_,_,_)=(_,_,_) |- _ =>inversion E;subst;clear E end.
   match goal with E:callcont(kcall _ _ _ _)=Some _ |- _ =>cbn[callcont]in E;inversion E;subst end.
   split;reflexivity.
Qed.

Lemma V293_sched_return_progsim :
 forall pc po pi ip T cst t ge le caller les M Mf ir aus si cs f body ks b ph Th O,
 get les t=Some le ->get aus t=Some((false,si,cs):localst) ->
 InOS(SKIP,(kenil,kcall f body caller ks))(pumerge po pi) ->
 getaddr le=((b,Tint8)::nil) ->free Tint8 b M=Some Mf ->
 get O curtid=Some(oscurt t) ->
 ProgSim(pc,(po,pi,ip))(set T t(SKIP,(kenil,ks)))(ge,set les t caller,Mf,ir,aus)ph Th O cst t ->
 ProgSim(pc,(po,pi,ip))(set T t(curs sret,(kenil,kcall f body caller ks)))
 (ge,les,M,ir,aus)ph Th O cst t.
Proof.
 intros pc po pi ip T cst t ge le caller les M Mf ir aus si cs f body ks b ph Th O
 Local Aux Inside Layout Free Cur Post.
 eapply V293_exit_pure_progsim with(ks:=kcall f body caller ks)
 (C':=(curs(sfree((b,Tint8)::nil)None),(kenil,kcall f body caller ks)))(le:=le);
 try eassumption;try reflexivity.
 - eapply stmt_step;[reflexivity| ];eapply sret_step;[reflexivity|reflexivity|exact Layout].
 - eapply V293_os_family_progsim with(le:=le)(si:=si)(cs:=cs)
   (C:=(curs(sfree((b,Tint8)::nil)None),(kenil,kcall f body caller ks)));try eassumption.
   + apply map_get_set.
   + eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
   + do 2 eexists;eapply stmt_step;[reflexivity| ];eapply sfree_step;try reflexivity;exact Free.
   + intros C1 g1 l1 M1 Step1.
     destruct(V293_free_one_successor _ _ _ _ _ _ _ _ _ Free Step1)as[A B].
     inversion B;subst g1 l1 M1;subst C1;clear B.
     assert(Same:set les t le=les).
     { change(CltEnvMod.set les t le=les);apply CltEnvMod.get_set_same;exact Local. }
     change(ProgSim(pc,(po,pi,ip))(set(set T t(curs(sfree((b,Tint8)::nil)None),
      (kenil,kcall f body caller ks)))t(curs(sfree nil None),(kenil,kcall f body caller ks)))
      (ge,set les t le,Mf,ir,aus)ph Th O cst t).
     rewrite Same;repeat rewrite <-set_set_eq.
     eapply V293_os_family_progsim with(le:=le)(si:=si)(cs:=cs)
      (C:=(curs(sfree nil None),(kenil,kcall f body caller ks)));try eassumption.
     * apply map_get_set.
     * eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
     * do 2 eexists;eapply stmt_step;[reflexivity| ];eapply sfreeend_step;reflexivity.
     * intros C2 g2 l2 M2 Step2.
       destruct(V293_free_end_successor _ _ _ _ _ _ _ _ _ _ Step2)as[A B].
       inversion B;subst g2 l2 M2;subst C2;clear B.
       repeat rewrite <-set_set_eq;exact Post.
Qed.

Theorem V293_sched_body_progsim :
 forall pc po pi ip T cst t ge caller les M ir aus si cs f unmap group rows high y ks
 bt bg br bh b lo hi g oldhigh ph Th O,
 po f=Some(V293_OSSchedNew_function unmap group rows high y) ->
 get les t=Some caller ->get aus t=Some((false,si,cs):localst) ->
 get O curtid=Some(oscurt t) ->fresh M b ->
 y<>unmap ->y<>group ->y<>rows ->y<>high ->
 get ge unmap=Some(bt,Tarray Tint8 256) ->get ge group=Some(bg,Tint8) ->
 get ge rows=Some(br,Tarray Tint8 2) ->get ge high=Some(bh,Tint8) ->
 V293_sched_read_memory M bt bg br lo hi g ->get M(bh,0%Z)=Some(true,oldhigh) ->
 lo<256 ->hi<256 ->g=V293_ready_group lo hi ->(exists p,V293_bitmap_ready lo hi p) ->
 ProgSim(pc,(po,pi,ip))(set T t(SKIP,(kenil,ks)))
 (ge,les,V293_write_byte M bh(V293_ready_select lo hi g),ir,aus)ph Th O cst t ->
 ProgSim(pc,(po,pi,ip))
 (set T t(curs(V293_OSSchedNew_body unmap group rows high y),
 (kenil,kcall f(V293_OSSchedNew_body unmap group rows high y)caller ks)))
 (ge,set les t(set emp y(b,Tint8):env),allocb M b 0%Z 1,ir,aus)ph Th O cst t.
Proof.
 intros pc po pi ip T cst t ge caller les M ir aus si cs f unmap group rows high y ks
 bt bg br bh b lo hi g oldhigh ph Th O Bind Local Aux Cur Fresh
 Yu Yg Yr Yh Gu Gg Gr Gh Reads High Lo Hi Group Nonempty Post.
 set(le:=set emp y(b,Tint8):env).
 set(Ma:=allocb M b 0%Z 1).
 set(Ms:=V293_write_byte(V293_write_byte Ma b(V293_ready_lookup g))bh(V293_ready_select lo hi g)).
 assert(Inside:InOS(SKIP,(kenil,kcall f(V293_OSSchedNew_body unmap group rows high y)caller ks))(pumerge po pi)).
 { eapply V293_bound_call_inos;exact Bind. }
 assert(FreshT:b<>bt).
 { eapply V293_success_load_not_fresh with(n:=V293_ready_lookup 0);[exact Fresh|exact(proj1(proj2 Reads)0 ltac:(lia))]. }
 assert(FreshG:b<>bg)by(eapply V293_success_load_not_fresh;[exact Fresh|exact(proj1 Reads)]).
 assert(FreshR:b<>br)by(eapply V293_success_load_not_fresh;[exact Fresh|exact(proj1(proj2(proj2 Reads)))]).
 assert(FreshH:b<>bh).
 { intro E;subst bh;assert(Empty:get M(b,0%Z)=None)by(apply V293_success_fresh_none;exact Fresh);congruence. }
 assert(AllocatedReads:V293_sched_read_memory Ma bt bg br lo hi g).
 { unfold Ma;change(V293_sched_read_memory(set M(b,0%Z)(true,Undef))bt bg br lo hi g).
   destruct Reads as[RG[RT[RR0 RR1]]];unfold V293_sched_read_memory,load,loadm in *;
   cbn[typelen loadbytes]in *;repeat split;
   try(intros n N);repeat rewrite map_get_set' by congruence;auto. }
 assert(ReadEnv:V293_sched_read_env ge le unmap group rows bt bg br).
 { unfold V293_sched_read_env,le;repeat split;try assumption;
   rewrite map_get_set' by congruence;apply map_emp_get. }
 assert(Ey:get le y=Some(b,Tint8))by(unfold le;apply map_get_set).
 assert(Eh:get le high=None)by(unfold le;rewrite map_get_set' by congruence;apply map_emp_get).
 assert(Wy:get Ma(b,0%Z)=Some(true,Undef))by(unfold Ma;change(get(set M(b,0%Z)(true,Undef))(b,0%Z)=Some(true,Undef));apply map_get_set).
 assert(Wh:get Ma(bh,0%Z)=Some(true,oldhigh)).
 { unfold Ma;rewrite V293_success_allocb_outside by(left;congruence);exact High. }
 assert(Layout:getaddr le=((b,Tint8)::nil)).
 { unfold le;change(getaddr(EnvMod.set EnvMod.emp y(b,Tint8))=((b,Tint8)::nil));reflexivity. }
 assert(Free:free Tint8 b Ms=Some(V293_write_byte M bh(V293_ready_select lo hi g))).
 { unfold Ms,Ma;eapply V293_sched_storage;[exact Fresh|exact High]. }
 assert(Restore:set(set les t le)t caller=les).
 { rewrite <-set_set_eq;change(CltEnvMod.set les t caller=les);apply CltEnvMod.get_set_same;exact Local. }
 unfold V293_OSSchedNew_body.
 eapply V293_exit_pure_progsim with(ks:=kcall f(V293_OSSchedNew_body unmap group rows high y)caller ks)
 (C':=(curs(V293_OSSchedNew_updates unmap group rows high y),
  (kenil,kseq sret(kcall f(V293_OSSchedNew_body unmap group rows high y)caller ks))))(le:=le);
 try eassumption;try reflexivity.
 - apply map_get_set.
 - eapply stmt_step;[reflexivity|apply sseq_step].
 - eapply V293_sched_updates_progsim with(bt:=bt)(bg:=bg)(br:=br)(bh:=bh)(byblock:=b)
   (lo:=lo)(hi:=hi)(g:=g)(oldy:=Undef)(oldhigh:=oldhigh)(le:=le);try eassumption.
   + apply map_get_set.
   + eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
   + eapply V293_exit_pure_progsim with(ks:=kcall f(V293_OSSchedNew_body unmap group rows high y)caller ks)
     (C':=(curs sret,(kenil,kcall f(V293_OSSchedNew_body unmap group rows high y)caller ks)))(le:=le);
     try eassumption;try reflexivity.
     * apply map_get_set.
     * eapply stmt_step;[reflexivity|apply sskip_step].
     * eapply V293_sched_return_progsim with(le:=le)(b:=b);try eassumption.
       -- apply map_get_set.
       -- rewrite Restore;exact Post.
Qed.

(* Stable interface: there is no simulation premise at the callee body. *)
Theorem V293_sched_call_progsim :
 forall pc po pi ip T cst t ge caller les M ir aus si cs f unmap group rows high y ks
 bt bg br bh lo hi g oldhigh ph Th O,
 po f=Some(V293_OSSchedNew_function unmap group rows high y) ->
 get les t=Some caller ->get aus t=Some((false,si,cs):localst) ->
 get T t=Some(curs(scall f nil),(kenil,ks)) ->
 InOS(SKIP,(kenil,ks))(pumerge po pi) ->get O curtid=Some(oscurt t) ->
 y<>unmap ->y<>group ->y<>rows ->y<>high ->
 get ge unmap=Some(bt,Tarray Tint8 256) ->get ge group=Some(bg,Tint8) ->
 get ge rows=Some(br,Tarray Tint8 2) ->get ge high=Some(bh,Tint8) ->
 V293_sched_read_memory M bt bg br lo hi g ->get M(bh,0%Z)=Some(true,oldhigh) ->
 lo<256 ->hi<256 ->g=V293_ready_group lo hi ->(exists p,V293_bitmap_ready lo hi p) ->
 ProgSim(pc,(po,pi,ip))(set T t(SKIP,(kenil,ks)))
 (ge,les,V293_write_byte M bh(V293_ready_select lo hi g),ir,aus)ph Th O cst t ->
 ProgSim(pc,(po,pi,ip))T(ge,les,M,ir,aus)ph Th O cst t.
Proof.
 intros pc po pi ip T cst t ge caller les M ir aus si cs f unmap group rows high y ks
 bt bg br bh lo hi g oldhigh ph Th O Bind Local Aux Code Inside Cur
 Yu Yg Yr Yh Gu Gg Gr Gh Reads High Lo Hi Group Nonempty Post.
 eapply V293_sched_call_entry_progsim;try eassumption.
 intros b Fresh;eapply V293_sched_body_progsim;try eassumption.
Qed.
