(* Resource-conditional simulation of the exact saved nested return context.
   This file does not establish wakeup or global rescheduling reachability. *)
Require Import CertiOS.certiucos.v293.proofs.V293ReadyResumePartition.
Require Import CertiOS.certiucos.v293.proofs.V293InvariantPendingTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293PendingReturnTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293ReturnClientTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyFullCall.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCallGlobal.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturnProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293SchedCallProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickReturnTail.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293ClientSkipTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293HandoffProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitch.
Require Import CertiOS.certiucos.v293.proofs.V293SwitchReturnTaskSim.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.simulation.
Require Import CertiOS.framework.proof.memory_prop.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition V293_return_addresses (cells:list V293_record_cell) :=
 map(fun cell=>let '(a,tp,_) :=cell in(fst a,tp))cells.

Lemma V293_nested_free_successor : forall p ge le M Mf b tp al ks C' m',
 free tp b M=Some Mf ->
 cstep p(curs(sfree((b,tp)::al)None),(kenil,ks))(ge,le,M)C' m' ->
 C'=(curs(sfree al None),(kenil,ks)) /\m'=(ge,le,Mf).
Proof.
 intros p ge le M Mf b tp al ks C' m' Free H;inversion H;subst.
 - match goal with H:estep _ _ _ _ _ _ |- _ =>inversion H;subst;try discriminate end.
 - match goal with H:sstep _ _ _ _ _ _ _ |- _ =>inversion H;subst;try discriminate end.
   inversion H0;subst.
   repeat match goal with E:(_,_,_)=(_,_,_) |- _ =>inversion E;subst;clear E end.
   split;[reflexivity|congruence].
Qed.

(* Internal composition interface: only the caller continuation is supplied.
   The free steps themselves are constructed from exclusive cell ownership. *)
Lemma V293_owned_frees_TaskSim : forall cells R pc po pi ip ph Ch O I Post t
 ge le M ir ie ci op f body caller ks,
 (forall a tp v,In(a,tp,v)cells ->snd a=0%Z) ->GoodInvAsrt R ->
 (forall st,st|=R ->st|=CurTid t **Atrue) ->
 InOS(SKIP,(kenil,kcall f body caller ks))(pumerge po pi) ->
 (ge,le,M,ir,(ie,nil,ci),O,op)|=V293_owned_record_cells cells **R ->
 (forall Mret,(ge,caller,Mret,ir,(ie,nil,ci),O,op)|=R ->
 TaskSim(pc,(po,pi,ip))(SKIP,(kenil,ks))(ge,caller,Mret,ir,(ie,nil,ci))
 ph Ch O V293_shared_li I Post t) ->
 TaskSim(pc,(po,pi,ip))(curs(sfree(V293_return_addresses cells)None),(kenil,kcall f body caller ks))
 (ge,le,M,ir,(ie,nil,ci))ph Ch O V293_shared_li I Post t.
Proof.
 induction cells as [ | [[[b z] tp] v] cells IH ];
 intros R pc po pi ip ph Ch O I Post t ge le M ir ie ci op f body caller ks Zero Good Current Inside Held Tail.
 - cbn[V293_return_addresses V293_owned_record_cells map]in Held|-*.
   apply astar_l_aemp_elim in Held.
   assert(Local:satp(ge,caller,M,ir,(ie,nil,ci))O(CurLINV V293_shared_li t)).
   { eapply V293_pending_local with(op:=op);apply Current.
     eapply good_inv_prop;[exact Good|exact Held]. }
   eapply V293_invariant_cstep_TaskSim;[ | | |exact Local|apply Tail; eapply good_inv_prop;[exact Good|exact Held]].
   + eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
   + intros[x E];discriminate E.
   + intros Mf Mall Join;exists Mall;split;[exact Join| ];split.
     * eapply stmt_step;[reflexivity| ];eapply sfreeend_step;reflexivity.
     * intros;eapply V293_free_end_successor;eassumption.
 - assert(Z:z=0%Z)by(apply(Zero(b,z)tp v);left;reflexivity);subst z.
   assert(Packed:(ge,le,M,ir,(ie,nil,ci),O,op)|=
    Amapsto(b,0%Z)tp true v **(V293_owned_record_cells cells **R)).
   { cbn[V293_owned_record_cells]in Held;unfold V293_owned_record_cell in Held;clear -Held;sep auto. }
   destruct(V293_tick_free_owned _ _ _ _ _ _ _ _ _ _ _ Packed)as(Mret&Free&Rest).
   assert(GoodRest:GoodInvAsrt(V293_owned_record_cells cells **R))
    by(split;[apply V293_owned_cells_good|exact Good]).
   assert(Local:satp(ge,le,Mret,ir,(ie,nil,ci))O(CurLINV V293_shared_li t)).
   { eapply V293_pending_local with(op:=op).
     apply astar_mono with(P':=V293_owned_record_cells cells)(Q':=CurTid t **Atrue)in Rest;
      [clear -Rest;sep auto|intros st H;exact H|exact Current]. }
   cbn[V293_return_addresses map].
   eapply V293_invariant_cstep_TaskSim;[ | | |exact Local| ].
   + eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
   + intros[x E];discriminate E.
   + intros Mf Mall Join;destruct(free_mono _ _ _ _ _ _ Join Free)as(Mall'&Free').
     exists Mall';split;[eapply join_free;eassumption| ];split.
     * eapply stmt_step;[reflexivity| ];eapply sfree_step;[reflexivity|reflexivity|exact Free'].
     * intros;eapply V293_nested_free_successor;eassumption.
   + eapply IH;[ |exact Good|exact Current|exact Inside|exact Rest|exact Tail].
     intros a tp' v' Member;apply(Zero a tp' v');right;exact Member.
Qed.

Lemma V293_owned_return_TaskSim : forall cells R pc po pi ip ph Ch O I Post t
 ge le M ir ie ci op f body caller ks,
 getaddr le=V293_return_addresses cells ->
 (forall a tp v,In(a,tp,v)cells ->snd a=0%Z) ->GoodInvAsrt R ->
 (forall st,st|=R ->st|=CurTid t **Atrue) ->
 InOS(SKIP,(kenil,kcall f body caller ks))(pumerge po pi) ->
 (ge,le,M,ir,(ie,nil,ci),O,op)|=V293_owned_record_cells cells **R ->
 (forall Mret,(ge,caller,Mret,ir,(ie,nil,ci),O,op)|=R ->
 TaskSim(pc,(po,pi,ip))(SKIP,(kenil,ks))(ge,caller,Mret,ir,(ie,nil,ci))
 ph Ch O V293_shared_li I Post t) ->
 TaskSim(pc,(po,pi,ip))(SKIP,(kenil,kseq sret(kcall f body caller ks)))
 (ge,le,M,ir,(ie,nil,ci))ph Ch O V293_shared_li I Post t.
Proof.
 intros cells R pc po pi ip ph Ch O I Post t ge le M ir ie ci op f body caller ks Layout Zero Good Current Inside Held Tail.
 assert(Local:satp(ge,le,M,ir,(ie,nil,ci))O(CurLINV V293_shared_li t)).
 { eapply V293_pending_local with(op:=op).
   apply astar_mono with(P':=V293_owned_record_cells cells)(Q':=CurTid t **Atrue)in Held;
    [clear -Held;sep auto|intros st H;exact H|exact Current]. }
 assert(Frees:TaskSim(pc,(po,pi,ip))
  (curs(sfree(V293_return_addresses cells)None),(kenil,kcall f body caller ks))
  (ge,le,M,ir,(ie,nil,ci))ph Ch O V293_shared_li I Post t).
 { eapply V293_owned_frees_TaskSim; eassumption. }
 assert(Return:TaskSim(pc,(po,pi,ip))(curs sret,(kenil,kcall f body caller ks))
  (ge,le,M,ir,(ie,nil,ci))ph Ch O V293_shared_li I Post t).
 { eapply V293_invariant_cstep_TaskSim;[ | | |exact Local|exact Frees].
   - eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
   - intros[x E];discriminate E.
   - intros Mf Mall Join;exists Mall;split;[exact Join| ].
     assert(Next:cstep(pumerge po pi)(curs sret,(kenil,kcall f body caller ks))(ge,le,Mall)
      (curs(sfree(V293_return_addresses cells)None),(kenil,kcall f body caller ks))(ge,le,Mall)).
     { eapply stmt_step;[reflexivity| ];eapply sret_step;[reflexivity|reflexivity|exact Layout]. }
     split;[exact Next| ];intros Cf mf Other.
     destruct(cstep_idmove_deter _ _ _ _ _ _ Next Other)as[EC EM];split;symmetry;assumption. }
 eapply V293_invariant_cstep_TaskSim;[ | | |exact Local|exact Return].
 - eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
 - intros[x E];discriminate E.
 - intros Mf Mall Join;exists Mall;split;[exact Join| ].
   assert(Next:cstep(pumerge po pi)(SKIP,(kenil,kseq sret(kcall f body caller ks)))(ge,le,Mall)
    (curs sret,(kenil,kcall f body caller ks))(ge,le,Mall)).
   { eapply stmt_step;[reflexivity|apply sskip_step]. }
   split;[exact Next| ];intros Cf mf Other.
   destruct(cstep_idmove_deter _ _ _ _ _ _ Next Other)as[EC EM];split;symmetry;assumption.
Qed.

Lemma V293_nested_return_suffix : forall (I:Inv)(R F:asrt) cells
 pc po pi ip A t ge M ir ie ci O op f body tau d1 d2 fd bodyd taud e1 e2
 outer client tail saved b n,
 po f=Some(tau,d1,d2,body) ->po fd=Some(taud,e1,e2,bodyd) ->
 getaddr outer=V293_return_addresses cells ->
 (forall a tp v,In(a,tp,v)cells ->snd a=0%Z) ->
 V293_skip_client_state(SKIP,(kenil,tail)) ->GoodInvAsrt R ->
 (forall st,st|=R ->st|=CurTid t **Atrue) ->
 (forall ge' le' M' O' op', (ge',le',M',ir,(ie,nil,ci),O',op')|=R ->
  (ge',le',M',ir,(ie,nil,ci),O',op')|=RDYINV I t **F) ->
 (ge,V293_cpu_lenv saved b,M,ir,(ie,nil,ci),O,op)|=
 Amapsto(b,0%Z)Tint32 true(Vint32 n) **(V293_owned_record_cells cells **R) ->
 TaskSim(pc,(po,pi,ip))
 (SKIP,(kenil,kseq sret(kcall f body outer(kseq sret(kcall fd bodyd client tail)))))
 (ge,V293_cpu_lenv saved b,M,ir,(ie,nil,ci))(pc,A)(SKIP,(kenil,tail))O V293_shared_li I
 (fun st=>satp(fst st)(snd st)((RDYINV I t **F) **LINV V293_shared_li t nil))t.
Proof.
 intros I R F cells pc po pi ip A t ge M ir ie ci O op f body tau d1 d2 fd bodyd taud e1 e2
 outer client tail saved b n Bind BindD Layout Zero Cases Good Current Close Held.
 eapply V293_owned_return_TaskSim with(cells:=cons ((b,0%Z),Tint32,Vint32 n) nil)
  (R:=V293_owned_record_cells cells **R)(op:=op).
 - apply V293_cpu_layout.
 - intros a tp v Member;cbn[In]in Member;destruct Member as[E|E];[inversion E;reflexivity|contradiction].
 - split;[apply V293_owned_cells_good|exact Good].
 - intros st H;apply astar_mono with(P':=V293_owned_record_cells cells)(Q':=CurTid t **Atrue)in H;
    [clear -H;sep auto|intros s Hs;exact Hs|exact Current].
 - eapply V293_bound_call_inos;exact Bind.
 - cbn[V293_owned_record_cells V293_owned_record_cell];clear -Held;sep auto.
 - intros Mret Rest.
   eapply V293_owned_return_TaskSim with(cells:=cells)(R:=R)(op:=op);
    [exact Layout|exact Zero|exact Good|exact Current| |exact Rest| ].
   + eapply V293_bound_call_inos;exact BindD.
   + intros Mf Final.
     assert(Ready:forall le',satp(ge,le',Mf,ir,(ie,nil,ci))O
       ((RDYINV I t **F) **LINV V293_shared_li t nil)).
     { intros le' ab;apply astar_r_aemp_intro in Final.
       assert(Rdy:(ge,le',Mf,ir,(ie,nil,ci),O,ab)|=RDYINV I t **F).
       { apply Close;eapply good_inv_prop;[exact Good|apply astar_r_aemp_elim;exact Final]. }
       apply astar_r_aemp_intro in Rdy.
       eapply astar_mono;[intros st H;exact H|apply V293_switch_local_empty|exact Rdy]. }
     apply V293_return_client_coinduction;[exact Cases| |apply Ready].
     eapply V293_pending_local with(op:=op);apply Current;eapply good_inv_prop;[exact Good|exact Final].
Qed.

(* Public bridge: the whole exact nested suffix is built here. Neither its
   execution nor its simulation is an input. The original frame is retained. *)
Theorem V293_ready_nested_return_TaskSim : forall br bg bp cells F
 pc po pi ip A t ge M ir top ci O op f body tau d1 d2 fd bodyd taud e1 e2
 outer client tail saved b n,
 po f=Some(tau,d1,d2,body) ->po fd=Some(taud,e1,e2,bodyd) ->
 getaddr outer=V293_return_addresses cells ->
 (forall a tp v,In(a,tp,v)cells ->snd a=0%Z) ->
 V293_skip_client_state(SKIP,(kenil,tail)) ->GoodInvAsrt F ->(forall i,ir i=false) ->
 (ge,V293_cpu_lenv saved b,M,ir,(false,nil,top::ci),O,op)|=
 Amapsto(b,0%Z)Tint32 true(Vint32 n) **
 (V293_owned_record_cells cells **(V293_ready_full br bg bp t **F)) ->
 TaskSim(pc,(po,pi,ip))
 (SKIP,(kenil,kseq(sseq(sprim excrit)sret)
  (kcall f body outer(kseq sret(kcall fd bodyd client tail)))))
 (ge,V293_cpu_lenv saved b,M,ir,(false,nil,top::ci))
 (pc,A)(SKIP,(kenil,tail))O V293_shared_li(V293_ready_inv br bg bp)
 (fun st=>satp(fst st)(snd st)
 ((RDYINV(V293_ready_inv br bg bp)t **F) **LINV V293_shared_li t nil))t.
Proof.
 intros br bg bp cells F pc po pi ip A t ge M ir top ci O op
 f body tau d1 d2 fd bodyd taud e1 e2 outer client tail saved b n
 Bind BindD Layout Zero Cases GoodF Clear Held.
 set(G:=V293_ready_inv br bg bp);set(Core:=V293_ready_core br bg bp).
 set(K:=kcall f body outer(kseq sret(kcall fd bodyd client tail))).
 set(Post:=fun st:taskst*osabst=>satp(fst st)(snd st)
  ((RDYINV G t **F) **LINV V293_shared_li t nil)).
 assert(GoodCur:GoodInvAsrt(CurTid t)).
 { unfold CurTid,Agvarmapsto,Aptrmapsto;cbn[GoodInvAsrt];intros;repeat split;exact Logic.I. }
 assert(GoodCore:GoodInvAsrt Core)by(apply V293_ready_core_good).
 assert(Packed:(ge,V293_cpu_lenv saved b,M,ir,(false,nil,top::ci),O,op)|=
 Amapsto(b,0%Z)Tint32 true(Vint32 n) **
 (V293_owned_record_cells cells **(Core **(CurTid t **F)))).
 { apply astar_mono with(P':=Amapsto(b,0%Z)Tint32 true(Vint32 n))
    (Q':=V293_owned_record_cells cells **((Core **CurTid t) **F))in Held;
    [clear -Held;sep auto|intros st H;exact H| ].
   apply astar_mono;[intros st H;exact H| ].
   apply astar_mono;[intros st H;apply(proj1(V293_ready_full_core_halves br bg bp t st));exact H|intros st H;exact H]. }
 assert(GoodAll:GoodInvAsrt(Amapsto(b,0%Z)Tint32 true(Vint32 n) **
  (V293_owned_record_cells cells **(Core **(CurTid t **F)))))
 by(split;[exact Logic.I|split;[apply V293_owned_cells_good|split;[exact GoodCore|split;assumption]]]).
 assert(While:forall le',satp(ge,le',M,ir,(false,nil,top::ci))O(CurLINV V293_shared_li t)).
 { intros le';eapply V293_pending_local with(op:=op).
   assert(H:(ge,le',M,ir,(false,nil,top::ci),O,op)|=
    Amapsto(b,0%Z)Tint32 true(Vint32 n) **
    (V293_owned_record_cells cells **(Core **(CurTid t **F))))
    by(eapply good_inv_prop;[exact GoodAll|exact Packed]);clear -H;sep auto. }
 assert(Inside:InOS(SKIP,(kenil,K))(pumerge po pi))
 by(unfold K;eapply V293_bound_call_inos;exact Bind).
 assert(Exit:TaskSim(pc,(po,pi,ip))(curs(sprim excrit),(kenil,kseq sret K))
 (ge,V293_cpu_lenv saved b,M,ir,(false,nil,top::ci))(pc,A)(SKIP,(kenil,tail))O V293_shared_li G Post t).
 { destruct top.
   - assert(Part:(ge,V293_cpu_lenv saved b,M,ir,(false,nil,true::ci),O,op)|=
     (Amapsto(b,0%Z)Tint32 true(Vint32 n) **(V293_owned_record_cells cells **(CurTid t **F))) **Core)
      by(clear -Packed;sep auto).
     apply sat_split in Part;destruct Part as(Mt&Ms&Ot&Os&JM&JO&Task&Shared).
     assert(TaskOn:(ge,V293_cpu_lenv saved b,Mt,ir,(true,nil,ci),Ot,op)|=
      Amapsto(b,0%Z)Tint32 true(Vint32 n) **(V293_owned_record_cells cells **(CurTid t **F))).
     { eapply good_inv_prop;[split;[exact Logic.I|split;[apply V293_owned_cells_good|split;assumption]]|exact Task]. }
     eapply V293_invariant_excrit_TaskSim;[reflexivity| |exact JM|exact JO| | | ].
     + eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
     + intro ab;apply V293_ready_resume_enabled_INV;[exact Clear|eapply good_inv_prop;[exact GoodCore|exact Shared]].
     + eapply V293_pending_local with(op:=op);clear -TaskOn;sep auto.
     + unfold K,Post;eapply V293_nested_return_suffix with(R:=CurTid t **F)(op:=op);
        [exact Bind|exact BindD|exact Layout|exact Zero|exact Cases|split;assumption| | | ].
       * intros st H;sep auto.
       * intros g e m o a H;apply sat_split in H;destruct H as(mc&mf&oc&ofr&Jm&Jo&Cur&Frame).
         apply sat_split';exists mc;exists mf;exists oc;exists ofr.
         split;[exact Jm| ];split;[exact Jo| ];split;[ |exact Frame].
         left;apply sat_split';exists(emp:mem);exists mc;exists(emp:osabst);exists oc.
         split;[apply map_join_comm;apply map_join_emp| ];
         split;[apply map_join_comm;apply map_join_emp| ];split;[ |exact Cur].
         split;[repeat split;reflexivity|exists ir;split;
          [repeat split;reflexivity|split;[exact Clear|split;reflexivity]]].
       * eapply good_inv_prop;[split;[exact Logic.I|split;[apply V293_owned_cells_good|split;assumption]]|exact Task].
   - eapply V293_invariant_excrit_TaskSim with(Mt:=M)(Ms:=(emp:mem))(Ot:=O)(Os:=(emp:osabst));
       [reflexivity| |apply map_join_emp|apply map_join_emp|apply V293_invariant_nil_close;reflexivity|exact(While(V293_cpu_lenv saved b))| ].
     + eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
     + unfold K,Post;eapply V293_nested_return_suffix with(R:=Core **(CurTid t **F))(op:=op);
        [exact Bind|exact BindD|exact Layout|exact Zero|exact Cases|split;[exact GoodCore|split;assumption]| | | ].
       * intros st H;sep auto.
       * intros g e m o a H.
         assert(P:(g,e,m,ir,(false,nil,ci),o,a)|=(Core **CurTid t) **F)by(clear -H;sep auto).
         apply sat_split in P;destruct P as(mr&mf&orr&ofr&Jm&Jo&Own&Frame).
         apply sat_split';exists mr;exists mf;exists orr;exists ofr.
         split;[exact Jm| ];split;[exact Jo| ];split;[ |exact Frame].
         right;unfold SWINVt;fold(CurTid t).
         apply sat_split in Own;destruct Own as(mc&mt&oc&ot&Jm'&Jo'&HC&HT).
         apply sat_split';exists mc;exists mt;exists oc;exists ot.
         split;[exact Jm'| ];split;[exact Jo'| ];split;[ |exact HT].
         apply V293_ready_resume_disabled_SWINV;[exact Clear|exact HC].
       * eapply good_inv_prop;[exact GoodAll|exact Packed]. }
 assert(Seq:TaskSim(pc,(po,pi,ip))(curs(sseq(sprim excrit)sret),(kenil,K))
  (ge,V293_cpu_lenv saved b,M,ir,(false,nil,top::ci))(pc,A)(SKIP,(kenil,tail))O V293_shared_li G Post t).
 { eapply V293_invariant_cstep_TaskSim;[ | | |exact(While(V293_cpu_lenv saved b))|exact Exit].
   - eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
   - intros[x E];discriminate E.
   - intros Mf Mall Join;exists Mall;split;[exact Join| ].
     assert(Next:cstep(pumerge po pi)(curs(sseq(sprim excrit)sret),(kenil,K))(ge,V293_cpu_lenv saved b,Mall)
       (curs(sprim excrit),(kenil,kseq sret K))(ge,V293_cpu_lenv saved b,Mall)).
     { eapply stmt_step;[reflexivity|apply sseq_step]. }
     split;[exact Next| ];intros Cf mf Other.
     destruct(cstep_idmove_deter _ _ _ _ _ _ Next Other)as[EC EM];split;symmetry;assumption. }
 eapply V293_invariant_cstep_TaskSim;[ | | |exact(While(V293_cpu_lenv saved b))|exact Seq].
 - eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
 - intros[x E];discriminate E.
 - intros Mf Mall Join;exists Mall;split;[exact Join| ].
   assert(Next:cstep(pumerge po pi)(SKIP,(kenil,kseq(sseq(sprim excrit)sret)K))(ge,V293_cpu_lenv saved b,Mall)
     (curs(sseq(sprim excrit)sret),(kenil,K))(ge,V293_cpu_lenv saved b,Mall)).
   { eapply stmt_step;[reflexivity|apply sskip_step]. }
   split;[exact Next| ];intros Cf mf Other.
   destruct(cstep_idmove_deter _ _ _ _ _ _ Next Other)as[EC EM];split;symmetry;assumption.
Qed.

Lemma V293_owned_freels : forall cells ge le M ir aux O op R,
 (forall a tp v,In(a,tp,v)cells ->snd a=0%Z) ->
 (ge,le,M,ir,aux,O,op)|=V293_owned_record_cells cells **R ->
 exists Mf,freels(V293_return_addresses cells)M Mf /\(ge,le,Mf,ir,aux,O,op)|=R.
Proof.
 induction cells as [ | [[[b z]tp]v] cells IH];intros ge le M ir aux O op R Zero Held.
 - exists M;split;[constructor|apply astar_l_aemp_elim;exact Held].
 - assert(Z:z=0%Z)by(apply(Zero(b,z)tp v);left;reflexivity);subst z.
   assert(Packed:(ge,le,M,ir,aux,O,op)|=
    Amapsto(b,0%Z)tp true v **(V293_owned_record_cells cells **R))
    by(cbn[V293_owned_record_cells]in Held;unfold V293_owned_record_cell in Held;clear -Held;sep auto).
   destruct(V293_tick_free_owned _ _ _ _ _ _ _ _ _ _ _ Packed)as(M1&Free&Rest).
   destruct(IH ge le M1 ir aux O op R)as(Mf&Frees&Final);
    [intros a tp' v' Member;apply(Zero a tp' v');right;exact Member|exact Rest| ].
   exists Mf;split;[econstructor;eassumption|exact Final].
Qed.

Lemma V293_owned_return_execution : forall p ge le caller M Mf f body ks cells,
 getaddr le=V293_return_addresses cells ->freels(V293_return_addresses cells)M Mf ->
 cstepstar p(SKIP,(kenil,kseq sret(kcall f body caller ks)))(ge,le,M)
 (SKIP,(kenil,ks))(ge,caller,Mf).
Proof.
 intros p ge le caller M Mf f body ks cells Layout Free.
 eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply sskip_step]| ].
 eapply c_stepstarn.
 - eapply stmt_step;[reflexivity| ];eapply sret_step;[reflexivity|reflexivity|exact Layout].
 - eapply V293_cstepstar_trans;[eapply V293_tick_freels_execution;exact Free| ].
   eapply c_stepstarn;[eapply stmt_step;[reflexivity| ];eapply sfreeend_step;reflexivity|apply c_stepstar0].
Qed.

Lemma V293_nested_freels_removed : forall al M Mf,
 freels al M Mf ->forall b tp k,In(b,tp)al ->k<typelen tp ->get Mf(b,Z.of_nat k)=None.
Proof.
 assert(Absent:forall al M0 M1,freels al M0 M1 ->
   forall b i,get M0(b,i)=None ->get M1(b,i)=None).
 { intros al M0 M1 Fs;induction Fs;intros c i Del;[exact Del| ].
   apply IHFs;unfold free in H.
   destruct(Pos.eq_dec c b)as[Same|Other].
   - subst c;destruct(Z_lt_dec i 0)as[Before|After].
     + erewrite V293_freeb_outside;[exact Del|exact H|right;left;exact Before].
     + destruct(Z_lt_dec i(Z.of_nat(typelen t)))as[Inside|Outside].
       * replace i with(0+Z.of_nat(Z.to_nat i))%Z by lia.
         eapply V293_freeb_removed;[exact H|lia].
       * erewrite V293_freeb_outside;[exact Del|exact H|right;right;lia].
   - erewrite V293_freeb_outside;[exact Del|exact H|left;exact Other]. }
 intros al M Mf Fs;induction Fs;intros c tp k Member Positive;[contradiction| ].
 destruct Member as[E|Member].
 - inversion E;subst;eapply Absent;[exact Fs| ].
   replace(Z.of_nat k)with(0+Z.of_nat k)%Z by lia.
   eapply V293_freeb_removed;[exact H|exact Positive].
 - eapply IHFs;[exact Member|exact Positive].
Qed.
