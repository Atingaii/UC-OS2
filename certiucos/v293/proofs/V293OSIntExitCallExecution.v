(* Actual call/allocate/body/free execution of the ADR-0005 abstract function.
   No execution of the raw port calls, no production WFFunEnv claim. *)
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitExecution.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.framework.include_frm.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition V293_OSIntExit_abstract_function running nesting lock saved table high target current counter sched_id int_switch : function :=
 (Tvoid,dnil,dcons saved Tint32 dnil,
 V293_OSIntExit_abstract_body running nesting lock saved table high target current counter sched_id int_switch).

(* All allocation, store, call-continuation and free side conditions are
   discharged internally. Only the actual global inputs/permission remain. *)
Theorem V293_OSIntExit_nested_call_execution : forall P ks ge caller M ir enabled si ci
 f running nesting lock saved table high target current counter sched_id int_switch br bn n,
 P f=Some(V293_OSIntExit_abstract_function running nesting lock saved table high target current counter sched_id int_switch) ->
 saved<>running -> saved<>nesting -> 2<=n -> n<256 ->
 get ge running=Some(br,Tint8) -> get ge nesting=Some(bn,Tint8) ->
 load Tint8 M(br,0%Z)=Some(V293_byteval 1) ->
 load Tint8 M(bn,0%Z)=Some(V293_byteval n) ->
 (exists old,get M(bn,0%Z)=Some(true,old)) ->
 exists bs Mf,
 fresh M bs /\ bs<>br /\ bs<>bn /\
 V293_local_steps P(curs(scall f nil),(kenil,ks))((ge,caller,M),ir,(enabled,si,ci))
 (curs(sskip None),(kenil,ks))((ge,caller,Mf),ir,(enabled,si,ci)) /\
 load Tint8 Mf(bn,0%Z)=Some(V293_byteval(Nat.pred n)) /\
 load Tint8 Mf(br,0%Z)=Some(V293_byteval 1) /\
 (forall k,k<4 ->get Mf(bs,Z.of_nat k)=None) /\
 (forall b i,b<>bs ->b<>bn ->get Mf(b,i)=get M(b,i)).
Proof.
 intros P ks ge caller M ir enabled si ci f running nesting lock saved table high target current counter
 sched_id int_switch br bn n Program SR SN Lower Bound GR GN Run Nest[old Writable].
 destruct(memory_has_fresh_block M)as[bs Fresh].
 assert(BR:bs<>br)by(eapply V293_success_load_not_fresh;eassumption).
 assert(BN:bs<>bn)by(eapply V293_success_load_not_fresh;eassumption).
 destruct(V293_success_scheduler_storage M bs Fresh)as[Ms[Init[W[Free Frame]]]].
 set(le:=set(emp:env)saved(bs,Tint32)).
 set(body:=V293_OSIntExit_abstract_body running nesting lock saved table high target current counter sched_id int_switch).
 assert(Saved:get le saved=Some(bs,Tint32))by(unfold le;apply map_get_set).
 assert(NR:get le running=None).
 { unfold le;rewrite map_get_set' by exact SR;apply map_emp_get. }
 assert(NN:get le nesting=None).
 { unfold le;rewrite map_get_set' by exact SN;apply map_emp_get. }
 assert(R0:load Tint8 Ms(br,0%Z)=Some(V293_byteval 1)).
 { etransitivity;[apply V293_load_block_frame;intro i;apply Frame;congruence  |  exact Run]. }
 assert(N0:load Tint8 Ms(bn,0%Z)=Some(V293_byteval n)).
 { etransitivity;[apply V293_load_block_frame;intro i;apply Frame;congruence  |  exact Nest]. }
 assert(WN:get Ms(bn,0%Z)=Some(true,old))by(rewrite Frame by congruence;exact Writable).
 pose proof(V293_put_byte_store Ms(bn,0%Z)(Nat.pred n)old WN)as Dec.
 set(M1:=V293_put_byte Ms(bn,0%Z)(Nat.pred n)).
 assert(Addr:getaddr le=[(bs,Tint32)]).
 { unfold le;change(getaddr(EnvMod.set EnvMod.emp saved(bs,Tint32))=[(bs,Tint32)]);reflexivity. }
 assert(ND:NoDup(map fst(getaddr le))).
 { rewrite Addr;cbn;repeat constructor;cbn;tauto. }
 assert(W1:forall b t,In(b,t)(getaddr le)->V293_bytes_writable M1 b 0%Z(typelen t)).
 { intros b t I;rewrite Addr in I;destruct I as[E  |  F];[inversion E;subst b t  |  contradiction].
   intros k K;unfold M1;rewrite V293_put_byte_other by(intro Alias;inversion Alias;congruence);apply W;exact K. }
 destruct(V293_OSIntExit_nested_execution P(kcall f body caller ks)ge le caller
 (allocb M bs 0%Z 4)Ms M1 ir enabled si ci
 running nesting lock saved table high target current counter sched_id int_switch br bn bs n f body ks
 Lower Bound Saved Init NR GR R0 NN GN N0 Dec eq_refl ND W1)as[Mf[Exec[Outside Removed]]].
 exists bs;exists Mf;split;[exact Fresh  |  ];split;[exact BR  |  ];split;[exact BN  |  ].
 split.
 - eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity  |  apply snpcall_step]  |  ].
   eapply V293_local_cons.
   { apply ostc_step;eapply stmt_step;[reflexivity  |  ];eapply sfexec_step with(d1:=dnil)(d2:=dcons saved Tint32 dnil).
     - reflexivity.
     - reflexivity.
     - exact Program.
     - exact I.
     - reflexivity. }
   eapply V293_local_cons.
   { apply ostc_step;eapply stmt_step;[reflexivity  |  ];eapply salloclv_step.
     - reflexivity.
     - reflexivity.
     - exists bs;split;[exact Fresh  |  ];split;[reflexivity  |  ];split.
       + intros[v V];rewrite map_emp_get in V;discriminate.
       + reflexivity. }
   eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity  |  apply sallocend_step]  |  ].
   exact Exec.
 - split.
   + etransitivity;[apply V293_load_block_frame;intro i;apply Outside;rewrite Addr;cbn;intuition congruence  |  ].
     unfold M1;apply V293_put_byte_load;lia.
   + split.
     * etransitivity;[apply V293_load_block_frame;intro i;apply Outside;rewrite Addr;cbn;intuition congruence  |  ].
       unfold M1;rewrite V293_put_byte_other_load.
       -- exact R0.
       -- intro E;inversion E;subst bn;rewrite Run in Nest;inversion Nest as[Eq].
          change(Int.unsigned(Int.repr 1)=Int.unsigned(Int.repr(Z.of_nat n)))in Eq.
          rewrite !Int.unsigned_repr in Eq by(unfold Int.max_unsigned,Int.modulus,Int.wordsize;cbn;lia);lia.
     * split.
       -- intros k K;apply Removed with Tint32;[rewrite Addr;left;reflexivity  |  exact K].
       -- intros b i Bs Bn;rewrite Outside by(rewrite Addr;cbn;intuition congruence).
          unfold M1;rewrite V293_put_byte_other by(intro Alias;inversion Alias;congruence);apply Frame;exact Bs.
Qed.
