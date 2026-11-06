(* Genuine call allocation. The byte local y remains raw and uninitialized;
   it is not silently initialized to satisfy the older typed body contract. *)
Require Import CertiOS.certiucos.v293.code.V293OSTimeDlyCall.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAPICall.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyFullCall.
Require Import CertiOS.certiucos.v293.proofs.V293TimeDlyEntry.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPublish.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.code.V293OSTimeDly.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.memory_prop.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition V293_dly_call_lenv ticks y saved bt by_ bs:env:=
 set(set(set emp ticks(bt,Tint32))y(by_,Tint8))saved(bs,Tint32).

Lemma V293_dly_fresh_byte_alloc:forall M by_ bs,
 by_<>bs ->fresh M bs ->fresh(allocb M by_ 0%Z 1)bs.
Proof.
 intros M by_ bs Different Fresh l i E[v Bound];subst l.
 change(get(allocb M by_ 0%Z 1)(bs,i)=Some v)in Bound.
 rewrite V293_success_allocb_outside in Bound by(left;congruence).
 apply(Fresh(bs,i)i eq_refl);exists v;exact Bound.
Qed.

Theorem V293_dly_call_allocate:forall P ks ge caller M ir aux O op
 f current rows group y ticks nesting lock sched saved bt by_ bs n R,
 P f=Some(V293_dly_function current rows group y ticks nesting lock sched saved) ->
 ticks<>y ->ticks<>saved ->y<>saved ->
 bt<>by_ ->bt<>bs ->by_<>bs ->fresh M bt ->fresh M by_ ->fresh M bs ->
 (ge,V293_dly_call_lenv ticks y saved bt by_ bs,M,ir,aux,O,op)|=R ->
 exists Mp,
 store Tint32(allocb M bt 0%Z 4)(bt,0%Z)(Vint32 n)=Some Mp /\
 let Ma:=allocb(allocb Mp by_ 0%Z 1)bs 0%Z 4 in
 V293_local_steps P(curs(scall f[econst32 n]),(kenil,ks))((ge,caller,M),ir,aux)
  (curs(V293_dly_full_body current rows group y ticks nesting lock sched saved),
   (kenil,kcall f(V293_dly_full_body current rows group y ticks nesting lock sched saved)caller ks))
  ((ge,V293_dly_call_lenv ticks y saved bt by_ bs,Ma),ir,aux) /\
 (ge,V293_dly_call_lenv ticks y saved bt by_ bs,Ma,ir,aux,O,op)|=
  Amapsto(bs,0%Z)Tint32 true Vundef **
  (Amapsto(by_,0%Z)Tint8 true Vundef **(Amapsto(bt,0%Z)Tint32 true(Vint32 n) **R)).
Proof.
 intros P ks ge caller M ir aux O op f current rows group y ticks nesting lock sched saved
 bt by_ bs n R Program TY TS YS BTY BTS BYS FreshT FreshY FreshS Held.
 pose proof(V293_tick_allocate_frame _ _ _ _ _ _ _ bt Tint32 _ FreshT Held)as Allocated.
 destruct(V293_time_parameter_store _ _ _ _ _ _ _ bt n R Allocated)as(Mp&Store&ParameterOwned).
 assert(FY:fresh Mp by_).
 { eapply V293_time_fresh_after_store;[exact BTY| |exact Store].
   apply V293_time_fresh_after_alloc;assumption. }
 assert(FS:fresh(allocb Mp by_ 0%Z 1)bs).
 { apply V293_dly_fresh_byte_alloc;[exact BYS| ].
   eapply V293_time_fresh_after_store;[exact BTS| |exact Store].
   apply V293_time_fresh_after_alloc;assumption. }
 exists Mp;split;[exact Store| ];split.
 - eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply spcall_step;reflexivity]| ].
   eapply V293_local_cons;[apply ostc_step;eapply expr_step;[reflexivity|constructor]| ].
   eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply svfevalnil_step]| ].
   eapply V293_local_cons.
   { apply ostc_step;eapply stmt_step;[reflexivity| ].
     eapply sfexec_step with(d1:=dcons ticks Tint32 dnil)(d2:=dcons y Tint8(dcons saved Tint32 dnil));
     [reflexivity|reflexivity|exact Program|split;[exact I|reflexivity]|reflexivity]. }
   eapply V293_local_cons.
   { apply ostc_step;eapply stmt_step;[reflexivity| ];eapply sallocp_step with(b:=bt);
     [reflexivity|reflexivity| |apply map_get_set|exact Store].
     exists bt;repeat split;try assumption;try reflexivity.
     intros[v E];rewrite map_emp_get in E;discriminate. }
   eapply V293_local_cons.
   { apply ostc_step;eapply stmt_step;[reflexivity| ];eapply salloclv_step;
     [reflexivity|reflexivity| ]. exists by_;repeat split;try assumption;try reflexivity.
     intros[v E];rewrite map_get_set' in E by congruence;rewrite map_emp_get in E;discriminate. }
   eapply V293_local_cons.
   { apply ostc_step;eapply stmt_step;[reflexivity| ];eapply salloclv_step;
     [reflexivity|reflexivity| ]. exists bs;repeat split;try assumption;try reflexivity.
     intros[v E];rewrite !map_get_set' in E by congruence;rewrite map_emp_get in E;discriminate. }
   eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sallocend_step]| ].
   apply V293_local_refl.
 - eapply (V293_tick_allocate_frame _ _ _ _ _ _ _ bs Tint32 _ FS).
   exact(V293_tick_allocate_frame _ _ _ _ _ _ _ by_ Tint8 _ FY ParameterOwned).
Qed.

(* Stable entry interface: stores and execution are conclusions, not inputs. *)
Theorem V293_dly_call_entry:forall P ks ge caller M ir aux O op
 f current rows group y ticks nesting lock sched saved bt by_ bs n R,
 P f=Some(V293_dly_function current rows group y ticks nesting lock sched saved) ->
 ticks<>y ->ticks<>saved ->y<>saved ->
 bt<>by_ ->bt<>bs ->by_<>bs ->fresh M bt ->fresh M by_ ->fresh M bs ->
 (ge,V293_dly_call_lenv ticks y saved bt by_ bs,M,ir,aux,O,op)|=R ->
 exists Mp Mi,
 store Tint32(allocb M bt 0%Z 4)(bt,0%Z)(Vint32 n)=Some Mp /\
 store Tint32(allocb(allocb Mp by_ 0%Z 1)bs 0%Z 4)(bs,0%Z)(Vint32 Int.zero)=Some Mi /\
 V293_local_steps P(curs(scall f[econst32 n]),(kenil,ks))((ge,caller,M),ir,aux)
  (curs(V293_dly_body current rows group y ticks nesting lock sched),
   (kenil,kcall f(V293_dly_full_body current rows group y ticks nesting lock sched saved)caller ks))
  ((ge,V293_dly_call_lenv ticks y saved bt by_ bs,Mi),ir,aux) /\
 (ge,V293_dly_call_lenv ticks y saved bt by_ bs,Mi,ir,aux,O,op)|=
  Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **
  (Amapsto(by_,0%Z)Tint8 true Vundef **(Amapsto(bt,0%Z)Tint32 true(Vint32 n) **R)).
Proof.
 intros P ks ge caller M ir aux O op f current rows group y ticks nesting lock sched saved
 bt by_ bs n R Program TY TS YS BTY BTS BYS FreshT FreshY FreshS Held.
 destruct(V293_dly_call_allocate P ks ge caller M ir aux O op f current rows group y ticks nesting lock sched saved
 bt by_ bs n R Program TY TS YS BTY BTS BYS FreshT FreshY FreshS Held)as(Mp&Store&Trace&Owned).
 destruct(V293_time_parameter_store _ _ _ _ _ _ _ bs Int.zero _ Owned)as(Mi&Init&After).
 exists Mp;exists Mi;split;[exact Store| ];split;[exact Init| ];split;[ |exact After].
 eapply V293_local_trans;[exact Trace| ].
 unfold V293_dly_full_body.
 eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sseq_step]| ].
 eapply V293_local_trans.
 { apply V293_csteps_local;eapply V293_success_assign_zero;
   [unfold V293_dly_call_lenv;apply map_get_set|exact Init]. }
 eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sskip_step]| ].
 apply V293_local_refl.
Qed.

(* First real assignment reads the TCB, not the uninitialized local y. *)
Theorem V293_dly_raw_y_assignment:forall P ks ge le M ir aux O op R
 current y bc by_ bt base row,
 get le current=None ->get ge current=Some(bc,Tptr V293_tcb_type) ->
 get le y=Some(by_,Tint8) ->
 load(Tptr V293_tcb_type)M(bc,0%Z)=Some(Vptr(bt,Int.repr base)) ->
 load Tint8 M(bt,(base+52)%Z)=Some(V293_byteval row) ->
 (0<=base)%Z ->(base+54<=Int.max_unsigned)%Z ->row<256 ->
 (ge,le,M,ir,aux,O,op)|=Amapsto(by_,0%Z)Tint8 true Vundef **R ->
 exists Mf,
 store Tint8 M(by_,0%Z)(V293_byteval row)=Some Mf /\
 cstepstar P(curs(sassign(evar y)(V293_dly_field current 18%Z)),(kenil,ks))(ge,le,M)
  (SKIP,(kenil,ks))(ge,le,Mf) /\
 (ge,le,Mf,ir,aux,O,op)|=V293_owned_record_cell((by_,0%Z),Tint8,V293_byteval row) **R /\
 (forall b i,b<>by_ ->get Mf(b,i)=get M(b,i)).
Proof.
 intros P ks ge le M ir aux O op R current y bc by_ bt base row Local Global Y Read Row Base Limit Bound Owned.
 assert(T:evaltype(evar current)(ge,le,M)=Some(Tptr V293_tcb_type))
 by(cbn[evaltype get_lenv get_genv];rewrite Local,Global;reflexivity).
 assert(V:evalval(evar current)(ge,le,M)=Some(Vptr(bt,Int.repr base)))
 by(cbn[evalval evaladdr evaltype get_lenv get_genv get_mem];rewrite Local,Global;cbn;exact Read).
 destruct(V293_pub_field_value ge le M(evar current)bt base 18%Z 52%Z Tint8(V293_byteval row)
 T V eq_refl eq_refl Base ltac:(lia)ltac:(lia)Row)as[Ty Value].
 destruct(V293_tick_raw_slot_update(by_,0%Z)Tint8 Vundef(V293_byteval row)R
 ge le M ir aux O op(V293_byte_type row Bound)Owned)as(Mf&Store&After).
 exists Mf;split;[exact Store| ];split.
 - eapply V293_assign_byte_offset_execution with(off:=0%Z);try eassumption;try lia;
   cbn[evaltype evaladdr get_lenv get_genv];rewrite Y;reflexivity.
 - split;[exact After| ];intros b i Different;unfold store in Store.
   eapply V293_storebytes_outside;[exact Store|left;exact Different].
Qed.

Definition V293_dly_after_y current rows group y :=
 sseq(V293_dly_clear_row current rows y)
  (sseq(sskip None)(V293_dly_group_if current rows group y)).
Definition V293_dly_after_y_cont current ticks sched ks :=
 kseq(sseq(sassign(V293_dly_field current 13%Z)(evar ticks))(sskip None))
 (kseq(sseq(sprim excrit)(scall sched nil))(kseq sret ks)).

(* The ownership snapshot retains entry aux, as in the older body interface.
   Execution itself has pushed IE and disabled interrupts. Arbitrary R is not
   claimed to be transported across that aux change. *)
Theorem V293_dly_body_first_y:forall P ks ge le M ir enabled si ci O op R
 current rows group y ticks nesting lock sched bc byloc bt base row bi bl bd duration,
 get le nesting=None ->get ge nesting=Some(bi,Tint8) ->
 load Tint8 M(bi,0%Z)=Some(V293_byteval 0) ->
 get le lock=None ->get ge lock=Some(bl,Tint8) ->
 load Tint8 M(bl,0%Z)=Some(V293_byteval 0) ->
 get le ticks=Some(bd,Tint32) ->load Tint32 M(bd,0%Z)=Some(Vint32 duration) ->duration<>Int.zero ->
 get le current=None ->get ge current=Some(bc,Tptr V293_tcb_type) ->
 get le y=Some(byloc,Tint8) ->
 load(Tptr V293_tcb_type)M(bc,0%Z)=Some(Vptr(bt,Int.repr base)) ->
 load Tint8 M(bt,(base+52)%Z)=Some(V293_byteval row) ->
 (0<=base)%Z ->(base+54<=Int.max_unsigned)%Z ->row<256 ->
 (ge,le,M,ir,(enabled,si,ci),O,op)|=Amapsto(byloc,0%Z)Tint8 true Vundef **R ->
 exists Mf,
 store Tint8 M(byloc,0%Z)(V293_byteval row)=Some Mf /\
 V293_local_steps P(curs(V293_dly_body current rows group y ticks nesting lock sched),(kenil,ks))
 ((ge,le,M),ir,(enabled,si,ci))
 (curs(V293_dly_after_y current rows group y),(kenil,V293_dly_after_y_cont current ticks sched ks))
 ((ge,le,Mf),ir,(false,si,enabled::ci)) /\
 (ge,le,Mf,ir,(enabled,si,ci),O,op)|=
  V293_owned_record_cell((byloc,0%Z),Tint8,V293_byteval row) **R /\
 (forall b i,b<>byloc ->get Mf(b,i)=get M(b,i)).
Proof.
 intros P ks ge le M ir enabled si ci O op R current rows group y ticks nesting lock sched
 bc byloc bt base row bi bl bd duration Nn Gn Ln Nl Gl Ll Bd Ld Positive Nc Gc YBinding PointerRead Row Base Limit Bound Owned.
 destruct(V293_dly_raw_y_assignment P
 (kseq(V293_dly_after_y current rows group y)(V293_dly_after_y_cont current ticks sched ks))
 ge le M ir(enabled,si,ci)O op R current y bc byloc bt base row
 Nc Gc YBinding PointerRead Row Base Limit Bound Owned)as(Mf&Store&Write&After&Frame).
 exists Mf;split;[exact Store| ];split;[ |split;assumption].
 eapply V293_local_trans.
 { apply V293_csteps_local;eapply V293_dly_body_enters_positive;eassumption. }
 unfold V293_dly_positive.
 eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sseq_step]| ].
 eapply V293_local_cons;[apply encrit_step;reflexivity| ].
 eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sskip_step]| ].
 eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sseq_step]| ].
 unfold V293_dly_updates,V293_dly_before_delay.
 eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sseq_step]| ].
 eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sseq_step]| ].
 eapply V293_local_trans;[apply V293_csteps_local;exact Write| ].
 eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sskip_step]| ].
 apply V293_local_refl.
Qed.
