Require Import CertiOS.audit.probes.V293ReadySchedCallProbe.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.simulation.
Require Import CertiOS.framework.proof.step_prop.
Require Import CertiOS.framework.proof.join_prop.
Require Import CertiOS.framework.auxlibs.MapLib.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.certiucos.v293.proofs.V293SchedCallEntryProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293ReadySchedCall.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCallGlobal.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.audit.probes.V293ReadyCriticalGlobalProbe.
Require Import CertiOS.audit.probes.V293HandoffProgSimProbe.
Require Import CertiOS.audit.probes.V293SwitchProgSimProbe.
Require Import CertiOS.audit.probes.V293ReadyFullCallProbe.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.audit.probes.V293ReadyTaskInvariantProbe.
Require Import Lia.
Require Import Coq.Lists.List.
Import ListNotations.

Definition CEM:=CGmemory OwnershipWaiting true 0 0.
Definition CEbody:=V293_OSSchedNew_body 100%Z 101%Z 102%Z 103%Z 104%Z.
Definition CEks:=kcall 107%Z CEbody CGle HPpending.
Definition CEcode:code:=(curs(salloc nil(dcons 104%Z Tint8 dnil)),(kenil,CEks)).
Definition CEnext:code:=(curs(salloc nil dnil),(kenil,CEks)).
Definition CET:tasks:=set HPtasks OwnershipWaiting CEcode.
Definition CEles:cltenvs:=set CGswitch_envs OwnershipWaiting(emp:env).
Definition CES enabled ci:osstate:=
 (CGge,CEles,CEM,(fun _=>false),CGswitch_aux enabled ci).
Definition CEMb b:=allocb CEM b 0%Z 1.
Definition CELb b:env:=set emp 104%Z(b,Tint8).
Definition CESb b enabled ci:osstate:=
 (CGge,set CEles OwnershipWaiting(CELb b),CEMb b,(fun _=>false),CGswitch_aux enabled ci).

Lemma CEbound : CGpo 107%Z=Some(V293_OSSchedNew_function 100%Z 101%Z 102%Z 103%Z 104%Z).
Proof. vm_compute;reflexivity. Qed.

Lemma CEtyped_heap : forall ci,CGstate OwnershipWaiting CEM ci |=
 SWINVt(V293_ready_inv 80%positive 81%positive 82%positive)OwnershipWaiting **
 (V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval 88) **
 (V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipWaiting) **
 (V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval 6) **
 (V293_owned_record_cell((95%positive,0%Z),Tint32,Vint32 Int.mone) ** CGframe 0 0)))).
Proof. intro ci;apply CGentry;lia. Qed.

Theorem CEall_fresh_global_progress : forall b enabled ci ip,fresh CEM b ->
 lpstep(RCprogram,(CGpo,CGempty,ip))CET HPcst(CES enabled ci)OwnershipWaiting
 (set CET OwnershipWaiting CEnext)HPcst(CESb b enabled ci)OwnershipWaiting.
Proof.
 intros b enabled ci ip Fresh;unfold CET,CES,CESb,CEles,CELb,CEMb.
 eapply V293_os_family_progress with(le:=(emp:env))(si:=nil)(cs:=enabled::ci).
 - apply map_get_set.
 - apply map_get_set.
 - apply map_get_set.
 - unfold CEcode,CEks,CEbody;eapply V293_bound_call_inos;exact CEbound.
 - unfold CEcode,CEnext;apply V293_byte_alloc_step;exact Fresh.
Qed.

Theorem CEall_global_successors : forall enabled ci ip Tf cf Sf tf,
 lpstep(RCprogram,(CGpo,CGempty,ip))CET HPcst(CES enabled ci)OwnershipWaiting Tf cf Sf tf ->
 exists b,fresh CEM b /\ Tf=set CET OwnershipWaiting CEnext /\ cf=HPcst /\
 Sf=CESb b enabled ci /\ tf=OwnershipWaiting.
Proof.
 intros enabled ci ip Tf cf Sf tf H.
 assert(In:InOS CEcode(pumerge CGpo CGempty)).
 { unfold CEcode,CEks,CEbody;eapply V293_bound_call_inos;exact CEbound. }
 assert(Progress:exists C' m',cstep(pumerge CGpo CGempty)CEcode(CGge,(emp:env),CEM)C' m').
 { destruct(memory_has_fresh_block CEM)as[b F];do 2 eexists;apply V293_byte_alloc_step;exact F. }
 destruct(V293_os_family_all_successors RCprogram CGpo CGempty ip CET HPcst OwnershipWaiting
 CEcode CGge(emp:env)CEles CEM(fun _=>false)(CGswitch_aux enabled ci)nil(enabled::ci)
 ltac:(unfold CEles;apply map_get_set)ltac:(apply map_get_set)ltac:(apply map_get_set)
 In Progress Tf cf Sf tf H)as(C'&g'&l'&M'&Step&Task&Client&State&Thread).
 destruct(V293_byte_alloc_successor _ _ _ _ _ _ _ Step)as(b&Fresh&Code&Memory).
 inversion Memory;subst g' l' M';subst C'.
 exists b;split;[exact Fresh| ];split;[exact Task| ];split;[exact Client| ];
 split;[exact State|exact Thread].
Qed.

(* Same heap, function, continuation and caller; only the fresh block changes. *)
Theorem CEtwo_fresh_successors : forall enabled ci ip,
 exists b1 b2,fresh CEM b1 /\ fresh CEM b2 /\ b1<>b2 /\
 lpstep(RCprogram,(CGpo,CGempty,ip))CET HPcst(CES enabled ci)OwnershipWaiting
 (set CET OwnershipWaiting CEnext)HPcst(CESb b1 enabled ci)OwnershipWaiting /\
 lpstep(RCprogram,(CGpo,CGempty,ip))CET HPcst(CES enabled ci)OwnershipWaiting
 (set CET OwnershipWaiting CEnext)HPcst(CESb b2 enabled ci)OwnershipWaiting /\
 CELb b1<>CELb b2 /\ CEMb b1<>CEMb b2.
Proof.
 intros enabled ci ip.
 destruct(V293_ready_fresh_avoiding CEM [])as(b1&F1&N1).
 destruct(V293_ready_fresh_avoiding CEM [b1])as(b2&F2&N2).
 assert(Different:b1<>b2)by(intro E;apply N2;simpl;left;exact E).
 assert(Locals:CELb b1<>CELb b2).
 { intro E;assert(A:get(CELb b1)104%Z=Some(b1,Tint8))by(apply map_get_set).
   assert(B:get(CELb b2)104%Z=Some(b2,Tint8))by(apply map_get_set).
   rewrite E in A;rewrite B in A;inversion A;congruence. }
 assert(Heaps:CEMb b1<>CEMb b2).
 { intro E.
   assert(A:get(CEMb b1)(b1,0%Z)=Some(true,Undef)).
   { unfold CEMb;cbn[allocb];apply map_get_set. }
   assert(B:get(CEMb b2)(b1,0%Z)=None).
   { unfold CEMb;rewrite V293_success_allocb_outside by(left;congruence).
     apply V293_success_fresh_none;exact F1. }
   rewrite E in A;rewrite B in A;discriminate. }
 exists b1;exists b2;split;[exact F1| ];split;[exact F2| ];split;[exact Different| ];
 split;[apply CEall_fresh_global_progress;exact F1| ];
 split;[apply CEall_fresh_global_progress;exact F2| ];split;assumption.
Qed.

Theorem CEunique_allocation_rejected :
 ~exists C' m',forall Cf mf,cstep CGprogram CEcode(CGge,(emp:env),CEM)Cf mf ->
 Cf=C' /\ mf=m'.
Proof.
 intros(C'&m'&Unique).
 destruct(CEtwo_fresh_successors true nil(fun _=>None))as(b1&b2&F1&F2&Different&StepFirst&StepSecond&LocalDifferent&MemoryDifferent).
 pose proof(V293_byte_alloc_step CGprogram 104%Z CEks CGge CEM b1 F1)as A.
 pose proof(V293_byte_alloc_step CGprogram 104%Z CEks CGge CEM b2 F2)as B.
 destruct(Unique _ _ A)as[_ EA];destruct(Unique _ _ B)as[_ EB].
 change((CGge,CELb b1,CEMb b1)=m')in EA.
 change((CGge,CELb b2,CEMb b2)=m')in EB.
 apply LocalDifferent.
 exact(f_equal(fun sm:smem=>snd(fst sm))(eq_trans EA(eq_sym EB))).
Qed.

(* The actual body remains a universal, visible obligation, not a proved post. *)
Theorem CEactual_call_entry : forall enabled ci ip ph Th O,
 get O curtid=Some(oscurt OwnershipWaiting) ->
 (forall b,fresh CEM b ->
 ProgSim(RCprogram,(CGpo,CGempty,ip))
 (set HPtasks OwnershipWaiting(curs CEbody,(kenil,CEks)))
 (CGge,set CGswitch_envs OwnershipWaiting(CELb b),CEMb b,(fun _=>false),CGswitch_aux enabled ci)
 ph Th O HPcst OwnershipWaiting) ->
 ProgSim(RCprogram,(CGpo,CGempty,ip))
 (set HPtasks OwnershipWaiting(curs(scall 107%Z nil),(kenil,HPpending)))
 (SPS CEM enabled ci)ph Th O HPcst OwnershipWaiting.
Proof.
 intros enabled ci ip ph Th O Cur Post;unfold SPS.
 eapply V293_sched_call_entry_progsim with(caller:=CGle)(si:=nil)(cs:=enabled::ci)
 (unmap:=100%Z)(group:=101%Z)(rows:=102%Z)(high:=103%Z)(y:=104%Z);try eassumption.
 - exact CEbound.
 - apply map_get_set.
 - apply map_get_set.
 - apply map_get_set.
 - exact HPcontext.
 - intros b Fresh;rewrite <-set_set_eq;apply Post;exact Fresh.
Qed.

Theorem CEactual_prefix_all_fresh : forall b,fresh CEM b ->
 cstepstar CGprogram(curs(scall 107%Z nil),(kenil,HPpending))(CGge,CGle,CEM)
 (curs CEbody,(kenil,CEks))(CGge,CELb b,CEMb b) /\
 get(CELb b)104%Z=Some(b,Tint8) /\ get(CELb b)120%Z=None /\
 get(CEMb b)(b,0%Z)=Some(true,Undef).
Proof.
 intros b Fresh;split.
 - eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply snpcall_step]| ].
   eapply c_stepstarn.
   { eapply stmt_step;[reflexivity| ].
     eapply sfexec_step with(d1:=dnil)(d2:=dcons 104%Z Tint8 dnil);
     [reflexivity|reflexivity|exact CEbound|exact I|reflexivity]. }
   eapply c_stepstarn;[apply V293_byte_alloc_step;exact Fresh| ].
   eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply sallocend_step]| ].
   apply c_stepstar0.
 - split;[apply map_get_set| ];split.
   + unfold CELb;rewrite map_get_set' by discriminate;apply map_emp_get.
   + unfold CEMb;cbn[allocb];apply map_get_set.
Qed.
