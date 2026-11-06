(* Independent controls for the actual byte-local allocation transition. *)
Require Import CertiOS.certiucos.v293.proofs.V293SchedHelperTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293ReadySchedCall.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.memory_prop.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Lemma HAallocation : forall p y ks ge M b,
 fresh M b ->
 cstep p(curs(salloc nil(dcons y Tint8 dnil)),(kenil,ks))(ge,(emp:env),M)
  (curs(salloc nil dnil),(kenil,ks))
  (ge,set(emp:env)y(b,Tint8),allocb M b 0%Z(typelen Tint8)).
Proof.
 intros p y ks ge M b Fresh;eapply stmt_step;[reflexivity| ].
 eapply salloclv_step;[reflexivity|reflexivity| ].
 exists b;split;[exact Fresh| ];split;[reflexivity| ];split;[ |reflexivity].
 intros[v E];rewrite map_emp_get in E;discriminate E.
Qed.

Lemma HAtwo_real_successors : forall p y ks ge M,
 exists b c,
 fresh M b /\fresh M c /\b<>c /\
 cstep p(curs(salloc nil(dcons y Tint8 dnil)),(kenil,ks))(ge,(emp:env),M)
  (curs(salloc nil dnil),(kenil,ks))
  (ge,set(emp:env)y(b,Tint8),allocb M b 0%Z(typelen Tint8)) /\
 cstep p(curs(salloc nil(dcons y Tint8 dnil)),(kenil,ks))(ge,(emp:env),M)
  (curs(salloc nil dnil),(kenil,ks))
  (ge,set(emp:env)y(c,Tint8),allocb M c 0%Z(typelen Tint8)) /\
 (ge,set(emp:env)y(b,Tint8),allocb M b 0%Z(typelen Tint8))<>
 (ge,set(emp:env)y(c,Tint8),allocb M c 0%Z(typelen Tint8)).
Proof.
 intros p y ks ge M;destruct(memory_has_fresh_block M)as[b FB].
 destruct(V293_ready_fresh_avoiding M[b])as(c&FC&Avoid).
 assert(BC:b<>c)by(intro E;subst;apply Avoid;left;reflexivity).
 exists b;exists c;split;[exact FB| ];split;[exact FC| ];split;[exact BC| ];split.
 - apply HAallocation;exact FB.
 - split;[apply HAallocation;exact FC| ].
   intro E;injection E;intros EM EL;contradiction.
Qed.

Lemma HAno_fixed_successor : forall p y ks ge M,
 ~exists Cf mf,forall C' m',
 cstep p(curs(salloc nil(dcons y Tint8 dnil)),(kenil,ks))(ge,(emp:env),M)C' m' ->
 C'=Cf /\m'=mf.
Proof.
 intros p y ks ge M(Cf&mf&Unique).
 destruct(HAtwo_real_successors p y ks ge M)as(b&c&FB&FC&BC&SB&SC&Different).
 destruct(Unique _ _ SB)as[_ MB];destruct(Unique _ _ SC)as[_ MC].
 apply Different;congruence.
Qed.

Lemma HAframe_excludes_old_choice : forall M b,
 fresh M b ->~fresh(allocb M b 0%Z(typelen Tint8))b /\
 exists c,c<>b /\fresh(allocb M b 0%Z(typelen Tint8))c.
Proof.
 intros M b Fresh;split.
 - intro F;destruct(allocb_get_some M b(typelen Tint8)0%Z 0)as[v Read];[cbn;lia| ].
   eapply(F (b,0%Z) 0%Z);[reflexivity|exists(true,v);exact Read].
 - destruct(V293_ready_fresh_avoiding(allocb M b 0%Z(typelen Tint8))[b])as(c&FC&Avoid).
   exists c;split;[intro E;subst;apply Avoid;left;reflexivity|exact FC].
Qed.

(* The unchanged linked helper reaches its body with any allowed local block. *)
Lemma HAhelper_real_prefix : forall p f unmap group rows high y ks ge caller M b,
 p f=Some(V293_OSSchedNew_function unmap group rows high y) ->fresh M b ->
 cstepstar p(curs(scall f nil),(kenil,ks))(ge,caller,M)
  (curs(V293_OSSchedNew_body unmap group rows high y),
   (kenil,kcall f(V293_OSSchedNew_body unmap group rows high y)caller ks))
  (ge,set(emp:env)y(b,Tint8),allocb M b 0%Z(typelen Tint8)).
Proof.
 intros p f unmap group rows high y ks ge caller M b Bind Fresh.
 eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply snpcall_step]| ].
 eapply c_stepstarn.
 { eapply stmt_step;[reflexivity| ];eapply sfexec_step with(d1:=dnil)(d2:=dcons y Tint8 dnil);
  [reflexivity|reflexivity|exact Bind|exact I|reflexivity]. }
 eapply c_stepstarn;[apply HAallocation;exact Fresh| ].
 eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply sallocend_step]|apply c_stepstar0].
Qed.
