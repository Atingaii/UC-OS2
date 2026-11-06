(* Prospective single-factor call-type dispatch ablation. Only opt changes.
   cstep (not arbitrary interrupt/loststep); no downstream execution credit. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtFunction.
Require Import Coq.Lists.List.
Import ListNotations.
Definition CallFunction := V293_CreateExt_function 92%Z 97%Z 98%Z 99%Z 904%Z 900%Z 901%Z.
Definition CallProgram (f:fid) : option function :=
 if Z.eq_dec f 905%Z then Some CallFunction else None.
Definition CallArgs (valid:bool) :=
 [if valid then Vint32 Int.zero else Vnull;
 Vnull;Vint32 Int.zero;Vnull;Vint32 Int.zero;Vint32 Int.zero;
 Vnull;Vnull;Vint32(Int.repr 700)].
Definition CallGE : env := emp.
Definition CallCaller : env := set emp 777%Z (31%positive,Tint8).
Definition CallM : mem := emp.
Definition CallStart valid := (curs(sfexec 905%Z (CallArgs valid) V293_CreateExt_argument_types),(kenil,kstop)).
Definition CallAllocated :=
 (curs(salloc (CallArgs true) (revlcons V293_CreateExt_parameters V293_CreateExt_locals)),
 (kenil,kcall 905%Z (V293_CreateExt_body 92%Z 97%Z 98%Z 99%Z 904%Z 900%Z 901%Z) CallCaller kstop)).
Theorem CallTypedDispatch :
 cstep CallProgram (CallStart true) (CallGE,CallCaller,CallM)
 CallAllocated (CallGE,emp,CallM).
Proof.
 eapply stmt_step;[reflexivity| ].
 eapply sfexec_step with (d1:=V293_CreateExt_parameters) (d2:=V293_CreateExt_locals);
 try reflexivity. repeat split.
Qed.
Theorem CallUntypedNoDispatch :
 ~exists C' m', cstep CallProgram (CallStart false) (CallGE,CallCaller,CallM) C' m'.
Proof.
 intros (C'&m'&Step). unfold CallStart in Step. inversion Step;subst;try discriminate.
 all: match goal with E : (curs(sfexec _ _ _),_) = (_,_) |- _ => inversion E;subst;clear E end.
 - match goal with H:estep _ _ _ _ _ _ |- _ => inversion H end.
 - match goal with H:sstep _ _ _ _ _ _ _ |- _ => inversion H;subst;try discriminate end.
Qed.
Print Assumptions CallTypedDispatch.
Print Assumptions CallUntypedNoDispatch.
