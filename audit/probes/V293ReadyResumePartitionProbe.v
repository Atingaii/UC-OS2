(* Original selected endpoint and a separate restored-suffix resource test.
   The suffix test does not identify the new task with the suspended task. *)
Require Import CertiOS.audit.probes.V293ReadyOwnedGlobalSwitchProbe.
Require Import CertiOS.audit.probes.V293ReadyOwnedSchedCallProbe.
Require Import CertiOS.audit.probes.V293TimeDlyCallGlobalProbe.
Require Import CertiOS.audit.probes.V293TimeDlyAllocatedProbe.
Require Import CertiOS.audit.probes.V293TimeDlyCallEntryProbe.
Require Import CertiOS.audit.probes.V293TimeDlySwitchProbe.
Require Import CertiOS.audit.probes.V293TimeDlyEntryProbe.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyResumePartition.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyGlobalTrace.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyOwnedGlobalSwitch.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293ClientSkipTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293ReturnClientTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyFullCall.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.simulation.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition DRG:=V293_ready_inv 30%positive 31%positive 83%positive.
Definition DRpartition c bs M:=
 (DWge,DCle,M,(fun _:hid=>false),(true,nil,nil),DGabs,spec_done None)|=
 (INV DRG **RDYINV DRG OwnershipWaiting) **DGframe c bs.

Theorem DRglobal_partition:forall c enabled,exists bs M,
 V293_global_steps DAprog DXclient(DXinitial c enabled)(DXfinal enabled bs M) /\
 DGpost c bs M /\DRpartition c bs M /\
 (forall a tp v,In(a,tp,v)(DOcells c) ->load tp M a=Some v) /\
 V293_bytes_writable M bs 0%Z 4 /\V293_bytes_writable M 13%positive 0%Z 4.
Proof.
 intros c enabled;destruct(DGglobal_switch c enabled)
 as(bs&y&My&Mh&Mcut&M&Prefix&Before&Free&Dead&Run&Step&Store&Post&Rest).
 destruct(DGobserved c bs M Post)as[Cells[CPU[Writable[OldCPU OldWritable]]]].
 exists bs;exists M;split;[exact Run| ];split;[exact Post| ];split.
 - unfold DRpartition,DRG;apply V293_ready_full_runtime_partition;
   [reflexivity|intro E;discriminate|exact Post].
 - split;[exact Cells| ];split;assumption.
Qed.

(* All three pieces rejoin to the exact actual heap and abstract total.
   INV and RDYINV are universal in the abstract operation, not snapshots. *)
Theorem DRglobal_partition_pieces:forall c enabled,exists bs M Ms Mt Mr Mtail Os Ot Or Otail,
 V293_global_steps DAprog DXclient(DXinitial c enabled)(DXfinal enabled bs M) /\
 DGpost c bs M /\
 join Mt Mr Mtail /\join Ms Mtail M /\join Ot Or Otail /\join Os Otail DGabs /\
 satp(DWge,DCle,Ms,(fun _:hid=>false),(true,nil,nil))Os(INV DRG) /\
 satp(DWge,DCle,Mt,(fun _:hid=>false),(true,nil,nil))Ot(RDYINV DRG OwnershipWaiting) /\
 (DWge,DCle,Mr,(fun _:hid=>false),(true,nil,nil),Or,spec_done None)|=DGframe c bs /\
 ~(Ms=(emp:mem) /\Os=(emp:osabst)).
Proof.
 intros c enabled;destruct(DRglobal_partition c enabled)as(bs&M&Run&Post&Partition&Rest).
 assert(Packed:(DWge,DCle,M,(fun _:hid=>false),(true,nil,nil),DGabs,spec_done None)|=
 INV DRG **(RDYINV DRG OwnershipWaiting **DGframe c bs)).
 { unfold DRpartition in Partition;clear -Partition;sep auto. }
 apply sat_split in Packed;destruct Packed as(Ms&Mtail&Os&Otail&JM&JO&Shared&Tail).
 apply sat_split in Tail;destruct Tail as(Mt&Mr&Ot&Or&JMt&JOt&Task&Frame).
 exists bs;exists M;exists Ms;exists Mt;exists Mr;exists Mtail;
 exists Os;exists Ot;exists Or;exists Otail.
 split;[exact Run| ];split;[exact Post| ];split;[exact JMt| ];split;[exact JM| ];
 split;[exact JOt| ];split;[exact JO| ];split.
 - intro ab;eapply INV_irrev_prop;exact Shared.
 - split.
   + eapply V293_return_ready_all_operations;exact Task.
   + split;[exact Frame| ];intros[EM EO];subst Ms Os.
     eapply V293_ready_enabled_empty_rejected;[reflexivity|exact Shared].
Qed.

Theorem DRboth_IE:forall c,
 (exists bs M,V293_global_steps DAprog DXclient(DXinitial c false)(DXfinal false bs M) /\DRpartition c bs M) /\
 (exists bs M,V293_global_steps DAprog DXclient(DXinitial c true)(DXfinal true bs M) /\DRpartition c bs M).
Proof.
 intro c;split;
 [destruct(DRglobal_partition c false)as(bs&M&Run&Post&Part&Rest)|
 destruct(DRglobal_partition c true)as(bs&M&Run&Post&Part&Rest)];
 exists bs;exists M;split;assumption.
Qed.

(* Only resource placement is neutralized; same actual execution, IE,
   full records, CPU permissions, counter and canary precede the late gate. *)
Theorem DRenabled_placement_ablation:forall c enabled,exists bs M,
 V293_global_steps DAprog DXclient(DXinitial c enabled)(DXfinal enabled bs M) /\
 DGpost c bs M /\DRpartition c bs M /\
 (forall a tp v,In(a,tp,v)(DOcells c) ->load tp M a=Some v) /\
 V293_bytes_writable M bs 0%Z 4 /\V293_bytes_writable M 13%positive 0%Z 4 /\
 ~((DWge,DCle,(emp:mem),(fun _:hid=>false),(true,nil,nil),(emp:osabst),spec_done None)|=INV DRG).
Proof.
 intros c enabled;destruct(DRglobal_partition c enabled)as(bs&M&Run&Post&Part&Cells&CPU&OldCPU).
 exists bs;exists M;split;[exact Run| ];split;[exact Post| ];split;[exact Part| ];
 split;[exact Cells| ];split;[exact CPU| ];split;[exact OldCPU| ].
 apply V293_ready_enabled_empty_rejected;reflexivity.
Qed.

Definition DRrest c:=V293_owned_record_cells(DOcells c) **
 (Amapsto(13%positive,0%Z)Tint32 true(Vint32 Int.zero) **
 V293_read_bytes 80%positive 0%Z V293_ready_table).

(* A genuine nonempty owned fixture tests both saved IE suffixes.
   Its kstop return context is intentionally not the nested DAcontinuation.
   No intervening global resumption of OwnershipReady is claimed. *)
Theorem DRrestored_suffix:forall c top,exists bs Mcut Mt Mr Ot Or,
 DXrun c top bs Mcut /\DOpost c top bs Mcut /\
 join Mt Mr Mcut /\join Ot Or(DEfinalabs(Int.repr 3)) /\
 (DWge,V293_cpu_lenv 501%Z bs,Mr,(fun _:hid=>false),(false,nil,(top::nil)),Or,spec_done None)|=DRrest c /\
 TaskSim DAprog
 (SKIP,(kenil,kseq(sprim excrit)(kseq sret(kcall 112%Z
 (V293_OSSched_success_body 501%Z 110%Z 111%Z 113%Z 117%Z 115%Z 116%Z 118%Z 119%Z)DCle kstop))))
 (DWge,V293_cpu_lenv 501%Z bs,Mt,(fun _:hid=>false),(false,nil,(top::nil)))
 DWhighprog(SKIP,(kenil,kstop))Ot V293_shared_li DRG
 (fun st=>satp(fst st)(snd st)(RDYINV DRG OwnershipReady **LINV V293_shared_li OwnershipReady nil))OwnershipReady.
Proof.
 intros c top;destruct(DOglobal_sched c top)
 as(bs&y&Mb&Mi&My&Mh&Mtarget&Mcut&Block&Initial&Run&F&FY&Free&Dead&Calls&Count&Owned&Target&Counter).
 assert(Open:(DWge,V293_cpu_lenv 501%Z bs,Mcut,(fun _:hid=>false),(false,nil,(top::nil)),
 DEfinalabs(Int.repr 3),spec_done None)|=
 V293_ready_full 30%positive 31%positive 83%positive OwnershipReady **DGframe c bs).
 { eapply V293_owned_switch_active_view;[apply DGframe_good|exact Owned]. }
 assert(Packed:(DWge,V293_cpu_lenv 501%Z bs,Mcut,(fun _:hid=>false),(false,nil,(top::nil)),
 DEfinalabs(Int.repr 3),spec_done None)|=
 (Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **
 V293_ready_full 30%positive 31%positive 83%positive OwnershipReady) **DRrest c).
 { unfold DRrest,DGframe in *;clear -Open;sep auto. }
 apply sat_split in Packed;destruct Packed as(Mt&Mr&Ot&Or&JM&JO&Local&Frame).
 exists bs;exists Mcut;exists Mt;exists Mr;exists Ot;exists Or.
 split;[exact Run| ];split;[exact Owned| ];split;[exact JM| ];split;[exact JO| ];split;[exact Frame| ].
 eapply V293_ready_full_pending_TaskSim;[reflexivity|right;right;reflexivity|reflexivity|exact Local].
Qed.
