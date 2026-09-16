# Roadmap

## Gate 0 — clean retarget

- one V2.93.01 upstream commit and source hash lock;
- one fixed configuration profile;
- no old OS-specific proof tree in the active repository;
- no proof holes in `certiucos/v293`;
- only two authorized repair families.

## Gate 1 — source inventory and repair freeze

1. Fetch and hash-check V2.93.01.
2. Generate effective `os_cfg.h` and verify its expected hash.
3. Preprocess the configured portable master translation unit.
4. Enumerate every configured public, internal, CPU-hook, and assembly body.
5. Implement the two repairs as minimal source patches against the pinned tree.
6. Run concrete regression fixtures for K1–K4 and freeze the repaired source
   manifest.

No Coq function is counted as source-modeled before the corresponding repaired
or upstream body is frozen and uniquely located.

## Gate 2 — common state and invariants

Build V2.93.01-specific concrete types and abstract state for TCBs, event
objects, ready tables, priority tables, queues, flags, memory partitions,
interrupt/task-switch boundaries, and initialization.

Global invariants must imply at least:

- ready-table / priority-table / TCB coherence;
- unique active task priorities;
- timeout/wait/pend-result consistency;
- nested-mutex base/effective priority consistency;
- the TCB backing the currently executing context is allocated and not reusable.

## Gate 3 — vertical function proofs

Maintain one machine-readable coverage row per configured source body:

`located -> modeled -> specified -> local Hoare -> component linked -> full target linked`

A large number of local lemmas is not a completion metric.  Each completed
function exposes one stable facade theorem used by the program-level proof.

## Gate 4 — program integration

Define and freeze:

- `V293_low_level_os_code`;
- `V293_os_spec`;
- `V293_ucos_init`.

Prove domain equality, every API/internal/interrupt obligation, initialization,
and program-level simulation/refinement.  The final theorem must be connected
to the complete configured function inventory.

## Gate 5 — final audit

- clean full build on Coq 8.18.0;
- `Print Assumptions` for final roots;
- `coqchk` for the dependency closure;
- no active `Admitted/admit` or new unreviewed axioms;
- K1–K4 regression theorems connected to the same repaired program;
- clean Git worktree and immutable release tag.

Compiler/binary/hardware refinement is explicitly outside these gates.
