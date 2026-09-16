# CertiUCOS-II V2.93.01 — Coq 8.18 verification

This repository is a clean verification target for **official uC/OS-II
V2.93.01**, pinned to commit
`0c4a48e6fbc6e915714e816196619a5481accf0c`.

The active goal is source-level functional correctness and safety for one fixed
configuration.  Optional services that are not in the selected scope are kept
disabled; the project does not attempt to verify every possible uC/OS-II build
configuration.

Two upstream behaviors are retained as explicit repair obligations:

1. nested-mutex priority restoration must not restore a stale intermediate
   inherited priority or overwrite another live task's priority-table entry;
2. deleting the currently executing task while the scheduler is already locked
   must not recycle its TCB while the old execution context can continue.

The upstream V2.93.01 mechanisms for independent pend-result state and
TCB-pointer mutex ownership are treated as native implementation behavior, not
as project-specific patches.

## Layout

- `framework/`, `tactics/` — version-independent CertiOS/CoqImp proof framework.
- `certiucos/v293/` — the only active OS-specific Coq development.
- `csrc/UPSTREAM.lock.json` — immutable upstream identity and source hashes.
- `csrc/config/v29301-profile.json` — fixed verification configuration.
- `csrc/repairs/` — only the two authorized V2.93.01 repairs.
- `scripts/` — source fetch/hash audit, config generation, and project audits.
- `audit/` — V2.93-specific machine evidence and generated reports.

## First use

```bash
make audit
make fetch-source
make build
```

`make fetch-source` fetches exactly the pinned commit and rejects any source
whose SHA-256 differs from the lock file.  No older kernel source is used as a
substitute.

The current repository is a **retargeted proof foundation**, not a completed
kernel proof.  The final source-linked `GOOD_OS` theorem remains open until all
configured functions have exact models/specifications, local Hoare proofs, and
program-level linkage.
