# Clean retarget report

## Result

The repository has been reset to a single V2.93.01 verification target.

- Active OS-specific Coq tree: `certiucos/v293/` only.
- Version-independent proof base retained: `framework/` and generic tactic
  modules that do not import removed OS definitions.
- Upstream identity: pinned commit plus per-file hashes in
  `csrc/UPSTREAM.lock.json`.
- Configuration: one fixed profile in `csrc/config/v29301-profile.json`.
- Repair scope: exactly two families in `csrc/repairs/REPAIR_TARGET.json`.
- Function coverage starts from an empty machine-readable matrix; no historical
  local proof is counted toward the new target.

## Current machine checks

`python3 scripts/project-audit.py` verifies that:

- no legacy target identifier remains in the clean repository;
- the active V2.93 Coq tree contains no `Admitted`, `admit`, new `Axiom`,
  `Parameter`, or `Conjecture`;
- the upstream lock is present.

The current execution environment does not provide `coqc`, so this refactor
cannot claim a Coq 8.18 build result here.  The intended next acceptance step is
`make fetch-source && make build` in the target Coq 8.18.0 environment.
