# Verification status

Status: **CLEAN V2.93.01 RETARGET — FOUNDATION OPEN**

## Completed by this refactor

- Fresh repository with no legacy OS-specific proof tree.
- Version-independent `framework/` and `tactics/` retained.
- Official V2.93.01 commit and 15 Source-file SHA-256 identities locked.
- Fixed configuration profile recorded; optional scope-expanding services are
  disabled.
- Active OS Coq namespace reset to `certiucos/v293/`.
- Regression-property foundations added for native pend-result behavior,
  nested-mutex effective-priority recomputation, and locked self-delete
  rejection.
- V2.93-specific upstream nested-mutex execution evidence retained as audit
  input.

## Not yet claimed

- Upstream checkout is not vendored in this artifact; run `make fetch-source`.
- Complete configured function inventory is not yet regenerated.
- The two source repairs are not yet integrated into the pinned upstream tree.
- No C-to-CoqImp translation coverage is yet claimed for V2.93.01 functions.
- No function-level source Hoare proof is yet counted.
- No full program linkage is yet counted.
- `V293_low_level_os_code`, `V293_os_spec`, `V293_ucos_init`, and the final
  `GOOD_OS` theorem remain open.

The small Coq regression models in the clean tree are specification foundations;
they must not be reported as source-level kernel verification until connected to
exact source statements and the final program.
