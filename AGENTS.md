# Agent instructions — V2.93.01 only

1. The only active kernel target is official uC/OS-II V2.93.01 at commit
   `0c4a48e6fbc6e915714e816196619a5481accf0c`, plus exactly the two repairs
   authorized in `PROJECT_SCOPE.md`.
2. Do not import, recreate, rename, or mechanically port an older OS proof tree.
   Reuse is allowed only for genuinely version-independent `framework/` or
   `tactics/` results.
3. Do not expand the configuration.  Multi-pend, timer manager, names,
   profiling, task registers, debug tables, tick-step support, and application
   hooks stay outside the active target unless the user explicitly changes the
   scope.
4. Functional correctness and safety are the verification goals.  Do not add
   unrelated property families.
5. Before modeling a C function, locate its exact configured V2.93.01 body and
   record its source hash/locator.  No source body may be substituted from
   another release.
6. The native V2.93.01 pend-result field and TCB-pointer mutex-owner check are
   upstream behavior, not project patches.  Prove them directly from upstream
   source.
7. The only current custom repair families are nested-mutex priority restoration
   and locked self-delete.  Any new repair requires a reproducible
   functional/safety counterexample and explicit user decision.
8. No `Admitted`, `admit`, new `Axiom`, `Parameter`, or `Conjecture` in
   `certiucos/v293`.
9. Every completed configured function must move through the machine-readable
   coverage states: located, modeled, specified, local Hoare, component linked,
   full-target linked.
10. Prefer vertical integration over proof-file proliferation.  Each function
    exposes one stable facade theorem used by the top-level program.
11. Do not begin compiler, ABI, binary, or hardware correctness work before the
    source-level `GOOD_OS` theorem is closed.
12. Keep Git checkpoints small, reproducible, and buildable.  Never use
    destructive cleanup to hide an unresolved proof or source mismatch.
