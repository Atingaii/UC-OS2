# Verification scope

## Fixed target

- Kernel: official uC/OS-II V2.93.01.
- Commit: `0c4a48e6fbc6e915714e816196619a5481accf0c`.
- Configuration: generated from the official template using
  `csrc/config/v29301-profile.json`.
- Proof assistant: Coq 8.18.x; the intended acceptance environment is 8.18.0.

The target is one immutable configured program, not the space of all uC/OS-II
configuration combinations.

## Included functional families

The selected configuration keeps the ordinary core/task/time/event services
needed by the existing verification program: scheduler/core operations, task
management, semaphores, mailboxes, queues, mutexes, event flags, and memory
partitions.  The exact function inventory must be generated from the pinned,
preprocessed V2.93.01 source before function coverage is reported.

The project deliberately disables optional newer facilities that would expand
the target without serving the stated verification goal, including timer
manager, multi-pend, event/task/flag/memory naming, task profiling, task
registers, tick-step support, debug tables, and application hooks.

## Required repairs

Only two project-specific semantic changes are authorized:

1. **Nested mutex restoration.** Restoration is computed from the task's base
   priority plus the priority contributions of mutexes it still owns; a freed
   intermediate priority must never be reused as a delayed restoration target.
2. **Locked self deletion.** A currently executing task must be rejected before
   destructive deletion if the scheduler was already locked by that execution
   context.  Its TCB and resources remain allocated so that an unlock/retry can
   occur safely.

Any additional source change requires a concrete reproducible functional/safety
counterexample and an explicit scope decision before it becomes part of the
active target.

## Required proof result

The eventual top-level result is a source-linked theorem of the same semantic
kind as CertiOS `GOOD_OS`, instantiated with a V2.93.01 program,
specification, and initialization state.  Completion additionally requires
machine-checkable regression theorems excluding the four known counterexample
classes recorded in `KNOWN_BUGS.md`.

## Trusted boundary

The project accepts the framework's task-switch/interrupt abstraction boundary.
Compiler correctness, assembler/linker correctness, final machine-code
correctness, and concrete hardware semantics are not Phase-3 proof obligations.
They may be studied later, but they must not block the source-level `GOOD_OS`
theorem.
