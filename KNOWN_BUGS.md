# Known counterexample classes and V2.93.01 obligations

## K1 — timeout / suspend / resume state split

Upstream V2.93.01 has an independent `OSTCBStatPend` result field.  Timeout
clears the event-wait status and records `OS_STAT_PEND_TO`; suspension and
resumption therefore do not rely on leaving an event-wait bit set until the
blocked API continuation runs.

**Project status:** upstream regression obligation; no custom patch permitted.
The Coq model must show that timeout followed by suspend/resume can re-enter the
ready set while preserving the timeout result.

## K2 — mutex deletion / priority-table / ready-table coherence

Upstream V2.93.01 restores the owner priority before clearing the mutex ceiling
slot in the historical single-mutex deletion scenario.  The exact source-level
proof must establish the invariant that every ready priority resolves to a
valid corresponding TCB.

**Project status:** upstream regression obligation; no custom patch permitted
for the already-corrected path.

## K3 — nested-mutex stale restoration priority

A task can own two mutexes while its effective priority changes through more
than one inheritance level.  If one mutex releases an intermediate priority
slot and another mutex later restores the task to that saved intermediate
value, the slot may already belong to a newly created task.  The later restore
can then create two live tasks at the same priority and overwrite the new
task's priority-table entry.

**Project status:** custom repair required.  Restoration must be recomputed from
the owner's base priority and the still-active mutex contributions rather than
from a stale intermediate saved value.

## K4 — scheduler-locked self-delete recycles the live TCB

A task can lock scheduling, delete itself, return its own TCB to the free list,
continue executing because scheduling is still locked, create another task that
reuses the same TCB/priority, and then unlock.  A priority-only scheduler check
can observe the same numeric priority and perform no context switch, leaving the
old execution context running while the TCB describes the new task.

**Project status:** custom repair required.  A locked current-task deletion is
rejected before any destructive mutation or resource release.
