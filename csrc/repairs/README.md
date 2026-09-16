# Authorized V2.93.01 repairs

This directory is intentionally small.  It contains only the two source-level
changes allowed by `PROJECT_SCOPE.md`.

## 1. Nested mutex restoration

The repair must distinguish a task's base priority from its current effective
priority.  A mutex acquisition stores the owner's base priority, and release or
deletion recomputes the effective priority from the base plus every mutex still
owned by that task.  Restoration may not write through a priority-table slot
owned by another live task.

`nested-mutex/protocol.c` is the repair algorithm to integrate into the exact
pinned `os_mutex.c`; it is not counted as applied until the post-fetch patch
step and concrete regression suite both pass.

## 2. Scheduler-locked current-task deletion

Before destructive mutation, `OSTaskDel` checks whether the selected TCB is
`OSTCBCur` while `OSLockNesting > 0`.  If so it exits the critical section and
returns existing error `OS_ERR_SCHED_LOCKED` (50).  The task, TCB, resources,
ready state, and lock count remain unchanged.

No additional error code is introduced.
