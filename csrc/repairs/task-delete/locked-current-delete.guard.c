/* V2.93.01 repair insertion point: immediately after OSTaskDel has resolved
 * prio and validated ptcb, before any ready/wait/resource mutation.
 */
if ((ptcb == OSTCBCur) && (OSLockNesting > 0u)) {
    OS_EXIT_CRITICAL();
    return (OS_ERR_SCHED_LOCKED);
}
