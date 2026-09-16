/* V2.93.01 nested-mutex repair algorithm.
 * Integration into the pinned os_mutex.c remains a source-freeze gate.
 * These helpers execute under the caller's existing critical section.
 */

static INT8U  OSMutex_BasePrio(OS_TCB *ptcb)
{
    INT8U     index;
    INT8U     base;
    INT8U     saved;
    OS_EVENT *other;

    base = ptcb->OSTCBPrio;
    for (index = 0u; index < OS_MAX_EVENTS; ++index) {
        other = &OSEventTbl[index];
        if ((other->OSEventType == OS_EVENT_TYPE_MUTEX) &&
            (other->OSEventPtr  == (void *)ptcb)) {
            saved = (INT8U)(other->OSEventCnt & OS_MUTEX_KEEP_LOWER_8);
            if ((saved != OS_MUTEX_AVAILABLE) && (base < saved)) {
                base = saved;
            }
        }
    }
    return (base);
}

static INT8U  OSMutex_EffectivePrio(OS_TCB *ptcb,
                                    OS_EVENT *excluding,
                                    INT8U base)
{
    INT8U     index;
    INT8U     pcp;
    INT8U     effective;
    OS_EVENT *other;

    effective = base;
    for (index = 0u; index < OS_MAX_EVENTS; ++index) {
        other = &OSEventTbl[index];
        if ((other != excluding) &&
            (other->OSEventType == OS_EVENT_TYPE_MUTEX) &&
            (other->OSEventPtr  == (void *)ptcb)) {
            pcp = (INT8U)(other->OSEventCnt >> 8u);
            if ((pcp != OS_PRIO_MUTEX_CEIL_DIS) &&
                (OSTCBPrioTbl[pcp] == ptcb) &&
                (pcp < effective)) {
                effective = pcp;
            }
        }
    }
    return (effective);
}

/* The source integration must use OSMutex_BasePrio(OSTCBCur), rather than the
 * current effective OSTCBPrio, when a free mutex records its owner priority.
 * Post/Del must restore to OSMutex_EffectivePrio(owner, pevent, base).
 * The existing priority relocation code must preserve ready/event membership
 * and may not overwrite a priority-table entry belonging to another live TCB.
 */
