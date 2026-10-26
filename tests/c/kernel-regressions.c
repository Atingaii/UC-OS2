/* Real configured kernel; executable, controlled CPU-boundary fixture.
 * The driver continues at API boundaries in the selected task's context.
 * It does NOT implement task stacks, asynchronous interrupts or a CPU proof.
 */
#include "ucos_ii.c"

static unsigned irq_disabled, critical_depth, deletion_hooks;
static void (*switch_action)(void);
static OS_TCB *owner, *waiter;
static OS_EVENT *first, *second;
static unsigned suspend_before_tick;
static INT8U delete_option = OS_DEL_ALWAYS;
static OS_STK stacks[4][128];

static void output(const char *s)
{
    unsigned n = 0, result;
    while (s[n]) ++n;
    __asm__ volatile ("int $0x80" : "=a"(result) : "0"(4), "b"(1), "c"(s), "d"(n) : "memory");
    (void)result;
}

static void number(unsigned value)
{
    char text[11];
    unsigned i = 10;
    text[i] = 0;
    do { text[--i] = (char)('0' + value % 10); value /= 10; } while (value);
    output(text + i);
}

static void die(const char *expression, unsigned line)
{
    output("FAIL line="); number(line); output(" expression="); output(expression); output("\n");
    __asm__ volatile ("int $0x80" : : "a"(1), "b"(2) : "memory");
    __builtin_unreachable();
}

#define REQUIRE(x) do { if (!(x)) die(#x, __LINE__); } while (0)

void V293_EnterCritical(OS_CPU_SR *saved)
{
    *saved = irq_disabled;
    irq_disabled = 1;
    ++critical_depth;
}

void V293_ExitCritical(OS_CPU_SR *saved)
{
    REQUIRE(critical_depth > 0);
    --critical_depth;
    irq_disabled = *saved;
}

static void select_highest(void)
{
    OS_SchedNew();
    OSTCBHighRdy = OSTCBPrioTbl[OSPrioHighRdy];
    REQUIRE(OSTCBHighRdy != (OS_TCB *)0);
    REQUIRE(OSTCBHighRdy != OS_TCB_RESERVED);
    REQUIRE(OSTCBHighRdy->OSTCBPrio == OSPrioHighRdy);
    OSTCBCur = OSTCBHighRdy;
    OSPrioCur = OSPrioHighRdy;
}

void OSCtxSw(void)
{
    unsigned saved_depth = critical_depth, saved_irq = irq_disabled;
    void (*action)(void) = switch_action;
    switch_action = 0;
    /* Other task segments run outside the suspended scheduler's critical
     * section. Restore that saved section when this boundary returns. */
    critical_depth = irq_disabled = 0;
    select_highest();
    if (action) action();
    REQUIRE(critical_depth == 0 && irq_disabled == 0);
    critical_depth = saved_depth;
    irq_disabled = saved_irq;
}

void OSIntCtxSw(void) { OSCtxSw(); }
void OSStartHighRdy(void) { select_highest(); }
void OSInitHookBegin(void) {}
void OSInitHookEnd(void) {}
void OSTaskCreateHook(OS_TCB *t) { (void)t; }
void OSTaskDelHook(OS_TCB *t) { (void)t; ++deletion_hooks; }
void OSTaskIdleHook(void) {}
void OSTaskReturnHook(OS_TCB *t) { (void)t; }
void OSTaskStatHook(void) {}
void OSTaskSwHook(void) {}
void OSTCBInitHook(OS_TCB *t) { (void)t; }
void OSTimeTickHook(void) {}
OS_STK *OSTaskStkInit(void (*task)(void *), void *arg, OS_STK *top, INT16U opt)
{ (void)task; (void)arg; (void)opt; return top; }

static void dummy_task(void *arg) { (void)arg; }

static OS_TCB *make_task(INT8U prio, unsigned stack)
{
    REQUIRE(OSTaskCreate(dummy_task, (void *)0, &stacks[stack][127], prio) == OS_ERR_NONE);
    return OSTCBPrioTbl[prio];
}

static void setup(void)
{
    OSInit();
    owner = make_task(10, 0);
    select_highest();
    REQUIRE(OSTaskSuspend(OS_TASK_STAT_PRIO) == OS_ERR_NONE);
    OSRunning = OS_TRUE;
    select_highest();
    REQUIRE(OSTCBCur == owner);
    REQUIRE(critical_depth == 0 && irq_disabled == 0);
}

static void ready_consistent(void)
{
    unsigned p;
    OS_TCB *a, *b;
    for (p = 0; p <= OS_LOWEST_PRIO; ++p) {
        unsigned y = p >> 3, bit = 1u << (p & 7);
        REQUIRE(((OSRdyGrp >> y) & 1u) == (OSRdyTbl[y] != 0));
        if ((OSRdyTbl[y] & bit) == 0) continue;
        a = OSTCBPrioTbl[p];
        REQUIRE(a && a != OS_TCB_RESERVED && a->OSTCBPrio == p);
    }
    for (a = OSTCBList; a; a = a->OSTCBNext)
        for (b = a->OSTCBNext; b; b = b->OSTCBNext)
            REQUIRE(a->OSTCBPrio != b->OSTCBPrio);
}

static void timeout_and_yield_owner(void)
{
    REQUIRE(OSTCBCur == owner);
    OSTimeTick();
    REQUIRE(waiter->OSTCBStatPend == OS_STAT_PEND_TO);
    REQUIRE(OSTaskSuspend(OS_PRIO_SELF) == OS_ERR_NONE);
    REQUIRE(OSTCBCur == waiter);
}

static void inherit(OS_EVENT *mutex, INT8U prio, unsigned stack)
{
    INT8U err = 255;
    waiter = make_task(prio, stack);
    REQUIRE(OSTCBCur == waiter);
    switch_action = timeout_and_yield_owner;
    OSMutexPend(mutex, 1, &err);
    REQUIRE(switch_action == 0);
    REQUIRE(OSTCBCur == waiter && err == OS_ERR_TIMEOUT);
    REQUIRE(OSTaskSuspend(OS_PRIO_SELF) == OS_ERR_NONE);
    REQUIRE(OSTaskResume(owner->OSTCBPrio) == OS_ERR_NONE);
    REQUIRE(OSTCBCur == owner);
    ready_consistent();
}

static void acquire(OS_EVENT *mutex, unsigned accept)
{
    INT8U err = 255;
    if (accept) REQUIRE(OSMutexAccept(mutex, &err) == OS_TRUE);
    else OSMutexPend(mutex, 0, &err);
    REQUIRE(err == OS_ERR_NONE);
    REQUIRE(mutex->OSEventPtr == owner);
}

static void delete_mutex(OS_EVENT *mutex)
{
    INT8U err = 255;
    REQUIRE(OSMutexDel(mutex, delete_option, &err) == (OS_EVENT *)0);
    REQUIRE(err == OS_ERR_NONE);
}

static void single_mutex(void)
{
    INT8U err;
    setup();
    first = OSMutexCreate(5, &err);
    REQUIRE(first && err == OS_ERR_NONE);
    acquire(first, 0);
    inherit(first, 7, 1);
    REQUIRE(owner->OSTCBPrio == 5);
    delete_mutex(first);
    REQUIRE(owner->OSTCBPrio == 10);
    REQUIRE(OSTCBPrioTbl[5] == (OS_TCB *)0);
    ready_consistent();
}

static void nested_mutex(unsigned accept, unsigned reverse, unsigned post, unsigned reuse)
{
    INT8U err;
    OS_TCB *replacement = (OS_TCB *)0;
    OS_EVENT *a, *b;
    setup();
    first = OSMutexCreate(5, &err);
    REQUIRE(first && err == OS_ERR_NONE);
    second = OSMutexCreate(3, &err);
    REQUIRE(second && err == OS_ERR_NONE);
    acquire(first, 0);
    inherit(first, 7, 1);
    REQUIRE(owner->OSTCBPrio == 5);
    acquire(second, accept);
    inherit(second, 4, 2);
    REQUIRE(owner->OSTCBPrio == 3);
    a = reverse ? second : first;
    b = reverse ? first : second;
    if (post) REQUIRE(OSMutexPost(a) == OS_ERR_NONE);
    else delete_mutex(a);
    REQUIRE(owner->OSTCBPrio == (reverse ? 5 : 3));
    if (reuse) {
        REQUIRE(!post && !reverse);
        replacement = make_task(5, 3);
    }
    if (post) REQUIRE(OSMutexPost(b) == OS_ERR_NONE);
    else delete_mutex(b);
    output("OBS owner_priority="); number(owner->OSTCBPrio);
    output(" slot5_replacement="); number(replacement && OSTCBPrioTbl[5] == replacement);
    output("\n");
    REQUIRE(owner->OSTCBPrio == 10);
    if (reuse) REQUIRE(OSTCBPrioTbl[5] == replacement && replacement->OSTCBPrio == 5);
    if (post) REQUIRE(OSTCBPrioTbl[5] == OS_TCB_RESERVED);
    ready_consistent();
}

static void timeout_suspend_resume(void)
{
    REQUIRE(OSTCBCur == owner);
    if (suspend_before_tick) REQUIRE(OSTaskSuspend(waiter->OSTCBPrio) == OS_ERR_NONE);
    OSTimeTick();
    REQUIRE(waiter->OSTCBStatPend == OS_STAT_PEND_TO);
    REQUIRE((waiter->OSTCBStat & OS_STAT_PEND_ANY) == 0);
    if (!suspend_before_tick) REQUIRE(OSTaskSuspend(waiter->OSTCBPrio) == OS_ERR_NONE);
    REQUIRE((OSRdyTbl[waiter->OSTCBY] & waiter->OSTCBBitX) == 0);
    REQUIRE(OSTaskResume(waiter->OSTCBPrio) == OS_ERR_NONE);
    REQUIRE(waiter->OSTCBStatPend == OS_STAT_PEND_TO);
    REQUIRE(OSTCBCur == waiter);
    ready_consistent();
}

static void pend_timeout(unsigned before)
{
    INT8U err = 255;
    OS_EVENT *sem;
    setup();
    suspend_before_tick = before;
    sem = OSSemCreate(0);
    REQUIRE(sem != (OS_EVENT *)0);
    waiter = make_task(7, 1);
    REQUIRE(OSTCBCur == waiter);
    switch_action = timeout_suspend_resume;
    OSSemPend(sem, 1, &err);
    REQUIRE(switch_action == 0);
    REQUIRE(OSTCBCur == waiter && err == OS_ERR_TIMEOUT);
    REQUIRE(waiter->OSTCBStat == OS_STAT_RDY);
    REQUIRE(waiter->OSTCBEventPtr == (OS_EVENT *)0);
    REQUIRE(sem->OSEventGrp == 0);
    ready_consistent();
}

struct deletion_snapshot {
    INT8U tcbs[sizeof(OSTCBTbl)], events[sizeof(OSEventTbl)], flags[sizeof(OSFlagTbl)];
    OS_TCB *table[OS_LOWEST_PRIO + 1], *list, *free_list, *cur, *high;
    OS_EVENT *event_free;
    OS_PRIO ready[OS_RDY_TBL_SIZE], group;
    INT8U task_count, current_priority, highest_priority, locks;
    unsigned hooks;
};

static void snapshot(struct deletion_snapshot *s)
{
    unsigned p;
    OS_MemClr((INT8U *)s, sizeof(*s));
    OS_MemCopy(s->tcbs, (INT8U *)OSTCBTbl, sizeof(OSTCBTbl));
    OS_MemCopy(s->events, (INT8U *)OSEventTbl, sizeof(OSEventTbl));
    OS_MemCopy(s->flags, (INT8U *)OSFlagTbl, sizeof(OSFlagTbl));
    for (p = 0; p <= OS_LOWEST_PRIO; ++p) s->table[p] = OSTCBPrioTbl[p];
    for (p = 0; p < OS_RDY_TBL_SIZE; ++p) s->ready[p] = OSRdyTbl[p];
    s->list = OSTCBList; s->free_list = OSTCBFreeList;
    s->cur = OSTCBCur; s->high = OSTCBHighRdy; s->event_free = OSEventFreeList;
    s->group = OSRdyGrp; s->task_count = OSTaskCtr;
    s->current_priority = OSPrioCur; s->highest_priority = OSPrioHighRdy;
    s->locks = OSLockNesting; s->hooks = deletion_hooks;
}

static unsigned equal_bytes(const void *a, const void *b, unsigned length)
{
    const INT8U *x = a, *y = b;
    while (length--) if (*x++ != *y++) return 0;
    return 1;
}

static void locked_delete(unsigned explicit_prio, unsigned nesting)
{
    struct deletion_snapshot before, after;
    INT8U result;
    OS_TCB *replacement;
    unsigned n;
    setup();
    for (n = 0; n < nesting; ++n) OSSchedLock();
    REQUIRE(OSLockNesting == nesting);
    snapshot(&before);
    result = OSTaskDel(explicit_prio ? 10 : OS_PRIO_SELF);
    snapshot(&after);
    output("OBS delete_result="); number(result);
    output(" current_is_free="); number(OSTCBCur == OSTCBFreeList);
    output("\n");
    if (result != OS_ERR_SCHED_LOCKED) {
        replacement = make_task(10, 1);
        output("OBS replacement_reused_current_tcb="); number(replacement == OSTCBCur);
        output("\n");
    }
    REQUIRE(result == OS_ERR_SCHED_LOCKED);
    REQUIRE(equal_bytes(&before, &after, sizeof(before)));
    REQUIRE(critical_depth == 0 && irq_disabled == 0);
    for (n = 0; n < nesting; ++n) OSSchedUnlock();
    REQUIRE(OSLockNesting == 0);
    REQUIRE(OSTaskDel(OS_PRIO_SELF) == OS_ERR_NONE);
    REQUIRE(OSTCBCur != owner && OSTCBFreeList == owner);
    ready_consistent();
}

static void delete_controls(void)
{
    INT8U err;
    OS_TCB *other;
    setup();
    other = make_task(9, 1);
    REQUIRE(OSTaskSuspend(OS_PRIO_SELF) == OS_ERR_NONE);
    REQUIRE(OSTCBCur == owner);
    first = OSMutexCreate(5, &err);
    REQUIRE(first && err == OS_ERR_NONE);
    OSSchedLock();
    OSIntNesting = 1;
    REQUIRE(OSTaskDel(OS_PRIO_SELF) == OS_ERR_TASK_DEL_ISR);
    OSIntNesting = 0;
    REQUIRE(OSTaskDel(OS_TASK_IDLE_PRIO) == OS_ERR_TASK_DEL_IDLE);
    REQUIRE(OSTaskDel(254) == OS_ERR_PRIO_INVALID);
    REQUIRE(OSTaskDel(8) == OS_ERR_TASK_NOT_EXIST);
    REQUIRE(OSTaskDel(5) == OS_ERR_TASK_DEL);
    REQUIRE(OSTaskDel(9) == OS_ERR_NONE);
    REQUIRE(OSTCBFreeList == other && OSTCBPrioTbl[9] == (OS_TCB *)0);
    REQUIRE(OSLockNesting == 1 && OSTCBCur == owner);
    OSSchedUnlock();
    REQUIRE(OSTaskDel(OS_PRIO_SELF) == OS_ERR_NONE);
    REQUIRE(OSTCBFreeList == owner && OSTCBCur != owner);
    ready_consistent();
}

static void suspended_owner(void)
{
    INT8U err;
    OS_TCB *controller;
    setup();
    first = OSMutexCreate(5, &err);
    REQUIRE(first && err == OS_ERR_NONE);
    second = OSMutexCreate(3, &err);
    REQUIRE(second && err == OS_ERR_NONE);
    acquire(first, 0); inherit(first, 7, 1);
    acquire(second, 0); inherit(second, 4, 2);
    REQUIRE(OSTaskSuspend(OS_PRIO_SELF) == OS_ERR_NONE);
    controller = make_task(6, 3);
    REQUIRE(OSTCBCur == controller);
    delete_mutex(first); delete_mutex(second);
    REQUIRE(owner->OSTCBPrio == 10);
    REQUIRE(owner->OSTCBStat == OS_STAT_SUSPEND);
    REQUIRE((OSRdyTbl[owner->OSTCBY] & owner->OSTCBBitX) == 0);
    REQUIRE(OSPrioCur == 6 && OSTCBCur == controller);
    REQUIRE(OSTaskResume(10) == OS_ERR_NONE);
    REQUIRE(OSTCBCur == controller);
    ready_consistent();
}

static OS_TCB *controller;
static unsigned handoff;

static void release_from_other_task(void)
{
    REQUIRE(OSTCBCur == controller && OSPrioCur == 3);
    if (handoff) {
        REQUIRE(OSMutexPost(second) == OS_ERR_NONE);
        REQUIRE(OSTCBCur == owner);
    } else {
        /* owner holds first and waits on second. Moving owner must not
         * make it ready or lose its bit in the second mutex's wait map. */
        delete_mutex(first);
        REQUIRE(owner->OSTCBPrio == 10);
        REQUIRE(OSPrioCur == 3 && OSTCBCur == controller);
        REQUIRE((OSRdyTbl[owner->OSTCBY] & owner->OSTCBBitX) == 0);
        REQUIRE((second->OSEventTbl[10 >> 3] & (1u << (10 & 7))) != 0);
        REQUIRE((second->OSEventTbl[5 >> 3] & (1u << (5 & 7))) == 0);
        OSTimeTick();
        REQUIRE(OSTaskSuspend(OS_PRIO_SELF) == OS_ERR_NONE);
        REQUIRE(OSTCBCur == owner);
    }
}

static void waiting_or_handoff(unsigned transfer)
{
    INT8U err;
    setup();
    first = OSMutexCreate(5, &err);
    REQUIRE(first && err == OS_ERR_NONE);
    second = OSMutexCreate(3, &err);
    REQUIRE(second && err == OS_ERR_NONE);
    acquire(first, 0); inherit(first, 7, 1);
    controller = make_task(6, 2);
    REQUIRE(OSTCBCur == owner);
    REQUIRE(OSTaskSuspend(OS_PRIO_SELF) == OS_ERR_NONE);
    REQUIRE(OSTCBCur == controller);
    OSMutexPend(second, 0, &err);
    REQUIRE(err == OS_ERR_NONE && second->OSEventPtr == controller);
    REQUIRE(OSTaskResume(5) == OS_ERR_NONE);
    REQUIRE(OSTCBCur == owner);
    handoff = transfer;
    switch_action = release_from_other_task;
    OSMutexPend(second, 1, &err);
    REQUIRE(switch_action == 0 && OSTCBCur == owner);
    if (transfer) {
        REQUIRE(err == OS_ERR_NONE && second->OSEventPtr == owner);
        REQUIRE((second->OSEventCnt & 0xffu) == 10);
        delete_mutex(first); delete_mutex(second);
        REQUIRE(owner->OSTCBPrio == 10);
    } else {
        REQUIRE(err == OS_ERR_TIMEOUT && second->OSEventGrp == 0);
        REQUIRE(owner->OSTCBPrio == 10 && owner->OSTCBEventPtr == (OS_EVENT *)0);
    }
    ready_consistent();
}

static void disabled_ceiling(void)
{
    INT8U err;
    setup();
    first = OSMutexCreate(OS_PRIO_MUTEX_CEIL_DIS, &err);
    REQUIRE(first && err == OS_ERR_NONE);
    second = OSMutexCreate(3, &err);
    REQUIRE(second && err == OS_ERR_NONE);
    acquire(first, 1); acquire(second, 0); inherit(second, 4, 1);
    REQUIRE(OSMutexPost(second) == OS_ERR_NONE);
    REQUIRE(owner->OSTCBPrio == 10);
    REQUIRE(OSMutexPost(first) == OS_ERR_NONE);
    ready_consistent();
}

int test_main(int argc, char **argv)
{
    unsigned test = 0;
    const char *s;
    REQUIRE(argc == 2);
    for (s = argv[1]; *s; ++s) { REQUIRE(*s >= '0' && *s <= '9'); test = test * 10 + *s - '0'; }
    switch (test) {
        case 0: pend_timeout(0); break;
        case 1: pend_timeout(1); break;
        case 2: single_mutex(); break;
        case 3: nested_mutex(0, 0, 0, 0); break;
        case 4: nested_mutex(1, 0, 0, 0); break;
        case 5: nested_mutex(0, 0, 0, 1); break;
        case 6: nested_mutex(1, 0, 0, 1); break;
        case 7: nested_mutex(0, 1, 0, 0); break;
        case 8: nested_mutex(1, 1, 0, 0); break;
        case 9: nested_mutex(0, 0, 1, 0); break;
        case 10: nested_mutex(1, 0, 1, 0); break;
        case 11: nested_mutex(0, 1, 1, 0); break;
        case 12: nested_mutex(1, 1, 1, 0); break;
        case 13: locked_delete(0, 1); break;
        case 14: locked_delete(1, 1); break;
        case 15: locked_delete(0, 255); break;
        case 16: locked_delete(1, 255); break;
        case 17: delete_controls(); break;
        case 18: delete_option = OS_DEL_NO_PEND; nested_mutex(0, 0, 0, 1); break;
        case 19: suspended_owner(); break;
        case 20: waiting_or_handoff(0); break;
        case 21: waiting_or_handoff(1); break;
        case 22: disabled_ceiling(); break;
        default: REQUIRE(0);
    }
    REQUIRE(switch_action == 0 && critical_depth == 0 && irq_disabled == 0);
    output("PASS\n");
    return 0;
}
