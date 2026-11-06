/* Controlled CPU-boundary test of the exact frozen kernel, not a CPU proof.
 * All task operations and the tick ISR execute real configured C functions.
 * The adapter runs finite task segments at context switches, without stacks.
 */
#include "ucos_ii.c"

static unsigned irq_disabled, critical_depth, armed, delete_in_window;
static unsigned interrupts, controller_runs, delete_hooks;
static INT8U delete_result = 255;
static OS_TCB *creator, *controller, *pending;
static OS_STK stacks[3][128];
static void inject_tick(void);

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
    output("TECHNICAL_OR_ENTRY_FAILURE line="); number(line);
    output(" expression="); output(expression); output("\n");
    __asm__ volatile ("int $0x80" : : "a"(1), "b"(3) : "memory");
    __builtin_unreachable();
}
#define REQUIRE(x) do { if (!(x)) die(#x, __LINE__); } while (0)

static unsigned ready(unsigned p)
{ return (OSRdyTbl[p >> 3] & (1u << (p & 7))) != 0; }

static unsigned in_pool(OS_TCB *t)
{
    unsigned i;
    for (i = 0; i < OS_MAX_TASKS + OS_N_SYS_TASKS; ++i)
        if (t == &OSTCBTbl[i]) return 1;
    return 0;
}

static unsigned member(OS_TCB *head, OS_TCB *t)
{
    unsigned count = 0;
    while (head) {
        REQUIRE(in_pool(head));
        if (head == t) return 1;
        if (++count > OS_MAX_TASKS + OS_N_SYS_TASKS) return 0;
        head = head->OSTCBNext;
    }
    return 0;
}

/* Independent oracle: bounded walks, actual table/ready bytes, actual links.
 * No production invariant or candidate pending relation is used as an oracle.
 */
static unsigned structure_ok(void)
{
    unsigned n = 0, nf = 0, p;
    OS_TCB *t = OSTCBList, *prev = 0;
    while (t) {
        if (!in_pool(t) || ++n > OS_MAX_TASKS + OS_N_SYS_TASKS) return 0;
        if (t->OSTCBPrev != prev || t->OSTCBPrio > OS_LOWEST_PRIO) return 0;
        if (OSTCBPrioTbl[t->OSTCBPrio] != t) return 0;
        if (member(OSTCBFreeList, t)) return 0;
        prev = t;
        t = t->OSTCBNext;
    }
    if (n != OSTaskCtr) return 0;
    for (t = OSTCBFreeList; t; t = t->OSTCBNext)
        if (!in_pool(t) || ++nf > OS_MAX_TASKS + OS_N_SYS_TASKS) return 0;
    for (p = 0; p <= OS_LOWEST_PRIO; ++p) {
        if (((OSRdyGrp >> (p >> 3)) & 1u) != (OSRdyTbl[p >> 3] != 0)) return 0;
        if (!ready(p)) continue;
        t = OSTCBPrioTbl[p];
        if (!t || t == OS_TCB_RESERVED || !in_pool(t)) return 0;
        if (t->OSTCBPrio != p || !member(OSTCBList, t)) return 0;
    }
    return 1;
}

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
    if (armed && !irq_disabled && !critical_depth &&
        OSTCBPrioTbl[8] && OSTCBPrioTbl[8] != OS_TCB_RESERVED && !ready(8)) {
        armed = 0;
        pending = OSTCBPrioTbl[8];
        inject_tick();
    }
}

static void select_highest(void)
{
    OS_SchedNew();
    REQUIRE(ready(OSPrioHighRdy));
    OSTCBHighRdy = OSTCBPrioTbl[OSPrioHighRdy];
    REQUIRE(OSTCBHighRdy && OSTCBHighRdy != OS_TCB_RESERVED);
    REQUIRE(OSTCBHighRdy->OSTCBPrio == OSPrioHighRdy);
    OSTCBCur = OSTCBHighRdy;
    OSPrioCur = OSPrioHighRdy;
}

void OSCtxSw(void) { select_highest(); }

void OSIntCtxSw(void)
{
    unsigned depth = critical_depth, irq = irq_disabled;
    /* Suspend the ISR's critical context; another task resumes enabled. */
    critical_depth = irq_disabled = 0;
    select_highest();
    REQUIRE(OSTCBCur == controller && OSIntNesting == 0 && OSLockNesting == 0);
    REQUIRE(!ready(8) && OSTCBPrioTbl[8] == pending);
    REQUIRE(!member(OSTCBList, pending) && !member(OSTCBFreeList, pending));
    ++controller_runs;
    output("COMMON controller=3 pending=8 ready8=0 active8=0 free8=0\n");
    /* The sole comparison factor; no hook mutates a kernel object. */
    if (delete_in_window) delete_result = OSTaskDel(8);
    REQUIRE(OSTCBCur == controller && critical_depth == 0 && irq_disabled == 0);
    REQUIRE(OSTaskSuspend(OS_PRIO_SELF) == OS_ERR_NONE);
    REQUIRE(OSTCBCur == creator && OSPrioCur == 7);
    REQUIRE(critical_depth == 0 && irq_disabled == 0);
    critical_depth = depth;
    irq_disabled = irq;
}

void OSStartHighRdy(void) { select_highest(); }
void OSInitHookBegin(void) {}
void OSInitHookEnd(void) {}
void OSTaskCreateHook(OS_TCB *t) { (void)t; }
void OSTaskDelHook(OS_TCB *t) { (void)t; ++delete_hooks; }
void OSTaskIdleHook(void) {}
void OSTaskReturnHook(OS_TCB *t) { (void)t; }
void OSTaskStatHook(void) {}
void OSTaskSwHook(void) {}
void OSTCBInitHook(OS_TCB *t) { (void)t; }
void OSTimeTickHook(void) {}
OS_STK *OSTaskStkInit(void (*task)(void *), void *arg, OS_STK *top, INT16U opt)
{ (void)task; (void)arg; (void)opt; return top; }
static void task(void *arg) { (void)arg; }

static void inject_tick(void)
{
    REQUIRE(OSTCBCur == creator && critical_depth == 0 && irq_disabled == 0);
    REQUIRE(OSIntNesting == 0 && OSLockNesting == 0 && OSRunning == OS_TRUE);
    REQUIRE(structure_ok() && pending->OSTCBPrio == 8);
    REQUIRE(!member(OSTCBList, pending) && !member(OSTCBFreeList, pending));
    REQUIRE(!ready(8) && controller->OSTCBDly == 1 && !ready(3));
    ++interrupts;
    irq_disabled = 1; /* Accepted hardware-entry mask in this CPU adapter. */
    OSIntEnter();
    REQUIRE(OSIntNesting == 1);
    OSTimeTick();
    REQUIRE(controller->OSTCBDly == 0 && ready(3));
    OSIntExit();
    REQUIRE(OSIntNesting == 0 && critical_depth == 0 && irq_disabled == 1);
    irq_disabled = 0;
    REQUIRE(OSTCBCur == creator && controller_runs == 1);
}

int test_main(int argc, char **argv)
{
    INT8U result;
    unsigned ok;
    REQUIRE(argc == 2 && (argv[1][0] == '0' || argv[1][0] == '1') && !argv[1][1]);
    delete_in_window = argv[1][0] == '1';
    OSInit();
    REQUIRE(OSTaskCreate(task, 0, &stacks[0][127], 7) == OS_ERR_NONE);
    creator = OSTCBPrioTbl[7];
    REQUIRE(OSTaskCreate(task, 0, &stacks[1][127], 3) == OS_ERR_NONE);
    controller = OSTCBPrioTbl[3];
    select_highest();
    REQUIRE(OSTaskSuspend(OS_TASK_STAT_PRIO) == OS_ERR_NONE);
    OSRunning = OS_TRUE;
    REQUIRE(OSTCBCur == controller);
    OSTimeDly(1); /* Controller's segment ends at the actual delay/switch. */
    REQUIRE(OSTCBCur == creator && controller->OSTCBDly == 1);
    REQUIRE(structure_ok() && !OSTCBPrioTbl[8] && !ready(8));
    armed = 1;
    result = OSTaskCreateExt(task, 0, &stacks[2][127], 8, 8, &stacks[2][0], 128, 0, 0);
    REQUIRE(!armed && interrupts == 1 && controller_runs == 1);
    REQUIRE(critical_depth == 0 && irq_disabled == 0 && OSIntNesting == 0);
    ok = structure_ok();
    output("OBS create="); number(result);
    output(" deletion="); number(delete_result);
    output(" ready8="); number(ready(8));
    output(" slot8_null="); number(OSTCBPrioTbl[8] == 0);
    output(" active8="); number(member(OSTCBList, pending));
    output(" free8="); number(member(OSTCBFreeList, pending));
    output(" structure="); number(ok);
    output(" deletion_hooks="); number(delete_hooks); output("\n");
    if (!ok) {
        output("FAIL ready_pointer_and_active_free_ownership\n");
        return 2;
    }
    REQUIRE(result == OS_ERR_NONE);
    if (!delete_in_window) {
        REQUIRE(OSTaskDel(8) == OS_ERR_NONE);
        REQUIRE(!ready(8) && !OSTCBPrioTbl[8] && structure_ok());
        output("CONTROL delete_after_complete=0 structure=1\n");
    }
    output("PASS\n");
    return 0;
}
