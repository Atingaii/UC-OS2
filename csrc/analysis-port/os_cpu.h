/* Analysis adapter only: no executable CPU port or hardware claim. */
#ifndef V293_ANALYSIS_OS_CPU_H
#define V293_ANALYSIS_OS_CPU_H

typedef unsigned char  BOOLEAN;
typedef signed char    INT8S;
typedef unsigned char  INT8U;
typedef unsigned short INT16U;
typedef unsigned int   INT32U;
typedef unsigned int   OS_STK;
typedef unsigned int   OS_CPU_SR;

_Static_assert(sizeof(INT8U) == 1, "INT8U width");
_Static_assert(sizeof(INT16U) == 2, "INT16U width");
_Static_assert(sizeof(INT32U) == 4, "INT32U width");
_Static_assert(sizeof(void *) == 4, "32-bit source analysis");

#define OS_STK_GROWTH      1u
#define OS_CRITICAL_METHOD 3u

/* Preserve critical-section operations as calls, never as empty macros.
 * The saved token must later be related to the framework interrupt state. */
void V293_EnterCritical(OS_CPU_SR *saved);
void V293_ExitCritical(OS_CPU_SR *saved);
#define OS_ENTER_CRITICAL() V293_EnterCritical(&cpu_sr)
#define OS_EXIT_CRITICAL()  V293_ExitCritical(&cpu_sr)

/* Declarations only: source-level context-switch obligations remain open. */
void OSStartHighRdy(void);
void OSIntCtxSw(void);
void OSCtxSw(void);
#define OS_TASK_SW() OSCtxSw()

#endif
