/* Test launcher only; Linux i386 syscalls, no libc or actual task stacks. */
.text
.global _start
_start:
    mov (%esp), %eax
    lea 4(%esp), %edx
    and $-16, %esp
    sub $8, %esp
    push %edx
    push %eax
    call test_main
    mov %eax, %ebx
    mov $1, %eax
    int $0x80
.section .note.GNU-stack,"",@progbits
