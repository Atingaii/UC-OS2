# Trusted base

The retained CertiOS framework predates this retarget and contains explicit
logical assumptions such as functional/extensional equality principles,
proof-irrelevance/equality transport support, classical reasoning, map
extensionality interfaces, and `memory.MemoryNotFull`.

Those assumptions are not silently strengthened by the V2.93.01 tree.  Active
`certiucos/v293` files may not introduce new `Axiom`, `Parameter`,
`Conjecture`, or proof holes.  Final acceptance must use `Print Assumptions` and
`coqchk` to report the exact dependency closure of the top-level theorem.

The task-switch/interrupt mechanism is an explicit semantic abstraction
boundary for the source-level proof.  Concrete CPU execution, compiler,
assembler/linker, and hardware correctness are outside the active theorem.
