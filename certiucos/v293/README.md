# V2.93.01 verification tree

This is the only active OS-specific Coq tree.

- `code/`: fixed configuration and source-level program definitions.
- `model/`: concrete/abstract state models and global invariants.
- `spec/`: API/internal-function specifications and safety statements.
- `proofs/`: source-linked Hoare proofs, integration proofs, and final theorem.

The small model/proof files currently present are **regression-property
foundations only**.  They do not claim source-level correspondence or the final
`GOOD_OS` theorem.  Source linkage must be established from the pinned
V2.93.01 checkout before a property is counted as a verified kernel function.
