# Pinned upstream source

The verification target is the official uC/OS-II V2.93.01 snapshot at commit
`0c4a48e6fbc6e915714e816196619a5481accf0c`.

The upstream source is intentionally not synthesized from older kernel code.
Run `make fetch-source` to create `checkout/` from the pinned commit and verify
every retained source hash before it can be used by the verification workflow.

`checkout/` is ignored by Git because the immutable source identity is already
recorded in `csrc/UPSTREAM.lock.json`.  A project release may vendor the exact
verified checkout if desired, but only after the same hash audit passes.
