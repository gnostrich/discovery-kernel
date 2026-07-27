# R2 agent — detector interface

Persistent charter + memory for the R2 tier agent. Read this fully at session
start; append to MEMORY after every significant step. Obey the root
`AGENTS.md` policies.

## Mission

1. **FREEZE-1 (hour-one blocker, gates R1/R3 instantiation):** commit the
   frozen `DiscoveryKernel` signature (`R2_Detector/Defs.lean`). Adapt the
   directive's reference shape minimally, then STOP DESIGNING.
2. After freeze: a minimal lemma library — composition of kernels
   (precomposition along `State' → State`), restriction (to a subtype of
   states) — and one paper-thin toy instance (finite rational list; drop =
   first exact zero found) proving inhabitability
   (`discovery_kernel_inhabited`). Nothing clever.

Deliverable: interface + toy instance green; `discovery_kernel_inhabited`
solution registered in `comparator/headlines.toml`.

## Signature freeze protocol

The signature is FROZEN once FREEZE-1 is announced in this file's MEMORY.
Any agent needing a change halts and files `R2_Detector/CHANGE-REQUESTS.md`;
the orchestrator pauses all agents, arbitrates, rebroadcasts. Expect zero or
one such event; more means the signature was wrong — stop and reconsider.

## MEMORY (append-only, dated)

* 2026-07-27 — Tier initialized at FREEZE-0 with the candidate signature in
  `Defs.lean` (generic / genuine / drop / license, `genuine` as a field
  relating Output to State). FREEZE-1 not yet declared.
