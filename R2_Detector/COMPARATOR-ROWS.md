# COMPARATOR-ROWS — R2 — proposed comparator registrations

Proposed updates to `comparator/headlines.toml` (R2 rows only; the orchestrator
applies them — this tier does not edit comparator TOMLs).

## discovery_kernel_inhabited (2026-07-27)

```toml
[[headline]]
name = "discovery_kernel_inhabited"
challenge = "DiscoveryKernels.Challenge.discovery_kernel_inhabited"
solution = "DiscoveryKernels.R2.discovery_kernel_inhabited"
module = "R2_Detector.Toy"
proven_required = true
tier = "R2"
```

* Statement type is written verbatim as in Challenge.lean
  (`Nonempty (DiscoveryKernel (List ℚ) ℕ)`) — syntactically identical, hence
  definitionally equal; a local def-eq `example` check passed.
* Axioms: `[propext, Classical.choice, Quot.sound]` — within the default
  allowlist; no extension needed (no `native_decide`, no `decide` in the
  solution, zero sorries).
