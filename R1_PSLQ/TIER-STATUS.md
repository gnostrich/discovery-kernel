# TIER-STATUS — R1 — PSLQ

INTERIM STATUS for orchestrator (2026-07-27, post-steering-change):

* Steering change acknowledged: R2/DiscoveryKernel instance work DROPPED;
  R0 ignored. Deliverables now: DEPS.md, empirical theorem, core + partial
  correctness, termination/lower bound.
* DEPS.md complete (all three verdicts):
  1. Hex: HEX-UNAVAILABLE for this pin (toolchain conflict v4.32.0-rc1 vs
     v4.32.0; Apache-2.0, exists upstream).
  2. certified-positivity: ADAPT (schema-level port of checkPDq_sound
     Bool-check + soundness and margin-transfer shapes; no code import —
     v4.28.0 vs v4.32.0).
  3. Prior-art negative RECORDED: no PSLQ/HJLS/integer-relation
     formalization found in Lean/Isabelle/Coq/HOL (3 searches, terms in
     DEPS.md). Adjacent: LLL in Isabelle/AFP (Thiemann et al.), Hex LLL.
* PROVEN: `DiscoveryKernels.R1.pslq_empirical_sound`
  (R1_PSLQ/Empirical.lean) — statement verbatim from Challenge.lean, sorry-
  free, axioms exactly [propext, Classical.choice, Quot.sound].
* IN PROGRESS: exact-arithmetic core (R1_PSLQ/Core.lean, CSV/HJLS
  normalization over ℚ) + partial correctness; then Borwein–Lisoněk lower
  bound.
* Sorry: Challenge.lean R1 placeholders (by design until refinement
  proposals land in R1_PSLQ/CHALLENGE-R1.proposed.md).
* Blocked: nothing.
