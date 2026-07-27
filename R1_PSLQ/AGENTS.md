# R1 agent — PSLQ (exact core, termination, empirical input)

Persistent charter + memory for the R1 tier agent. Read this fully at session
start; append to MEMORY after every significant step. Obey the root
`AGENTS.md` policies.

## Mission (strict order)

1. **DEPS.md verdict (blocker).** Locate and license-check the Hex library
   (Lean verified LLL/Gram–Schmidt, announced FLoC 2026, availability
   unverified). Write `R1_PSLQ/DEPS.md`: HEX-USABLE (dependency + pin) or
   HEX-UNAVAILABLE (fall back to Mathlib primitives / self-contained rational
   Gram–Schmidt). No proofs before this verdict is committed.
2. **Exact-arithmetic core over ℚ.** We formalize the PSLQ-class detector in
   the CSV/HJLS normalization (Chen–Stehlé–Villard, ISSAC 2013: PSLQ ≡ HJLS
   up to scaling): textbook PSLQ's `H` matrix is irrational even on rational
   input; the HJLS normalization uses rational Gram–Schmidt data throughout,
   so every state is exactly representable over ℚ. Fuel-based iteration;
   state `(y, B, GSO data)` with invariant `y = x ⬝ B` (`B` unimodular).
   Prove partial correctness: report `m` ⟹ `IsIntRelation x m` (report site:
   a zero appears in `y`; the relation is the corresponding column of `B`;
   nonzero by unimodularity).
3. **Termination / lower bound** (Borwein–Lisoněk form): while no relation is
   reported, every integer relation of `x` has norm exceeding an explicit
   rational bound from the GSO data (`‖m‖² ≥ 1 / max_j ‖b*_j‖²`-shaped).
4. **THE TIER'S POINT — `pslq_empirical_sound`.** Already stated
   algorithm-independently in Challenge.lean; refine to mention the core's
   output once `pslq` lands (dated STATEMENTS.md note), keeping the
   algorithm-independent lemma as the engine.
5. **Last:** `instance : DiscoveryKernel` for the scalar lattice state
   against the FROZEN R2 signature (`R2_Detector/Defs.lean`).

Do NOT ship the core without the empirical theorem. No `Float` anywhere.

## Refinement duties

When `pslq` lands: refine `pslq_partial_correct`, `pslq_lower_bound`,
`pslq_empirical_sound` in Challenge.lean (R1 section, append-only edits of
the placeholder statements) with dated STATEMENTS.md changelog entries, and
fill your rows of `comparator/headlines.toml`.

## MEMORY (append-only, dated)

* 2026-07-27 — Tier initialized at FREEZE-0. Orchestrator note: no Aristotle
  MCP server exists in this session; use `scripts/aristotle.py` (API key in
  env). Hex verdict pending.
