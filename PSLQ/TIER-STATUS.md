# TIER-STATUS — R1 — PSLQ

Updated 2026-07-27 (post core + lower bound).

## Proven (sorry-free, axioms exactly `[propext, Classical.choice, Quot.sound]`)

* `DiscoveryKernels.R1.pslq_empirical_sound` (`PSLQ/Empirical.lean`) —
  THE TIER'S POINT. Statement verbatim from Challenge.lean; comparator-green.
  Under the repository's new organizing thesis (condition number
  `κ(x) = ‖x‖ / dist(x, Σ)`) this is the PSLQ instance's certified margin:
  input precision `p` + coefficient bound `M` ⟹ the report is exact, not a
  rounding artifact.
* `DiscoveryKernels.R1.pslq_partial_correct` (`PSLQ/Core.lean`) — the
  exact-arithmetic PSLQ-class core `R1.pslq` over `ℚ` (CSV/HJLS
  normalization) reports only genuine integer relations. Challenge.lean's
  refined statement is already landed by the orchestrator and matches.
* `DiscoveryKernels.R1.pslq_lower_bound` (`PSLQ/Bound.lean`) — the
  Borwein–Lisoněk termination bound over the state's exact rational
  Gram–Schmidt data. Proposed Challenge.lean replacement text is in
  `PSLQ/CHALLENGE-R1.proposed.md`, comparator `isDefEq`-verified against
  the proof.
* Supporting, all proved: `ElemOp.apply_inv` (certified elementary column
  operations preserve the loop invariant — partial correctness is therefore
  independent of the search strategy), `PSLQState.report?_spec`,
  `applyProgram_inv`, `pslqState_inv`, `checkRelation_sound` /
  `checkRelation_iff` / `pslq_checkRelation` (the `checkPDq_sound` Bool-check
  schema adapted from certified-positivity per DEPS.md), `gso_orthogonal`
  (rational Gram–Schmidt orthogonality, proved from scratch — Mathlib's
  `gramSchmidt` needs `RCLike` and is unavailable over `ℚ`),
  `PSLQState.relation_eq_sum_smul_proj`, `pslq_none_report`,
  `pslq_none_y_ne_zero`.

## Sorry

* Nothing in `PSLQ/`. `Core.lean` and `Bound.lean` are sorry-free.
* `Challenge.lean`'s R1 placeholders are `sorry` **by design** (that file
  states, it never proves).

## Honest caveats (stated, not hidden)

* `pslq_lower_bound` pins the index `k` (the top of the support of
  `Binv · m`) instead of taking a `min` over all indices. This is forced: the
  `n` projected basis columns span the `(n-1)`-dimensional `x^⊥`, so exactly
  one Gram–Schmidt direction degenerates and a `min`-shaped bound would be
  the trivial `0`. The `min`-shaped packaging exists as the corollary
  `PSLQState.gsoNormSq_le_of_relation_of_min` and is non-vacuous exactly for
  nondegenerate GSO data.
* The headline's `hnone : pslq x fuel = none` hypothesis is not used by the
  proof (the bound holds at every invariant state — see the stronger
  `PSLQState.gsoNormSq_le_of_relation`). It is kept because the charter's
  target sentence is "while no relation has been reported"; this makes the
  headline weaker than what is proved, never stronger.
* Faithfulness of the *strategy* (`roundProgram`: full Hermite size-reduction
  pass, then the γ-weighted maximal-diagonal swap with γ² = 2) is asserted by
  construction and by the references, not proved. Nothing in either headline
  depends on it: correctness holds for any strategy that only issues
  `ElemOp`s. No convergence/complexity claim is made anywhere.

## Dependencies (DEPS.md — complete, all three verdicts)

1. Hex: **HEX-UNAVAILABLE** for this pin (v4.32.0-rc1 vs our v4.32.0).
2. certified-positivity: **ADAPT** (schema-level port of the
   `checkPDq_sound` Bool-check + soundness/margin-transfer shapes; no code
   import — v4.28.0 vs v4.32.0). Realized as `checkRelation` /
   `checkRelation_sound` / `checkRelation_iff` in `Core.lean`.
3. Prior art: **negative, recorded** — no PSLQ/HJLS/integer-relation
   formalization found in Lean/Isabelle/Coq/HOL.

## Build state

* `lakefile.toml` PSLQ entry: glob `["PSLQ.+"]` **restored** (every
  module under `PSLQ/` elaborates). `lake build` from the repo root:
  green, 8665 jobs.
* No `Float` and no `ℝ` anywhere in `Core.lean` or `Bound.lean`; `ℝ` appears
  only in `Empirical.lean`, where the truth vector lives by design.

## Blocked

* Nothing.

## Deliverables for the orchestrator

* `PSLQ/CHALLENGE-R1.proposed.md` — exact replacement text for
  `pslq_lower_bound` (and the already-landed `pslq_partial_correct`), the
  required Challenge.lean import line, and a dated STATEMENTS.md changelog
  paragraph.
* `PSLQ/COMPARATOR-ROWS.md` — the three R1 `headlines.toml` rows and the
  `comparator/AxiomCheck.lean` additions, with the local verification table.
