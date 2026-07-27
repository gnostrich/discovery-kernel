/-
Copyright (c) 2026 discovery-kernels contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.

# Challenge.lean — the statement registry of `discovery-kernels`

This file IS the set of claims of this repository. Prose (README,
STATEMENTS.md) never claims anything this file does not state.

Rules of this file:
* Two append-only tier sections (R1, R3), delimited below. No agent edits
  another tier's section. (R0 and R2 were descoped 2026-07-27 — the scalar
  license lives in the sibling repo `gnostrich/realization-lean`, and no
  abstract detector interface is designed up front; see STATEMENTS.md
  changelog.)
* Every headline here is stated with `:= sorry` — permanently. Solutions live
  in the tier directories and are checked against these statements by
  `comparator/` (definitional-equality check + per-theorem axiom allowlist).
  R3 headlines are stated frontier: no solution is claimed, by design.
* Statement changes after FREEZE-0 are recorded in STATEMENTS.md with a dated
  note.
-/
import R1_PSLQ.Defs
import R1_PSLQ.Core
import R3_OV.Defs

namespace DiscoveryKernels.Challenge

-- ==== R1 ==== PSLQ: exact core, termination, empirical input ==============

/-- **PSLQ partial correctness.** If the exact-arithmetic PSLQ-class core
`R1.pslq`, run on exact rational input `x` with any fuel, reports `m`, then
`m` is an integer relation of `x` (nonzero, with `∑ mᵢ xᵢ = 0`).

Soundness only: this says a report is correct, never that the core reports
whenever a relation exists. Refined from the FREEZE-0 `True` placeholder on
2026-07-27, when `R1.pslq` landed; see STATEMENTS.md changelog. -/
theorem pslq_partial_correct
    {n : ℕ} (x : Fin n → ℚ) (fuel : ℕ) (m : Fin n → ℤ)
    (h : R1.pslq x fuel = some m) :
    R1.IsIntRelation x m := sorry

/-- **PSLQ termination / lower bound (Borwein–Lisoněk form).** While the
exact-arithmetic core has reported no relation within `fuel` rounds
(`R1.pslq x fuel = none`), every integer relation `m` of the exact rational
input `x` is large: its squared euclidean norm is at least the explicit
rational number `gsoNormSq x k` read off the state's own rational
(CSV/HJLS-normalized) Gram–Schmidt data after `fuel` rounds, where `k` is the
last index at which `m` has a nonzero coordinate in the algorithm's current
basis (`coords m = Binv · m`, an integer vector by unimodularity).

The index `k` is stated rather than hidden behind a `min` because it must be:
the `n` projections of the basis columns onto `x^⊥` span an
`(n-1)`-dimensional space, so exactly one Gram–Schmidt direction degenerates
and a `min` over all `j` would be the trivial bound `0`. Pinning `k` is what
makes the bound a real one. Refined from the FREEZE-0 `True` placeholder on
2026-07-27; see STATEMENTS.md changelog. -/
theorem pslq_lower_bound
    {n : ℕ} (x : Fin n → ℚ) (fuel : ℕ) (hnone : R1.pslq x fuel = none)
    (m : Fin n → ℤ) (hm : R1.IsIntRelation x m) (k : Fin n)
    (hk : (R1.pslqState x fuel).coords m k ≠ 0)
    (hlast : ∀ j, k < j → (R1.pslqState x fuel).coords m j = 0) :
    (R1.pslqState x fuel).gsoNormSq x k ≤ ∑ i, ((m i : ℚ)) ^ 2 := sorry

/-- **THE TIER'S POINT — empirical-input soundness.** Input known to precision
`p` (true vector `x : Fin n → ℝ`, computed rational approximation `xq` with
`|x i - xq i| ≤ p`), reported integer vector `m` with coefficient bound
`|m i| ≤ M` that is an exact relation of `xq` (which is what the exact
arithmetic core guarantees). Then:
1. the reported relation is `ε`-genuine for the truth with the explicit
   `ε(p, M, n) = n * M * p`: `|∑ mᵢ xᵢ| ≤ n * M * p`; and
2. under the separation hypothesis — every candidate integer vector `k` with
   `‖k‖∞ ≤ M` either annihilates `x` exactly or misses by more than
   `n * M * p` — the reported `m` is a genuine exact relation of `x`:
   the report is not a numerical artifact. -/
theorem pslq_empirical_sound
    {n : ℕ} (x : Fin n → ℝ) (xq : Fin n → ℚ) (p : ℝ) (M : ℤ)
    (m : Fin n → ℤ)
    (happ : ∀ i, |x i - (xq i : ℝ)| ≤ p)
    (hM : ∀ i, |m i| ≤ M)
    (hrel : R1.IsIntRelation xq m) :
    |∑ i, (m i : ℝ) * x i| ≤ (n : ℝ) * (M : ℝ) * p ∧
      ((∀ k : Fin n → ℤ, k ≠ 0 → (∀ i, |k i| ≤ M) →
          ∑ i, (k i : ℝ) * x i = 0 ∨ (n : ℝ) * (M : ℝ) * p < |∑ i, (k i : ℝ) * x i|) →
        R1.IsIntRelation x m) := sorry

-- ==== R3 ==== operator-valued license — STATEMENTS ONLY ===================

/-- **Operator-valued license (MSY-shaped), stated frontier.** For an
operator-valued moment sequence over a ring `B`: finite OV Hankel rank,
existence of a finite linear realization (rational `B`-valued resolvent), and
finite atomicity are equivalent. Cf. Mai–Speicher–Yin. `sorry` BY DESIGN:
this tier states the frontier; no proof is claimed. FREEZE-0 draft shape —
requires operator review before any refinement is merged (see R3_OV/AGENTS.md). -/
theorem ov_license
    {B : Type} [Ring B] (M : ℕ → B) :
    (R3.HasFiniteOVHankelRank B M ↔ R3.HasFiniteRealization B M) ∧
      (R3.HasFiniteRealization B M ↔ R3.IsFinitelyAtomicOV B M) := sorry

/-- **Operator-valued completeness (free-Ax–Schanuel-shaped), stated frontier**
(FREEZE-0 placeholder — the definitional layer for "genuine OV alignment" and
"structural cause" is R3 work; the refined statement lands with it, under the
operator-review gate; see STATEMENTS.md changelog). Target: every genuine
operator-valued alignment (rank drop) has a structural cause (an exact
noncommutative algebraic relation). `sorry` BY DESIGN. -/
theorem ov_completeness : True := sorry

end DiscoveryKernels.Challenge
