# STATEMENTS

This file mirrors `Challenge.lean`, the statement registry of this repository.
**The Lean statements are the claims.** Prose in this repository never claims
anything `Challenge.lean` does not state. If a statement must change, it
changes in `Challenge.lean` and here first, with a dated note in the
changelog at the bottom.

## Statements (verbatim from Challenge.lean)

### R0 — scalar license (Kronecker 1881)

```lean
theorem hankel_finite_rank_iff_rational
    {K : Type} [Field K] (a : ℕ → K) :
    R0.HasFiniteHankelRank K a ↔ R0.IsRationalGF K a := sorry
```

```lean
theorem rational_iff_finitely_many_atoms
    {K : Type} [Field K] [IsAlgClosed K] [CharZero K] (a : ℕ → K) :
    R0.IsRationalGF K a ↔ R0.IsFinitelyAtomic K a := sorry
```

### R1 — PSLQ

```lean
theorem pslq_partial_correct : True := sorry
```
*(FREEZE-0 placeholder; to be refined against the exact-arithmetic core
`R1.pslq` when it lands — see changelog.)*

```lean
theorem pslq_lower_bound : True := sorry
```
*(FREEZE-0 placeholder; Borwein–Lisoněk-form bound, to be refined — see
changelog.)*

```lean
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
```

### R2 — detector interface

```lean
theorem discovery_kernel_inhabited :
    Nonempty (DiscoveryKernel (List ℚ) ℕ) := sorry
```

### R3 — operator-valued license (STATEMENTS ONLY)

```lean
theorem ov_license
    {B : Type} [Ring B] (M : ℕ → B) :
    (R3.HasFiniteOVHankelRank B M ↔ R3.HasFiniteRealization B M) ∧
      (R3.HasFiniteRealization B M ↔ R3.IsFinitelyAtomicOV B M) := sorry
```
*(Stated frontier, `sorry` by design; FREEZE-0 draft shape, held for operator
review — see R3_OV/AGENTS.md.)*

```lean
theorem ov_completeness : True := sorry
```
*(FREEZE-0 placeholder; free-Ax–Schanuel-shaped statement lands with the R3
definitional layer, under the operator-review gate — see changelog.)*

## What we do NOT claim

* **No claim to prove any R3 statement.** R3 is stated frontier only; its
  headlines are `sorry` by design, and the R3 definitional layer is a
  deliberately minimal algebraic abstraction of the analytic
  (Mai–Speicher–Yin) setting — the simplifications are flagged in docstrings
  (left modules instead of bimodules; atoms and weights abstracted to ring
  elements; no positivity, no von Neumann algebra, no conditional
  expectation).
* **No claim that the R2 abstraction is a contribution.** `DiscoveryKernel` is
  organizing scaffolding.
* **No floating-point claims.** Everything is exact arithmetic (ℚ, ℤ) or
  interval-/rational-certified statements about real quantities. No `Float`
  appears in any statement.
* **No novelty claim for LLL formalization.** LLL is formalized in
  Isabelle/HOL (Thiemann et al., 2018–2020) and announced for Lean via the
  Hex library (FLoC 2026); see `R1_PSLQ/DEPS.md` for what this repository
  does and does not depend on.
* **No claim about the measure-theoretic (positive) Kronecker theorem.** The
  R0 atomic statement is the exponential-polynomial ("atoms with
  multiplicity") normal form over an algebraically closed field of
  characteristic zero, not the positive-measure moment-problem version.
* **No claim to formalize floating-point PSLQ as implemented in practice.**
  We formalize an exact-arithmetic PSLQ-class core in the CSV/HJLS
  normalization (Chen–Stehlé–Villard: equivalent to PSLQ up to scaling),
  because textbook PSLQ's `H`-matrix is irrational even on rational input.

## Changelog

* 2026-07-27 — FREEZE-0. Initial registry. `pslq_partial_correct`,
  `pslq_lower_bound`, `ov_completeness` are typed `True` placeholders pending
  their tier definitional layers (algorithm core, R3 vocabulary); their
  target statements are recorded in their docstrings. All other headlines are
  stated in full.
