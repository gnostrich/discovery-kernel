# STATEMENTS

This file mirrors `Challenge.lean`, the statement registry of this repository.
**The Lean statements are the claims.** Prose in this repository never claims
anything `Challenge.lean` does not state. If a statement must change, it
changes in `Challenge.lean` and here first, with a dated note in the
changelog at the bottom.

Sibling repositories (this repo makes no claims about their content):

* `gnostrich/realization-lean` — owns the scalar license (Kronecker
  realizability, rank stabilization, Kalman uniqueness, and related spine).
* `gnostrich/certified-positivity` — frozen prior art (read/cite/import
  only): decidable-check-soundness (`checkPDq_sound`) and expand/halt
  certificate schemas.

## Statements (verbatim from Challenge.lean)

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
* **No scalar-license (Kronecker) claim in this repository.** That material
  lives in `gnostrich/realization-lean`; it is not duplicated here.
* **No abstract detector interface.** No `DiscoveryKernel`-style abstraction
  is designed up front; if ever wanted, it gets extracted from working
  instances elsewhere. (An earlier draft interface was descoped 2026-07-27;
  see changelog.)
* **No floating-point claims.** Everything is exact arithmetic (ℚ, ℤ) or
  interval-/rational-certified statements about real quantities. No `Float`
  appears in any statement.
* **No novelty claim for LLL formalization.** LLL is formalized in
  Isabelle/HOL (Thiemann et al., 2018–2020) and announced for Lean via the
  Hex library (FLoC 2026); see `R1_PSLQ/DEPS.md` for what this repository
  does and does not depend on.
* **No claim to formalize floating-point PSLQ as implemented in practice.**
  We formalize an exact-arithmetic PSLQ-class core in the CSV/HJLS
  normalization (Chen–Stehlé–Villard: equivalent to PSLQ up to scaling),
  because textbook PSLQ's `H`-matrix is irrational even on rational input.
* **No claims about sibling repositories.** `certified-positivity` is frozen
  prior art; `realization-lean` is under construction; this repo cites and
  may import them but claims nothing on their behalf.

## Changelog

* 2026-07-27 — FREEZE-0. Initial registry (then four tiers).
  `pslq_partial_correct`, `pslq_lower_bound`, `ov_completeness` typed `True`
  placeholders pending their tier definitional layers; all other headlines
  stated in full.
* 2026-07-27 — **DESCOPE (operator steering directive).** R0 (scalar
  license / Kronecker) and R2 (`DiscoveryKernel` interface) removed from this
  repository: the scalar license is owned by `gnostrich/realization-lean`;
  no abstract interface is designed up front. Removed headlines:
  `hankel_finite_rank_iff_rational`, `rational_iff_finitely_many_atoms`
  (relocated in realization-form to realization-lean),
  `discovery_kernel_inhabited` (dropped; the completed R2 artifact — frozen
  signature, lemma library, zero-sorry toy instance — is preserved in git
  history at the pre-descope commit). R1 and R3 statements are unchanged.
