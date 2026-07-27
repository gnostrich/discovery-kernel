# STATEMENTS

This file mirrors `Challenge.lean`, the statement registry of this repository.
**The Lean statements are the claims.** Prose in this repository never claims
anything `Challenge.lean` does not state. If a statement must change, it
changes in `Challenge.lean` and here first, with a dated note in the
changelog at the bottom.

## The thesis, in one paragraph

A problem maps input data to an answer. Some inputs are **ill-posed**: an
arbitrarily small perturbation changes the answer discontinuously. Write `Σ`
for the set of ill-posed inputs. The condition number `κ(x)` measures error
amplification and is infinite exactly on `Σ`. The **Condition Number
Theorem** (Demmel 1987, Numer. Math. 51, 251–289; canonical text
Bürgisser–Cucker, *Condition: The Geometry of Numerical Algorithms*, Springer
2013) says that for many problems `κ(x) = ‖x‖ / dist(x, Σ)` — conditioning is
inverse distance to ill-posedness. Therefore `dist(x, Σ)` is a **margin**: a
certified bound `dist(x, Σ) ≥ c > 0` licenses a finite-precision computation,
because data accurate to better than `c` yields a provably correct answer.
This repository certifies such margins at three altitudes: the scalar theory
(`Conditioning/`), one instance (`PSLQ`, where `Σ` = vectors admitting a
shorter integer relation), and the operator lift (`OV`).

## Statements (verbatim from Challenge.lean)

### PSLQ — integer relation detection (Σ = vectors admitting a shorter relation)

```lean
theorem pslq_partial_correct
    {n : ℕ} (x : Fin n → ℚ) (fuel : ℕ) (m : Fin n → ℤ)
    (h : R1.pslq x fuel = some m) :
    R1.IsIntRelation x m := sorry
```
**PROVEN** — `DiscoveryKernels.R1.pslq_partial_correct` (`R1_PSLQ/Core.lean`),
axioms `[propext, Classical.choice, Quot.sound]`.

```lean
theorem pslq_lower_bound
    {n : ℕ} (x : Fin n → ℚ) (fuel : ℕ) (hnone : R1.pslq x fuel = none)
    (m : Fin n → ℤ) (hm : R1.IsIntRelation x m) (k : Fin n)
    (hk : (R1.pslqState x fuel).coords m k ≠ 0)
    (hlast : ∀ j, k < j → (R1.pslqState x fuel).coords m j = 0) :
    (R1.pslqState x fuel).gsoNormSq x k ≤ ∑ i, ((m i : ℚ)) ^ 2 := sorry
```
**PROVEN** — `DiscoveryKernels.R1.pslq_lower_bound` (`R1_PSLQ/Bound.lean`),
axioms `[propext, Classical.choice, Quot.sound]`.

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
**PROVEN** — `DiscoveryKernels.R1.pslq_empirical_sound`
(`R1_PSLQ/Empirical.lean`), axioms `[propext, Classical.choice, Quot.sound]`.
This is the PSLQ instance of the condition number theorem: `p` is the input
precision, `M` the coefficient bound, `n * M * p` the certified margin, and
the separation hypothesis is the statement that the input is at distance more
than that margin from `Σ`.

### OV — operator-valued lift (STATEMENTS ONLY, under human-review gate)

```lean
theorem ov_license
    {B : Type} [Ring B] (M : ℕ → B) :
    (R3.HasFiniteOVHankelRank B M ↔ R3.HasFiniteRealization B M) ∧
      (R3.HasFiniteRealization B M ↔ R3.IsFinitelyAtomicOV B M) := sorry
```
**DECLARED DEFECTIVE, AWAITING REPLACEMENT.** This FREEZE-0 draft is *false*
as stated, not merely imprecise: unconditional `rational ⟺ atomic` fails on
`M n = cos nθ` over `ℝ` and on the Jordan block `n·λⁿ` over `ℂ`, and the
span-of-shifts rank definition has a Noetherian gap against realizations. A
corrected replacement (positivity hypotheses, star-corrected atomicity,
Fliess stable-submodule rank) compiles in `R3_OV/CHALLENGE-R3.proposed.lean`
and is **approved in direction, awaiting human sign-off on exact statements**
before entering `Challenge.lean`.

```lean
theorem ov_completeness : True := sorry
```
**PLACEHOLDER**, replacement drafted in `R3_OV/CHALLENGE-R3.proposed.lean`
under the same gate.

#### Collapse test: result of the operator lift (PROVED, not proposed)

The OV tier was opened on the thesis that *the condition number of an
operator-valued problem is an element of `B`*. That thesis was tested
deliberately, as required, and **the element-valued form is refuted**. The
following are proved in `R3_OV/Cond.lean` with zero sorries and axioms
`[propext, Classical.choice, Quot.sound]`:

* `globalInf_collapses` — the naive `dist_B`, defined as a global infimum over
  `Σ`, is identically **zero**, exhibited in the most favourable instance
  available: `B = ℝ × ℝ` (commutative, a lattice), `E = id` (no information
  lost), `x = (1,2)` invertible with `κ = 2`. `Σ` is cheap in every direction
  of `B`, so any global infimum is useless; the bound must be compressed to
  `ker y`.
* `bvaluedDistance_not_scalar` — the surviving object does **not** collapse to
  `λ_min` or to a norm: `(1,2)` and `(2,1)` over `ℝ × ℝ` share every scalar
  condition invariant (`‖x‖ = 2`, `σ_min = 1`, `κ = 2`) yet have distinct
  `B`-valued distances `(1,4)` and `(4,1)`, both strictly above the best
  scalar margin.
* `isMargin_diagonal_iff` and `bvaluedDistance_fails_of_no_infimum` —
  `dist_B` is element-valued for all `2×2` inputs **iff** the positive cone of
  `B` is an inf-semilattice. By Kadison's anti-lattice theorem that fails over
  **every factor**. So `dist_B` is a *certificate set*, not an element of `B`,
  precisely for the noncommutative algebras this tier exists to serve.

Consequently **we do not claim that the operator-valued condition number is an
element of `B`**; we claim the opposite, and it is proved. The honest residue
is a dichotomy: for abelian `B` the margin set is fibrewise a *componentwise*
condition number, which is occupied literature (Skeel/Rohn/Higham — see
`Conditioning/SWEEP.md` S2), so there is no novelty there; for noncommutative
`B` the object is not element-valued at all, and it is the certificate-set
formulation together with the anti-lattice obstruction that no literature was
found to have.

### Conditioning — the headline tier

Statements are in preparation; they land in `Challenge.lean` (first section,
ahead of PSLQ) when the tier's proposals are reviewed. Nothing is claimed
here until then.

## Status of every `sorry`

Per STEERING 02, sorries are classified:

* **Registry sorries** — every headline in `Challenge.lean` is `:= sorry` *by
  construction*. `Challenge.lean` is a statement registry, never a proof
  site; solutions live tier-side and are matched to it by the comparator
  (definitional-equality check plus per-theorem axiom allowlist). A registry
  `sorry` is not an open problem.
* **Targets** (intended to be proven): the OV tier's statements are now
  targets, not a permanent frontier marker. Their difficulty is real and no
  timeline is claimed.
* **Declared-open**: the infinite-dimensional operator-valued license in the
  sense of Mai–Speicher–Yin is declared open. We do not claim it.

## What we do NOT claim

* **No novelty for Eckart–Young–Mirsky, Weyl, Courant–Fischer, or
  Davis–Kahan.** These are formalized in Lean 4, sorry-free, in the
  third-party library `YuanheZ/lean-stat-learning-theory` (core development
  accepted at ICML 2026) — not in Mathlib, and not framed as conditioning,
  but formalized. Eckart–Young–Mirsky in particular *is* the distance
  identity for the rank-deficiency ill-posed set, so we claim no priority on
  it. See `Conditioning/SWEEP.md` (S1) for the full verdict and evidence.
  What this repository claims in that area is the conditioning layer that no
  proof assistant was found to have: certified, executable, exact-arithmetic
  **lower bounds** on `dist(x, Σ)` with soundness theorems, together with
  **sharpness witnesses** where the bound degenerates.
* **No novelty for floating-point or rounding-error verification.** That
  field is mature and occupied (Flocq, VCFloat2, PRECiSA, Boldo et al.'s
  Runge–Kutta round-off analysis, ITrees-based numerical methods in
  Isabelle/HOL). We bound conditioning, not rounding, and make no
  floating-point claim.
* **No novelty for LLL formalization.** LLL is formalized in Isabelle/HOL
  (Thiemann et al., 2018–2020) and announced for Lean via the Hex library
  (FLoC 2026); see `R1_PSLQ/DEPS.md`. This repository depends on neither.
* **No claim to have formalized control theory.** arXiv 2607.19727
  (Doll–Shames, 22 July 2026) formalizes Lyapunov stability and the
  small-gain theorem in Lean; pole assignment — on Demmel's list — is not
  formalized there, and is not formalized here either.
* **Soundness only, never completeness.** Every checker theorem in this
  repository has the shape `checker x = true → P x`. None claims the
  converse: a checker that says "no" tells you nothing. PSLQ inherits this —
  `pslq_partial_correct` says a *report* is a genuine relation, never that
  the core finds a relation whenever one exists.
* **No floating-point claims.** Everything is exact arithmetic (ℚ, ℤ) or
  interval-/rational-certified statements about real quantities. No `Float`
  appears in any statement or definition.
* **No claim to formalize floating-point PSLQ as implemented in practice.**
  We formalize an exact-arithmetic PSLQ-class core in the CSV/HJLS
  normalization (Chen–Stehlé–Villard: equivalent to PSLQ up to scaling),
  because textbook PSLQ's `H`-matrix is irrational even on rational input.
* **No claim that `pslq_lower_bound` holds in a `min`-over-all-`j` form.**
  It does not, and packaging it that way would be a fake theorem: the `n`
  projected basis columns span an `(n−1)`-dimensional space, so exactly one
  Gram–Schmidt direction necessarily degenerates and the `min` form is the
  trivial bound `0`. The index `k` is therefore stated explicitly.
* **No claim about sibling repositories.** `certified-positivity` is frozen
  prior art, read and adapted at schema level only (its Lean pin differs);
  `realization-lean` is not a dependency of this repository.
* **No claim to prove the operator-valued license.** See the sorry
  classification above.

## Changelog

* 2026-07-27 — FREEZE-0. Initial registry (then four tiers).
  `pslq_partial_correct`, `pslq_lower_bound`, `ov_completeness` typed `True`
  placeholders pending their tier definitional layers.
* 2026-07-27 — **DESCOPE (STEERING 01).** R0 (scalar license / Kronecker)
  and R2 (`DiscoveryKernel` interface) removed. Removed headlines:
  `hankel_finite_rank_iff_rational`, `rational_iff_finitely_many_atoms`,
  `discovery_kernel_inhabited`. The completed R2 artifact (frozen signature,
  lemma library, zero-sorry toy instance) is preserved in git history at the
  pre-descope commit.
* 2026-07-27 — **`pslq_partial_correct` refined** from the `True` placeholder
  to the real statement against the exact-arithmetic core `R1.pslq`, which
  landed the same day:
  `(h : R1.pslq x fuel = some m) : R1.IsIntRelation x m`.
  Justification: the core proves strictly more than the registry stated, and
  an unstated proof is not yet a claim. Soundness only; no completeness
  claim is made or implied. Solution registered in the comparator and
  audited green.
* 2026-07-27 — **`pslq_lower_bound` refined** from the `True` placeholder to
  the Borwein–Lisoněk-form statement over the state's own rational
  (CSV/HJLS-normalized) Gram–Schmidt data. Justification: the bound is now
  proven, and it is stated with the explicit index `k` rather than a `min`
  over all `j`, because the `min` form is provably the trivial bound `0` (see
  non-claims above). The unused hypothesis `hnone` is retained for
  faithfulness to the "while no relation has been reported" reading; it makes
  the headline weaker than what is proved, never stronger.
* 2026-07-27 — **Novelty claim narrowed (STEERING 02, sweep S1).** The
  blocking prior-art sweep found Eckart–Young–Mirsky, Weyl, Courant–Fischer
  and Davis–Kahan already formalized in Lean 4 outside Mathlib. The
  corresponding non-claim above was added before any Conditioning Lean was
  written. Sweep S2 found the real-valued structured/mixed/componentwise
  condition number literature to be large and mature, and no algebra-valued
  condition number; the OV tier is on notice for the named collapse test.
* 2026-07-27 — **Conditioning tier opened** as the headline claim, with
  `Conditioning/SWEEP.md` (S1, S2) committed before any Lean in that tier.
