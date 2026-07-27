# R0 Mathlib sweep (v4.32.0) — verdicts per needed lemma

Swept 2026-07-27 under `.lake/packages/mathlib/Mathlib`. Verdict legend:
CITE(`name`) = use directly; PORT = adapt/wrap a nearby result; BUILD = not in
Mathlib, prove in `R0_Kronecker/`.

## Hankel matrices
* Hankel matrix / Hankel rank / Kronecker's theorem: **BUILD** — no `Hankel`
  anywhere in Mathlib. Tier defs in `R0_Kronecker/Defs.lean` are the working
  ontology (row space = span of shifts).

## Linear recurrences
* `Mathlib/Algebra/LinearRecurrence.lean`: has `LinearRecurrence`,
  `IsSolution`, `solSpace`, `toInit` (solution ≃ initial values),
  `charPoly`, `geom_sol_iff_root_charPoly`. **No** link to generating
  functions, Hankel rank, or closed forms (file header says closed forms
  "currently not implemented"). Verdict: recurrence ⇔ rank and recurrence ⇔
  rational GF are both **BUILD**. We use a local
  `∃ d c, ∀ n, a (n+d) = ∑ i, c i * a (n+i)` predicate (defeq to
  `E.IsSolution`); Mathlib's structure adds nothing we need.

## Shift endomorphism / annihilating polynomial (rank → recurrence)
* Cayley–Hamilton for endomorphisms: **CITE(`LinearMap.aeval_self_charpoly`,
  `LinearMap.charpoly_monic`, `LinearMap.charpoly_natDegree`)**
  (`Mathlib/LinearAlgebra/Charpoly/Basic.lean`; needs `Module.Finite` +
  `Module.Free`, both automatic for a f.d. space over a field).
* Restrict shift to the row space: **CITE(`LinearMap.restrict`,
  `LinearMap.restrict_apply`, `Submodule.map_span`, `Submodule.span_le`)**.
* Submodule of f.d. is f.d.: **CITE(`Submodule.finiteDimensional_of_le`,
  `Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean:195`)**; span of finite
  set is FG: **CITE(`Submodule.fg_span`)**; `Module.Finite ↔ FG`:
  **CITE(`Module.Finite.iff_fg`, `Mathlib/RingTheory/Finiteness/Basic.lean:331`)**.
* `Polynomial.aeval_eq_sum_range` for expanding `aeval S χ`: **CITE**.

## Rational generating functions / power series
* Polynomial ↪ power series: **CITE(`Polynomial.coeff_coe`, `coe_mul`,
  `coe_sub`(ring hom), `coe_one`, `coe_C`, `coe_X`, `coe_pow`,
  `Polynomial.coeToPowerSeries.ringHom`)** (`RingTheory/PowerSeries/Basic.lean`).
* Coefficient extraction: **CITE(`PowerSeries.coeff_mul`,
  `PowerSeries.coeff_X_pow_mul'`, `PowerSeries.coeff_C_mul`,
  `PowerSeries.coeff_mk`)**; antidiagonal → range:
  **CITE(`Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk`)**;
  reindex: **CITE(`Finset.sum_range_reflect`, `Finset.sum_range_succ'`)**.
* Truncation for "tail-zero series is a polynomial":
  **CITE(`PowerSeries.trunc`, `PowerSeries.coeff_trunc`)**.
* `PowerSeries.invOfUnit` / `invUnitsSub` / `invOneSubPow`
  (`RingTheory/PowerSeries/Inverse.lean`, `WellKnown.lean`): present, but our
  statements multiply through by `q` (no division needed). Verdict: **not
  needed**; the `q(0) ≠ 0 → q unit` fact is implicit in the statement design.
* Kronecker equivalence rank ⇔ rational itself: **BUILD**.

## Partial fractions
* `Mathlib/Algebra/Polynomial/PartialFractions.lean`: division-free partial
  fraction decompositions over an integral domain / field of fractions
  (`div_eq_quo_add_rem_div_add_rem_div`, `eq_quo_mul_prod_pow_add_...`).
  Usable in principle for the atomic half, but it decomposes in `K(X)` and we
  would still owe the coefficient-of-`Xⁿ` extraction per pole. Verdict:
  **BUILD** the atomic half by strip-one-linear-factor induction instead
  (geometric resummation); cite only root extraction:
  **CITE(`IsAlgClosed.exists_root`, `Polynomial.dvd_iff_isRoot`,
  `Polynomial.degree_sub_lt`)**.

## Exponential polynomials / C-finite sequences / moment problems
* No C-finite/exponential-polynomial theory in Mathlib; no discrete moment
  problem. **BUILD**: mode lemmas (`n ↦ P(n)·λⁿ`), discrete antiderivative
  (char 0), shifted-resolvent inverse (`R(X+1) − (λ/μ)·R = S`), transient
  (finsupp) handling, closure of atomicity under `+`.
* Vanishing polynomial from vanishing on ℕ (char 0):
  **CITE(`Polynomial.eq_zero_of_infinite_isRoot`)** if needed by fallback
  routes; primary route avoids independence arguments entirely.
* Faulhaber for the antiderivative: `sum_range_pow`
  (`Mathlib/NumberTheory/Bernoulli.lean:298`, over ℚ) exists — **PORT**
  candidate, but a direct triangular-operator induction over `K` (char 0) is
  self-contained; primary verdict **BUILD**, Faulhaber as fallback.

## Summary
Mathlib provides all the linear-algebra and power-series *infrastructure*
(Cayley–Hamilton, span/FG lemmas, coefficient calculus) — every *theorem of
Kronecker type* (rank ⇔ recurrence ⇔ rational ⇔ atomic) is absent and must be
BUILT in this tier.
