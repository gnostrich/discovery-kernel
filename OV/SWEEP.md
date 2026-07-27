# OV tier — blocking sweep S3 (symbolic / Łojasiewicz fallback)

Date of sweep: **2026-07-27**. Author: orchestrator. Method: targeted web
search plus direct fetch of the most relevant paper's abstract. Written
**before any Lean was authored for the symbolic form**, per STEERING 02a §4.

Companion sweeps S1 (condition number theorem formalization) and S2
(operator-valued / structured condition numbers) are in
`Conditioning/SWEEP.md`.

---

## S3 — Has an operator-valued or non-commutative Łojasiewicz inequality been
## formulated?

**VERDICT: THE MATRIX-VALUED GROUND IS OCCUPIED — AND OCCUPIED PRECISELY ON
OUR OBJECT. The non-commutative / operator-valued case, and the
per-direction exponent tuple, were not found. The symbolic fallback is
viable only in the exact shape STEERING 02a specifies, and its collapse test
coincides with its occupancy test.**

### Occupied, and closer to home than expected

* **Łojasiewicz inequalities with explicit exponent for the smallest
  singular value function** (arXiv 1604.02805). Verified by fetching the
  abstract. This proves a nonsmooth Łojasiewicz gradient inequality for the
  smallest singular value function `f(x)` of a `p×q` **real polynomial
  matrix**, with an explicit exponent `1 − 2/𝓡(n+p, 2d+2)`, and — decisively
  for us — it also establishes **"versions of the Łojasiewicz inequality for
  the distance function with explicit exponents, locally and globally"** for
  that same smallest-singular-value function.

  This is the *same object* as this repository's Conditioning tier: `σ_min`,
  and a distance-to-degeneracy bound. The symbolic picture of "distance as
  order of vanishing" is therefore **already carried out for polynomial
  matrices, with computable exponents**. We claim no novelty for it.

  Two properties of that work bound what remains open, and both matter:
  (a) the setting is **commutative** — real polynomial matrices, not
  operator-algebra valued; (b) the exponent is a **single real number**, not
  direction-dependent.

* **Łojasiewicz-type inequalities with explicit exponents for the largest
  eigenvalue function of real symmetric polynomial matrices**
  (arXiv 1501.01419) — the eigenvalue counterpart, same commutative,
  single-exponent character.

* **Kurdyka–Łojasiewicz is heavily used in optimization**, exactly as
  STEERING 02a warned. The KL property underpins convergence analysis for
  nonsmooth nonconvex problems; there is a developed *calculus of the KL
  exponent* with linear-convergence applications (Foundations of
  Computational Mathematics), and extensions to semialgebraic, Nash and
  nonsmooth settings. All of it is **real-valued**.

* **Classical theory**, cited and never re-derived: Łojasiewicz (1959, 1965);
  the order-of-vanishing proof of the one-dimensional case; Bierstone–Milman
  on resolution and Łojasiewicz exponents; Kurdyka (1998).

### Not found

* **No Łojasiewicz inequality over a C\*-algebra or von Neumann algebra**, and
  no non-commutative Łojasiewicz inequality of any kind. Searches on the
  operator-algebra framing returned only classical commutative real-analytic
  geometry. The nearest adjacent object is Putinar's work on positive
  polynomials in scalar and matrix variables / free analysis, which is
  positivity and the spectral theorem, not a vanishing-order inequality.
* **No per-direction exponent tuple.** Every exponent found in the literature
  is a single real number (or an infimum of admissible exponents). The
  multi-component, "which directions vanish to which order" object that
  STEERING 02a proposes as the anti-collapse feature was not found anywhere.

### Consequence, and a sharpened collapse test (binding on the tier)

The novelty available to the symbolic form is **not** "Łojasiewicz for
conditioning" — that exists, for polynomial matrices, on `σ_min`, with
explicit exponents, including the distance-function version. What was not
found is exactly the two properties STEERING 02a singles out: the
**non-commutative / operator-valued** setting, and the **per-direction
exponent tuple**.

This makes the addendum's symbolic collapse test and the occupancy question
**the same test**:

> If the exponent tuple is always constant across directions, the
> multi-component claim is vacuous *and* the object degenerates to a single
> Łojasiewicz exponent — which is the published, occupied case
> (arXiv 1604.02805). Either way the symbolic form dies, and the negative is
> to be reported plainly in `TIER-STATUS.md`.

So the tier must exhibit a witness where **two directions have genuinely
different vanishing orders**, or concede the form. That is the analogue of
the metric form's surviving witness (`bvaluedDistance_not_scalar`, where two
inputs share every scalar invariant but differ in `B`-valued distance).

### Boundary restated (from STEERING 02a, not negotiable)

Both forms require the object to sit in a **parametrised family**. Where no
family exists, neither applies, and a family must not be invented to make the
machinery fit — an imposed parametrisation is the gameable proxy this
programme forbids. The extension to symbolic proof search over a proof
library is **closed**: statements in a formal library are not parametrised,
have no discriminant, and admit no order of vanishing.

## Queries used (verbatim, 2026-07-27)

1. `"Łojasiewicz inequality" operator algebras noncommutative "Lojasiewicz exponent" matrix-valued`
2. `Kurdyka-Lojasiewicz property noncommutative operator-valued free algebra optimization convergence`
3. `Lojasiewicz inequality "C*-algebra" OR "von Neumann algebra" spectral analytic germ vanishing order noncommutative real algebraic geometry`
4. Direct fetch of `arxiv.org/abs/1604.02805` (smallest singular value function).

## Caveat

Absence of evidence from targeted search, not proof of nonexistence. Any
agent finding a non-commutative Łojasiewicz inequality, or a per-direction
exponent tuple in the literature, must report it immediately and amend
`STATEMENTS.md` before further claims are made.
