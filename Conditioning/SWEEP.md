# Conditioning tier — blocking prior-art sweeps (S1, S2)

Date of sweep: **2026-07-27**. Author: orchestrator. Method: web search
(WebSearch/WebFetch) plus direct inspection of the local Mathlib v4.32.0
checkout and of the frozen prior-art repo `gnostrich/certified-positivity`.

Both verdicts below were written **before any Lean was authored in this
tier**, as required.

---

## S1 — Has any condition number theorem, or any certified bound on
## distance-to-ill-posedness, been formalized in a proof assistant?

**VERDICT: PARTIALLY OCCUPIED. The novelty claim survives but must be
narrowed, and `STATEMENTS.md` says so explicitly.**

### What IS already formalized (occupied — we claim no novelty here)

* **Eckart–Young–Mirsky is formalized in Lean 4**, outside Mathlib, in
  [`YuanheZ/lean-stat-learning-theory`](https://github.com/YuanheZ/lean-stat-learning-theory)
  (core development accepted at ICML 2026). Verified by reading the
  repository's own README: the constant is `Matrix.eckartYoungMirsky_hdp`,
  in its `MatrixInfra/` module layer. The same library formalizes
  **Weyl's inequality** (`LinearMap.IsSymmetric.abs_eigenvalues_sub_le_opNorm`
  plus a singular-value variant), **Courant–Fischer**
  (`LinearMap.IsSymmetric.eigenvalues_eq_courantFischerMaxMin_succ` and
  singular-value versions), and **Davis–Kahan**
  (`LinearMap.IsSymmetric.davisKahan_eigenvector_angle_hdp`). The library
  states it contains no `sorry`, `axiom`, `admit`, or `native_decide`.

  **This matters directly.** Eckart–Young–Mirsky *is* the distance identity
  for the rank-deficiency ill-posed set: the distance from a matrix to the
  nearest matrix of rank ≤ k is σ_{k+1}. So the central *identity* behind
  "distance to ill-posedness" already exists in Lean 4 for the matrix case.
  We must not claim to be first to formalize it, and we do not.

  Two qualifications, both verified, neither of which rescues a broad
  novelty claim but which do bound what is occupied: (a) that README
  contains **no mention of condition numbers, distance to singularity,
  rank-deficiency metrics, or ill-posedness** — the theorems are formalized
  as matrix perturbation theory for statistical learning, not as
  conditioning; (b) it is a third-party library, **not Mathlib**, so it is
  not available to us by default and its pin is unverified against ours.

* **Control theory in Lean**: arXiv **2607.19727**, "Foundations of
  Machine-Checked Control Theory in Lean" (Moritz Doll, Iman Shames, Univ.
  of Melbourne; submitted 22 July 2026) formalizes **Lyapunov stability
  theory** (via neighbourhood filters, covering points and sets, and
  continuous/discrete/hybrid systems) and the **small-gain theorem**
  (input-output systems as relations, without the usual well-posedness
  assumption). Checked against this sweep's scope: it does **not** address
  condition numbers or distance to ill-posedness. Pole assignment — which is
  on Demmel's list — is **not** formalized there. The adjacent room is
  occupied; this specific room is not. Cited either way, as instructed.

* **Floating-point / rounding-error verification** is a mature, occupied
  field, and is *not* what this tier does: Flocq and VCFloat2 in Coq
  (round-off error bounds for floating-point C programs), PRECiSA,
  Boldo et al.'s verified round-off analysis of Runge–Kutta methods, and
  "Verifying Numerical Methods with Isabelle/HOL" (arXiv 2511.20550, an
  ITrees-based framework for numerical programs). These bound *rounding
  error*; none of them proves a *conditioning* or distance-to-ill-posedness
  theorem. Our tier is exact/interval-certified and makes no floating-point
  claim, so there is no overlap.

### What is NOT formalized anywhere found (vacant — where our claim lives)

No result in any of Lean, Coq/Rocq, Isabelle/AFP, HOL, or ACL2 was found
for any of:

1. **The Condition Number Theorem itself** — κ(x) = ‖x‖ / dist(x, Σ)
   (Demmel 1987) — as a formal statement relating a conditioning quantity to
   a distance to an ill-posed set.
2. **Σ framed as an ill-posed set** with certified *lower bounds*
   `dist(x, Σ) ≥ c > 0` used to license a finite-precision computation.
3. **Executable checkers proven sound for such bounds** — a `Bool` decision
   procedure with `checker x = true → dist(x, Σ) ≥ c`.
4. **Sharpness witnesses** — certified inputs where the bound degenerates to
   exactly zero, proving a bound is tight rather than conservative.

### Mathlib v4.32.0, checked directly in the local checkout

* `Mathlib/Analysis/InnerProductSpace/SingularValues.lean` **exists**:
  `LinearMap.singularValues : ℕ →₀ ℝ` with `singularValues_nonneg`,
  `singularValues_antitone`, `card_support_singularValues`,
  `injective_iff_forall_lt_finrank_singularValues_pos`, and the bridge
  `sq_singularValues_fin` / `hasEigenvalue_adjoint_comp_self_sq_singularValues`
  (σᵢ² are eigenvalues of `T†T`). Stated for **linear maps, not matrices** —
  a `Matrix ↔ LinearMap` transport is the first thing to BUILD.
* **Zero hits** for "condition number" anywhere in Mathlib.
* **No SVD, no `Matrix.singularValues`, no Eckart–Young, no
  distance-to-singularity** in Mathlib.
* **Perturbation theory in Mathlib** (re-verified 2026-07-28): no Weyl
  *eigenvalue perturbation* inequality (the `Weyl` hits in Mathlib are all
  Lie-theoretic — Weyl groups, weights, root systems), no Courant–Fischer
  min-max, no Bauer–Fike. **Gershgorin IS present** — see the correction
  below; the original entry here was FALSE.
* Matrix operator norm exists but is **scoped and opt-in**
  (`Mathlib/Analysis/CStarAlgebra/Matrix.lean`, `Matrix.l2_opNorm_def`,
  the C*-identity `l2_opNorm_conjTranspose_mul_self`), under
  `scoped[Matrix.Norms.L2Operator]`. Failing to `open scoped` it silently
  selects a different norm instance — a real footgun for a norm-based
  certificate.

### Consequence for the novelty claim (binding on STATEMENTS.md)

We do **not** claim to be first to machine-check Eckart–Young–Mirsky, Weyl,
Courant–Fischer, or Davis–Kahan; those are formalized in Lean 4 in
`lean-stat-learning-theory`. We do **not** claim any novelty in
floating-point error verification. What this tier claims is the
*conditioning* layer that no assistant was found to have: certified,
executable, exact-arithmetic **lower bounds** on `dist(x, Σ)` with soundness
theorems, together with **sharpness witnesses** where the bound degenerates.

---

## S2 — Does an operator-valued / block-structured condition number already
## exist in numerical analysis, valued in an algebra rather than in ℝ?

**VERDICT: THE REAL-VALUED STRUCTURED THEORY IS HEAVILY OCCUPIED; AN
ALGEBRA-VALUED CONDITION NUMBER WAS NOT FOUND. The OV tier is not
duplicative, but it is on notice — see the named failure mode.**

### Occupied, and larger than expected (must be cited, never re-derived)

**Structured, mixed, and componentwise condition numbers are a mature
subfield**, covering more ground than the term "structured" suggests:

* Structured mixed and componentwise condition numbers for **matrix
  inversion and linear systems** over structured classes — Cauchy,
  Vandermonde, **Toeplitz, Hankel**, circulant — via Kronecker-product
  techniques (J. Comput. Appl. Math.). Note Hankel appears here explicitly.
* Structured condition numbers for **matrix factorizations** (LU, Cholesky,
  QR) of structured matrices, with explicit expressions specializing to the
  normwise, mixed, and componentwise cases.
* **Mixed and componentwise condition numbers for matrix decompositions**
  (Theoret. Comput. Sci.); componentwise analysis is sharper than normwise
  for badly scaled or sparse data.
* Structured condition numbers for **total least squares with linear
  equality constraint** (arXiv 2105.08132), for **quasiseparable
  parameterized** multiple-RHS systems (arXiv 1910.05450), and for
  **symmetric algebraic Riccati equations** (arXiv 1601.03787).
* A **structured condition number for self-adjoint polynomial matrix
  equations with applications in linear control** (J. Comput. Appl. Math.) —
  the closest published object to "conditioning with operator structure".
* Higham, *Condition Numbers and Their Condition Numbers* — conditioning of
  the conditioning map itself.

**Crucially: every one of these is real-valued** (or a vector of reals in
the componentwise case). They measure a structured perturbation with a
scalar. None is valued in an algebra `B`.

### Not found

No condition number **valued in a C*-algebra or von Neumann algebra**, and
no Condition Number Theorem with distance measured in a conditional
expectation `E_B`, was found. The nearest genuinely algebra-valued neighbour
is the **index of a conditional expectation** (Watatani/Jones index for
finite-index inclusions; `C(X)`-valued conditional expectations), which is an
algebra-valued invariant of an inclusion — adjacent in flavour, unrelated in
purpose. Hilbert C*-module perturbation theory (e.g. perturbation of
continuous frames in Hilbert C*-modules) exists but is not conditioning.

### Consequence for the OV tier (binding)

The OV tier is **not** duplicating an existing object; the search supports
that an algebra-valued condition number is genuinely unclaimed. But the
absence of a literature is itself a warning, and the tier is subject to the
operator's named failure mode, which is to be tested deliberately and
reported as a first-class result either way:

> if `dist_B` provably collapses to `λ_min` or to a norm, the definition is a
> renaming and the tier is dead.

The heavily-occupied structured/componentwise literature above is the honest
comparison class: if `dist_B` turns out to be equivalent to a structured or
componentwise condition number already in that literature, that is also a
collapse, and must be reported as one.

---

## Queries used (verbatim, 2026-07-27)

S1:
1. `condition number theorem formalized Lean Mathlib Coq Isabelle proof assistant "distance to ill-posedness"`
2. `formalized verified "condition number" numerical analysis Isabelle HOL Archive of Formal Proofs matrix`
3. `arXiv 2607.19727 control theory Lean formalization Lyapunov small-gain`
4. `Coq Rocq formalization "condition number" OR "Eckart-Young" matrix perturbation distance nearest singular matrix verified`
5. `Coq VCFloat Flocq Boldo verified rounding error analysis numerical program "condition number" formal proof`
6. `Lean 4 Mathlib formalization "smallest singular value" OR "distance to the nearest singular matrix" OR "Eckart-Young" theorem`
7. Direct fetch of `github.com/YuanheZ/lean-stat-learning-theory` README.
8. Local greps of Mathlib v4.32.0 for `condition number`, `singularValue`, SVD, Gershgorin, perturbation.

S2:
1. `"structured condition number" "block condition number" matrix-valued componentwise condition number operator-valued numerical analysis`
2. `"condition number" valued in C*-algebra OR "operator-valued" conditional expectation perturbation bound Hilbert module numerical analysis`

## Caveat

This is absence of evidence from targeted web search plus direct inspection
of Mathlib, not a proof of nonexistence. Any agent that finds a formalization
contradicting S1 or S2 must report it immediately and amend `STATEMENTS.md`
before further claims are made.

---

## CORRECTION — 2026-07-28 (STATEMENT-DEFECT class)

**The claim "Mathlib has no Gershgorin" was FALSE.** Mathlib v4.32.0 contains
`Mathlib/LinearAlgebra/Matrix/Gershgorin.lean` (ported from mathlib3), with:

* `Matrix.eigenvalue_mem_ball` — eigenvalue localisation over any
  `NormedField`, any `Fintype` index;
* `Matrix.det_ne_zero_of_sum_row_lt_diag` and `Matrix.det_ne_zero_of_sum_col_lt_diag`
  — strict diagonal dominance ⟹ nonsingular.

Consequences, applied:

* `Conditioning/Gershgorin.lean`'s `gershgorin_disc` is a specialization of
  `Matrix.eigenvalue_mem_ball` to `ℝ`/`Fin n`/real eigenvalues. **No novelty
  claimed.**
* `Conditioning/Checker.lean`'s `det_ne_zero_of_strict_diag_dominance`
  duplicates `Matrix.det_ne_zero_of_sum_row_lt_diag` at weaker generality.
  **No novelty claimed.**
* `gershgorin_rayleigh_floor` **survives**, verified rather than assumed: the
  Rayleigh quadratic-form floor `μ‖x‖² ≤ xᵀMx` under diagonal dominance is a
  different statement from eigenvalue localisation, and Mathlib's Gershgorin
  file contains exactly the three lemmas listed above and nothing else.

**Root cause.** A sweep verdict is the one artifact in this repository that is
*asserted* rather than kernel-checked. The comparator verifies statements and
axioms; nothing verified the sweep. This absence claim was propagated from a
subagent report into a verdict without an independent grep, and the method
note then described a grep that had not been run.

**Re-verification of every other absence claim in S1** (greps re-run
2026-07-28 against the pinned Mathlib v4.32.0 checkout; file-hit counts):

| term | hits | verdict |
|---|---|---|
| `condition number` / `conditionNumber` | 0 / 0 | absent, as claimed |
| `Gershgorin` | **2** | **PRESENT — claim was false** |
| `Courant` | 0 | absent, as claimed |
| `Bauer`, `Fike` | 0, 0 | absent, as claimed |
| `Eckart`, `Mirsky` | 0, 0 | absent from Mathlib, as claimed |
| `svd` / `SVD` | 0 / 0 | absent, as claimed |
| `singularValue` / `SingularValue` | 2 / 2 | present, as claimed |
| `Weyl` | 13 | present but **Lie-theoretic only**; no eigenvalue perturbation inequality |

**Process fix.** Absence claims are now machine-checked in CI by
`comparator/sweep_check.py`, which re-runs these greps against the pinned
Mathlib and fails the build if anything claimed absent is found. A false
absence claim now breaks CI instead of surviving into prose.
