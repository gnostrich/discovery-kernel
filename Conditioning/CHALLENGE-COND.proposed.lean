/-
Copyright (c) 2026 discovery-kernels contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.

# PROPOSED Conditioning section of `Challenge.lean`

This file is a **proposal**, not the registry. It compiles (`lake env lean
Conditioning/CHALLENGE-COND.proposed.lean`) and every headline ends `:= sorry`,
exactly as `Challenge.lean` requires. The orchestrator is asked to place the
block below — from the `-- ==== COND ====` banner to the end of the namespace
— **first** in `Challenge.lean`, and to add

    import Conditioning.Sharpness

to `Challenge.lean`'s import list (one line: `Sharpness` transitively imports
`Checker → Margin → Gershgorin → Defs`; `Bridge` is pulled in by the same line
only if the orchestrator prefers, but `cond_dist_to_illposed`'s *statement*
needs nothing from `Bridge` — only its proof does, so `Bridge` must appear in
`comparator/AxiomCheck.lean`, see `COMPARATOR-ROWS.md`).

**Footgun, handled:** `cond_dist_to_illposed` mentions `Metric.infDist` on
matrices, which needs Mathlib's ℓ² operator-norm instance. That instance is
`scoped[Matrix.Norms.L2Operator]` and is NOT Mathlib's default `Matrix` norm.
The statement below therefore sits inside its own
`section L2OperatorNormScope` with `open scoped Matrix.Norms.L2Operator`, so
the scope is opened for that single declaration and cannot silently change the
meaning of any other statement in `Challenge.lean`. Removing that `open` does
not produce an error — it produces a *different theorem about a different
norm*. Do not remove it, and do not hoist it to the top of the file.
-/
import Conditioning.Sharpness
import Conditioning.Bridge

open scoped BigOperators Matrix

namespace DiscoveryKernels.Challenge

-- ==== COND ==== conditioning: certified distance to ill-posedness ==========

/-- **Executable exact-rational conditioning checker, sound.** If the
`Bool`-valued decision procedure `Cond.condCheck` — pure `ℚ` arithmetic, no
`Float`, no `native_decide` — accepts the rational matrix `A` at margin `c`,
then the real matrix `Cond.toReal A` has smallest singular value at least `c`:
`c‖v‖ ≤ ‖Av‖` for every `v`, written as `Cond.SigmaMinGE`.

**Soundness only, by design**: "says yes ⟹ the bound holds". No completeness is
claimed; `cond_gershgorin_wall` below certifies an input where the checker says
nothing useful even though the input is well-posed. Adapted at schema level
(no code imported; pins differ) from `certified-positivity`'s
`checkPDq_sound`. -/
theorem cond_check_sound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (c : ℚ)
    (h : Cond.condCheck A c = true) :
    Cond.SigmaMinGE (Cond.toReal A) (c : ℝ) := sorry

section L2OperatorNormScope
open scoped Matrix.Norms.L2Operator

/-- **THE HEADLINE — a certified distance to ill-posedness, from an executable
exact-rational check.** `Σ` is `Cond.SigmaSing n`, the set of singular matrices:
the ill-posed inputs of the matrix-inversion problem, at which the answer is a
discontinuous function of the data. If the checker accepts `A` at margin `c`,
then

    c ≤ dist(A, Σ)

where the distance is Mathlib's `Metric.infDist` in Mathlib's **ℓ² operator
norm** (scope `Matrix.Norms.L2Operator`; see the file header). By the Condition
Number Theorem (Demmel, Numer. Math. 51 (1987) 251–289; Bürgisser–Cucker,
*Condition*, Springer 2013) this is exactly an upper bound on the condition
number, and it is what licenses a finite-precision computation: data accurate
to better than `c` determines the answer.

`0 < n` is load-bearing, not decoration: for `n = 0` the empty matrix has
`det = 1`, so `Σ = ∅` and `Metric.infDist _ ∅ = 0`. -/
theorem cond_dist_to_illposed {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (c : ℚ)
    (hn : 0 < n) (h : Cond.condCheck A c = true) :
    (c : ℝ) ≤ Metric.infDist (Cond.toReal A) (Cond.SigmaSing n) := sorry

end L2OperatorNormScope

/-- **THE TIER'S POINT — a certified margin licenses a finite-precision
computation.** If the exact-rational checker accepts `A` at margin `c`, and the
right-hand side of the linear system `A x = b` is known only to within `ε` in
the Euclidean norm, then the solution is still determined to within `ε / c`.
Stated squared, so no square roots and no `Float` appear:

    c² ‖x - y‖² ≤ ε².

This is the linear-algebra analogue of `pslq_empirical_sound`: a certified
distance to ill-posedness converts input accuracy into output accuracy. -/
theorem cond_licenses_computation {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (c : ℚ)
    (h : Cond.condCheck A c = true) (x y b b' : Fin n → ℝ)
    (hx : Cond.toReal A *ᵥ x = b) (hy : Cond.toReal A *ᵥ y = b') (ε : ℝ)
    (hε : Cond.sqNorm (b - b') ≤ ε ^ 2) :
    (c : ℝ) ^ 2 * Cond.sqNorm (x - y) ≤ ε ^ 2 := sorry

/-- **Certified margin to the zero-eigenvalue set.** For a Hermitian (real
symmetric) rational matrix, acceptance by the exact-rational checker at margin
`c` certifies `c ≤ |λ|` for **every** one of Mathlib's own
`Matrix.IsHermitian.eigenvalues`. Since `Σ` for the symmetric eigenvalue
problem is exactly the matrices with a zero eigenvalue, this is the distance
statement in eigenvalue form. -/
theorem cond_eigenvalue_margin {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (c : ℚ)
    (h : Cond.condCheck A c = true) (hA : (Cond.toReal A).IsHermitian) (j : Fin n) :
    (c : ℝ) ≤ |hA.eigenvalues j| := sorry

/-- **SHARPNESS WITNESS 1 — the certified floor is exactly the distance.** On
the explicit exact-rational input `Cond.diagA = !![3,0;0,5]`:

* the checker accepts `c = 3`, and accepts nothing larger — so `3` is the
  engine's exact output, not a lucky guess;
* hence `dist(diagA, Σ) ≥ 3`;
* and no `c > 3` admits a distance certificate, because an explicit
  perturbation of spectral norm `3` lands in `Σ`.

So `dist(diagA, Σ) = 3` exactly: the tier's bound is **tight, not
conservative**, on this input. The upper bound is a certified witness, so
nothing here uses Eckart–Young (which, per `Conditioning/SWEEP.md` S1, is
already formalized in Lean 4 elsewhere and is claimed by nobody here). -/
theorem cond_margin_sharp :
    Cond.condCheck Cond.diagA 3 = true ∧
      Cond.DistGE (Cond.toReal Cond.diagA) 3 ∧
      (∀ c : ℝ, 3 < c → ¬ Cond.DistGE (Cond.toReal Cond.diagA) c) ∧
      (∀ c : ℚ, Cond.condCheck Cond.diagA c = true → c ≤ 3) := sorry

/-- **SHARPNESS WITNESS 2 — the engine's wall, certified.** On the explicit
exact-rational input `Cond.wallA = !![1,1;0,1]` (a unimodular shear, `det = 1`):

* the first row of its exact rational Gram matrix has diagonal-dominance margin
  **exactly zero** — an equality between exact rationals, so no sharper
  enclosure of the entries can improve it;
* consequently the checker certifies only `c = 0`, which by
  `Cond.distGE_zero_vacuous` is a *vacuous* statement true of every matrix,
  singular ones included;
* and yet the input is genuinely well-posed: a direct Rayleigh argument
  certifies `dist(wallA, Σ) ≥ 1/2 > 0`.

The zero is therefore a property of the **Gershgorin engine**, not of the
input — as distinct from `Cond.singular_dist_zero`, where a reported zero is
the truth. Certifying both cases is what makes a reported floor interpretable;
this is the conditioning analogue of `certified-positivity`'s
`three_grid_last_row_gershgorin_zero`. -/
theorem cond_gershgorin_wall :
    Cond.gramQ Cond.wallA 0 0 - Cond.gershRadiusQ (Cond.gramQ Cond.wallA) 0 = 0 ∧
      (∀ c : ℚ, Cond.condCheck Cond.wallA c = true → c = 0) ∧
      Cond.DistGE (Cond.toReal Cond.wallA) (1 / 2) := sorry

end DiscoveryKernels.Challenge
