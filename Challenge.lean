/-
Copyright (c) 2026 discovery-kernels contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.

# Challenge.lean — the statement registry of `discovery-kernels`

This file IS the set of claims of this repository. Prose (README,
STATEMENTS.md) never claims anything this file does not state.

One theory at three altitudes, in the order the claims lead:
* `COND` — the scalar conditioning theory: certified lower bounds on
  `dist(x, Σ)`, the distance to the ill-posed set, with executable checkers
  proven sound and sharpness witnesses where the bound degenerates.
* `R1` — one instance: PSLQ integer-relation detection, where `Σ` is the set
  of vectors admitting a shorter relation.
* `R3` — the operator lift, `Σ` and the margin taken in an algebra `B`.

Rules of this file:
* Three append-only tier sections, delimited below. No agent edits another
  tier's section. (R0 and R2 were descoped 2026-07-27; see STATEMENTS.md
  changelog.)
* Every headline here is stated with `:= sorry` — permanently. Solutions live
  in the tier directories and are checked against these statements by
  `comparator/` (definitional-equality check + per-theorem axiom allowlist).
  A `sorry` here is a registry marker, never an open problem.
* R3 headlines are under a human-review gate and are stated frontier; see
  STATEMENTS.md for which sorries are targets and which are declared-open.
* Statement changes after FREEZE-0 are recorded in STATEMENTS.md with a dated
  note.
-/
import Conditioning.Sharpness
import Conditioning.Bridge
import PSLQ.Defs
import PSLQ.Core
import OV.Defs

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
norm** (scope `Matrix.Norms.L2Operator`). By the Condition Number Theorem
(Demmel, Numer. Math. 51 (1987) 251–289; Bürgisser–Cucker, *Condition*,
Springer 2013) this is exactly an upper bound on the condition number, and it
is what licenses a finite-precision computation: data accurate to better than
`c` determines the answer.

`0 < n` is load-bearing, not decoration: for `n = 0` the empty matrix has
`det = 1`, so `Σ = ∅` and `Metric.infDist _ ∅ = 0`.

The `open scoped Matrix.Norms.L2Operator` above is confined to this one
declaration deliberately. That instance is NOT Mathlib's default `Matrix`
norm; removing the `open` does not error, it silently states a *different
theorem about a different norm*. Do not hoist or delete it. -/
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
requires operator review before any refinement is merged (see OV/AGENTS.md). -/
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
