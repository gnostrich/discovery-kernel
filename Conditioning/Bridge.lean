/-
Copyright (c) 2026 discovery-kernels contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.

# Bridge: the elementary formulations really are the textbook ones

`Defs.lean` states `SpecNormLe`, `SigmaMinGE` and `DistGE` as elementary
inequalities between finite sums of squares, deliberately avoiding Mathlib's
matrix norm instances. This file discharges the obligation that creates: it
shows those elementary statements imply the genuine ones, stated with

* Mathlib's `EuclideanSpace ℝ (Fin n)` norm, and
* Mathlib's **ℓ² operator norm on matrices**, and
* Mathlib's `Metric.infDist`, and
* Mathlib's `Matrix.IsHermitian.eigenvalues`.

## The scoped-instance footgun, handled explicitly

Mathlib's ℓ² operator norm on `Matrix` is **scoped**: it lives in
`Matrix.Norms.L2Operator` and is *not* the default `Matrix` norm instance.
Without `open scoped Matrix.Norms.L2Operator` one silently gets a different
norm (and hence a different `dist`, and a different `infDist`). This file opens
that scope at the top, and **every theorem in it that mentions `‖·‖`, `dist`,
or `Metric.infDist` on matrices is a statement about the ℓ² operator norm.**
No other file in this tier mentions a matrix norm instance at all.
-/
import Conditioning.Checker

open scoped BigOperators Matrix
open scoped Matrix.Norms.L2Operator

namespace DiscoveryKernels.Cond

variable {n : ℕ}

/-! ### `sqNorm` is the Euclidean norm, squared -/

/-- A plain vector viewed in `EuclideanSpace ℝ (Fin n)`. -/
noncomputable def euc (v : Fin n → ℝ) : EuclideanSpace ℝ (Fin n) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm v

/-- `sqNorm` is exactly the square of Mathlib's Euclidean norm. -/
theorem norm_euc_sq (v : Fin n → ℝ) : ‖euc v‖ ^ 2 = sqNorm v := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp [sqNorm, euc, sq_abs]

/-! ### `SpecNormLe` is the ℓ² operator norm bound -/

/-- **`SpecNormLe` is implied by the genuine ℓ² operator norm bound.** This is
the direction the distance theorem needs: it converts Mathlib's `‖E‖ ≤ b`
(spectral norm) into the elementary hypothesis used throughout the tier. -/
theorem specNormLe_of_l2_opNorm_le {E : Matrix (Fin n) (Fin n) ℝ} {b : ℝ}
    (hb : 0 ≤ b) (h : ‖E‖ ≤ b) : SpecNormLe E b := by
  intro v
  have hk := Matrix.l2_opNorm_mulVec E (euc v)
  have h2 : (EuclideanSpace.equiv (Fin n) ℝ).symm (E *ᵥ (euc v)) = euc (E *ᵥ v) := rfl
  rw [h2] at hk
  have h3 : ‖euc (E *ᵥ v)‖ ≤ b * ‖euc v‖ :=
    hk.trans (mul_le_mul_of_nonneg_right h (norm_nonneg _))
  have h4 : ‖euc (E *ᵥ v)‖ ^ 2 ≤ (b * ‖euc v‖) ^ 2 := by
    nlinarith [norm_nonneg (euc (E *ᵥ v)), h3, norm_nonneg (euc v), hb]
  rw [norm_euc_sq, mul_pow, norm_euc_sq] at h4
  exact h4

/-- Conversely, `SigmaMinGE A c` is exactly `c‖v‖ ≤ ‖Av‖` in Mathlib's
Euclidean norm — so the elementary phrasing is not a weakening. -/
theorem sigmaMinGE_iff_norm {A : Matrix (Fin n) (Fin n) ℝ} {c : ℝ} (hc : 0 ≤ c) :
    SigmaMinGE A c ↔ ∀ v : Fin n → ℝ, c * ‖euc v‖ ≤ ‖euc (A *ᵥ v)‖ := by
  constructor
  · intro h v
    have := h v
    rw [← norm_euc_sq, ← norm_euc_sq] at this
    nlinarith [norm_nonneg (euc v), norm_nonneg (euc (A *ᵥ v)), this]
  · intro h v
    have hv := h v
    have hX : 0 ≤ c * ‖euc v‖ := mul_nonneg hc (norm_nonneg _)
    have hsq := mul_le_mul hv hv hX (norm_nonneg (euc (A *ᵥ v)))
    rw [← norm_euc_sq, ← norm_euc_sq]
    nlinarith [hsq]

/-! ### `DistGE` is a genuine `Metric.infDist` lower bound -/

/-- **The faithfulness theorem for `DistGE`.** The elementary `DistGE A c`
implies the honest metric statement

    c ≤ Metric.infDist A Σ

with `Σ` the set of singular matrices and the distance taken in **Mathlib's
ℓ² operator norm** (scope `Matrix.Norms.L2Operator`, opened at the top of this
file). So every `DistGE` certificate produced by this tier — in particular
every one produced by the executable checker `condCheck` — is a certified lower
bound on a real distance to ill-posedness, not on a bespoke surrogate.

`0 < n` is needed and is not a technicality: for `n = 0` the empty matrix has
`det = 1`, so `Σ = ∅` and `infDist _ ∅ = 0`. -/
theorem le_infDist_sigmaSing_of_distGE {A : Matrix (Fin n) (Fin n) ℝ} {c : ℝ}
    (hn : 0 < n) (h : DistGE A c) : c ≤ Metric.infDist A (SigmaSing n) := by
  have hne : (SigmaSing n).Nonempty := by
    refine ⟨0, ?_⟩
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    simpa [SigmaSing] using Matrix.det_zero this
  refine (Metric.le_infDist hne).mpr ?_
  intro S hS
  by_contra hlt
  push_neg at hlt
  refine h (S - A) (dist A S) dist_nonneg hlt ?_ ?_
  · refine specNormLe_of_l2_opNorm_le dist_nonneg ?_
    rw [dist_eq_norm, ← norm_neg]
    simp
  · simpa using hS

/-- Packaged for the executable checker: a `true` from `condCheck` is a
certified lower bound on the genuine `Metric.infDist` to the singular
matrices, in the ℓ² operator norm. -/
theorem condCheck_le_infDist (A : Matrix (Fin n) (Fin n) ℚ) (c : ℚ) (hn : 0 < n)
    (h : condCheck A c = true) :
    (c : ℝ) ≤ Metric.infDist (toReal A) (SigmaSing n) :=
  le_infDist_sigmaSing_of_distGE hn (condCheck_distGE A c h)

/-! ### `IsEigenvalue` covers Mathlib's Hermitian eigenvalues -/

/-- Every entry of Mathlib's `Matrix.IsHermitian.eigenvalues` really is an
eigenvalue in the sense of `Defs.IsEigenvalue`. -/
theorem isEigenvalue_eigenvalues {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    (j : Fin n) : IsEigenvalue A (hA.eigenvalues j) := by
  refine ⟨(hA.eigenvectorBasis j).ofLp, ?_, hA.mulVec_eigenvectorBasis j⟩
  intro hz
  exact hA.eigenvectorBasis.orthonormal.ne_zero j (by
    apply (WithLp.ofLp_eq_zero (p := 2)).mp hz)

/-- **The charter's target statement, wired to Mathlib's own eigenvalues.**
If the executable exact-rational checker accepts `c` on a symmetric rational
matrix, then every one of Mathlib's `IsHermitian.eigenvalues` of that matrix
satisfies `c ≤ |λ|` — a certified margin to the zero-eigenvalue set, i.e. to
`Σ` for the symmetric eigenvalue problem. -/
theorem condCheck_hermitian_eigenvalue_margin (A : Matrix (Fin n) (Fin n) ℚ) (c : ℚ)
    (h : condCheck A c = true) (hA : (toReal A).IsHermitian) (j : Fin n) :
    (c : ℝ) ≤ |hA.eigenvalues j| :=
  condCheck_abs_eigenvalue A c h (isEigenvalue_eigenvalues hA j)

end DiscoveryKernels.Cond
