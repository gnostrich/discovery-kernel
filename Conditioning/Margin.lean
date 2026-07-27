/-
Copyright (c) 2026 discovery-kernels contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.

# From a singular-value floor to a certified distance to ill-posedness

This file contains the tier's mathematical spine. Everything here is
**elementary and unconditional**: no Eckart–Young, no SVD, no perturbation
theory is used or needed.

The chain is

    Rayleigh floor on `AᵀA`   (Gershgorin, exact ℚ input)
      ⟹ `SigmaMinGE A c`      (`σ_min(A) ≥ c`)
      ⟹ `DistGE A c`          (`dist(A, Σ) ≥ c`, Σ = singular matrices)
      ⟹ certified forward-error bound for `A x = b`

Only the **lower** bound `dist(A, Σ) ≥ σ_min(A)` is used, and that is the easy
direction — a two-line contradiction argument. The reverse inequality
`dist(A, Σ) ≤ σ_min(A)` is Eckart–Young; we neither prove nor assume it. Where
we need it (to show a certified floor is *exactly* the distance) we supply an
explicit singular perturbation instead — see `Sharpness.lean`. That is a
strictly stronger, fully certified substitute for a general appeal to
Eckart–Young, and it is the honest thing to do given `SWEEP.md` S1 (which
records that Eckart–Young–Mirsky *is* already formalized in Lean 4 in
`YuanheZ/lean-stat-learning-theory`, so this tier claims no novelty for it).
-/
import Conditioning.Gershgorin

open scoped BigOperators Matrix

namespace DiscoveryKernels.Cond

variable {n : ℕ}

/-! ### The Gram transport: any symmetric Rayleigh engine becomes a σ_min engine -/

/-- A Rayleigh floor `c²` on the Gram matrix `AᵀA` is exactly a singular-value
floor `c` on `A`. This is what lets the (symmetric-only) Gershgorin engine
certify an **arbitrary** square matrix. -/
theorem sigmaMinGE_of_gram_floor {A : Matrix (Fin n) (Fin n) ℝ} {c : ℝ}
    (h : ∀ v : Fin n → ℝ, c ^ 2 * sqNorm v ≤ quadForm (Aᵀ * A) v) : SigmaMinGE A c := by
  intro v
  rw [← quadForm_gram]
  exact h v

/-! ### σ_min floor ⟹ nonsingularity, eigenvalue margin, and distance to Σ -/

/-- A positive singular-value floor certifies nonsingularity: the input is
**well-posed**, i.e. `A ∉ Σ`. -/
theorem det_ne_zero_of_sigmaMinGE {A : Matrix (Fin n) (Fin n) ℝ} {c : ℝ}
    (hc : 0 < c) (h : SigmaMinGE A c) : A.det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hvz⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have h1 := h v
  rw [hvz] at h1
  have h2 : sqNorm (0 : Fin n → ℝ) = 0 := by simp [sqNorm]
  rw [h2] at h1
  have h3 := sqNorm_pos hv
  have h4 : 0 < c ^ 2 * sqNorm v := mul_pos (by positivity) h3
  linarith

/-- `A ∉ Σ` in the `Set` phrasing. -/
theorem not_mem_sigmaSing_of_sigmaMinGE {A : Matrix (Fin n) (Fin n) ℝ} {c : ℝ}
    (hc : 0 < c) (h : SigmaMinGE A c) : A ∉ SigmaSing n :=
  det_ne_zero_of_sigmaMinGE hc h

/-- **Eigenvalue margin.** A singular-value floor `c` bounds every real
eigenvalue away from zero: `c ≤ |λ|`. Combined with `Gershgorin`, this is the
certified *distance to the zero-eigenvalue set* in the sense asked for by the
tier charter. Works for arbitrary square real matrices, not just symmetric
ones. -/
theorem abs_eigenvalue_ge_of_sigmaMinGE {A : Matrix (Fin n) (Fin n) ℝ} {c : ℝ}
    (hc : 0 ≤ c) (h : SigmaMinGE A c) {l : ℝ} (hl : IsEigenvalue A l) : c ≤ |l| := by
  obtain ⟨v, hv, hAv⟩ := hl
  have h1 := h v
  rw [hAv, sqNorm_smul] at h1
  have h2 := sqNorm_pos hv
  have hle : c ^ 2 ≤ l ^ 2 := le_of_mul_le_mul_right h1 h2
  nlinarith [hle, sq_abs l, abs_nonneg l]

/-- **The distance theorem** (lower bound direction of the Condition Number
Theorem for `Σ = ` singular matrices).

`σ_min(A) ≥ c` implies `dist(A, Σ) ≥ c`: no perturbation of spectral norm
strictly below `c` can make `A` singular. This is the statement that licenses
a finite-precision computation — data known to accuracy better than `c`
determines invertibility. -/
theorem distGE_of_sigmaMinGE {A : Matrix (Fin n) (Fin n) ℝ} {c : ℝ}
    (h : SigmaMinGE A c) : DistGE A c := by
  intro E b hb hbc hE hmem
  have hdet : (A + E).det = 0 := hmem
  obtain ⟨v, hv, hvz⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  rw [Matrix.add_mulVec] at hvz
  have hAv : A *ᵥ v = -(E *ᵥ v) := by
    have := eq_neg_of_add_eq_zero_left hvz
    simpa using this
  have h1 := h v
  rw [hAv, sqNorm_neg] at h1
  have h2 := hE v
  have h3 := sqNorm_pos hv
  have h5 : c ^ 2 ≤ b ^ 2 := le_of_mul_le_mul_right (le_trans h1 h2) h3
  have hcb : 0 < (c - b) * (c + b) := mul_pos (sub_pos.mpr hbc) (by linarith)
  nlinarith [h5, hcb]

/-- Packaged: a Gram Rayleigh floor certifies a distance to ill-posedness. -/
theorem distGE_of_gram_floor {A : Matrix (Fin n) (Fin n) ℝ} {c : ℝ}
    (h : ∀ v : Fin n → ℝ, c ^ 2 * sqNorm v ≤ quadForm (Aᵀ * A) v) : DistGE A c :=
  distGE_of_sigmaMinGE (sigmaMinGE_of_gram_floor h)

/-- Contrapositive tool for **sharpness**: an explicit singular perturbation of
spectral norm at most `b` caps the distance at `b`. Together with
`DistGE A b` this pins `dist(A, Σ) = b` exactly, with no appeal to
Eckart–Young. -/
theorem not_distGE_of_singular_perturbation {A E : Matrix (Fin n) (Fin n) ℝ} {b c : ℝ}
    (hb : 0 ≤ b) (hbc : b < c) (hE : SpecNormLe E b) (hsing : (A + E).det = 0) :
    ¬ DistGE A c :=
  fun h => h E b hb hbc hE hsing

/-! ### What the margin buys: certified error amplification -/

/-- **The condition-number bound.** A floor `c` on `σ_min(A)` caps the
amplification of the inverse: `‖A⁻¹ w‖ ≤ (1/c)‖w‖` for every `w`. Since
`κ₂(A) = ‖A‖ ‖A⁻¹‖`, any upper bound `‖A‖ ≤ N` combines with this to give the
explicit certified condition number bound `κ₂(A) ≤ N / c` — the
`κ(x) = ‖x‖ / dist(x, Σ)` identity in its usable, one-sided form. -/
theorem specNormLe_inv_of_sigmaMinGE {A : Matrix (Fin n) (Fin n) ℝ} {c : ℝ}
    (hc : 0 < c) (h : SigmaMinGE A c) : SpecNormLe A⁻¹ (1 / c) := by
  intro w
  have hunit : IsUnit A.det := Ne.isUnit (det_ne_zero_of_sigmaMinGE hc h)
  have hAA : A *ᵥ (A⁻¹ *ᵥ w) = w := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hunit, Matrix.one_mulVec]
  have h1 := h (A⁻¹ *ᵥ w)
  rw [hAA] at h1
  have hc2 : 0 < c ^ 2 := by positivity
  rw [div_pow, one_pow, one_div, inv_mul_eq_div, le_div_iff₀ hc2]
  linarith [h1]

/-- **THE TIER'S POINT — a certified margin licenses a finite-precision
computation.** If `A x = b` exactly and `A y = b'` where the right-hand sides
agree to within `ε` in the Euclidean norm, then the solutions agree to within
`ε / c`, stated squared so that no square roots appear:
`c² ‖x - y‖² ≤ ε²`.

This is the linear-algebra analogue of `R1.pslq_empirical_sound`: the certified
distance to ill-posedness converts input accuracy into output accuracy. -/
theorem solve_error_bound {A : Matrix (Fin n) (Fin n) ℝ} {c : ℝ}
    (h : SigmaMinGE A c) (x y b b' : Fin n → ℝ)
    (hx : A *ᵥ x = b) (hy : A *ᵥ y = b') (ε : ℝ) (hε : sqNorm (b - b') ≤ ε ^ 2) :
    c ^ 2 * sqNorm (x - y) ≤ ε ^ 2 := by
  have hmv : A *ᵥ (x - y) = b - b' := by
    rw [Matrix.mulVec_sub, hx, hy]
  have h1 := h (x - y)
  rw [hmv] at h1
  linarith

end DiscoveryKernels.Cond
