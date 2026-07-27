/-
Copyright (c) 2026 discovery-kernels contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.

# Executable exact-rational checkers, proven sound

Two `Bool`-returning decision procedures over **exact rationals** (no `Float`,
no `native_decide` — `decide` over `ℚ` only, exactly as
`certified-positivity`'s `checkPDq` does), each with a soundness theorem of the
shape

    checker A c = true  →  <certified bound on the real matrix A>

**SOUNDNESS ONLY.** Neither checker is complete, and neither is claimed to be:
"says yes ⟹ the bound holds" is the entire contract. A `false` answer means
*this engine could not certify it*, never *the bound is false*. `Sharpness.lean`
exhibits a well-conditioned input on which `condCheck` returns `false` for every
positive `c` — the engine's wall, certified.

* `condCheck A c` — Gershgorin applied to the **exact rational Gram matrix**
  `AᵀA`. Certifies `σ_min(A) ≥ c`, hence `dist(A, Σ) ≥ c` and `c ≤ |λ|` for
  every real eigenvalue. Works for arbitrary square `A`; the Gram matrix is
  always symmetric, so no symmetry hypothesis on `A` is needed.
* `discCheck A c` — Gershgorin's circle theorem applied to `A` directly.
  Cheaper, and it certifies `c ≤ |λ|` for every **real** eigenvalue plus
  nonsingularity. It does **not** certify `dist(A, Σ) ≥ c` for non-normal `A`
  (eigenvalue margin is not a distance to singularity away from normality) —
  see the caveat on `discCheck_abs_eigenvalue`.
-/
import Conditioning.Margin

open scoped BigOperators Matrix

namespace DiscoveryKernels.Cond

variable {n : ℕ}

/-- Exact rational matrix data viewed in `ℝ`. The checkers consume `ℚ`; the
theorems are about `toReal` of that data, so every certified statement is a
statement about a real matrix. -/
def toReal (A : Matrix (Fin n) (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℝ :=
  A.map (Rat.cast : ℚ → ℝ)

/-- Off-diagonal absolute row sum, over `ℚ`, computed exactly. -/
def gershRadiusQ (M : Matrix (Fin n) (Fin n) ℚ) (i : Fin n) : ℚ :=
  ∑ j ∈ Finset.univ.erase i, |M i j|

/-- The Gram matrix `AᵀA`, over `ℚ`, computed exactly. -/
def gramQ (A : Matrix (Fin n) (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ := Aᵀ * A

/-! ### Cast lemmas -/

theorem toReal_gramQ (A : Matrix (Fin n) (Fin n) ℚ) :
    (gramQ A).map (Rat.cast : ℚ → ℝ) = (toReal A)ᵀ * toReal A := by
  ext i j
  simp only [gramQ, toReal, Matrix.map_apply, Matrix.mul_apply, Matrix.transpose_apply]
  push_cast
  rfl

theorem gershRadius_toReal (M : Matrix (Fin n) (Fin n) ℚ) (i : Fin n) :
    gershRadius (M.map (Rat.cast : ℚ → ℝ)) i = ((gershRadiusQ M i : ℚ) : ℝ) := by
  simp only [gershRadius, gershRadiusQ, Matrix.map_apply]
  push_cast
  rfl

theorem transpose_gramQ (A : Matrix (Fin n) (Fin n) ℚ) : (gramQ A)ᵀ = gramQ A := by
  simp [gramQ, Matrix.transpose_mul]

/-! ### The Gram checker -/

/-- **Executable exact-rational conditioning checker.** Returns `true` only if
Gershgorin diagonal dominance of the exact rational Gram matrix `AᵀA`
certifies the singular-value floor `c`.

All arithmetic is over `ℚ`; there is no `Float` and no `native_decide`
anywhere in the definition or in `condCheck_sound`. -/
def condCheck (A : Matrix (Fin n) (Fin n) ℚ) (c : ℚ) : Bool :=
  decide (0 ≤ c ∧ ∀ i : Fin n, c ^ 2 + gershRadiusQ (gramQ A) i ≤ gramQ A i i)

@[simp] theorem condCheck_eq_true (A : Matrix (Fin n) (Fin n) ℚ) (c : ℚ) :
    condCheck A c = true ↔
      0 ≤ c ∧ ∀ i : Fin n, c ^ 2 + gershRadiusQ (gramQ A) i ≤ gramQ A i i := by
  simp [condCheck]

/-- **`condCheck_sound` — the `checkPDq_sound` shape for conditioning.**
If the executable exact-rational checker says `true`, then the real matrix
`toReal A` has smallest singular value at least `c`.

Soundness only: no completeness claim is made or intended. -/
theorem condCheck_sound (A : Matrix (Fin n) (Fin n) ℚ) (c : ℚ)
    (h : condCheck A c = true) : SigmaMinGE (toReal A) (c : ℝ) := by
  rw [condCheck_eq_true] at h
  obtain ⟨_, hrows⟩ := h
  refine sigmaMinGE_of_gram_floor ?_
  rw [← toReal_gramQ]
  refine gershgorin_rayleigh_floor _ ?_ _ ?_
  · rw [← Matrix.transpose_map, transpose_gramQ]
  · intro i
    rw [gershRadius_toReal]
    have := hrows i
    have : (((c ^ 2 + gershRadiusQ (gramQ A) i : ℚ)) : ℝ) ≤ ((gramQ A i i : ℚ) : ℝ) :=
      Rat.cast_le.mpr this
    push_cast at this ⊢
    simpa [Matrix.map_apply] using this

/-- **The headline shape: a certified distance to ill-posedness from an
executable exact-rational check.** `condCheck A c = true` certifies
`dist(toReal A, Σ) ≥ c` in the spectral norm, where `Σ` is the set of singular
matrices — i.e. no perturbation of spectral norm `< c` can make `A` singular. -/
theorem condCheck_distGE (A : Matrix (Fin n) (Fin n) ℚ) (c : ℚ)
    (h : condCheck A c = true) : DistGE (toReal A) (c : ℝ) :=
  distGE_of_sigmaMinGE (condCheck_sound A c h)

/-- **The charter's target shape**: `condCheck M c = true` certifies that every
real eigenvalue `λ` of the real matrix `toReal M` satisfies `c ≤ |λ|` — a
certified margin to the zero-eigenvalue set. -/
theorem condCheck_abs_eigenvalue (A : Matrix (Fin n) (Fin n) ℚ) (c : ℚ)
    (h : condCheck A c = true) {l : ℝ} (hl : IsEigenvalue (toReal A) l) : (c : ℝ) ≤ |l| := by
  have hc : (0 : ℝ) ≤ (c : ℝ) := by
    rw [condCheck_eq_true] at h; exact_mod_cast h.1
  exact abs_eigenvalue_ge_of_sigmaMinGE hc (condCheck_sound A c h) hl

/-- A positive certificate proves well-posedness outright. -/
theorem condCheck_det_ne_zero (A : Matrix (Fin n) (Fin n) ℚ) (c : ℚ) (hc : 0 < c)
    (h : condCheck A c = true) : (toReal A).det ≠ 0 :=
  det_ne_zero_of_sigmaMinGE (by exact_mod_cast hc) (condCheck_sound A c h)

/-- A positive certificate caps the amplification of `A⁻¹`, hence the condition
number: `κ₂(A) ≤ ‖A‖ / c`. -/
theorem condCheck_inv_bound (A : Matrix (Fin n) (Fin n) ℚ) (c : ℚ) (hc : 0 < c)
    (h : condCheck A c = true) : SpecNormLe (toReal A)⁻¹ (1 / (c : ℝ)) :=
  specNormLe_inv_of_sigmaMinGE (by exact_mod_cast hc) (condCheck_sound A c h)

/-- **THE PAYOFF, executable form.** A `true` from the exact-rational checker
converts right-hand-side accuracy into solution accuracy: solving `A x = b`
with the right-hand side known only to within `ε` still determines `x` to
within `ε / c`. -/
theorem condCheck_licenses_solve (A : Matrix (Fin n) (Fin n) ℚ) (c : ℚ)
    (h : condCheck A c = true) (x y b b' : Fin n → ℝ)
    (hx : toReal A *ᵥ x = b) (hy : toReal A *ᵥ y = b') (ε : ℝ)
    (hε : sqNorm (b - b') ≤ ε ^ 2) :
    (c : ℝ) ^ 2 * sqNorm (x - y) ≤ ε ^ 2 :=
  solve_error_bound (condCheck_sound A c h) x y b b' hx hy ε hε

/-! ### The direct (circle-theorem) checker -/

/-- **Second engine**: Gershgorin's circle theorem applied to `A` itself, in
absolute-value form. Cheaper than `condCheck` (no Gram matrix), and it does not
require `A` to be symmetric.

Honest scope: this certifies a margin on the **real** eigenvalues of `A` and
nonsingularity. For a non-normal matrix an eigenvalue margin is *not* a
distance to singularity, so `discCheck` is deliberately **not** wired to
`DistGE`. Use `condCheck` for distance claims. -/
def discCheck (A : Matrix (Fin n) (Fin n) ℚ) (c : ℚ) : Bool :=
  decide (0 ≤ c ∧ ∀ i : Fin n, c + gershRadiusQ A i ≤ |A i i|)

@[simp] theorem discCheck_eq_true (A : Matrix (Fin n) (Fin n) ℚ) (c : ℚ) :
    discCheck A c = true ↔ 0 ≤ c ∧ ∀ i : Fin n, c + gershRadiusQ A i ≤ |A i i| := by
  simp [discCheck]

/-- Soundness of `discCheck` for real eigenvalues. Soundness only. -/
theorem discCheck_abs_eigenvalue (A : Matrix (Fin n) (Fin n) ℚ) (c : ℚ)
    (h : discCheck A c = true) {l : ℝ} (hl : IsEigenvalue (toReal A) l) : (c : ℝ) ≤ |l| := by
  rw [discCheck_eq_true] at h
  obtain ⟨_, hrows⟩ := h
  obtain ⟨i, hi⟩ := gershgorin_disc (toReal A) l hl
  have hrow : ((c : ℝ)) + gershRadius (toReal A) i ≤ |toReal A i i| := by
    rw [toReal, gershRadius_toReal]
    have := Rat.cast_le (K := ℝ) |>.mpr (hrows i)
    push_cast at this ⊢
    simpa [Matrix.map_apply] using this
  have h2 : |toReal A i i| - |l| ≤ |l - toReal A i i| := by
    have := abs_sub_abs_le_abs_sub (toReal A i i) l
    calc |toReal A i i| - |l| ≤ |toReal A i i - l| := this
      _ = |l - toReal A i i| := abs_sub_comm _ _
  linarith

/-- Strict diagonal dominance certifies nonsingularity (Levy–Desplanques),
derived from the circle theorem proved in `Gershgorin.lean`. -/
theorem det_ne_zero_of_strict_diag_dominance (M : Matrix (Fin n) (Fin n) ℝ)
    (h : ∀ i, gershRadius M i < |M i i|) : M.det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hvz⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  obtain ⟨i, hi⟩ := gershgorin_disc M 0 ⟨v, hv, by simpa using hvz⟩
  rw [zero_sub, abs_neg] at hi
  exact absurd hi (not_le.mpr (h i))

end DiscoveryKernels.Cond
