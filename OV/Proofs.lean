/-
Copyright (c) 2026 discovery-kernels contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.

# OV — PROOFS of the R3/OV TARGET headlines.

The statements are frozen in `Challenge.lean` (operator sign-off, 2026-07-28);
the constants below have types DEFINITIONALLY EQUAL to them and are the
solutions registered in `comparator/headlines.toml` (rows proposed in
`OV/COMPARATOR-ROWS.md`).

Contents (see `OV/TIER-STATUS.md` for the current ledger):

* `ov_dist_not_element_valued` — PROVED. The tier's decisive negative: an
  explicit `2 × 2` matrix over `B = M₂(ℝ)` (Loewner order) with NO greatest
  certified margin, i.e. no `B`-valued distance to the ill-posed set. This is
  Kadison's anti-lattice phenomenon (Proc. AMS 2 (1951) 505–510) in exact
  rational arithmetic, fed into the already-proved reduction
  `bvaluedDistance_fails_of_no_infimum` (`OV/Cond.lean`).
* `ov_condition_number_theorem` — PROVED. Both directions of the `B`-valued
  Condition Number Theorem. The `⇐` direction is the Eckart–Young rank-one
  construction `y = x - (xξ)ξ*` (Eckart–Young 1936; Demmel, Numer. Math. 51
  (1987) 251–289).
* `ov_lojasiewicz_order` — PROVED. The symbolic (FALLBACK) form: below the
  Łojasiewicz order every coefficient of the direction datum vanishes, and the
  order-`k` leading certificate is strictly positive in `B`.

Witness arithmetic for the first (all exact, all rational):

  `d₁ = !![2,0; 0,1]`, `d₂ = !![2,1; 0,2]`, so
  `a₁ = d₁* d₁ = !![4,0; 0,1]` and `a₂ = d₂* d₂ = !![4,2; 2,5]`.
  Both `1` and `c = !![31/10,0; 0,0]` are positive common lower bounds of
  `a₁, a₂`. A greatest common lower bound `m` would satisfy `1 ≤ m ≤ a₁`,
  forcing `m₂₂ = 1` and then (zero diagonal entry of the positive `a₁ - m`)
  `m₁₂ = 0`; `m ≤ a₂` then forces `m₁₁ ≤ 3`, contradicting `c ≤ m`
  (`m₁₁ ≥ 31/10`). The `M₂(ℝ)` pair used here is a rescaling of the pair
  recorded in `OV/CHALLENGE-R3.proposed.md` §3b.3, chosen so that `a₁, a₂`
  have RATIONAL square roots `d₁, d₂` — the reduction consumes `star d * d`,
  not `a`, and rational factors keep the whole witness in exact arithmetic.
-/
import Mathlib
import OV.Cond
import OV.Symbolic

namespace DiscoveryKernels.R3

open Matrix Polynomial

/-! ## §1 A 2×2 real Loewner toolkit -/

section Loewner

open scoped MatrixOrder

/-- Positive semidefiniteness of a real symmetric `2 × 2` matrix from the
classical minors: `a ≥ 0`, `c ≥ 0`, `b² ≤ ac`. Proved from the quadratic form
directly (the SOS identity `a·Q = (a x₀ + b x₁)² + (ac - b²) x₁²`), so no
eigenvalue machinery is used. -/
lemma psd_two {a b c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hb : b ^ 2 ≤ a * c) :
    (!![a, b; b, c] : Matrix (Fin 2) (Fin 2) ℝ).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun v => ?_
  · ext i j
    fin_cases i <;> fin_cases j <;> simp
  · have hexp : star v ⬝ᵥ (!![a, b; b, c] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ v
        = a * v 0 * v 0 + 2 * b * (v 0 * v 1) + c * (v 1 * v 1) := by
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two]
      ring
    rw [hexp]
    rcases eq_or_lt_of_le ha with rfl | ha'
    · have hb0 : b = 0 := by nlinarith [sq_nonneg b]
      subst hb0
      nlinarith [sq_nonneg (v 1)]
    · nlinarith [sq_nonneg (a * v 0 + b * v 1), mul_nonneg (sub_nonneg.mpr hb) (sq_nonneg (v 1)),
        sq_nonneg (v 0), sq_nonneg (v 1)]

/-- The quadratic form read off the Loewner order: `A ≤ B` gives
`0 ≤ vᵀ (B - A) v` entrywise-expanded for `n = 2`. -/
lemma quad_of_le {A B : Matrix (Fin 2) (Fin 2) ℝ} (h : A ≤ B) (v : Fin 2 → ℝ) :
    0 ≤ v 0 * ((B 0 0 - A 0 0) * v 0 + (B 0 1 - A 0 1) * v 1)
      + v 1 * ((B 1 0 - A 1 0) * v 0 + (B 1 1 - A 1 1) * v 1) := by
  have := (Matrix.le_iff.mp h).dotProduct_mulVec_nonneg v
  simpa [dotProduct, Matrix.mulVec, Fin.sum_univ_two, Matrix.sub_apply] using this

/-- Symmetry of the difference, from `PosSemidef.isHermitian`. -/
lemma herm_of_le {A B : Matrix (Fin 2) (Fin 2) ℝ} (h : A ≤ B) :
    B 1 0 - A 1 0 = B 0 1 - A 0 1 := by
  have := (Matrix.le_iff.mp h).isHermitian.apply 0 1
  simpa [Matrix.sub_apply] using this

end Loewner

/-! ## §2 The Kadison anti-lattice witness in `M₂(ℝ)` -/

section Kadison

open scoped MatrixOrder

/-- First factor: `d₁* d₁ = diag(4, 1)`. -/
def kd₁ : Matrix (Fin 2) (Fin 2) ℝ := !![2, 0; 0, 1]

/-- Second factor: `d₂* d₂ = !![4,2; 2,5]`. -/
def kd₂ : Matrix (Fin 2) (Fin 2) ℝ := !![2, 1; 0, 2]

lemma kd₁_sq : star kd₁ * kd₁ = !![4, 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kd₁, Matrix.star_eq_conjTranspose, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

lemma kd₂_sq : star kd₂ * kd₂ = !![4, 2; 2, 5] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kd₂, Matrix.star_eq_conjTranspose, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

/-- The second common lower bound, `diag(31/10, 0)` — incomparable with `1`. -/
noncomputable def kdC : Matrix (Fin 2) (Fin 2) ℝ := !![31/10, 0; 0, 0]

/-- **The anti-lattice instance, machine-checked.** The positive elements
`star kd₁ * kd₁` and `star kd₂ * kd₂` of `M₂(ℝ)` have NO greatest common lower
bound inside the positive cone. -/
theorem kadison_no_inf :
    ¬ ∃ b : Matrix (Fin 2) (Fin 2) ℝ,
      IsGreatest {c : Matrix (Fin 2) (Fin 2) ℝ |
        0 ≤ c ∧ c ≤ star kd₁ * kd₁ ∧ c ≤ star kd₂ * kd₂} b := by
  rw [kd₁_sq, kd₂_sq]
  rintro ⟨m, ⟨hm0, hm1, hm2⟩, hub⟩
  -- `1` is a positive common lower bound
  have hone : (1 : Matrix (Fin 2) (Fin 2) ℝ) ∈
      {c : Matrix (Fin 2) (Fin 2) ℝ | 0 ≤ c ∧ c ≤ !![4, 0; 0, 1] ∧ c ≤ !![(4:ℝ), 2; 2, 5]} := by
    refine ⟨?_, ?_, ?_⟩
    · rw [Matrix.nonneg_iff_posSemidef]
      have h1 : (1 : Matrix (Fin 2) (Fin 2) ℝ) = !![1, 0; 0, 1] := by
        ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply]
      rw [h1]; exact psd_two (by norm_num) (by norm_num) (by norm_num)
    · rw [Matrix.le_iff]
      have h1 : (!![(4:ℝ), 0; 0, 1] - 1) = !![3, 0; 0, 0] := by
        ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply] <;> norm_num
      rw [h1]; exact psd_two (by norm_num) (by norm_num) (by norm_num)
    · rw [Matrix.le_iff]
      have h1 : (!![(4:ℝ), 2; 2, 5] - 1) = !![3, 2; 2, 4] := by
        ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply] <;> norm_num
      rw [h1]; exact psd_two (by norm_num) (by norm_num) (by norm_num)
  -- `diag(31/10, 0)` is another positive common lower bound
  have hc : kdC ∈
      {c : Matrix (Fin 2) (Fin 2) ℝ | 0 ≤ c ∧ c ≤ !![4, 0; 0, 1] ∧ c ≤ !![(4:ℝ), 2; 2, 5]} := by
    refine ⟨?_, ?_, ?_⟩
    · rw [Matrix.nonneg_iff_posSemidef, kdC]
      exact psd_two (by norm_num) (by norm_num) (by norm_num)
    · rw [Matrix.le_iff]
      have h1 : (!![(4:ℝ), 0; 0, 1] - kdC) = !![9/10, 0; 0, 1] := by
        ext i j; fin_cases i <;> fin_cases j <;> simp [kdC] <;> norm_num
      rw [h1]; exact psd_two (by norm_num) (by norm_num) (by norm_num)
    · rw [Matrix.le_iff]
      have h1 : (!![(4:ℝ), 2; 2, 5] - kdC) = !![9/10, 2; 2, 5] := by
        ext i j; fin_cases i <;> fin_cases j <;> simp [kdC] <;> norm_num
      rw [h1]; exact psd_two (by norm_num) (by norm_num) (by norm_num)
  have h1m : (1 : Matrix (Fin 2) (Fin 2) ℝ) ≤ m := hub hone
  have hcm : kdC ≤ m := hub hc
  -- `1 ≤ m ≤ diag(4,1)` pins the second diagonal entry
  have e1 : (1:ℝ) ≤ m 1 1 := by
    have := quad_of_le h1m ![0, 1]
    simpa [Matrix.one_apply] using this
  have e2 : m 1 1 ≤ 1 := by
    have := quad_of_le hm1 ![0, 1]
    simp at this
    linarith
  have hm11 : m 1 1 = 1 := le_antisymm e2 e1
  -- `kdC ≤ m` bounds the first diagonal entry from below
  have e3 : (31/10 : ℝ) ≤ m 0 0 := by
    have := quad_of_le hcm ![1, 0]
    simp [kdC] at this
    linarith
  have hP00 : m 0 0 ≤ 4 := by
    have := quad_of_le hm1 ![1, 0]
    simp at this
    linarith
  -- a positive matrix with a zero diagonal entry has zero off-diagonal entries
  have hoff : m 0 1 = 0 := by
    have hsym := herm_of_le hm1
    simp at hsym
    have key : ∀ s : ℝ, 0 ≤ (4 - m 0 0) * s * s + 2 * (0 - m 0 1) * s := by
      intro s
      have := quad_of_le hm1 ![s, 1]
      simp [hm11] at this
      rw [hsym] at this
      nlinarith [this]
    have := key (m 0 1)
    nlinarith [sq_nonneg (m 0 1), e3, hP00]
  -- and then `m ≤ a₂` caps the first diagonal entry at `3 < 31/10`
  have hfin : m 0 0 ≤ 3 := by
    have := quad_of_le hm2 ![1, -(1/2)]
    have hsym := herm_of_le hm2
    simp [hm11, hoff] at this hsym
    nlinarith [this, hsym]
  linarith

open scoped MatrixOrder in
/-- **TARGET 1 — PROVED.** `Challenge.ov_dist_not_element_valued`: over
`B = M₂(ℝ)` with the Loewner order there is a `2 × 2` matrix over `B`
admitting NO greatest certified margin. `dist_B(·, Σ)` is a certificate SET,
never a `B`-valued number. -/
theorem ov_dist_not_element_valued :
    ∃ x : Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) ℝ),
      ∀ b : Matrix (Fin 2) (Fin 2) ℝ,
        ¬ R3.IsBValuedDistance (Matrix (Fin 2) (Fin 2) ℝ) x b :=
  bvaluedDistance_fails_of_no_infimum ⟨kd₁, kd₂, kadison_no_inf⟩

end Kadison

/-! ## §3 The `B`-valued Condition Number Theorem -/

/-- **TARGET 2 — PROVED.** `Challenge.ov_condition_number_theorem`: the
algebraic and geometric readings of "`b` is a certified `B`-valued margin for
`x`" coincide.

`⇒` is `margin_imp_distanceCertificate` specialised to unit vectors. `⇐` is
Eckart–Young: given a unit `ξ`, the rank-one perturbation
`r = (xξ) ξ*` satisfies `r ξ = xξ` (because `⟨ξ,ξ⟩ = 1`), so `y = x - r`
kills `ξ` and is therefore ill-posed unless `B` is trivial — and applying the
geometric hypothesis at that `y` returns exactly the algebraic bound. The
degenerate branch is genuine and handled: if `y` happens to be invertible then
`ξ = 0`, so `1 = ⟨ξ,ξ⟩ = 0` and `B` is a subsingleton. -/
theorem ov_condition_number_theorem
    {B : Type} [Ring B] [StarRing B] [PartialOrder B] [StarOrderedRing B]
    {n : ℕ} (x : Matrix (Fin n) (Fin n) B) (b : B) (hb : 0 ≤ b) :
    (∀ ξ : Fin n → B, R3.ovInner B ξ ξ = 1 →
        R3.ovRayleigh B b ξ ≤ R3.ovInner B (x *ᵥ ξ) (x *ᵥ ξ)) ↔
      (∀ y : Matrix (Fin n) (Fin n) B, R3.IsIllPosed B y → ∀ ξ : Fin n → B,
        R3.ovInner B ξ ξ = 1 → y *ᵥ ξ = 0 →
          R3.ovRayleigh B b ξ ≤ R3.ovInner B ((x - y) *ᵥ ξ) ((x - y) *ᵥ ξ)) := by
  constructor
  · intro h y _ ξ hξ hy
    have hxy : (x - y) *ᵥ ξ = x *ᵥ ξ := by rw [Matrix.sub_mulVec, hy, sub_zero]
    rw [hxy]
    exact h ξ hξ
  · intro h ξ hξ
    -- the Eckart–Young rank-one perturbation `r = (xξ) ξ*`
    set r : Matrix (Fin n) (Fin n) B := Matrix.vecMulVec (x *ᵥ ξ) (fun j => star (ξ j)) with hrdef
    have hrξ : r *ᵥ ξ = x *ᵥ ξ := by
      funext i
      have hri : (r *ᵥ ξ) i = (x *ᵥ ξ) i * ovInner B ξ ξ := by
        simp only [hrdef, Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, ovInner,
          Finset.mul_sum, mul_assoc]
      rw [hri, hξ, mul_one]
    set y : Matrix (Fin n) (Fin n) B := x - r with hydef
    have hyξ : y *ᵥ ξ = 0 := by rw [hydef, Matrix.sub_mulVec, hrξ, sub_self]
    have hxy : x - y = r := by rw [hydef]; abel
    by_cases hu : IsUnit y
    · -- degenerate branch: `y` invertible forces `ξ = 0`, hence `1 = 0` in `B`
      obtain ⟨u, hu⟩ := hu
      have hξ0 : ξ = 0 := by
        have hinv : (↑u⁻¹ : Matrix (Fin n) (Fin n) B) *ᵥ (y *ᵥ ξ) = ξ := by
          rw [Matrix.mulVec_mulVec, ← hu, u.inv_mul, Matrix.one_mulVec]
        rw [hyξ, Matrix.mulVec_zero] at hinv
        exact hinv.symm
      have h10 : (0 : B) = 1 := by rw [← hξ, hξ0]; simp [ovInner]
      haveI : Subsingleton B := subsingleton_of_zero_eq_one h10
      exact le_of_eq (Subsingleton.elim _ _)
    · have hgeo := h y hu ξ hξ hyξ
      rwa [hxy, hrξ] at hgeo

/-! ## §4 The scalar base case: `B = ℝ` recovers `λ_min(xᵀx)`

Courant–Fischer is absent from Mathlib (Conditioning/SWEEP.md S1). The
min-characterisation actually needed here is obtained directly instead, from
the spectral theorem: `A - t·1` is unitarily conjugate to
`diagonal (λ - t)`, and `Matrix.posSemidef_diagonal_iff` finishes. -/

section Scalar

open Unitary

/-- The quadratic form of `xᴴx - t·1` IS the margin defect. -/
lemma quad_id {n : ℕ} (x : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) (ξ : Fin n → ℝ) :
    star ξ ⬝ᵥ ((xᴴ * x - t • (1 : Matrix (Fin n) (Fin n) ℝ)) *ᵥ ξ)
      = ovInner ℝ (x *ᵥ ξ) (x *ᵥ ξ) - ovRayleigh ℝ t ξ := by
  have h1 : star ξ ⬝ᵥ ((xᴴ * x) *ᵥ ξ) = ovInner ℝ (x *ᵥ ξ) (x *ᵥ ξ) := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
    rfl
  have h2 : star ξ ⬝ᵥ ((t • (1 : Matrix (Fin n) (Fin n) ℝ)) *ᵥ ξ) = ovRayleigh ℝ t ξ := by
    simp [ovRayleigh, dotProduct, Matrix.mulVec, Matrix.smul_apply, Matrix.one_apply]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [Matrix.sub_mulVec, dotProduct_sub, h1, h2]

lemma isHermitian_smul_one {n : ℕ} (t : ℝ) :
    (t • (1 : Matrix (Fin n) (Fin n) ℝ)).IsHermitian := by
  simp [Matrix.IsHermitian]

/-- **The shifted spectral decomposition.** `A - t·1` is unitarily conjugate to
`diagonal (eigenvalues - t)` — this is the substitute for Courant–Fischer. -/
lemma shifted_spectral {N : Type*} [Fintype N] [DecidableEq N]
    {A : Matrix N N ℝ} (hA : A.IsHermitian) (t : ℝ) :
    A - t • (1 : Matrix N N ℝ)
      = (hA.eigenvectorUnitary : Matrix N N ℝ)
          * Matrix.diagonal (fun i => hA.eigenvalues i - t)
          * star (hA.eigenvectorUnitary : Matrix N N ℝ) := by
  have hUU : (hA.eigenvectorUnitary : Matrix N N ℝ)
      * star (hA.eigenvectorUnitary : Matrix N N ℝ) = 1 :=
    Unitary.coe_mul_star_self _
  have hdiag : (Matrix.diagonal (fun i => hA.eigenvalues i - t) : Matrix N N ℝ)
      = Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) - t • (1 : Matrix N N ℝ) := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.diagonal, Matrix.one_apply, h]
  rw [hdiag, Matrix.mul_sub, Matrix.sub_mul]
  congr 1
  · conv_lhs => rw [hA.spectral_theorem]
    simp [Unitary.conjStarAlgAut_apply]
  · rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hUU]

/-- `t` is below the whole spectrum of a Hermitian `A` iff `A - t·1 ⪰ 0`. -/
lemma posSemidef_shift_iff {N : Type*} [Fintype N] [DecidableEq N]
    {A : Matrix N N ℝ} (hA : A.IsHermitian) (t : ℝ) :
    (A - t • (1 : Matrix N N ℝ)).PosSemidef ↔ ∀ i, t ≤ hA.eigenvalues i := by
  rw [shifted_spectral hA t, Unitary.isUnit_coe.posSemidef_star_right_conjugate_iff,
    Matrix.posSemidef_diagonal_iff]
  simp [sub_nonneg]

/-- **TARGET 4 — PROVED.** `Challenge.ov_cnt_recovers_scalar`: at `B = ℝ` the
`B`-valued margin set is exactly `{t : 0 ≤ t ∧ t ≤ λ_min(xᵀx)}` — the
classical Demmel/Eckart–Young answer, no more and no less. -/
theorem ov_cnt_recovers_scalar
    {n : ℕ} (x : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    R3.IsMargin ℝ x t ↔
      0 ≤ t ∧ ∀ i, t ≤ (Matrix.isHermitian_conjTranspose_mul_self x).eigenvalues i := by
  constructor
  · rintro ⟨ht, h⟩
    refine ⟨ht, ?_⟩
    rw [← posSemidef_shift_iff (Matrix.isHermitian_conjTranspose_mul_self x) t]
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      ((Matrix.isHermitian_conjTranspose_mul_self x).sub (isHermitian_smul_one t)) fun ξ => ?_
    rw [quad_id]
    exact sub_nonneg.mpr (h ξ)
  · rintro ⟨ht, h⟩
    refine ⟨ht, fun ξ => ?_⟩
    have hpsd := (posSemidef_shift_iff (Matrix.isHermitian_conjTranspose_mul_self x) t).mpr h
    have hq := hpsd.dotProduct_mulVec_nonneg ξ
    rw [quad_id] at hq
    exact sub_nonneg.mp hq

end Scalar

/-! ## §5 The symbolic (FALLBACK) Łojasiewicz order form -/

/-- **TARGET 3 — PROVED.** `Challenge.ov_lojasiewicz_order`: at a direction of
Łojasiewicz order `k`, every lower-order coefficient of the direction datum
vanishes and the order-`k` leading certificate `∑ᵢ (cᵢ)* cᵢ` is STRICTLY
positive in `B`.

Both halves are bookkeeping on the trailing degree plus faithfulness of the
positive cone: `k` is the infimum over directions-components of the trailing
degrees, so (i) every component kills its coefficients below `k`, and (ii) the
infimum is ATTAINED at some component `i₀` whose order-`k` coefficient is
therefore nonzero; `hfaith` upgrades `0 ≤ star c * c` to `0 < star c * c`
there, and `Finset.sum_pos'` propagates strictness to the sum. -/
theorem ov_lojasiewicz_order
    {B : Type} [Ring B] [StarRing B] [PartialOrder B] [StarOrderedRing B]
    (hfaith : ∀ c : B, star c * c = 0 → c = 0)
    {n : ℕ} (X : Matrix (Fin n) (Fin n) (Polynomial B))
    (hdeg : R3.IsDegenerateAtZero B X)
    (ξ : Fin n → B) (k : ℕ)
    (hk : R3.ovVanishingOrder B X ξ = (k : ℕ∞)) :
    (∀ j < k, R3.ovDatumCoeff B X ξ j = 0) ∧
      0 < R3.ovLeadingCertificate B X ξ k := by
  classical
  have hge : ∀ i : Fin n, ((k : ℕ∞)) ≤ (ovFamilyImage B X ξ i).trailingDegree := by
    intro i
    rw [← hk]
    exact Finset.inf_le (Finset.mem_univ i)
  constructor
  · intro j hj
    funext i
    by_contra hc
    have hle := Polynomial.trailingDegree_le_of_ne_zero hc
    have hjk : ((j : ℕ∞)) < (k : ℕ∞) := by exact_mod_cast hj
    exact absurd (le_trans (hge i) hle) (by exact_mod_cast not_le.mpr hjk)
  · have hne : (Finset.univ : Finset (Fin n)).Nonempty := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · exfalso
        rw [ovVanishingOrder] at hk
        simp at hk
      · exact Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hn)
    obtain ⟨i₀, -, hi₀⟩ :=
      Finset.exists_mem_eq_inf Finset.univ hne (fun i => (ovFamilyImage B X ξ i).trailingDegree)
    have hti : (ovFamilyImage B X ξ i₀).trailingDegree = (k : ℕ∞) := by
      rw [← hi₀, ← hk, ovVanishingOrder]
    have hne0 : ovFamilyImage B X ξ i₀ ≠ 0 := by
      intro h0
      rw [h0] at hti
      simp at hti
    have hnat : (ovFamilyImage B X ξ i₀).natTrailingDegree = k :=
      Polynomial.natTrailingDegree_eq_of_trailingDegree_eq_some hti
    have hcoeff : (ovFamilyImage B X ξ i₀).coeff k ≠ 0 := by
      rw [← hnat]
      exact Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr hne0
    have hpos : 0 < star (ovDatumCoeff B X ξ k i₀) * (ovDatumCoeff B X ξ k i₀) :=
      lt_of_le_of_ne (star_mul_self_nonneg _) (fun hz => hcoeff (hfaith _ hz.symm))
    exact Finset.sum_pos' (fun i _ => star_mul_self_nonneg _) ⟨i₀, Finset.mem_univ i₀, hpos⟩

end DiscoveryKernels.R3
