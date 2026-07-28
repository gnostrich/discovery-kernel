/-
Copyright (c) 2026 discovery-kernels contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.

# The Gershgorin / diagonal-dominance engine

Mathlib **does** have Gershgorin, in `Mathlib/LinearAlgebra/Matrix/Gershgorin.lean`
(ported from mathlib3): `Matrix.eigenvalue_mem_ball` (eigenvalue localisation,
over any `NormedField` and any `Fintype` index), together with
`Matrix.det_ne_zero_of_sum_row_lt_diag` and `..._col_lt_diag` (strict diagonal
dominance ⟹ nonsingular). An earlier version of this file claimed the opposite;
that claim was FALSE and is corrected here (2026-07-28, STATEMENT-DEFECT — see
STATEMENTS.md and Conditioning/SWEEP.md).

We therefore claim **no novelty** for eigenvalue localisation or for the
diagonal-dominance nonsingularity lemma. What this file retains:

* `gershgorin_rayleigh_floor` — a *Rayleigh quadratic-form* lower bound
  `μ * ‖x‖² ≤ xᵀMx` under diagonal dominance. This is a different statement
  from eigenvalue localisation, and it is **not** in Mathlib's Gershgorin file
  (verified 2026-07-28: that file contains exactly `eigenvalue_mem_ball`,
  `det_ne_zero_of_sum_row_lt_diag`, `det_ne_zero_of_sum_col_lt_diag`). It is
  the form the checker actually consumes.
* `gershgorin_disc` — a specialization of `Matrix.eigenvalue_mem_ball` to `ℝ`,
  `Fin n` and the `IsEigenvalue` shape used downstream. Retained for interface
  convenience only; it duplicates Mathlib at strictly weaker generality.

Two forms are given:

* `gershgorin_rayleigh_floor` — the **Rayleigh floor**: strict diagonal
  dominance with margin `μ` gives `μ‖x‖² ≤ xᵀMx` for symmetric `M`. This is the
  form adapted (schema-level; **no code imported**, the pin differs) from
  `gnostrich/certified-positivity`'s `R5.gershgorin_margin`.
* `gershgorin_disc` — the **circle theorem** for real eigenvalues of an
  arbitrary square real matrix: every real eigenvalue lies in some Gershgorin
  disc. Proved by the maximal-coordinate argument; needs no symmetry.

Both are purely algebraic: **no sign assumption on `μ`**, so both are honest
about degenerating (a `μ ≤ 0` conclusion is the vacuous case, and
`Sharpness.lean` exhibits an input where `μ = 0` exactly).
-/
import Conditioning.Defs

open scoped BigOperators Matrix

namespace DiscoveryKernels.Cond

variable {n : ℕ}

/-- The Gershgorin radius of row `i`: the sum of the absolute values of the
off-diagonal entries. -/
def gershRadius (M : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : ℝ :=
  ∑ j ∈ Finset.univ.erase i, |M i j|

/-- Rewrite an `erase`-sum as a full sum with an `if`. -/
private theorem sum_erase_as_ite {α : Type*} [AddCommMonoid α] (f : Fin n → α) (i : Fin n) :
    ∑ j ∈ Finset.univ.erase i, f j = ∑ j, if j ≠ i then f j else 0 := by
  rw [← Finset.filter_ne' Finset.univ i, Finset.sum_filter]

/-- **Gershgorin/diagonal-dominance Rayleigh floor.** For a real symmetric
matrix `M`, if every row satisfies `μ + (off-diagonal absolute row sum) ≤ Mᵢᵢ`,
then the quadratic form is bounded below by `μ‖x‖²`.

No sign assumption is made on `μ`; for `μ ≤ 0` the conclusion is true but
vacuous, and saying so is part of the contract of this tier. -/
theorem gershgorin_rayleigh_floor (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : Mᵀ = M) (μ : ℝ)
    (hrow : ∀ i, μ + gershRadius M i ≤ M i i) :
    ∀ x : Fin n → ℝ, μ * sqNorm x ≤ quadForm M x := by
  intro x
  have hsymm : ∀ i j, M j i = M i j := fun i j => by
    have := congrFun (congrFun hM i) j
    simpa [Matrix.transpose_apply] using this
  -- split the quadratic form into diagonal and off-diagonal parts
  have hsplit : quadForm M x
      = ∑ i, M i i * x i ^ 2 + ∑ i, ∑ j ∈ Finset.univ.erase i, x i * M i j * x j := by
    unfold quadForm
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    ring
  -- off-diagonal part is bounded below by minus the symmetrized absolute sum
  have hoff : ∀ i : Fin n,
      -(∑ j ∈ Finset.univ.erase i, |M i j| * ((x i ^ 2 + x j ^ 2) / 2))
        ≤ ∑ j ∈ Finset.univ.erase i, x i * M i j * x j := by
    intro i
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    have h1 : (0 : ℝ) ≤ (|M i j| + M i j) * (x i + x j) ^ 2 :=
      mul_nonneg (by linarith [neg_abs_le (M i j)]) (sq_nonneg _)
    have h2 : (0 : ℝ) ≤ (|M i j| - M i j) * (x i - x j) ^ 2 :=
      mul_nonneg (by linarith [le_abs_self (M i j)]) (sq_nonneg _)
    nlinarith [h1, h2]
  have hoffsum :
      -(∑ i, ∑ j ∈ Finset.univ.erase i, |M i j| * ((x i ^ 2 + x j ^ 2) / 2))
        ≤ ∑ i, ∑ j ∈ Finset.univ.erase i, x i * M i j * x j := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun i _ => hoff i
  -- the symmetrization collapses to the Gershgorin radii
  have hswap : ∑ i, ∑ j ∈ Finset.univ.erase i, |M i j| * x j ^ 2
      = ∑ i, ∑ j ∈ Finset.univ.erase i, |M i j| * x i ^ 2 := by
    simp only [sum_erase_as_ite]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rcases eq_or_ne i j with h | h
    · simp [h]
    · rw [if_pos h, if_pos (Ne.symm h), hsymm i j]
  have hcollapse : ∑ i, ∑ j ∈ Finset.univ.erase i, |M i j| * ((x i ^ 2 + x j ^ 2) / 2)
      = ∑ i, gershRadius M i * x i ^ 2 := by
    have e1 : ∀ i : Fin n, ∑ j ∈ Finset.univ.erase i, |M i j| * ((x i ^ 2 + x j ^ 2) / 2)
        = (∑ j ∈ Finset.univ.erase i, |M i j| * x i ^ 2) / 2
          + (∑ j ∈ Finset.univ.erase i, |M i j| * x j ^ 2) / 2 := by
      intro i
      rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    simp only [e1]
    rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div, hswap]
    rw [show ∀ a : ℝ, a / 2 + a / 2 = a from fun a => by ring]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_mul]
    rfl
  -- assemble
  have hdiag : μ * sqNorm x ≤ ∑ i, M i i * x i ^ 2 - ∑ i, gershRadius M i * x i ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    unfold sqNorm
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have := hrow i
    nlinarith [sq_nonneg (x i)]
  rw [hsplit]
  linarith [hoffsum, hcollapse ▸ hoffsum]

/-- **Gershgorin's circle theorem, real-eigenvalue form.** Every real
eigenvalue of an arbitrary square real matrix lies within `gershRadius M i` of
the diagonal entry `M i i` for some `i`. No symmetry is needed.

Proved by the classical maximal-coordinate argument.

**No novelty claimed.** This is `Matrix.eigenvalue_mem_ball`
(`Mathlib/LinearAlgebra/Matrix/Gershgorin.lean`) specialized to `ℝ`, `Fin n`
and real eigenvalues; Mathlib's version is strictly more general (any
`NormedField`, any `Fintype`). Retained only because downstream code is stated
against the local `IsEigenvalue` shape. An earlier docstring asserted Mathlib
had no Gershgorin theorem; that was FALSE (corrected 2026-07-28). -/
theorem gershgorin_disc (M : Matrix (Fin n) (Fin n) ℝ) (l : ℝ)
    (hl : IsEigenvalue M l) : ∃ i : Fin n, |l - M i i| ≤ gershRadius M i := by
  obtain ⟨v, hv, hMv⟩ := hl
  -- pick a coordinate of maximal absolute value
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exact absurd (funext fun i => absurd i.2 (by omega)) hv
    · exact Finset.univ_nonempty_iff.mpr ⟨⟨0, h⟩⟩
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n)) (fun j => |v j|) hne
  have hvi : 0 < |v i| := by
    rcases eq_or_lt_of_le (abs_nonneg (v i)) with h | h
    · exact absurd (funext fun j => abs_eq_zero.mp (le_antisymm
        (h ▸ hi j (Finset.mem_univ j)) (abs_nonneg _))) hv
    · exact h
  refine ⟨i, ?_⟩
  -- the i-th row of the eigenvalue equation
  have hrow : ∑ j, M i j * v j = l * v i := by
    have := congrFun hMv i
    simpa [Matrix.mulVec, dotProduct] using this
  have hkey : (l - M i i) * v i = ∑ j ∈ Finset.univ.erase i, M i j * v j := by
    have : ∑ j, M i j * v j
        = M i i * v i + ∑ j ∈ Finset.univ.erase i, M i j * v j :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
    rw [this] at hrow
    linarith [hrow]
  have hbound : |∑ j ∈ Finset.univ.erase i, M i j * v j| ≤ gershRadius M i * |v i| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    unfold gershRadius
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hi j (Finset.mem_univ j)) (abs_nonneg _)
  have : |l - M i i| * |v i| ≤ gershRadius M i * |v i| := by
    rw [← abs_mul, hkey]; exact hbound
  exact le_of_mul_le_mul_right (by linarith) hvi

end DiscoveryKernels.Cond
