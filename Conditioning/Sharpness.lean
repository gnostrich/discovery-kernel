/-
Copyright (c) 2026 discovery-kernels contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.

# Sharpness witnesses

A library that only certifies floors cannot tell a tight bound from a
conservative one. This file certifies **where the floor is exact and where it
degenerates**, on explicit exact-rational inputs. It is the part of this tier
that is more than a formalization of textbook material.

Three witnesses, each fully proved, no `sorry`, no `native_decide`:

1. `diag_dist_exact` — an input where the certified floor is **exactly** the
   distance to ill-posedness. The checker's optimum on this input is `c = 3`
   (both `condCheck A 3 = true` and `condCheck A c = true → c ≤ 3` are
   certified), so `dist(A, Σ) ≥ 3`; and an explicit perturbation of spectral
   norm `3` makes `A` singular, so `dist(A, Σ) ≤ 3`. Hence `dist(A, Σ) = 3` on
   the nose, with **no appeal to Eckart–Young**: the upper bound is a certified
   witness, not an identity.

2. `wall_*` — the **engine's wall**: an input on which the Gershgorin margin is
   *exactly zero*, so the checker certifies nothing positive no matter how the
   entries are enclosed — and yet the input is genuinely well-posed, with a
   positive margin certified by a stronger route. This is the exact analogue of
   `certified-positivity`'s `three_grid_last_row_gershgorin_zero`, transplanted
   from the Gram-kernel setting to conditioning.

3. `singular_dist_zero` — a genuinely ill-posed input, where `dist(·, Σ) = 0`
   and *every* positive certificate is impossible. The floor is zero and the
   zero is the truth.

Witness 2 is the one that carries information: it separates "the bound is
small because the problem is hard" (witness 3) from "the bound is small because
*this engine* is blind" (witness 2). Without both, a reported `0` is
uninterpretable — and by `distGE_zero_vacuous` it is also a vacuous statement.
-/
import Conditioning.Checker

open scoped BigOperators Matrix

namespace DiscoveryKernels.Cond

/-! ## Witness 1 — the certified floor is exactly the distance to `Σ` -/

/-- The exact-rational input of witness 1. -/
def diagA : Matrix (Fin 2) (Fin 2) ℚ := !![3, 0; 0, 5]

/-- The explicit singular perturbation realizing the distance. -/
def diagE : Matrix (Fin 2) (Fin 2) ℝ := !![-3, 0; 0, 0]

theorem toReal_diagA : toReal diagA = !![(3 : ℝ), 0; 0, 5] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toReal, diagA]

/-- The executable exact-rational checker accepts `c = 3` on this input. -/
theorem diagA_condCheck : condCheck diagA 3 = true := by
  rw [condCheck_eq_true]
  refine ⟨by norm_num, ?_⟩
  intro i
  fin_cases i <;>
    simp [gershRadiusQ_eq, gramQ, diagA, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

/-- …and `3` is the **best** the checker can do here: the engine's output on
this input is exactly `3`, so witness 1 pins the engine, not just one lucky
value. -/
theorem diagA_condCheck_le (c : ℚ) (h : condCheck diagA c = true) : c ≤ 3 := by
  rw [condCheck_eq_true] at h
  obtain ⟨hc, hrows⟩ := h
  have h0 := hrows 0
  have hr : gershRadiusQ (gramQ diagA) 0 = 0 := by
    simp [gershRadiusQ_eq, gramQ, diagA, Matrix.mul_apply, Fin.sum_univ_two]
  have hd : gramQ diagA 0 0 = 9 := by
    simp [gramQ, diagA, Matrix.mul_apply, Fin.sum_univ_two]; norm_num
  rw [hr, hd] at h0
  nlinarith [h0, hc]

theorem diagE_mulVec (v : Fin 2 → ℝ) : diagE *ᵥ v = ![-3 * v 0, 0] := by
  funext i
  fin_cases i <;> simp [diagE, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- `‖diagE‖₂ ≤ 3`: the perturbation really is at distance `3`. -/
theorem diagE_specNorm : SpecNormLe diagE 3 := by
  intro v
  rw [diagE_mulVec]
  simp only [sqNorm, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons]
  nlinarith [sq_nonneg (v 1)]

/-- `diagA + diagE` is singular: the perturbation lands in `Σ`. -/
theorem diagA_add_diagE_singular : (toReal diagA + diagE).det = 0 := by
  rw [toReal_diagA]
  simp [Matrix.det_fin_two, diagE]

/-- **WITNESS 1 — the certified floor is attained.**

* the executable exact-rational checker accepts `c = 3` and nothing larger;
* hence `dist(diagA, Σ) ≥ 3`;
* an explicit perturbation of spectral norm `3` makes it singular, so
  `dist(diagA, Σ) ≤ 3`.

Therefore `dist(diagA, Σ) = 3` exactly: the bound this tier certifies is
**tight, not conservative**, on this input. The upper bound is proved by
exhibiting the perturbation, so nothing here uses Eckart–Young. -/
theorem diag_dist_exact :
    condCheck diagA 3 = true ∧
      DistGE (toReal diagA) 3 ∧
      (∀ c : ℝ, 3 < c → ¬ DistGE (toReal diagA) c) ∧
      (∀ c : ℚ, condCheck diagA c = true → c ≤ 3) := by
  refine ⟨diagA_condCheck, ?_, ?_, diagA_condCheck_le⟩
  · have := condCheck_distGE diagA 3 diagA_condCheck
    simpa using this
  · intro c hc
    exact not_distGE_of_singular_perturbation (by norm_num) hc diagE_specNorm
      diagA_add_diagE_singular

/-! ## Witness 2 — the Gershgorin wall: margin exactly zero on a well-posed input -/

/-- The exact-rational input of witness 2: a unimodular shear, `det = 1`. -/
def wallA : Matrix (Fin 2) (Fin 2) ℚ := !![1, 1; 0, 1]

/-- The Gram matrix of `wallA`, computed exactly over `ℚ`. -/
theorem wallA_gram : gramQ wallA = !![1, 1; 1, 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gramQ, wallA, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

theorem wallA_gram_00 : gramQ wallA 0 0 = 1 := by
  simp [gramQ, wallA, Matrix.mul_apply, Fin.sum_univ_two]

theorem wallA_gersh_radius_0 : gershRadiusQ (gramQ wallA) 0 = 1 := by
  simp [gershRadiusQ_eq, gramQ, wallA, Matrix.mul_apply, Fin.sum_univ_two]

/-- **WITNESS 2(a) — the zero-margin identity.** In the first row of the exact
rational Gram matrix `wallAᵀ · wallA`, the diagonal entry equals the
off-diagonal absolute row sum exactly. The row's diagonal-dominance margin is
therefore **exactly `0`**, not merely small: no sharper enclosure of the entries
can change it, because the entries are exact rationals and the identity is an
equality.

This is the conditioning analogue of `certified-positivity`'s
`three_grid_last_row_gershgorin_zero`. -/
theorem wall_gersh_margin_zero :
    gramQ wallA 0 0 - gershRadiusQ (gramQ wallA) 0 = 0 := by
  rw [wallA_gram_00, wallA_gersh_radius_0]; ring

/-- **WITNESS 2(b) — the engine certifies nothing positive.** On this input the
executable checker returns `true` only for `c = 0`. Since `DistGE A 0` is
vacuously true for *every* matrix (`distGE_zero_vacuous`), the engine's output
here carries **no information at all**. Saying so is the point: a bound that
degenerates to `0` is a fake theorem unless it is labelled as one. -/
theorem wall_condCheck_forces_zero (c : ℚ) (h : condCheck wallA c = true) : c = 0 := by
  rw [condCheck_eq_true] at h
  obtain ⟨hc, hrows⟩ := h
  have h0 := hrows 0
  rw [wallA_gram_00, wallA_gersh_radius_0] at h0
  nlinarith [h0, hc, sq_nonneg c]

/-- The checker does accept `c = 0`, so `0` really is the engine's exact output
on this input — the wall is at zero, not below it. -/
theorem wall_condCheck_zero : condCheck wallA 0 = true := by
  rw [condCheck_eq_true]
  refine ⟨le_rfl, ?_⟩
  intro i
  fin_cases i <;>
    simp [gershRadiusQ_eq, gramQ, wallA, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

theorem toReal_wallA : toReal wallA = !![(1 : ℝ), 1; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toReal, wallA]

theorem wallA_mulVec (v : Fin 2 → ℝ) : toReal wallA *ᵥ v = ![v 0 + v 1, v 1] := by
  rw [toReal_wallA]
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- **WITNESS 2(c) — but the input is genuinely well-posed.** A direct Rayleigh
argument (not Gershgorin) certifies `σ_min(wallA) ≥ 1/2`, hence
`dist(wallA, Σ) ≥ 1/2 > 0`.

So the zero in 2(a)/2(b) is a limitation of the **Gershgorin engine**, not a
property of the input. That distinction — certified on both sides — is exactly
what a sharpness witness is for. (The true value is
`σ_min = (√5 - 1)/2 ≈ 0.618`; we certify the rational floor `1/2`, which is what
an exact-arithmetic certificate can carry.) -/
theorem wall_sigmaMin_half : SigmaMinGE (toReal wallA) (1 / 2) := by
  intro v
  rw [wallA_mulVec]
  simp only [sqNorm, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons]
  nlinarith [sq_nonneg (3 * v 0 + 4 * v 1), sq_nonneg (v 1)]

/-- Packaged form of witness 2(c): a genuine positive certified distance to
ill-posedness on the very input where the Gershgorin engine reads exactly zero. -/
theorem wall_distGE_half : DistGE (toReal wallA) (1 / 2) :=
  distGE_of_sigmaMinGE wall_sigmaMin_half

/-- **WITNESS 2, packaged.** The Gershgorin margin is exactly zero; the checker
therefore certifies only `c = 0`, which is vacuous; yet the input has certified
distance at least `1/2` to ill-posedness. -/
theorem gershgorin_wall :
    gramQ wallA 0 0 - gershRadiusQ (gramQ wallA) 0 = 0 ∧
      (∀ c : ℚ, condCheck wallA c = true → c = 0) ∧
      DistGE (toReal wallA) (1 / 2) :=
  ⟨wall_gersh_margin_zero, wall_condCheck_forces_zero, wall_distGE_half⟩

/-! ## Witness 3 — a genuinely ill-posed input -/

/-- The exact-rational input of witness 3: a rank-one symmetric matrix, an
element of `Σ` itself. -/
def singA : Matrix (Fin 2) (Fin 2) ℚ := !![1, 1; 1, 1]

theorem toReal_singA : toReal singA = !![(1 : ℝ), 1; 1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toReal, singA]

theorem singA_det_zero : (toReal singA).det = 0 := by
  rw [toReal_singA]
  simp [Matrix.det_fin_two]

/-- **WITNESS 3 — the floor is zero and the zero is the truth.** For this input
no positive certificate is possible: `dist(·, Σ) = 0`. Contrast with witness 2,
where the engine also reports `0` but the truth is `≥ 1/2`. Certifying both
cases is what makes a reported floor interpretable. -/
theorem singular_dist_zero : ∀ c : ℝ, 0 < c → ¬ DistGE (toReal singA) c := by
  intro c hc
  refine not_distGE_of_singular_perturbation (E := 0) (b := 0) le_rfl hc ?_ ?_
  · intro v; simp [sqNorm]
  · simpa using singA_det_zero

end DiscoveryKernels.Cond
