/-
Copyright (c) 2026 discovery-kernels contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.

R1 — the PSLQ termination / lower-bound theorem, Borwein–Lisoněk form, over
the state's EXACT rational Gram–Schmidt data (no `Float`, no `ℝ`).

The classical statement (Ferguson–Bailey–Arno 1999, Thm 1; Borwein–Lisoněk)
is `‖m‖ ≥ 1 / max_j |H_{jj}|` for every integer relation `m` of `x`, where
`H` is the algorithm's lower-trapezoidal Gram–Schmidt matrix. In the
CSV/HJLS normalization used here the same inequality is read on the *primal*
side: the state's GSO data is `gso (s.proj x)`, the Gram–Schmidt sequence of
the `x`-orthogonal projections of the current basis columns, and the bound
reads

  `‖m‖² ≥ (z k)² * ‖b*_k‖² ≥ ‖b*_k‖²`,

where `z = Binv · m` is the relation read in the algorithm's own coordinates
and `k` is the top of the support of `z`. (`H_{jj}` and `‖b*_j‖` are
reciprocal diagonals of mutually inverse triangular factors, which is why the
classical form has a `max` and a reciprocal and this one does not.)

The index `k` is genuinely needed: the `n` projections `proj x j` span the
`(n-1)`-dimensional space `x^⊥`, so exactly one GSO vector degenerates
(`‖b*_j‖ = 0`) and a `min` over all `j` would be the trivial bound `0`. The
theorem below therefore pins `k` (the last index at which the relation has a
nonzero coordinate in the algorithm's basis) rather than hiding it behind a
`min`; `gsoNormSq_le_of_relation_of_min` packages the uniform-bound corollary.

Everything here is proved; there are no `sorry`s in this file.
-/
import R1_PSLQ.Core

namespace DiscoveryKernels.R1

open Matrix Finset

variable {n : ℕ}

/-! ## Orthogonality of the rational Gram–Schmidt data

Mathlib's `gramSchmidt` is unavailable over `ℚ` (it needs `RCLike`), so the
orthogonality of `gso` is proved here from scratch. The division-by-zero
convention (`_ / 0 = 0`) is harmless: over `ℚ`, `v ⬝ᵥ v = 0 ↔ v = 0`, so a
degenerate direction contributes nothing on either side. -/

private theorem gso_orth_aux (v : Fin n → Fin n → ℚ) :
    ∀ N : ℕ, ∀ j : Fin n, (j : ℕ) ≤ N → ∀ l : Fin n, l < j →
      gso v j ⬝ᵥ gso v l = 0 := by
  intro N
  induction N with
  | zero =>
    intro j hj l hl
    have h := Fin.lt_def.mp hl
    omega
  | succ N ih =>
    intro j hj l hl
    have hlj : (l : ℕ) < (j : ℕ) := Fin.lt_def.mp hl
    have hio : ∀ i ∈ Finset.Iio j, i ≠ l → gso v i ⬝ᵥ gso v l = 0 := by
      intro i hi hil
      have hij : (i : ℕ) < (j : ℕ) := Fin.lt_def.mp (Finset.mem_Iio.mp hi)
      rcases lt_or_gt_of_ne hil with h | h
      · have h2 := ih l (by omega) i h
        rwa [dotProduct_comm] at h2
      · exact ih i (by omega) l h
    have hsum :
        (∑ i ∈ Finset.Iio j,
            ((v j ⬝ᵥ gso v i) / (gso v i ⬝ᵥ gso v i)) • gso v i) ⬝ᵥ gso v l
          = ((v j ⬝ᵥ gso v l) / (gso v l ⬝ᵥ gso v l)) * (gso v l ⬝ᵥ gso v l) := by
      rw [sum_dotProduct, Finset.sum_eq_single l]
      · rw [smul_dotProduct, smul_eq_mul]
      · intro i hi hil
        rw [smul_dotProduct, hio i hi hil, smul_zero]
      · intro hnot
        exact absurd (Finset.mem_Iio.mpr hl) hnot
    rw [gso_def v j, sub_dotProduct, hsum]
    by_cases hG : gso v l ⬝ᵥ gso v l = 0
    · have hz : gso v l = 0 := dotProduct_self_eq_zero.mp hG
      rw [hz]
      simp
    · rw [div_mul_cancel₀ _ hG, sub_self]

/-- **The rational Gram–Schmidt data is orthogonal.** -/
theorem gso_orthogonal (v : Fin n → Fin n → ℚ) {j l : Fin n} (h : j ≠ l) :
    gso v j ⬝ᵥ gso v l = 0 := by
  rcases lt_or_gt_of_ne h with hlt | hlt
  · have h2 := gso_orth_aux v (l : ℕ) l le_rfl j hlt
    rwa [dotProduct_comm] at h2
  · exact gso_orth_aux v (j : ℕ) j le_rfl l hlt

/-- `v j` is its own Gram–Schmidt vector plus a combination of the earlier
ones (the unitriangularity of Gram–Schmidt). -/
theorem v_eq_gso_add_tail (v : Fin n → Fin n → ℚ) (j : Fin n) :
    v j = gso v j +
      ∑ i ∈ Finset.Iio j, ((v j ⬝ᵥ gso v i) / (gso v i ⬝ᵥ gso v i)) • gso v i :=
  sub_eq_iff_eq_add.mp (gso_def v j).symm

private theorem gsoTail_dotProduct (v : Fin n → Fin n → ℚ) {j l : Fin n}
    (hjl : (j : ℕ) ≤ (l : ℕ)) :
    (∑ i ∈ Finset.Iio j,
      ((v j ⬝ᵥ gso v i) / (gso v i ⬝ᵥ gso v i)) • gso v i) ⬝ᵥ gso v l = 0 := by
  rw [sum_dotProduct]
  refine Finset.sum_eq_zero fun i hi => ?_
  have hij : (i : ℕ) < (j : ℕ) := Fin.lt_def.mp (Finset.mem_Iio.mp hi)
  have hil : i ≠ l := by
    intro h
    subst h
    omega
  rw [smul_dotProduct, gso_orthogonal v hil, smul_zero]

/-- `⟨v j, b*_j⟩ = ‖b*_j‖²`. -/
theorem dotProduct_gso_self (v : Fin n → Fin n → ℚ) (j : Fin n) :
    v j ⬝ᵥ gso v j = gso v j ⬝ᵥ gso v j := by
  rw [v_eq_gso_add_tail v j, add_dotProduct, gsoTail_dotProduct v (le_refl (j : ℕ)),
    add_zero]

/-- `⟨v j, b*_l⟩ = 0` for `j < l`. -/
theorem dotProduct_gso_of_lt (v : Fin n → Fin n → ℚ) {j l : Fin n} (h : j < l) :
    v j ⬝ᵥ gso v l = 0 := by
  rw [v_eq_gso_add_tail v j, add_dotProduct, gso_orthogonal v (ne_of_lt h),
    gsoTail_dotProduct v (le_of_lt (Fin.lt_def.mp h)), zero_add]

namespace PSLQState

/-! ## The relation in the algorithm's own coordinates -/

theorem B_mulVec_coords {x : Fin n → ℚ} {s : PSLQState n} (hInv : s.Inv x)
    (m : Fin n → ℤ) : s.B *ᵥ s.coords m = m := by
  rw [coords, mulVec_mulVec, hInv.hBl, one_mulVec]

theorem coords_ne_zero {x : Fin n → ℚ} {s : PSLQState n} (hInv : s.Inv x)
    {m : Fin n → ℤ} (hm : m ≠ 0) : s.coords m ≠ 0 := by
  intro h
  exact hm (by rw [← B_mulVec_coords hInv m, h, mulVec_zero])

theorem sum_B_coords {x : Fin n → ℚ} {s : PSLQState n} (hInv : s.Inv x)
    (m : Fin n → ℤ) (i : Fin n) :
    ∑ j, ((s.B i j : ℚ)) * ((s.coords m j : ℤ) : ℚ) = (m i : ℚ) := by
  have h := congrFun (B_mulVec_coords hInv m) i
  have h' : ∑ j, s.B i j * s.coords m j = m i := by
    simpa [Matrix.mulVec, dotProduct] using h
  have : ((∑ j, s.B i j * s.coords m j : ℤ) : ℚ) = (m i : ℚ) := by rw [h']
  rw [← this]
  push_cast
  ring

/-- Under the invariant, the relation's coordinates annihilate `y`. -/
theorem sum_coords_mul_y {x : Fin n → ℚ} {s : PSLQState n} (hInv : s.Inv x)
    {m : Fin n → ℤ} (hm : IsIntRelation x m) :
    ∑ j, ((s.coords m j : ℤ) : ℚ) * s.y j = 0 := by
  have hy := hInv.hy
  calc ∑ j, ((s.coords m j : ℤ) : ℚ) * s.y j
      = ∑ j, ∑ i, x i * ((s.B i j : ℚ) * ((s.coords m j : ℤ) : ℚ)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hy j, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = ∑ i, ∑ j, x i * ((s.B i j : ℚ) * ((s.coords m j : ℤ) : ℚ)) :=
        Finset.sum_comm
    _ = ∑ i, x i * ∑ j, (s.B i j : ℚ) * ((s.coords m j : ℤ) : ℚ) := by
        exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
    _ = ∑ i, (m i : ℚ) * x i := by
        exact Finset.sum_congr rfl fun i _ => by
          rw [sum_B_coords hInv m i]; ring
    _ = 0 := hm.2

/-- **The relation is the `z`-combination of the projected basis columns.**
This is where the CSV/HJLS normalization pays off: `m ⊥ x`, so `m` equals its
own `x`-orthogonal projection, which is `∑ z j • proj x j` — all rational. -/
theorem relation_eq_sum_smul_proj {x : Fin n → ℚ} {s : PSLQState n}
    (hInv : s.Inv x) {m : Fin n → ℤ} (hm : IsIntRelation x m) :
    (fun i => (m i : ℚ)) = ∑ j, ((s.coords m j : ℤ) : ℚ) • s.proj x j := by
  funext i
  have hz := sum_coords_mul_y hInv hm
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, proj, col,
    Pi.sub_apply]
  have hsplit : ∀ j : Fin n,
      ((s.coords m j : ℤ) : ℚ) * ((s.B i j : ℚ) - s.y j / (x ⬝ᵥ x) * x i)
        = ((s.B i j : ℚ)) * ((s.coords m j : ℤ) : ℚ)
          - (((s.coords m j : ℤ) : ℚ) * s.y j) * (x i / (x ⬝ᵥ x)) := by
    intro j; ring
  rw [Finset.sum_congr rfl fun j _ => hsplit j, Finset.sum_sub_distrib,
    ← Finset.sum_mul, hz, zero_mul, sub_zero, sum_B_coords hInv m i]

/-! ## The Borwein–Lisoněk lower bound -/

/-- The inner product of the relation with the `k`-th Gram–Schmidt vector,
where `k` is the top of the support of `z = Binv · m`: it is exactly
`z k * ‖b*_k‖²`. -/
theorem dotProduct_gso_eq {x : Fin n → ℚ} {s : PSLQState n} (hInv : s.Inv x)
    {m : Fin n → ℤ} (hm : IsIntRelation x m) (k : Fin n)
    (hlast : ∀ j, k < j → s.coords m j = 0) :
    (fun i => (m i : ℚ)) ⬝ᵥ gso (s.proj x) k
      = ((s.coords m k : ℤ) : ℚ) * s.gsoNormSq x k := by
  rw [relation_eq_sum_smul_proj hInv hm, sum_dotProduct, Finset.sum_eq_single k]
  · rw [smul_dotProduct, dotProduct_gso_self, gsoNormSq, smul_eq_mul]
  · intro j _ hjk
    rw [smul_dotProduct]
    rcases lt_or_gt_of_ne hjk with h | h
    · rw [dotProduct_gso_of_lt _ h, smul_zero]
    · rw [hlast j h]
      simp
  · intro hnot
    exact absurd (Finset.mem_univ k) hnot

theorem gsoNormSq_nonneg (x : Fin n → ℚ) (s : PSLQState n) (k : Fin n) :
    0 ≤ s.gsoNormSq x k := by
  rw [gsoNormSq, dotProduct]
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg _

/-- **The lower bound, state form (Borwein–Lisoněk).** For a state satisfying
the loop invariant and any integer relation `m` of `x`, if `k` is the last
index at which `m` has a nonzero coordinate in the algorithm's basis
(`z = Binv · m`), then the squared euclidean norm of `m` is at least the
`k`-th squared Gram–Schmidt norm of the state's rational GSO data. -/
theorem gsoNormSq_le_of_relation {x : Fin n → ℚ} {s : PSLQState n}
    (hInv : s.Inv x) {m : Fin n → ℤ} (hm : IsIntRelation x m) (k : Fin n)
    (hk : s.coords m k ≠ 0) (hlast : ∀ j, k < j → s.coords m j = 0) :
    s.gsoNormSq x k ≤ ∑ i, ((m i : ℚ)) ^ 2 := by
  have hG0 : 0 ≤ s.gsoNormSq x k := gsoNormSq_nonneg x s k
  have hM0 : 0 ≤ ∑ i, ((m i : ℚ)) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hinner := dotProduct_gso_eq hInv hm k hlast
  -- discrete Cauchy–Schwarz over `ℚ`
  have hCS : ((fun i => (m i : ℚ)) ⬝ᵥ gso (s.proj x) k) ^ 2
      ≤ (∑ i, ((m i : ℚ)) ^ 2) * s.gsoNormSq x k := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => (m i : ℚ))
      (fun i => gso (s.proj x) k i)
    have hg : s.gsoNormSq x k = ∑ i, (gso (s.proj x) k i) ^ 2 := by
      rw [gsoNormSq, dotProduct]
      exact Finset.sum_congr rfl fun i _ => (pow_two _).symm
    rw [hg]
    simpa [dotProduct] using h
  rw [hinner] at hCS
  by_cases hG : s.gsoNormSq x k = 0
  · rw [hG]; exact hM0
  · have hGpos : 0 < s.gsoNormSq x k := lt_of_le_of_ne hG0 (Ne.symm hG)
    have hz1 : (1 : ℚ) ≤ ((s.coords m k : ℤ) : ℚ) ^ 2 := by
      have h0 : (0 : ℤ) < (s.coords m k) ^ 2 := by positivity
      have h1 : (1 : ℤ) ≤ (s.coords m k) ^ 2 := by omega
      exact_mod_cast h1
    have hsq : (1 : ℚ) * s.gsoNormSq x k ^ 2
        ≤ ((s.coords m k : ℤ) : ℚ) ^ 2 * s.gsoNormSq x k ^ 2 :=
      mul_le_mul_of_nonneg_right hz1 (sq_nonneg _)
    have h2 : s.gsoNormSq x k * s.gsoNormSq x k
        ≤ (∑ i, ((m i : ℚ)) ^ 2) * s.gsoNormSq x k := by nlinarith [hsq, hCS]
    exact le_of_mul_le_mul_right h2 hGpos

/-- Uniform-bound corollary: any rational `c` that lower-bounds every squared
Gram–Schmidt norm of the state lower-bounds `‖m‖²` for every integer relation
`m` of `x`. (Non-vacuous exactly when the state's GSO data is nondegenerate;
see the module docstring.) -/
theorem gsoNormSq_le_of_relation_of_min {x : Fin n → ℚ} {s : PSLQState n}
    (hInv : s.Inv x) {m : Fin n → ℤ} (hm : IsIntRelation x m) (c : ℚ)
    (hc : ∀ j, c ≤ s.gsoNormSq x j) : c ≤ ∑ i, ((m i : ℚ)) ^ 2 := by
  classical
  have hz : s.coords m ≠ 0 := coords_ne_zero hInv hm.1
  have hex : ∃ j : Fin n, s.coords m j ≠ 0 := by
    by_contra h
    exact hz (funext fun j => not_not.mp fun hj => h ⟨j, hj⟩)
  obtain ⟨j0, hj0⟩ := hex
  -- the largest index of the support
  obtain ⟨k, hk, hmax⟩ :
      ∃ k : Fin n, s.coords m k ≠ 0 ∧ ∀ j, s.coords m j ≠ 0 → j ≤ k := by
    have hne : (Finset.univ.filter fun j => s.coords m j ≠ 0).Nonempty :=
      ⟨j0, by simpa using hj0⟩
    refine ⟨(Finset.univ.filter fun j => s.coords m j ≠ 0).max' hne, ?_, ?_⟩
    · have := (Finset.univ.filter fun j => s.coords m j ≠ 0).max'_mem hne
      simpa using this
    · intro j hj
      exact Finset.le_max' _ j (by simpa using hj)
  refine le_trans (hc k) (gsoNormSq_le_of_relation hInv hm k hk ?_)
  intro j hj
  by_contra hne
  exact absurd (hmax j hne) (not_le.mpr hj)

end PSLQState

/-! ## Driver-level statements -/

theorem pslqState_eq_iterate (x : Fin n → ℚ) (k : ℕ) :
    pslqState x k = (pslqRound x)^[k] (PSLQState.init x) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pslqState, ih, Function.iterate_succ_apply']

theorem pslqAux_none_report (x : Fin n → ℚ) : ∀ (fuel : ℕ) (s : PSLQState n),
    pslqAux x fuel s = none → ((pslqRound x)^[fuel] s).report? = none := by
  intro fuel
  induction fuel with
  | zero =>
    intro s h
    rw [Function.iterate_zero_apply]
    exact h
  | succ fuel ih =>
    intro s h
    rw [pslqAux] at h
    cases hr : s.report? with
    | some m => rw [hr] at h; exact absurd h (by simp)
    | none =>
      rw [hr] at h
      rw [Function.iterate_succ_apply]
      exact ih _ h

/-- If the detector reported nothing within `fuel` rounds, then the state
after `fuel` rounds has no report either. -/
theorem pslq_none_report (x : Fin n → ℚ) (fuel : ℕ) (h : pslq x fuel = none) :
    (pslqState x fuel).report? = none := by
  rw [pslqState_eq_iterate]
  exact pslqAux_none_report x fuel _ h

/-- ... equivalently, no exact zero has appeared in `y`. -/
theorem pslq_none_y_ne_zero (x : Fin n → ℚ) (fuel : ℕ) (h : pslq x fuel = none)
    (j : Fin n) : (pslqState x fuel).y j ≠ 0 := by
  have h0 := pslq_none_report x fuel h
  rw [PSLQState.report?, Option.map_eq_none_iff, List.find?_eq_none] at h0
  have := h0 j (List.mem_finRange j)
  simpa using this

-- `hnone` is deliberately part of the statement (the charter's "while no
-- relation has been reported" clause, and what makes the bound the relevant
-- one) even though the proof does not need it: the bound holds at every state
-- satisfying the loop invariant. See `PSLQState.gsoNormSq_le_of_relation` for
-- the hypothesis-free state-level form.
set_option linter.unusedVariables false in
/-- **PSLQ lower bound (Borwein–Lisoněk form).** While the detector has
reported no relation within `fuel` rounds, every integer relation `m` of the
exact rational input `x` has squared euclidean norm at least the explicit
rational number `gsoNormSq x (pslqState x fuel) k` read off the state's
rational Gram–Schmidt data, where `k` is the last index at which `m` has a
nonzero coordinate in the algorithm's own basis. -/
theorem pslq_lower_bound (x : Fin n → ℚ) (fuel : ℕ) (hnone : pslq x fuel = none)
    (m : Fin n → ℤ) (hm : IsIntRelation x m) (k : Fin n)
    (hk : (pslqState x fuel).coords m k ≠ 0)
    (hlast : ∀ j, k < j → (pslqState x fuel).coords m j = 0) :
    (pslqState x fuel).gsoNormSq x k ≤ ∑ i, ((m i : ℚ)) ^ 2 :=
  PSLQState.gsoNormSq_le_of_relation (pslqState_inv x fuel) hm k hk hlast

end DiscoveryKernels.R1
