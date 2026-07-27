/-
Copyright (c) 2026 discovery-kernels contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.

R1 — THE TIER'S POINT: empirical-input soundness of exact integer-relation
detection.

The theorem is algorithm-independent: it consumes only (a) an exact rational
relation `m` of the computed approximation `xq` — which is exactly what the
exact-arithmetic core certifies — plus (b) the precision bound and (c) a
coefficient bound. Conclusion 1 is the triangle inequality with the explicit
`ε(p, M, n) = n * M * p`; conclusion 2 upgrades to a genuine exact relation
of the truth `x` under the separation hypothesis.

The statement text is copied verbatim from `Challenge.lean` (R1 section) so
the comparator's definitional-equality check is trivial.
-/
import PSLQ.Defs

namespace DiscoveryKernels.R1

/-- **Empirical-input soundness.** Input known to precision `p` (true vector
`x : Fin n → ℝ`, computed rational approximation `xq` with
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
        R1.IsIntRelation x m) := by
  obtain ⟨hm0, hq⟩ := hrel
  -- Cast the exact rational relation to ℝ.
  have hqR : ∑ i, (m i : ℝ) * (xq i : ℝ) = 0 := by
    have h := congrArg (fun q : ℚ => (q : ℝ)) hq
    push_cast at h
    simpa using h
  -- Conclusion 1: triangle inequality.
  have key : |∑ i, (m i : ℝ) * x i| ≤ (n : ℝ) * (M : ℝ) * p := by
    have hsplit : ∑ i, (m i : ℝ) * x i
        = ∑ i, (m i : ℝ) * (x i - (xq i : ℝ)) := by
      simp [mul_sub, Finset.sum_sub_distrib, hqR]
    have hterm : ∀ i ∈ Finset.univ,
        |(m i : ℝ) * (x i - (xq i : ℝ))| ≤ (M : ℝ) * p := by
      intro i _
      have hMR : |(m i : ℝ)| ≤ (M : ℝ) := by
        exact_mod_cast hM i
      have hM0 : (0 : ℝ) ≤ (M : ℝ) := le_trans (abs_nonneg _) hMR
      calc |(m i : ℝ) * (x i - (xq i : ℝ))|
          = |(m i : ℝ)| * |x i - (xq i : ℝ)| := abs_mul _ _
        _ ≤ (M : ℝ) * p :=
            mul_le_mul hMR (happ i) (abs_nonneg _) hM0
    calc |∑ i, (m i : ℝ) * x i|
        = |∑ i, (m i : ℝ) * (x i - (xq i : ℝ))| := by rw [hsplit]
      _ ≤ ∑ i, |(m i : ℝ) * (x i - (xq i : ℝ))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin n, (M : ℝ) * p := Finset.sum_le_sum hterm
      _ = (n : ℝ) * ((M : ℝ) * p) := by
          simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = (n : ℝ) * (M : ℝ) * p := by ring
  refine ⟨key, fun hsep => ⟨hm0, ?_⟩⟩
  -- Conclusion 2: separation rules out the artifact branch.
  rcases hsep m hm0 hM with h0 | hgt
  · exact h0
  · exact absurd key (not_le.mpr hgt)

end DiscoveryKernels.R1
