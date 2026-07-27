/-
Copyright (c) 2026 discovery-kernels contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.

R1 — the exact-arithmetic PSLQ-class integer-relation detector, in the
CSV/HJLS normalization (Chen–Stehlé–Villard, ISSAC 2013: PSLQ ≡ HJLS up to
scaling; the HJLS normalization keeps all Gram–Schmidt data rational).

Design:
* Exact arithmetic only: the state is a rational vector `y`, an integer
  change-of-basis matrix `B`, and an explicit integer inverse `Binv`
  (unimodularity certificate). No `Float`, no `ℝ` anywhere in this file.
* Loop invariant `PSLQState.Inv x s`: `y j = ∑ i, x i * B i j` and
  `B * Binv = 1 = Binv * B`.
* Every mutation goes through the two certified elementary column
  operations (`ElemOp.addMul`, `ElemOp.swap`), and a round is a fold of
  state-dependent op choices (`applyProgram`). Partial correctness is
  therefore INDEPENDENT of the strategy: whatever ops the strategy picks,
  the invariant is preserved (`applyProgram_inv`), and a report from the
  report site is an exact integer relation (`PSLQState.report?_spec`,
  `pslq_partial_correct`).
* The strategy (`roundProgram`) is PSLQ in the HJLS normalization: a full
  size-reduction (Hermite reduction) pass against the rational Gram–Schmidt
  data of the x-orthogonal projections of the current basis columns,
  followed by the PSLQ γ-weighted maximal-diagonal swap with γ² = 2
  (any γ² > 4/3 is admissible for PSLQ; squaring keeps the weights in ℚ).
* Following the `checkPDq_sound` schema of certified-positivity (see
  DEPS.md), `checkRelation` is a decidable Bool certificate checker with a
  soundness theorem `checkRelation_sound`.
-/
import PSLQ.Defs

namespace DiscoveryKernels.R1

open Matrix Finset

variable {n : ℕ}

/-! ## State and invariant -/

/-- The state of the detector: transformed vector `y`, integer
change-of-basis `B`, and explicit integer inverse `Binv` (the unimodularity
certificate). -/
structure PSLQState (n : ℕ) where
  y : Fin n → ℚ
  B : Matrix (Fin n) (Fin n) ℤ
  Binv : Matrix (Fin n) (Fin n) ℤ

namespace PSLQState

/-- The loop invariant: `y` is the input `x` transported by `B`
(`y = x ⬝ B`), and `Binv` is a two-sided inverse of `B` over `ℤ`. -/
structure Inv (x : Fin n → ℚ) (s : PSLQState n) : Prop where
  hy : ∀ j, s.y j = ∑ i, x i * (s.B i j : ℚ)
  hBl : s.B * s.Binv = 1
  hBr : s.Binv * s.B = 1

/-- Initial state: `y = x`, `B = Binv = 1`. -/
def init (x : Fin n → ℚ) : PSLQState n := ⟨x, 1, 1⟩

theorem init_inv (x : Fin n → ℚ) : (init x).Inv x := by
  refine ⟨fun j => ?_, ?_, ?_⟩
  · simp [init, Matrix.one_apply, apply_ite (Int.cast : ℤ → ℚ)]
  · simp [init]
  · simp [init]

end PSLQState

/-! ## Certified elementary column operations -/

/-- Elementary unimodular column operations.
* `addMul q k j`: add `q` times column `k` to column `j` (no-op if `k = j`);
* `swap j k`: exchange columns `j` and `k`. -/
inductive ElemOp (n : ℕ) where
  | addMul (q : ℤ) (k j : Fin n)
  | swap (j k : Fin n)

namespace ElemOp

/-- Apply an elementary operation to the state: `B` is multiplied on the
right by the corresponding unimodular matrix, `Binv` on the left by its
inverse, and `y` is updated incrementally (the honest PSLQ data flow). -/
def apply : ElemOp n → PSLQState n → PSLQState n
  | .addMul q k j, s =>
    if _h : k = j then s
    else
      { y := Function.update s.y j (s.y j + (q : ℚ) * s.y k)
        B := s.B * Matrix.transvection k j q
        Binv := Matrix.transvection k j (-q) * s.Binv }
  | .swap j k, s =>
      { y := fun j' => s.y (Equiv.swap j k j')
        B := s.B.submatrix id (Equiv.swap j k)
        Binv := s.Binv.submatrix (Equiv.swap j k) id }

/-- The certified-op lemma: every elementary operation preserves the loop
invariant. This is the only fact partial correctness needs about steps. -/
theorem apply_inv (e : ElemOp n) (x : Fin n → ℚ) (s : PSLQState n)
    (h : s.Inv x) : (e.apply s).Inv x := by
  obtain ⟨hy, hBl, hBr⟩ := h
  cases e with
  | addMul q k j =>
    rw [apply]
    split
    · exact ⟨hy, hBl, hBr⟩
    · rename_i hkj
      refine ⟨fun j' => ?_, ?_, ?_⟩ <;> dsimp only
      · by_cases hj' : j' = j
        · subst hj'
          rw [Function.update_self, hy j', hy k, Finset.mul_sum,
            ← Finset.sum_add_distrib]
          simp only [Matrix.mul_transvection_apply_same]
          push_cast
          exact Finset.sum_congr rfl fun i _ => by ring
        · rw [Function.update_of_ne hj', hy j']
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Matrix.mul_transvection_apply_of_ne k j i j' hj' q s.B]
      · rw [mul_assoc, ← mul_assoc (Matrix.transvection k j q),
          Matrix.transvection_mul_transvection_same k j hkj q (-q), add_neg_cancel,
          Matrix.transvection_zero, one_mul, hBl]
      · rw [mul_assoc, ← mul_assoc s.Binv, hBr, one_mul,
          Matrix.transvection_mul_transvection_same k j hkj (-q) q, neg_add_cancel,
          Matrix.transvection_zero]
  | swap j k =>
    rw [apply]
    refine ⟨fun j' => ?_, ?_, ?_⟩ <;> dsimp only
    · simpa using hy (Equiv.swap j k j')
    · have h1 := Matrix.submatrix_mul_equiv s.B s.Binv id (Equiv.swap j k) id
      rw [hBl] at h1
      simpa using h1
    · have h2 := Matrix.submatrix_mul_equiv s.Binv s.B (⇑(Equiv.swap j k))
        (Equiv.refl (Fin n)) (⇑(Equiv.swap j k))
      rw [hBr] at h2
      simpa [Matrix.submatrix_one_equiv] using h2

end ElemOp

/-! ## Programs: strategy-chosen sequences of certified ops -/

/-- Run a program: a list of state-dependent op choices, applied in order.
The strategy may compute each op from the current state (GSO data etc.);
correctness only uses that every mutation goes through `ElemOp.apply`. -/
def applyProgram (s : PSLQState n) (prog : List (PSLQState n → ElemOp n)) :
    PSLQState n :=
  prog.foldl (fun st f => (f st).apply st) s

theorem applyProgram_inv (x : Fin n → ℚ)
    (prog : List (PSLQState n → ElemOp n)) (s : PSLQState n) (h : s.Inv x) :
    (applyProgram s prog).Inv x := by
  induction prog generalizing s with
  | nil => exact h
  | cons f t ih => exact ih _ (ElemOp.apply_inv _ _ _ h)

/-! ## Report site -/

/-- Report site: the first index `j` with `y j = 0`, if any; the candidate
relation is column `j` of `B` (nonzero by unimodularity). -/
def PSLQState.report? (s : PSLQState n) : Option (Fin n → ℤ) :=
  ((List.finRange n).find? fun j => decide (s.y j = 0)).map fun j i => s.B i j

/-- Soundness of the report site: under the invariant, every reported vector
is an exact integer relation of the input. -/
theorem PSLQState.report?_spec {x : Fin n → ℚ} {s : PSLQState n}
    (hInv : s.Inv x) {m : Fin n → ℤ} (h : s.report? = some m) :
    IsIntRelation x m := by
  obtain ⟨hy, hBl, hBr⟩ := hInv
  unfold PSLQState.report? at h
  cases hf : (List.finRange n).find? fun j => decide (s.y j = 0) with
  | none => rw [hf] at h; exact absurd h (by simp)
  | some j =>
    rw [hf] at h
    have hm : (fun i => s.B i j) = m := by simpa using h
    have hy0 : s.y j = 0 := by
      have hd := List.find?_some hf
      simpa using hd
    subst hm
    constructor
    · intro hc
      have hcol : ∀ i, s.B i j = 0 := fun i => congrFun hc i
      have h1 : (s.Binv * s.B) j j = (1 : Matrix (Fin n) (Fin n) ℤ) j j := by
        rw [hBr]
      rw [Matrix.mul_apply] at h1
      simp [hcol] at h1
    · calc ∑ i, (((fun i => s.B i j) i : ℚ)) * x i
          = ∑ i, x i * (s.B i j : ℚ) :=
            Finset.sum_congr rfl fun i _ => mul_comm _ _
        _ = s.y j := (hy j).symm
        _ = 0 := hy0

/-- The relation `m` read in the algorithm's current basis: `z = Binv · m`,
so that `m = B · z`. An integer vector, by unimodularity; used to state the
lower bound of `PSLQ.Bound`. -/
def PSLQState.coords (s : PSLQState n) (m : Fin n → ℤ) : Fin n → ℤ :=
  s.Binv *ᵥ m

/-! ## Rational Gram–Schmidt data (the HJLS normalization) -/

/-- Column `j` of the current basis, over `ℚ`. -/
def PSLQState.col (s : PSLQState n) (j : Fin n) : Fin n → ℚ :=
  fun i => (s.B i j : ℚ)

/-- The projection of basis column `j` orthogonally to `x`, computed from
state data (under the invariant, `y j = ⟨x, b_j⟩`). Total thanks to the
division-by-zero convention (`_ / 0 = 0`); for `x ≠ 0` it is the genuine
orthogonal projection. All entries rational — this is the CSV/HJLS point. -/
def PSLQState.proj (x : Fin n → ℚ) (s : PSLQState n) (j : Fin n) :
    Fin n → ℚ :=
  s.col j - (s.y j / (x ⬝ᵥ x)) • x

/-- Gram–Schmidt orthogonalization over `ℚ` (division-by-zero convention: a
degenerate direction contributes nothing). Mirrors Mathlib's `gramSchmidt`,
which is unavailable over `ℚ` (it requires `RCLike`). -/
def gso (v : Fin n → Fin n → ℚ) (j : Fin n) : Fin n → ℚ :=
  v j - ∑ l : Finset.Iio j, ((v j ⬝ᵥ gso v l) / (gso v l ⬝ᵥ gso v l)) • gso v l
termination_by j
decreasing_by
  have hl : (l : Fin n) ∈ Finset.Iio j := l.2
  exact Fin.lt_def.mp (Finset.mem_Iio.mp hl)

/-- `gso` unfolding with a plain (unattached) sum. -/
theorem gso_def (v : Fin n → Fin n → ℚ) (j : Fin n) :
    gso v j = v j -
      ∑ l ∈ Finset.Iio j,
        ((v j ⬝ᵥ gso v l) / (gso v l ⬝ᵥ gso v l)) • gso v l := by
  rw [← Finset.sum_attach, Finset.attach_eq_univ, gso]

/-- The squared GSO norms of the projected basis: the state's rational
Gram–Schmidt data. `gsoNormSq x s j` is `‖b*_j‖²` for the projected basis. -/
def PSLQState.gsoNormSq (x : Fin n → ℚ) (s : PSLQState n) (j : Fin n) : ℚ :=
  gso (s.proj x) j ⬝ᵥ gso (s.proj x) j

/-! ## The PSLQ strategy (correctness-irrelevant, faithfulness-relevant) -/

/-- Size-reduction pairs `(l, j)`, `l < j`: columns `j` in increasing order,
each reduced against `l = j-1, …, 0` in decreasing order (Hermite
reduction order). -/
def sizeRedPairs (n : ℕ) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun j =>
    (((List.finRange n).filter fun l => l < j).reverse.map fun l => (l, j))

/-- One size-reduction op: reduce column `j` against `gso` direction `l`
using the nearest-integer multiplier, recomputed from the current state. -/
def sizeRedOp (x : Fin n → ℚ) (l j : Fin n) (s : PSLQState n) : ElemOp n :=
  let P := s.proj x
  let g := gso P l
  .addMul (-round ((P j ⬝ᵥ g) / (g ⬝ᵥ g))) l j

/-- The PSLQ swap choice: swap `r, r+1` for `r` maximizing the γ-weighted
squared diagonal `(γ²)^r · ‖b*_r‖²` with `γ² = 2` (any `γ² > 4/3` is a
valid PSLQ weighting; squares keep everything in `ℚ`). -/
def swapOp (x : Fin n → ℚ) (hn : 2 ≤ n) (s : PSLQState n) : ElemOp n :=
  let cands : List (Fin n × Fin n) :=
    (List.finRange n).filterMap fun r : Fin n =>
      if h : (r : ℕ) + 1 < n then some (r, (⟨(r : ℕ) + 1, h⟩ : Fin n)) else none
  match cands.argmax fun p => (2 : ℚ) ^ (p.1 : ℕ) * s.gsoNormSq x p.1 with
  | some p => .swap p.1 p.2
  | none => .addMul 0 ⟨0, by omega⟩ ⟨0, by omega⟩  -- unreachable for n ≥ 2

/-- One PSLQ round: a full size-reduction pass, then the weighted swap. -/
def roundProgram (x : Fin n → ℚ) : List (PSLQState n → ElemOp n) :=
  ((sizeRedPairs n).map fun lj => sizeRedOp x lj.1 lj.2) ++
    (if h : 2 ≤ n then [swapOp x h] else [])

/-- One round of the algorithm. -/
def pslqRound (x : Fin n → ℚ) (s : PSLQState n) : PSLQState n :=
  applyProgram s (roundProgram x)

theorem pslqRound_inv (x : Fin n → ℚ) (s : PSLQState n) (h : s.Inv x) :
    (pslqRound x s).Inv x :=
  applyProgram_inv x _ s h

/-! ## The driver -/

/-- The state after `k` rounds on input `x`. -/
def pslqState (x : Fin n → ℚ) : ℕ → PSLQState n
  | 0 => .init x
  | k + 1 => pslqRound x (pslqState x k)

theorem pslqState_inv (x : Fin n → ℚ) (k : ℕ) : (pslqState x k).Inv x := by
  induction k with
  | zero => exact PSLQState.init_inv x
  | succ k ih => exact pslqRound_inv x _ ih

/-- Fuel-based driver from a given state. -/
def pslqAux (x : Fin n → ℚ) : ℕ → PSLQState n → Option (Fin n → ℤ)
  | 0, s => s.report?
  | fuel + 1, s =>
    match s.report? with
    | some m => some m
    | none => pslqAux x fuel (pslqRound x s)

/-- **The exact-arithmetic PSLQ-class detector.** Runs at most `fuel`
strategy rounds on the exact rational input `x`; reports the first exact
zero of `y` as a candidate relation (a column of the unimodular `B`). -/
def pslq (x : Fin n → ℚ) (fuel : ℕ) : Option (Fin n → ℤ) :=
  pslqAux x fuel (.init x)

/-- Partial correctness of the driver from any invariant state. -/
theorem pslqAux_partial_correct (x : Fin n → ℚ) (fuel : ℕ)
    (s : PSLQState n) (hs : s.Inv x) {m : Fin n → ℤ}
    (h : pslqAux x fuel s = some m) : IsIntRelation x m := by
  induction fuel generalizing s with
  | zero => exact PSLQState.report?_spec hs h
  | succ fuel ih =>
    rw [pslqAux] at h
    cases hr : s.report? with
    | some m' =>
      rw [hr] at h
      cases h
      exact PSLQState.report?_spec hs hr
    | none =>
      rw [hr] at h
      exact ih _ (pslqRound_inv x s hs) h

/-- **PSLQ partial correctness.** If the exact-arithmetic core, run on exact
rational input `x`, reports `m`, then `m` is an integer relation of `x`. -/
theorem pslq_partial_correct (x : Fin n → ℚ) (fuel : ℕ) (m : Fin n → ℤ)
    (h : pslq x fuel = some m) : IsIntRelation x m :=
  pslqAux_partial_correct x fuel _ (PSLQState.init_inv x) h

/-! ## Executable certificate checker (checkPDq_sound schema, see DEPS.md) -/

/-- `IsIntRelation` over `ℚ` is decidable: both conjuncts are decidable
equalities in a finite-dimensional rational setting. This is what makes the
Bool certificate checker below executable. -/
instance instDecidableIsIntRelation (xq : Fin n → ℚ) (m : Fin n → ℤ) :
    Decidable (IsIntRelation xq m) :=
  decidable_of_iff (m ≠ 0 ∧ ∑ i, (m i : ℚ) * xq i = 0) Iff.rfl

/-- Decidable Bool certificate checker for a claimed integer relation. -/
def checkRelation (xq : Fin n → ℚ) (m : Fin n → ℤ) : Bool :=
  decide (IsIntRelation xq m)

/-- Soundness of the executable checker (the `checkPDq_sound` shape). -/
theorem checkRelation_sound {xq : Fin n → ℚ} {m : Fin n → ℤ}
    (h : checkRelation xq m = true) : IsIntRelation xq m :=
  of_decide_eq_true h

/-- Completeness of the executable checker: the Bool check is exactly
`IsIntRelation` (the `checkPDq` schema's two-sided form). -/
theorem checkRelation_iff {xq : Fin n → ℚ} {m : Fin n → ℤ} :
    checkRelation xq m = true ↔ IsIntRelation xq m :=
  decide_eq_true_iff

/-- The detector's output always passes the certificate checker. -/
theorem pslq_checkRelation (x : Fin n → ℚ) (fuel : ℕ) (m : Fin n → ℤ)
    (h : pslq x fuel = some m) : checkRelation x m = true :=
  checkRelation_iff.mpr (pslq_partial_correct x fuel m h)

end DiscoveryKernels.R1
