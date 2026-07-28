/-
Copyright (c) 2026 discovery-kernels contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.

# Conditioning tier — definitional layer

The organizing identity of this tier is the **Condition Number Theorem**
(Demmel, *On condition numbers and the distance to the nearest ill-posed
problem*, Numer. Math. 51 (1987) 251–289; Bürgisser–Cucker, *Condition*,
Springer 2013):

    κ(x) = ‖x‖ / dist(x, Σ)

where `Σ` is the set of **ill-posed inputs** — those at which the answer is a
discontinuous function of the data. Conditioning is inverse distance to
ill-posedness, so a certified lower bound `dist(x, Σ) ≥ c > 0` is a **licence
for a finite-precision computation**: data known to accuracy better than `c`
determines the answer.

This file fixes the vocabulary. Everything is stated over `ℝ` with explicit
finite sums; **no `Float` occurs anywhere in this tier**, and no scoped norm
instance is used, so there is no silent-instance footgun (`Matrix`'s L2
operator norm lives under `scoped[Matrix.Norms.L2Operator]` and is *not*
Mathlib's default `Matrix` norm).

## Design note: why the elementary formulations

`SpecNormLe E b` says `‖E‖₂ ≤ b` and `SigmaMinGE A c` says `σ_min(A) ≥ c`,
both written out as elementary inequalities between finite sums of squares.
This is deliberate:

* it keeps every statement checkable by eye against the textbook definition;
* it avoids committing the tier to one of Mathlib's several (mostly scoped,
  mutually incompatible) matrix norm instances;
* the quantities are exactly the ones an exact-rational checker can bound.

`Bridge.lean` connects `SpecNormLe`/`SigmaMinGE` back to Mathlib's genuine
`EuclideanSpace` operator norm, so the elementary phrasing is *justified*, not
merely asserted.
-/
import Mathlib

open scoped BigOperators Matrix

namespace DiscoveryKernels.Cond

variable {n : ℕ}

/-- Squared Euclidean norm `‖v‖²` of a real vector, as an explicit finite sum. -/
def sqNorm (v : Fin n → ℝ) : ℝ := ∑ i, v i ^ 2

/-- The quadratic form `xᵀ M x`, as an explicit finite double sum. -/
def quadForm (M : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, x i * M i j * x j

/-- **Σ, the ill-posed set for matrix inversion**: the singular matrices.

At a singular matrix the answer to "invert this" is discontinuous in the data
(indeed undefined), and an arbitrarily small perturbation changes it; this is
the canonical instance of Demmel's `Σ`. Membership in `Σ` is equivalent to
having `0` as an eigenvalue, so for symmetric inputs this is the ill-posed set
of the symmetric eigenvalue problem as well.

Scope note, stated so nothing is overclaimed: `Σ` here is **all** singular
matrices, and `DistGE` below quantifies over **all** perturbations. Since the
symmetric-singular set is a subset of `Σ`, every lower bound on `dist(·, Σ)`
proved in this tier is a fortiori a lower bound on the distance to the
symmetric-singular set — which is the direction that licenses a computation.
That the two distances *coincide* for symmetric inputs is true but is **not
proved here and never used**. -/
def SigmaSing (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℝ) := {S | S.det = 0}

/-- `‖E‖₂ ≤ b`: the spectral (ℓ² operator) norm of `E` is at most `b`, written
elementarily. Note `SpecNormLe E b` is invariant under `b ↦ -b`, so every use
site must carry `0 ≤ b` — this is not decoration, it is what makes
`DistGE` a faithful rendering of a distance bound. -/
def SpecNormLe (E : Matrix (Fin n) (Fin n) ℝ) (b : ℝ) : Prop :=
  ∀ v : Fin n → ℝ, sqNorm (E *ᵥ v) ≤ b ^ 2 * sqNorm v

/-- `σ_min(A) ≥ c`: a certified floor on the smallest singular value of `A`,
i.e. `c‖v‖ ≤ ‖Av‖` for every `v`, written elementarily (squared, so no square
roots appear). -/
def SigmaMinGE (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) : Prop :=
  ∀ v : Fin n → ℝ, c ^ 2 * sqNorm v ≤ sqNorm (A *ᵥ v)

/-- **`dist(A, Σ) ≥ c`** — a certified distance to ill-posedness, in the
spectral norm: *no* perturbation of spectral norm strictly less than `c`
makes `A` singular.

The `∃`-free phrasing quantifies over a witness `b` for `‖E‖₂ ≤ b < c`, which
is equivalent to `‖E‖₂ < c` because `‖E‖₂` is the infimum of such `b`
(see `Bridge.lean`). The hypothesis `0 ≤ b` is **load-bearing**: without it
one could take `b` very negative and the statement would be false. -/
def DistGE (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) : Prop :=
  ∀ (E : Matrix (Fin n) (Fin n) ℝ) (b : ℝ), 0 ≤ b → b < c → SpecNormLe E b →
    A + E ∉ SigmaSing n

/-- `l` is a real eigenvalue of `A`. Self-contained (no `Module.End`
machinery) so that the margin theorems can be read off directly; `Bridge.lean`
connects this to Mathlib's `Matrix.IsHermitian.eigenvalues`. -/
def IsEigenvalue (A : Matrix (Fin n) (Fin n) ℝ) (l : ℝ) : Prop :=
  ∃ v : Fin n → ℝ, v ≠ 0 ∧ A *ᵥ v = l • v

/-! ### Elementary facts about `sqNorm` -/

theorem sqNorm_nonneg (v : Fin n → ℝ) : 0 ≤ sqNorm v :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem sqNorm_eq_zero_iff (v : Fin n → ℝ) : sqNorm v = 0 ↔ v = 0 := by
  constructor
  · intro h
    funext i
    have h1 : ∀ i ∈ Finset.univ, v i ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _).mp h
    simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (h1 i (Finset.mem_univ i))
  · rintro rfl; simp [sqNorm]

theorem sqNorm_pos {v : Fin n → ℝ} (hv : v ≠ 0) : 0 < sqNorm v :=
  lt_of_le_of_ne (sqNorm_nonneg v) (fun h => hv ((sqNorm_eq_zero_iff v).mp h.symm))

theorem sqNorm_smul (c : ℝ) (v : Fin n → ℝ) : sqNorm (c • v) = c ^ 2 * sqNorm v := by
  simp only [sqNorm, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]

theorem sqNorm_neg (v : Fin n → ℝ) : sqNorm (-v) = sqNorm v := by
  simp [sqNorm]

/-- The Gram identity `‖Av‖² = vᵀ(AᵀA)v`. This is the transport that turns
*any* Rayleigh-floor engine for symmetric matrices (Gershgorin below) into a
singular-value floor for an **arbitrary** square matrix. -/
theorem quadForm_gram (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    quadForm (Aᵀ * A) v = sqNorm (A *ᵥ v) := by
  have h1 : quadForm (Aᵀ * A) v = ∑ i, ∑ j, ∑ k, (v i * A k i) * (A k j * v j) := by
    simp only [quadForm, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => by ring
  have h2 : sqNorm (A *ᵥ v) = ∑ k, ∑ i, ∑ j, (v i * A k i) * (A k j * v j) := by
    simp only [sqNorm, Matrix.mulVec, dotProduct, sq, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => by ring
  have h3 : ∀ i : Fin n, ∑ j, ∑ k, (v i * A k i) * (A k j * v j)
      = ∑ k, ∑ j, (v i * A k i) * (A k j * v j) := fun _ => Finset.sum_comm
  rw [h1, h2]
  simp_rw [h3]
  exact Finset.sum_comm

end DiscoveryKernels.Cond
