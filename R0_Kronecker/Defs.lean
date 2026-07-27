/-
Copyright (c) 2026 discovery-kernels contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.

R0 — definitions for the scalar license (Kronecker 1881).

References:
* L. Kronecker, "Zur Theorie der Elimination einer Variabeln aus zwei
  algebraischen Gleichungen", Monatsber. Königl. Preuss. Akad. Wiss. (1881).
* V. V. Peller, "Hankel Operators and Their Applications", Springer 2003,
  Chapter 1 (Kronecker's theorem).
-/
import Mathlib

namespace DiscoveryKernels.R0

variable (K : Type*) [Field K]

/-- The (infinite) Hankel matrix of a sequence `a : ℕ → K`: entry `(i, j)` is
`a (i + j)`. -/
def hankelMatrix (a : ℕ → K) : Matrix ℕ ℕ K :=
  Matrix.of fun i j => a (i + j)

/-- The `i`-th shift of a sequence: `shiftSeq a i = fun j => a (i + j)`.
This is exactly the `i`-th row of the Hankel matrix of `a`. -/
def shiftSeq (a : ℕ → K) (i : ℕ) : ℕ → K := fun j => a (i + j)

omit [Field K] in
theorem hankelMatrix_row (a : ℕ → K) (i : ℕ) :
    hankelMatrix K a i = shiftSeq K a i := rfl

/-- The row space of the infinite Hankel matrix of `a`: the span, inside the
function space `ℕ → K`, of all shifts of `a`. Its dimension is the rank of the
infinite Hankel matrix. -/
def hankelRowSpace (a : ℕ → K) : Submodule K (ℕ → K) :=
  Submodule.span K (Set.range (shiftSeq K a))

/-- `a` has finite Hankel rank: the row space of its (infinite) Hankel matrix is
a finite-dimensional subspace of `ℕ → K`. -/
def HasFiniteHankelRank (a : ℕ → K) : Prop :=
  Module.Finite K (hankelRowSpace K a)

/-- The generating function `∑ aₙ Xⁿ` of `a` is a rational function: there are
polynomials `p, q` with `q(0) ≠ 0` and `q · (∑ aₙ Xⁿ) = p` in `K⟦X⟧`.
(`q(0) ≠ 0` makes `q` a unit of `K⟦X⟧`, so this says `∑ aₙ Xⁿ = p / q`.) -/
def IsRationalGF (a : ℕ → K) : Prop :=
  ∃ p q : Polynomial K, q.coeff 0 ≠ 0 ∧
    (q : PowerSeries K) * PowerSeries.mk a = (p : PowerSeries K)

/-- `a` is **finitely atomic** (exponential-polynomial normal form): apart from a
finitely supported transient `b`, it is a finite sum of polynomially weighted
geometric modes with nonzero atoms `l`:

`a n = b n + ∑ l ∈ s, (c l).eval n * l ^ n`.

This is the partial-fractions normal form of a rational generating function
(atoms = inverse poles, polynomial weights = pole multiplicities); in the
classical moment-problem reading, the atoms are the support points of a finitely
atomic (signed, with multiplicity) spectral distribution. See Peller, Ch. 1. -/
def IsFinitelyAtomic (a : ℕ → K) : Prop :=
  ∃ (b : ℕ →₀ K) (s : Finset K) (c : K → Polynomial K),
    (0 : K) ∉ s ∧ ∀ n : ℕ, a n = b n + ∑ l ∈ s, (c l).eval (n : K) * l ^ n

end DiscoveryKernels.R0
