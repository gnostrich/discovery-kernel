/-
Copyright (c) 2026 discovery-kernels contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.

R3 — refined definitional layer for the operator-valued (OV) license and
OV completeness. STATEMENTS ONLY: nothing here is proved beyond what
elaboration forces; the headline theorems stay `sorry` by design.

This file EXTENDS `OV/Defs.lean` (FREEZE-0) without changing it: the
FREEZE-0 definitions keep their meaning so that the current Challenge.lean
R3 section is untouched; the refined headline statements (see
`OV/CHALLENGE-R3.proposed.lean`, PENDING HUMAN REVIEW) are stated against
the definitions below.

References:
* T. Mai, R. Speicher, S. Yin — rationality of operator-valued
  resolvents/Cauchy transforms and atomicity of the `E_B`-conditioned
  spectral distribution in amalgamated free probability (the "MSY-shaped"
  OV license).
* M.-P. Schützenberger (1961), M. Fliess (1974, "Matrices de Hankel"),
  J. Berstel, C. Reutenauer, *Noncommutative Rational Series with
  Applications* — recognizable series, finite linear realizations, and the
  stable-finitely-generated-submodule characterization of finite Hankel rank.
* Free Ax–Schanuel line (Ax 1971; Bays–Kirby; in the free-probability
  reading: Mai–Speicher–Weber, absence of algebraic relations under
  regularity hypotheses) — "every genuine alignment has a structural cause".

Every definition names the informal object and flags its simplifications.
Human-review flag: R3 statements require operator review before merge; see
OV/TIER-STATUS.md.
-/
import Mathlib
import OV.Defs

namespace DiscoveryKernels.R3

/-! ## Shift-stable modules and the corrected OV Hankel rank -/

section HankelRank

variable (B : Type*) [Ring B]

/-- The one-step shift `f ↦ f (· + 1)` on `B`-valued sequences — the
backward-shift operator on the (row space of the) `B`-valued Hankel matrix
`(M (i+j))_{i,j}`; equivalently, multiplication by the variable on the
associated series. Left `B`-linear. Cf. Fliess (1974); Kronecker (1881) for
the scalar case. -/
def shiftSeq (f : ℕ → B) : ℕ → B := fun n => f (n + 1)

/-- A submodule of `B`-valued sequences is *shift-stable* if it is carried
into itself by `shiftSeq`. This is the "stable submodule" of the theory of
recognizable series (Fliess 1974; Berstel–Reutenauer, Ch. 2), specialized to
one variable. Simplification flag: LEFT `B`-module structure only; the
`B`-bimodule structure of the amalgamated (MSY) setting is not modelled. -/
def IsShiftStable (W : Submodule B (ℕ → B)) : Prop :=
  ∀ f ∈ W, shiftSeq B f ∈ W

/-- **Corrected OV finite Hankel rank** (refines FREEZE-0
`HasFiniteOVHankelRank`): `M` lies in some finitely generated shift-stable
left `B`-submodule of `ℕ → B`. Informally: the row module of the `B`-valued
Hankel matrix of `M` is contained in a finitely generated stable module —
Fliess's characterization of recognizable (rational) series over a
noncommutative coefficient ring.

Why not FREEZE-0's "the span of the shifts of `M` is finitely generated"?
Because a finite linear realization only places the shift span INSIDE a
finitely generated stable module; over a non-Noetherian `B` the span itself
has no license to be finitely generated. The two versions agree whenever `B`
is left-Noetherian, and for the containment version the equivalence with
finite realizations is theorem-shaped over EVERY ring (Fliess/Schützenberger),
which is what the license headline needs. Simplification flags: left modules
(not bimodules); no positivity; sequence-indexed (one variable) rather than
word-indexed. -/
def HasFiniteOVHankelRankStable (M : ℕ → B) : Prop :=
  ∃ W : Submodule B (ℕ → B), W.FG ∧ IsShiftStable B W ∧ M ∈ W

end HankelRank

/-! ## Positivity layer: OV moment sequences and star-atomicity -/

section Positivity

variable (B : Type*) [Ring B] [StarRing B] [PartialOrder B]

/-- The `B`-valued Hankel kernel of `M` is positive semidefinite: every
finite section `(M (i+j))_{i,j<k}` is a positive `B`-valued form,
`0 ≤ ∑ i j, star (b i) * M (i+j) * b j`. This is the operator-valued
Hamburger moment condition — the algebraic shadow of "`M n = E_B (xⁿ)` for a
self-adjoint `x` conditioned by a positive `E_B`" (Mai–Speicher–Yin setting).
Positivity is meaningful under `[StarOrderedRing B]`, which the headline
assumes. Simplification flags: level-1 positivity only — COMPLETE positivity
(all matrix amplifications), automatic in the analytic setting, is NOT
required here; no normality/continuity; `B` is an abstract star-ordered ring,
not a von Neumann algebra. -/
def OVHankelPSD (M : ℕ → B) : Prop :=
  ∀ (k : ℕ) (b : Fin k → B),
    0 ≤ ∑ i : Fin k, ∑ j : Fin k, star (b i) * M (i.val + j.val) * b j

/-- `M` is an *operator-valued moment sequence*: hermitian entries plus a
positive semidefinite `B`-valued Hankel kernel. This is the definitional
surrogate for "`M` is the moment sequence of the `E_B`-conditioned spectral
measure `μ = E_B ∘ E_x` of a self-adjoint `x`" (MSY); no measure, spectral
theorem, or conditional expectation is constructed (Mathlib has none of the
three in operator-algebraic form — see OV/VOCAB.md). Simplification flags:
as in `OVHankelPSD`; determinacy/boundedness of the underlying measure is not
encoded. -/
def IsOVMomentSequence (M : ℕ → B) : Prop :=
  (∀ n, star (M n) = M n) ∧ OVHankelPSD B M

/-- `M` is *finitely atomic in the star sense*: `M n = ∑ i, star (w i) *
(a i)ⁿ * w i` with finitely many SELF-ADJOINT atoms `a i ∈ B` and weights in
the manifestly positive sandwich form `star (w i) * · * w i`. Informal
object: the moment sequence of a finitely atomic positive `B`-valued measure
`∑ i (star (w i) · w i)-weighted δ_{a i}` — the atomic `E_B`-conditioned
distribution of MSY. Simplification flags: atoms are taken IN `B` (in the
analytic setting they are spectral data of an operator affiliated with the
ambient algebra; `x ∈ B` itself is the honest base case, with `δ_x` its
distribution); weights `star w * w` rather than arbitrary positive elements
(equivalent in a C*-algebra, an abstraction here); atom/weight
compatibility (`w i` commuting with `a i`, weights summing to `M 0`) is not
imposed beyond what the moment formula forces. -/
def IsFinitelyAtomicOVStar (M : ℕ → B) : Prop :=
  ∃ (k : ℕ) (a w : Fin k → B),
    (∀ i, star (a i) = a i) ∧ ∀ n, M n = ∑ i, star (w i) * (a i) ^ n * w i

end Positivity

/-! ## Multivariate layer: OV alignment and structural cause -/

section Completeness

variable {A : Type*} [Ring A] [Algebra ℂ A]
variable {B : Type*} [AddCommGroup B] [Module ℂ B]

/-- The noncommutative monomial attached to a word: the multiplicative
embedding `FreeMonoid (Fin d) →* FreeAlgebra ℂ (Fin d)` sending a word to the
corresponding product of generators. Its image is the monomial basis of the
free algebra (`FreeAlgebra.basisFreeMonoid`), so "nonzero coefficient vector
⇒ nonzero polynomial" is meaningful. Cf. Berstel–Reutenauer, Ch. 1. -/
def ncMonomial (d : ℕ) : FreeMonoid (Fin d) →* FreeAlgebra ℂ (Fin d) :=
  FreeMonoid.lift (FreeAlgebra.ι ℂ)

/-- *Operator-valued alignment at level `n`* of a tuple `x` under a
conditioning map `E : A →ₗ[ℂ] B`: some nonzero scalar coefficient vector `c`,
supported on words of length ≤ `n`, annihilates the word-indexed OV
moment/Hankel data `w' ↦ E (x_{w w'})` — i.e. the rows `{E (x_{w ·})}_{|w|≤n}`
of the multivariate `B`-valued Hankel kernel are linearly dependent, so its
rank drops below the generic (free) value `#{words of length ≤ n}`.
Informal object: a "genuine alignment" in the `E_B`-moment data of
`(x_1, …, x_d)` — the OV analogue of an unexpected rank drop in a discovery
kernel. Simplification flags: scalar (ℂ) coefficients, not `B`-coefficients
(the `B`-bimodule Hankel of the amalgamated setting is not modelled); `E` is
a bare ℂ-linear map — `B`-bimodularity, unitality, and complete positivity of
the analytic `E_B` are dropped, with faithfulness reinstated as an explicit
hypothesis of the headline; `B` needs no ring structure at all here. -/
def HasOVAlignment {d : ℕ} (E : A →ₗ[ℂ] B) (x : Fin d → A) (n : ℕ) : Prop :=
  ∃ c : FreeMonoid (Fin d) →₀ ℂ, c ≠ 0 ∧ (∀ w ∈ c.support, w.length ≤ n) ∧
    ∀ w' : FreeMonoid (Fin d),
      (c.sum fun w z => z • E (FreeMonoid.lift x (w * w'))) = 0

/-- *Structural cause at level `n`*: a nonzero noncommutative polynomial of
degree ≤ `n` (a nonzero element of the span of monomials of length ≤ `n` in
`FreeAlgebra ℂ (Fin d)` — genuinely nonzero by `FreeAlgebra.basisFreeMonoid`)
annihilates the tuple `x` under evaluation `FreeAlgebra.lift ℂ x`. Informal
object: an exact noncommutative algebraic relation among `x_1, …, x_d` — the
"structural cause" that free-Ax–Schanuel-type completeness demands for every
genuine alignment (cf. Ax 1971; Bays–Kirby; Mai–Speicher–Weber for the free
setting). -/
def HasPolyCause {d : ℕ} (x : Fin d → A) (n : ℕ) : Prop :=
  ∃ p : FreeAlgebra ℂ (Fin d), p ≠ 0 ∧
    p ∈ Submodule.span ℂ (⇑(ncMonomial d) '' {w : FreeMonoid (Fin d) | w.length ≤ n}) ∧
    FreeAlgebra.lift ℂ x p = 0

end Completeness

end DiscoveryKernels.R3
