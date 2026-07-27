/-
Copyright (c) 2026 discovery-kernels contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.

# R3 — the OPERATOR LIFT of the conditioning tier: a `B`-valued distance to
# the ill-posed set, and the collapse test.

STEERING-02 reframe. The finite-dimensional first step is done here, in the
algebraic (exact, no `Float`, no analysis) setting: `A = Mₙ(B)` over a
star-ordered ring `B`, ill-posed set `Σ = {y : ¬ IsUnit y}`.

References:
* J. Demmel, *On condition numbers and the distance to the nearest ill-posed
  problem*, Numer. Math. 51 (1987) 251–289 — κ(x) = ‖x‖ / dist(x, Σ).
* P. Bürgisser, F. Cucker, *Condition: The Geometry of Numerical
  Algorithms*, Springer 2013 — the condition-number/distance framework.
* C. Eckart, G. Young (1936) — the rank-one perturbation identity behind the
  distance-to-singularity computation.
* R. V. Kadison, *Order properties of bounded self-adjoint operators*, Proc.
  AMS 2 (1951) 505–510 — the ANTI-LATTICE theorem: in a factor, `sup{a,b}`
  (hence `inf{a,b}`) exists only for comparable `a, b`. This is the
  obstruction that makes `dist_B` a SET of certificates rather than an
  element of `B`; see `infima_of_bvaluedDistance_diagonal` below.
* Y. Watatani, *Index for C*-subalgebras*, Mem. AMS 83 (1990) — the nearest
  genuinely algebra-valued neighbour in the literature (Conditioning/SWEEP.md,
  S2); adjacent in flavour, unrelated in purpose.
* Componentwise/structured condition numbers (Skeel; Rohn; Higham; the
  structured literature catalogued in Conditioning/SWEEP.md S2) — the honest
  comparison class for the ABELIAN case, where our object collapses into
  known art. Flagged as a collapse in OV/CHALLENGE-R3.proposed.md.

Everything in this file is PROVED (no `sorry`); the proposed headline
statements built on it live in OV/CHALLENGE-R3.proposed.lean.
-/
import Mathlib

namespace DiscoveryKernels.R3

open Matrix

/-! ## The `B`-valued forms -/

section Forms

variable (B : Type*) [Ring B] [StarRing B] [PartialOrder B]

/-- `B`-valued inner product on the free right `B`-module `Bⁿ`,
`⟨ξ, η⟩ = ∑ᵢ (ξᵢ)* ηᵢ`. The Hilbert C*-module form (Paschke; Lance,
*Hilbert C*-modules*) written algebraically: no completeness, no norm. -/
def ovInner {n : ℕ} (ξ η : Fin n → B) : B := ∑ i, star (ξ i) * η i

/-- The `b`-weighted Rayleigh form `⟨ξ, b ξ⟩ = ∑ᵢ (ξᵢ)* b ξᵢ`. `b` plays the
role of a *`B`-valued squared margin*: in the scalar case `B = ℝ`, `b = t`
gives `t‖ξ‖²`. -/
def ovRayleigh {n : ℕ} (b : B) (ξ : Fin n → B) : B := ∑ i, star (ξ i) * b * ξ i

/-- **The ill-posed set `Σ`** for the linear-solve problem over `B`: the
non-invertible matrices. In the scalar case this is `{det = 0}`, the classical
`Σ` of Demmel (1987). -/
def IsIllPosed {n : ℕ} (y : Matrix (Fin n) (Fin n) B) : Prop := ¬ IsUnit y

/-- **`b` is a certified `B`-valued margin for `x`.** `b ≥ 0` and
`⟨ξ, b ξ⟩ ≤ ⟨xξ, xξ⟩` for every `ξ ∈ Bⁿ`: the `B`-valued lower Rayleigh
bound, i.e. the operator-valued analogue of `σ_min(x)² ≥ b`. Simplification
flags: left/right module conventions fixed as above; no norm or completeness;
`B` an abstract star-ordered ring, not a C*- or von Neumann algebra. -/
def IsMargin {n : ℕ} (x : Matrix (Fin n) (Fin n) B) (b : B) : Prop :=
  0 ≤ b ∧ ∀ ξ : Fin n → B, ovRayleigh B b ξ ≤ ovInner B (x *ᵥ ξ) (x *ᵥ ξ)

/-- **`dist_B(x, Σ)` — the `B`-valued distance object.** It is the SET of
certified margins, not an element of `B`. That this is the honest form, and
not a stylistic choice, is the content of
`infima_of_bvaluedDistance_diagonal` below together with Kadison's
anti-lattice theorem: for noncommutative `B` a greatest margin need not
exist, so no `B`-VALUED NUMBER can represent the distance. The set is
downward closed in the positive cone and plays the role of
`{t : t ≤ dist(x, Σ)²}` in Demmel's scalar theory. -/
def distB {n : ℕ} (x : Matrix (Fin n) (Fin n) B) : Set B := {b | IsMargin B x b}

/-- `b` IS the `B`-valued distance of `x` to `Σ` (squared), when a greatest
certified margin exists: `IsGreatest (distB x) b`. Existence is exactly what
Kadison's anti-lattice theorem puts in doubt for noncommutative `B`. -/
def IsBValuedDistance {n : ℕ} (x : Matrix (Fin n) (Fin n) B) (b : B) : Prop :=
  IsGreatest (distB B x) b

/-- **The distance certificate**: every ill-posed `y` is at least `b` away
from `x`, measured on `y`'s kernel in the `B`-valued Rayleigh form. This is
the "distance to `Σ`" side of the Condition Number Theorem; the bound is
COMPRESSED to the kernel of `y` (a corner of `B`), which is forced — the
uncompressed, global form provably collapses to `0`, see
`globalInf_collapses`. -/
def IsDistanceCertificate {n : ℕ} (x : Matrix (Fin n) (Fin n) B) (b : B) : Prop :=
  0 ≤ b ∧ ∀ y : Matrix (Fin n) (Fin n) B, IsIllPosed B y → ∀ ξ : Fin n → B,
    y *ᵥ ξ = 0 → ovRayleigh B b ξ ≤ ovInner B ((x - y) *ᵥ ξ) ((x - y) *ᵥ ξ)

/-- **The NAIVE `B`-valued distance (definition D1), kept only to be
refuted**: a global infimum over `Σ` of the conditioned squared perturbation
`E (δ* δ)`. This is the first definition anyone writes for "distance to `Σ`
measured in `E_B`"; `globalInf_collapses` proves it is identically `0` even
for a perfectly conditioned `x` and even when `E` is the identity — the
named failure mode, run and reported. -/
def IsGlobalInfMargin {A : Type*} [Ring A] [StarRing A] (E : A → B) (x : A) (b : B) :
    Prop :=
  0 ≤ b ∧ ∀ y : A, ¬ IsUnit y → b ≤ E (star (x - y) * (x - y))

end Forms

/-! ## Elementary computations -/

section Basic

variable {B : Type*} [Ring B] [StarRing B] [PartialOrder B]

@[simp] lemma ovInner_zero {n : ℕ} : ovInner B (0 : Fin n → B) 0 = 0 := by
  simp [ovInner]

lemma ovRayleigh_single {n : ℕ} [NeZero n] (b : B) (i : Fin n) :
    ovRayleigh B b (Pi.single i (1 : B)) = b := by
  classical
  rw [ovRayleigh, Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [Pi.single_apply, hj]
  · simp

lemma ovInner_single {n : ℕ} (i : Fin n) (c d : B) :
    ovInner B (Pi.single i c) (Pi.single i d) = star c * d := by
  classical
  rw [ovInner, Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [Pi.single_apply, hj]
  · simp

end Basic

/-! ## The Condition Number Theorem, `B`-valued: margin ⇒ distance -/

section CNT

variable {B : Type*} [Ring B] [StarRing B] [PartialOrder B]

/-- **Half of the `B`-valued Condition Number Theorem (proved).** A certified
`B`-valued margin for `x` is a certified distance from `x` to the ill-posed
set `Σ`: on the kernel of any ill-posed `y`, the perturbation `x - y` is at
least `b` in the `B`-valued Rayleigh form. (Demmel 1987, the easy inequality
`dist(x, Σ) ≥ 1/‖x⁻¹‖`, lifted to `B`.) -/
theorem margin_imp_distanceCertificate {n : ℕ} (x : Matrix (Fin n) (Fin n) B) (b : B)
    (h : IsMargin B x b) : IsDistanceCertificate B x b := by
  refine ⟨h.1, fun y _ ξ hξ => ?_⟩
  have hxy : (x - y) *ᵥ ξ = x *ᵥ ξ := by
    rw [Matrix.sub_mulVec, hξ, sub_zero]
  rw [hxy]
  exact h.2 ξ

/-- **Certified margin ⇒ certified solve (proved).** If `b` is a certified
`B`-valued margin for an invertible `x`, then the solve operator `x⁻¹` is
bounded in the `B`-valued Rayleigh form by `b`: `⟨x⁻¹η, b x⁻¹η⟩ ≤ ⟨η, η⟩`.
This is the operator-valued form of the licensing half of the Condition
Number Theorem, `‖x⁻¹‖ ≤ 1/dist(x, Σ)` (Demmel 1987): a certified margin
bounds the error amplification of the computation. NOTE (reported honestly in
OV/CHALLENGE-R3.proposed.md): the argument is the scalar one verbatim —
the mathematical weight of the `B`-valued theory sits in the DEFINITION of
the margin, not in this inequality. -/
theorem margin_imp_inverse_bound {n : ℕ} (u : (Matrix (Fin n) (Fin n) B)ˣ) (b : B)
    (h : IsMargin B (u : Matrix (Fin n) (Fin n) B) b) (η : Fin n → B) :
    ovRayleigh B b ((↑u⁻¹ : Matrix (Fin n) (Fin n) B) *ᵥ η) ≤ ovInner B η η := by
  have hb := h.2 ((↑u⁻¹ : Matrix (Fin n) (Fin n) B) *ᵥ η)
  rwa [Matrix.mulVec_mulVec, u.mul_inv, Matrix.one_mulVec] at hb

end CNT

/-! ## The decisive structural reduction: diagonal `x` -/

section Diagonal

variable {B : Type*} [Ring B] [StarRing B] [PartialOrder B] [StarOrderedRing B]

/-- **Margin set of a diagonal matrix.** For `x = diagonal d`, `b` is a
certified `B`-valued margin exactly when `b` is a positive common lower bound
of the entrywise squared moduli `(dᵢ)* dᵢ`. This is the operator-valued
version of `σ_min(diag(d))² = minᵢ |dᵢ|²`, with `min` replaced by "common
lower bound" — and it is the bridge to the anti-lattice obstruction. -/
theorem isMargin_diagonal_iff {n : ℕ} (d : Fin n → B) (b : B) :
    IsMargin B (Matrix.diagonal d) b ↔ 0 ≤ b ∧ ∀ i, b ≤ star (d i) * d i := by
  classical
  constructor
  · rintro ⟨hb, h⟩
    refine ⟨hb, fun i => ?_⟩
    have := h (Pi.single i (1 : B))
    have hmul : (Matrix.diagonal d) *ᵥ (Pi.single i (1 : B)) = Pi.single i (d i) := by
      ext j
      rcases eq_or_ne j i with rfl | hj
      · simp [Matrix.mulVec_diagonal]
      · simp [Matrix.mulVec_diagonal, Pi.single_apply, hj]
    rw [hmul, ovInner_single] at this
    have hR : ovRayleigh B b (Pi.single i (1 : B)) = b := by
      rw [ovRayleigh, Finset.sum_eq_single i]
      · simp
      · intro j _ hj; simp [Pi.single_apply, hj]
      · simp
    rwa [hR] at this
  · rintro ⟨hb, h⟩
    refine ⟨hb, fun ξ => ?_⟩
    have : ∀ i : Fin n, star (ξ i) * b * ξ i
        ≤ star ((Matrix.diagonal d *ᵥ ξ) i) * ((Matrix.diagonal d *ᵥ ξ) i) := by
      intro i
      have := star_left_conjugate_le_conjugate (h i) (ξ i)
      simpa [Matrix.mulVec_diagonal, star_mul, mul_assoc] using this
    calc ovRayleigh B b ξ = ∑ i, star (ξ i) * b * ξ i := rfl
      _ ≤ ∑ i, star ((Matrix.diagonal d *ᵥ ξ) i) * ((Matrix.diagonal d *ᵥ ξ) i) :=
          Finset.sum_le_sum fun i _ => this i
      _ = ovInner B (Matrix.diagonal d *ᵥ ξ) (Matrix.diagonal d *ᵥ ξ) := rfl

/-- The `B`-valued distance SET of a diagonal matrix is exactly the set of
positive common lower bounds of the `(dᵢ)* dᵢ`. -/
theorem distB_diagonal {n : ℕ} (d : Fin n → B) :
    distB B (Matrix.diagonal d) = {b : B | 0 ≤ b ∧ ∀ i, b ≤ star (d i) * d i} := by
  ext b; exact isMargin_diagonal_iff d b

/-- **THE OBSTRUCTION (proved).** If every `2 × 2` diagonal matrix over `B`
has a `B`-VALUED distance — i.e. a greatest certified margin, an element of
`B` — then every pair of positive elements of the form `(dᵢ)* dᵢ` has a
greatest common lower bound in the positive cone of `B`.

Contrapositive, which is the operative statement: in any `B` whose positive
cone is not an inf-semilattice, `dist_B(·, Σ)` is NOT representable by an
element of `B`. By Kadison's anti-lattice theorem (1951) this covers every
factor — in particular `Mₚ(ℂ)` for `p ≥ 2` and every `II₁` factor, i.e.
exactly the algebras the MSY/free-probability setting cares about. A
hand-verified explicit witness in `M₂` (`a₁ = diag(2,1)`,
`a₂ = [[3/2,1/2],[1/2,3/2]]`, incomparable lower bounds `1` and
`diag(21/20, 9/10)`) is recorded in OV/CHALLENGE-R3.proposed.md. -/
theorem infima_of_bvaluedDistance_diagonal
    (h : ∀ d : Fin 2 → B, ∃ b, IsBValuedDistance B (Matrix.diagonal d) b)
    (d₁ d₂ : B) :
    ∃ b : B, IsGreatest {c : B | 0 ≤ c ∧ c ≤ star d₁ * d₁ ∧ c ≤ star d₂ * d₂} b := by
  obtain ⟨b, hb⟩ := h ![d₁, d₂]
  refine ⟨b, ?_, ?_⟩
  · have := hb.1
    rw [distB, Set.mem_setOf_eq, isMargin_diagonal_iff] at this
    exact ⟨this.1, by simpa using this.2 0, by simpa using this.2 1⟩
  · rintro c ⟨hc0, hc1, hc2⟩
    refine hb.2 ?_
    rw [distB, Set.mem_setOf_eq, isMargin_diagonal_iff]
    refine ⟨hc0, fun i => ?_⟩
    fin_cases i
    · simpa using hc1
    · simpa using hc2

/-- **Contrapositive of the obstruction (proved): `dist_B` is not
element-valued.** If some pair of positive elements of `B` has no greatest
common lower bound in the positive cone — which is the generic situation in a
noncommutative `B` by Kadison's anti-lattice theorem — then there is a
`2 × 2` matrix over `B` with NO `B`-valued distance to `Σ` at all. The
`B`-valued condition number of an operator-valued problem is therefore a
CERTIFICATE SET (`distB`), not an element of `B`. -/
theorem bvaluedDistance_fails_of_no_infimum
    (h : ∃ d₁ d₂ : B,
      ¬ ∃ b : B, IsGreatest {c : B | 0 ≤ c ∧ c ≤ star d₁ * d₁ ∧ c ≤ star d₂ * d₂} b) :
    ∃ x : Matrix (Fin 2) (Fin 2) B, ∀ b : B, ¬ IsBValuedDistance B x b := by
  obtain ⟨d₁, d₂, hno⟩ := h
  by_contra hcon
  push_neg at hcon
  refine hno (infima_of_bvaluedDistance_diagonal (fun d => ?_) d₁ d₂)
  obtain ⟨b, hb⟩ := hcon (Matrix.diagonal d)
  exact ⟨b, hb⟩

end Diagonal

/-! ## Collapse test 1: the naive global infimum (definition D1) is dead -/

section CollapseD1

/-- The two ill-posed elements used to kill D1: `(0, 2)` and `(1, 0)` are
non-units of `ℝ × ℝ`. -/
private lemma not_isUnit_prod_fst_zero (t : ℝ) : ¬ IsUnit ((0 : ℝ), t) := by
  rintro ⟨u, hu⟩
  have h := congrArg Prod.fst u.val_inv
  rw [hu] at h
  simp at h

private lemma not_isUnit_prod_snd_zero (t : ℝ) : ¬ IsUnit ((t : ℝ), (0 : ℝ)) := by
  rintro ⟨u, hu⟩
  have h := congrArg Prod.snd u.val_inv
  rw [hu] at h
  simp at h

/-- **COLLAPSE TEST 1, RUN — NEGATIVE RESULT (proved).** The naive
`B`-valued distance "`inf over Σ of E(δ*δ)`" collapses to `0`.

The instance is as favourable as possible to the definition: `B = ℝ × ℝ`
(commutative, a lattice, so infima are not obstructed), `A = B`, `E = id`
(NO information is lost by the conditional expectation), and
`x = (1, 2)` is invertible and perfectly conditioned (its scalar condition
number is `2`). Yet the only `b ≥ 0` below `E(δ*δ)` for every ill-posed `y`
is `b = 0`: the perturbation `(1,0)` reaches `Σ` cheaply in the first
coordinate and `(0,2)` reaches it cheaply in the second, and a global
infimum must be below both.

Reading: a `B`-valued distance to `Σ` CANNOT be defined by a global
infimum over `Σ`; the bound must be compressed to the corner of `B` where the
ill-posed direction lives (`IsDistanceCertificate`). Definition D1 is dead,
and this is a first-class deliverable, not a disappointment. -/
theorem globalInf_collapses (b : ℝ × ℝ)
    (h : IsGlobalInfMargin (ℝ × ℝ) (id : (ℝ × ℝ) → ℝ × ℝ) ((1, 2) : ℝ × ℝ) b) :
    b = 0 := by
  obtain ⟨hb0, hb⟩ := h
  have h1 := hb ((0, 2) : ℝ × ℝ) (not_isUnit_prod_fst_zero 2)
  have h2 := hb ((1, 0) : ℝ × ℝ) (not_isUnit_prod_snd_zero 1)
  simp only [id, Prod.mk_sub_mk, sub_zero, sub_self, star_trivial, Prod.mk_mul_mk,
    mul_zero, mul_one, one_mul, zero_mul] at h1 h2
  have hb1 : b.1 ≤ 0 := (Prod.le_def.mp h2).1
  have hb2 : b.2 ≤ 0 := (Prod.le_def.mp h1).2
  have h01 : (0 : ℝ) ≤ b.1 := (Prod.le_def.mp hb0).1
  have h02 : (0 : ℝ) ≤ b.2 := (Prod.le_def.mp hb0).2
  exact Prod.ext (le_antisymm hb1 h01) (le_antisymm hb2 h02)

end CollapseD1

/-! ## Collapse test 2: does the surviving object collapse to `λ_min`? -/

section CollapseD2

/-- The `1 × 1` matrix over `ℝ × ℝ` with entry `(1, 2)`: a perfectly
conditioned element whose two "fibres" have different margins. -/
def witnessX : Matrix (Fin 1) (Fin 1) (ℝ × ℝ) := Matrix.diagonal ![((1 : ℝ), (2 : ℝ))]

/-- The same with the fibres swapped: `(2, 1)`. It has the SAME scalar
condition data as `witnessX` (same norm, same `σ_min`, same `κ`). -/
def witnessX' : Matrix (Fin 1) (Fin 1) (ℝ × ℝ) := Matrix.diagonal ![((2 : ℝ), (1 : ℝ))]

/-- **COLLAPSE TEST 2, RUN — NO COLLAPSE (proved).** `dist_B` is not
`λ_min`, not a norm, and not any scalar-valued invariant.

`(1, 4)` is the `B`-valued distance of `witnessX` and `(4, 1)` that of
`witnessX'`; the two matrices are indistinguishable by every scalar condition
invariant (both have `‖x‖ = 2`, `σ_min = 1`, `κ = 2`), yet their `B`-valued
distances differ. Moreover the best SCALAR margin `(t, t)` for either is
`t ≤ 1 = λ_min`, strictly below the `B`-valued answer in one fibre: the
`B`-valued object strictly refines `λ_min`.

HONESTY FLAG (the second collapse condition of Conditioning/SWEEP.md S2):
for ABELIAN `B` such as this `ℝ × ℝ`, `dist_B` is exactly the fibrewise
scalar condition number, i.e. a COMPONENTWISE condition number — which is
mature, occupied literature (Skeel; Rohn; Higham; the structured/componentwise
corpus of SWEEP S2). So test 2 is passed only in the weak sense; the tier's
surviving novelty is confined to NONCOMMUTATIVE `B`, where by
`infima_of_bvaluedDistance_diagonal` the object is not even element-valued.
See OV/CHALLENGE-R3.proposed.md for the full verdict. -/
theorem bvaluedDistance_not_scalar :
    IsBValuedDistance (ℝ × ℝ) witnessX ((1 : ℝ), (4 : ℝ)) ∧
      IsBValuedDistance (ℝ × ℝ) witnessX' ((4 : ℝ), (1 : ℝ)) ∧
      (∀ t : ℝ, IsMargin (ℝ × ℝ) witnessX (t, t) → t ≤ 1) ∧
      (∀ t : ℝ, IsMargin (ℝ × ℝ) witnessX' (t, t) → t ≤ 1) := by
  have key : ∀ (u : ℝ × ℝ) (b : ℝ × ℝ),
      IsMargin (ℝ × ℝ) (Matrix.diagonal ![u]) b ↔ 0 ≤ b ∧ b ≤ u * u := by
    intro u b
    rw [isMargin_diagonal_iff]
    constructor
    · rintro ⟨h0, h⟩; exact ⟨h0, by simpa [star_trivial] using h 0⟩
    · rintro ⟨h0, h⟩
      refine ⟨h0, fun i => ?_⟩
      fin_cases i
      simpa [star_trivial] using h
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [distB, Set.mem_setOf_eq, witnessX, key]
    constructor
    · exact Prod.le_def.mpr ⟨by norm_num, by norm_num⟩
    · exact le_of_eq (by norm_num [Prod.ext_iff])
  · rintro b hb
    rw [distB, Set.mem_setOf_eq, witnessX, key] at hb
    exact le_of_le_of_eq hb.2 (by norm_num [Prod.ext_iff])
  · rw [distB, Set.mem_setOf_eq, witnessX', key]
    constructor
    · exact Prod.le_def.mpr ⟨by norm_num, by norm_num⟩
    · exact le_of_eq (by norm_num [Prod.ext_iff])
  · rintro b hb
    rw [distB, Set.mem_setOf_eq, witnessX', key] at hb
    exact le_of_le_of_eq hb.2 (by norm_num [Prod.ext_iff])
  · intro t ht
    rw [witnessX, key] at ht
    have := (Prod.le_def.mp ht.2).1
    simpa using this
  · intro t ht
    rw [witnessX', key] at ht
    have := (Prod.le_def.mp ht.2).2
    simpa using this

end CollapseD2

end DiscoveryKernels.R3
