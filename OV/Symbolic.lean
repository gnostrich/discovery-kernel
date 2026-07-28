/-
Copyright (c) 2026 discovery-kernels contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.

# OV — the SYMBOLIC (order-of-vanishing) form: a per-direction, operator-valued
# Łojasiewicz exponent.

STEERING-02a. This is the FALLBACK form of the tier; the PRIMARY form is the
metric one in `OV/Cond.lean` (`distB`, the `B`-valued distance to the
ill-posed set). The two are stated side by side in
`OV/CHALLENGE-R3.proposed.lean`.

The symbolic picture needs no metric. Its three ingredients, instantiated
here:

1. **Σ as a discriminant** — degeneracy is algebraic: `IsIllPosed`
   (non-invertibility of the fibre), no distance anywhere;
2. **perturbation as deformation** — the object is a POLYNOMIAL FAMILY
   `X : Mₙ(B[t])`, and one asks where in the family it degenerates
   (here: normalized so the degenerate fibre sits at `t = 0`);
3. **distance as order of vanishing** — an INTEGER (`ℕ∞`), the trailing
   degree of the direction datum, recorded PER DIRECTION rather than
   aggregated.

Order of vanishing is discrete and multi-component by nature, so
"which directions vanish to which order" is a tuple; the collapse test for
this form is whether that tuple is ever non-constant
(`exponentTuple_not_constant*` below: it is not — proved, twice, once with a
NONCOMMUTATIVE `B`).

References:
* S. Łojasiewicz (1959; *Ensembles semi-analytiques*, IHES 1965) — the
  inequality `|f(x)| ≥ c · dist(x, Σ)^α` and the order-of-vanishing proof of
  the one-variable case; `α` is the transversality constant playing the role
  that `1/dist` plays in the metric picture.
* E. Bierstone, P. Milman — resolution of singularities and Łojasiewicz
  exponents.
* K. Kurdyka (1998) — the Kurdyka–Łojasiewicz property.
* J. Demmel, Numer. Math. 51 (1987) 251–289, and P. Bürgisser, F. Cucker,
  *Condition*, Springer 2013 — the metric counterpart this form replaces.
* OCCUPANCY (OV/SWEEP.md, S3, binding): Łojasiewicz inequalities with
  explicit exponents for the SMALLEST SINGULAR VALUE FUNCTION of real
  polynomial matrices, including distance-function versions, are ALREADY
  PUBLISHED (arXiv 1604.02805; eigenvalue counterpart arXiv 1501.01419). We
  claim no novelty there. What was not found is (a) any noncommutative /
  algebra-valued Łojasiewicz inequality and (b) any per-direction exponent
  tuple — every published exponent is a single real number. Those two are
  the only claims this file makes.

BOUNDARY (STEERING-02a, not negotiable): both forms require the object to sit
in a parametrised family. A single `x ∈ Mₙ(B)` has no family, no
discriminant, and no order of vanishing — and no family is invented here to
make the machinery fit. See `OV/CHALLENGE-R3.proposed.md` §3c for where this
form does and does not apply.

Everything in this file is PROVED (no `sorry`).
-/
import Mathlib
import OV.Cond

namespace DiscoveryKernels.R3

open Matrix Polynomial

/-! ## The symbolic definitional layer -/

section Symbolic

variable (B : Type*) [Ring B] [StarRing B]

/-- The **direction datum** of a polynomial family `X : Mₙ(B[t])` in the
direction `ξ ∈ Bⁿ`: the vector of polynomials `t ↦ X(t) ξ`. This is the
"defining function" whose vanishing along the degenerate locus is measured;
`ξ` is a constant direction (the deformation lives entirely in `X`). -/
noncomputable def ovFamilyImage {n : ℕ} (X : Matrix (Fin n) (Fin n) (Polynomial B))
    (ξ : Fin n → B) : Fin n → Polynomial B :=
  X *ᵥ fun i => Polynomial.C (ξ i)

/-- **The operator-valued Łojasiewicz order in direction `ξ`**: the order of
vanishing at the degenerate parameter `t = 0` of the direction datum, i.e.
the trailing degree of `t ↦ X(t) ξ`, an element of `ℕ∞` (`⊤` when the
direction is annihilated identically along the family).

This is the discrete replacement for `dist(x, Σ)`: Łojasiewicz's
`|f| ≥ c · dist^α` computed along the family, where for a transversally
parametrised family the exponent `α` in direction `ξ` IS this integer
(curve-selection form of the Łojasiewicz exponent; Łojasiewicz 1959/1965,
Bierstone–Milman, Kurdyka 1998).

Simplification flags: (i) the degenerate parameter is normalized to `t = 0`
(translate first); (ii) the parameter is assumed transversal, so the order of
vanishing of the parameter-distance is `1` and the Łojasiewicz exponent
equals this order rather than a ratio of orders; (iii) one parameter only —
no multi-parameter (Bierstone–Milman) resolution; (iv) `ξ` ranges over
CONSTANT directions in `Bⁿ`, not over `B[t]`-directions. -/
noncomputable def ovVanishingOrder {n : ℕ} (X : Matrix (Fin n) (Fin n) (Polynomial B))
    (ξ : Fin n → B) : ℕ∞ :=
  Finset.univ.inf fun i => (ovFamilyImage B X ξ i).trailingDegree

/-- The fibre of the family at the degenerate parameter `t = 0`, obtained
coefficientwise (no `eval`, so no commutativity is used). -/
def familyFibreZero {n : ℕ} (X : Matrix (Fin n) (Fin n) (Polynomial B)) :
    Matrix (Fin n) (Fin n) B :=
  X.map fun p => p.coeff 0

/-- **The discriminant condition**: the fibre at the distinguished parameter
is ill-posed (non-invertible). Purely algebraic — this is `Σ` as a
discriminant, with no metric anywhere. -/
def IsDegenerateAtZero {n : ℕ} (X : Matrix (Fin n) (Fin n) (Polynomial B)) : Prop :=
  IsIllPosed B (familyFibreZero B X)

/-- The order-`j` coefficient vector of the direction datum: the `j`-th
"derivative" of the defining data in direction `ξ`. -/
noncomputable def ovDatumCoeff {n : ℕ} (X : Matrix (Fin n) (Fin n) (Polynomial B))
    (ξ : Fin n → B) (j : ℕ) : Fin n → B :=
  fun i => (ovFamilyImage B X ξ i).coeff j

/-- **The Łojasiewicz leading certificate at order `j`**:
`∑ᵢ (cᵢ)* cᵢ` for the order-`j` coefficient vector `c`. In the ordered
setting it is `≥ 0` always, and (under faithfulness of the positive cone) it
is `> 0` exactly at the vanishing order — it is the `B`-valued constant `c`
of `|f| ≥ c · dist^α`, recorded per direction. -/
noncomputable def ovLeadingCertificate {n : ℕ} (X : Matrix (Fin n) (Fin n) (Polynomial B))
    (ξ : Fin n → B) (j : ℕ) : B :=
  ovInner B (ovDatumCoeff B X ξ j) (ovDatumCoeff B X ξ j)

/-- **The collapse predicate for the symbolic form.** The exponent tuple is
constant if every direction that is not identically degenerate vanishes to
the same order. If this held always, the per-direction claim would be vacuous
AND the object would degenerate to a single Łojasiewicz exponent — the
published, occupied case (OV/SWEEP.md S3). It does not hold: see
`exponentTuple_not_constant` and `exponentTuple_not_constant_noncomm`. -/
def ExponentTupleConstant {n : ℕ} (X : Matrix (Fin n) (Fin n) (Polynomial B)) : Prop :=
  ∀ ξ η : Fin n → B, ovVanishingOrder B X ξ ≠ ⊤ → ovVanishingOrder B X η ≠ ⊤ →
    ovVanishingOrder B X ξ = ovVanishingOrder B X η

end Symbolic

/-! ## Computation helpers for one-dimensional families -/

section Helpers

variable {B : Type*} [Ring B]

lemma ovFamilyImage_diagonal_one (p : Polynomial B) (ξ : Fin 1 → B) :
    ovFamilyImage B (Matrix.diagonal ![p]) ξ 0 = p * Polynomial.C (ξ 0) := by
  simp [ovFamilyImage, Matrix.mulVec_diagonal]

lemma ovVanishingOrder_one (X : Matrix (Fin 1) (Fin 1) (Polynomial B)) (ξ : Fin 1 → B) :
    ovVanishingOrder B X ξ = (ovFamilyImage B X ξ 0).trailingDegree := by
  simp [ovVanishingOrder]

end Helpers

/-! ## COLLAPSE TEST (symbolic form): is the exponent tuple constant? -/

section CollapseAbelian

/-- The family `t ↦ (t, t²)` over `B = ℝ × ℝ`, as a `1 × 1` matrix over
`B[t]`. Its fibre at `t = 0` is `0`, hence ill-posed: an honest deformation
through the discriminant. -/
noncomputable def symWitness : Matrix (Fin 1) (Fin 1) (Polynomial (ℝ × ℝ)) :=
  Matrix.diagonal ![Polynomial.monomial 1 ((1 : ℝ), (0 : ℝ))
    + Polynomial.monomial 2 ((0 : ℝ), (1 : ℝ))]

lemma symWitness_degenerate : IsDegenerateAtZero (ℝ × ℝ) symWitness := by
  have h0 : familyFibreZero (ℝ × ℝ) symWitness = 0 := by
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [familyFibreZero, symWitness, Matrix.diagonal, Polynomial.coeff_monomial]
  rw [IsDegenerateAtZero, h0]
  exact not_isUnit_zero

/-- Direction `(1,0)` sees the family vanish to order `1`. -/
lemma symWitness_order_fst :
    ovVanishingOrder (ℝ × ℝ) symWitness (fun _ => ((1 : ℝ), (0 : ℝ))) = (1 : ℕ) := by
  rw [ovVanishingOrder_one, symWitness, ovFamilyImage_diagonal_one]
  have : (Polynomial.monomial 1 ((1 : ℝ), (0 : ℝ)) + Polynomial.monomial 2 ((0 : ℝ), (1 : ℝ)))
      * Polynomial.C ((1 : ℝ), (0 : ℝ)) = Polynomial.monomial 1 ((1 : ℝ), (0 : ℝ)) := by
    rw [← Polynomial.monomial_zero_left, add_mul, Polynomial.monomial_mul_monomial,
      Polynomial.monomial_mul_monomial]
    norm_num [Prod.ext_iff]
  simp only [this]
  exact Polynomial.trailingDegree_monomial (by simp [Prod.ext_iff])

/-- Direction `(0,1)` sees the SAME family vanish to order `2`. -/
lemma symWitness_order_snd :
    ovVanishingOrder (ℝ × ℝ) symWitness (fun _ => ((0 : ℝ), (1 : ℝ))) = (2 : ℕ) := by
  rw [ovVanishingOrder_one, symWitness, ovFamilyImage_diagonal_one]
  have : (Polynomial.monomial 1 ((1 : ℝ), (0 : ℝ)) + Polynomial.monomial 2 ((0 : ℝ), (1 : ℝ)))
      * Polynomial.C ((0 : ℝ), (1 : ℝ)) = Polynomial.monomial 2 ((0 : ℝ), (1 : ℝ)) := by
    rw [← Polynomial.monomial_zero_left, add_mul, Polynomial.monomial_mul_monomial,
      Polynomial.monomial_mul_monomial]
    norm_num [Prod.ext_iff]
  simp only [this]
  exact Polynomial.trailingDegree_monomial (by simp [Prod.ext_iff])

/-- **COLLAPSE TEST (symbolic), RUN — NO COLLAPSE (proved).** The exponent
tuple is NOT constant across directions: in the family `t ↦ (t, t²)` the
direction `(1,0)` vanishes to order `1` and `(0,1)` to order `2`. A single
aggregated Łojasiewicz exponent — the only kind in the published literature
(OV/SWEEP.md S3) — cannot record this. The per-direction form is therefore
not vacuous.

Honest caveat, carried over from the metric side: `ℝ × ℝ` is ABELIAN, so this
witness alone shows only that aggregation loses information, which is a
statement about tuples, not about noncommutativity. The noncommutative
witness is `exponentTuple_not_constant_noncomm`. -/
theorem exponentTuple_not_constant : ¬ ExponentTupleConstant (ℝ × ℝ) symWitness := by
  intro h
  have h1 := symWitness_order_fst
  have h2 := symWitness_order_snd
  have := h (fun _ => ((1 : ℝ), (0 : ℝ))) (fun _ => ((0 : ℝ), (1 : ℝ)))
    (by rw [h1]; exact ENat.coe_ne_top 1) (by rw [h2]; exact ENat.coe_ne_top 2)
  rw [h1, h2] at this
  exact absurd this (by decide)

end CollapseAbelian

section CollapseNoncommutative

/-- Matrix units of `M₂(ℝ)`, the noncommutative coefficient algebra. -/
def e₁ : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]

def e₂ : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 0, 1]

lemma e₁_mul_e₁ : e₁ * e₁ = e₁ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [e₁, Matrix.mul_apply, Fin.sum_univ_two]

lemma e₂_mul_e₁ : e₂ * e₁ = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [e₁, e₂, Matrix.mul_apply, Fin.sum_univ_two]

lemma e₁_mul_e₂ : e₁ * e₂ = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [e₁, e₂, Matrix.mul_apply, Fin.sum_univ_two]

lemma e₂_mul_e₂ : e₂ * e₂ = e₂ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [e₂, Matrix.mul_apply, Fin.sum_univ_two]

lemma e₁_ne_zero : e₁ ≠ 0 := by
  intro h
  have := congrFun (congrFun h 0) 0
  simp [e₁] at this

lemma e₂_ne_zero : e₂ ≠ 0 := by
  intro h
  have := congrFun (congrFun h 1) 1
  simp [e₂] at this

/-- The NONCOMMUTATIVE witness family `t ↦ e₁ t + e₂ t²` over
`B = M₂(ℝ)`. -/
noncomputable def symWitnessNC :
    Matrix (Fin 1) (Fin 1) (Polynomial (Matrix (Fin 2) (Fin 2) ℝ)) :=
  Matrix.diagonal ![Polynomial.monomial 1 e₁ + Polynomial.monomial 2 e₂]

lemma symWitnessNC_degenerate :
    IsDegenerateAtZero (Matrix (Fin 2) (Fin 2) ℝ) symWitnessNC := by
  have h0 : familyFibreZero (Matrix (Fin 2) (Fin 2) ℝ) symWitnessNC = 0 := by
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [familyFibreZero, symWitnessNC, Matrix.diagonal, Polynomial.coeff_monomial]
  rw [IsDegenerateAtZero, h0]
  exact not_isUnit_zero

lemma symWitnessNC_order_e₁ :
    ovVanishingOrder (Matrix (Fin 2) (Fin 2) ℝ) symWitnessNC (fun _ => e₁) = (1 : ℕ) := by
  rw [ovVanishingOrder_one, symWitnessNC, ovFamilyImage_diagonal_one]
  have : (Polynomial.monomial 1 e₁ + Polynomial.monomial 2 e₂) * Polynomial.C e₁
      = Polynomial.monomial 1 e₁ := by
    rw [← Polynomial.monomial_zero_left, add_mul, Polynomial.monomial_mul_monomial,
      Polynomial.monomial_mul_monomial, e₁_mul_e₁, e₂_mul_e₁]
    simp
  simp only [this]
  exact Polynomial.trailingDegree_monomial e₁_ne_zero

lemma symWitnessNC_order_e₂ :
    ovVanishingOrder (Matrix (Fin 2) (Fin 2) ℝ) symWitnessNC (fun _ => e₂) = (2 : ℕ) := by
  rw [ovVanishingOrder_one, symWitnessNC, ovFamilyImage_diagonal_one]
  have : (Polynomial.monomial 1 e₁ + Polynomial.monomial 2 e₂) * Polynomial.C e₂
      = Polynomial.monomial 2 e₂ := by
    rw [← Polynomial.monomial_zero_left, add_mul, Polynomial.monomial_mul_monomial,
      Polynomial.monomial_mul_monomial, e₁_mul_e₂, e₂_mul_e₂]
    simp
  simp only [this]
  exact Polynomial.trailingDegree_monomial e₂_ne_zero

/-- **COLLAPSE TEST (symbolic), NONCOMMUTATIVE INSTANCE — NO COLLAPSE
(proved).** Over the noncommutative `B = M₂(ℝ)`, the family
`t ↦ e₁ t + e₂ t²` vanishes to order `1` in direction `e₁` and to order `2`
in direction `e₂`. This is the witness OV/SWEEP.md S3 demands: two directions
with genuinely different vanishing orders, in the setting (noncommutative
coefficients + per-direction tuple) that the sweep found unoccupied. -/
theorem exponentTuple_not_constant_noncomm :
    ¬ ExponentTupleConstant (Matrix (Fin 2) (Fin 2) ℝ) symWitnessNC := by
  intro h
  have h1 := symWitnessNC_order_e₁
  have h2 := symWitnessNC_order_e₂
  have := h (fun _ => e₁) (fun _ => e₂)
    (by rw [h1]; exact ENat.coe_ne_top 1) (by rw [h2]; exact ENat.coe_ne_top 2)
  rw [h1, h2] at this
  exact absurd this (by decide)

end CollapseNoncommutative

end DiscoveryKernels.R3
