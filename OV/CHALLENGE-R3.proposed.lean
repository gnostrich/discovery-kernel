/-
Copyright (c) 2026 discovery-kernels contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.

# CHALLENGE-R3.proposed.lean — PROPOSED refined R3 headlines

PENDING HUMAN REVIEW — this file is a PROPOSAL, not the statement registry.
Challenge.lean's R3 section is untouched; per the R3 charter's human-review
gate, the orchestrator holds the merge until the operator approves. Upon
approval, the two theorem statements below replace the bodies of
`DiscoveryKernels.Challenge.ov_license` / `ov_completeness` verbatim (the
namespace here exists only to avoid clashing with the live registry), and
the definitions they cite (OV/Vocab.lean) become part of the R3
definitional layer, with a dated STATEMENTS.md changelog entry.

Justification and the analysis of why FREEZE-0's `ov_license` draft is not
kept as-is: OV/CHALLENGE-R3.proposed.md.

Both statements end in `sorry` BY DESIGN: R3 is a statements-only tier.
-/
import OV.Vocab
import OV.Cond
import OV.Symbolic

namespace DiscoveryKernels.Challenge.ProposedR3

open Matrix

/-- **Operator-valued license (MSY-shaped), stated frontier — PROPOSED.**
Let `B` be a star-ordered ring and `M : ℕ → B` an operator-valued moment
sequence (hermitian entries, positive semidefinite `B`-valued Hankel kernel —
the algebraic shadow of `M n = E_B (xⁿ)` for `x` self-adjoint, cf.
Mai–Speicher–Yin). Then the license chain holds:

1. finite OV Hankel rank (membership in a finitely generated shift-stable
   left `B`-submodule, Fliess/Schützenberger form) ⟺ finite linear
   realization over `B` (rational `B`-valued resolvent); and
2. finite linear realization ⟺ finitely atomic in the star sense
   (`M n = ∑ i, star (w i) * (a i)ⁿ * w i`, self-adjoint atoms `a i ∈ B`,
   manifestly positive weights).

Chain 1 is theorem-shaped over every ring and needs neither star, order, nor
`hM`. Chain 2 is the MSY frontier: the moment hypothesis `hM` is essential —
without positivity the FREEZE-0 unconditional version is FALSE (Jordan
blocks / `cos nθ`-type realizations have no atomic form; see the proposal
notes). For `B = ℂ` chain 2 is classical (finite-rank PSD Hankel ⟺ finitely
atomic Hamburger measure); for general `B` it is stated frontier. `sorry` BY
DESIGN. -/
theorem ov_license
    {B : Type} [Ring B] [StarRing B] [PartialOrder B] [StarOrderedRing B]
    (M : ℕ → B) (hM : R3.IsOVMomentSequence B M) :
    (R3.HasFiniteOVHankelRankStable B M ↔ R3.HasFiniteRealization B M) ∧
      (R3.HasFiniteRealization B M ↔ R3.IsFinitelyAtomicOVStar B M) := sorry

/-- **Operator-valued completeness (free-Ax–Schanuel-shaped), stated
frontier — PROPOSED.** Every genuine operator-valued alignment has a
structural cause. Concretely: let `x : Fin d → A` be a self-adjoint tuple in
a complex star algebra, conditioned by a ℂ-linear map `E : A →ₗ[ℂ] B`. The
genericity/freeness hypothesis is `hfaith`: `E` is faithful on positives
(`E (star a * a) = 0 → a = 0`) — the abstract role played by a faithful
(normal) conditional expectation `E_B` in the free-probability setting
(Mai–Speicher–Weber regularity line). If the word-indexed OV moment/Hankel
data of `x` under `E` shows a rank drop at level `n` (an *alignment*: some
nonzero scalar row combination of `{E (x_{w ·}) : |w| ≤ n}` vanishes
identically), then there is a *structural cause*: a nonzero noncommutative
polynomial of degree ≤ `n` in `FreeAlgebra ℂ (Fin d)` annihilating the tuple
under evaluation. The alignment is never a numerical accident: it certifies
an exact algebraic relation. `sorry` BY DESIGN. -/
theorem ov_completeness
    {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]
    {B : Type} [AddCommGroup B] [Module ℂ B]
    (E : A →ₗ[ℂ] B) {d : ℕ} (x : Fin d → A) (n : ℕ)
    (hsa : ∀ i, star (x i) = x i)
    (hfaith : ∀ a : A, E (star a * a) = 0 → a = 0)
    (halign : R3.HasOVAlignment E x n) :
    R3.HasPolyCause x n := sorry

/-! ## STEERING-02: the operator lift of the conditioning tier — PRIMARY FORM

The tier states TWO forms of the operator lift, and this section is the
**PRIMARY (metric) form**: a distance to the ill-posed set, valued in `B`.
The **FALLBACK (symbolic, order-of-vanishing) form** is the final section of
this file (`ov_lojasiewicz_order`), stated per STEERING-02a. They are
independent: the metric form needs a distance, the symbolic form needs a
parametrised family and no distance at all.

The three statements below are the OPERATOR LIFT of the `Conditioning/`
headline: a Condition Number Theorem with the distance to the ill-posed set
`Σ` valued in `B` rather than in `ℝ` (Demmel, Numer. Math. 51 (1987)
251–289; Bürgisser–Cucker, *Condition*, Springer 2013). The definitional
layer and the RUN COLLAPSE TESTS (all proved, no `sorry`) are in
`OV/Cond.lean`; the verdict is in `OV/CHALLENGE-R3.proposed.md`.

Sorry status per the STEERING-02 rule: all three are TARGETS (intended to be
proven), not declared-open frontier. -/

/-- **`B`-valued Condition Number Theorem, finite-dimensional — PROPOSED,
TARGET.** For `x ∈ Mₙ(B)` and a positive `b ∈ B`, the two readings of "`b` is
a certified `B`-valued margin" coincide:

* the ALGEBRAIC reading — `⟨ξ, b ξ⟩ ≤ ⟨xξ, xξ⟩` for every unit vector `ξ`
  (the operator-valued `σ_min(x)² ≥ b`); and
* the GEOMETRIC reading — every ill-posed `y` (non-invertible: `y ∈ Σ`) is at
  least `b` away from `x`, measured on `y`'s kernel.

This is Demmel's `κ(x) = ‖x‖ / dist(x, Σ)` with `dist` valued in `B`. The `⇒`
direction is proved (`R3.margin_imp_distanceCertificate`); the `⇐` direction
is the Eckart–Young rank-one construction `y = x - (xξ)ξ*`, which is why the
distance is measured on kernels. The bound MUST be compressed to the kernel:
the uncompressed global-infimum definition provably collapses to `0`
(`R3.globalInf_collapses`). -/
theorem ov_condition_number_theorem
    {B : Type} [Ring B] [StarRing B] [PartialOrder B] [StarOrderedRing B]
    {n : ℕ} (x : Matrix (Fin n) (Fin n) B) (b : B) (hb : 0 ≤ b) :
    (∀ ξ : Fin n → B, R3.ovInner B ξ ξ = 1 →
        R3.ovRayleigh B b ξ ≤ R3.ovInner B (x *ᵥ ξ) (x *ᵥ ξ)) ↔
      (∀ y : Matrix (Fin n) (Fin n) B, R3.IsIllPosed B y → ∀ ξ : Fin n → B,
        R3.ovInner B ξ ξ = 1 → y *ᵥ ξ = 0 →
          R3.ovRayleigh B b ξ ≤ R3.ovInner B ((x - y) *ᵥ ξ) ((x - y) *ᵥ ξ)) := sorry

/-- **Scalar base case: the `B`-valued distance MUST collapse when `B = ℝ`,
and does — PROPOSED, TARGET.** The certified margins of a real matrix are
exactly the `t ≤ λ_min(xᵀx) = σ_min(x)²`. This is the sanity condition on the
lift: at `B = ℝ` the `B`-valued object is obliged to be the classical
Demmel/Eckart–Young answer, no more and no less. (Courant–Fischer is not in
Mathlib — see Conditioning/SWEEP.md S1 — so this target carries a real
dependency.) -/
theorem ov_cnt_recovers_scalar
    {n : ℕ} (x : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    R3.IsMargin ℝ x t ↔
      0 ≤ t ∧ ∀ i, t ≤ (Matrix.isHermitian_conjTranspose_mul_self x).eigenvalues i := sorry

open scoped MatrixOrder in
/-- **The `B`-valued condition number is NOT an element of `B` — PROPOSED,
TARGET (the tier's decisive negative).** Over `B = M₂(ℝ)` with the Loewner
order there is a `2 × 2` matrix over `B` admitting NO greatest certified
margin: `dist_B(·, Σ)` is a certificate SET, never a `B`-valued number.

Witness (hand-verified, arithmetic in OV/CHALLENGE-R3.proposed.md, not yet
machine-checked): `x = diagonal ![d₁, d₂]` with `d₁* d₁ = diag(2,1)` and
`d₂* d₂ = [[3/2,1/2],[1/2,3/2]]`. By `R3.isMargin_diagonal_iff` the margin
set is the set of positive common lower bounds of those two, and `1` and
`diag(21/20, 9/10)` are incomparable lower bounds admitting no common upper
bound inside the set. The general reduction
(`R3.bvaluedDistance_fails_of_no_infimum`) is already PROVED; what remains is
this instance of Kadison's anti-lattice theorem (Proc. AMS 2 (1951) 505–510)
in machine-checked form. -/
theorem ov_dist_not_element_valued :
    ∃ x : Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) ℝ),
      ∀ b : Matrix (Fin 2) (Fin 2) ℝ,
        ¬ R3.IsBValuedDistance (Matrix (Fin 2) (Fin 2) ℝ) x b := sorry

/-! ## STEERING-02a: the symbolic (order-of-vanishing) form — FALLBACK FORM

**Marking, explicitly: the metric form above (`ov_condition_number_theorem`,
`ov_cnt_recovers_scalar`, `ov_dist_not_element_valued`) is PRIMARY; the
statement below is the FALLBACK.** The metric form survived its collapse test
(`R3.bvaluedDistance_not_scalar`), so the fallback is a structurally
different plan B, not a replacement: it needs no metric, only a discriminant
(`R3.IsDegenerateAtZero`), a deformation (a polynomial family), and an
integer order of vanishing recorded PER DIRECTION (`R3.ovVanishingOrder`).

Definitional layer and the run collapse test (proved, no `sorry`, including a
NONCOMMUTATIVE witness): `OV/Symbolic.lean`. Occupancy: OV/SWEEP.md S3 —
Łojasiewicz with explicit exponents for `σ_min` of real polynomial matrices
is PUBLISHED (arXiv 1604.02805) and claimed by nobody here; only the
noncommutative setting and the per-direction tuple are claimed.

Citations: Łojasiewicz (1959, 1965); Bierstone–Milman; Kurdyka (1998);
Demmel (1987) and Bürgisser–Cucker (2013) for the metric counterpart.

Sorry status: TARGET. -/

/-- **Operator-valued Łojasiewicz order form — PROPOSED, TARGET (FALLBACK).**
Let `X : Mₙ(B[t])` be a polynomial family over a star-ordered ring `B` whose
positive cone is faithful (`hfaith`, automatic in any C*-algebra), degenerate
at the parameter origin (`hdeg`: the fibre `X(0)` is ill-posed — `Σ` as a
discriminant, no metric). Fix a direction `ξ ∈ Bⁿ` whose Łojasiewicz order is
`k` (`hk`). Then the defining data vanish to order exactly `k` in that
direction:

* every lower-order coefficient of the direction datum vanishes — `k`
  "derivatives" of the defining function die along the degenerate locus; and
* the order-`k` Łojasiewicz leading certificate is STRICTLY POSITIVE in `B`
  — the `B`-valued constant `c` of `|f| ≥ c · dist^α`, recorded per
  direction rather than aggregated into one real number.

The exponent tuple `ξ ↦ k(ξ)` is provably non-constant, over commutative and
noncommutative `B` alike (`R3.exponentTuple_not_constant`,
`R3.exponentTuple_not_constant_noncomm`), so this form does not degenerate to
the published single-exponent case. -/
theorem ov_lojasiewicz_order
    {B : Type} [Ring B] [StarRing B] [PartialOrder B] [StarOrderedRing B]
    (hfaith : ∀ c : B, star c * c = 0 → c = 0)
    {n : ℕ} (X : Matrix (Fin n) (Fin n) (Polynomial B))
    (hdeg : R3.IsDegenerateAtZero B X)
    (ξ : Fin n → B) (k : ℕ)
    (hk : R3.ovVanishingOrder B X ξ = (k : ℕ∞)) :
    (∀ j < k, R3.ovDatumCoeff B X ξ j = 0) ∧
      0 < R3.ovLeadingCertificate B X ξ k := sorry

end DiscoveryKernels.Challenge.ProposedR3
