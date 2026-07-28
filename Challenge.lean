/-
Copyright (c) 2026 discovery-kernels contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.

# Challenge.lean — the statement registry of `discovery-kernels`

This file IS the set of claims of this repository. Prose (README,
STATEMENTS.md) never claims anything this file does not state.

One theory at three altitudes, in the order the claims lead:
* `COND` — the scalar conditioning theory: certified lower bounds on
  `dist(x, Σ)`, the distance to the ill-posed set, with executable checkers
  proven sound and sharpness witnesses where the bound degenerates.
* `R1` — one instance: PSLQ integer-relation detection, where `Σ` is the set
  of vectors admitting a shorter relation.
* `R3` — the operator lift, `Σ` and the margin taken in an algebra `B`.

Rules of this file:
* Three append-only tier sections, delimited below. No agent edits another
  tier's section. (R0 and R2 were descoped 2026-07-27; see STATEMENTS.md
  changelog.)
* Every headline here is stated with `:= sorry` — permanently. Solutions live
  in the tier directories and are checked against these statements by
  `comparator/` (definitional-equality check + per-theorem axiom allowlist).
  A `sorry` here is a registry marker, never an open problem.
* R3 headlines are stated frontier. Their refined forms were signed off by
  the operator on 2026-07-28; see STATEMENTS.md for which sorries are targets
  and which are declared-open.
* Statement changes after FREEZE-0 are recorded in STATEMENTS.md with a dated
  note.
-/
import Conditioning.Sharpness
import Conditioning.Bridge
import PSLQ.Defs
import PSLQ.Core
import OV.Defs
import OV.Vocab
import OV.Cond
import OV.Symbolic

open scoped BigOperators Matrix

namespace DiscoveryKernels.Challenge

-- ==== COND ==== conditioning: certified distance to ill-posedness ==========

/-- **Executable exact-rational conditioning checker, sound.** If the
`Bool`-valued decision procedure `Cond.condCheck` — pure `ℚ` arithmetic, no
`Float`, no `native_decide` — accepts the rational matrix `A` at margin `c`,
then the real matrix `Cond.toReal A` has smallest singular value at least `c`:
`c‖v‖ ≤ ‖Av‖` for every `v`, written as `Cond.SigmaMinGE`.

**Soundness only, by design**: "says yes ⟹ the bound holds". No completeness is
claimed; `cond_gershgorin_wall` below certifies an input where the checker says
nothing useful even though the input is well-posed. Adapted at schema level
(no code imported; pins differ) from `certified-positivity`'s
`checkPDq_sound`. -/
theorem cond_check_sound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (c : ℚ)
    (h : Cond.condCheck A c = true) :
    Cond.SigmaMinGE (Cond.toReal A) (c : ℝ) := sorry

section L2OperatorNormScope
open scoped Matrix.Norms.L2Operator

/-- **THE HEADLINE — a certified distance to ill-posedness, from an executable
exact-rational check.** `Σ` is `Cond.SigmaSing n`, the set of singular matrices:
the ill-posed inputs of the matrix-inversion problem, at which the answer is a
discontinuous function of the data. If the checker accepts `A` at margin `c`,
then

    c ≤ dist(A, Σ)

where the distance is Mathlib's `Metric.infDist` in Mathlib's **ℓ² operator
norm** (scope `Matrix.Norms.L2Operator`). By the Condition Number Theorem
(Demmel, Numer. Math. 51 (1987) 251–289; Bürgisser–Cucker, *Condition*,
Springer 2013) this is exactly an upper bound on the condition number, and it
is what licenses a finite-precision computation: data accurate to better than
`c` determines the answer.

`0 < n` is load-bearing, not decoration: for `n = 0` the empty matrix has
`det = 1`, so `Σ = ∅` and `Metric.infDist _ ∅ = 0`.

The `open scoped Matrix.Norms.L2Operator` above is confined to this one
declaration deliberately. That instance is NOT Mathlib's default `Matrix`
norm; removing the `open` does not error, it silently states a *different
theorem about a different norm*. Do not hoist or delete it. -/
theorem cond_dist_to_illposed {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (c : ℚ)
    (hn : 0 < n) (h : Cond.condCheck A c = true) :
    (c : ℝ) ≤ Metric.infDist (Cond.toReal A) (Cond.SigmaSing n) := sorry

end L2OperatorNormScope

/-- **THE TIER'S POINT — a certified margin licenses a finite-precision
computation.** If the exact-rational checker accepts `A` at margin `c`, and the
right-hand side of the linear system `A x = b` is known only to within `ε` in
the Euclidean norm, then the solution is still determined to within `ε / c`.
Stated squared, so no square roots and no `Float` appear:

    c² ‖x - y‖² ≤ ε².

This is the linear-algebra analogue of `pslq_empirical_sound`: a certified
distance to ill-posedness converts input accuracy into output accuracy. -/
theorem cond_licenses_computation {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (c : ℚ)
    (h : Cond.condCheck A c = true) (x y b b' : Fin n → ℝ)
    (hx : Cond.toReal A *ᵥ x = b) (hy : Cond.toReal A *ᵥ y = b') (ε : ℝ)
    (hε : Cond.sqNorm (b - b') ≤ ε ^ 2) :
    (c : ℝ) ^ 2 * Cond.sqNorm (x - y) ≤ ε ^ 2 := sorry

/-- **Certified margin to the zero-eigenvalue set.** For a Hermitian (real
symmetric) rational matrix, acceptance by the exact-rational checker at margin
`c` certifies `c ≤ |λ|` for **every** one of Mathlib's own
`Matrix.IsHermitian.eigenvalues`. Since `Σ` for the symmetric eigenvalue
problem is exactly the matrices with a zero eigenvalue, this is the distance
statement in eigenvalue form. -/
theorem cond_eigenvalue_margin {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (c : ℚ)
    (h : Cond.condCheck A c = true) (hA : (Cond.toReal A).IsHermitian) (j : Fin n) :
    (c : ℝ) ≤ |hA.eigenvalues j| := sorry

/-- **SHARPNESS WITNESS 1 — the certified floor is exactly the distance.** On
the explicit exact-rational input `Cond.diagA = !![3,0;0,5]`:

* the checker accepts `c = 3`, and accepts nothing larger — so `3` is the
  engine's exact output, not a lucky guess;
* hence `dist(diagA, Σ) ≥ 3`;
* and no `c > 3` admits a distance certificate, because an explicit
  perturbation of spectral norm `3` lands in `Σ`.

So `dist(diagA, Σ) = 3` exactly: the tier's bound is **tight, not
conservative**, on this input. The upper bound is a certified witness, so
nothing here uses Eckart–Young (which, per `Conditioning/SWEEP.md` S1, is
already formalized in Lean 4 elsewhere and is claimed by nobody here). -/
theorem cond_margin_sharp :
    Cond.condCheck Cond.diagA 3 = true ∧
      Cond.DistGE (Cond.toReal Cond.diagA) 3 ∧
      (∀ c : ℝ, 3 < c → ¬ Cond.DistGE (Cond.toReal Cond.diagA) c) ∧
      (∀ c : ℚ, Cond.condCheck Cond.diagA c = true → c ≤ 3) := sorry

/-- **SHARPNESS WITNESS 2 — the engine's wall, certified.** On the explicit
exact-rational input `Cond.wallA = !![1,1;0,1]` (a unimodular shear, `det = 1`):

* the first row of its exact rational Gram matrix has diagonal-dominance margin
  **exactly zero** — an equality between exact rationals, so no sharper
  enclosure of the entries can improve it;
* consequently the checker certifies only `c = 0`, which by
  `Cond.distGE_zero_vacuous` is a *vacuous* statement true of every matrix,
  singular ones included;
* and yet the input is genuinely well-posed: a direct Rayleigh argument
  certifies `dist(wallA, Σ) ≥ 1/2 > 0`.

The zero is therefore a property of the **Gershgorin engine**, not of the
input — as distinct from `Cond.singular_dist_zero`, where a reported zero is
the truth. Certifying both cases is what makes a reported floor interpretable;
this is the conditioning analogue of `certified-positivity`'s
`three_grid_last_row_gershgorin_zero`. -/
theorem cond_gershgorin_wall :
    Cond.gramQ Cond.wallA 0 0 - Cond.gershRadiusQ (Cond.gramQ Cond.wallA) 0 = 0 ∧
      (∀ c : ℚ, Cond.condCheck Cond.wallA c = true → c = 0) ∧
      Cond.DistGE (Cond.toReal Cond.wallA) (1 / 2) := sorry

-- ==== R1 ==== PSLQ: exact core, termination, empirical input ==============

/-- **PSLQ partial correctness.** If the exact-arithmetic PSLQ-class core
`R1.pslq`, run on exact rational input `x` with any fuel, reports `m`, then
`m` is an integer relation of `x` (nonzero, with `∑ mᵢ xᵢ = 0`).

Soundness only: this says a report is correct, never that the core reports
whenever a relation exists. Refined from the FREEZE-0 `True` placeholder on
2026-07-27, when `R1.pslq` landed; see STATEMENTS.md changelog. -/
theorem pslq_partial_correct
    {n : ℕ} (x : Fin n → ℚ) (fuel : ℕ) (m : Fin n → ℤ)
    (h : R1.pslq x fuel = some m) :
    R1.IsIntRelation x m := sorry

/-- **PSLQ termination / lower bound (Borwein–Lisoněk form).** While the
exact-arithmetic core has reported no relation within `fuel` rounds
(`R1.pslq x fuel = none`), every integer relation `m` of the exact rational
input `x` is large: its squared euclidean norm is at least the explicit
rational number `gsoNormSq x k` read off the state's own rational
(CSV/HJLS-normalized) Gram–Schmidt data after `fuel` rounds, where `k` is the
last index at which `m` has a nonzero coordinate in the algorithm's current
basis (`coords m = Binv · m`, an integer vector by unimodularity).

The index `k` is stated rather than hidden behind a `min` because it must be:
the `n` projections of the basis columns onto `x^⊥` span an
`(n-1)`-dimensional space, so exactly one Gram–Schmidt direction degenerates
and a `min` over all `j` would be the trivial bound `0`. Pinning `k` is what
makes the bound a real one. Refined from the FREEZE-0 `True` placeholder on
2026-07-27; see STATEMENTS.md changelog. -/
theorem pslq_lower_bound
    {n : ℕ} (x : Fin n → ℚ) (fuel : ℕ) (hnone : R1.pslq x fuel = none)
    (m : Fin n → ℤ) (hm : R1.IsIntRelation x m) (k : Fin n)
    (hk : (R1.pslqState x fuel).coords m k ≠ 0)
    (hlast : ∀ j, k < j → (R1.pslqState x fuel).coords m j = 0) :
    (R1.pslqState x fuel).gsoNormSq x k ≤ ∑ i, ((m i : ℚ)) ^ 2 := sorry

/-- **THE TIER'S POINT — empirical-input soundness.** Input known to precision
`p` (true vector `x : Fin n → ℝ`, computed rational approximation `xq` with
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
        R1.IsIntRelation x m) := sorry

-- ==== R3 ==== operator-valued lift — STATEMENTS ONLY =======================

/- Six statements, refined 2026-07-28 (see STATEMENTS.md changelog). The
FREEZE-0 `ov_license` draft was REPLACED, not weakened: it was proved *false*
as stated. Sorry status per tier rule: `ov_license` is DECLARED-OPEN; the
other five are TARGETS. Definitional layers: OV/Vocab.lean, OV/Cond.lean,
OV/Symbolic.lean — whose collapse tests are proved, sorry-free. -/

/-- **Operator-valued license (MSY-shaped), stated frontier .**
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
frontier .** Every genuine operator-valued alignment has a
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
an exact algebraic relation.

`[StarModule ℂ A]` — the compatibility axiom `star (c • a) = star c • star a`,
satisfied by every C*-algebra and every intended model — was ADDED on
2026-07-28 (a disclosed weakening; see STATEMENTS.md changelog). It is not
cosmetic: without it `star (algebraMap ℂ A z)` can fall outside the range of
`algebraMap`, which takes `star a` out of the ℂ-span of the words and blocks
the faithfulness argument. That this cannot be derived from
`[Ring A] [StarRing A] [Algebra ℂ A]` alone is itself PROVED
(`R3.star_algebraMap_not_in_range`, with `ℂ × ℂ` under a twisted star as the
witness). No counterexample to the unhypothesised statement is known; the
hypothesis repairs the route, it does not rescue a false claim. -/
theorem ov_completeness
    {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
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
and does — TARGET.** The certified margins of a real matrix are
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

/-- **Operator-valued Łojasiewicz order form — TARGET (FALLBACK).**
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

end DiscoveryKernels.Challenge
